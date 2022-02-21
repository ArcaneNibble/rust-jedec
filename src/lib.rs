//! JEDEC programming file format parser and writer

#![no_std]
extern crate alloc;

use bitvec::prelude::*;

use alloc::vec;
use alloc::vec::Vec;
use core::fmt;
use core::fmt::Write;
use core::num;
use core::num::Wrapping;
use core::str;

/// Errors that can occur when parsing a .jed file
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum JedParserError {
    /// No STX byte found
    MissingSTX,
    /// No ETX byte found
    MissingETX,
    /// An invalid UTF-8 sequence occurred
    InvalidNonASCIICharacter(str::Utf8Error),
    /// A field contains a character not appropriate for that field (e.g. non-hex digit in a hex field)
    InvalidCharacter,
    /// An unexpected end of file was encountered in the file checksum
    UnexpectedEnd,
    /// The file checksum was nonzero and incorrect
    BadFileChecksum,
    /// The fuse checksum (`C` command) was incorrect
    BadFuseChecksum,
    /// A `L` field index was out of range
    InvalidFuseIndex,
    /// There was no `QF` field
    MissingQF,
    /// There was no `F` field, but not all fuses had a value specified
    MissingF,
    /// There was a field that this program does not recognize
    UnrecognizedField,
}

#[cfg(std)]
impl std::error::Error for JedParserError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            &JedParserError::MissingSTX => None,
            &JedParserError::MissingETX => None,
            &JedParserError::InvalidUtf8(ref err) => Some(err),
            &JedParserError::InvalidCharacter => None,
            &JedParserError::UnexpectedEnd => None,
            &JedParserError::BadFileChecksum => None,
            &JedParserError::BadFuseChecksum => None,
            &JedParserError::InvalidFuseIndex => None,
            &JedParserError::MissingQF => None,
            &JedParserError::MissingF => None,
            &JedParserError::UnrecognizedField => None,
        }
    }
}

impl fmt::Display for JedParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &JedParserError::MissingSTX => write!(f, "STX not found"),
            &JedParserError::MissingETX => write!(f, "ETX not found"),
            &JedParserError::InvalidNonASCIICharacter(err) => {
                write!(f, "invalid utf8 character: {}", err)
            }
            &JedParserError::InvalidCharacter => write!(f, "invalid character in field"),
            &JedParserError::UnexpectedEnd => write!(f, "unexpected end of file"),
            &JedParserError::BadFileChecksum => write!(f, "invalid file checksum"),
            &JedParserError::BadFuseChecksum => write!(f, "invalid fuse checksum"),
            &JedParserError::InvalidFuseIndex => write!(f, "invalid fuse index value"),
            &JedParserError::MissingQF => write!(f, "missing QF field"),
            &JedParserError::MissingF => write!(f, "missing F field"),
            &JedParserError::UnrecognizedField => write!(f, "unrecognized field"),
        }
    }
}

impl From<str::Utf8Error> for JedParserError {
    fn from(err: str::Utf8Error) -> Self {
        JedParserError::InvalidNonASCIICharacter(err)
    }
}

impl From<num::ParseIntError> for JedParserError {
    fn from(_: num::ParseIntError) -> Self {
        JedParserError::InvalidCharacter
    }
}

const STX: u8 = 0x02;
const ETX: u8 = 0x03;

/// Struct representing parsing quirk options
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct ParseQuirks {
    no_design_spec: bool,
}

impl ParseQuirks {
    /// Construct a new object with default quirk settings
    pub fn new() -> Self {
        Self {
            no_design_spec: false,
        }
    }

    /// Xilinx is known to output JEDEC files that do not contain a
    /// design specification block
    pub fn no_design_spec(mut self, no_design_spec: bool) -> Self {
        self.no_design_spec = no_design_spec;
        self
    }
}

impl Default for ParseQuirks {
    fn default() -> Self {
        Self::new()
    }
}

/// Struct representing a JEDEC programming file
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct JEDECFile<'a> {
    /// Fuse array
    pub f: BitVec,
    /// Data that appears before the STX byte
    pub header: &'a [u8],
    /// Data that appears after the ETX byte
    pub footer: &'a [u8],
    /// Design specification field
    pub design_spec: &'a [u8],
    /// Parsed N (Note) commands
    pub notes: Vec<&'a [u8]>,
}

fn trim_slice_start(mut in_: &[u8]) -> &[u8] {
    while in_.len() > 0 {
        match in_[0] {
            b' ' | b'\r' | b'\n' => {
                in_ = &in_[1..];
            }
            _ => {
                break;
            }
        }
    }
    in_
}

fn trim_slice_end(mut in_: &[u8]) -> &[u8] {
    while in_.len() > 0 {
        match in_[in_.len() - 1] {
            b' ' | b'\r' | b'\n' => {
                in_ = &in_[..in_.len() - 1];
            }
            _ => {
                break;
            }
        }
    }
    in_
}

fn trim_slice(in_: &[u8]) -> &[u8] {
    trim_slice_end(trim_slice_start(in_))
}

impl<'a> JEDECFile<'a> {
    /// Reads a .jed file
    pub fn from_bytes(in_bytes: &'a [u8], quirks: &ParseQuirks) -> Result<Self, JedParserError> {
        // Find STX
        let jed_stx = in_bytes
            .iter()
            .position(|&x| x == STX)
            .ok_or(JedParserError::MissingSTX)?;

        // Checksum and find ETX
        let mut file_csum = Wrapping(0u16);
        let jed_etx = in_bytes
            .iter()
            .position(|&x| {
                file_csum += Wrapping(x as u16);
                x == ETX
            })
            .ok_or(JedParserError::MissingETX)?;

        // Add the ETX to the checksum too
        file_csum += Wrapping(ETX as u16);

        // Check the checksum
        if jed_etx + 4 >= in_bytes.len() {
            return Err(JedParserError::UnexpectedEnd);
        }
        let csum_expected = &in_bytes[jed_etx + 1..jed_etx + 5];
        let csum_expected = str::from_utf8(csum_expected)?;
        let csum_expected = u16::from_str_radix(csum_expected, 16)?;
        if csum_expected != 0 && csum_expected != file_csum.0 {
            return Err(JedParserError::BadFileChecksum);
        }

        // // Make a str object out of the body
        // let jed_body = str::from_utf8(&in_bytes[jed_stx + 1..jed_etx])?;

        // slice out header/footer/body
        let header = &in_bytes[..jed_stx];
        let jed_body = &in_bytes[jed_stx + 1..jed_etx];
        let footer = &in_bytes[jed_etx + 5..];

        // state
        let mut fuse_expected_csum = None;
        let mut num_fuses = 0;
        let mut fuses = bitvec![];
        let mut fuses_written = bitvec![];
        let mut default_fuse = None;
        let mut vecs_alloced = false;
        let mut notes = Vec::new();

        // Ready to parse each line
        let mut jed_fields = jed_body.split(|&c| c == b'*');

        let design_spec = if quirks.no_design_spec {
            &[]
        } else {
            jed_fields.next().unwrap_or(&[])
        };

        for l in jed_fields {
            let l = trim_slice_start(l);
            if l.len() == 0 {
                // FIXME: Should we do something else here?
                // ignore empty fields
                continue;
            }

            // Now we can look at the first byte to figure out what we have
            match l[0] {
                b'J' => {}                                                  // TODO: "Official" device type
                b'G' => {}                                                  // TODO: Security fuse
                b'B' | b'I' | b'K' | b'M' | b'O' | b'W' | b'Y' | b'Z' => {} // Explicitly reserved in spec, ignore
                b'D' => {}                                                  // Obsolete
                b'E' | b'U' => {} // TODO: Extra fuses, unsupported for now
                b'X' | b'V' | b'P' | b'S' | b'R' | b'T' | b'A' => {} // Testing-related, no intent to support for now
                b'F' => {
                    // Default state
                    let default_state_str = trim_slice(&l[1..]);
                    default_fuse = Some(match default_state_str {
                        b"0" => false,
                        b"1" => true,
                        _ => return Err(JedParserError::InvalidCharacter),
                    });
                }
                b'N' => {
                    // Notes
                    notes.push(&l[1..]);
                }
                b'Q' => {
                    // Look for QF
                    if &l[0..2] == b"QF" {
                        let num_fuses_str = trim_slice(&l[2..]);
                        let num_fuses_str = str::from_utf8(num_fuses_str)?;
                        num_fuses = usize::from_str_radix(num_fuses_str, 10)?;
                    }
                }
                b'L' => {
                    // A set of fuses
                    if num_fuses == 0 {
                        return Err(JedParserError::MissingQF);
                    }

                    if !vecs_alloced {
                        if let Some(default_fuse) = default_fuse {
                            fuses = BitVec::repeat(default_fuse, num_fuses);
                        } else {
                            fuses = BitVec::repeat(false, num_fuses);
                            fuses_written = BitVec::repeat(false, num_fuses);
                        }
                        vecs_alloced = true;
                    }

                    // l is something like "L012345 1010101"
                    let fuse_data = trim_slice(&l[1..]);

                    let mut fuse_split =
                        fuse_data.splitn(2, |&c| c == b' ' || c == b'\r' || c == b'\n');

                    let fuse_idx_str = fuse_split.next().unwrap();
                    let fuse_idx_str = str::from_utf8(fuse_idx_str)?;
                    let mut fuse_idx = usize::from_str_radix(fuse_idx_str, 10)?;

                    let fuse_bits = fuse_split.next().ok_or(JedParserError::InvalidFuseIndex)?;
                    for fusec in fuse_bits {
                        match &fusec {
                            b'0' => {
                                if fuse_idx >= num_fuses {
                                    return Err(JedParserError::InvalidFuseIndex);
                                }
                                fuses.set(fuse_idx, false);
                                if default_fuse.is_none() {
                                    fuses_written.set(fuse_idx, true);
                                }
                                fuse_idx += 1;
                            }
                            b'1' => {
                                if fuse_idx >= num_fuses {
                                    return Err(JedParserError::InvalidFuseIndex);
                                }
                                fuses.set(fuse_idx, true);
                                if default_fuse.is_none() {
                                    fuses_written.set(fuse_idx, true);
                                }
                                fuse_idx += 1;
                            }
                            b' ' | b'\r' | b'\n' => {} // Do nothing
                            _ => return Err(JedParserError::InvalidCharacter),
                        }
                    }
                }
                b'C' => {
                    // Checksum
                    let csum_str = trim_slice(&l[1..]);
                    if csum_str.len() != 4 {
                        return Err(JedParserError::BadFuseChecksum);
                    }
                    let csum_str = str::from_utf8(csum_str)?;
                    fuse_expected_csum = Some(u16::from_str_radix(csum_str, 16)?);
                }
                _ => return Err(JedParserError::UnrecognizedField),
            }
        }

        // Check to make sure all fuses were written
        if !vecs_alloced && num_fuses > 0 {
            return Err(JedParserError::MissingF);
        }
        if default_fuse.is_none() {
            if !fuses_written.all() {
                return Err(JedParserError::MissingF);
            }
        }

        // Fuse checksum
        let mut fuse_csum = Wrapping(0u16);
        if let Some(fuse_expected_csum) = fuse_expected_csum {
            for i in 0..num_fuses {
                if fuses[i as usize] {
                    // Fuse is a 1 and contributes to the sum
                    fuse_csum += Wrapping(1u16 << (i % 8));
                }
            }

            if fuse_expected_csum != fuse_csum.0 {
                return Err(JedParserError::BadFuseChecksum);
            }
        }

        Ok(Self {
            f: fuses,
            header,
            footer,
            design_spec,
            notes,
        })
    }

    /// Writes the contents to a JEDEC file. Note that a `&mut Write` can also be passed as a writer. Line breaks are
    /// inserted _before_ the given fuse numbers in the iterator.
    pub fn write_custom_linebreaks<W, I>(&self, mut writer: W, linebreaks: I) -> fmt::Result
    where
        W: Write,
        I: Iterator<Item = usize>,
    {
        // FIXME: Un-hardcode the number of 0s in the fuse index

        write!(writer, "\x02")?;

        write!(writer, "QF{}*\n", self.f.len())?;
        //         if let Some(ref dev_name_str) = self.dev_name_str {
        //             write!(writer, "N DEVICE {}*\n", dev_name_str)?;
        //         }
        write!(writer, "\n")?;

        let mut next_written_fuse = 0;
        for linebreak in linebreaks {
            // Write one line
            if next_written_fuse == linebreak {
                // One or more duplicate breaks.
                write!(writer, "\n")?;
            } else {
                write!(writer, "L{:06} ", next_written_fuse)?;
                for i in next_written_fuse..linebreak {
                    write!(writer, "{}", if self.f[i] { "1" } else { "0" })?;
                }
                write!(writer, "*\n")?;
                next_written_fuse = linebreak;
            }
        }

        // Last chunk
        if next_written_fuse < self.f.len() {
            write!(writer, "L{:06} ", next_written_fuse)?;
            for i in next_written_fuse..self.f.len() {
                write!(writer, "{}", if self.f[i] { "1" } else { "0" })?;
            }
            write!(writer, "*\n")?;
        }

        write!(writer, "\x030000\n")?;

        Ok(())
    }

    /// Writes the contents to a JEDEC file. Note that a `&mut Write` can also be passed as a writer. Line breaks
    /// happen every `break_inverval` fuses.
    pub fn write_with_linebreaks<W>(&self, writer: W, break_inverval: usize) -> fmt::Result
    where
        W: Write,
    {
        self.write_custom_linebreaks(writer, (0..self.f.len()).step_by(break_inverval).skip(1))
    }

    /// Writes the contents to a JEDEC file. Note that a `&mut Write` can also be passed as a writer. Line breaks
    /// default to once every 16 fuses.
    pub fn write<W>(&self, writer: W) -> fmt::Result
    where
        W: Write,
    {
        self.write_with_linebreaks(writer, 16)
    }

    // /// Constructs a fuse array with the given number of fuses
    // pub fn new(size: usize) -> Self {
    //     let f = BitVec::repeat(false, size);

    //     Self { f, notes: vec![] }
    // }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn read_no_stx() {
        let ret = JEDECFile::from_bytes(b"asdf", &ParseQuirks::new());

        assert_eq!(ret, Err(JedParserError::MissingSTX));
    }

    #[test]
    fn read_no_etx() {
        let ret = JEDECFile::from_bytes(b"asdf\x02fdsa", &ParseQuirks::new());

        assert_eq!(ret, Err(JedParserError::MissingETX));
    }

    #[test]
    fn read_no_csum() {
        let ret = JEDECFile::from_bytes(b"asdf\x02fdsa\x03", &ParseQuirks::new());
        assert_eq!(ret, Err(JedParserError::UnexpectedEnd));

        let ret = JEDECFile::from_bytes(b"asdf\x02fdsa\x03AAA", &ParseQuirks::new());
        assert_eq!(ret, Err(JedParserError::UnexpectedEnd));
    }

    #[test]
    fn read_bad_csum() {
        let ret = JEDECFile::from_bytes(b"asdf\x02fdsa\x03AAAA", &ParseQuirks::new());

        assert_eq!(ret, Err(JedParserError::BadFileChecksum));
    }

    #[test]
    fn read_malformed_csum() {
        let ret = JEDECFile::from_bytes(b"asdf\x02fdsa\x03AAAZ", &ParseQuirks::new());

        assert_eq!(ret, Err(JedParserError::InvalidCharacter));
    }

    #[test]
    fn read_no_f() {
        let ret = JEDECFile::from_bytes(b"\x02*QF1*\x030000", &ParseQuirks::new());

        assert_eq!(ret, Err(JedParserError::MissingF));
    }

    #[test]
    fn read_empty_no_fuses() {
        let ret = JEDECFile::from_bytes(b"\x02\x030000", &ParseQuirks::new()).unwrap();

        assert_eq!(ret.f, bitvec![]);
    }

    #[test]
    fn read_header_trailer() {
        let ret =
            JEDECFile::from_bytes(b"asdf\nfdsa\x02\x030000zzzzzz", &ParseQuirks::new()).unwrap();

        assert_eq!(ret.header, b"asdf\nfdsa");
        assert_eq!(ret.footer, b"zzzzzz");
    }

    #[test]
    fn read_design_spec() {
        let ret =
            JEDECFile::from_bytes(b"\x02hello world!\n*\x030000", &ParseQuirks::new()).unwrap();

        assert_eq!(ret.design_spec, b"hello world!\n");
    }

    #[test]
    fn read_bogus_f_command() {
        let ret = JEDECFile::from_bytes(b"\x02*F2*\x030000", &ParseQuirks::new());

        assert_eq!(ret, Err(JedParserError::InvalidCharacter));
    }

    #[test]
    fn read_notes() {
        let ret = JEDECFile::from_bytes(
            b"\x02*Note test1*  N DEVICE asdf*  Note 3 \r  \x030000",
            &ParseQuirks::new(),
        )
        .unwrap();

        assert_eq!(
            ret.notes,
            vec![b"ote test1".as_slice(), b" DEVICE asdf", b"ote 3 \r  "]
        );
    }

    #[test]
    fn read_l_without_qf() {
        let ret = JEDECFile::from_bytes(b"\x02*L0 0*\x030000", &ParseQuirks::new());

        assert_eq!(ret, Err(JedParserError::MissingQF));
    }

    #[test]
    fn read_one_fuse() {
        let ret = JEDECFile::from_bytes(b"\x02*QF1*L0 1*\x030000", &ParseQuirks::new()).unwrap();

        assert_eq!(ret.f, bitvec![1]);
    }

    #[test]
    fn read_no_spec_quirk() {
        let ret = JEDECFile::from_bytes(
            b"\x02QF69420*QF1*L0 1*\x030000",
            &ParseQuirks::new().no_design_spec(true),
        )
        .unwrap();

        assert_eq!(ret.f, bitvec![1]);
    }

    #[test]
    fn read_one_fuse_csum_good() {
        let ret =
            JEDECFile::from_bytes(b"\x02*QF1*L0 1*C0001*\x030000", &ParseQuirks::new()).unwrap();

        assert_eq!(ret.f, bitvec![1]);
    }

    #[test]
    fn read_one_fuse_csum_bad() {
        let ret = JEDECFile::from_bytes(b"\x02*QF1*L0 1*C0002*\x030000", &ParseQuirks::new());

        assert_eq!(ret, Err(JedParserError::BadFuseChecksum));
    }

    #[test]
    fn read_two_fuses_space() {
        let ret = JEDECFile::from_bytes(b"\x02*QF2*L 0 0 1*\x030000", &ParseQuirks::new()).unwrap();

        assert_eq!(ret.f, bitvec![0, 1]);
    }
}
