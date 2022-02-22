//! JEDEC programming file format parser and writer

#![no_std]
extern crate alloc;

use bitvec::prelude::*;

use alloc::borrow::Cow;
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
    /// A field contains a character not appropriate for that field
    /// (e.g. non-ASCII character, non-hex digit in a hex field)
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
}

#[cfg(std)]
impl std::error::Error for JedParserError {}

impl fmt::Display for JedParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &JedParserError::MissingSTX => write!(f, "STX not found"),
            &JedParserError::MissingETX => write!(f, "ETX not found"),
            &JedParserError::InvalidCharacter => write!(f, "invalid character in field"),
            &JedParserError::UnexpectedEnd => write!(f, "unexpected end of file"),
            &JedParserError::BadFileChecksum => write!(f, "invalid file checksum"),
            &JedParserError::BadFuseChecksum => write!(f, "invalid fuse checksum"),
            &JedParserError::InvalidFuseIndex => write!(f, "invalid fuse index value"),
            &JedParserError::MissingQF => write!(f, "missing QF field"),
            &JedParserError::MissingF => write!(f, "missing F field"),
        }
    }
}

impl From<str::Utf8Error> for JedParserError {
    fn from(_: str::Utf8Error) -> Self {
        JedParserError::InvalidCharacter
    }
}

impl From<num::ParseIntError> for JedParserError {
    fn from(_: num::ParseIntError) -> Self {
        JedParserError::InvalidCharacter
    }
}

const STX: u8 = 0x02;
const ETX: u8 = 0x03;

/// Struct representing quirk options
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Quirks {
    no_design_spec: bool,
}

impl Quirks {
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

impl Default for Quirks {
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
    pub header: Cow<'a, [u8]>,
    /// Data that appears after the ETX byte
    pub footer: Cow<'a, [u8]>,
    /// Design specification field
    pub design_spec: Cow<'a, [u8]>,
    /// Parsed N (Note) commands. This does _not_ round-trip.
    /// When writing, all notes will be written before all fuses
    pub notes: Vec<Cow<'a, [u8]>>,
    /// Security `G` fuse
    pub secure_fuse: Option<bool>,
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

const fn width_calc(len: usize) -> usize {
    // needed because no_std has no log10
    match len {
        0..=9 => 1,
        10..=99 => 2,
        100..=999 => 3,
        1000..=9999 => 4,
        10000..=99999 => 5,
        100000..=999999 => 6,
        1000000..=9999999 => 7,
        10000000..=99999999 => 8,
        100000000..=999999999 => 9,
        1000000000..=9999999999 => 10,
        10000000000..=99999999999 => 11,
        100000000000..=999999999999 => 12,
        1000000000000..=9999999999999 => 13,
        10000000000000..=99999999999999 => 14,
        100000000000000..=999999999999999 => 15,
        1000000000000000..=9999999999999999 => 16,
        10000000000000000..=99999999999999999 => 17,
        100000000000000000..=999999999999999999 => 18,
        1000000000000000000..=9999999999999999999 => 19,
        10000000000000000000..=18446744073709551615 => 20,
        _ => unreachable!(),
    }
}

impl<'a> JEDECFile<'a> {
    /// Reads a .jed file
    pub fn from_bytes(in_bytes: &'a [u8], quirks: &Quirks) -> Result<Self, JedParserError> {
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

        // storage for various fields that get captured
        let mut notes = Vec::new();
        let mut secure_fuse = None;

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
                b'F' => {
                    // Default state
                    let default_state_str = trim_slice(&l[1..]);
                    default_fuse = Some(match default_state_str {
                        b"0" => false,
                        b"1" => true,
                        _ => return Err(JedParserError::InvalidCharacter),
                    });
                }
                b'G' => {
                    // Secure fuse
                    let secure_fuse_str = trim_slice(&l[1..]);
                    secure_fuse = Some(match secure_fuse_str {
                        b"0" => false,
                        b"1" => true,
                        _ => return Err(JedParserError::InvalidCharacter),
                    });
                }
                b'N' => {
                    // Notes
                    notes.push(Cow::Borrowed(&l[1..]));
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
                _ => {
                    // ignore unsupported fields
                }
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
            header: Cow::Borrowed(header),
            footer: Cow::Borrowed(footer),
            design_spec: Cow::Borrowed(design_spec),
            notes,
            secure_fuse,
        })
    }

    /// Writes the contents to a JEDEC file
    pub fn write_custom_linebreaks<W, I>(
        &self,
        mut writer: W,
        quirks: &Quirks,
        linebreaks: I,
    ) -> fmt::Result
    where
        W: Write,
        I: Iterator<Item = usize>,
    {
        // FIXME: The number of 0s in the fuse index isn't minimal because of linebreaks
        // FIXME: utf8 handing

        write!(writer, "{}", str::from_utf8(&self.header).unwrap())?;
        write!(writer, "\x02")?;

        if !quirks.no_design_spec {
            write!(writer, "{}*\n", str::from_utf8(&self.design_spec).unwrap())?;
        }

        if let Some(secure_fuse) = self.secure_fuse {
            write!(writer, "G{}*\n", if secure_fuse { "1" } else { "0" })?;
        }
        write!(writer, "QF{}*\n", self.f.len())?;
        write!(writer, "\n")?;

        for note in &self.notes {
            write!(writer, "N{}*\n", str::from_utf8(note).unwrap())?;
        }
        if self.notes.len() > 0 {
            write!(writer, "\n")?;
        }

        let fuse_idx_width = width_calc(self.f.len());

        let mut next_written_fuse = 0;
        for linebreak in linebreaks {
            // Write one line
            if next_written_fuse == linebreak {
                // One or more duplicate breaks.
                write!(writer, "\n")?;
            } else {
                write!(
                    writer,
                    "L{:0width$} ",
                    next_written_fuse,
                    width = fuse_idx_width
                )?;
                for i in next_written_fuse..linebreak {
                    write!(writer, "{}", if self.f[i] { "1" } else { "0" })?;
                }
                write!(writer, "*\n")?;
                next_written_fuse = linebreak;
            }
        }

        // Last chunk
        if next_written_fuse < self.f.len() {
            write!(
                writer,
                "L{:0width$} ",
                next_written_fuse,
                width = fuse_idx_width
            )?;
            for i in next_written_fuse..self.f.len() {
                write!(writer, "{}", if self.f[i] { "1" } else { "0" })?;
            }
            write!(writer, "*\n")?;
        }

        write!(writer, "\x030000\n")?;
        write!(writer, "{}", str::from_utf8(&self.footer).unwrap())?;

        Ok(())
    }

    /// Writes the contents to a JEDEC file
    pub fn write_with_linebreaks<W>(
        &self,
        writer: W,
        quirks: &Quirks,
        break_inverval: usize,
    ) -> fmt::Result
    where
        W: Write,
    {
        self.write_custom_linebreaks(
            writer,
            quirks,
            (0..self.f.len()).step_by(break_inverval).skip(1),
        )
    }

    /// Writes the contents to a JEDEC file
    pub fn write<W>(&self, writer: W, quirks: &Quirks) -> fmt::Result
    where
        W: Write,
    {
        self.write_with_linebreaks(writer, quirks, 16)
    }

    /// Constructs a fuse array with the given number of fuses
    pub fn new(size: usize) -> Self {
        let f = BitVec::repeat(false, size);

        Self {
            f,
            header: vec![].into(),
            footer: vec![].into(),
            design_spec: vec![].into(),
            notes: vec![],
            secure_fuse: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::String;

    #[test]
    fn read_no_stx() {
        let ret = JEDECFile::from_bytes(b"asdf", &Quirks::new());

        assert_eq!(ret, Err(JedParserError::MissingSTX));
    }

    #[test]
    fn read_no_etx() {
        let ret = JEDECFile::from_bytes(b"asdf\x02fdsa", &Quirks::new());

        assert_eq!(ret, Err(JedParserError::MissingETX));
    }

    #[test]
    fn read_no_csum() {
        let ret = JEDECFile::from_bytes(b"asdf\x02fdsa\x03", &Quirks::new());
        assert_eq!(ret, Err(JedParserError::UnexpectedEnd));

        let ret = JEDECFile::from_bytes(b"asdf\x02fdsa\x03AAA", &Quirks::new());
        assert_eq!(ret, Err(JedParserError::UnexpectedEnd));
    }

    #[test]
    fn read_bad_csum() {
        let ret = JEDECFile::from_bytes(b"asdf\x02fdsa\x03AAAA", &Quirks::new());

        assert_eq!(ret, Err(JedParserError::BadFileChecksum));
    }

    #[test]
    fn read_malformed_csum() {
        let ret = JEDECFile::from_bytes(b"asdf\x02fdsa\x03AAAZ", &Quirks::new());

        assert_eq!(ret, Err(JedParserError::InvalidCharacter));
    }

    #[test]
    fn read_no_f() {
        let ret = JEDECFile::from_bytes(b"\x02*QF1*\x030000", &Quirks::new());

        assert_eq!(ret, Err(JedParserError::MissingF));
    }

    #[test]
    fn read_empty_no_fuses() {
        let ret = JEDECFile::from_bytes(b"\x02\x030000", &Quirks::new()).unwrap();

        assert_eq!(ret.f, bitvec![]);
    }

    #[test]
    fn read_header_trailer() {
        let ret = JEDECFile::from_bytes(b"asdf\nfdsa\x02\x030000zzzzzz", &Quirks::new()).unwrap();

        assert_eq!(ret.header, b"asdf\nfdsa".as_slice());
        assert_eq!(ret.footer, b"zzzzzz".as_slice());
    }

    #[test]
    fn read_design_spec() {
        let ret = JEDECFile::from_bytes(b"\x02hello world!\n*\x030000", &Quirks::new()).unwrap();

        assert_eq!(ret.design_spec, b"hello world!\n".as_slice());
    }

    #[test]
    fn read_bogus_f_command() {
        let ret = JEDECFile::from_bytes(b"\x02*F2*\x030000", &Quirks::new());

        assert_eq!(ret, Err(JedParserError::InvalidCharacter));
    }

    #[test]
    fn read_notes() {
        let ret = JEDECFile::from_bytes(
            b"\x02*Note test1*  N DEVICE asdf*  Note 3 \r  \x030000",
            &Quirks::new(),
        )
        .unwrap();

        assert_eq!(
            ret.notes,
            vec![b"ote test1".as_slice(), b" DEVICE asdf", b"ote 3 \r  "]
        );
    }

    #[test]
    fn read_l_without_qf() {
        let ret = JEDECFile::from_bytes(b"\x02*L0 0*\x030000", &Quirks::new());

        assert_eq!(ret, Err(JedParserError::MissingQF));
    }

    #[test]
    fn read_one_fuse() {
        let ret = JEDECFile::from_bytes(b"\x02*QF1*L0 1*\x030000", &Quirks::new()).unwrap();

        assert_eq!(ret.f, bitvec![1]);
    }

    #[test]
    fn read_no_spec_quirk() {
        let ret = JEDECFile::from_bytes(
            b"\x02QF69420*QF1*L0 1*\x030000",
            &Quirks::new().no_design_spec(true),
        )
        .unwrap();

        assert_eq!(ret.f, bitvec![1]);
    }

    #[test]
    fn read_one_fuse_csum_good() {
        let ret = JEDECFile::from_bytes(b"\x02*QF1*L0 1*C0001*\x030000", &Quirks::new()).unwrap();

        assert_eq!(ret.f, bitvec![1]);
    }

    #[test]
    fn read_one_fuse_csum_bad() {
        let ret = JEDECFile::from_bytes(b"\x02*QF1*L0 1*C0002*\x030000", &Quirks::new());

        assert_eq!(ret, Err(JedParserError::BadFuseChecksum));
    }

    #[test]
    fn read_two_fuses_space() {
        let ret = JEDECFile::from_bytes(b"\x02*QF2*L 0 0 1*\x030000", &Quirks::new()).unwrap();

        assert_eq!(ret.f, bitvec![0, 1]);
    }

    #[test]
    fn read_secure_fuse() {
        let ret = JEDECFile::from_bytes(b"\x02*\x030000", &Quirks::new()).unwrap();
        assert_eq!(ret.secure_fuse, None);
        let ret = JEDECFile::from_bytes(b"\x02*G0*\x030000", &Quirks::new()).unwrap();
        assert_eq!(ret.secure_fuse, Some(false));
        let ret = JEDECFile::from_bytes(b"\x02*G1*\x030000", &Quirks::new()).unwrap();
        assert_eq!(ret.secure_fuse, Some(true));
    }

    #[test]
    fn write_empty() {
        let x = JEDECFile::new(0);

        let mut out = String::new();
        x.write(&mut out, &Quirks::new()).unwrap();

        assert_eq!(
            out,
            "\x02*
QF0*

\x030000
"
        );
    }

    #[test]
    fn write_nine_fuses() {
        let mut x = JEDECFile::new(9);
        x.f.set(1, true);
        x.f.set(8, true);

        let mut out = String::new();
        x.write(&mut out, &Quirks::new()).unwrap();

        assert_eq!(
            out,
            "\x02*
QF9*

L0 010000001*
\x030000
"
        );
    }

    #[test]
    fn write_nine_fuses_linebreaks() {
        let mut x = JEDECFile::new(9);
        x.f.set(1, true);
        x.f.set(8, true);

        let mut out = String::new();
        x.write_with_linebreaks(&mut out, &Quirks::new(), 4)
            .unwrap();

        assert_eq!(
            out,
            "\x02*
QF9*

L0 0100*
L4 0000*
L8 1*
\x030000
"
        );
    }

    #[test]
    fn write_nine_fuses_linebreaks2() {
        let mut x = JEDECFile::new(9);
        x.f.set(1, true);
        x.f.set(8, true);

        let mut out = String::new();
        x.write_with_linebreaks(&mut out, &Quirks::new(), 3)
            .unwrap();

        assert_eq!(
            out,
            "\x02*
QF9*

L0 010*
L3 000*
L6 001*
\x030000
"
        );
    }

    #[test]
    fn write_with_human_noise() {
        let mut x = JEDECFile::new(100);
        x.header = Cow::Borrowed(b"this is a header\n");
        x.footer = Cow::Borrowed(b"this is a footer");
        x.design_spec = Cow::Borrowed(b"this design is for a blah blah blah device");
        x.notes = vec![
            Cow::Borrowed(b"lolol note 1"),
            Cow::Borrowed(b"lolol note 2"),
        ];

        let mut out = String::new();
        x.write(&mut out, &Quirks::new()).unwrap();

        assert_eq!(
            out,
            "this is a header
\x02this design is for a blah blah blah device*
QF100*

Nlolol note 1*
Nlolol note 2*

L000 0000000000000000*
L016 0000000000000000*
L032 0000000000000000*
L048 0000000000000000*
L064 0000000000000000*
L080 0000000000000000*
L096 0000*
\x030000
this is a footer"
        );

        // make sure the quirk works
        let mut out = String::new();
        x.write(&mut out, &Quirks::new().no_design_spec(true))
            .unwrap();

        assert_eq!(
            out,
            "this is a header
\x02QF100*

Nlolol note 1*
Nlolol note 2*

L000 0000000000000000*
L016 0000000000000000*
L032 0000000000000000*
L048 0000000000000000*
L064 0000000000000000*
L080 0000000000000000*
L096 0000*
\x030000
this is a footer"
        );
    }
}
