#![no_std]

//! JEDEC programming file format parser and writer

use bitvec::prelude::*;

#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "alloc")]
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

#[cfg(feature = "std")]
impl std::error::Error for JedParserError {}

impl fmt::Display for JedParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            JedParserError::MissingSTX => write!(f, "STX not found"),
            JedParserError::MissingETX => write!(f, "ETX not found"),
            JedParserError::InvalidCharacter => write!(f, "invalid character in field"),
            JedParserError::UnexpectedEnd => write!(f, "unexpected end of file"),
            JedParserError::BadFileChecksum => write!(f, "invalid file checksum"),
            JedParserError::BadFuseChecksum => write!(f, "invalid fuse checksum"),
            JedParserError::InvalidFuseIndex => write!(f, "invalid fuse index value"),
            JedParserError::MissingQF => write!(f, "missing QF field"),
            JedParserError::MissingF => write!(f, "missing F field"),
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
pub struct JEDECFile<
    FuseArray: AsRef<BitSlice>,
    StringBits: AsRef<[u8]>,
    NotesList: AsRef<[StringBits]>,
> {
    /// Fuse array
    pub f: FuseArray,
    /// Data that appears before the STX byte
    pub header: StringBits,
    /// Data that appears after the ETX byte
    pub footer: StringBits,
    /// Design specification field
    pub design_spec: StringBits,
    /// Parsed N (Note) commands. This does _not_ round-trip.
    /// When writing, all notes will be written before all fuses
    pub notes: NotesList,
    /// Security `G` fuse
    pub secure_fuse: Option<bool>,
}

/// Abstract over memory regions including those which cannot implement [IndexMut](core::ops::IndexMut) (e.g. [BitSlice])
pub trait MemoryBuffer<T> {
    /// Get some memory
    fn get(&self, idx: usize) -> T;
    /// Write some memory
    fn set(&mut self, idx: usize, val: T);
    /// Assert that we have at least this much memory
    ///
    /// For growable memory such as Vec, initialize the memory with `fill`
    fn assert_capacity(&mut self, capacity: usize, fill: T);
}
impl<T, B: MemoryBuffer<T> + ?Sized> MemoryBuffer<T> for &mut B {
    fn get(&self, idx: usize) -> T {
        (**self).get(idx)
    }
    fn set(&mut self, idx: usize, val: T) {
        (**self).set(idx, val)
    }
    fn assert_capacity(&mut self, capacity: usize, fill: T) {
        (**self).assert_capacity(capacity, fill);
    }
}
impl<T: Copy> MemoryBuffer<T> for [T] {
    fn get(&self, idx: usize) -> T {
        self[idx]
    }
    fn set(&mut self, idx: usize, val: T) {
        self[idx] = val;
    }
    fn assert_capacity(&mut self, capacity: usize, _fill: T) {
        assert!(capacity <= self.len());
    }
}
impl MemoryBuffer<bool> for BitSlice {
    fn get(&self, idx: usize) -> bool {
        self[idx]
    }
    fn set(&mut self, idx: usize, val: bool) {
        self.set(idx, val);
    }
    fn assert_capacity(&mut self, capacity: usize, _fill: bool) {
        assert!(capacity <= self.len());
    }
}
#[cfg(feature = "alloc")]
impl<T: Copy> MemoryBuffer<T> for Vec<T> {
    fn get(&self, idx: usize) -> T {
        self[idx]
    }
    fn set(&mut self, idx: usize, val: T) {
        self[idx] = val;
    }
    fn assert_capacity(&mut self, capacity: usize, fill: T) {
        if capacity > self.len() {
            self.resize(capacity, fill);
        }
    }
}
#[cfg(feature = "alloc")]
impl MemoryBuffer<bool> for BitVec {
    fn get(&self, idx: usize) -> bool {
        self[idx]
    }
    fn set(&mut self, idx: usize, val: bool) {
        BitSlice::set(self, idx, val);
    }
    fn assert_capacity(&mut self, capacity: usize, fill: bool) {
        if capacity > self.len() {
            self.resize(capacity, fill);
        }
    }
}

fn trim_slice_start(mut in_: &[u8]) -> &[u8] {
    while in_.len() > 0 {
        if let b' ' | b'\r' | b'\n' = in_[0] {
            in_ = &in_[1..];
        } else {
            break;
        }
    }
    in_
}

fn trim_slice_end(mut in_: &[u8]) -> &[u8] {
    while in_.len() > 0 {
        if let b' ' | b'\r' | b'\n' = in_[in_.len() - 1] {
            in_ = &in_[..in_.len() - 1];
        } else {
            break;
        }
    }
    in_
}

fn trim_slice(in_: &[u8]) -> &[u8] {
    trim_slice_end(trim_slice_start(in_))
}

const fn width_calc(len: usize) -> usize {
    if len == 0 {
        1
    } else {
        len.ilog10() as usize + 1
    }
}

/// Used to abstract over write sinks to share code
enum MyWriter<'a> {
    Slice(&'a mut [u8]),
    Fmt(&'a mut dyn fmt::Write),
    #[cfg(feature = "std")]
    Io(&'a mut dyn std::io::Write),
}
impl<'a> MyWriter<'a> {
    fn write_fmt(&mut self, fmt: fmt::Arguments<'_>) -> Result<(), MyWriterError> {
        match self {
            MyWriter::Slice(ref mut s) => {
                struct SliceWrap<'a>(&'a mut [u8]);
                impl<'a> fmt::Write for SliceWrap<'a> {
                    fn write_str(&mut self, s: &str) -> fmt::Result {
                        let s_bytes = s.as_bytes();
                        self.0[..s_bytes.len()].copy_from_slice(s_bytes);

                        let slice = core::mem::replace(&mut self.0, &mut []);
                        self.0 = &mut slice[s_bytes.len()..];

                        Ok(())
                    }
                }

                let mut wrap: SliceWrap<'a> = SliceWrap(core::mem::replace(s, &mut []));
                wrap.write_fmt(fmt).unwrap();
                *s = wrap.0;

                Ok(())
            }
            MyWriter::Fmt(w) => w.write_fmt(fmt).map_err(|e| MyWriterError::Fmt(e)),
            #[cfg(feature = "std")]
            MyWriter::Io(w) => w.write_fmt(fmt).map_err(|e| MyWriterError::Io(e)),
        }
    }

    fn write_bytes(&mut self, bytes: &[u8]) -> Result<(), MyWriterError> {
        match self {
            MyWriter::Slice(ref mut s) => {
                s[..bytes.len()].copy_from_slice(bytes);

                // xxx wtf, stolen from resize-slice crate
                let slice = core::mem::replace(s, &mut []);
                *s = &mut slice[bytes.len()..];

                Ok(())
            }
            MyWriter::Fmt(w) => w
                .write_str(str::from_utf8(bytes).unwrap())
                .map_err(|e| MyWriterError::Fmt(e)),
            #[cfg(feature = "std")]
            MyWriter::Io(w) => w.write(bytes).map(|_| ()).map_err(|e| MyWriterError::Io(e)),
        }
    }
}
/// Used to abstract over write sinks to share code
#[derive(Debug)]
enum MyWriterError {
    Fmt(fmt::Error),
    #[cfg(feature = "std")]
    Io(std::io::Error),
}
impl From<MyWriterError> for fmt::Error {
    fn from(value: MyWriterError) -> Self {
        #[allow(irrefutable_let_patterns)]
        if let MyWriterError::Fmt(e) = value {
            e
        } else {
            unreachable!()
        }
    }
}
#[cfg(feature = "std")]
impl From<MyWriterError> for std::io::Error {
    fn from(value: MyWriterError) -> Self {
        if let MyWriterError::Io(e) = value {
            e
        } else {
            unreachable!()
        }
    }
}

impl<
        'a,
        FuseArray: AsRef<BitSlice> + AsMut<BitSlice> + MemoryBuffer<bool>,
        NotesList: AsRef<[&'a [u8]]> + AsMut<[&'a [u8]]> + MemoryBuffer<&'a [u8]>,
    > JEDECFile<FuseArray, &'a [u8], NotesList>
{
    fn read_common(
        in_bytes: &'a [u8],
        quirks: &Quirks,
        // storage to write into
        mut notes: NotesList,
        mut fuses: FuseArray,
        mut fuses_written: FuseArray,
    ) -> Result<Self, JedParserError> {
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
        let mut default_fuse = None;
        let mut vecs_alloced = false;
        let mut num_notes = 0;
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
                    notes.assert_capacity(num_notes + 1, &[]);
                    notes.as_mut().set(num_notes, &l[1..]);
                    num_notes += 1;
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
                            fuses.assert_capacity(num_fuses, default_fuse);
                        } else {
                            fuses.assert_capacity(num_fuses, false);
                            fuses_written.assert_capacity(num_fuses, false);
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
                                fuses.as_mut().set(fuse_idx, false);
                                if default_fuse.is_none() {
                                    fuses_written.as_mut().set(fuse_idx, true);
                                }
                                fuse_idx += 1;
                            }
                            b'1' => {
                                if fuse_idx >= num_fuses {
                                    return Err(JedParserError::InvalidFuseIndex);
                                }
                                fuses.as_mut().set(fuse_idx, true);
                                if default_fuse.is_none() {
                                    fuses_written.as_mut().set(fuse_idx, true);
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
            if !fuses_written.as_ref()[..num_fuses].all() {
                return Err(JedParserError::MissingF);
            }
        }

        // Fuse checksum
        let mut fuse_csum = Wrapping(0u16);
        if let Some(fuse_expected_csum) = fuse_expected_csum {
            for i in 0..num_fuses {
                if fuses.as_ref()[i as usize] {
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
            header: header,
            footer: footer,
            design_spec: design_spec,
            notes,
            secure_fuse,
        })
    }
}

impl<'inp, 'out> JEDECFile<&'out mut BitSlice, &'inp [u8], &'out mut [&'inp [u8]]> {
    /// Reads a .jed file into preallocated memory buffers
    pub fn read_into_buffers(
        in_bytes: &'inp [u8],
        quirks: &Quirks,
        // storage to write into
        notes: &'out mut [&'inp [u8]],
        fuses: &'out mut BitSlice,
        fuses_written: &'out mut BitSlice,
    ) -> Result<Self, JedParserError> {
        JEDECFile::read_common(in_bytes, quirks, notes, fuses, fuses_written)
    }
}

#[cfg(feature = "alloc")]
impl<'inp> JEDECFile<BitVec, &'inp [u8], Vec<&'inp [u8]>> {
    /// Reads a .jed file into dynamically allocated memory
    pub fn read_into_vecs(in_bytes: &'inp [u8], quirks: &Quirks) -> Result<Self, JedParserError> {
        JEDECFile::read_common(in_bytes, quirks, Vec::new(), BitVec::new(), BitVec::new())
    }
}

impl<FuseArray: AsRef<BitSlice>, StringBits: AsRef<[u8]>, NotesList: AsRef<[StringBits]>>
    JEDECFile<FuseArray, StringBits, NotesList>
{
    fn write_common<I: Iterator<Item = usize>>(
        &self,
        mut writer: MyWriter,
        quirks: &Quirks,
        linebreaks: I,
    ) -> Result<(), MyWriterError> {
        // FIXME: The number of 0s in the fuse index isn't minimal because of linebreaks

        writer.write_bytes(self.header.as_ref())?;
        write!(writer, "\x02")?;

        if !quirks.no_design_spec {
            writer.write_bytes(self.design_spec.as_ref())?;
            write!(writer, "*\n")?;
        }

        if let Some(secure_fuse) = self.secure_fuse {
            write!(writer, "G{}*\n", if secure_fuse { "1" } else { "0" })?;
        }
        write!(writer, "QF{}*\n", self.f.as_ref().len())?;
        write!(writer, "\n")?;

        for note in self.notes.as_ref() {
            write!(writer, "N")?;
            writer.write_bytes(note.as_ref())?;
            write!(writer, "*\n")?;
        }
        if self.notes.as_ref().len() > 0 {
            write!(writer, "\n")?;
        }

        let fuse_idx_width = width_calc(self.f.as_ref().len());

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
                    write!(writer, "{}", if self.f.as_ref()[i] { "1" } else { "0" })?;
                }
                write!(writer, "*\n")?;
                next_written_fuse = linebreak;
            }
        }

        // Last chunk
        if next_written_fuse < self.f.as_ref().len() {
            write!(
                writer,
                "L{:0width$} ",
                next_written_fuse,
                width = fuse_idx_width
            )?;
            for i in next_written_fuse..self.f.as_ref().len() {
                write!(writer, "{}", if self.f.as_ref()[i] { "1" } else { "0" })?;
            }
            write!(writer, "*\n")?;
        }

        write!(writer, "\x030000\n")?;
        writer.write_bytes(self.footer.as_ref())?;

        Ok(())
    }

    /// Writes the contents to a JEDEC file. Linebreaks will be inserted at
    /// the fuse indices returned by the `linebreaks` iterator.
    pub fn write_fmt_custom_linebreaks<W, I>(
        &self,
        mut writer: W,
        quirks: &Quirks,
        linebreaks: I,
    ) -> fmt::Result
    where
        W: fmt::Write,
        I: Iterator<Item = usize>,
    {
        self.write_common(MyWriter::Fmt(&mut writer), quirks, linebreaks)
            .map_err(|e| e.into())
    }

    /// Writes the contents to a JEDEC file. Fuses will be broken up into
    /// lines of `break_interval` fuses each.
    pub fn write_fmt_with_linebreaks<W>(
        &self,
        writer: W,
        quirks: &Quirks,
        break_inverval: usize,
    ) -> fmt::Result
    where
        W: fmt::Write,
    {
        self.write_fmt_custom_linebreaks(
            writer,
            quirks,
            (0..self.f.as_ref().len()).step_by(break_inverval).skip(1),
        )
    }

    /// Writes the contents to a JEDEC file. Fuses will be broken up into
    /// lines of 16 fuses each.
    pub fn write_fmt<W>(&self, writer: W, quirks: &Quirks) -> fmt::Result
    where
        W: fmt::Write,
    {
        self.write_fmt_with_linebreaks(writer, quirks, 16)
    }

    /// Writes the contents to a JEDEC file. Linebreaks will be inserted at
    /// the fuse indices returned by the `linebreaks` iterator.
    pub fn write_preallocated_custom_linebreaks<I>(
        &self,
        writer: &mut [u8],
        quirks: &Quirks,
        linebreaks: I,
    ) where
        I: Iterator<Item = usize>,
    {
        self.write_common(MyWriter::Slice(writer), quirks, linebreaks)
            .unwrap();
    }

    /// Writes the contents to a JEDEC file. Fuses will be broken up into
    /// lines of `break_interval` fuses each.
    pub fn write_preallocated_with_linebreaks(
        &self,
        writer: &mut [u8],
        quirks: &Quirks,
        break_inverval: usize,
    ) {
        self.write_preallocated_custom_linebreaks(
            writer,
            quirks,
            (0..self.f.as_ref().len()).step_by(break_inverval).skip(1),
        )
    }

    /// Writes the contents to a JEDEC file. Fuses will be broken up into
    /// lines of 16 fuses each.
    pub fn write_preallocated(&self, writer: &mut [u8], quirks: &Quirks) {
        self.write_preallocated_with_linebreaks(writer, quirks, 16)
    }
}

#[cfg(feature = "std")]
impl<FuseArray: AsRef<BitSlice>, StringBits: AsRef<[u8]>, NotesList: AsRef<[StringBits]>>
    JEDECFile<FuseArray, StringBits, NotesList>
{
    /// Writes the contents to a JEDEC file. Linebreaks will be inserted at
    /// the fuse indices returned by the `linebreaks` iterator.
    pub fn write_io_custom_linebreaks<W, I>(
        &self,
        mut writer: W,
        quirks: &Quirks,
        linebreaks: I,
    ) -> std::io::Result<()>
    where
        W: std::io::Write,
        I: Iterator<Item = usize>,
    {
        self.write_common(MyWriter::Io(&mut writer), quirks, linebreaks)
            .map_err(|e| e.into())
    }

    /// Writes the contents to a JEDEC file. Fuses will be broken up into
    /// lines of `break_interval` fuses each.
    pub fn write_io_with_linebreaks<W>(
        &self,
        writer: W,
        quirks: &Quirks,
        break_inverval: usize,
    ) -> std::io::Result<()>
    where
        W: std::io::Write,
    {
        self.write_io_custom_linebreaks(
            writer,
            quirks,
            (0..self.f.as_ref().len()).step_by(break_inverval).skip(1),
        )
    }

    /// Writes the contents to a JEDEC file. Fuses will be broken up into
    /// lines of 16 fuses each.
    pub fn write_io<W>(&self, writer: W, quirks: &Quirks) -> std::io::Result<()>
    where
        W: std::io::Write,
    {
        self.write_io_with_linebreaks(writer, quirks, 16)
    }
}

#[cfg(feature = "alloc")]
impl JEDECFile<BitVec, Vec<u8>, Vec<Vec<u8>>> {
    /// Constructs a fuse array with the given number of fuses
    pub fn new(size: usize) -> Self {
        let f = BitVec::repeat(false, size);

        Self {
            f,
            header: Vec::new(),
            footer: Vec::new(),
            design_spec: Vec::new(),
            notes: Vec::new(),
            secure_fuse: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(feature = "alloc")]
    use alloc::string::String;
    #[cfg(feature = "alloc")]
    use alloc::vec;

    #[cfg(feature = "alloc")]
    #[test]
    fn read_no_stx() {
        let ret = JEDECFile::read_into_vecs(b"asdf", &Quirks::new());

        assert_eq!(ret, Err(JedParserError::MissingSTX));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn read_no_etx() {
        let ret = JEDECFile::read_into_vecs(b"asdf\x02fdsa", &Quirks::new());

        assert_eq!(ret, Err(JedParserError::MissingETX));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn read_no_csum() {
        let ret = JEDECFile::read_into_vecs(b"asdf\x02fdsa\x03", &Quirks::new());
        assert_eq!(ret, Err(JedParserError::UnexpectedEnd));

        let ret = JEDECFile::read_into_vecs(b"asdf\x02fdsa\x03AAA", &Quirks::new());
        assert_eq!(ret, Err(JedParserError::UnexpectedEnd));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn read_bad_csum() {
        let ret = JEDECFile::read_into_vecs(b"asdf\x02fdsa\x03AAAA", &Quirks::new());

        assert_eq!(ret, Err(JedParserError::BadFileChecksum));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn read_malformed_csum() {
        let ret = JEDECFile::read_into_vecs(b"asdf\x02fdsa\x03AAAZ", &Quirks::new());

        assert_eq!(ret, Err(JedParserError::InvalidCharacter));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn read_no_f() {
        let ret = JEDECFile::read_into_vecs(b"\x02*QF1*\x030000", &Quirks::new());

        assert_eq!(ret, Err(JedParserError::MissingF));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn read_empty_no_fuses() {
        let ret = JEDECFile::read_into_vecs(b"\x02\x030000", &Quirks::new()).unwrap();

        assert_eq!(ret.f, bitvec![]);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn read_header_trailer() {
        let ret =
            JEDECFile::read_into_vecs(b"asdf\nfdsa\x02\x030000zzzzzz", &Quirks::new()).unwrap();

        assert_eq!(ret.header, b"asdf\nfdsa".as_slice());
        assert_eq!(ret.footer, b"zzzzzz".as_slice());
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn read_design_spec() {
        let ret =
            JEDECFile::read_into_vecs(b"\x02hello world!\n*\x030000", &Quirks::new()).unwrap();

        assert_eq!(ret.design_spec, b"hello world!\n".as_slice());
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn read_bogus_f_command() {
        let ret = JEDECFile::read_into_vecs(b"\x02*F2*\x030000", &Quirks::new());

        assert_eq!(ret, Err(JedParserError::InvalidCharacter));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn read_notes() {
        let ret = JEDECFile::read_into_vecs(
            b"\x02*Note test1*  N DEVICE asdf*  Note 3 \r  \x030000",
            &Quirks::new(),
        )
        .unwrap();

        assert_eq!(
            ret.notes,
            vec![b"ote test1".as_slice(), b" DEVICE asdf", b"ote 3 \r  "]
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn read_l_without_qf() {
        let ret = JEDECFile::read_into_vecs(b"\x02*L0 0*\x030000", &Quirks::new());

        assert_eq!(ret, Err(JedParserError::MissingQF));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn read_one_fuse() {
        let ret = JEDECFile::read_into_vecs(b"\x02*QF1*L0 1*\x030000", &Quirks::new()).unwrap();

        assert_eq!(ret.f, bitvec![1]);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn read_no_spec_quirk() {
        let ret = JEDECFile::read_into_vecs(
            b"\x02QF69420*QF1*L0 1*\x030000",
            &Quirks::new().no_design_spec(true),
        )
        .unwrap();

        assert_eq!(ret.f, bitvec![1]);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn read_one_fuse_csum_good() {
        let ret =
            JEDECFile::read_into_vecs(b"\x02*QF1*L0 1*C0001*\x030000", &Quirks::new()).unwrap();

        assert_eq!(ret.f, bitvec![1]);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn read_one_fuse_csum_bad() {
        let ret = JEDECFile::read_into_vecs(b"\x02*QF1*L0 1*C0002*\x030000", &Quirks::new());

        assert_eq!(ret, Err(JedParserError::BadFuseChecksum));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn read_two_fuses_space() {
        let ret = JEDECFile::read_into_vecs(b"\x02*QF2*L 0 0 1*\x030000", &Quirks::new()).unwrap();

        assert_eq!(ret.f, bitvec![0, 1]);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn read_secure_fuse() {
        let ret = JEDECFile::read_into_vecs(b"\x02*\x030000", &Quirks::new()).unwrap();
        assert_eq!(ret.secure_fuse, None);
        let ret = JEDECFile::read_into_vecs(b"\x02*G0*\x030000", &Quirks::new()).unwrap();
        assert_eq!(ret.secure_fuse, Some(false));
        let ret = JEDECFile::read_into_vecs(b"\x02*G1*\x030000", &Quirks::new()).unwrap();
        assert_eq!(ret.secure_fuse, Some(true));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn write_empty() {
        let x = JEDECFile::new(0);

        let mut out = String::new();
        x.write_fmt(&mut out, &Quirks::new()).unwrap();

        assert_eq!(
            out,
            "\x02*
QF0*

\x030000
"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn write_nine_fuses() {
        let mut x = JEDECFile::new(9);
        x.f.set(1, true);
        x.f.set(8, true);

        let mut out = String::new();
        x.write_fmt(&mut out, &Quirks::new()).unwrap();

        assert_eq!(
            out,
            "\x02*
QF9*

L0 010000001*
\x030000
"
        );
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn write_nine_fuses_linebreaks() {
        let mut x = JEDECFile::new(9);
        x.f.set(1, true);
        x.f.set(8, true);

        let mut out = String::new();
        x.write_fmt_with_linebreaks(&mut out, &Quirks::new(), 4)
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

    #[cfg(feature = "alloc")]
    #[test]
    fn write_nine_fuses_linebreaks2() {
        let mut x = JEDECFile::new(9);
        x.f.set(1, true);
        x.f.set(8, true);

        let mut out = String::new();
        x.write_fmt_with_linebreaks(&mut out, &Quirks::new(), 3)
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

    #[cfg(feature = "alloc")]
    #[test]
    fn write_with_human_noise() {
        let mut x = JEDECFile::new(100);
        x.header = (b"this is a header\n").to_vec();
        x.footer = (b"this is a footer").to_vec();
        x.design_spec = (b"this design is for a blah blah blah device").to_vec();
        x.notes = vec![(b"lolol note 1").to_vec(), (b"lolol note 2").to_vec()];

        let mut out = String::new();
        x.write_fmt(&mut out, &Quirks::new()).unwrap();

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
        x.write_fmt(&mut out, &Quirks::new().no_design_spec(true))
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

    #[cfg(feature = "std")]
    #[test]
    fn write_io_nonutf8() {
        let mut x = JEDECFile::new(100);
        x.header = (b"this\xFF is a header\n").to_vec();
        x.footer = (b"this is a footer").to_vec();
        x.design_spec = (b"this design is for a blah blah blah device").to_vec();
        x.notes = vec![(b"lolol note 1").to_vec(), (b"lolol note 2").to_vec()];

        let mut out: Vec<u8> = Vec::new();
        x.write_io(&mut out, &Quirks::new()).unwrap();

        assert_eq!(
            out,
            b"this\xFF is a header
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
    }

    #[test]
    fn test_completely_no_allocation_read() {
        let mut fuses = bitarr![0; 2];
        let mut fuses_written = bitarr![0; 2];
        let mut notes: [&[u8]; 1] = [&[]; 1];

        let ret = JEDECFile::read_into_buffers(
            b"\x02*QF2*L 0 0 1*\x030000",
            &Quirks::new(),
            &mut notes,
            &mut fuses,
            &mut fuses_written,
        )
        .unwrap();

        assert_eq!(ret.f[..2], bits![0, 1]);
    }

    #[test]
    fn test_completely_no_allocation_write() {
        let x = JEDECFile {
            f: bits![0; 100],
            header: b"this is a header\n" as &[u8],
            footer: b"this is a footer" as &[u8],
            design_spec: b"this design is for a blah blah blah device" as &[u8],
            notes: [b"lolol note 1" as &[u8], b"lolol note 2" as &[u8]],
            secure_fuse: None,
        };

        let mut out = [0; 272];
        x.write_preallocated(&mut out, &Quirks::new());

        assert_eq!(
            &out,
            b"this is a header
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
    }
}
