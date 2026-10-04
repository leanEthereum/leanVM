//! Loading a guest: a static RV64 ELF executable to a program's text, entry point and RAM.
//!
//! Anything the machine could not run as the file means it is refused here.
//!
//! It is never discovered later as a trap.
//!
//! Loading reads the file in three passes:
//!
//! - the file header is checked;
//! - the executable segments become the text, the others RAM's image;
//! - two symbols give the ends of RAM and of the advice.

use super::program::ProgramError;
use super::region::Region;

/// What a program is made from: its undecoded text, entry point and memory sizes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Guest {
    /// The text's words, the first at the text's base.
    pub text: Vec<u32>,
    /// The address of the first instruction run.
    pub entry_pc: u64,
    /// RAM's first words.
    pub image: Vec<u64>,
    /// RAM holds 2^log_ram words.
    pub log_ram: usize,
    /// The advice holds 2^log_advice words.
    pub log_advice: usize,
}

impl Guest {
    /// The symbol whose value is the end of RAM, which the guests' linker script defines.
    const RAM_END_SYMBOL: &'static str = "__stack_top";

    /// The symbol whose value is the end of the advice, which the guests' linker script defines.
    const ADVICE_END_SYMBOL: &'static str = "__advice_top";

    /// The guest of a static RV64 executable linked with the guests' linker script.
    ///
    /// - Its executable segments are the text.
    /// - Every other load segment is RAM's image.
    /// - RAM ends where the script's stack starts.
    /// - The advice ends where the script says.
    ///
    /// # Errors
    ///
    /// Returns the first rule the file breaks.
    pub fn from_elf(elf: &[u8]) -> Result<Self, ElfError> {
        let file = ElfFile::new(elf);
        let header = file.header()?;
        let mut loaded = Loaded::new();

        // Place each load segment in the text or in RAM's image.
        for i in 0..header.program_header_count {
            let ph = ElfFile::record(header.program_headers, i, FileHeader::PROGRAM_HEADER_SIZE)?;
            if let Some(segment) = file.segment(ph)? {
                loaded.place(&segment, header.entry_pc, file.len())?;
            }
        }

        // Segments are disjoint, the entry point is loaded, and there is code.
        loaded.ranges.sort_unstable();
        if loaded.ranges.windows(2).any(|pair| pair[0].1 > pair[1].0) {
            return Err(ElfError::MalformedSegment);
        }
        if !loaded.entry_loaded {
            return Err(ElfError::EntryPoint { entry: header.entry_pc });
        }
        if loaded.text.is_empty() {
            return Err(ElfError::NoText);
        }

        // RAM ends at its symbol, a power of two of words holding every data segment.
        let ram_end = file.symbol(Self::RAM_END_SYMBOL)?.ok_or(ElfError::MissingSymbol {
            symbol: Self::RAM_END_SYMBOL,
        })?;
        let log_ram = Region::RAM
            .log_words_ending_at(ram_end)
            .filter(|_| loaded.data_end <= ram_end)
            .ok_or(ElfError::RamSize)?;

        // The advice ends at its symbol, a power of two of words.
        let advice_end = file.symbol(Self::ADVICE_END_SYMBOL)?.ok_or(ElfError::MissingSymbol {
            symbol: Self::ADVICE_END_SYMBOL,
        })?;
        let log_advice = Region::ADVICE
            .log_words_ending_at(advice_end)
            .ok_or(ElfError::AdviceSize)?;

        // The bytes as little-endian words.
        let text = loaded.text.as_chunks::<4>().0.iter().map(|&w| u32::from_le_bytes(w));
        let image = loaded.image.as_chunks::<8>().0.iter().map(|&w| u64::from_le_bytes(w));
        Ok(Self {
            text: text.collect(),
            entry_pc: header.entry_pc,
            image: image.collect(),
            log_ram,
            log_advice,
        })
    }
}

/// Why a file is no guest.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ElfError {
    /// A field runs past the end of the file, or its offset overflows.
    #[error("not a leanVM guest: a field runs past the end of the file")]
    Truncated,
    /// Not a little-endian ELF64 file.
    #[error("not a leanVM guest: not a little-endian ELF64 file")]
    NotElf64,
    /// An ELF version or a header size this loader does not read.
    #[error("not a leanVM guest: an unsupported ELF header")]
    UnsupportedHeader,
    /// A dynamic or position-independent executable, or one with thread-local storage.
    #[error("not a leanVM guest: not a static executable")]
    NotStatic,
    /// Not built for RISC-V.
    #[error("not a leanVM guest: built for machine {machine}, not RISC-V")]
    NotRiscV {
        /// The file's machine number.
        machine: u16,
    },
    /// Built with compressed instructions, which rv64im does not have.
    #[error("not a leanVM guest: compressed instructions")]
    Compressed,
    /// Built for a hardware floating-point ABI.
    #[error("not a leanVM guest: a hardware float ABI")]
    FloatAbi,
    /// RISC-V header flags this machine does not support.
    #[error("not a leanVM guest: unsupported RISC-V flags {flags:#x}")]
    UnsupportedFlags {
        /// The header's flags.
        flags: u32,
    },
    /// The entry point is not an aligned instruction the file carries.
    #[error("not a leanVM guest: the entry point {entry:#x} is not a file-backed instruction")]
    EntryPoint {
        /// The header's entry point.
        entry: u64,
    },
    /// A load segment is inconsistent: its sizes, its alignment, an overlap, or bytes the file lacks.
    #[error("not a leanVM guest: a malformed load segment")]
    MalformedSegment,
    /// An executable segment is also writable.
    #[error("not a leanVM guest: the executable segment at {vaddr:#x} is writable")]
    WritableText {
        /// The segment's address.
        vaddr: u64,
    },
    /// An executable segment lies outside the text region.
    #[error("not a leanVM guest: the executable segment at {vaddr:#x} is outside the text region")]
    TextOutsideRegion {
        /// The segment's address.
        vaddr: u64,
    },
    /// No executable segment.
    #[error("not a leanVM guest: no executable segment")]
    NoText,
    /// A data segment lies outside RAM.
    #[error("not a leanVM guest: the data segment at {vaddr:#x} is outside RAM")]
    DataOutsideRam {
        /// The segment's address.
        vaddr: u64,
    },
    /// A symbol the guests' linker script defines is missing.
    #[error("not a leanVM guest: no {symbol} symbol, so not linked with the guests' script")]
    MissingSymbol {
        /// The symbol's name.
        symbol: &'static str,
    },
    /// RAM is not a power of two of words, or does not hold the data.
    #[error("not a leanVM guest: RAM's size is not a power of two, or too small for the data")]
    RamSize,
    /// The advice is not a power of two of words, or exceeds its region.
    #[error("not a leanVM guest: the advice region's size is not a power of two, or exceeds its bounds")]
    AdviceSize,
    /// The symbol table or its string table is malformed.
    #[error("not a leanVM guest: a malformed symbol table")]
    MalformedSymbols,
    /// The loaded text and RAM form no program.
    #[error("not a leanVM guest: {0}")]
    Program(ProgramError),
}

/// An ELF file's bytes, every read checked against its length.
#[derive(Clone, Copy, Debug)]
struct ElfFile<'a>(&'a [u8]);

impl<'a> ElfFile<'a> {
    /// A symbol table section.
    const SHT_SYMTAB: u32 = 2;

    /// A string table section.
    const SHT_STRTAB: u32 = 3;

    /// The size of an ELF64 section header.
    const SECTION_HEADER_SIZE: u64 = 64;

    /// The size of an ELF64 symbol.
    const SYMBOL_SIZE: u64 = 24;

    /// The file of `bytes`.
    const fn new(bytes: &'a [u8]) -> Self {
        Self(bytes)
    }

    /// The file's length in bytes.
    const fn len(&self) -> u64 {
        self.0.len() as u64
    }

    /// The `len` bytes at offset `at`.
    ///
    /// # Errors
    ///
    /// Refuses a range past the end of the file, or one whose end overflows.
    fn bytes(&self, at: u64, len: u64) -> Result<&'a [u8], ElfError> {
        let end = at.checked_add(len).filter(|&end| end <= self.len());
        end.map(|end| &self.0[at as usize..end as usize])
            .ok_or(ElfError::Truncated)
    }

    /// The `u16` at offset `at`.
    fn u16(&self, at: u64) -> Result<u16, ElfError> {
        Ok(u16::from_le_bytes(self.array(at)?))
    }

    /// The `u32` at offset `at`.
    fn u32(&self, at: u64) -> Result<u32, ElfError> {
        Ok(u32::from_le_bytes(self.array(at)?))
    }

    /// The `u64` at offset `at`.
    fn u64(&self, at: u64) -> Result<u64, ElfError> {
        Ok(u64::from_le_bytes(self.array(at)?))
    }

    /// The `N` bytes at offset `at`.
    fn array<const N: usize>(&self, at: u64) -> Result<[u8; N], ElfError> {
        Ok(self.bytes(at, N as u64)?.try_into().expect("exactly N bytes"))
    }

    /// The offset `base + offset`, which a malformed header can make overflow.
    ///
    /// A wrapped offset would name a field the header never pointed at.
    fn at(base: u64, offset: u64) -> Result<u64, ElfError> {
        base.checked_add(offset).ok_or(ElfError::Truncated)
    }

    /// The offset of record `index` in a table of `size`-byte records at `base`.
    fn record(base: u64, index: u64, size: u64) -> Result<u64, ElfError> {
        Self::at(base, index.checked_mul(size).ok_or(ElfError::Truncated)?)
    }

    /// The file header, and the program header table's bounds.
    ///
    /// The checks run in a fixed order, so a broken file always gets the same error.
    ///
    /// # Errors
    ///
    /// Refuses anything but a little-endian ELF64 static RISC-V executable.
    ///
    /// Compressed instructions and hardware floats are refused too.
    fn header(&self) -> Result<FileHeader, ElfError> {
        // The whole header is in the file.
        self.bytes(0, FileHeader::SIZE as u64)?;

        // The magic, 64-bit, little-endian, version 1.
        if self.bytes(0, 7)? != [0x7f, b'E', b'L', b'F', 2, 1, 1] {
            return Err(ElfError::NotElf64);
        }

        // An executable at fixed addresses, for RISC-V.
        if self.u16(16)? != FileHeader::ET_EXEC {
            return Err(ElfError::NotStatic);
        }
        let machine = self.u16(18)?;
        if machine != FileHeader::EM_RISCV {
            return Err(ElfError::NotRiscV { machine });
        }

        // Version 1, whose header has the size this loader reads.
        if self.u32(20)? != 1 || self.u16(52)? != FileHeader::SIZE {
            return Err(ElfError::UnsupportedHeader);
        }

        // No compressed instructions, no hardware floats, no other flag.
        let flags = self.u32(48)?;
        if flags & FileHeader::EF_RISCV_RVC != 0 {
            return Err(ElfError::Compressed);
        }
        if flags & FileHeader::EF_RISCV_FLOAT_ABI != 0 {
            return Err(ElfError::FloatAbi);
        }
        if flags != 0 {
            return Err(ElfError::UnsupportedFlags { flags });
        }

        // An entry point on an instruction boundary.
        let entry_pc = self.u64(24)?;
        if !entry_pc.is_multiple_of(4) {
            return Err(ElfError::EntryPoint { entry: entry_pc });
        }

        // A program header table of 56-byte records, all of it in the file.
        let (program_headers, size, count) = (self.u64(32)?, self.u16(54)? as u64, self.u16(56)? as u64);
        if size != FileHeader::PROGRAM_HEADER_SIZE {
            return Err(ElfError::UnsupportedHeader);
        }
        self.bytes(program_headers, count * size)?;
        Ok(FileHeader {
            entry_pc,
            program_headers,
            program_header_count: count,
        })
    }

    /// The load segment of the program header at offset `ph`.
    ///
    /// Returns `None` for a header that loads nothing.
    ///
    /// # Errors
    ///
    /// Refuses a header that needs a runtime loader, and a load segment that is inconsistent.
    fn segment(&self, ph: u64) -> Result<Option<Segment<'a>>, ElfError> {
        // A static executable has nothing for a runtime loader to do.
        let (kind, flags) = (self.u32(ph)?, self.u32(Self::at(ph, 4)?)?);
        if matches!(kind, Segment::PT_DYNAMIC | Segment::PT_INTERP | Segment::PT_TLS) {
            return Err(ElfError::NotStatic);
        }
        if kind != Segment::PT_LOAD {
            return Ok(None);
        }

        // The file's bytes are a prefix of the segment.
        let field = |offset: u64| self.u64(Self::at(ph, offset)?);
        let (offset, vaddr, filesz, memsz) = (field(8)?, field(16)?, field(32)?, field(40)?);
        if filesz > memsz {
            return Err(ElfError::MalformedSegment);
        }

        // An alignment ties the address to the file offset, modulo itself.
        let align = field(48)?;
        if align > 1 && (!align.is_power_of_two() || vaddr % align != offset % align) {
            return Err(ElfError::MalformedSegment);
        }

        // The segment's end, and the bytes the file carries for it.
        let end = vaddr.checked_add(memsz).ok_or(ElfError::MalformedSegment)?;
        let bytes = self.bytes(offset, filesz)?;
        Ok(Some(Segment {
            flags,
            vaddr,
            end,
            bytes,
        }))
    }

    /// The value of the symbol `name`.
    ///
    /// Returns `None` if no symbol table defines it.
    ///
    /// # Errors
    ///
    /// Refuses a section table or a symbol table that is malformed or runs past the file.
    fn symbol(&self, name: &str) -> Result<Option<u64>, ElfError> {
        // The section header table: 64-byte records, all of it in the file.
        let name = name.as_bytes();
        let (sections, size, count) = (self.u64(40)?, self.u16(58)? as u64, self.u16(60)? as u64);
        if size != Self::SECTION_HEADER_SIZE {
            return Err(ElfError::UnsupportedHeader);
        }
        self.bytes(sections, count * size)?;

        for i in 0..count {
            // Only symbol tables hold symbols.
            let sh = Self::record(sections, i, size)?;
            if self.u32(Self::at(sh, 4)?)? != Self::SHT_SYMTAB {
                continue;
            }

            // The table: whole 24-byte symbols, and a link to its string table.
            let (offset, bytes, link, entsize) = (
                self.u64(Self::at(sh, 24)?)?,
                self.u64(Self::at(sh, 32)?)?,
                self.u32(Self::at(sh, 40)?)? as u64,
                self.u64(Self::at(sh, 56)?)?,
            );
            if entsize != Self::SYMBOL_SIZE || !bytes.is_multiple_of(entsize) || link >= count {
                return Err(ElfError::MalformedSymbols);
            }
            self.bytes(offset, bytes)?;

            // The linked section must be a string table, all of it in the file.
            let strings = Self::record(sections, link, size)?;
            if self.u32(Self::at(strings, 4)?)? != Self::SHT_STRTAB {
                return Err(ElfError::MalformedSymbols);
            }
            let (str_offset, str_size) = (self.u64(Self::at(strings, 24)?)?, self.u64(Self::at(strings, 32)?)?);
            self.bytes(str_offset, str_size)?;

            // A symbol matches when its name, then a terminating zero, lies in the string table.
            for s in 0..bytes / entsize {
                let sym = Self::record(offset, s, entsize)?;
                let name_at = self.u32(sym)? as u64;
                if name_at + (name.len() as u64) < str_size
                    && self.bytes(Self::at(str_offset, name_at)?, name.len() as u64 + 1)? == [name, &[0]].concat()
                {
                    return self.u64(Self::at(sym, 8)?).map(Some);
                }
            }
        }
        Ok(None)
    }
}

/// What the loader needs of a checked file header.
#[derive(Clone, Copy, Debug)]
struct FileHeader {
    /// The address of the first instruction run, aligned to 4.
    entry_pc: u64,
    /// The program header table's offset.
    program_headers: u64,
    /// The program header table's length.
    program_header_count: u64,
}

impl FileHeader {
    /// The size of an ELF64 file header.
    const SIZE: u16 = 64;

    /// The size of an ELF64 program header.
    const PROGRAM_HEADER_SIZE: u64 = 56;

    /// The file type of an executable at fixed addresses.
    const ET_EXEC: u16 = 2;

    /// The machine number of RISC-V.
    const EM_RISCV: u16 = 243;

    /// The header flag declaring compressed instructions.
    const EF_RISCV_RVC: u32 = 1;

    /// The header flags selecting a hardware floating-point ABI.
    const EF_RISCV_FLOAT_ABI: u32 = 6;
}

/// A load segment whose sizes, alignment and bytes are checked.
#[derive(Clone, Copy, Debug)]
struct Segment<'a> {
    /// Its permissions.
    flags: u32,
    /// The address of its first byte.
    vaddr: u64,
    /// The address one past its last byte in memory.
    end: u64,
    /// The bytes the file carries: a prefix of the segment, the rest being zeros.
    bytes: &'a [u8],
}

impl Segment<'_> {
    /// A loadable segment.
    const PT_LOAD: u32 = 1;

    /// Dynamic linking information, which needs a runtime loader.
    const PT_DYNAMIC: u32 = 2;

    /// An interpreter path, which needs a runtime loader.
    const PT_INTERP: u32 = 3;

    /// Thread-local storage, which needs runtime support.
    const PT_TLS: u32 = 7;

    /// The executable permission.
    const PF_X: u32 = 1;

    /// The writable permission.
    const PF_W: u32 = 2;

    /// Whether the segment holds code.
    const fn is_executable(&self) -> bool {
        self.flags & Self::PF_X != 0
    }

    /// Whether the segment may be written.
    const fn is_writable(&self) -> bool {
        self.flags & Self::PF_W != 0
    }
}

/// The segments placed so far.
#[derive(Debug)]
struct Loaded {
    /// The text's bytes, from the text's base, in whole instructions.
    text: Vec<u8>,
    /// RAM's image bytes, from RAM's base, in whole words.
    image: Vec<u8>,
    /// Every nonempty segment's address range, to check they are disjoint.
    ranges: Vec<(u64, u64)>,
    /// Whether a text segment's file bytes hold the entry point's instruction.
    entry_loaded: bool,
    /// The end of the highest data segment, at least RAM's base.
    data_end: u64,
}

impl Loaded {
    /// Nothing placed yet.
    const fn new() -> Self {
        Self {
            text: Vec::new(),
            image: Vec::new(),
            ranges: Vec::new(),
            entry_loaded: false,
            data_end: Region::RAM.base(),
        }
    }

    /// Place `segment` in the text or in RAM's image.
    ///
    /// A buffer grows to the segment's own address.
    ///
    /// So a few bytes at the top of a region would allocate the whole region.
    ///
    /// A segment's offset in its region may therefore not exceed the file's length.
    fn place(&mut self, segment: &Segment<'_>, entry_pc: u64, file_len: u64) -> Result<(), ElfError> {
        let Segment { vaddr, end, bytes, .. } = *segment;
        if end != vaddr {
            self.ranges.push((vaddr, end));
        }

        if segment.is_executable() {
            // Code is read-only, aligned, in the text region, and no larger than the file.
            if segment.is_writable() {
                return Err(ElfError::WritableText { vaddr });
            }
            if !vaddr.is_multiple_of(4) || !Region::TEXT.contains(vaddr..end) {
                return Err(ElfError::TextOutsideRegion { vaddr });
            }
            let offset = vaddr - Region::TEXT.base();
            if offset + bytes.len() as u64 > file_len {
                return Err(ElfError::MalformedSegment);
            }

            // The entry point's four bytes come from the file.
            let entry_end = entry_pc.checked_add(4);
            self.entry_loaded |= entry_pc >= vaddr && entry_end.is_some_and(|e| e <= vaddr + bytes.len() as u64);
            self.write_segment(segment);
        } else {
            // Data lies in RAM, and its file bytes are no larger than the file.
            if !Region::RAM.contains(vaddr..end) {
                return Err(ElfError::DataOutsideRam { vaddr });
            }
            self.data_end = self.data_end.max(end);
            if !bytes.is_empty() {
                let offset = vaddr - Region::RAM.base();
                if offset + bytes.len() as u64 > file_len {
                    return Err(ElfError::MalformedSegment);
                }
                self.write_segment(segment);
            }
        }
        Ok(())
    }

    /// Copy a checked segment into text or RAM, zero-filling gaps and rounding to whole words.
    fn write_segment(&mut self, segment: &Segment<'_>) {
        let (buffer, region) = if segment.is_executable() {
            (&mut self.text, Region::TEXT)
        } else {
            (&mut self.image, Region::RAM)
        };
        let offset = (segment.vaddr - region.base()) as usize;
        let end = offset + segment.bytes.len();
        if buffer.len() < end {
            buffer.resize(end.next_multiple_of(region.word_bytes() as usize), 0);
        }
        buffer[offset..end].copy_from_slice(segment.bytes);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn bytes_succeeds_exactly_inside_the_file(len in 0usize..64, at in any::<u64>(), n in any::<u64>()) {
            // Fixture: a file of `len` bytes.
            let bytes = vec![0u8; len];
            let file = ElfFile::new(&bytes);

            // A read succeeds exactly when it ends inside the file, without overflowing.
            let inside = at.checked_add(n).is_some_and(|end| end <= len as u64);
            prop_assert_eq!(file.bytes(at, n).is_ok(), inside);
        }
    }

    #[test]
    fn fields_are_little_endian() {
        // Fixture: eight bytes counting up.
        let bytes = [1u8, 2, 3, 4, 5, 6, 7, 8];
        let file = ElfFile::new(&bytes);

        // Each width reads its low bytes first.
        assert_eq!(file.u16(0), Ok(0x0201));
        assert_eq!(file.u32(4), Ok(0x0807_0605));
        assert_eq!(file.u64(0), Ok(0x0807_0605_0403_0201));

        // One byte short is truncated.
        assert_eq!(file.u64(1), Err(ElfError::Truncated));
    }
}
