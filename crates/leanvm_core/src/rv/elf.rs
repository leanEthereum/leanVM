//! Loading a [`Guest`]: a static RV64 ELF executable to a program's text, entry point
//! and RAM. Anything the machine could not run as the file means it to be run is
//! refused here, not discovered as a trap.

use super::{ADVICE_BASE, MAX_LOG_ADVICE, MAX_LOG_RAM, MAX_LOG_TEXT, ProgramError, RAM_BASE, TEXT_BASE};

/// What a program is made from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Guest {
    /// The text's words, the first at [`TEXT_BASE`].
    pub text: Vec<u32>,
    pub entry_pc: u64,
    /// RAM's first words.
    pub image: Vec<u64>,
    pub log_ram: usize,
    pub log_advice: usize,
}

/// Why a file is no guest.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ElfError {
    /// A field runs past the end of the file, or its offset wraps.
    #[error("not a leanVM guest: a field runs past the end of the file")]
    Truncated,
    /// Not a little-endian ELF64 file.
    #[error("not a leanVM guest: not a little-endian ELF64 file")]
    NotElf64,
    /// An ELF version or header size this loader does not read.
    #[error("not a leanVM guest: an unsupported ELF header")]
    UnsupportedHeader,
    /// A dynamic or position-independent executable, or one with thread-local storage.
    #[error("not a leanVM guest: not a static executable")]
    NotStatic,
    /// Not built for RISC-V.
    #[error("not a leanVM guest: built for machine {machine}, not RISC-V")]
    NotRiscV { machine: u16 },
    /// Built with compressed instructions, which rv64im does not have.
    #[error("not a leanVM guest: compressed instructions")]
    Compressed,
    /// Built for a hardware floating-point ABI.
    #[error("not a leanVM guest: a hardware float ABI")]
    FloatAbi,
    /// RISC-V header flags this machine does not support.
    #[error("not a leanVM guest: unsupported RISC-V flags {flags:#x}")]
    UnsupportedFlags { flags: u32 },
    /// The entry point is not an aligned instruction the file carries.
    #[error("not a leanVM guest: the entry point {entry:#x} is not a file-backed instruction")]
    EntryPoint { entry: u64 },
    /// A loaded segment is inconsistent: its sizes, alignment, overlap, or bytes the file lacks.
    #[error("not a leanVM guest: a malformed load segment")]
    MalformedSegment,
    /// An executable segment is also writable.
    #[error("not a leanVM guest: the executable segment at {vaddr:#x} is writable")]
    WritableText { vaddr: u64 },
    /// An executable segment lies outside the text region.
    #[error("not a leanVM guest: the executable segment at {vaddr:#x} is outside the text region")]
    TextOutsideRegion { vaddr: u64 },
    /// No executable segment.
    #[error("not a leanVM guest: no executable segment")]
    NoText,
    /// A data segment lies outside RAM.
    #[error("not a leanVM guest: the data segment at {vaddr:#x} is outside RAM")]
    DataOutsideRam { vaddr: u64 },
    /// A symbol the guests' linker script defines is missing.
    #[error("not a leanVM guest: no {symbol} symbol, so not linked with the guests' script")]
    MissingSymbol { symbol: &'static str },
    /// RAM is not a power of two of words, or does not hold the data.
    #[error("not a leanVM guest: RAM's size is not a power of two, or too small for the data")]
    RamSize,
    /// The advice region is not a power of two of words, or exceeds its bounds.
    #[error("not a leanVM guest: the advice region's size is not a power of two, or exceeds its bounds")]
    AdviceSize,
    /// The symbol table or its string table is malformed.
    #[error("not a leanVM guest: a malformed symbol table")]
    MalformedSymbols,
    /// The loaded text and RAM do not form a program.
    #[error("not a leanVM guest: {0}")]
    Program(ProgramError),
}

const ET_EXEC: u16 = 2;
const EM_RISCV: u16 = 243;
/// `e_flags`: compressed instructions, and the float ABIs.
const EF_RISCV_RVC: u32 = 1;
const EF_RISCV_FLOAT_ABI: u32 = 6;
const PT_LOAD: u32 = 1;
const PT_DYNAMIC: u32 = 2;
const PT_INTERP: u32 = 3;
const PT_TLS: u32 = 7;
const PF_X: u32 = 1;
const PF_W: u32 = 2;
const SHT_SYMTAB: u32 = 2;
const SHT_STRTAB: u32 = 3;

/// The symbols whose values are the ends of RAM and of the advice region, which the
/// linker script defines.
const RAM_END_SYMBOL: &str = "__stack_top";
const ADVICE_END_SYMBOL: &str = "__advice_top";

/// `base + offset`, which a malformed header can wrap: a wrapped address would name
/// a field inside the file that the header did not point at.
fn at(base: u64, offset: u64) -> Result<u64, ElfError> {
    base.checked_add(offset).ok_or(ElfError::Truncated)
}

/// Little-endian fields of `bytes`, every read checked.
struct Reader<'a>(&'a [u8]);

impl Reader<'_> {
    fn bytes(&self, at: u64, len: u64) -> Result<&[u8], ElfError> {
        let end = at.checked_add(len).filter(|&end| end <= self.0.len() as u64);
        end.map(|end| &self.0[at as usize..end as usize])
            .ok_or(ElfError::Truncated)
    }
    fn u16(&self, at: u64) -> Result<u16, ElfError> {
        Ok(u16::from_le_bytes(self.bytes(at, 2)?.try_into().unwrap()))
    }
    fn u32(&self, at: u64) -> Result<u32, ElfError> {
        Ok(u32::from_le_bytes(self.bytes(at, 4)?.try_into().unwrap()))
    }
    fn u64(&self, at: u64) -> Result<u64, ElfError> {
        Ok(u64::from_le_bytes(self.bytes(at, 8)?.try_into().unwrap()))
    }
}

/// `bytes` written at `offset` of a buffer of whole `WORD`-byte words, grown to hold them.
fn place<const WORD: usize>(buffer: &mut Vec<u8>, offset: u64, bytes: &[u8]) {
    let end = offset as usize + bytes.len();
    if buffer.len() < end {
        buffer.resize(end.next_multiple_of(WORD), 0);
    }
    buffer[offset as usize..end].copy_from_slice(bytes);
}

impl Guest {
    /// A static RV64 executable linked with the guests' linker script: its executable
    /// segments are the text, every other loaded segment is RAM's image, RAM ends
    /// where the script says the stack starts, and the advice region where it says.
    pub fn from_elf(elf: &[u8]) -> Result<Self, ElfError> {
        let r = Reader(elf);
        r.bytes(0, 64)?;
        // 64-bit, little-endian, version 1.
        if r.bytes(0, 7)? != [0x7f, b'E', b'L', b'F', 2, 1, 1] {
            return Err(ElfError::NotElf64);
        }
        if r.u16(16)? != ET_EXEC {
            return Err(ElfError::NotStatic);
        }
        let machine = r.u16(18)?;
        if machine != EM_RISCV {
            return Err(ElfError::NotRiscV { machine });
        }
        if r.u32(20)? != 1 || r.u16(52)? != 64 {
            return Err(ElfError::UnsupportedHeader);
        }
        let flags = r.u32(48)?;
        if flags & EF_RISCV_RVC != 0 {
            return Err(ElfError::Compressed);
        }
        if flags & EF_RISCV_FLOAT_ABI != 0 {
            return Err(ElfError::FloatAbi);
        }
        if flags != 0 {
            return Err(ElfError::UnsupportedFlags { flags });
        }
        let entry_pc = r.u64(24)?;
        if !entry_pc.is_multiple_of(4) {
            return Err(ElfError::EntryPoint { entry: entry_pc });
        }

        let (mut text, mut image) = (Vec::new(), Vec::new());
        let (phoff, phentsize, phnum) = (r.u64(32)?, r.u16(54)? as u64, r.u16(56)? as u64);
        if phentsize != 56 {
            return Err(ElfError::UnsupportedHeader);
        }
        r.bytes(phoff, phnum * phentsize)?;
        let mut segments = Vec::new();
        let mut entry_loaded = false;
        let mut data_end = RAM_BASE;

        // What a region may hold is capped by the map, but a buffer here is grown to a
        // segment's own address, so a handful of bytes at the top of a region would
        // allocate the whole of it. A program gets no more text and no more image than
        // its file carries: the rest would be zeros, which is no instruction and no data
        // the program did not write itself.
        let file_len = elf.len() as u64;
        for i in 0..phnum {
            let ph = at(phoff, i.checked_mul(phentsize).ok_or(ElfError::Truncated)?)?;
            let (kind, flags) = (r.u32(ph)?, r.u32(at(ph, 4)?)?);
            if matches!(kind, PT_DYNAMIC | PT_INTERP | PT_TLS) {
                return Err(ElfError::NotStatic);
            }
            if kind != PT_LOAD {
                continue;
            }
            let (offset, vaddr, filesz, memsz) = (
                r.u64(at(ph, 8)?)?,
                r.u64(at(ph, 16)?)?,
                r.u64(at(ph, 32)?)?,
                r.u64(at(ph, 40)?)?,
            );
            if filesz > memsz {
                return Err(ElfError::MalformedSegment);
            }
            let align = r.u64(at(ph, 48)?)?;
            if align > 1 && (!align.is_power_of_two() || vaddr % align != offset % align) {
                return Err(ElfError::MalformedSegment);
            }
            let end = vaddr.checked_add(memsz).ok_or(ElfError::MalformedSegment)?;
            let bytes = r.bytes(offset, filesz)?;
            if memsz != 0 {
                segments.push((vaddr, end));
            }
            if flags & PF_X != 0 {
                if flags & PF_W != 0 {
                    return Err(ElfError::WritableText { vaddr });
                }
                if vaddr < TEXT_BASE || vaddr % 4 != 0 || end > TEXT_BASE + (4 << MAX_LOG_TEXT) {
                    return Err(ElfError::TextOutsideRegion { vaddr });
                }
                if vaddr - TEXT_BASE + bytes.len() as u64 > file_len {
                    return Err(ElfError::MalformedSegment);
                }
                entry_loaded |= entry_pc >= vaddr
                    && entry_pc
                        .checked_add(4)
                        .is_some_and(|entry_end| entry_end <= vaddr + filesz);
                place::<4>(&mut text, vaddr - TEXT_BASE, bytes);
            } else {
                if vaddr < RAM_BASE || end > RAM_BASE + (8 << MAX_LOG_RAM) {
                    return Err(ElfError::DataOutsideRam { vaddr });
                }
                data_end = data_end.max(end);
                if !bytes.is_empty() {
                    if vaddr - RAM_BASE + bytes.len() as u64 > file_len {
                        return Err(ElfError::MalformedSegment);
                    }
                    place::<8>(&mut image, vaddr - RAM_BASE, bytes);
                }
            }
        }
        segments.sort_unstable();
        if segments.windows(2).any(|pair| pair[0].1 > pair[1].0) {
            return Err(ElfError::MalformedSegment);
        }
        if !entry_loaded {
            return Err(ElfError::EntryPoint { entry: entry_pc });
        }
        if text.is_empty() {
            return Err(ElfError::NoText);
        }

        let ram_end = symbol(&r, RAM_END_SYMBOL)?.ok_or(ElfError::MissingSymbol { symbol: RAM_END_SYMBOL })?;
        let ram_bytes = ram_end.wrapping_sub(RAM_BASE);
        if ram_end <= RAM_BASE || !ram_bytes.is_power_of_two() || ram_bytes < 8 {
            return Err(ElfError::RamSize);
        }
        if data_end > ram_end {
            return Err(ElfError::RamSize);
        }
        let log_ram = (ram_bytes / 8).trailing_zeros() as usize;
        let advice_end = symbol(&r, ADVICE_END_SYMBOL)?.ok_or(ElfError::MissingSymbol {
            symbol: ADVICE_END_SYMBOL,
        })?;
        let advice_bytes = advice_end.wrapping_sub(ADVICE_BASE);
        if advice_end <= ADVICE_BASE || !advice_bytes.is_power_of_two() || advice_bytes < 8 {
            return Err(ElfError::AdviceSize);
        }
        let log_advice = (advice_bytes / 8).trailing_zeros() as usize;
        if log_advice > MAX_LOG_ADVICE {
            return Err(ElfError::AdviceSize);
        }
        let text: Vec<u32> = text.as_chunks::<4>().0.iter().map(|&w| u32::from_le_bytes(w)).collect();
        let image: Vec<u64> = image
            .as_chunks::<8>()
            .0
            .iter()
            .map(|&w| u64::from_le_bytes(w))
            .collect();
        if log_ram > MAX_LOG_RAM || image.len() > 1 << log_ram {
            return Err(ElfError::RamSize);
        }
        Ok(Self {
            text,
            entry_pc,
            image,
            log_ram,
            log_advice,
        })
    }
}

/// The value of the symbol `name`, from the file's symbol table.
fn symbol(r: &Reader, name: &str) -> Result<Option<u64>, ElfError> {
    let name = name.as_bytes();
    let (shoff, shentsize, shnum) = (r.u64(40)?, r.u16(58)? as u64, r.u16(60)? as u64);
    if shentsize != 64 {
        return Err(ElfError::UnsupportedHeader);
    }
    r.bytes(shoff, shnum * shentsize)?;
    for i in 0..shnum {
        let sh = at(shoff, i.checked_mul(shentsize).ok_or(ElfError::Truncated)?)?;
        if r.u32(at(sh, 4)?)? != SHT_SYMTAB {
            continue;
        }
        let (offset, size, link, entsize) = (
            r.u64(at(sh, 24)?)?,
            r.u64(at(sh, 32)?)?,
            r.u32(at(sh, 40)?)? as u64,
            r.u64(at(sh, 56)?)?,
        );
        if entsize != 24 || !size.is_multiple_of(entsize) || link >= shnum {
            return Err(ElfError::MalformedSymbols);
        }
        r.bytes(offset, size)?;
        let strings = at(shoff, link * shentsize)?;
        if r.u32(at(strings, 4)?)? != SHT_STRTAB {
            return Err(ElfError::MalformedSymbols);
        }
        let (str_offset, str_size) = (r.u64(at(strings, 24)?)?, r.u64(at(strings, 32)?)?);
        r.bytes(str_offset, str_size)?;
        for s in 0..size / entsize {
            let sym = at(offset, s * entsize)?;
            let name_at = r.u32(sym)? as u64;
            if name_at + (name.len() as u64) < str_size
                && r.bytes(at(str_offset, name_at)?, name.len() as u64 + 1)? == [name, &[0]].concat()
            {
                return r.u64(at(sym, 8)?).map(Some);
            }
        }
    }
    Ok(None)
}
