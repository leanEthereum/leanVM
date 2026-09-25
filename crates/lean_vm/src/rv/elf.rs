//! Loading a [`Guest`]: a static RV64 ELF executable to a program's text, entry point
//! and RAM. Anything the machine could not run as the file means it to be run is
//! refused here, not discovered as a trap.

use super::{ADVICE_BASE, INPUT_WORDS, MAX_LOG_ADVICE, MAX_LOG_RAM, MAX_LOG_TEXT, RAM_BASE, TEXT_BASE};

/// What a program is made from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Guest {
    /// The text's words, the first at [`TEXT_BASE`].
    pub text: Vec<u32>,
    pub entry_pc: u64,
    /// RAM's words after the input's.
    pub image: Vec<u64>,
    pub log_ram: usize,
    pub log_advice: usize,
}

/// Why a file is no guest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ElfError(pub &'static str);

impl std::fmt::Display for ElfError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "not a leanVM guest: {}", self.0)
    }
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

/// The symbols whose values are the ends of RAM and of the advice region, which the
/// linker script defines.
const RAM_END_SYMBOL: &[u8] = b"__stack_top";
const ADVICE_END_SYMBOL: &[u8] = b"__advice_top";

/// `base + offset`, which a malformed header can wrap: a wrapped address would name
/// a field inside the file that the header did not point at.
fn at(base: u64, offset: u64) -> Result<u64, ElfError> {
    base.checked_add(offset).ok_or(ElfError("a field's address wraps"))
}

/// Little-endian fields of `bytes`, every read checked.
struct Reader<'a>(&'a [u8]);

impl Reader<'_> {
    fn bytes(&self, at: u64, len: u64) -> Result<&[u8], ElfError> {
        let end = at.checked_add(len).filter(|&end| end <= self.0.len() as u64);
        end.map(|end| &self.0[at as usize..end as usize])
            .ok_or(ElfError("a field runs past the end of the file"))
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
        // 64-bit, little-endian, version 1.
        if r.bytes(0, 7)? != [0x7f, b'E', b'L', b'F', 2, 1, 1] {
            return Err(ElfError("not a little-endian ELF64 file"));
        }
        if r.u16(16)? != ET_EXEC {
            return Err(ElfError("not a static executable (a PIE would need relocating)"));
        }
        if r.u16(18)? != EM_RISCV {
            return Err(ElfError("not for RISC-V"));
        }
        let flags = r.u32(48)?;
        if flags & EF_RISCV_RVC != 0 {
            return Err(ElfError("compressed instructions"));
        }
        if flags & EF_RISCV_FLOAT_ABI != 0 {
            return Err(ElfError("a hardware float ABI"));
        }
        let entry_pc = r.u64(24)?;

        let (mut text, mut image) = (Vec::new(), Vec::new());
        let (phoff, phentsize, phnum) = (r.u64(32)?, r.u16(54)? as u64, r.u16(56)? as u64);
        // What a region may hold is capped by the map, but a buffer here is grown to a
        // segment's own address, so a handful of bytes at the top of a region would
        // allocate the whole of it. A program gets no more text and no more image than
        // its file carries: the rest would be zeros, which is no instruction and no data
        // the program did not write itself.
        let file_len = elf.len() as u64;
        for i in 0..phnum {
            let ph = at(
                phoff,
                i.checked_mul(phentsize).ok_or(ElfError("a header's address wraps"))?,
            )?;
            let (kind, flags) = (r.u32(ph)?, r.u32(at(ph, 4)?)?);
            if matches!(kind, PT_DYNAMIC | PT_INTERP | PT_TLS) {
                return Err(ElfError("dynamic linking or thread-local storage"));
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
            let end = vaddr
                .checked_add(memsz)
                .ok_or(ElfError("a segment wraps the address space"))?;
            let bytes = r.bytes(offset, filesz.min(memsz))?;
            if flags & PF_X != 0 {
                if flags & PF_W != 0 {
                    return Err(ElfError("a writable executable segment"));
                }
                if vaddr < TEXT_BASE || vaddr % 4 != 0 || end > TEXT_BASE + (4 << MAX_LOG_TEXT) {
                    return Err(ElfError("an executable segment outside the text region"));
                }
                if vaddr - TEXT_BASE + bytes.len() as u64 > file_len {
                    return Err(ElfError("more text than the file carries"));
                }
                place::<4>(&mut text, vaddr - TEXT_BASE, bytes);
            } else {
                // RAM's first words are the input's: a segment may reserve them, not fill them.
                let first = RAM_BASE + 8 * INPUT_WORDS as u64;
                if vaddr < RAM_BASE || end > RAM_BASE + (8 << MAX_LOG_RAM) || (vaddr < first && !bytes.is_empty()) {
                    return Err(ElfError("a data segment outside RAM, or over the input words"));
                }
                if !bytes.is_empty() {
                    if vaddr - first + bytes.len() as u64 > file_len {
                        return Err(ElfError("more image than the file carries"));
                    }
                    place::<8>(&mut image, vaddr - first, bytes);
                }
            }
        }
        if text.is_empty() {
            return Err(ElfError("no executable segment"));
        }

        let ram_end =
            symbol(&r, RAM_END_SYMBOL)?.ok_or(ElfError("no __stack_top symbol: not linked with the guests' script"))?;
        let ram_bytes = ram_end.wrapping_sub(RAM_BASE);
        if ram_end <= RAM_BASE || !ram_bytes.is_power_of_two() || ram_bytes < 8 * (INPUT_WORDS as u64 + 1) {
            return Err(ElfError("RAM's size is not a power of two"));
        }
        let log_ram = (ram_bytes / 8).trailing_zeros() as usize;
        let advice_end = symbol(&r, ADVICE_END_SYMBOL)?.ok_or(ElfError("no __advice_top symbol"))?;
        let advice_bytes = advice_end.wrapping_sub(ADVICE_BASE);
        if advice_end <= ADVICE_BASE || !advice_bytes.is_power_of_two() || advice_bytes < 8 {
            return Err(ElfError("the advice region's size is not a power of two"));
        }
        let log_advice = (advice_bytes / 8).trailing_zeros() as usize;
        if log_advice > MAX_LOG_ADVICE {
            return Err(ElfError("the advice region exceeds its bounds"));
        }
        let text: Vec<u32> = text.as_chunks::<4>().0.iter().map(|&w| u32::from_le_bytes(w)).collect();
        let image: Vec<u64> = image
            .as_chunks::<8>()
            .0
            .iter()
            .map(|&w| u64::from_le_bytes(w))
            .collect();
        if log_ram > MAX_LOG_RAM || INPUT_WORDS + image.len() > 1 << log_ram {
            return Err(ElfError("the image does not fit RAM"));
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
fn symbol(r: &Reader, name: &[u8]) -> Result<Option<u64>, ElfError> {
    let (shoff, shentsize, shnum) = (r.u64(40)?, r.u16(58)? as u64, r.u16(60)? as u64);
    for i in 0..shnum {
        let sh = at(
            shoff,
            i.checked_mul(shentsize).ok_or(ElfError("a section's address wraps"))?,
        )?;
        if r.u32(at(sh, 4)?)? != SHT_SYMTAB {
            continue;
        }
        let (offset, size, link, entsize) = (
            r.u64(at(sh, 24)?)?,
            r.u64(at(sh, 32)?)?,
            r.u32(at(sh, 40)?)? as u64,
            r.u64(at(sh, 56)?)?,
        );
        if entsize == 0 || link >= shnum {
            return Err(ElfError("a malformed symbol table"));
        }
        let strings = at(shoff, link * shentsize)?;
        let (str_offset, str_size) = (r.u64(at(strings, 24)?)?, r.u64(at(strings, 32)?)?);
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
