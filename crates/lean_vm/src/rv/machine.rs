//! The interpreter: the reference semantics of a [`Program`], one [`Step`] at a time.

use super::{
    ADVICE_BASE, Class, Entry, INPUT_WORDS, LOG_REGS, MAX_LOG_ADVICE, MAX_LOG_RAM, MAX_LOG_TEXT, OUTPUT_REGS, RAM_BASE,
    SYS_EXIT, SYSCALL_REG, TEXT_BASE,
};
use super::{Target, decode, hash, load, semantics, store};

/// A decoded program: its text, where it starts, RAM as the run finds it, and the
/// advice's size.
#[derive(Clone, Debug)]
pub struct Program {
    /// A power of two of entries, instruction `i` at [`Self::pc_of`]`(i)`. The last
    /// is the halt slot, which is illegal, as is every slot holding no instruction.
    pub entries: Vec<Entry>,
    pub entry_pc: u64,
    /// RAM's words after the [`INPUT_WORDS`] the public input takes. The rest of its
    /// `2^log_ram` words are zero.
    pub image: Vec<u64>,
    pub log_ram: usize,
    /// The advice region holds `2^log_advice` words ([`ADVICE_BASE`]).
    pub log_advice: usize,
}

impl Program {
    /// Decode `text`, whose first word sits at [`TEXT_BASE`].
    pub fn new(text: &[u32], entry_pc: u64, image: Vec<u64>, log_ram: usize, log_advice: usize) -> Self {
        let mut entries: Vec<Entry> = text
            .iter()
            .enumerate()
            .map(|(i, &word)| decode(word, TEXT_BASE + 4 * i as u64))
            .collect();
        // Two more slots at least: the halt slot, and an illegal one before it, so that
        // a run falling off the text traps instead of halting.
        entries.resize((text.len() + 2).next_power_of_two(), Entry::ILLEGAL);
        assert!(
            entries.len() <= 1 << MAX_LOG_TEXT,
            "the text exceeds 2^{MAX_LOG_TEXT} instructions"
        );
        assert!(
            (2..=MAX_LOG_RAM).contains(&log_ram) && INPUT_WORDS + image.len() <= 1 << log_ram,
            "RAM is too small for its image, or exceeds its region"
        );
        assert!(log_advice <= MAX_LOG_ADVICE, "the advice exceeds its region");
        Self {
            entries,
            entry_pc,
            image,
            log_ram,
            log_advice,
        }
    }

    pub fn pc_of(&self, index: usize) -> u64 {
        TEXT_BASE + 4 * index as u64
    }

    /// The entry at `pc`, if `pc` names one.
    pub fn index_of(&self, pc: u64) -> Option<usize> {
        let offset = pc.wrapping_sub(TEXT_BASE);
        (offset.is_multiple_of(4) && offset / 4 < self.entries.len() as u64).then_some((offset / 4) as usize)
    }

    /// Where a run ends: the last slot, which is never executed.
    pub fn halt_pc(&self) -> u64 {
        self.pc_of(self.entries.len() - 1)
    }

    /// The bytecode's `dt` field: a taken entry's target, as a XOR against `pc + 4`.
    pub fn dt_of(&self, index: usize) -> u64 {
        self.target_of(index)
            .map_or(0, |target| target ^ self.pc_of(index).wrapping_add(4))
    }

    /// Where entry `index` goes when its class takes the jump.
    pub fn target_of(&self, index: usize) -> Option<u64> {
        match self.entries[index].target {
            Target::Next => None,
            Target::Abs(target) => Some(target),
            Target::Halt => Some(self.halt_pc()),
        }
    }
}

/// Why a run stops without halting. No proof exists of a run that traps.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Trap {
    /// `pc` names no instruction: outside the text, misaligned, or an illegal one.
    Illegal {
        pc: u64,
    },
    Misaligned {
        pc: u64,
        address: u64,
    },
    /// An access outside RAM.
    Unmapped {
        pc: u64,
        address: u64,
    },
    /// An `ECALL` that is not `exit`.
    NotAnExit {
        syscall: u64,
    },
    CycleCap,
    /// The run is sound but longer than one proof holds: its witness would be
    /// `2^log_words` words.
    TooLong {
        log_words: usize,
    },
}

impl std::fmt::Display for Trap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Self::Illegal { pc } => write!(f, "no legal instruction at pc {pc:#x}"),
            Self::Misaligned { pc, address } => write!(f, "misaligned access to {address:#x} at pc {pc:#x}"),
            Self::Unmapped { pc, address } => write!(f, "access outside RAM, to {address:#x}, at pc {pc:#x}"),
            Self::NotAnExit { syscall } => write!(f, "ecall {syscall} is not exit"),
            Self::CycleCap => write!(f, "the run exceeds its cycle cap"),
            Self::TooLong { log_words } => write!(
                f,
                "the run's witness is 2^{log_words} words, more than one proof holds (continuations are not implemented)"
            ),
        }
    }
}

/// The RAM cell a step accessed.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RamAccess {
    /// What goes on the memory bus ([`semantics::bus_address`]): the word's byte
    /// address, for an aligned access.
    pub address: u64,
    pub old: u64,
    pub new: u64,
}

/// The block a hash row works on ([`hash`]): its words as the row found them, and
/// the four it leaves in the result's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HashAccess {
    pub block: [u64; hash::WORDS],
    pub out: [u64; 4],
}

/// One executed instruction, as a row of its class's table records it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step {
    /// The entry executed.
    pub index: usize,
    pub v1: u64,
    pub v2: u64,
    /// What the class computed.
    pub out: u64,
    pub taken: bool,
    /// What `ad` held, and what it holds now: `out`, or `pc + 4` for a link. Zeros
    /// for a hash row, which writes no register.
    pub vd_old: u64,
    pub vd: u64,
    pub ram: Option<RamAccess>,
    pub hash: Option<Box<HashAccess>>,
    pub npc: u64,
}

/// What entry `e` computes from the registers it reads and, for a load or a store, the
/// RAM cell it names: `(out, taken, RAM access)`, whether or not a run could make
/// that access.
pub fn compute(e: &Entry, v1: u64, v2: u64, cell: u64) -> (u64, bool, RamAccess) {
    let address = semantics::address(v1, e.imm);
    let ram = |new: u64, log_width: u64| RamAccess {
        address: semantics::bus_address(address, log_width),
        old: cell,
        new,
    };
    let none = RamAccess::default();
    match e.class {
        Class::Alu => {
            let (out, taken) = semantics::alu(v1, v2, e.imm, e.flags);
            (out, taken, none)
        }
        Class::Shift => (semantics::shift(v1, v2, e.imm, e.flags), false, none),
        Class::Mul => (semantics::mul(v1, v2, e.flags), false, none),
        Class::Mulh => (semantics::mulh(v1, v2, e.flags), false, none),
        Class::Div => (semantics::div(v1, v2, e.flags), false, none),
        Class::Load => (
            semantics::load(cell, address, e.flags),
            false,
            ram(cell, e.flags & load::LOG_WIDTH),
        ),
        Class::Store => (
            0,
            false,
            ram(semantics::store(cell, address, v2, e.flags), e.flags & store::LOG_WIDTH),
        ),
        Class::Hash | Class::Illegal => (0, false, none),
    }
}

/// What a hash row does to its block: [`semantics::blake2s`] of the block's words.
pub fn compute_hash(block: [u64; hash::WORDS], t: u64, flags: u64) -> HashAccess {
    HashAccess {
        block,
        out: semantics::blake2s(&block, t, flags),
    }
}

pub struct Machine<'a> {
    pub program: &'a Program,
    /// `x0..x31`, then [`super::SINK`].
    pub regs: [u64; 1 << LOG_REGS],
    /// RAM's cells, then the advice's.
    mem: Vec<u64>,
    pub pc: u64,
}

impl<'a> Machine<'a> {
    /// The machine about to run `program` on `input`, RAM's first words, and `advice`,
    /// the advice region's first words.
    pub fn new(program: &'a Program, input: [u64; INPUT_WORDS], advice: &[u64]) -> Self {
        assert!(
            advice.len() <= 1 << program.log_advice,
            "the advice does not fit its region"
        );
        let mut mem = input.to_vec();
        mem.extend(&program.image);
        mem.resize(1 << program.log_ram, 0);
        mem.extend(advice);
        mem.resize((1 << program.log_ram) + (1 << program.log_advice), 0);
        Self {
            program,
            regs: [0; 1 << LOG_REGS],
            mem,
            pc: program.entry_pc,
        }
    }

    pub fn ram(&self) -> &[u64] {
        &self.mem[..1 << self.program.log_ram]
    }

    pub fn advice(&self) -> &[u64] {
        &self.mem[1 << self.program.log_ram..]
    }

    /// The cell holding `address`: RAM's, or past them the advice's.
    fn cell(&self, address: u64) -> Result<usize, Trap> {
        let (ram, advice) = (
            address.wrapping_sub(RAM_BASE) / 8,
            address.wrapping_sub(ADVICE_BASE) / 8,
        );
        if address >= RAM_BASE && ram < 1 << self.program.log_ram {
            Ok(ram as usize)
        } else if address >= ADVICE_BASE && advice < 1 << self.program.log_advice {
            Ok((1 << self.program.log_ram) + advice as usize)
        } else {
            Err(Trap::Unmapped { pc: self.pc, address })
        }
    }

    pub fn halted(&self) -> bool {
        self.pc == self.program.halt_pc()
    }

    pub fn step(&mut self) -> Result<Step, Trap> {
        let pc = self.pc;
        let index = self.program.index_of(pc).ok_or(Trap::Illegal { pc })?;
        let e = self.program.entries[index];
        let (v1, v2) = (self.regs[e.a1 as usize], self.regs[e.a2 as usize]);
        let cell = match e.class {
            Class::Load | Class::Store => {
                let address = semantics::address(v1, e.imm);
                if !semantics::is_aligned(address, e.flags & load::LOG_WIDTH) {
                    return Err(Trap::Misaligned { pc, address });
                }
                Some(self.cell(address)?)
            }
            Class::Illegal => return Err(Trap::Illegal { pc }),
            _ => None,
        };
        let (out, taken, access) = compute(&e, v1, v2, cell.map_or(0, |cell| self.mem[cell]));
        let ram = cell.map(|cell| {
            self.mem[cell] = access.new;
            access
        });
        let hash = match e.class {
            Class::Hash => Some(Box::new(self.hash(pc, v1, v2, e.flags)?)),
            _ => None,
        };
        let pc4 = pc.wrapping_add(4);
        let vd = if e.link { pc4 } else { out };
        let vd_old = match e.class {
            Class::Hash => 0,
            _ => std::mem::replace(&mut self.regs[e.ad as usize], vd),
        };
        let npc = match (e.jalr, taken) {
            (true, _) => out,
            (false, true) => self.program.target_of(index).expect("a taken entry has a target"),
            (false, false) => pc4,
        };
        self.pc = npc;
        Ok(Step {
            index,
            v1,
            v2,
            out,
            taken,
            vd_old,
            vd,
            ram,
            hash,
            npc,
        })
    }

    /// A hash row's block ([`hash`]): word `k` is the cell at `base ^ 8k`, so `base`
    /// has to be a word address and every word of the block in RAM.
    fn hash(&mut self, pc: u64, base: u64, t: u64, flags: u64) -> Result<HashAccess, Trap> {
        if !base.is_multiple_of(8) {
            return Err(Trap::Misaligned { pc, address: base });
        }
        let mut cells = [0usize; hash::WORDS];
        for (k, cell) in cells.iter_mut().enumerate() {
            *cell = self.cell(base ^ (8 * k as u64))?;
        }
        let access = compute_hash(cells.map(|cell| self.mem[cell]), t, flags);
        for (j, &out) in access.out.iter().enumerate() {
            self.mem[cells[hash::OUT as usize / 8 + j]] = out;
        }
        Ok(access)
    }

    /// Run to the halt slot, within `cycle_cap` steps, and return the public output `a0..a3`.
    pub fn run(&mut self, cycle_cap: u64) -> Result<[u64; 4], Trap> {
        for _ in 0..cycle_cap {
            if self.halted() {
                let syscall = self.regs[SYSCALL_REG as usize];
                return if syscall == SYS_EXIT {
                    Ok(OUTPUT_REGS.map(|r| self.regs[r as usize]))
                } else {
                    Err(Trap::NotAnExit { syscall })
                };
            }
            self.step()?;
        }
        Err(Trap::CycleCap)
    }
}

#[cfg(test)]
mod tests {
    use super::super::asm::{self, *};
    use super::*;

    const LOG_RAM: usize = 8;
    const RAM_BYTES: u64 = 8 << LOG_RAM;

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
        /// A word biased toward the values arithmetic gets wrong.
        fn word(&mut self) -> u64 {
            match self.below(8) {
                0 => [
                    0,
                    1,
                    u64::MAX,
                    1 << 63,
                    (1 << 63) - 1,
                    1 << 31,
                    (1 << 31) - 1,
                    0xffff_ffff,
                ][self.below(8) as usize],
                1 => self.next() as u32 as u64,
                2 => self.next() as i32 as i64 as u64,
                3 => self.below(65),
                _ => self.next(),
            }
        }
    }

    /// RISC-V straight from the specification, on registers and BYTES: shares no code
    /// with the decoder, the class functions or the word-addressed RAM.
    fn spec_step(word: u32, x: &mut [u64; 32], pc: &mut u64, mem: &mut [u8]) {
        let (opcode, rd, f3) = (word & 0x7f, (word >> 7 & 31) as usize, word >> 12 & 7);
        let (rs1, rs2, f7) = ((word >> 15 & 31) as usize, (word >> 20 & 31) as usize, word >> 25);
        let (a, b) = (x[rs1], x[rs2]);
        let imm_i = (word as i32 >> 20) as i64 as u64;
        let at = |address: u64| (address - RAM_BASE) as usize;
        let w = |v: u64| v as i32 as i64 as u64;
        let mut next = pc.wrapping_add(4);
        let mut result = None;
        match opcode {
            0x37 => result = Some((word & 0xffff_f000) as i32 as i64 as u64),
            0x17 => result = Some(pc.wrapping_add((word & 0xffff_f000) as i32 as i64 as u64)),
            0x6f => {
                let o = ((word >> 31) << 20)
                    | ((word >> 12 & 0xff) << 12)
                    | ((word >> 20 & 1) << 11)
                    | ((word >> 21 & 0x3ff) << 1);
                result = Some(next);
                next = pc.wrapping_add(((o << 11) as i32 >> 11) as i64 as u64);
            }
            0x67 => {
                result = Some(next);
                next = a.wrapping_add(imm_i) & !1;
            }
            0x63 => {
                let o = ((word >> 31) << 12)
                    | ((word >> 7 & 1) << 11)
                    | ((word >> 25 & 0x3f) << 5)
                    | ((word >> 8 & 0xf) << 1);
                let taken = match f3 {
                    0 => a == b,
                    1 => a != b,
                    4 => (a as i64) < (b as i64),
                    5 => (a as i64) >= (b as i64),
                    6 => a < b,
                    _ => a >= b,
                };
                if taken {
                    next = pc.wrapping_add(((o << 19) as i32 >> 19) as i64 as u64);
                }
            }
            0x03 => {
                let p = at(a.wrapping_add(imm_i));
                let bytes = |n: usize| {
                    let mut le = [0u8; 8];
                    le[..n].copy_from_slice(&mem[p..p + n]);
                    u64::from_le_bytes(le)
                };
                result = Some(match f3 {
                    0 => bytes(1) as i8 as i64 as u64,
                    1 => bytes(2) as i16 as i64 as u64,
                    2 => bytes(4) as i32 as i64 as u64,
                    3 => bytes(8),
                    4 => bytes(1),
                    5 => bytes(2),
                    _ => bytes(4),
                });
            }
            0x23 => {
                let imm = (((f7 << 5) | rd as u32) << 20) as i32 >> 20;
                let p = at(a.wrapping_add(imm as i64 as u64));
                let n = 1 << f3;
                mem[p..p + n].copy_from_slice(&b.to_le_bytes()[..n]);
            }
            0x13 | 0x1b | 0x33 | 0x3b => {
                let word32 = opcode & 8 != 0;
                let immediate = opcode & 0x20 == 0;
                let b = if immediate { imm_i } else { b };
                let m_ext = !immediate && f7 == 1;
                let alt = if immediate {
                    f3 == 5 && word >> 30 & 1 == 1
                } else {
                    f7 == 0x20
                };
                let sh = (b & if word32 { 31 } else { 63 }) as u32;
                let r = if m_ext && !word32 {
                    match f3 {
                        0 => a.wrapping_mul(b),
                        1 => ((a as i64 as i128 * b as i64 as i128) >> 64) as u64,
                        2 => ((a as i64 as i128 * b as i128) >> 64) as u64,
                        3 => ((a as u128 * b as u128) >> 64) as u64,
                        4 if b == 0 => u64::MAX,
                        4 => (a as i64).wrapping_div(b as i64) as u64,
                        5 if b == 0 => u64::MAX,
                        5 => a / b,
                        6 if b == 0 => a,
                        6 => (a as i64).wrapping_rem(b as i64) as u64,
                        _ if b == 0 => a,
                        _ => a % b,
                    }
                } else if m_ext {
                    let (a, b) = (a as i32, b as i32);
                    let (ua, ub) = (a as u32, b as u32);
                    w(match f3 {
                        0 => a.wrapping_mul(b) as u64,
                        4 if b == 0 => u64::MAX,
                        4 => a.wrapping_div(b) as u64,
                        5 if b == 0 => u64::MAX,
                        5 => (ua / ub) as u64,
                        6 if b == 0 => a as u64,
                        6 => a.wrapping_rem(b) as u64,
                        _ if b == 0 => ua as u64,
                        _ => (ua % ub) as u64,
                    })
                } else if word32 {
                    let a = a as u32;
                    w(match f3 {
                        0 if alt && !immediate => a.wrapping_sub(b as u32) as u64,
                        0 => a.wrapping_add(b as u32) as u64,
                        1 => (a << sh) as u64,
                        _ if alt => (a as i32 >> sh) as u64,
                        _ => (a >> sh) as u64,
                    })
                } else {
                    match f3 {
                        0 if alt && !immediate => a.wrapping_sub(b),
                        0 => a.wrapping_add(b),
                        1 => a << sh,
                        2 => ((a as i64) < (b as i64)) as u64,
                        3 => (a < b) as u64,
                        4 => a ^ b,
                        5 if alt => (a as i64 >> sh) as u64,
                        5 => a >> sh,
                        6 => a | b,
                        _ => a & b,
                    }
                };
                result = Some(r);
            }
            _ => unreachable!("the generator made {word:#010x}"),
        }
        if let Some(r) = result
            && rd != 0
        {
            x[rd] = r;
        }
        *pc = next;
    }

    /// A random legal instruction. `base` is a register the caller points at
    /// `address - imm` for a load or a store.
    fn random_instruction(rng: &mut Rng) -> (u32, Option<(u32, i32, u32)>) {
        let reg = |rng: &mut Rng| rng.below(32) as u32;
        let (rd, rs1, rs2) = (reg(rng), reg(rng), reg(rng));
        let imm = rng.below(4096) as i32 - 2048;
        let word = match rng.below(10) {
            0 | 1 => {
                let (_, opcode, f3, f7) = R_OPS[rng.below(R_OPS.len() as u64) as usize];
                r_type(opcode, f3, f7, rd, rs1, rs2)
            }
            2 => {
                let (_, opcode, f3) = I_OPS[rng.below(I_OPS.len() as u64) as usize];
                i_type(opcode, f3, rd, rs1, imm)
            }
            3 => {
                let (_, opcode, f3, top, bits) = SHIFT_OPS[rng.below(SHIFT_OPS.len() as u64) as usize];
                i_type(opcode, f3, rd, rs1, (top | rng.below(1 << bits) as u32) as i32)
            }
            4 => {
                let f3 = LOAD_OPS[rng.below(LOAD_OPS.len() as u64) as usize].1;
                let base = 1 + rng.below(31) as u32;
                return (i_type(0x03, f3, rd, base, imm), Some((base, imm, f3 & 3)));
            }
            5 => {
                let f3 = STORE_OPS[rng.below(STORE_OPS.len() as u64) as usize].1;
                let base = 1 + rng.below(31) as u32;
                return (s_type(0x23, f3, base, rs2, imm), Some((base, imm, f3)));
            }
            6 => b_type(
                BRANCH_OPS[rng.below(6) as usize].1,
                rs1,
                rs2,
                (rng.below(2048) as i32 - 1024) * 4,
            ),
            7 => j_type(rd, (rng.below(1 << 18) as i32 - (1 << 17)) * 4),
            8 => i_type(0x67, 0, rd, rs1, imm),
            _ => u_type(if rng.below(2) == 0 { 0x37 } else { 0x17 }, rd, rng.next() as u32),
        };
        (word, None)
    }

    /// One random instruction from one random state, through the decoder and the class
    /// functions and through the specification: same registers, same `pc`, same RAM.
    #[test]
    fn every_instruction_matches_the_specification() {
        let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
        for _ in 0..300_000 {
            let (word, access) = random_instruction(&mut rng);
            let program = Program::new(
                &[word],
                TEXT_BASE,
                (INPUT_WORDS..1 << LOG_RAM).map(|_| rng.next()).collect(),
                LOG_RAM,
                0,
            );
            let mut m = Machine::new(&program, [0; 4], &[]);
            for r in 1..32 {
                m.regs[r] = rng.word();
            }
            if let Some((base, imm, log_width)) = access {
                let address = RAM_BASE + (rng.below(RAM_BYTES - 8) & !((1 << log_width) - 1));
                m.regs[base as usize] = address.wrapping_sub(imm as i64 as u64);
            }
            let mut x: [u64; 32] = m.regs[..32].try_into().unwrap();
            let mut mem: Vec<u8> = m.ram().iter().flat_map(|w| w.to_le_bytes()).collect();
            let mut pc = m.pc;
            spec_step(word, &mut x, &mut pc, &mut mem);
            m.step().unwrap_or_else(|trap| panic!("{word:#010x}: {trap}"));
            assert_eq!(m.regs[..32], x, "{word:#010x}: registers");
            assert_eq!(m.pc, pc, "{word:#010x}: pc");
            let ram: Vec<u8> = m.ram().iter().flat_map(|w| w.to_le_bytes()).collect();
            assert_eq!(ram, mem, "{word:#010x}: RAM");
        }
    }

    fn run(text: &[u32], image: Vec<u64>) -> Result<[u64; 4], Trap> {
        Machine::new(&Program::new(text, TEXT_BASE, image, LOG_RAM, 0), [7, 0, 0, 0], &[]).run(1 << 20)
    }

    #[test]
    fn li_loads_any_constant() {
        let mut rng = Rng(7);
        for _ in 0..2000 {
            let value = rng.word();
            let text = Asm::new().li(A0, value).exit().finish();
            assert_eq!(run(&text, vec![]), Ok([value, 0, 0, 0]), "{value:#x}");
        }
    }

    /// A loop, a call and return through `jal`/`jalr`, a stack, and an in-place sort.
    #[test]
    fn programs_run() {
        // Fibonacci: a0 <- F(90), iteratively.
        let text = Asm::new()
            .li(A0, 0)
            .li(A1, 1)
            .li(T0, 90)
            .label("loop")
            .r("add", A2, A0, A1)
            .i("addi", A0, A1, 0)
            .i("addi", A1, A2, 0)
            .i("addi", T0, T0, -1)
            .branch("bne", T0, ZERO, "loop")
            .li(A1, 0)
            .li(A2, 0)
            .exit()
            .finish();
        assert_eq!(run(&text, vec![]), Ok([2_880_067_194_370_816_120, 0, 0, 0]));

        // Bubble sort of eight words through a stack frame, then a0 <- the median pair's sum.
        const DATA: u64 = RAM_BASE + 8 * INPUT_WORDS as u64;
        let data = [5u64, 3, 9, 1, 8, 2, 7, 4];
        let text = Asm::new()
            .li(SP, RAM_BASE + RAM_BYTES)
            .li(A0, DATA)
            .jal(RA, "sort")
            .li(T0, DATA)
            .load("ld", A0, 24, T0)
            .load("ld", A1, 32, T0)
            .r("add", A0, A0, A1)
            .li(A1, 0)
            .li(A2, 0)
            .li(A3, 0)
            .exit()
            .label("sort")
            .i("addi", SP, SP, -16)
            .store("sd", RA, 8, SP)
            .li(T2, 7)
            .label("outer")
            .i("addi", T0, A0, 0)
            .i("addi", T1, T2, 0)
            .label("inner")
            .load("ld", A2, 0, T0)
            .load("ld", A3, 8, T0)
            .branch("bgeu", A3, A2, "ordered")
            .store("sd", A3, 0, T0)
            .store("sd", A2, 8, T0)
            .label("ordered")
            .i("addi", T0, T0, 8)
            .i("addi", T1, T1, -1)
            .branch("bne", T1, ZERO, "inner")
            .i("addi", T2, T2, -1)
            .branch("bne", T2, ZERO, "outer")
            .load("ld", RA, 8, SP)
            .i("addi", SP, SP, 16)
            .jalr(ZERO, RA, 0)
            .finish();
        let program = Program::new(&text, TEXT_BASE, data.to_vec(), LOG_RAM, 0);
        let mut m = Machine::new(&program, [0; 4], &[]);
        assert_eq!(m.run(1 << 20), Ok([4 + 5, 0, 0, 0]));
        assert_eq!(m.ram()[INPUT_WORDS..][..8], [1, 2, 3, 4, 5, 7, 8, 9]);
        assert_eq!(m.regs[0], 0, "x0");
    }

    #[test]
    fn traps() {
        let text = |f: &mut dyn FnMut(&mut Asm)| {
            let mut a = Asm::new();
            f(&mut a);
            a.exit().finish()
        };
        let pc = TEXT_BASE + 4;
        // A misaligned load, one outside RAM, one reaching for the text.
        let t = text(&mut |a| {
            a.li(T0, RAM_BASE).load("lw", A0, 2, T0);
        });
        assert_eq!(
            run(&t, vec![]),
            Err(Trap::Misaligned {
                pc,
                address: RAM_BASE + 2
            })
        );
        let t = text(&mut |a| {
            a.li(T0, RAM_BASE).load("ld", A0, -8, T0);
        });
        assert_eq!(
            run(&t, vec![]),
            Err(Trap::Unmapped {
                pc,
                address: RAM_BASE - 8
            })
        );
        let t = text(&mut |a| {
            a.li(T0, TEXT_BASE).store("sd", A0, 0, T0);
        });
        assert_eq!(run(&t, vec![]), Err(Trap::Unmapped { pc, address: TEXT_BASE }));
        // Falling off the text, a jump into the middle of an instruction, EBREAK.
        assert_eq!(run(&[0x13], vec![]), Err(Trap::Illegal { pc }));
        assert_eq!(
            run(&[asm::i_type(0x67, 0, 0, 0, 0), 0x13], vec![]),
            Err(Trap::Illegal { pc: 0 })
        );
        assert_eq!(run(&[0x0010_0073], vec![]), Err(Trap::Illegal { pc: TEXT_BASE }));
        // An ecall that is not exit, and a loop that never ends.
        assert_eq!(run(&[ECALL], vec![]), Err(Trap::NotAnExit { syscall: 0 }));
        assert_eq!(run(&[asm::j_type(0, 0)], vec![]), Err(Trap::CycleCap));
    }
}
