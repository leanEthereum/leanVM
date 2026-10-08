//! The interpreter: the reference semantics of a program, one step at a time.
//!
//! A step reads the entry at `pc`, its two registers and, for a memory class, memory.
//!
//! It then writes its destination and memory, and moves `pc`.
//!
//! A run that faults stops with a trap, and no proof can follow it.

use super::entry::{Class, Entry};
use super::program::RiscvProgram;
use super::region::Region;
use super::register::{ExtRegisterFile, Reg, RegisterFile, Syscall};
use super::semantics::{BlockAccess, ElementAccess, Ext, Hash, InstructionClass, Load, WordAccess};
use thiserror::Error;

/// Why a run stops without halting: a fault of the ISA.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum Trap {
    /// `pc` names no legal instruction: it is outside the text, misaligned, or illegal.
    #[error("no legal instruction at pc {pc:#x}")]
    Illegal {
        /// The faulting address.
        pc: u64,
    },
    /// A load, a store or a hash block at an address its width does not divide.
    #[error("misaligned access to {address:#x} at pc {pc:#x}")]
    Misaligned {
        /// The instruction's address.
        pc: u64,
        /// The access's address.
        address: u64,
    },
    /// An access outside RAM and the advice.
    #[error("access outside RAM, to {address:#x}, at pc {pc:#x}")]
    Unmapped {
        /// The instruction's address.
        pc: u64,
        /// The access's address.
        address: u64,
    },
    /// A checked extension-field product whose result is not zero.
    #[error("a checked extension-field product is not zero at pc {pc:#x}")]
    NonZero {
        /// The instruction's address.
        pc: u64,
    },
    /// The run reached the halt slot by an `ecall` that is not `exit`.
    #[error("ecall {syscall} is not exit")]
    NotAnExit {
        /// The system call number found.
        syscall: u64,
    },
}

/// The interpreter's state: the program, the registers, memory and `pc`.
#[derive(Clone, Debug)]
pub struct Machine<'a> {
    /// The program being run.
    program: &'a RiscvProgram,
    /// `x0` to `x31`, then the sink.
    registers: RegisterFile,
    /// `f0` to `f127`.
    ext: ExtRegisterFile,
    /// RAM and the advice.
    memory: Memory,
    /// The address of the next instruction.
    pc: u64,
    /// Whether the last step jumped to the halt slot.
    exited: bool,
}

impl<'a> Machine<'a> {
    /// The machine about to run `program`, the advice's first words being `advice`.
    ///
    /// # Panics
    ///
    /// Panics if the advice does not fit its region.
    pub fn new(program: &'a RiscvProgram, advice: &[u64]) -> Self {
        Self {
            program,
            registers: RegisterFile::new(),
            ext: ExtRegisterFile::new(),
            memory: Memory::new(program, advice),
            pc: program.entry_pc(),
            exited: false,
        }
    }

    /// The program being run.
    pub const fn program(&self) -> &'a RiscvProgram {
        self.program
    }

    /// The register file: `x0` to `x31`, then the sink, which nothing reads.
    pub const fn registers(&self) -> &RegisterFile {
        &self.registers
    }

    /// The extension registers.
    pub const fn ext_registers(&self) -> &ExtRegisterFile {
        &self.ext
    }

    /// RAM and the advice.
    pub const fn memory(&self) -> &Memory {
        &self.memory
    }

    /// The address of the next instruction.
    pub const fn pc(&self) -> u64 {
        self.pc
    }

    /// Whether the run has reached the halt slot by an `ecall`.
    pub const fn halted(&self) -> bool {
        self.exited && self.pc == self.program.halt_pc()
    }

    /// Execute one instruction.
    ///
    /// # Errors
    ///
    /// Returns the trap the instruction raises, the machine left as it was.
    pub fn step(&mut self) -> Result<Step, Trap> {
        // Fetch: the legal entry at pc.
        let pc = self.pc;
        let index = self.program.index_of(pc).ok_or(Trap::Illegal { pc })?;
        let entry = self.program.entries()[index];
        if entry.class == Class::Illegal {
            return Err(Trap::Illegal { pc });
        }

        // Read both registers; an instruction with fewer reads x0.
        //
        // An extension-field product names extension registers, but for a base-field operand.
        let (v1, v2) = match entry.class {
            Class::Ext if entry.flags & Ext::BASE != 0 => (0, self.registers.read(entry.a2)),
            Class::Ext => (0, 0),
            // A store of an element names an extension register as its second.
            Class::Esd => (self.registers.read(entry.a1), 0),
            _ => (self.registers.read(entry.a1), self.registers.read(entry.a2)),
        };

        // Resolve every address before writing anything, so a trap leaves no trace.
        let cell = match entry.class {
            Class::Load | Class::Store | Class::Ld | Class::Sd => {
                let address = WordAccess::address(v1, entry.imm);
                // A double word's width is its class's, a narrower access's its flags'.
                let log_width = match entry.class {
                    Class::Ld | Class::Sd => 3,
                    _ => entry.flags & Load::LOG_WIDTH,
                };
                Some(self.cell(pc, address, log_width)?)
            }
            _ => None,
        };
        let block = match entry.class {
            Class::Hash => Some(self.block(pc, v1, v2, self.registers.read(entry.ad))?),
            _ => None,
        };
        let element = match entry.class {
            Class::Eld | Class::Esd => {
                let address = WordAccess::word_address(v1, entry.imm);
                let mut cells = [0; 3];
                for (k, cell) in cells.iter_mut().enumerate() {
                    *cell = self.cell(pc, ElementAccess::limb_address(address, k), 3)?;
                }
                Some((address, cells))
            }
            _ => None,
        };
        let product = match entry.class {
            Class::Ext => Some(self.product(pc, &entry, v2)?),
            _ => None,
        };

        // Compute, then apply the memory access.
        let outcome = entry.evaluate(pc, v1, v2, cell.map_or(0, |cell| self.memory.get(cell)));
        let memory = match (cell, outcome.access, block, product) {
            (Some(cell), Some(access), _, _) => {
                self.memory.set(cell, access.new);
                MemoryAccess::Word(access)
            }
            (_, _, Some(cells), _) => {
                let (x, to) = (self.registers.read(entry.imm as u8), self.registers.read(entry.ad));
                MemoryAccess::Block(Box::new(self.compress(&cells, x, to, entry.flags)))
            }
            (_, _, _, Some(instance)) => {
                self.ext.write(entry.ad, instance.eval());
                MemoryAccess::Ext(Box::new(instance))
            }
            // A load moves the three words to the register, a store the register to the three words.
            _ if element.is_some() => {
                let (address, cells) = element.expect("an element's move");
                let words = cells.map(|cell| self.memory.get(cell));
                let (limbs, old) = if entry.class == Class::Eld {
                    let old = self.ext.read(entry.ad);
                    self.ext.write(entry.ad, words);
                    (words, old)
                } else {
                    let limbs = self.ext.read(entry.a2);
                    for (cell, limb) in cells.into_iter().zip(limbs) {
                        self.memory.set(cell, limb);
                    }
                    (limbs, words)
                };
                MemoryAccess::Element(ElementAccess { address, limbs, old })
            }
            _ => MemoryAccess::None,
        };

        // Write the destination: the output, which is `pc + 4` for a jump that links.
        let vd = outcome.out;
        let vd_old = self.write_destination(&entry, vd);

        // Move pc: the fixed target, the address an indirect jump computes, or the next instruction.
        let npc = match (outcome.taken, self.program.target_of(index)) {
            (true, Some(target)) => target,
            (true, None) => v1.wrapping_add(entry.imm) & !1,
            (false, _) => pc.wrapping_add(4),
        };
        self.exited = entry.is_exit();
        self.pc = npc;
        Ok(Step {
            index,
            v1,
            v2,
            out: outcome.out,
            taken: outcome.taken,
            vd_old,
            vd,
            memory,
            npc,
        })
    }

    /// Run to the halt slot and return the public output.
    ///
    /// A program that never halts never returns: bound the run with the step-limited form.
    ///
    /// # Errors
    ///
    /// Returns the trap that stops the run.
    pub fn run(&mut self) -> Result<[u64; 4], Trap> {
        loop {
            if let Some(output) = self.run_for(u64::MAX)? {
                return Ok(output);
            }
        }
    }

    /// Run to the halt slot within `max_steps` steps, and return the public output.
    ///
    /// Returns `None` if the steps run out first, the machine left where it stopped.
    ///
    /// # Errors
    ///
    /// Returns the trap that stops the run.
    pub fn run_for(&mut self, max_steps: u64) -> Result<Option<[u64; 4]>, Trap> {
        // Check for the halt before each step, and once more after the last.
        for _ in 0..max_steps {
            if self.halted() {
                return self.output().map(Some);
            }
            self.step()?;
        }
        if self.halted() {
            self.output().map(Some)
        } else {
            Ok(None)
        }
    }

    /// The public output of a halted run: `a0` to `a3`.
    ///
    /// # Errors
    ///
    /// Returns a trap if the system call number is not `exit`.
    pub fn output(&self) -> Result<[u64; 4], Trap> {
        let syscall = self.registers.get(Reg::SYSCALL);
        if syscall != Syscall::Exit.number() {
            return Err(Trap::NotAnExit { syscall });
        }
        Ok(Reg::OUTPUTS.map(|r| self.registers.get(r)))
    }

    /// The cell an access of `2^log_width` bytes at `address` names.
    ///
    /// A misaligned access traps before an unmapped one.
    fn cell(&self, pc: u64, address: u64, log_width: u64) -> Result<usize, Trap> {
        if !WordAccess::is_aligned(address, log_width) {
            return Err(Trap::Misaligned { pc, address });
        }
        self.memory.cell(address).ok_or(Trap::Unmapped { pc, address })
    }

    /// The cells of a compression: the chaining value's four words, the message's eight, then the result's four,
    /// word `k` of each at its pointer `^ 8k`.
    ///
    /// Each must be a word address, and every word mapped.
    fn block(&self, pc: u64, h: u64, m: u64, to: u64) -> Result<[usize; 16], Trap> {
        let mut cells = [0; 16];
        let words = (0..4)
            .map(|k| (h, k))
            .chain((0..8).map(|k| (m, k)))
            .chain((0..4).map(|k| (to, k)));
        for (cell, (base, k)) in cells.iter_mut().zip(words) {
            *cell = self.cell(pc, base ^ (8 * k as u64), 3)?;
        }
        Ok(cells)
    }

    /// The extension-field product the entry names, as it finds its operands.
    ///
    /// A base-field `b` is the word `v2`. A checked form whose result is not zero traps.
    fn product(&self, pc: u64, entry: &Entry, v2: u64) -> Result<Ext, Trap> {
        let b = if entry.flags & Ext::BASE != 0 {
            [v2, 0, 0]
        } else {
            self.ext.read(entry.a2)
        };
        let instance = Ext {
            flags: entry.flags,
            a: self.ext.read(entry.a1),
            b,
            c: self.ext.read(entry.ad),
        };
        if instance.runs() {
            Ok(instance)
        } else {
            Err(Trap::NonZero { pc })
        }
    }

    /// Compress the words in `cells`, every one read first, and write the result to its words.
    fn compress(&mut self, cells: &[usize; 16], x: u64, to: u64, flags: u64) -> BlockAccess {
        let words = cells.map(|cell| self.memory.get(cell));
        let hash = Hash {
            flags,
            x,
            h: std::array::from_fn(|k| words[k]),
            m: std::array::from_fn(|k| words[4 + k]),
        };
        let access = BlockAccess {
            hash,
            to,
            old: std::array::from_fn(|k| words[12 + k]),
            out: hash.eval(),
        };
        for (&cell, &word) in cells[12..].iter().zip(&access.out) {
            self.memory.set(cell, word);
        }
        access
    }

    /// Write `vd` to the entry's destination and return what it held.
    ///
    /// A store and a hash always write the sink, which nothing reads.
    ///
    /// An extension-field product writes an extension register, and no integer one.
    ///
    /// They make no write at all, so their tables have none to prove.
    const fn write_destination(&mut self, entry: &Entry, vd: u64) -> u64 {
        match entry.class {
            Class::Store | Class::Sd | Class::Hash | Class::Ext | Class::Eld | Class::Esd => 0,
            _ => self.registers.replace(entry.ad, vd),
        }
    }
}

/// What an executed instruction did to memory.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MemoryAccess {
    /// Nothing: every class but the memory classes.
    None,
    /// One cell: a load or a store.
    Word(WordAccess),
    /// A whole block: the hash.
    Block(Box<BlockAccess>),
    /// An element moved between memory and an extension register.
    Element(ElementAccess),
    /// An extension-field product: the instance as the row found its operands.
    Ext(Box<Ext>),
}

/// One executed instruction, as a row of its class's table records it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step {
    /// The entry executed.
    pub index: usize,
    /// The first register's value.
    pub v1: u64,
    /// The second register's value.
    pub v2: u64,
    /// What the class computed.
    pub out: u64,
    /// Whether the class took the jump.
    pub taken: bool,
    /// What the destination held before.
    ///
    /// Zero for a store, a hash or an extension-field product, which write no register.
    pub vd_old: u64,
    /// What the destination holds now: the output.
    pub vd: u64,
    /// What the instruction did to memory.
    pub memory: MemoryAccess,
    /// The next `pc`.
    pub npc: u64,
}

/// RAM's cells, then the advice's.
///
/// - RAM is its image, then zeros, 2^log_ram cells in all.
/// - The advice is the prover's words, then zeros, 2^log_advice cells in all.
///
/// A cell's number is also its row in the memory argument.
#[derive(Clone, Debug)]
pub struct Memory {
    /// Every cell, RAM's first.
    cells: Vec<u64>,
    /// RAM holds 2^log_ram cells.
    log_ram: usize,
    /// The advice holds 2^log_advice cells.
    log_advice: usize,
}

impl Memory {
    /// The memory a run of `program` starts from, the advice's first words being `advice`.
    ///
    /// # Panics
    ///
    /// Panics if the advice does not fit its region.
    fn new(program: &RiscvProgram, advice: &[u64]) -> Self {
        let (log_ram, log_advice) = (program.log_ram(), program.log_advice());
        assert!(advice.len() <= 1 << log_advice, "the advice does not fit its region");

        // The image then zeros, the advice then zeros.
        let mut cells = Vec::with_capacity((1 << log_ram) + (1 << log_advice));
        cells.extend_from_slice(program.image());
        cells.resize(1 << log_ram, 0);
        cells.extend_from_slice(advice);
        cells.resize((1 << log_ram) + (1 << log_advice), 0);
        Self {
            cells,
            log_ram,
            log_advice,
        }
    }

    /// RAM's cells.
    pub fn ram(&self) -> &[u64] {
        &self.cells[..1 << self.log_ram]
    }

    /// The advice's cells.
    pub fn advice(&self) -> &[u64] {
        &self.cells[1 << self.log_ram..]
    }

    /// The number of the cell holding the byte at `address`.
    ///
    /// Returns `None` for an address in neither RAM nor the advice.
    pub fn cell(&self, address: u64) -> Option<usize> {
        // RAM's cells come first, then the advice's.
        let ram = || Region::RAM.index(address, self.log_ram);
        let advice = || {
            Region::ADVICE
                .index(address, self.log_advice)
                .map(|i| (1 << self.log_ram) + i)
        };
        ram().or_else(advice)
    }

    /// The value of cell `cell`.
    fn get(&self, cell: usize) -> u64 {
        self.cells[cell]
    }

    /// Write `value` to cell `cell`.
    fn set(&mut self, cell: usize, value: u64) {
        self.cells[cell] = value;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::Region;
    use crate::rv::asm::*;
    use crate::rv::semantics::InstructionClass;
    use crate::rv::semantics::tests::edge_word;
    use proptest::prelude::*;

    /// The fixture's RAM: 2^8 words.
    const LOG_RAM: usize = 8;

    /// The fixture's RAM in bytes.
    const RAM_BYTES: u64 = 8 << LOG_RAM;

    /// Run `text` from its first word, for at most 2^20 steps.
    fn run(text: &[u32], image: Vec<u64>) -> Result<Option<[u64; 4]>, Trap> {
        let program = RiscvProgram::new(text, Region::TEXT.base(), image, LOG_RAM, 0).expect("a valid program");
        Machine::new(&program, &[]).run_for(1 << 20)
    }

    /// `text` built by `f`, then `exit`.
    fn exiting(f: impl FnOnce(&mut Asm)) -> Vec<u32> {
        let mut asm = Asm::new();
        f(&mut asm);
        asm.exit().finish()
    }

    proptest! {
        #[test]
        fn li_loads_any_constant(value in edge_word()) {
            // The constant lands in a0, which the run outputs.
            let text = Asm::new().li(Reg::A0, value).exit().finish();
            prop_assert_eq!(run(&text, vec![]), Ok(Some([value, 0, 0, 0])));
        }
    }

    #[test]
    fn a_loop_computes_fibonacci() {
        // a0 = F(90), iteratively, on registers.
        let text = Asm::new()
            .li(Reg::A0, 0)
            .li(Reg::A1, 1)
            .li(Reg::T0, 90)
            .label("loop")
            .r(Add, Reg::A2, Reg::A0, Reg::A1)
            .i(Addi, Reg::A0, Reg::A1, 0)
            .i(Addi, Reg::A1, Reg::A2, 0)
            .i(Addi, Reg::T0, Reg::T0, -1)
            .branch(Bne, Reg::T0, Reg::ZERO, "loop")
            .li(Reg::A1, 0)
            .li(Reg::A2, 0)
            .exit()
            .finish();
        assert_eq!(run(&text, vec![]), Ok(Some([2_880_067_194_370_816_120, 0, 0, 0])));
    }

    #[test]
    fn a_call_sorts_through_a_stack_frame() {
        // Fixture: eight words in RAM, bubble-sorted by a function with a stack frame.
        //
        //     before   [5, 3, 9, 1, 8, 2, 7, 4]
        //     after    [1, 2, 3, 4, 5, 7, 8, 9]
        //     a0       the median pair's sum, 4 + 5
        let data = [5u64, 3, 9, 1, 8, 2, 7, 4];
        let text = Asm::new()
            .li(Reg::SP, Region::RAM.base() + RAM_BYTES)
            .li(Reg::A0, Region::RAM.base())
            .jal(Reg::RA, "sort")
            .li(Reg::T0, Region::RAM.base())
            .load(Ld, Reg::A0, 24, Reg::T0)
            .load(Ld, Reg::A1, 32, Reg::T0)
            .r(Add, Reg::A0, Reg::A0, Reg::A1)
            .li(Reg::A1, 0)
            .li(Reg::A2, 0)
            .li(Reg::A3, 0)
            .exit()
            // sort(a0): seven passes, each swapping out-of-order neighbours.
            .label("sort")
            .i(Addi, Reg::SP, Reg::SP, -16)
            .store(Sd, Reg::RA, 8, Reg::SP)
            .li(Reg::T2, 7)
            .label("outer")
            .i(Addi, Reg::T0, Reg::A0, 0)
            .i(Addi, Reg::T1, Reg::T2, 0)
            .label("inner")
            .load(Ld, Reg::A2, 0, Reg::T0)
            .load(Ld, Reg::A3, 8, Reg::T0)
            .branch(Bgeu, Reg::A3, Reg::A2, "ordered")
            .store(Sd, Reg::A3, 0, Reg::T0)
            .store(Sd, Reg::A2, 8, Reg::T0)
            .label("ordered")
            .i(Addi, Reg::T0, Reg::T0, 8)
            .i(Addi, Reg::T1, Reg::T1, -1)
            .branch(Bne, Reg::T1, Reg::ZERO, "inner")
            .i(Addi, Reg::T2, Reg::T2, -1)
            .branch(Bne, Reg::T2, Reg::ZERO, "outer")
            .load(Ld, Reg::RA, 8, Reg::SP)
            .i(Addi, Reg::SP, Reg::SP, 16)
            .jalr(Reg::ZERO, Reg::RA, 0)
            .finish();
        let program =
            RiscvProgram::new(&text, Region::TEXT.base(), data.to_vec(), LOG_RAM, 0).expect("a valid program");
        let mut m = Machine::new(&program, &[]);

        assert_eq!(m.run(), Ok([4 + 5, 0, 0, 0]));
        assert_eq!(m.memory().ram()[..8], [1, 2, 3, 4, 5, 7, 8, 9]);
        assert_eq!(m.registers().get(Reg::ZERO), 0);
    }

    #[test]
    fn a_hash_reads_three_places_and_writes_one() {
        // Fixture: h = 1..4 at RAM's base, room for the result after it, m = 9..16 from word 8, a final compression.
        let block: [u64; 16] = std::array::from_fn(|k| if (4..8).contains(&k) { 0 } else { k as u64 + 1 });
        let run = |f: &dyn Fn(&mut Asm)| {
            let text = exiting(|a| {
                a.li(Reg::T0, Region::RAM.base())
                    .li(Reg::T1, Region::RAM.base() + 64)
                    .li(Reg::T2, Region::RAM.base() + 32)
                    .li(Reg::T3, 64);
                f(a);
            });
            let program = RiscvProgram::new(&text, Region::TEXT.base(), block.to_vec(), LOG_RAM, 0).unwrap();
            let mut m = Machine::new(&program, &[]);
            m.run().unwrap();
            m.memory().ram()[..16].to_vec()
        };
        let (h, m) = ([1, 2, 3, 4], [9, 10, 11, 12, 13, 14, 15, 16]);
        let hash = |flags, x| Hash { flags, x, h, m }.eval();

        // Only the result's words change, to the reference compression.
        let ram = run(&|a| {
            a.blake2s(Reg::T2, Reg::T0, Reg::T1, Reg::T3, true);
        });
        assert_eq!(ram[4..8], hash(Hash::FINAL, 64));
        assert_eq!((&ram[..4], &ram[8..]), (&block[..4], &block[8..]));

        // The result may go where the chaining value is: every word is read first.
        let ram = run(&|a| {
            a.blake2s(Reg::T0, Reg::T0, Reg::T1, Reg::T3, true);
        });
        assert_eq!(ram[..4], hash(Hash::FINAL, 64));

        // A node orders the message's halves by its register's low bit, and counts one block.
        for bit in [0, 1] {
            let ram = run(&|a| {
                a.li(Reg::T3, 6 + bit).blake2s_node(Reg::T2, Reg::T0, Reg::T1, Reg::T3);
            });
            let swapped: [u64; 8] = std::array::from_fn(|k| m[(k + 4 * bit as usize) % 8]);
            let expected = Hash {
                flags: Hash::FINAL,
                x: 64,
                h,
                m: swapped,
            };
            assert_eq!(ram[4..8], expected.eval(), "bit {bit}");
        }
    }

    #[test]
    fn an_extension_product_reads_every_operand_before_it_writes() {
        // Fixture: x = 3 + 5y + 7y^2 built in f3 from the constants, and the base-field w = 9 in t1.
        //
        //     f3 = 1 * 3,  f3 += y * 5,  f3 += y^2 * 7
        let (x, w) = ([3, 5, 7], 9);
        let product = |a: [u64; 3], b: [u64; 3]| {
            Ext {
                flags: 0,
                a,
                b,
                c: [0; 3],
            }
            .eval()
        };
        let run = |f: &dyn Fn(&mut Asm)| {
            let text = exiting(|a| {
                a.li(Reg::T0, 3).li(Reg::T1, 5).li(Reg::T2, 7);
                a.ext(Extmulk, 3, 0, 5).ext(Extmack, 3, 1, 6).ext(Extmack, 3, 2, 7);
                a.li(Reg::T1, w);
                f(a);
            });
            let program = RiscvProgram::new(&text, Region::TEXT.base(), vec![], LOG_RAM, 0).unwrap();
            let mut m = Machine::new(&program, &[]);
            m.run().map(|_| *m.ext_registers().cells())
        };

        // The constants, and x.
        let loaded = run(&|_| {}).unwrap();
        assert_eq!(loaded[..4], [[1, 0, 0], [0, 1, 0], [0, 0, 1], x]);

        // Squaring in place: c is a and b, read before it is written.
        let square = product(x, x);
        assert_eq!(
            run(&|a| {
                a.ext(Extmul, 3, 3, 3);
            })
            .unwrap()[3],
            square
        );

        // Accumulating twice into f4, the second time by the base-field w.
        let sum: [u64; 3] = std::array::from_fn(|i| square[i] ^ product(x, [w, 0, 0])[i]);
        let cells = run(&|a| {
            a.ext(Extmul, 4, 3, 3).ext(Extmack, 4, 3, 6);
        });
        assert_eq!(cells.unwrap()[4], sum);

        // A checked form runs on a zero result, which it leaves, and traps on any other.
        let equal = run(&|a| {
            a.ext(Extmul, 4, 3, 0).ext(Extmacz, 4, 3, 0);
        });
        assert_eq!(equal.unwrap()[4], [0; 3]);
        let unequal = run(&|a| {
            a.ext(Extmul, 4, 3, 3).ext(Extmacz, 4, 3, 0);
        });
        assert!(matches!(unequal, Err(Trap::NonZero { .. })));
    }

    #[test]
    fn faults_trap_and_leave_no_trace() {
        // The fixture's faulting instruction is always the second.
        let pc = Region::TEXT.base() + 4;

        // A misaligned load, one below RAM, a store reaching into the text.
        let misaligned = exiting(|a| {
            a.li(Reg::T0, Region::RAM.base()).load(Lw, Reg::A0, 2, Reg::T0);
        });
        let below = exiting(|a| {
            a.li(Reg::T0, Region::RAM.base()).load(Ld, Reg::A0, -8, Reg::T0);
        });
        let into_text = exiting(|a| {
            a.li(Reg::T0, Region::TEXT.base()).store(Sd, Reg::A0, 0, Reg::T0);
        });
        assert_eq!(
            run(&misaligned, vec![]),
            Err(Trap::Misaligned {
                pc,
                address: Region::RAM.base() + 2
            })
        );

        // Misaligned double words, at offsets a word would allow and at ones it would not.
        for offset in [4, 1] {
            let load = exiting(|a| {
                a.li(Reg::T0, Region::RAM.base()).load(Ld, Reg::A0, offset, Reg::T0);
            });
            let store = exiting(|a| {
                a.li(Reg::T0, Region::RAM.base()).store(Sd, Reg::A0, offset, Reg::T0);
            });
            for text in [load, store] {
                assert_eq!(
                    run(&text, vec![]),
                    Err(Trap::Misaligned {
                        pc,
                        address: Region::RAM.base() + offset as u64
                    }),
                    "offset {offset}"
                );
            }
        }
        assert_eq!(
            run(&below, vec![]),
            Err(Trap::Unmapped {
                pc,
                address: Region::RAM.base() - 8
            })
        );
        assert_eq!(
            run(&into_text, vec![]),
            Err(Trap::Unmapped {
                pc,
                address: Region::TEXT.base()
            })
        );

        // A hash block at no word address, and one below RAM.
        let unaligned_block = exiting(|a| {
            a.li(Reg::T0, Region::RAM.base() + 4)
                .blake2s(Reg::T0, Reg::T0, Reg::T0, Reg::ZERO, false);
        });
        let below_block = exiting(|a| {
            a.li(Reg::T0, Region::RAM.base() - 128)
                .blake2s(Reg::T0, Reg::T0, Reg::T0, Reg::ZERO, false);
        });
        // Both bases take two instructions to form, so the hash is the third.
        let pc = Region::TEXT.base() + 8;
        assert_eq!(
            run(&unaligned_block, vec![]),
            Err(Trap::Misaligned {
                pc,
                address: Region::RAM.base() + 4
            })
        );
        assert_eq!(
            run(&below_block, vec![]),
            Err(Trap::Unmapped {
                pc,
                address: Region::RAM.base() - 128
            })
        );

        // Falling off the text, a jump to address zero, EBREAK.
        let pc = Region::TEXT.base() + 4;
        let jump_to_zero = [Instruction::i(Opcode::Jalr, 0, Reg::ZERO, Reg::ZERO, 0).bits(), 0x13];
        assert_eq!(run(&[0x13], vec![]), Err(Trap::Illegal { pc }));
        assert_eq!(run(&jump_to_zero, vec![]), Err(Trap::Illegal { pc: 0 }));
        assert_eq!(
            run(&[0x0010_0073], vec![]),
            Err(Trap::Illegal {
                pc: Region::TEXT.base()
            })
        );

        // An ecall that is not exit.
        assert_eq!(
            run(&[Instruction::ECALL.bits()], vec![]),
            Err(Trap::NotAnExit { syscall: 0 })
        );
    }

    #[test]
    fn a_trapping_hash_writes_nothing() {
        // Fixture: RAM of 8 words, all 7: the chaining value and the result in its first words, the message past it.
        let text = Asm::new().blake2s(Reg::T0, Reg::T0, Reg::T1, Reg::ZERO, false).finish();
        let program = RiscvProgram::new(&text, Region::TEXT.base(), vec![7; 8], 3, 0).unwrap();
        let mut m = Machine::new(&program, &[]);
        m.registers.set(Reg::T0, Region::RAM.base());
        m.registers.set(Reg::T1, Region::RAM.base() + 64);

        // The step traps on the message's first word, before writing the result.
        assert_eq!(
            m.step(),
            Err(Trap::Unmapped {
                pc: Region::TEXT.base(),
                address: Region::RAM.base() + 64
            })
        );

        // The machine is as it was: same pc, RAM untouched.
        assert_eq!(m.pc(), Region::TEXT.base());
        assert_eq!(m.memory().ram(), [7; 8]);
    }

    #[test]
    fn a_run_out_of_steps_stops_where_it_is() {
        // A jump to itself never halts.
        let spin = [Instruction::j(Reg::ZERO, 0).bits()];
        assert_eq!(run(&spin, vec![]), Ok(None));
    }

    /// The memory layout and address map.
    mod memory {
        use super::super::*;
        use crate::rv::{Region, RiscvProgram};
        use proptest::prelude::*;

        proptest! {
            #[test]
            fn cell_maps_exactly_the_two_regions(address in prop_oneof![
                any::<u64>(),
                Region::RAM.base() - 16..Region::RAM.base() + 80,
                Region::ADVICE.base() - 16..Region::ADVICE.base() + 48,
            ]) {
                // Fixture: 8 cells of RAM, then 4 of advice.
                let program = RiscvProgram::new(&[0x13], Region::TEXT.base(), vec![], 3, 2).unwrap();
                let memory = Memory::new(&program, &[]);

                // Each byte of a region maps to its cell; no other address maps at all.
                let expected = if (Region::RAM.base()..Region::RAM.base() + 64).contains(&address) {
                    Some(((address - Region::RAM.base()) / 8) as usize)
                } else if (Region::ADVICE.base()..Region::ADVICE.base() + 32).contains(&address) {
                    Some(8 + ((address - Region::ADVICE.base()) / 8) as usize)
                } else {
                    None
                };
                prop_assert_eq!(memory.cell(address), expected);
            }
        }

        #[test]
        fn new_lays_out_the_image_and_the_advice() {
            // Fixture: a 2-word image in 4 cells of RAM, 1 word of advice in 2 cells.
            let program = RiscvProgram::new(&[0x13], Region::TEXT.base(), vec![7, 8], 2, 1).unwrap();
            let memory = Memory::new(&program, &[9]);

            // Each region is its initial words, then zeros.
            assert_eq!(memory.ram(), [7, 8, 0, 0]);
            assert_eq!(memory.advice(), [9, 0]);
        }
    }

    /// RISC-V straight from the specification, on registers and bytes.
    ///
    /// It shares no code with the decoder, the semantics or the word-addressed memory.
    ///
    /// The interpreter must agree with it on every instruction.
    mod spec {
        use super::super::Machine;
        use crate::rv::asm::*;
        use crate::rv::semantics::tests::edge_word;
        use crate::rv::{Region, RiscvProgram};
        use proptest::prelude::*;
        use proptest::sample::select;

        /// The fixture's RAM: 2^8 words.
        const LOG_RAM: usize = 8;

        /// The fixture's RAM in bytes.
        const RAM_BYTES: u64 = 8 << LOG_RAM;

        /// One step of the specification: update `x`, `pc` and `mem` for the instruction `word`.
        ///
        /// `mem` is RAM as bytes, from its base.
        fn spec_step(word: u32, x: &mut [u64; 32], pc: &mut u64, mem: &mut [u8]) {
            // The fields, read straight off the word.
            let (opcode, rd, f3) = (word & 0x7f, (word >> 7 & 31) as usize, word >> 12 & 7);
            let (rs1, rs2, f7) = ((word >> 15 & 31) as usize, (word >> 20 & 31) as usize, word >> 25);
            let (a, b) = (x[rs1], x[rs2]);
            let imm_i = (word as i32 >> 20) as i64 as u64;
            let at = |address: u64| (address - Region::RAM.base()) as usize;
            let w = |v: u64| v as i32 as i64 as u64;

            // Each opcode sets the result, the next pc, or memory.
            let mut next = pc.wrapping_add(4);
            let mut result = None;
            match opcode {
                // LUI and AUIPC.
                0x37 => result = Some((word & 0xffff_f000) as i32 as i64 as u64),
                0x17 => result = Some(pc.wrapping_add((word & 0xffff_f000) as i32 as i64 as u64)),

                // JAL: link, and jump by the 21-bit offset.
                0x6f => {
                    let o = ((word >> 31) << 20)
                        | ((word >> 12 & 0xff) << 12)
                        | ((word >> 20 & 1) << 11)
                        | ((word >> 21 & 0x3ff) << 1);
                    result = Some(next);
                    next = pc.wrapping_add(((o << 11) as i32 >> 11) as i64 as u64);
                }

                // JALR: link, and jump to rs1 + imm with bit 0 cleared.
                0x67 => {
                    result = Some(next);
                    next = a.wrapping_add(imm_i) & !1;
                }

                // Branches, by the 13-bit offset.
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

                // Loads: little-endian bytes, extended.
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

                // Stores: the low 2^f3 bytes.
                0x23 => {
                    let imm = (((f7 << 5) | rd as u32) << 20) as i32 >> 20;
                    let p = at(a.wrapping_add(imm as i64 as u64));
                    let n = 1 << f3;
                    mem[p..p + n].copy_from_slice(&b.to_le_bytes()[..n]);
                }

                // Integer arithmetic: 64- or 32-bit, register or immediate, base or M.
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

            // Write back, except to x0.
            if let Some(r) = result
                && rd != 0
            {
                x[rd] = r;
            }
            *pc = next;
        }

        /// A memory access the test must aim at RAM: the base register, the offset, the log of the width.
        type Access = (Reg, i32, u32);

        /// A random legal instruction, and the access it makes, if any.
        ///
        /// Register-register operations are drawn twice as often as each other kind.
        fn instruction() -> impl Strategy<Value = (u32, Option<Access>)> {
            // A memory base is never x0, so the test can point it anywhere.
            let base = (1u8..32).prop_map(|i| Reg::new(i).expect("below 32"));
            let imm = -2048i32..2048;
            prop_oneof![
                2 => (select(&RegOp::ALL[..]), any::<Reg>(), any::<Reg>(), any::<Reg>()).prop_map(|(op, rd, rs1, rs2)| (op.encode(rd, rs1, rs2).bits(), None)),
                1 => (select(&ImmOp::ALL[..]), any::<Reg>(), any::<Reg>(), imm.clone()).prop_map(|(op, rd, rs1, imm)| (op.encode(rd, rs1, imm).bits(), None)),
                1 => (select(&ShiftOp::ALL[..]), any::<Reg>(), any::<Reg>(), any::<u32>()).prop_map(|(op, rd, rs1, amount)| (op.encode(rd, rs1, amount).bits(), None)),
                1 => (select(&LoadOp::ALL[..]), any::<Reg>(), base.clone(), imm.clone())
                    .prop_map(|(op, rd, base, imm)| (op.encode(rd, base, imm).bits(), Some((base, imm, op.log_width())))),
                1 => (select(&StoreOp::ALL[..]), any::<Reg>(), base, imm.clone())
                    .prop_map(|(op, rs2, base, imm)| (op.encode(rs2, base, imm).bits(), Some((base, imm, op.log_width())))),
                1 => (select(&BranchOp::ALL[..]), any::<Reg>(), any::<Reg>(), -1024i32..1024).prop_map(|(op, rs1, rs2, k)| (op.encode(rs1, rs2, 4 * k).bits(), None)),
                1 => (any::<Reg>(), -(1i32 << 17)..1 << 17).prop_map(|(rd, k)| (Instruction::j(rd, 4 * k).bits(), None)),
                1 => (any::<Reg>(), any::<Reg>(), imm).prop_map(|(rd, rs1, imm)| (Instruction::i(Opcode::Jalr, 0, rd, rs1, imm).bits(), None)),
                1 => (select(&[Opcode::Lui, Opcode::Auipc][..]), any::<Reg>(), any::<u32>()).prop_map(|(op, rd, imm)| (Instruction::u(op, rd, imm).bits(), None)),
            ]
        }

        proptest! {
            #![proptest_config(ProptestConfig::with_cases(20_000))]

            #[test]
            fn every_instruction_matches_the_specification(
                (word, access) in instruction(),
                regs in proptest::array::uniform31(edge_word()),
                image in proptest::collection::vec(any::<u64>(), 1 << LOG_RAM),
                slot in 0u64..RAM_BYTES - 8,
            ) {
                // Fixture: one instruction, a random RAM image and random registers.
                let program = RiscvProgram::new(&[word], Region::TEXT.base(), image, LOG_RAM, 0).expect("a legal instruction");
                let mut m = Machine::new(&program, &[]);
                for (r, &value) in (1..32).filter_map(Reg::new).zip(&regs) {
                    m.registers.set(r, value);
                }

                // Aim a memory access at an aligned address in RAM.
                if let Some((base, imm, log_width)) = access {
                    let address = Region::RAM.base() + (slot & !((1 << log_width) - 1));
                    m.registers.set(base, address.wrapping_sub(imm as i64 as u64));
                }

                // The specification's state, from the same start.
                let mut x: [u64; 32] = m.registers().cells()[..32].try_into().unwrap();
                let mut mem: Vec<u8> = m.memory().ram().iter().flat_map(|w| w.to_le_bytes()).collect();
                let mut pc = m.pc;

                // One step each: same registers, same pc, same RAM.
                spec_step(word, &mut x, &mut pc, &mut mem);
                m.step().unwrap_or_else(|trap| panic!("{word:#010x}: {trap}"));
                prop_assert_eq!(m.registers().cells()[..32].to_vec(), x.to_vec(), "{:#010x}: registers", word);
                prop_assert_eq!(m.pc, pc, "{:#010x}: pc", word);
                let ram: Vec<u8> = m.memory().ram().iter().flat_map(|w| w.to_le_bytes()).collect();
                prop_assert_eq!(ram, mem, "{:#010x}: RAM", word);
            }
        }
    }
}
