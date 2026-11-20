# The statement's machine as the meet of riscv-zkvm's two

`Rv64mc/Probe/StepMeet.lean` defines the machine the end statement will name and proves that every step of it is a step of SP1's `stepSp1` (`step_stepSp1`) and of riscv-zkvm's generic `step` (`step_step`), both without `sorry`. An accepting run of ours is then an accepting run of the machine machine-checked's `SafeN` is about (`detStep stepSp1`), and also of braid's `Rv64.step`, which is the generic `step`.

```lean
def inWindow (a : Word) (w : Nat) : Bool :=
  (decide (0x10000000 ≤ a.toNat) && decide (a.toNat + w ≤ 0x78000000)) ||
    (decide (0xa0000000 ≤ a.toNat) && decide (a.toNat + w ≤ 0xc0000000))

def memOk (s : MachineState) (i : Instr) : Bool :=
  memOkSp1 s i && match memAccess s i with
    | none => true
    | some (a, w, _) => inWindow a w

def step (s : MachineState) : Option MachineState :=
  match s.code s.pc with
  | none | some .ECALL | some .EBREAK | some (.CSRS ..) => none
  | some i => if memOk s i then some (execInstrBr s i) else none

theorem step_stepSp1 {s t} (h : step s = some t) : stepSp1 s = some t
theorem step_step {s t} (h : step s = some t) : RiscvZkvm.Rv64.step s = some t
```

`memOk` is `memOkSp1` literally (address below `SP1_MAX_MEMORY = 2^37`, natural alignment for 2, 4 and 8 bytes, and for a store `noCodeAt`: no 4-aligned code word overlaps it), and the access lies wholly in one of the guest's windows (`guest/link.x`, `guest/src/main.rs`): input and heap `0x10000000..0x78000000` (input at `0x10000000`, heap `0x20000000..0x78000000`), and `.rodata`, `.data`, `.bss` and the stack `0xa0000000..0xc0000000` (stack top `0xbffffff0`). Code (`0x80000000`) is in no window, so a load from code traps too.

How the arms meet:

- SP1 (`stepSp1`): every non-memory instruction but `ECALL`, `EBREAK`, `CSRS` executes; a load or store executes iff `memOkSp1`. Ours executes a subset.
- Generic (`step`): `LD`/`SD` need `isValidDwordAccess` (in a zone and 8-aligned), `LW`/`LWU`/`SW` 4-aligned, `LH`/`LHU`/`SH` 2-aligned, bytes none, and the zones are `[0x20, 0x78000000]`, `[0x40000000, 0x40002000]`, `[0xa0000000, 0xc0000000]`, checked on the start address only. Our windows lie inside the first and third zones and the alignments are the same (`alignedFor`), so ours implies the generic check. The generic machine does not check `noCodeAt` on stores; ours does, which only makes ours trap more.
- `ECALL` is no step of ours, so a run stops at it; the end statement's `Halts` asks that state to be the halting one (`t0 = 0`, `a0 = 0`), which is machine-checked's `Accepted`. `stepSp1` at that state goes to `sp1Ecall`, whose host branch is the generic `step`, which returns `none` for `t0 = 0`: both machines stop there as well.

What this leaves out, as the design says: a deployment that executes where ours traps (a misaligned or out-of-window access, a store into code) is not covered. Both proofs are a case split and `omega`, under 20 s to check.
