module

public import NativeRustcArm.Sym.Sound

/-!
# Reading a block's summary

What a proof reads off `Match env S' m'` after a block: a known register's value
(`Match.regs`), SP (`Match.sp`), the flags (`Match.flagsEq`), and the integer `Mem.loadInt` gives
for up to 8 bytes in a region (`Match.read`), each as the evaluation of a symbolic value of the
literal `S'`; and a bound it adds for the next block (`Match.addBound`). `sym_simp` unfolds such an evaluation to plain `BitVec` terms over the environment's
atoms (`env.regs r`, `env.load r off n`, `env.base r`, `label l`).
-/

namespace NativeRustcArm.Sym

public section

variable [Labels] {env : Env} {S : SState} {m : MachineData}

/-- **The bytes of a region after a block**: the `n ≤ 8` bytes at `o` in region `r` hold the
symbolic load `Sym.loadSym S.mem r o n` (computed from the literal `S` by `rfl`). -/
theorem Match.read (hm : Match env S m) (hwf : env.WF) {r o n sz : Nat} {al : Bool}
    (hr : S.regions[r]? = some (sz, al)) (hle : o + n ≤ sz) (hn : n ≤ 8) :
    Mem.loadInt m.dmem (env.base r + BitVec.ofNat 64 o) n =
      some (((NativeRustcArm.Sym.loadSym S.mem r o n).eval env).toNat : Int) := by
  obtain ⟨b, hb, -⟩ := hm.regions r sz al hr
  rw [Env.base_eq hb]
  exact (hm.loadSym hwf hb hle hn).1

/-- A bound the state records, for indexed loads (e.g. the condition of the branch the block
did not take). -/
theorem Match.addBound (hm : Match env S m) {x : Sym} {n : Nat} (h : (x.eval env).toNat < n) :
    Match env { S with bounds := (x, n) :: S.bounds } m :=
  ⟨hm.regs, hm.sp, hm.flags, hm.regions, hm.mem, hm.labels, fun y k hy => by
    rcases List.mem_cons.mp hy with hy | hy
    · cases hy
      exact h
    · exact hm.bounds y k hy, hm.aliases, hm.outside⟩

end

/-- Unfolds the evaluation of symbolic values and booleans to `BitVec` terms, in the goal or at
the given hypotheses. -/
syntax "sym_simp" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| sym_simp $[$loc]?) =>
    `(tactic| simp only [NativeRustcArm.Sym.eval, NativeRustcArm.SBool.eval,
      NativeRustcArm.SFlags.eval, NativeRustcArm.BinOp.apply, NativeRustcArm.UnOp.apply,
      NativeRustcArm.CmpOp.apply, NativeRustcArm.Sym.low_W64, NativeRustcArm.Sym.ext_W64,
      NativeRustcArm.Sym.low_W32, NativeRustcArm.Sym.ext_W32, NativeRustcArm.shiftW,
      NativeRustcArm.Sym.bytesOf, NativeRustcArm.revW] $[$loc]?)

end NativeRustcArm.Sym
