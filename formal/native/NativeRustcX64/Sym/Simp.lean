module

public import NativeRustcX64.Sym.Sound

/-!
# Reading a block's summary

What a proof reads off `Match env S' m'` after a block: a known register's value
(`Match.regs`), the known flags (`Match.flags`), and the integer `Mem.loadInt` gives for up to 8
bytes in a region (`Match.read`), each as the evaluation of a symbolic value of the literal `S'`.
`sym_simp` unfolds such an evaluation to plain `BitVec` terms over the environment's atoms
(`env.regs r`, `env.load r off n`, `env.base r`, `label l`, `env.ret`).
-/

namespace NativeRustcX64.Sym

public section

variable [Labels] {env : Env} {S : SState} {m : MachineData}

/-- **The bytes of a region after a block**: the `n ≤ 8` bytes at `o` in region `r` hold the
symbolic load `Sym.loadSym S.mem r o n` (computed from the literal `S` by `rfl`). -/
theorem Match.read (hm : Match env S m) (hwf : env.WF) {r o n sz : Nat}
    (hr : S.regions[r]? = some sz) (hle : o + n ≤ sz) (hn : n ≤ 8) :
    Mem.loadInt m.dmem (env.base r + BitVec.ofNat 64 o) n =
      some (((NativeRustcX64.Sym.loadSym S.mem r o n).eval env).toNat : Int) := by
  obtain ⟨b, hb⟩ := hm.regions r sz hr
  rw [Env.base_eq hb]
  exact (hm.loadSym hwf hb hle hn).1

end

/-- Unfolds the evaluation of symbolic values and booleans to `BitVec` terms. -/
macro "sym_simp" : tactic =>
  `(tactic| simp only [Sym.eval, SBool.eval, BinOp.apply, UnOp.apply, TernOp.apply, CmpOp.apply,
    low_W64, ext_W64, bytesOf])

end NativeRustcX64.Sym
