/-
  Rv64mc.Proof.Layout.Table

  `Table::n_constraints` and `Table::count_columns` keep their contracts (`Spec.Layout.Table`): a bounds check
  against six, then a word, or a slice's two words, of a constant table read through `NConstraintsData`,
  `CountColumnsData`.
-/

import Rv64mc.Spec.Layout.Table
import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Gen.Tmpl.Verifier.Layout.Table.NConstraints
import Rv64mc.Gen.Tmpl.Verifier.Layout.Table.CountColumns
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Layout.Table

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Layout.Table

/-- An index of at most five, shifted as the code scales it. -/
theorem shl_small {x : Word} (h : x ≤ 5#64) (s : Nat) :
    x <<< s = BitVec.ofNat 64 (2 ^ s * x.toNat) ∧ x.toNat ≤ 5 := by
  rw [BitVec.le_def, BitVec.toNat_ofNat] at h
  refine ⟨BitVec.eq_of_toNat_eq ?_, by omega⟩
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_comm]

theorem nConstraints (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Gen.Verifier.Layout.Table.NConstraints.Link)
    (hp : p[i]? = some (Gen.Verifier.Layout.Table.NConstraints.tmpl L)) (hL : L.WF p)
    (hpanic : Spec.Runtime.NoReturn env p L.panicBoundsCheck.idx 0)
    (hdata : NConstraintsData env L.d_c48_401b839e) : nConstraintsSpec env p i := by
  rv_auto hp with [hL] using [hpanic]
  obtain ⟨e, hk⟩ := shl_small hc 3
  rw [e, show 2 ^ 3 * (regs .x10).toNat = 8 * (regs .x10).toNat from rfl, hdata.get hpre_4 _ (by simp [Model.nConstraintsRust]; omega)]
  simp [List.getElem?_eq_getElem (show (regs .x10).toNat < Model.nConstraintsRust.length by
    simp [Model.nConstraintsRust]; omega)]

theorem countColumns (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Gen.Verifier.Layout.Table.CountColumns.Link)
    (hp : p[i]? = some (Gen.Verifier.Layout.Table.CountColumns.tmpl L)) (hL : L.WF p)
    (hpanic : Spec.Runtime.NoReturn env p L.panicBoundsCheck.idx 0)
    (hdata : CountColumnsData env L.d_c96_da3654e1) : countColumnsSpec env p i := by
  rv_auto hp with [hL] using [hpanic]
  obtain ⟨e, hk⟩ := shl_small hc 4
  obtain ⟨q, hq⟩ := hdata (regs .x10).toNat (by omega)
  intro M hM
  obtain ⟨h1, h2, -⟩ := hq m hpre_4
  obtain ⟨-, -, h3⟩ := hq M hM
  have e8 : L.d_c96_da3654e1.hi + L.d_c96_da3654e1.lo + BitVec.ofNat 64 (16 * (regs .x10).toNat) + 8#64 =
      L.d_c96_da3654e1.hi + L.d_c96_da3654e1.lo + BitVec.ofNat 64 (16 * (regs .x10).toNat + 8) := by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp
  rw [e, show 2 ^ 4 * (regs .x10).toNat = 16 * (regs .x10).toNat from rfl, e8, h1, h2]
  exact ⟨by simp, h3⟩

end Rv64mc.Proof.Layout.Table
