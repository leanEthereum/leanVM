/-
  Rv64mc.Proof.Layout.QkeccakSlot

  `qkeccak_slot` keeps its contract (`Spec.Layout.QkeccakSlot.spec`): two comparisons pick the range of
  `Model.qkeccakSlotRust_closed` the column lies in.
-/

import Rv64mc.Spec.Layout.QkeccakSlot
import Rv64mc.Model.Extra.Layout
import Rv64mc.Gen.Tmpl.Verifier.Layout.QkeccakSlot
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Layout.QkeccakSlot

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Layout Rv64mc.Spec.Layout.QkeccakSlot
open Rv64mc.Gen.Verifier.Layout.QkeccakSlot (Link tmpl)

theorem none_lt {c : Word} (h : c < 66#64) :
    match Model.qkeccakSlotRust c.toNat with
    | none => (0#64 : Word) = 0#64
    | some v => (0#64 : Word) = 1#64 ∧ (66#64 : Word) = BitVec.ofNat 64 v := by
  rw [Model.qkeccakSlotRust_closed, ite_eq_left (by rw [BitVec.lt_def] at h; simpa using h)]

theorem spare {c : Word} (h1 : 66#64 ≤ c) (h2 : c ≤ 79#64) :
    match Model.qkeccakSlotRust c.toNat with
    | none => (1#64 : Word) = 0#64
    | some v => (1#64 : Word) = 1#64 ∧ c + 18446744073709551600#64 = BitVec.ofNat 64 v := by
  rw [BitVec.le_def] at h1 h2
  simp only [BitVec.toNat_ofNat] at h1 h2
  rw [Model.qkeccakSlotRust_closed, ite_eq_right (by omega), ite_eq_left (by omega)]
  refine ⟨rfl, ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

theorem lane {c : Word} (h2 : 79#64 < c) :
    match Model.qkeccakSlotRust c.toNat with
    | none => BinOp.ult.eval (c + 18446744073709551535#64) 25#64 = 0#64
    | some v => BinOp.ult.eval (c + 18446744073709551535#64) 25#64 = 1#64 ∧
      c + 18446744073709551535#64 = BitVec.ofNat 64 v := by
  rw [BitVec.lt_def] at h2
  simp only [BitVec.toNat_ofNat] at h2
  have hc := c.isLt
  have hv : (c + 18446744073709551535#64).toNat = (c.toNat + 18446744073709551535) % 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Model.qkeccakSlotRust_closed, ite_eq_right (by omega), ite_eq_right (by omega)]
  by_cases h : 81 ≤ c.toNat ∧ c.toNat < 106
  · rw [ite_eq_left h]
    refine ⟨?_, ?_⟩
    · simp only [BinOp.eval, BitVec.ult, hv]; rw [ite_eq_left (by simp; omega)]; rfl
    · apply BitVec.eq_of_toNat_eq; rw [hv, BitVec.toNat_ofNat]; omega
  · rw [ite_eq_right h]
    simp only [BinOp.eval, BitVec.ult, hv]; rw [ite_eq_right (by simp; omega)]; rfl

theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) :
    spec env p i := by
  rv_auto hp
  · exact spare hc_1 hc
  · exact lane hc
  · exact none_lt hc

end Rv64mc.Proof.Layout.QkeccakSlot
