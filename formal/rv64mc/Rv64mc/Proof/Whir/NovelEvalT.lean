/-
  Rv64mc.Proof.Whir.NovelEvalT

  `novel_eval(coefficients, what)` is total (`specT`): from `coefficients` (`a0`, `a1` elements) none or in a window
  and 8-byte aligned, and `what` (`a2`, `a3`) as `novel_basis` asks (`NovelBasisT.SliceK`), it returns, writing
  nothing of its caller's besides what it allocates, or the run ends with `a0 = 2` where `novel_basis` does. It builds
  the basis of `a1` `K`s in its frame (`NovelBasisT`), then the zip of the coefficients with the basis and sums it
  (`ESumNovelT`: the zip's index `0`, both sides slices, the basis's from `novel_basis`'s `VecT`). Safety only: the
  partial contract's value (`Spec.Whir.Subspace.evalSpec`, `Model.novelEvalRust`) is owed (class C).

  ## Main definitions

  * `PreT`, `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Whir.NovelBasisT
import Rv64mc.Proof.Field.ESumNovelT
import Rv64mc.Gen.Tmpl.Verifier.Whir.NovelEval

namespace Rv64mc.Proof.Whir.NovelEvalT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT RawVecT VecT)
open Rv64mc.Gen.Verifier.Whir.NovelEval (Link tmpl)

/-- The total precondition: `coefficients` (`a1` elements at `a0`) none, or in a window and 8-byte aligned; `what`
    (`a3` `K`s at `a2`) `SliceK`. -/
def PreT (env : Env) (regs : Reg → Word) (_m : MachineState) : Prop :=
  ((regs .x11).toNat = 0 ∨ InWin env (regs .x10) (16 * (regs .x11).toNat) ∧ (regs .x10).toNat % 8 = 0) ∧
    NovelBasisT.SliceK env (regs .x12) (regs .x13)

/-- **The total contract of `novel_eval`**: it returns, writing nothing of its caller's, or `a0 = 2`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (fun _ _ _ _ => True) (Stop := AbortStop)

/-- The coefficients' slice, as the zip reads it (`a0` to `a0 + 16 a1`). -/
theorem eslice {env : Env} {q n : Word}
    (h : n.toNat = 0 ∨ InWin env q (16 * n.toNat) ∧ q.toNat % 8 = 0) :
    q.toNat ≤ (q + n <<< 4).toNat ∧
      (q + n <<< 4 = q ∨ InWin env q ((q + n <<< 4).toNat - q.toNat) ∧ q.toNat % 8 = 0) := by
  rcases h with h0 | ⟨hw, ha⟩
  · have : n = 0#64 := BitVec.eq_of_toNat_eq h0
    subst this; simp
  · have := hw.lt
    have e : (q + n <<< 4).toNat = q.toNat + 16 * n.toNat := Runtime.WinT.elem_toNat (s := 4) (by omega)
    rw [e]; exact ⟨by omega, .inr ⟨by rw [show q.toNat + 16 * n.toNat - q.toNat = 16 * n.toNat by omega]; exact hw, ha⟩⟩

/-- The basis's slice, from `novel_basis`'s `VecT` (its buffer `BufT`, the length at most the capacity). -/
theorem kslice {env : Env} {m : MachineState} {P L C : Word}
    (hb : C.toNat = 0 ∨ (0x10000000 ≤ P.toNat ∧ env.Live m P (C.toNat * 8) ∧ P.toNat % 8 = 0))
    (hl : L.toNat ≤ C.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) :
    P.toNat + 8 * L.toNat < 2 ^ 64 ∧ Field.ESumNovelT.SliceW env P (P + L <<< 3) := by
  have hhe := env.heapEnd.isLt
  rcases hb with h0 | ⟨hlo, hlv, ha⟩
  · have : L = 0#64 := BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat]; omega)
    subst this; simp only [BitVec.zero_shiftLeft, BitVec.add_zero]
    exact ⟨by have := P.isLt; omega, le_rfl, .inl rfl⟩
  · unfold Env.Live at hlv
    have e : (P + L <<< 3).toNat = P.toNat + 8 * L.toNat := Runtime.WinT.elem_toNat (s := 3) (by omega)
    refine ⟨by omega, by rw [e]; omega, .inr ⟨?_, ha⟩⟩
    rw [e, show P.toNat + 8 * L.toNat - P.toNat = 8 * L.toNat by omega]
    exact .inl ⟨hlo, by omega⟩

set_option rv_sym.heap true in
/-- **`novel_eval` is total.** -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needB needS : Nat} (hnB : 112 + needB ≤ need) (hnS : 112 + needS ≤ need)
    (hnb : NovelBasisT.specT env p L.novelBasis.idx needB)
    (hsum : Field.ESumNovelT.SumSafeT env p L.sumMapZipIterEIntoIterKNovelEvalClosure0.idx needS) :
    specT env p i need := by
  rv_autoT hp with [hL] using [hnb, hsum]
  -- the coefficients
  · exact (eslice hpre_6).1
  · exact (eslice hpre_6).2
  all_goals
    obtain ⟨hcA, hpA, hcV, hpV, hlV⟩ := Runtime.SavedT.hdr_at top 18446744073709551504#64 m1
    simp only [BitVec.reduceAdd] at hpA hpV hlV
    rw [hcA, hpA] at hret1_19
    rw [hcV, hlV] at hret1_21
    have hk := kslice hret1_19 hret1_21 (Nat.le_trans (by unfold Env.Live at *; omega) hret1_14.2.1)
  -- the basis
  · simp only [Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, BitVec.add_assoc, BitVec.reduceAdd]
    simp [MachineState.getMem_setMem_eq, MachineState.getMem_setMem_ne, BitVec.add_right_inj]
    have := hk.1
    rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  · exact hk.2.2

end Rv64mc.Proof.Whir.NovelEvalT

/-- info: 'Rv64mc.Proof.Whir.NovelEvalT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Whir.NovelEvalT.total
