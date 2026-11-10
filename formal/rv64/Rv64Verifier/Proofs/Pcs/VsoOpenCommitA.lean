import Rv64Verifier.Proofs.Pcs.VsoOpenFinal

/-!
# `verify_stacked_opening`'s level loop: the commitment's bytes and model

Below the last level `0x8000a534` reads the next root (`next_scalars(2)`, `Digest::from_halves`):
`0x8000a588` copies the halves' words to `S - 384` and keeps the root's bytes `7..31` in
callee-saved registers and spills (`B58`) through `samples`, `next_scalar` and
`sumcheck_round_poly`, and `0x8000a698` reassembles them (`a698_words`). The mirror's level opens
with `TM.commit` (`afk_commit`), the root `dOf` of the two scalars (`fromHalves_eAt`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol LeanVM.Protocol.KeccakHash
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The first half's bytes `0..6` merged into a doubleword. -/
theorem low7b (old w : Word) :
    Sym.StoreKind.b.merge
      (Sym.StoreKind.h.merge (Sym.StoreKind.w.merge old 0 w) 4
        (BitVec.signExtend 64 (extractHalfword w (4 / 2))))
      6 (BitVec.zeroExtend 64 (extractByte w 6)) &&& 0x00ffffffffffffff =
    w &&& 0x00ffffffffffffff := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Sym.StoreKind.merge, replaceWord32, replaceHalfword, replaceByte, extractHalfword,
    BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.zeroExtend_eq_setWidth, getLsbD_extractByte,
    BitVec.getLsbD_signExtend]
  interval_cases i <;> simp

/-- After `0x8000a588`: the root's bytes `7..23` and doubleword `w3` (of `w0`..`w3`) in the
callee-saved registers and the spills from `P + 32`. -/
structure B58 (u : MachineState) (P w0 w1 w2 w3 : Word) : Prop where
  x18 : u.getReg .x18 = zb w1 2
  x19 : u.getReg .x19 = zb w1 6
  x20 : u.getReg .x20 = w3
  x21 : u.getReg .x21 = zb w1 4
  x22 : u.getReg .x22 = zb w1 5
  x23 : u.getReg .x23 = zb w1 0
  x24 : u.getReg .x24 = zb w1 1
  x25 : u.getReg .x25 = zb w2 0
  m56 : u.getMem (P + 56#64) = zb w2 6
  m64 : u.getMem (P + 64#64) = zb w2 5
  m32 : u.getMem (P + 32#64) = zb w2 4
  m72 : u.getMem (P + 72#64) = zb w2 3
  m40 : u.getMem (P + 40#64) = zb w2 2
  m48 : u.getMem (P + 48#64) = zb w2 1
  m80 : u.getMem (P + 80#64) = zb w1 7
  m88 : u.getMem (P + 88#64) = zb w1 3
  m96 : u.getMem (P + 96#64) = zb w0 7
  m120 : u.getMem (P + 120#64) = w2

theorem b58_of {u t : MachineState} (h : b8000a588.Holds u t) :
    B58 t (u.getReg .x2) (u.getMem (u.getReg .x1)) (u.getMem (u.getReg .x1 + 8#64))
      (u.getMem (u.getReg .x1 + 24#64)) (u.getMem (u.getReg .x1 + 32#64)) where
  x18 := h.reg_eq .x18 rfl (by rv_eval [])
  x19 := h.reg_eq .x19 rfl (by rv_eval [])
  x20 := h.reg_eq .x20 rfl (by rv_eval [])
  x21 := h.reg_eq .x21 rfl (by rv_eval [])
  x22 := h.reg_eq .x22 rfl (by rv_eval [])
  x23 := h.reg_eq .x23 rfl (by rv_eval [])
  x24 := h.reg_eq .x24 rfl (by rv_eval [])
  x25 := h.reg_eq .x25 rfl (by rv_eval [])
  m56 := h.mem_eq 1 (by decide) (by rv_eval []) (by rv_eval [])
  m64 := h.mem_eq 2 (by decide) (by rv_eval []) (by rv_eval [])
  m32 := h.mem_eq 3 (by decide) (by rv_eval []) (by rv_eval [])
  m72 := h.mem_eq 4 (by decide) (by rv_eval []) (by rv_eval [])
  m40 := h.mem_eq 5 (by decide) (by rv_eval []) (by rv_eval [])
  m48 := h.mem_eq 6 (by decide) (by rv_eval []) (by rv_eval [])
  m80 := h.mem_eq 7 (by decide) (by rv_eval []) (by rv_eval [])
  m88 := h.mem_eq 8 (by decide) (by rv_eval []) (by rv_eval [])
  m96 := h.mem_eq 9 (by decide) (by rv_eval []) (by rv_eval [])
  m120 := h.mem_eq 11 (by decide) (by rv_eval []) (by rv_eval [])

/-- Kept by a step that keeps the callee-saved registers and the spills. -/
theorem B58.keep {u v : MachineState} {P w0 w1 w2 w3 : Word} {X : Word → Prop}
    (h : B58 u P w0 w1 w2 w3) (hr : ∀ r ∈ [Reg.x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25],
      v.getReg r = u.getReg r) (hX : DFrame u v X)
    (hXm : ∀ a, X a → ¬ Within a (P + 32) 96) (hP : P.toNat + 128 ≤ 2 ^ 64) :
    B58 v P w0 w1 w2 w3 := by
  have k (o : ℕ) (h1 : 32 ≤ o) (h2 : o ≤ 120) : v.getMem (P + BitVec.ofNat 64 o) =
      u.getMem (P + BitVec.ofNat 64 o) :=
    hX _ fun i hi hw ↦ hXm _ hw (by addr_omega [hi, h1, h2, hP])
  exact {
    x18 := by rw [hr .x18 (by decide)]; exact h.x18
    x19 := by rw [hr .x19 (by decide)]; exact h.x19
    x20 := by rw [hr .x20 (by decide)]; exact h.x20
    x21 := by rw [hr .x21 (by decide)]; exact h.x21
    x22 := by rw [hr .x22 (by decide)]; exact h.x22
    x23 := by rw [hr .x23 (by decide)]; exact h.x23
    x24 := by rw [hr .x24 (by decide)]; exact h.x24
    x25 := by rw [hr .x25 (by decide)]; exact h.x25
    m56 := (k 56 (by decide) (by decide)).trans h.m56
    m64 := (k 64 (by decide) (by decide)).trans h.m64
    m32 := (k 32 (by decide) (by decide)).trans h.m32
    m72 := (k 72 (by decide) (by decide)).trans h.m72
    m40 := (k 40 (by decide) (by decide)).trans h.m40
    m48 := (k 48 (by decide) (by decide)).trans h.m48
    m80 := (k 80 (by decide) (by decide)).trans h.m80
    m88 := (k 88 (by decide) (by decide)).trans h.m88
    m96 := (k 96 (by decide) (by decide)).trans h.m96
    m120 := (k 120 (by decide) (by decide)).trans h.m120 }

/-- `0x8000a698`'s doublewords: the root's bytes `7..14`, `15..22`, `23`, `24..31`. -/
theorem a698_words {u v : MachineState} {w0 w1 w2 w3 : Word} (h : b8000a698.Holds u v)
    (hB : B58 u (u.getReg .x2) w0 w1 w2 w3) :
    v.getMem (u.getReg .x2 + 96) = w0 >>> 56 ||| w1 <<< 8 ∧
      v.getMem (u.getReg .x2 + 88) = w1 >>> 56 ||| w2 <<< 8 ∧
      v.getMem (u.getReg .x2 + 120) = w2 >>> 56 ∧ v.getMem (u.getReg .x2 + 104) = w3 := by
  have m120 : v.getMem (u.getReg .x2 + 120) = _ := h.mem_eq 0 (by decide) (by rv_eval []) rfl
  have m88 : v.getMem (u.getReg .x2 + 88) = _ := h.mem_eq 1 (by decide) (by rv_eval []) rfl
  have m96 : v.getMem (u.getReg .x2 + 96) = _ := h.mem_eq 2 (by decide) (by rv_eval []) rfl
  have m104 : v.getMem (u.getReg .x2 + 104) = _ := h.mem_eq 3 (by decide) (by rv_eval []) rfl
  simp only [reduceMem, List.getElem_cons_succ, List.getElem_cons_zero, Sym.E.eval,
    Sym.BinOp.eval, hB.x18, hB.x19, hB.x20, hB.x21, hB.x22, hB.x23, hB.x24, hB.x25, hB.m56,
    hB.m64, hB.m32, hB.m72, hB.m40, hB.m48, hB.m80, hB.m88, hB.m96, hB.m120] at m96 m88 m120 m104
  refine ⟨m96.trans ?_, m88.trans ?_, m120.trans ?_, m104⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight, BitVec.zeroExtend_eq_setWidth, getLsbD_extractByte]
    interval_cases i <;> simp

/-! ## The root -/

/-- The root `Digest::from_halves` makes of the two scalars at `p` and `p + 24`. -/
def dOf (u : MachineState) (p : Word) : Digest :=
  #v[((eAt u p).limb 0).lane, ((eAt u p).limb 1).lane, ((eAt u (p + 24)).limb 0).lane,
    ((eAt u (p + 24)).limb 1).lane]

theorem fromHalves_eAt (u : MachineState) (p : Word) (h0 : u.getMem (p + 16) = 0)
    (h1 : u.getMem (p + 24 + 16) = 0) :
    digestFromHalves (eAt u p, eAt u (p + 24)) = some (dOf u p) := by
  have c0 : IsCanonical128 (eAt u p) := by
    show BF64.ofBitVec (u.getMem (p + 16)) = 0
    rw [h0]; rfl
  have c1 : IsCanonical128 (eAt u (p + 24)) := by
    show BF64.ofBitVec (u.getMem (p + 24 + 16)) = 0
    rw [h1]; rfl
  simp only [digestFromHalves, c0, c1, and_self, ite_true]
  rfl

theorem dOf_get (u : MachineState) (p : Word) :
    (dOf u p)[0].toBitVec = u.getMem p ∧ (dOf u p)[1].toBitVec = u.getMem (p + 8) ∧
      (dOf u p)[2].toBitVec = u.getMem (p + 24) ∧ (dOf u p)[3].toBitVec = u.getMem (p + 24 + 8) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## The mirror below the last level -/

/-- Below the last level, the mirror commits to the next root, samples the out-of-domain point,
reads its value and the intro message, then grinds. -/
theorem afk_commit (s : MachineState) (x : LCtx) {ℓ : ℕ} (hl : ℓ ≠ K0 s + 1) (hlt : ℓ < K0 s + 2)
    (W : Model.Pcs.WhirLocals × List E) :
    AFk s x ℓ W =
      Model.TM.commit ((s.getReg .x12).toNat - W.1.folds.length - fcOf s (ℓ + 1) + rtOf s (ℓ + 1))
        (3 * 2 ^ fcOf s (ℓ + 1)) >>= fun _ ↦
      Model.TM.samples ((s.getReg .x12).toNat - W.1.folds.length) >>= fun p ↦
      Model.TM.nextScalar >>= fun v ↦ Model.TM.sumcheckRoundPoly 3 v none >>= fun i ↦
      Model.Pcs.afterCommit (s.getReg .x12).toNat (cfgOf s) (basisOf s x) ℓ (fcOf s ℓ)
        (rtOf s ℓ) (restOf s ℓ) W.1 W.2 ([], [(i, Model.Pcs.GluedWeightRust.ood p)]) := by
  obtain ⟨W, lfs⟩ := W
  have hlen : ¬ ℓ = (cfgOf s).folds.length - 1 := by
    simp only [cfgOf, Model.Pcs.ladderFolds, List.length_cons, List.length_replicate]; omega
  rw [AFk, Model.Pcs.afterFolds_eq]
  simp only [Model.Pcs.levelOpen, ite_eq_right_of_eq_false _ _ (eq_false hlen), bind_assoc,
    pure_bind, zip_drop s (show ℓ + 1 < K0 s + 2 by omega)]

/-- The next level's root shape, from the folds through this level. -/
theorem rootShape_next (s : MachineState) {ℓ n : ℕ} (hn : n = ((Model.Pcs.ladderFolds (K0 s + 1)).take (ℓ + 1)).sum) :
    rootShape s (ℓ + 1) = ((s.getReg .x12).toNat - n - fcOf s (ℓ + 1) + rtOf s (ℓ + 1),
      3 * 2 ^ fcOf s (ℓ + 1)) := by
  simp only [rootShape, take_succ_sum _ (ℓ + 1), hn, fcOf, rtOf, Nat.sub_sub]

end Rv64Verifier.Proofs.Pcs.Vso
