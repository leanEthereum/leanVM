/-
  LeanVM.Prover.Keccak.Reduction

  The executable Keccak reduction makes the moves of the specification's `hKeccak`.
-/

module

public import LeanVM.Prover.Keccak.Layer
public import LeanVM.Prover.Keccak.Open

/-!
# The reduction

`corr_keccak`: on a column `col'` agreeing with `col` on `q_keccak`'s `2^(P + 10)` words and a
point `inst` of `P + 4` coordinates, `keccakProve col' P inst output` makes the moves of
`hKeccak P col inst output`: `committed` from the slot words
(`committed_eq`), the layers (`corr_layers`), the outputs' opening (`corr_openOut`) and word, the
inputs' opening (`corr_input`).
-/

namespace LeanVM.Prover.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

variable {P : ℕ} {col' col : ℕ → K}

theorem eqKernel_getD_lt (pt : List E) {w : ℕ} (hw : w < 2 ^ pt.length) :
    (eqKernel pt).getD w 0 = eqAt pt w := by
  rw [eqKernel_getD, ite_eq_left hw]

/-- The honest `committed` from the slot words. -/
theorem committed_eq (hcol : ColAgree P col' col) {inst segment lanesPt : List E}
    (hi : inst.length = P + 4) (hs : segment.length = 1) (hl : lanesPt.length = 5) :
    (eqKernel segment).getD 0 0 * sumRange 25 (fun l ↦ (eqKernel lanesPt).getD l 0 *
      (slotWords col' (P + 4) inst).getD (25 + l) 0) = committedOf P col inst segment lanesPt := by
  rw [committedOf, eqKernel_getD_lt _ (by rw [hs]; norm_num), sumRange_eq]
  refine congrArg (eqAt segment 0 * ·) (Finset.sum_congr rfl fun l hl' ↦ ?_)
  have hl'' := Finset.mem_range.1 hl'
  rw [eqKernel_getD_lt _ (by rw [hl]; norm_num; omega), slotWords_getD hcol hi (by omega), midMle]

theorem keccakFirstClaim_eq (inst segment lanesPt output : List E) (committed : E) :
    keccakFirstClaim inst segment lanesPt output committed =
      firstClaim inst segment lanesPt output committed := rfl

/-- **The reduction makes the moves of `hKeccak`.** -/
theorem corr_keccak (hcol : ColAgree P col' col) {inst : List E} (hi : inst.length = P + 4)
    (output : List E) :
    Corr (fun _ _ ↦ True) (keccakProve col' P inst output) (hKeccak P col inst output) := by
  unfold keccakProve hKeccak
  rw [show LeanVM.Protocol.Compile.grindingBits (keccakSegmentBits + keccakLaneBits) = 0 by decide,
    keccakSegmentBits_eq,
    show keccakLaneBits = 5 from rfl]
  simp only [Script.grindBits, ↓reduceIte, Script.bind_eq, Script.ret_bind, hOpen_eq]
  refine Corr.bind (fun seg seg' h ↦ ?_) _ _ (corr_sampleN 1)
  obtain ⟨rfl, hs⟩ := h
  refine Corr.bind (fun ln ln' h ↦ ?_) _ _ (corr_sampleN 5)
  obtain ⟨rfl, hl⟩ := h
  rw [committed_eq hcol hi hs hl, keccakFirstClaim_eq]
  refine corr_sendE rfl ?_
  refine Corr.bind (fun c c' h ↦ ?_) _ _
    (corr_layers hcol 12 0 rfl _ (firstClaim_shape _ hi hs))
  obtain ⟨rfl, hsh⟩ := h
  refine Corr.bind (fun x x' h ↦ ?_) _ _ (corr_openOut hcol hi hs hl)
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hword : (x.2.pairs.headD (#[], #[])).2.getD 0 0 = Qo (P + 4) col inst x'.1 := by
    rw [headD_getD, ← h1]; exact tabInv_full (h2.2.2 0 (by norm_num)).2 h4
  rw [hword]
  exact corr_sendE rfl (corr_input hcol c hsh _)

end
end LeanVM.Prover.KeccakGkr
