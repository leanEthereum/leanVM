/-
  LeanVM.Prover.Keccak.Layer

  The executable Keccak layers make the moves of the specification's `hLayer`, `hLayers`.
-/

module

public import LeanVM.Prover.Keccak.Position
public import LeanVM.Prover.Keccak.Product

/-!
# The layers

`corr_layer`: on a column agreeing with the specification's on `q_keccak`'s words and a claim of
the layer's shape, `layerProve col' P d claim` makes the moves of
`hLayer (statesAt (P + 4) col (d + 1)) P claim` and returns the same claim: `G`'s coefficients
(`gCoeffs_eq`), the pack rounds (`corr_pack`), the position rounds (`corr_pos`), the `t` values
from the folded tables (`posInv_full`), the next weights (`batchWeights_eq`). `corr_layers`: the
twelve layers.
-/

namespace LeanVM.Prover.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

theorem batchWeights_eq (p : List E) (beta : E) : batchWeights p beta = batchW p beta := by
  simp only [batchWeights, batchW, eqTable_eq, array_getD_toArray]

/-- **A layer makes the moves of `hLayer`**, and returns its claim. -/
theorem corr_layer {P : ℕ} {col' col : ℕ → K} (hcol : ColAgree P col' col) {d : ℕ} (hd : d < 12)
    (claim : KeccakClaim) (hshape : ClaimShape P claim) :
    Corr (fun a b ↦ a = b ∧ ClaimShape P a) (layerProve col' P d claim)
      (hLayer (statesAt (P + 4) col (d + 1)) P claim) := by
  unfold layerProve hLayer
  simp only [Script.bind_eq, Script.ret_bind]
  rw [gCoeffs_eq hcol hd hshape.2.1]
  refine Corr.bind_same _ fun _ ↦ Corr.bind_same _ fun s ↦ ?_
  rw [kappa_eq s]
  refine Corr.bind (fun a b hab ↦ ?_) _ _ (corr_pack (T := statesAt (P + 4) col (d + 1))
    (w := claim.weights) hshape.2.1 claim.point [] _ (packInv_start hcol hd s claim.point) rfl)
  obtain ⟨hb1, hb2, hl, hinv⟩ := hab
  rw [List.nil_append] at hinv
  have hacc : a.1.length = P + 1 := by rw [hl, hshape.2.1]
  rw [hb1, hb2]
  refine Corr.bind (fun a2 b2 hab2 ↦ ?_) _ _ (corr_pos (w := claim.weights) hinv hacc a.2.scale)
  obtain ⟨h1, h2, h3, h4⟩ := hab2
  obtain ⟨t0, t1, t2⟩ := posInv_full h2 h4
  refine corr_sendList (by rw [t0, t1, t2, h1]) ?_
  refine Corr.bind_same _ fun b ↦ ?_
  refine corr_ret ⟨?_, keccakInstanceWeights_length s, hacc, keccakLinearTranspose_length _⟩
  rw [t0, t1, t2, h1, batchWeights_eq]

/-- **The layers make the moves of `hLayers`.** -/
theorem corr_layers {P : ℕ} {col' col : ℕ → K} (hcol : ColAgree P col' col) :
    ∀ (n d : ℕ), d + n = 12 → ∀ claim, ClaimShape P claim →
      Corr (fun a b ↦ a = b ∧ ClaimShape P a) (layersProve col' P (List.range' d n) claim)
        (hLayers P col (List.range' d n) claim)
  | 0, _, _, _, h => corr_ret ⟨rfl, h⟩
  | n + 1, d, hd, claim, h => by
    rw [List.range'_succ]
    show Corr _ ((layerProve col' P d claim).bind fun c ↦
        layersProve col' P (List.range' (d + 1) n) c)
      ((hLayer (statesAt (P + 4) col (d + 1)) P claim).bind fun c ↦
        hLayers P col (List.range' (d + 1) n) c)
    refine Corr.bind (fun a b hab ↦ ?_) _ _ (corr_layer hcol (by omega) claim h)
    obtain ⟨rfl, hs⟩ := hab
    exact corr_layers hcol n (d + 1) (by omega) a hs

end
end LeanVM.Prover.KeccakGkr
