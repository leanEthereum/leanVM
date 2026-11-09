/-
  LeanVM.Protocol.Keccak.CompleteLayer

  The honest prover of one layer of `verifyKeccak`, as a script, and its simulation of
  `verifyKeccakLayer`: every check passes, for every challenge, and the next claim is true.
-/

module

public import LeanVM.Protocol.Keccak.Gkr

/-!
# An honest layer

On a claim that holds of the states after the round, the honest prover sends (`hLayer`)

* the coefficients of the product polynomial `G` (`gList (Gpoly …)`);
* per pack and segment round, the round polynomial `x ↦ scale·FP(acc ++ [x])` without its
  constant coefficient (`hPack`, equality mode);
* the position rounds' polynomials (`hSumcheck` on the family `FX`);
* `T_0, T_1, T_2` at the position point.

`follows_layer`: this script follows `verifyKeccakLayer` (both checks pass, by the identities
the soundness proof reads backwards: `claimSum_round` and the final check), and the claim it
returns holds of the states before the round (`batch_eq`).
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Prover (Script)

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.Whir.Complete Finset

@[expose] public section

/-! ## The pack and segment rounds -/

/-- The honest equality-mode rounds of `keccakPackRounds` for the family `F`: per round, the
round polynomial `x ↦ scale·F(acc ++ [x])` on the wire. Returns the scale and the challenges. -/
noncomputable def hPack (F : List E → E) : List E → List E → E → Script (E × List E)
  | [], _, scale => Script.ret (scale, [])
  | rk :: rs, acc, scale =>
    (Script.sendList (wire (some rk) (coeffsOf 2 fun x ↦ scale * F (acc ++ [x])))).bind fun _ ↦
      Script.sampleE.bind fun c ↦
        (hPack F rs (acc ++ [c]) (scale * (1 + rk + c))).bind fun r ↦ Script.ret (r.1, c :: r.2)

/-- **The honest pack rounds follow the program's.** -/
theorem follows_pack (F : List E → E) (r : List E) (hF : EqFamily (fun (_ : Unit) acc ↦ F acc) r 2)
    (cs : Commits) : ∀ (rs acc : List E) (value scale : E), rs = r.drop acc.length →
      value = scale * F acc →
      Follows (fun cs' a b ↦ cs' = cs ∧ b.2.1 = a.1 ∧ b.2.2 = a.2 ∧ b.2.2.length = rs.length ∧
          b.1 = b.2.1 * F (acc ++ b.2.2))
        (hPack F rs acc scale) (keccakPackRounds rs value scale) cs
  | [], acc, value, scale, _, hv => by
    simp [hPack, keccakPackRounds, Follows, hv]
  | rk :: rs, acc, value, scale, hrs, hv => by
    have hlt : acc.length < r.length := by
      by_contra h
      rw [List.drop_eq_nil_of_le (by omega)] at hrs
      exact List.cons_ne_nil _ _ hrs
    have hrk : r[acc.length] = rk := by
      have := congrArg List.head? hrs
      rw [List.head?_drop, List.getElem?_eq_getElem hlt] at this
      simpa using this.symm
    obtain ⟨hdeg, hsplit⟩ := hF () acc hlt
    simp only at hdeg hsplit
    have hd : PolyLE 2 fun x ↦ scale * F (acc ++ [x]) := PolyLE.const_mul hdeg scale
    have hround := follows_sumcheckRoundPoly 3 value (some rk)
      (coeffsOf 2 fun x ↦ scale * F (acc ++ [x])) (by rw [length_coeffsOf]) (by norm_num) (by
        rw [RoundSplit, polyEval_coeffsOf hd, polyEval_coeffsOf hd, hv, hsplit, hrk]; ring) cs
    simp only [hPack, keccakPackRounds, VerifierProgram.bind_eq]
    refine Follows.bind (fun cs₁ _ msg h₁ ↦ ?_) _ _ _ hround
    obtain ⟨rfl, rfl⟩ := h₁
    refine Follows.bind (fun cs₂ c c' h₂ ↦ ?_) _ _ _ (Follows.sampleE_sampleE cs₁)
    obtain ⟨rfl, rfl⟩ := h₂
    have hrs' : rs = r.drop (acc ++ [c]).length := by
      rw [List.length_append, List.length_singleton, ← List.drop_drop, ← hrs]
      rfl
    have hv' : (1 + rk + c) * polyEval (coeffsOf 2 fun x ↦ scale * F (acc ++ [x])) c =
        scale * (1 + rk + c) * F (acc ++ [c]) := by
      rw [polyEval_coeffsOf hd]; ring
    have ih := follows_pack F r hF cs₂ rs (acc ++ [c])
      ((1 + rk + c) * polyEval (coeffsOf 2 fun x ↦ scale * F (acc ++ [x])) c)
      (scale * (1 + rk + c)) hrs' hv' 
    refine Follows.bind (fun cs₃ a b h₃ ↦ ?_) _ _ _ ih
    obtain ⟨rfl, h1, h2, h3, h4⟩ := h₃
    obtain ⟨v, sc, pt⟩ := b
    dsimp only at h1 h2 h3 h4
    show _ = _ ∧ sc = a.1 ∧ c :: pt = c :: a.2 ∧ (c :: pt).length = (rk :: rs).length ∧
      v = sc * F (acc ++ c :: pt)
    refine ⟨rfl, h1, by rw [← h2], by simp [h3], ?_⟩
    rw [h4]
    simp

/-! ## A layer -/

/-- **The honest layer.** -/
noncomputable def hLayer (T : States) (P : ℕ) (claim : KeccakClaim) : Script KeccakClaim :=
  Script.sendList (gList (Gpoly T P claim.point claim.weights)) >>= fun _ ↦
  Script.ret () >>= fun _ ↦
  Script.sampleE >>= fun s ↦
  hPack (FP T P s claim.weights claim.point) claim.point [] 1 >>= fun pk ↦
  hSumcheck 4 (FX T P s claim.weights pk.2 pk.1) (List.replicate keccakLocalBits none) [] >>=
    fun ps ↦
  Script.sendList [Tk T P s pk.2 0 ps.1, Tk T P s pk.2 1 ps.1, Tk T P s pk.2 2 ps.1] >>= fun _ ↦
  Script.ret () >>= fun _ ↦
  Script.sampleE >>= fun b ↦
  Script.ret ⟨Tk T P s pk.2 0 ps.1 + b * (Tk T P s pk.2 1 ps.1 + b * Tk T P s pk.2 2 ps.1),
    keccakInstanceWeights s, pk.2, keccakLinearTranspose (batchW ps.1 b)⟩

/-- **The honest layer follows `verifyKeccakLayer`**: both checks pass for every challenge, and
the claim returned holds of the states before the round. -/
theorem follows_layer (T : States) (step P : ℕ) (claim : KeccakClaim) (hshape : ClaimShape P claim)
    (htrue : ClaimTrue (afterRound T step) P claim) (cs : Commits) :
    Follows (fun cs' a c ↦ cs' = cs ∧ a = c ∧ ClaimShape P c ∧ ClaimTrue T P c)
      (hLayer T P claim) (verifyKeccakLayer (P + 4) step claim) cs := by
  let G := Gpoly T P claim.point claim.weights
  rw [verifyKeccakLayer_eq, layerProg, show productBits = (gList G).length from
    (gList_length G).symm]
  unfold hLayer
  refine Follows.bind_of (Follows.sendList_readN cs (gList G)) fun cs₁ _ product h₁ ↦ ?_
  obtain ⟨rfl, rfl⟩ := h₁
  -- the product check passes
  have hcheck : projectedOf claim (gList G) + iotaOf P step claim * sumE claim.mu = claim.value := by
    rw [htrue, claimSum_round T step P _ _ _ hshape.2.1, projectedOf,
      projected_eq claim.mu _ hshape.1 _ (fun c hc ↦ gList_getD G hc), iotaOf,
      iota_eq step P _ _ hshape.2.1, sumE_mu hshape.1]
  refine Follows.bind_of (Follows.ret_require (R := fun cs' _ _ ↦ cs' = cs₁) hcheck rfl)
    fun cs₂ _ _ h₂ ↦ ?_
  subst h₂
  refine Follows.bind_of (Follows.sampleE_sampleE cs₂) fun cs₃ s s' h₃ ↦ ?_
  obtain ⟨rfl, rfl⟩ := h₃
  -- the pack rounds
  have hpack := follows_pack (FP T P s claim.weights claim.point) claim.point
    (fun _ acc hacc ↦ FP_eqFamily P s claim.weights (fun _ : Unit ↦ T) claim.point hshape.2.1 ()
      acc hacc) cs₃ claim.point [] (polyEval (gList G) s) 1 rfl
    (by rw [one_mul, FP_nil, polyEval_gList (natDegree_Gpoly _ _ _ _)])
  refine Follows.bind_of hpack fun cs₄ pk res h₄ ↦ ?_
  obtain ⟨rfl, hsc, hpt, hlen, hval⟩ := h₄
  rw [List.nil_append, FP_full _ _ _ _ _ _ hshape.2.1 (by rw [hlen, hshape.2.1])] at hval
  -- the position rounds
  have hplain := FX_plainFamily P s claim.weights (fun _ : Unit ↦ T) res.2.2 res.2.1
  have hsum := follows_sumcheck 4 (by norm_num) (FX T P s claim.weights pk.2 pk.1)
    (List.replicate keccakLocalBits none) [] cs₄
    (fun ext hext ↦ by
      have := (hplain () ext (by simpa [keccakLocalBits] using hext)).1
      rw [← hsc, ← hpt]; simpa using this)
    (fun ext hext ↦ by
      have := (hplain () ext (by simpa [keccakLocalBits] using hext)).2
      simp only [List.getElem_replicate, RoundSplit, List.nil_append]
      rw [← hsc, ← hpt]; exact this.symm)
  have hv0 : res.1 = FX T P s claim.weights pk.2 pk.1 [] := by
    rw [hval, FX_nil, hsc, hpt]
  rw [hv0]
  refine Follows.bind_of hsum fun cs₅ ps res2 h₅ ↦ ?_
  obtain ⟨rfl, rfl, hl5, hf5⟩ := h₅
  rw [List.nil_append] at hf5
  -- `t` and the final check
  unfold layerTail
  have ht := Follows.sendList_readN cs₅
    [Tk T P s pk.2 0 ps.1, Tk T P s pk.2 1 ps.1, Tk T P s pk.2 2 ps.1]
  refine Follows.bind_of ht fun cs₆ _ t h₆ ↦ ?_
  obtain ⟨rfl, rfl⟩ := h₆
  have hl11 : ps.1.length = 11 := by simpa [keccakLocalBits] using hl5
  have hfinal : res.2.1 * dot ((eqKernel ps.1).take keccakBits) claim.weights *
      (sumE (keccakInstanceWeights s) * Tk T P s pk.2 0 ps.1 +
        (sumE (keccakInstanceWeights s) + Tk T P s pk.2 1 ps.1) * Tk T P s pk.2 2 ps.1) = ps.2 := by
    rw [hf5, FX_full _ _ _ _ _ _ _ hl11, dot_weights _ _ hl11 hshape.2.2, kappa_eq, phi, hsc]
    ring
  refine Follows.bind_of (Follows.ret_require (R := fun cs' _ _ ↦ cs' = cs₆) ?_ rfl)
    fun cs₇ _ _ h₇ ↦ ?_
  · simp only [List.getD_cons_zero, List.getD_cons_succ]
    exact hfinal
  subst h₇
  refine Follows.bind_of (Follows.sampleE_sampleE cs₇) fun cs₈ b b' h₈ ↦ ?_
  obtain ⟨rfl, rfl⟩ := h₈
  simp only [Follows, List.getD_cons_zero, List.getD_cons_succ]
  refine ⟨trivial, by rw [hpt], ⟨keccakInstanceWeights_length s, ?_,
    keccakLinearTranspose_length _⟩, ?_⟩
  · show res.2.2.length = P + 1
    rw [hlen, hshape.2.1]
  · show _ = claimSum T P res.2.2 (keccakInstanceWeights s) (keccakLinearTranspose (batchW ps.1 b))
    rw [hpt]
    exact batch_eq T P s pk.2 ps.1 hl11 b

end
end LeanVM.Protocol.KeccakGkr
