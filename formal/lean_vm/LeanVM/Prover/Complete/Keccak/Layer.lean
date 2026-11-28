/-
  LeanVM.Prover.Complete.Keccak.Layer

  The honest prover of one layer of `verifyKeccak`, as a script, wins `verifyKeccakLayer`: every
  check passes, for every challenge, and the next claim is true.
-/

module

public import LeanVM.Prover.Complete.Keccak.Sumcheck
public import LeanVM.Protocol.Keccak.Layer

/-!
# An honest layer

On a claim that holds of the states after the round, the honest prover sends (`hLayer`)

* the coefficients of the product polynomial `G` (`gList (Gpoly …)`);
* after the grind and `s`, per pack and segment round, the round polynomial `x ↦ FP(acc ++ [x])`
  without its constant coefficient (`hPack`, equality mode);
* the position rounds' polynomials (`hSumcheck` on the family `FX`);
* `T_0, T_1, T_2` at the position point.

`wins_layer`: this script wins `verifyKeccakLayer` (both checks pass, by the identities the
soundness proof reads backwards: `claimSum_round` and the final check), and the claim it returns
holds of the states before the round (`batch_eq`). The only grind of nonzero bits is `s`'s,
`grindingBits 46 = 3` bits.
-/

@[expose] public section

namespace LeanVM.Prover.Complete.Keccak

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.KeccakGkr Finset

variable {B : ℕ}

/-! ## The pack and segment rounds -/

/-- The honest equality-mode rounds of `keccakPackRounds` for the family `F`: each round sends
`F(acc ++ [x])` without its constant coefficient, grinds, and returns the challenges. -/
noncomputable def hPack (F : List E → E) : List E → List E → Script (List E)
  | [], _ => Script.ret []
  | rk :: rs, acc =>
    ((Script.sendList (wire (some rk) (coeffsOf 2 fun x ↦ F (acc ++ [x])))).bind fun _ ↦
      Script.grindBits (roundBits 3 (some rk))).bind fun _ ↦
      Script.sampleE.bind fun c ↦
        (hPack F rs (acc ++ [c])).bind fun r ↦ Script.ret (c :: r)

theorem roundBits_three (mode : Option E) : roundBits 3 mode = 0 := by
  cases mode <;> exact grindingBits_le_eight (by simp)

theorem roundBits_four (mode : Option E) : roundBits 4 mode = 0 := by
  cases mode <;> exact grindingBits_le_eight (by simp)

/-- **The honest pack rounds win the program's.** -/
theorem wins_pack (F : List E → E) (r : List E) (hF : EqFamily (fun (_ : Unit) acc ↦ F acc) r 2)
    (cs : List Committed) : ∀ (rs acc : List E) (value : E), rs = r.drop acc.length →
      value = F acc →
      Wins B (fun a b g' cs' ↦ a.2 = b ∧ a.2.length = rs.length ∧ a.1 = F (acc ++ a.2) ∧
          g' = false ∧ cs' = cs)
        (keccakPackRounds rs value) (hPack F rs acc) false cs
  | [], acc, value, _, hv => ⟨rfl, rfl, by simp [hv], rfl, rfl⟩
  | rk :: rs, acc, value, hrs, hv => by
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
    have hround := wins_roundPoly (B := B) 3 value (some rk)
      (coeffsOf 2 fun x ↦ F (acc ++ [x])) (by rw [length_coeffsOf]) (by norm_num)
      (by rw [roundBits_three]; exact Nat.zero_le _) (by
        rw [RoundSplit, polyEval_coeffsOf hdeg, polyEval_coeffsOf hdeg, hv, hsplit, hrk]) cs
    simp only [hPack, keccakPackRounds, VerifierProgram.bind_eq]
    refine LeanVM.Prover.Wins.bind (fun msg _ g₁ cs₁ h₁ ↦ ?_) _ _ _ _ hround
    obtain ⟨rfl, h₁⟩ := h₁
    subst cs₁
    refine LeanVM.Prover.Wins.bind (fun c c' g₂ cs₂ h₂ ↦ ?_) _ _ _ _ (Wins.sampleE g₁ cs)
    obtain ⟨rfl, rfl, h₂⟩ := h₂
    subst cs₂
    have hrs' : rs = r.drop (acc ++ [c]).length := by
      rw [List.length_append, List.length_singleton, ← List.drop_drop, ← hrs]
      rfl
    have ih := wins_pack F r hF cs rs (acc ++ [c])
      (polyEval (coeffsOf 2 fun x ↦ F (acc ++ [x])) c) hrs' (polyEval_coeffsOf hdeg c)
    refine LeanVM.Prover.Wins.bind (fun a b g₃ cs₃ h₃ ↦ ?_) _ _ _ _ ih
    obtain ⟨h1, h2, h3, rfl, h₃⟩ := h₃
    subst cs₃
    obtain ⟨v, pt⟩ := a
    dsimp only at h1 h2 h3 ⊢
    refine ⟨by rw [h1], by simp [h2], ?_, rfl, rfl⟩
    rw [h3]
    simp

/-! ## A layer -/

/-- **The honest layer.** -/
noncomputable def hLayer (T : States) (P : ℕ) (claim : KeccakClaim) : Script KeccakClaim :=
  Script.sendList (gList (Gpoly T P claim.point claim.weights)) >>= fun _ ↦
  Script.ret () >>= fun _ ↦
  (Script.grindSample (grindingBits (productBits - 1))).bind fun s ↦
  hPack (FP T P s claim.weights claim.point) claim.point [] >>= fun pk ↦
  hSumcheck 4 (FX T P s claim.weights pk) (List.replicate keccakLocalBits none) [] >>=
    fun ps ↦
  Script.sendList [Tk T P s pk 0 ps.1, Tk T P s pk 1 ps.1, Tk T P s pk 2 ps.1] >>= fun _ ↦
  Script.ret () >>= fun _ ↦
  Script.grindBits (grindingBits 2) >>= fun _ ↦
  Script.sampleE >>= fun b ↦
  Script.ret ⟨Tk T P s pk 0 ps.1 + b * (Tk T P s pk 1 ps.1 + b * Tk T P s pk 2 ps.1),
    keccakInstanceWeights s, pk, keccakLinearTranspose (batchW ps.1 b)⟩

/-- **The honest layer wins `verifyKeccakLayer`**: both checks pass for every challenge, and the
claim returned holds of the states before the round. -/
theorem wins_layer (hB : 3 ≤ B) (T : States) (step P : ℕ) (claim : KeccakClaim)
    (hshape : ClaimShape P claim) (htrue : ClaimTrue (afterRound T step) P claim)
    (cs : List Committed) :
    Wins B (fun c a g' cs' ↦ a = c ∧ ClaimShape P c ∧ ClaimTrue T P c ∧ g' = false ∧ cs' = cs)
      (verifyKeccakLayer (P + 4) step claim) (hLayer T P claim) false cs := by
  let G := Gpoly T P claim.point claim.weights
  rw [verifyKeccakLayer_eq, layerProg, show productBits = (gList G).length from
    (gList_length G).symm]
  unfold hLayer
  refine LeanVM.Prover.Wins.bind' (Wins.sendList_readScalars cs (gList G))
    fun product _ g₁ cs₁ h₁ ↦ ?_
  obtain ⟨rfl, rfl, h₁⟩ := h₁
  subst cs₁
  -- the product check passes
  have hcheck : projectedOf claim (gList G) + iotaOf P step claim * sumE claim.mu =
      claim.value := by
    rw [htrue, claimSum_round T step P _ _ _ hshape.2.1, projectedOf,
      projected_eq claim.mu _ hshape.1 _ (fun c hc ↦ gList_getD G hc), iotaOf,
      iota_eq step P _ _ hshape.2.1, sumE_mu hshape.1]
  refine LeanVM.Prover.Wins.bind' (Wins.require hcheck false cs) fun _ _ g₂ cs₂ h₂ ↦ ?_
  obtain ⟨-, rfl, h₂⟩ := h₂
  subst cs₂
  rw [gList_length G]
  refine Wins.grindSample_bind ((le_of_eq grindingBits_product).trans hB) fun s ↦ ?_
  -- the pack rounds
  have hpack := wins_pack (B := B) (FP T P s claim.weights claim.point) claim.point
    (fun _ acc hacc ↦ FP_eqFamily P s claim.weights (fun _ : Unit ↦ T) claim.point hshape.2.1 ()
      acc hacc) cs claim.point [] (polyEval (gList G) s) rfl
    (by rw [FP_nil, polyEval_gList (natDegree_Gpoly _ _ _ _)])
  refine LeanVM.Prover.Wins.bind' hpack fun res pk g₄ cs₄ h₄ ↦ ?_
  obtain ⟨hpt, hlen, hval, rfl, h₄⟩ := h₄
  subst cs₄
  rw [List.nil_append, FP_full _ _ _ _ _ _ hshape.2.1 (by rw [hlen, hshape.2.1])] at hval
  -- the position rounds
  have hplain := FX_plainFamily P s claim.weights (fun _ : Unit ↦ T) res.2
  have hsum := wins_sumcheck (B := B) 4 (by norm_num) (FX T P s claim.weights pk)
    (List.replicate keccakLocalBits none) [] cs
    (fun m _ ↦ by rw [roundBits_four]; exact Nat.zero_le _)
    (fun ext hext ↦ by
      have := (hplain () ext (by simpa [keccakLocalBits] using hext)).1
      rw [← hpt]; simpa using this)
    (fun ext hext ↦ by
      have := (hplain () ext (by simpa [keccakLocalBits] using hext)).2
      simp only [List.getElem_replicate, RoundSplit, List.nil_append]
      rw [← hpt]; exact this.symm)
  have hv0 : res.1 = FX T P s claim.weights pk [] := by
    rw [hval, FX_nil, hpt]
  rw [hv0]
  refine LeanVM.Prover.Wins.bind' hsum fun res2 ps g₅ cs₅ h₅ ↦ ?_
  obtain ⟨rfl, hl5, hf5, rfl, h₅⟩ := h₅
  subst cs₅
  rw [List.nil_append] at hf5
  -- `t` and the final check
  unfold layerTail
  refine LeanVM.Prover.Wins.bind' (Wins.sendList_readScalars cs
    [Tk T P s pk 0 res2.1, Tk T P s pk 1 res2.1, Tk T P s pk 2 res2.1]) fun t _ g₆ cs₆ h₆ ↦ ?_
  obtain ⟨rfl, rfl, h₆⟩ := h₆
  subst cs₆
  have hl11 : res2.1.length = 11 := by simpa [keccakLocalBits] using hl5
  have hfinal : dot ((eqKernel res2.1).take keccakBits) claim.weights *
      (sumE (keccakInstanceWeights s) * Tk T P s pk 0 res2.1 +
        (sumE (keccakInstanceWeights s) + Tk T P s pk 1 res2.1) * Tk T P s pk 2 res2.1) =
        res2.2 := by
    rw [hf5, FX_full _ _ _ _ _ _ hl11, dot_weights _ _ hl11 hshape.2.2, kappa_eq, phi]
  refine LeanVM.Prover.Wins.bind' (Wins.require ?_ false cs) fun _ _ g₇ cs₇ h₇ ↦ ?_
  · simp only [List.getD_cons_zero, List.getD_cons_succ]
    exact hfinal
  obtain ⟨-, rfl, h₇⟩ := h₇
  subst cs₇
  refine LeanVM.Prover.Wins.bind' (Wins.grindBits (by
    rw [grindingBits_le_eight (by decide)]; exact Nat.zero_le _) cs) fun _ _ g₈ cs₈ h₈ ↦ ?_
  obtain ⟨-, h₈⟩ := h₈
  subst cs₈
  refine LeanVM.Prover.Wins.bind' (Wins.sampleE g₈ cs) fun b b' g₉ cs₉ h₉ ↦ ?_
  obtain ⟨rfl, rfl, h₉⟩ := h₉
  subst cs₉
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  refine ⟨by rw [hpt], ⟨keccakInstanceWeights_length s, ?_, keccakLinearTranspose_length _⟩, ?_,
    rfl, rfl⟩
  · show res.2.length = P + 1
    rw [hlen, hshape.2.1]
  · show _ = claimSum T P res.2 (keccakInstanceWeights s) (keccakLinearTranspose (batchW res2.1 b))
    rw [hpt]
    exact batch_eq T P s pk res2.1 hl11 b

end LeanVM.Prover.Complete.Keccak

end
