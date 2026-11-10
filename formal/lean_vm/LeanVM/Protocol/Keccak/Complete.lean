/-
  LeanVM.Protocol.Keccak.Complete

  Completeness of the Keccak reduction: the honest prover of `verifyKeccak`, as a script, makes
  every check pass for every choice of challenges, and the claims the verifier returns hold.
-/

module

public import LeanVM.Protocol.Keccak.CompleteLayer

/-!
# The honest Keccak prover

For a column `col` whose output-lane claims hold against the committed middle state
(`outClaimsTrueMid`) and whose middle state agrees with twelve rounds of the input at `inst`
(`midAgree`; both follow from `RegionValid` and the claims against `keccakF`,
`outClaims_of_regionValid`), the honest prover `hKeccak` sends

* `committed`, the middle state's value at the challenges (`committedOf`);
* the twelve layers' messages (`hLayers`, `hLayer`);
* the outputs' slot rounds (`hSumcheck` on `Fo`) and `word`, the column at `(inst, ρ)`;
* the inputs' instance and slot rounds (`hSumcheck` on `Fl`, `Fs`) and the `64` slices.

`follows_keccak`: it follows `verifyKeccak`, and the verifier's result is a list of true column
claims and `64` true slice claims (`Follows`, `LeanVM.Protocol.Whir.Complete.Script`).
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Prover (Script)

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete LeanVM.Protocol.Whir.Complete Finset

@[expose] public section

variable (P : ℕ)

/-! ## The layers -/

/-- The honest layers from depth `d`, on the column `col`. -/
noncomputable def hLayers (col : ℕ → K) : List ℕ → KeccakClaim → Script KeccakClaim
  | [], claim => Script.ret claim
  | d :: ds, claim => hLayer (statesAt (P + 4) col (d + 1)) P claim >>= fun c ↦ hLayers col ds c

theorem follows_layers (col : ℕ → K) (cs : Commits) :
    ∀ (n d : ℕ), d + n = 12 → ∀ claim, ClaimShape P claim →
      ClaimTrue (statesAt (P + 4) col d) P claim →
      Follows (fun cs' a c ↦ cs' = cs ∧ a = c ∧ ClaimShape P c ∧
          ClaimTrue (statesAt (P + 4) col 12) P c)
        (hLayers P col (List.range' d n) claim) (keccakLayers (P + 4) (List.range' d n) claim) cs
  | 0, d, hd, claim, hs, ht => by
    rw [show d = 12 by omega] at ht
    exact ⟨rfl, rfl, hs, ht⟩
  | n + 1, d, hd, claim, hs, ht => by
    show Follows _ (hLayer (statesAt (P + 4) col (d + 1)) P claim >>= fun c ↦
      hLayers P col (List.range' (d + 1) n) c)
      (verifyKeccakLayer (P + 4) d claim >>= fun c ↦ keccakLayers (P + 4) (List.range' (d + 1) n) c)
      cs
    refine Follows.bind_of (follows_layer _ d P claim hs
      ((claimTrue_round (P + 4) col (by omega) P claim).1 ht) cs) fun cs₁ a c h₁ ↦ ?_
    obtain ⟨rfl, rfl, hs', ht'⟩ := h₁
    exact follows_layers col cs₁ n (d + 1) (by omega) a hs' ht'

/-! ## The first claim -/

/-- The honest `committed`: the middle state's value at the challenges. -/
noncomputable def committedOf (col : ℕ → K) (inst segment lanesPt : List E) : E :=
  eqAt segment 0 * ∑ l ∈ range 25, eqAt lanesPt l * midMle (P + 4) col inst l

/-- **The honest first claim holds.** -/
theorem first_true (col : ℕ → K) {inst segment lanesPt output : List E}
    (hi : inst.length = P + 4) (hs : segment.length = 1) (hl : lanesPt.length = 5)
    (ho : output.length = 25) (hmid : outClaimsTrueMid (P + 4) col inst output)
    (hagree : midAgree (P + 4) col inst) :
    ClaimTrue (statesAt (P + 4) col 0) P
      (firstClaim inst segment lanesPt output (committedOf P col inst segment lanesPt)) := by
  rw [ClaimTrue, firstClaim_sum (P + 4) P rfl col hi hl]
  have hdot : dot ((eqKernel lanesPt).take 25) output =
      ∑ l ∈ range 25, eqAt lanesPt l * output.getD l 0 := by
    rw [dot_eq _ _ (by simp [eqKernel_length, hl, ho])]
    simp only [List.length_take, eqKernel_length, hl]
    refine Finset.sum_congr rfl fun l hl' ↦ ?_
    have hl'' := Finset.mem_range.1 hl'
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left (by omega),
      ← List.getD_eq_getElem?_getD, eqKernel_getD, hl, ite_eq_left (by omega)]
  have hseg : (eqKernel segment).getD (keccakSegments - 1) 0 = eqAt segment 1 := by
    rw [eqKernel_getD, hs]; rfl
  change committedOf P col inst segment lanesPt + (eqKernel segment).getD (keccakSegments - 1) 0 *
    dot ((eqKernel lanesPt).take 25) output = _
  rw [hseg, hdot, committedOf, Finset.sum_range_succ (n := 1), Finset.sum_range_succ (n := 0),
    Finset.sum_range_zero, zero_add]
  refine congrArg₂ (· + ·) (congrArg (HMul.hMul _) (Finset.sum_congr rfl fun l hl' ↦ ?_))
    (congrArg (HMul.hMul _) (Finset.sum_congr rfl fun l hl' ↦ ?_))
  · exact congrArg _ (hagree l (Finset.mem_range.1 hl')).symm
  · exact congrArg _ (hmid l (Finset.mem_range.1 hl')).symm

/-! ## The openings -/

/-- The honest slot rounds of `keccakOpen`, for the family `F`. -/
noncomputable def hOpen (F : List E → E) : Script (List E × E) :=
  hSumcheck 3 F (List.replicate 6 none) [] >>= fun r ↦ Script.ret r

omit P in
theorem follows_open (F : List E → E) (h : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E)
    (hfam : PlainFamily (fun (_ : Unit) acc ↦ F acc) 2 6) (hv : value = F []) (cs : Commits) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a.1 = b.1 ∧ b.1.length = 6 ∧
        b.2.1 = (foldAll b.1 (keccakSlotWeights h claim first count)).headD [] ∧ b.2.2 = F b.1)
      (hOpen F) (keccakOpen h claim first count value) cs := by
  rw [keccakOpen_eq, qkeccakSlotBits_eq, hv, hOpen]
  refine Follows.bind_of (follows_sumcheck 3 (by norm_num) F (List.replicate 6 none) [] cs
    (fun ext hext ↦ by simpa using (hfam () ext (by simpa using hext)).1)
    (fun ext hext ↦ by
      simp only [List.getElem_replicate, RoundSplit, List.nil_append]
      exact (hfam () ext (by simpa using hext)).2.symm)) fun cs' r x h' ↦ ?_
  obtain ⟨rfl, rfl, hl, hf⟩ := h'
  simp only [Follows]
  exact ⟨by simp, by simp, by simpa using hl, by simp, by simpa using hf⟩

/-- The honest slices: slice `z` of the column at `(a, ρ)`. -/
@[irreducible] noncomputable def slicesOf (col : ℕ → K) (a slot : List E) : List E :=
  (List.range 64).map fun z ↦ Qs P col a z slot

theorem slicesOf_length (col : ℕ → K) (a slot : List E) : (slicesOf P col a slot).length = 64 := by
  unfold slicesOf; simp

theorem slicesOf_getD (col : ℕ → K) (a slot : List E) {z : ℕ} (hz : z < 64) :
    (slicesOf P col a slot).getD z 0 = Qs P col a z slot := by
  unfold slicesOf; simp [List.getD_eq_getElem?_getD, hz]

/-- The honest inputs' opening, returning what the verifier returns: the column claims `outs`,
the point and the slices. -/
noncomputable def hInput (col : ℕ → K) (claim : KeccakClaim) (outs : List ColumnClaim) :
    Script (List ColumnClaim × List E × List E) :=
  hSumcheck 3 (Fl P col claim) (List.replicate 4 none) [] >>= fun y ↦
  hOpen (Fs P col claim y.1) >>= fun x ↦
  Script.sendList (slicesOf P col (y.1 ++ claim.point.take P) x.1) >>= fun _ ↦
  Script.ret () >>= fun _ ↦
  Script.ret (outs, y.1 ++ claim.point.take P ++ x.1, slicesOf P col (y.1 ++ claim.point.take P) x.1)

theorem follows_input (col : ℕ → K) (claim : KeccakClaim) (hshape : ClaimShape P claim)
    (htrue : ClaimTrue (statesAt (P + 4) col 12) P claim) (outs : List ColumnClaim)
    (cs : Commits) :
    Follows (fun cs' a res ↦ cs' = cs ∧ a = res ∧ res.1 = outs ∧
        slicesTrue (P + 4) col res.2.1 res.2.2)
      (hInput P col claim outs) (inputTail (P + 4) claim outs) cs := by
  have hv : claim.value = Fl P col claim [] := by rw [htrue, Fl_nil]
  unfold inputTail hInput
  rw [hv]
  refine Follows.bind_of (follows_sumcheck 3 (by norm_num) (Fl P col claim) (List.replicate 4 none)
    [] cs
    (fun ext hext ↦ by
      simpa using (Fl_plainFamily P (fun _ : Unit ↦ col) claim () ext (by simpa using hext)).1)
    (fun ext hext ↦ by
      simp only [List.getElem_replicate, RoundSplit, List.nil_append]
      exact (Fl_plainFamily P (fun _ : Unit ↦ col) claim () ext (by simpa using hext)).2.symm))
    fun cs₁ y y' h₁ ↦ ?_
  obtain ⟨rfl, rfl, hl4, hf4⟩ := h₁
  have hy : y.1.length = 4 := by simpa using hl4
  rw [List.nil_append] at hf4
  refine Follows.bind_of (follows_open (Fs P col claim y.1) (P + 4) claim 0 keccakSegments y.2
    (fun _ acc hacc ↦ Fs_plainFamily P (fun _ : Unit ↦ col) claim y.1 () acc hacc)
    (by rw [hf4, Fl, cubeSum_full _ hy, Fs_nil P col claim hshape hy]) cs₁) fun cs₂ a x h₂ ↦ ?_
  obtain ⟨rfl, ha, hx6, hxw, hxv⟩ := h₂
  rw [show kBits = (slicesOf P col (y.1 ++ claim.point.take P) a.1).length from
    (slicesOf_length P col _ _).symm]
  refine Follows.bind_of (Follows.sendList_readN cs₂ _) fun cs₃ _ slices h₃ ↦ ?_
  obtain ⟨rfl, rfl⟩ := h₃
  have ha' : (y.1 ++ claim.point.take P).length = P + 4 := by
    simp [hy, hshape.2.1]; omega
  have hcheck : multilinearEval claim.mu y.1 *
      dot x.2.1 (slicesOf P col (y.1 ++ claim.point.take P) a.1) = x.2.2 := by
    rw [hxv, Fs, cubeSum_full _ hx6, hxw, multilinearEval_mu hshape.1 hy,
      dot_eq _ _ (by rw [fold_in_length P claim hx6, slicesOf_length]),
      fold_in_length P claim hx6]
    refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun z hz ↦ ?_)
    have hz' := Finset.mem_range.1 hz
    rw [fold_in P claim hx6 hz', slicesOf_getD P col _ _ hz', ha]
  refine Follows.bind_of (Follows.ret_require (R := fun cs' _ _ ↦ cs' = cs₃) hcheck rfl)
    fun cs₄ _ _ h₄ ↦ ?_
  subst h₄
  refine ⟨rfl, by rw [ha, show P + 4 - 4 = P by omega], rfl, ?_, slicesOf_length P col _ _,
    fun i hi ↦ ?_⟩
  · simp [hy, hshape.2.1, hx6]; omega
  · rw [show P + 4 - 4 = P by omega, slicesOf_getD P col _ _ hi, ha,
      ← slices_eq P col ha' hx6 i]

/-! ## The whole reduction -/

/-- **The honest Keccak prover**, returning what the verifier returns. -/
noncomputable def hKeccak (col : ℕ → K) (inst output : List E) :
    Script (List ColumnClaim × List E × List E) :=
  Script.sampleN 1 >>= fun segment ↦
  Script.sampleN 5 >>= fun lanesPt ↦
  Script.sendE (committedOf P col inst segment lanesPt) >>= fun _ ↦
  hLayers P col (List.range' 0 12)
    (firstClaim inst segment lanesPt output (committedOf P col inst segment lanesPt)) >>= fun claim ↦
  hOpen (Fo (P + 4) col inst segment lanesPt) >>= fun x ↦
  Script.sendE (Qo (P + 4) col inst x.1) >>= fun _ ↦
  Script.ret () >>= fun _ ↦
  hInput P col claim [(⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ x.1, Qo (P + 4) col inst x.1⟩ :
    ColumnClaim)]

/-- **Completeness of the Keccak reduction.** For a column whose output-lane claims hold
against the committed middle state and whose middle state agrees with twelve rounds of the
input at `inst`, the honest prover follows `verifyKeccak` (every check passes, for every
challenge), and the verifier returns true column claims and `64` true slice claims. -/
theorem follows_keccak (col : ℕ → K) {inst output : List E} (hi : inst.length = P + 4)
    (ho : output.length = 25) (hmid : outClaimsTrueMid (P + 4) col inst output)
    (hagree : midAgree (P + 4) col inst) (cs : Commits) :
    Follows (fun cs' a res ↦ cs' = cs ∧ a = res ∧ (∀ c ∈ res.1, colTrue (P + 4) col c) ∧
        slicesTrue (P + 4) col res.2.1 res.2.2 ∧ res.1.length = 1)
      (hKeccak P col inst output) (verifyKeccak (P + 4) inst output) cs := by
  rw [verifyKeccak_eq, gkrProg, keccakSegmentBits_eq, show keccakLaneBits = 5 from rfl]
  unfold hKeccak
  refine Follows.bind_of (Follows.sampleN_sampleN cs 1) fun cs₁ seg seg' h₁ ↦ ?_
  obtain ⟨rfl, rfl, hs⟩ := h₁
  refine Follows.bind_of (Follows.sampleN_sampleN cs₁ 5) fun cs₂ lanes lanes' h₂ ↦ ?_
  obtain ⟨rfl, rfl, hl⟩ := h₂
  refine Follows.bind_of (Follows.sendE_readE _ cs₂) fun cs₃ _ c h₃ ↦ ?_
  obtain ⟨rfl, rfl⟩ := h₃
  rw [show List.range keccakDepth = List.range' 0 12 from List.range_eq_range']
  refine Follows.bind_of (follows_layers P col cs₃ 12 0 rfl _ (firstClaim_shape _ hi hs)
    (first_true P col hi hs hl ho hmid hagree)) fun cs₄ claim claim' h₄ ↦ ?_
  obtain ⟨rfl, rfl, hshape, htrue⟩ := h₄
  refine Follows.bind_of (follows_open (Fo (P + 4) col inst seg lanes) (P + 4) _ 1
    (keccakSegments - 1) _ (fun _ acc hacc ↦ Fo_plainFamily (P + 4) (fun _ : Unit ↦ col) inst seg
      lanes () acc hacc) (by rw [Fo_nil (P + 4) col inst hs hl, committedOf]) cs₄)
    fun cs₅ a x h₅ ↦ ?_
  obtain ⟨rfl, ha, hx6, hxw, hxv⟩ := h₅
  refine Follows.bind_of (Follows.sendE_readE _ cs₅) fun cs₆ _ word h₆ ↦ ?_
  obtain ⟨rfl, rfl⟩ := h₆
  have hcheck : x.2.1.headD 0 * Qo (P + 4) col inst a.1 = x.2.2 := by
    rw [hxw, show keccakSegments - 1 = 1 from rfl, fold_out hi _ hx6, hxv, Fo,
      cubeSum_full _ hx6, ha]
  refine Follows.bind_of (Follows.ret_require (R := fun cs' _ _ ↦ cs' = cs₆) hcheck rfl)
    fun cs₇ _ _ h₇ ↦ ?_
  subst h₇
  rw [ha]
  refine Follows.mono (fun cs' u res hres ↦ ?_) _ _ _ (follows_input P col claim hshape htrue
    [(⟨qkeccak, inst.take 4 ++ inst.drop 4 ++ x.1, Qo (P + 4) col inst x.1⟩ : ColumnClaim)] cs₇)
  obtain ⟨hcs, hu, hres1, hsl⟩ := hres
  refine ⟨hcs, hu, fun c hc ↦ ?_, hsl, by rw [hres1]; rfl⟩
  rw [hres1, List.mem_singleton] at hc
  subst hc
  refine ⟨rfl, by simp [hi, hx6], ?_⟩
  show Qo (P + 4) col inst x.1 = _
  rw [List.take_append_drop, ← hx6, col_split hi, Qo, hx6]
  rfl

end
end LeanVM.Protocol.KeccakGkr
