/-
  LeanVM.Guest.B1.VerifySub.Complete

  `verify_sub` is complete on every honest child (`verify_sub_complete_Spec`), `verify_keccak`'s
  completeness (`VkCompleteAt`) assumed.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Match
public import LeanVM.Guest.B1.VerifySub.H.KidsC
public import LeanVM.Guest.AcceptableChild

/-!
# `verify_sub` is complete

`verify_sub_complete`: on an honest child (`child_segments`: its segments `S`), `verify_sub`'s
body is flat (`completeAt_flatDepR`). Its own buffers hold `S.ownW` (`ChildSegs.ownW_fits`); its
callees are `S.kids` (`kid_complete`, `term_complete`), reading slices of the caller's words, the
own buffers and (the terminal) `certify_placement`'s and `open_stacked`'s results; its valuation
is the honest one (`vs_sig`: the section data `vsCPre_complete` takes, `vs_callsMatch`,
`vs_loads`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

theorem vs_notIte : vsCPre.all notIteB = true := by decide +kernel

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- **The own buffers fit their sizes.** -/
theorem ownW_fits (hbl : bytecode.length = 2 ^ 23) (hst : c.proof.stream.length ≤ Coverage.childStreamCap) :
    List.Forall₂ (fun c s ↦ c.length ≤ s) S.ownW (vsSizes S.μ) := by
  have hpl := (S.runG' hbl).2.2.1
  have hτ := S.τ_bounds hbl
  obtain ⟨-, hopl, hkpl, hsll, -⟩ := S.runK' hbl
  have hn : S.H.n ≤ 32 := by
    show (Tables.tableHeightsOf S.rowsN).foldl max 0 ≤ 32
    rcases Tables.VtHonest.vsFoldl_max_mem (Tables.tableHeightsOf S.rowsN) 0 with h | h
    · omega
    · have := S.hh33 hbl _ h
      omega
  simp only [ChildSegs.ownW, vsSizes, List.forall₂_cons, List.forall₂_nil_left_iff, and_true]
  refine ⟨(S.poolW_length hbl).le, ?_, by simp [S.hrowsL], by simp [vsDimsW, S.hs_length],
    by simp [vsKbW, S.hs_length], hpl.le, S.alphas_length.le, ?_, ?_, ?_, hsll.le,
    S.rchs_length.le, by simp [ringCoefficients, kBits]⟩
  · simp only [vsStreamW, List.length_append, List.length_replicate, Coverage.childStreamCap] at hst ⊢
    omega
  · rw [KeccakGkr.eqKernel_length, S.alphas_length]
    norm_num
  · rw [S.chis_length]
    omega
  · simp only [zvW, List.length_append, List.length_replicate]
    omega

end ChildSegs

/-- **`verify_sub`'s lift obligations on an honest child**, but its callees' completeness: its
callees read the caller's words, its own buffers and the results before them, those words are in
memory, and its valuation is the honest one (`completeAt_flatDepR`'s and `completeAt_flatDepRB`'s
`hkr`, `hkm`, `hσ`). -/
theorem vs_obligations {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) (fs : String → ℕ) {sqE outE : ℕ}
    {Lin : Main.Layout} {κ : ℕ} (hκ : 14 ≤ κ) (hexpL : ∀ q ∈ log2Lin sqE, q ∈ Lin)
    (hout : (outE, DeferredClaim.cells c.freshClaim) ∈ Lin) :
    let K := fun fp ↦ S.kids (bases (fp + fs "verify_sub") (vsSizes S.μ)) sqE
    let own := fun fp ↦ bufL (fp + fs "verify_sub") (vsSizes S.μ) S.ownW
    let args := [(digestHalves (statementDigest seed c.statement)).1,
      (digestHalves (statementDigest seed c.statement)).2, (digestHalves seed).1,
      (digestHalves seed).2, ofK (addressOfIndex sqE), ofK (addressOfIndex outE)]
    (∀ fp outs, OutsOk (kidsAt (K fp) [] outs) outs →
      RegionsOk (fun i ↦ Main.RegionL Lin i ∨ Main.RegionL (own fp) i) (fun _ ↦ False)
        (kidsAt (K fp) [] outs) outs) ∧
    (∀ fp outs, OutsOk (kidsAt (K fp) [] outs) outs → ∀ rd, LowDef κ rd → Main.MemL rd (own fp) →
      Main.MemL rd Lin → Main.MemL rd (outsL (kidsAt (K fp) [] outs) outs) →
      Main.MemL rd (Kid.lins (kidsAt (K fp) [] outs))) ∧
    (∀ fp (outs : List (List E × Main.Layout)), outs.length = (K fp).length →
      OutsOk (kidsAt (K fp) [] outs) outs → ∀ rd, LowDef κ rd → Main.MemL rd (own fp) →
      Main.MemL rd Lin →
      Main.MemL rd (outsL (kidsAt (K fp) [] outs) outs) →
      ∃ σ : Val, (Fn.params Data.core18).map σ = args ∧ (∀ s ∈ vsCPre, DispOk σ s) ∧
        Stmt.HoldsList (fun _ _ _ ↦ True) rd σ (Fn.body Data.core18) False (fun r ↦ r = []) ∧
        (vsCPre.filterMap Main.Stmt.allocSz).map (fun x ↦ x.2.elim id fun s ↦ logG (σ s)) =
          vsSizes S.μ ∧
        ((vsCPre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs "verify_sub") (vsSizes S.μ)).map (fun b ↦ ofK (addressOfIndex b)) ∧
        CallsMatch σ ((vsCPre.filterMap (Stmt.callSF σ)).map (mkCall σ))
          (kidsAt (K fp) [] outs) outs ∧
        ∀ q ∈ vsCPre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * Parameters.addressOfIndex q.2 = Parameters.addressOfIndex i ∧
          (Main.RegionL Lin i ∨ Main.RegionL (own fp) i ∨
            outRegion (kidsAt (K fp) [] outs) outs i)) := by
  intro K own args
  dsimp only [K, own, args]
  have hsqm : (sqE, expTableWords) ∈ Lin := hexpL _ (by simp [log2Lin])
  -- the terminal's own words: the own buffers and the exponent table
  have hterm : ∀ b, ∀ q ∈ S.termLin (bases b (vsSizes S.μ)) sqE,
      q ∈ bufL b (vsSizes S.μ) S.ownW ∨ q ∈ Lin := by
    intro b q hq
    simp only [ChildSegs.termLin, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (vs_own_mem S b (i := 5) (by norm_num))
    · exact Or.inl (vs_own_mem S b (i := 8) (by norm_num))
    · exact Or.inl (vs_own_mem S b (i := 4) (by norm_num))
    · exact Or.inr hsqm
    · exact Or.inl (vs_own_mem S b (i := 9) (by norm_num))
    · exact Or.inl (vs_own_mem S b (i := 12) (by norm_num))
  -- the terminal's words when it is entered
  have hLin12 : ∀ (bs : List ℕ) (outs : List (List E × Main.Layout)),
      S.termOk (outs.take 12) →
      (kidAt (S.kids bs sqE) [] outs 12).Lin =
        (outs.getD 9 ([], [])).2 ++ (outs.getD 11 ([], [])).2 ++ S.termLin bs sqE := by
    intro bs outs hok
    show @ite _ (S.termOk (outs.take 12)) (Classical.propDecidable _) _ _ = _
    rw [@ite_pos' _ _ (Classical.propDecidable _) _ _ hok, ChildSegs.cpRes, ChildSegs.osRes,
      List.nil_append, take_getD _ _ (by norm_num : 9 < 12), take_getD _ _ (by norm_num : 11 < 12)]
  refine ⟨?_, ?_, ?_⟩
  · -- the callees read the caller's words, the own buffers, the results before them
    intro fp outs ho
    refine regionsOk_kidsAt _ _ _ _ fun j hj _ ht i hi ↦ ?_
    have hj13 : j < 13 := by simpa [ChildSegs.kids_length] using hj
    obtain ⟨q, hq, h1, h2⟩ := hi
    by_cases h12 : j < 12
    · rcases kid_lin_sub hbl S (fp + fs "verify_sub") hexpL h12 _ q hq with h | h
      · exact Or.inl (Or.inl (subOf_region h h1 h2))
      · exact Or.inl (Or.inr (subOf_region h h1 h2))
    · obtain rfl : j = 12 := by omega
      have hok : S.termOk (outs.take 12) := @of_decide_eq_true _ (Classical.propDecidable _) ht
      rw [hLin12 _ outs hok] at hq
      simp only [List.mem_append] at hq
      rcases hq with (hq | hq) | hq
      · exact Or.inr (Or.inr ⟨9, by norm_num, rfl, q, hq, h1, h2⟩)
      · exact Or.inr (Or.inr ⟨11, by norm_num, rfl, q, hq, h1, h2⟩)
      · rcases hterm _ q hq with h | h
        · exact Or.inl (Or.inr ⟨q, h, h1, h2⟩)
        · exact Or.inl (Or.inl ⟨q, h, h1, h2⟩)
  · -- the callees' words are in memory
    intro fp outs ho rd hlow hB hL hLo
    refine memL_lins_kidsAt _ _ _ fun j hj ho' ↦ ?_
    have hj13 : j < 13 := by simpa [ChildSegs.kids_length] using hj
    by_cases h12 : j < 12
    · intro q hq
      rcases kid_lin_sub hbl S (fp + fs "verify_sub") hexpL h12 _ q hq with h | h
      · exact subOf_memL hL h
      · exact subOf_memL hB h
    · obtain rfl : j = 12 := by omega
      by_cases hok : S.termOk (outs.take 12)
      · rw [hLin12 _ outs hok]
        intro q hq
        simp only [List.mem_append] at hq
        rcases hq with (hq | hq) | hq
        · exact memL_outsL_at hLo 9 (by simp [ChildSegs.kids_length]) (by omega) rfl q hq
        · exact memL_outsL_at hLo 11 (by simp [ChildSegs.kids_length]) (by omega) rfl q hq
        · rcases hterm _ q hq with h | h
          · exact hB q h
          · exact hL q h
      · intro q hq
        have hq' : q ∈ @ite _ (S.termOk (outs.take 12)) (Classical.propDecidable _)
            ((ChildSegs.cpRes (outs.take 12)).2 ++ (ChildSegs.osRes (outs.take 12)).2 ++
              S.termLin (bases (fp + fs "verify_sub") (vsSizes S.μ)) sqE) [] := hq
        rw [@ite_neg' _ _ (Classical.propDecidable _) _ _ hok] at hq'
        simp at hq'
  · -- the honest valuation
    intro fp outs hlen ho rd hlow hB hL hLo
    have hl13 : outs.length = 13 := by rw [hlen]; rfl
    set bs := bases (fp + fs "verify_sub") (vsSizes S.μ) with hbs
    have O := vs_outs S bs sqE outs hl13 ho
    have hmem : ∀ i < 13, ReadsAt rd (ofK (addressOfIndex (bs.getD i 0))) (S.ownW.getD i []) :=
      fun i hi ↦ hB _ (vs_own_mem S _ hi)
    have hsq := hL _ hsqm
    have hfx := hL _ hout
    obtain ⟨⟨D⟩, G⟩ := vs_sig (rd := rd) hbl S rfl bs outs O hκ hlow hmem hsq hfx
    have hpl := (S.runG' hbl).2.2.1
    have hcl : 24 ≤ (DeferredClaim.cells c.freshClaim).length := by
      rw [DeferredClaim.cells, S.fresh_eq hbl]
      simp only [List.length_append, List.length_take, List.length_cons, List.length_nil, hpl,
        S.alphas_length]
      have := (S.μ_bounds hbl).1
      omega
    -- `col_eval_words` in the stream buffer
    have hcev : ∃ e, vsσ rd (vsW bs outs) args (.n 645) = ofK (addressOfIndex e) ∧
        ∀ k < 159, Main.RegionL Lin (e + k) ∨
          Main.RegionL (bufL (fp + fs "verify_sub") (vsSizes S.μ) S.ownW) (e + k) := by
      refine ⟨_, G.e645, fun k hk ↦ Or.inr ⟨_, vs_own_mem S _ (i := 1) (by norm_num), ?_, ?_⟩⟩
      · simp only [ChildSegs.cT, vcG, vb, hbs]; omega
      · have := S.stream_pool_lt hbl (j := k + 5) (by omega)
        have hsl : c.proof.stream.length ≤ (S.ownW.getD 1 []).length := by
          show c.proof.stream.length ≤ (vsStreamW c.proof.stream).length
          simp [vsStreamW]
        simp only [ChildSegs.cT, vcG, vb, ← hbs]
        omega
    refine ⟨_, ?_, vs_dispOk S G.e1686, ?_, vs_alloc_sizes hbl G O, vs_alloc_bases G hbs,
      vs_callsMatch hbl rfl G O, vs_loads (fun k hk ↦ vs_own_mem S _ hk) G.ptr
        (S.ownW_lens hbl) hout hcl (G.par 5 (by norm_num)) hsqm hcev G.push⟩
    · rw [vs_params]
      simp only [List.map_cons, List.map_nil]
      rw [G.par 0 (by norm_num), G.par 1 (by norm_num), G.par 2 (by norm_num),
        G.par 3 (by norm_num), G.par 4 (by norm_num), G.par 5 (by norm_num)]
      rfl
    · rw [show Fn.body Data.core18 = vsCPre ++ [.ret []] from vs_body.trans vsT_splitPre,
        holdsList_append]
      exact vsCPre_complete D (by simp [Stmt.HoldsList, Stmt.Holds])

end
end LeanVM.Guest.B1.VerifySub
