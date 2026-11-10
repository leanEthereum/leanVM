/-
  LeanVM.Guest.B1.VerifySub.Complete

  `verify_sub`'s lift obligations on an honest child: its callees' words, and its honest
  valuation (`completeAt_flatDepR`'s `hkr`, `hkm`, `hσ`).
-/

module

public import LeanVM.Guest.B1.VerifySub.CLoads
public import LeanVM.Guest.B1.VerifySub.H.Fits
public import LeanVM.Guest.B1.VerifySub.H.Regions

/-!
# `verify_sub`'s obligations

On an honest child (`S : ChildSegs`), `verify_sub`'s body is flat (`completeAt_flatDepR`): its own
buffers hold `S.ownW`, its callees are `S.kids` on the bump allocator's bases. `vs_obligations`:
the callees read the caller's words, the own buffers and the results before them (`kid_lin_sub`
and its cases `10`, `11`, `15`), those words are in memory, and the honest valuation
`vsσ rd (vsW bs outs) (vsArgs …)` satisfies every statement (`vsCPre_complete` on `vs_sig`), the
allocations (`vs_alloc_sizes`, `vs_alloc_bases`), the frames (`hcm`, `VsCallsMatch`) and the loads
(`vs_loads`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- **The frames match the callees** on an honest child, with the own buffers at `b`. -/
def VsCallsMatch {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)
    (sqE outE : ℕ) (Lin : Main.Layout) : Prop :=
  ∀ (b : ℕ) (outs : List (List E × Main.Layout)), VsOuts S (bases b (vsSizes S.d)) sqE outs →
    ∀ rd : Reader, Main.MemL rd (bufL b (vsSizes S.d) S.ownW) → Main.MemL rd Lin →
      CallsMatch (vsσ rd (vsW (bases b (vsSizes S.d)) outs) (vsArgs seed c sqE outE))
        ((vsCPre.filterMap (Stmt.callSF (vsσ rd (vsW (bases b (vsSizes S.d)) outs)
          (vsArgs seed c sqE outE)))).map
          (Main.mkCall (vsσ rd (vsW (bases b (vsSizes S.d)) outs) (vsArgs seed c sqE outE))))
        (kidsAt (S.kids (bases b (vsSizes S.d)) sqE) [] outs) outs

theorem vs_w253 {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest} {c : Child}
    (S : ChildSegs bytecode seed c) {bs : List ℕ} {sqE : ℕ} {outs : List (List E × Main.Layout)}
    (O : VsOuts S bs sqE outs) : vsW bs outs 253 = gen ^ S.d := by
  rw [vsW_r (j := 2) (k := 0) (a := 253) (by norm_num) (by decide) rfl, O.o2, S.d_eq hbl]; simp

theorem vs_kidsAt_getD (ks : List KidD) (outs : List (List E × Main.Layout)) (j : ℕ) :
    kidAt ks [] outs j = ks.getD j noKid (outs.take j) := by
  simp [kidAt]

theorem vs_regionL {L : Main.Layout} {q : ℕ × List E} (hq : q ∈ L) {i : ℕ} (h1 : q.1 ≤ i)
    (h2 : i < q.1 + q.2.length) : Main.RegionL L i := ⟨q, hq, h1, h2⟩

/-- **`verify_sub`'s lift obligations on an honest child.** -/
theorem vs_obligations {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest}
    {c : Child} (S : ChildSegs bytecode seed c) (fs : String → ℕ) {sqE outE : ℕ}
    {Lin : Main.Layout} {κ : ℕ} (hκ : 16 ≤ κ) (hexp : ∀ q ∈ vsExpLin sqE, q ∈ Lin)
    (hout : (outE, DeferredClaim.cells c.freshClaim) ∈ Lin) (hcm : VsCallsMatch S sqE outE Lin) :
    let K := fun fp ↦ S.kids (bases (fp + fs "verify_sub") (vsSizes S.d)) sqE
    let own := fun fp ↦ bufL (fp + fs "verify_sub") (vsSizes S.d) S.ownW
    let args := vsArgs seed c sqE outE
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
          vsSizes S.d ∧
        ((vsCPre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs "verify_sub") (vsSizes S.d)).map (fun b ↦ ofK (addressOfIndex b)) ∧
        CallsMatch σ ((vsCPre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
          (kidsAt (K fp) [] outs) outs ∧
        ∀ q ∈ vsCPre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * Parameters.addressOfIndex q.2 =
            Parameters.addressOfIndex i ∧
          (Main.RegionL Lin i ∨ Main.RegionL (own fp) i ∨
            outRegion (kidsAt (K fp) [] outs) outs i)) := by
  intro K own args
  have hd := S.d_bounds hbl
  -- callee `j`'s words: the caller's, the own buffers', or an earlier callee's result
  have hlin : ∀ fp (outs : List (List E × Main.Layout)), OutsOk (kidsAt (K fp) [] outs) outs →
      ∀ j < 16, j < outs.length → ∀ q ∈ (kidAt (K fp) [] outs j).Lin,
        SubOf Lin q ∨ SubOf (own fp) q ∨
          ∃ m < j, (kidAt (K fp) [] outs m).taken = true ∧ q ∈ (outs.getD m ([], [])).2 := by
    intro fp outs ho j hj hjo q hq
    rw [vs_kidsAt_getD] at hq
    by_cases h10 : j = 10
    · subst h10
      have h9 := outsOk_at ho 9 (by simp [K, ChildSegs.kids_length]) (by omega) rfl
      rw [vs_kidsAt_getD] at h9
      rcases kid10_lin_sub hbl S (fp + fs "verify_sub") hexp (outs.take 10)
        (by rw [take_getD _ _ (by norm_num : 9 < 10)]; exact h9) q hq with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨9, by norm_num, rfl, by rwa [take_getD _ _ (by norm_num)] at h⟩)
    by_cases h11 : j = 11
    · subst h11
      exact (kid11_lin_sub hbl S (fp + fs "verify_sub") hexp (outs.take 11) q hq).imp_right Or.inl
    by_cases h15 : j = 15
    · subst h15
      rcases kid15_lin_sub hbl S (fp + fs "verify_sub") hexp (outs.take 15) q hq with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨3, by norm_num, rfl, by rwa [take_getD _ _ (by norm_num)] at h⟩)
      · exact Or.inr (Or.inr ⟨14, by norm_num, rfl, by rwa [take_getD _ _ (by norm_num)] at h⟩)
    exact (kid_lin_sub hbl S (fp + fs "verify_sub") hexp hj h10 h11 h15 (outs.take j) q hq).imp_right
      Or.inl
  refine ⟨?_, ?_, ?_⟩
  · -- the callees read the caller's words, the own buffers, the results before them
    intro fp outs ho
    refine regionsOk_kidsAt _ _ _ _ fun j hj hjo _ i hi ↦ ?_
    have hj16 : j < 16 := by simpa [K, ChildSegs.kids_length] using hj
    obtain ⟨q, hq, h1, h2⟩ := hi
    rcases hlin fp outs ho j hj16 hjo q hq with h | h | ⟨m, hm, hmt, hmq⟩
    · exact Or.inl (Or.inl (subOf_region h h1 h2))
    · exact Or.inl (Or.inr (subOf_region h h1 h2))
    · exact Or.inr (Or.inr ⟨m, hm, hmt, vs_regionL hmq h1 h2⟩)
  · -- the callees' words are in memory
    intro fp outs ho rd _ hB hL hLo
    refine memL_lins_kidsAt _ _ _ fun j hj hjo q hq ↦ ?_
    have hj16 : j < 16 := by simpa [K, ChildSegs.kids_length] using hj
    rcases hlin fp outs ho j hj16 hjo q hq with h | h | ⟨m, hm, hmt, hmq⟩
    · exact subOf_memL hL h
    · exact subOf_memL hB h
    · exact memL_outsL_at hLo m (by simp [K, ChildSegs.kids_length]; omega) (by omega) hmt q hmq
  · -- the honest valuation
    intro fp outs hlen ho rd hlow hB hL hLo
    have hl16 : outs.length = 16 := by rw [hlen]; rfl
    set b := fp + fs "verify_sub" with hb
    have O := vs_outs S (bases b (vsSizes S.d)) sqE outs hl16 ho
    obtain ⟨D⟩ := vs_sig hbl S b sqE outE hexp hout O hκ hlow hB hL
    have hla : args.length = 6 := rfl
    refine ⟨vsσ rd (vsW (bases b (vsSizes S.d)) outs) args, ?_, vs_dispOk D, ?_,
      vs_alloc_sizes hla (by omega) (vs_w253 hbl S O),
      vs_alloc_bases hla _ outs (by rw [bases_length]; rfl), hcm b outs O rd hB hL,
      fun q hq ↦ ?_⟩
    · rw [vs_params]
      simp only [List.map_cons, List.map_nil]
      rw [vsC_param hla (i := 0) (by norm_num), vsC_param hla (i := 1) (by norm_num),
        vsC_param hla (i := 2) (by norm_num), vsC_param hla (i := 3) (by norm_num),
        vsC_param hla (i := 4) (by norm_num), vsC_param hla (i := 5) (by norm_num)]
      rfl
    · rw [show Fn.body Data.core18 = vsCPre ++ [.ret []] from vs_body.trans vsT_splitPre,
        holdsList_append]
      exact vsCPre_complete D (by simp [Stmt.HoldsList, Stmt.Holds])
    · obtain ⟨i, hi, h⟩ := vs_loads hbl S b sqE outE hexp hout O hB q hq
      exact ⟨i, hi, h.imp_right Or.inl⟩

end
end LeanVM.Guest.B1.VerifySub
