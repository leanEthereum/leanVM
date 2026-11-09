/-
  LeanVM.Guest.B1.Da.FlatOut

  A flat function with dependent callees, each within its bound by a tree of its predicate,
  returning buffers of its own and of its callees: complete within its bound by a node of honest
  shape (`Budget.NodeHonest`).
-/

module

public import LeanVM.Guest.B1.Terminal.KidsDepBP
public import LeanVM.Guest.B1.Tables.FlatAtT

/-!
# Dependent callees, returned buffers

`completeAt_flatDepRBP` (`Terminal/KidsDepBP`) returns no buffer. `da_vector` returns its own
`zs` and the buffers of three of its callees (the top leaves in `da_expand`'s frame, the cell
factors, the column offsets), which `da_verify`'s column loop reads.

* `kidsFromInT_of_depBPo`: `kidsFromInT_of_depBP` with the callees' layout a permutation of the
  buffers they return (`outsL`) and the rest.
* `completeAt_flatDepOut`: a flat function whose dependent callees are within their bounds by
  trees of their predicates (`KidsDepBP`) is complete within `fs f + sizes.sum + Bs.sum`, by a
  node of `NodeHonest … (namedP fs names Bs Ps)`, its returned layout its own buffers and its
  callees' returned buffers (`Res (rets fp outs) (bufL … ++ outsL …)`); `completeAt_flatDepRet`:
the same returning words only (`Returns R`), the buffers its own layout.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem disjL_perm {L L' : Layout} (hp : L.Perm L') (h : DisjL L) : DisjL L' :=
  (hp.pairwise_iff fun {_ _} h => h.symm).mp h

theorem within_perm {L L' : Layout} {b n : ℕ} (hp : L.Perm L') (h : Within L b n) : Within L' b n :=
  fun q hq => h q (hp.mem_iff.mpr hq)

theorem memL_perm {rd : Reader} {L L' : Layout} (hp : L.Perm L') (h : MemL rd L) : MemL rd L' :=
  fun q hq => h q (hp.mem_iff.mpr hq)

theorem regionL_perm {L L' : Layout} (hp : L.Perm L') {i : ℕ} (h : RegionL L i) : RegionL L' i :=
  let ⟨q, hq, h1, h2⟩ := h
  ⟨q, hp.mem_iff.mp hq, h1, h2⟩

theorem outRegion_of_outsL : ∀ {ks : List Kid} {outs : List (List E × Layout)} {i : ℕ},
    RegionL (outsL ks outs) i → outRegion ks outs i
  | k :: ks, o :: os, i, ⟨q, hq, h1, h2⟩ => by
    simp only [outsL, List.mem_append] at hq
    rcases hq with hq | hq
    · by_cases ht : k.taken = true
      · simp only [ht, ↓reduceIte] at hq
        exact Or.inl ⟨ht, q, hq, h1, h2⟩
      · simp [ht] at hq
    · exact Or.inr (outRegion_of_outsL ⟨q, hq, h1, h2⟩)
  | [], _, _, ⟨q, hq, _⟩ => by simp [outsL] at hq
  | _ :: _, [], _, ⟨q, hq, _⟩ => by simp [outsL] at hq

/-- **`kidsFromInT_of_depBP`, the callees' layout a permutation of their returned buffers and
the rest.** -/
theorem kidsFromInT_of_depBPo (κ : ℕ) : ∀ (ks : List KidD) (names : List String) (Bs : List ℕ)
    (Ps : List (Tree → Prop))
    (prev : List (List E × Layout)), List.Forall₂ (fun k n ↦ ∀ pv, (k pv).f = n) ks names →
    KidsDepBP fs cert κ ks Bs Ps → ∀ b : ℕ,
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), N ≤ Bs.sum ∧
      outs.length = ks.length ∧
      OutsOk (kidsAt ks prev outs) outs ∧ Within L b N ∧ DisjL L ∧
      OutsIn (kidsAt ks prev outs) outs L ∧
      (∃ Lw : Layout, L.Perm (outsL (kidsAt ks prev outs) outs ++ Lw)) ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop),
        CallsMatch σ cs (kidsAt ks prev outs) outs → LowDef κ rd → MemL rd L →
        MemL rd (Kid.lins (kidsAt ks prev outs)) → RegionsOk R Dacc (kidsAt ks prev outs) outs →
        KidsFromInT coreProgram fs cert rd σ R Dacc cs (namedP fs names Bs Ps)
          b N (fun i => Dacc i ∨ outRegion (kidsAt ks prev outs) outs i)
  | [], [], [], [], _, _, _, b => ⟨0, [], [], le_rfl, rfl, trivial, fun _ h => by simp at h, disj_nil,
      trivial, ⟨[], by simp [kidsAt, outsL]⟩, fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | [], [], _ :: _, _, _, _, h, _ => by simp [KidsDepBP] at h
  | [], [], [], _ :: _, _, _, h, _ => by simp [KidsDepBP] at h
  | _ :: _, _ :: _, [], _, _, _, h, _ => by simp [KidsDepBP] at h
  | _ :: _, _ :: _, _ :: _, [], _, _, h, _ => by simp [KidsDepBP] at h
  | [], _ :: _, _, _, _, hn, _, _ => by simp at hn
  | _ :: _, [], _, _, _, hn, _, _ => by simp at hn
  | kf :: ks, nm :: names, bk :: Bs, P :: Ps, prev, hn, ⟨hok, hoks⟩, b => by
    obtain ⟨hnm, hns⟩ := List.forall₂_cons.mp hn
    by_cases ht : (kf prev).taken = true
    · obtain ⟨n, Lown, rets, Lout, hnb, hout, hw, hd, hrel⟩ := (hok prev).1 ht b
      obtain ⟨N, L, outs, hNb, hlen, ho, hW, hD, hI, ⟨Lw, hP⟩, hK⟩ :=
        kidsFromInT_of_depBPo κ ks names Bs Ps (prev ++ [(rets, Lout)]) hns hoks (b + n)
      refine ⟨n + N, Lout ++ Lown ++ L, (rets, Lout) :: outs, by simp only [List.sum_cons]; omega,
        by simp [hlen], ⟨fun _ => hout, ho⟩, ?_, disj_append hd hD hw hW le_rfl,
        ⟨fun _ q hq => by simp [hq], hI.mono fun q hq => by simp [hq]⟩, ⟨Lw ++ Lown, ?_⟩, ?_⟩
      · rw [within_append]
        exact ⟨hw.mono le_rfl (by omega), hW.mono (by omega) (by omega)⟩
      · simp only [kidsAt, outsL, ht, ↓reduceIte, List.append_assoc]
        refine List.Perm.append_left Lout ?_
        refine ((hP.append_left Lown).trans List.perm_append_comm).trans ?_
        simp only [List.append_assoc]
        exact List.Perm.refl _
      · intro rd σ cs R Dacc hc hlow hL hLin hRg
        match cs, hc with
        | c :: cs, ⟨hf, hct, hcar, hc⟩ =>
          obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
          simp only [kidsAt, Kid.lins, List.flatMap_cons] at hLin
          obtain ⟨hLk, hLs⟩ := Main.memL_append.mp hLin
          obtain ⟨hR1, hR2⟩ := hRg
          obtain ⟨ha, hr⟩ := hcar ht
          refine ⟨n, N, RegionL (kf prev).Lin, RegionL Lout, rfl, hR1 ht, ?_, ?_⟩
          · rw [hct]
            simp only [ht, ↓reduceIte]
            rw [hf, ha, hr]
            have h := relAtInT_named (B := bk) (hrel rd hlow (Main.memL_append.mpr ⟨hL1, hLk⟩)) hnb
            rw [hnm prev] at h ⊢
            exact h
          · refine kidsFromInT_dend cs _ _ _ _ ?_ (hK rd σ cs R _ hc hlow hL2 hLs ?_)
            · intro i hi
              rcases hi with hi | ⟨_, hi⟩ | hi
              · exact Or.inl (Or.inl hi)
              · exact Or.inl (Or.inr ⟨by rw [hct]; exact ht, hi⟩)
              · exact Or.inr hi
            · simpa [hct] using hR2
    · have ht' : (kf prev).taken = false := by simpa using ht
      have hfb := (hok prev).2 ht'
      obtain ⟨N, L, outs, hNb, hlen, ho, hW, hD, hI, ⟨Lw, hP⟩, hK⟩ :=
        kidsFromInT_of_depBPo κ ks names Bs Ps (prev ++ [([], [])]) hns hoks (b + fs (kf prev).f)
      refine ⟨fs (kf prev).f + N, L, ([], []) :: outs, by simp only [List.sum_cons]; omega,
        by simp [hlen], ⟨fun h => absurd h ht, ho⟩,
        hW.mono (by omega) (by omega), hD, ⟨fun h => absurd h ht, hI⟩, ⟨Lw, ?_⟩, ?_⟩
      · simpa [kidsAt, outsL, ht'] using hP
      intro rd σ cs R Dacc hc hlow hL hLin hRg
      match cs, hc with
      | c :: cs, ⟨hf, hct, _, hc⟩ =>
        simp only [kidsAt, Kid.lins, List.flatMap_cons] at hLin
        refine ⟨fs (kf prev).f, N, fun _ => False, fun _ => False, rfl, fun _ h => h.elim, ?_, ?_⟩
        · rw [hct, ht']
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hf]
        · refine kidsFromInT_dend cs _ _ _ _ ?_
            (hK rd σ cs R _ hc hlow hL (Main.memL_append.mp hLin).2 ?_)
          · intro i hi
            rcases hi with hi | ⟨h, _⟩ | hi
            · exact Or.inl (Or.inl hi)
            · exact absurd h ht
            · exact Or.inr hi
          · have := hRg.2
            simp only [hct, ht, Bool.false_eq_true, false_and, or_false] at this ⊢
            exact this

/-- **A flat function with dependent callees, returning its own and its callees' buffers, is
complete within `fs f + sizes.sum + Bs.sum`** by a node of honest shape: its walk's calls, its
`HeapBuf`s, its callees by `namedP fs names Bs Ps`, its valuation satisfying `Q`. -/
theorem completeAt_flatDepOut {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args : List E)
    (rets : ℕ → List (List E × Layout) → List E) (Res : List E → Layout → Prop)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (hni : pre.all notIteB = true)
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes) (kids : ℕ → List KidD)
    (names : List String) (Bs : List ℕ) (Ps : List (Tree → Prop)) (Q : Val → Prop)
    (hn : ∀ fp, List.Forall₂ (fun k n ↦ ∀ pv, (k pv).f = n) (kids fp) names)
    (hkc : ∀ fp, KidsDepBP fs cert κ (kids fp) Bs Ps)
    (hout : ∀ fp outs, outs.length = (kids fp).length → OutsOk (kidsAt (kids fp) [] outs) outs →
      Res (rets fp outs) (bufL (fp + fs f) sizes (own fp) ++ outsL (kidsAt (kids fp) [] outs) outs))
    (hkr : ∀ fp outs, OutsOk (kidsAt (kids fp) [] outs) outs →
      RegionsOk (fun i => RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i) (fun _ => False)
        (kidsAt (kids fp) [] outs) outs)
    (hkm : ∀ fp outs, OutsOk (kidsAt (kids fp) [] outs) outs → ∀ rd, LowDef κ rd →
      MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      MemL rd (outsL (kidsAt (kids fp) [] outs) outs) → MemL rd (Kid.lins (kidsAt (kids fp) [] outs)))
    (hσ : ∀ fp (outs : List (List E × Layout)), outs.length = (kids fp).length →
      OutsOk (kidsAt (kids fp) [] outs) outs → ∀ rd,
      LowDef κ rd → MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      MemL rd (outsL (kidsAt (kids fp) [] outs) outs) →
      ∃ σ : Val, fn.params.map σ = args ∧ (∀ s ∈ pre, DispOk σ s) ∧
        Stmt.HoldsList (fun _ _ _ => True) rd σ fn.body False (fun r => r = rets fp outs) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (addressOfIndex b)) ∧
        CallsMatch σ (flatCalls pre σ) (kidsAt (kids fp) [] outs) outs ∧
        (∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 =
            addressOfIndex i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i ∨
            outRegion (kidsAt (kids fp) [] outs) outs i)) ∧ Q σ) :
    CompleteAtDTB fs cert κ f Lin args Res
      (Budget.NodeHonest coreProgram f Q (flatCalls pre) (fun _ ↦ sizes) (namedP fs names Bs Ps))
      (fs f + sizes.sum + Bs.sum) := by
  intro fp
  obtain ⟨N, L, outs, hNb, hlen, ho, hW, hD, hI, ⟨Lw, hP⟩, hK⟩ := kidsFromInT_of_depBPo (fs := fs)
    (cert := cert) κ (kids fp) names Bs Ps [] (hn fp) (hkc fp) (fp + fs f + sizes.sum)
  have hdj := disj_append (bufL_disj _ _ _ (hown fp)) hD (bufL_within _ _ _ (hown fp)) hW le_rfl
  have hPf : (bufL (fp + fs f) sizes (own fp) ++ L).Perm
      (bufL (fp + fs f) sizes (own fp) ++ outsL (kidsAt (kids fp) [] outs) outs ++ Lw) := by
    rw [List.append_assoc]; exact hP.append_left _
  refine ⟨fs f + sizes.sum + N, Lw, rets fp outs,
    bufL (fp + fs f) sizes (own fp) ++ outsL (kidsAt (kids fp) [] outs) outs, by omega,
    hout fp outs hlen ho, ?_, disjL_perm hPf hdj, fun rd hlow hL => ?_⟩
  · refine within_perm hPf ?_
    rw [within_append]
    exact ⟨(bufL_within _ _ _ (hown fp)).mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  obtain ⟨hLm, hLin⟩ := Main.memL_append.mp hL
  have hLm' := memL_perm hPf.symm hLm
  obtain ⟨hB, hLk⟩ := Main.memL_append.mp hLm'
  have hLo := memL_outsL hI hLk
  obtain ⟨σ, hp, hdo, hh, hsz, hbuf, hcm, hld, hQ⟩ := hσ fp outs hlen ho rd hlow hB hLin hLo
  have hw := walk_flat σ vs pre hst hdo
  rw [← hb] at hw
  obtain ⟨i1, i2, i3, i4, i5⟩ := flat_parts σ pre hst
  have hsat := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
  rw [hw] at hsat
  have hes : ∀ e ∈ pre.flatMap (flEvs σ), e.Holds rd σ := fun e he => (hsat.1 e he).1
  have hr : vs.map σ = rets fp outs := hsat.2
  have hal : allocs σ (pre.flatMap (flEvs σ)) = sizes := by rw [i2, hsz]
  have hown' : ∀ i, RegionL (bufL (fp + fs f) sizes (own fp)) i →
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i :=
    fun i hi => Or.inl (by rw [hal]; exact bufL_region _ _ _ (hown fp) i hi)
  have hk := hK rd σ (calls (pre.flatMap (flEvs σ))) (fun i => RegionL Lin i ∨
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i)
    (fun _ => False) (by rw [i4]; exact hcm) hlow hLk (hkm fp outs ho rd hlow hB hLin hLo)
    ((hkr fp outs ho).mono_R fun i hi => hi.imp_right (hown' i))
  have hb' : fp + fs f + sizes.sum = fp + fs f + (allocs σ (pre.flatMap (flEvs σ))).sum := by
    rw [hal]
  rw [hb'] at hk
  have hcl : (calls (pre.flatMap (flEvs σ))).length ≤ (namedP fs names Bs Ps).length := by
    rw [i4]
    show (flatCalls pre σ).length ≤ _
    rw [kdbt_callsMatch_length hcm, kidsAt_length _ _ _ hlen,
      namedP_length (hn fp).length_eq (hkc fp).length.1 (hkc fp).length.2]
  obtain ⟨t, ⟨htn, htv, htb, htp, htt, htl, htd⟩, ks, rfl, hkT⟩ :=
    relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := RegionL (bufL (fp + fs f) sizes (own fp) ++ outsL (kidsAt (kids fp) [] outs) outs))
    (Dk := fun i => False ∨ outRegion (kidsAt (kids fp) [] outs) outs i) (N := N)
    (fp := fp) coreProgram_wf hf (Or.inl hl) hp hw hr hes (by rw [hal, i1]; exact hbuf)
    (by rw [i3, haddrs]; simp) _ hk (fun A hA => by
      rw [i5] at hA
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
      obtain ⟨i, hi, h | h | h⟩ := hld q (filterMap_of_loadsEv hni hq)
      · exact ⟨i, hi, Or.inr (Or.inl h)⟩
      · exact ⟨i, hi, Or.inl (hown' i h)⟩
      · exact ⟨i, hi, Or.inr (Or.inr (Or.inr h))⟩)
    (fun i hi => by
      obtain ⟨q, hq, h1, h2⟩ := hi
      rcases List.mem_append.mp hq with hq | hq
      · exact Or.inl (hown' i ⟨q, hq, h1, h2⟩)
      · exact Or.inr (Or.inr (outRegion_of_outsL ⟨q, hq, h1, h2⟩)))
  refine ⟨_, ⟨htn, htv, htb, htp, by rw [htt, hal], htl, htd⟩, σ, ks, by rw [hal], hQ,
    fun fn' es' vs' hf' hw' => ?_, ?_, ?_⟩
  · rw [hf, Option.some.injEq] at hf'
    subst hf'
    rw [hw, Out.ret.injEq] at hw'
    rw [← hw'.1, i4]
    rfl
  · rw [i4] at hcl; exact hcl
  · rw [i4] at hkT; exact hkT

/-- **`completeAt_flatDepOut`, returning words and no buffer**: its own and its callees' buffers
are its own layout (`Returns R`). -/
theorem completeAt_flatDepRet {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args : List E)
    (rets : ℕ → List (List E × Layout) → List E) (R : List E)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (hni : pre.all notIteB = true)
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes) (kids : ℕ → List KidD)
    (names : List String) (Bs : List ℕ) (Ps : List (Tree → Prop)) (Q : Val → Prop)
    (hn : ∀ fp, List.Forall₂ (fun k n ↦ ∀ pv, (k pv).f = n) (kids fp) names)
    (hkc : ∀ fp, KidsDepBP fs cert κ (kids fp) Bs Ps)
    (hout : ∀ fp outs, outs.length = (kids fp).length → OutsOk (kidsAt (kids fp) [] outs) outs →
      rets fp outs = R)
    (hkr : ∀ fp outs, OutsOk (kidsAt (kids fp) [] outs) outs →
      RegionsOk (fun i => RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i) (fun _ => False)
        (kidsAt (kids fp) [] outs) outs)
    (hkm : ∀ fp outs, OutsOk (kidsAt (kids fp) [] outs) outs → ∀ rd, LowDef κ rd →
      MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      MemL rd (outsL (kidsAt (kids fp) [] outs) outs) → MemL rd (Kid.lins (kidsAt (kids fp) [] outs)))
    (hσ : ∀ fp (outs : List (List E × Layout)), outs.length = (kids fp).length →
      OutsOk (kidsAt (kids fp) [] outs) outs → ∀ rd,
      LowDef κ rd → MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      MemL rd (outsL (kidsAt (kids fp) [] outs) outs) →
      ∃ σ : Val, fn.params.map σ = args ∧ (∀ s ∈ pre, DispOk σ s) ∧
        Stmt.HoldsList (fun _ _ _ => True) rd σ fn.body False (fun r => r = rets fp outs) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (addressOfIndex b)) ∧
        CallsMatch σ (flatCalls pre σ) (kidsAt (kids fp) [] outs) outs ∧
        (∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 =
            addressOfIndex i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i ∨
            outRegion (kidsAt (kids fp) [] outs) outs i)) ∧ Q σ) :
    CompleteAtDTB fs cert κ f Lin args (Returns R)
      (Budget.NodeHonest coreProgram f Q (flatCalls pre) (fun _ ↦ sizes) (namedP fs names Bs Ps))
      (fs f + sizes.sum + Bs.sum) := by
  intro fp
  obtain ⟨N, L, outs, hNb, hlen, ho, hW, hD, hI, ⟨Lw, hP⟩, hK⟩ := kidsFromInT_of_depBPo (fs := fs)
    (cert := cert) κ (kids fp) names Bs Ps [] (hn fp) (hkc fp) (fp + fs f + sizes.sum)
  have hdj := disj_append (bufL_disj _ _ _ (hown fp)) hD (bufL_within _ _ _ (hown fp)) hW le_rfl
  have hPf : (bufL (fp + fs f) sizes (own fp) ++ L).Perm
      (bufL (fp + fs f) sizes (own fp) ++ outsL (kidsAt (kids fp) [] outs) outs ++ Lw) := by
    rw [List.append_assoc]; exact hP.append_left _
  refine ⟨fs f + sizes.sum + N,
    bufL (fp + fs f) sizes (own fp) ++ outsL (kidsAt (kids fp) [] outs) outs ++ Lw, rets fp outs,
    [], by omega, ⟨hout fp outs hlen ho, rfl⟩, ?_, by rw [List.nil_append]; exact disjL_perm hPf hdj,
    fun rd hlow hL => ?_⟩
  · rw [List.nil_append]
    refine within_perm hPf ?_
    rw [within_append]
    exact ⟨(bufL_within _ _ _ (hown fp)).mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  rw [List.nil_append] at hL
  obtain ⟨hLm, hLin⟩ := Main.memL_append.mp hL
  have hLm' := memL_perm hPf.symm hLm
  obtain ⟨hB, hLk⟩ := Main.memL_append.mp hLm'
  have hLo := memL_outsL hI hLk
  obtain ⟨σ, hp, hdo, hh, hsz, hbuf, hcm, hld, hQ⟩ := hσ fp outs hlen ho rd hlow hB hLin hLo
  have hw := walk_flat σ vs pre hst hdo
  rw [← hb] at hw
  obtain ⟨i1, i2, i3, i4, i5⟩ := flat_parts σ pre hst
  have hsat := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
  rw [hw] at hsat
  have hes : ∀ e ∈ pre.flatMap (flEvs σ), e.Holds rd σ := fun e he => (hsat.1 e he).1
  have hr : vs.map σ = rets fp outs := hsat.2
  have hal : allocs σ (pre.flatMap (flEvs σ)) = sizes := by rw [i2, hsz]
  have hown' : ∀ i, RegionL (bufL (fp + fs f) sizes (own fp)) i →
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i :=
    fun i hi => Or.inl (by rw [hal]; exact bufL_region _ _ _ (hown fp) i hi)
  have hk := hK rd σ (calls (pre.flatMap (flEvs σ))) (fun i => RegionL Lin i ∨
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i)
    (fun _ => False) (by rw [i4]; exact hcm) hlow hLk (hkm fp outs ho rd hlow hB hLin hLo)
    ((hkr fp outs ho).mono_R fun i hi => hi.imp_right (hown' i))
  have hb' : fp + fs f + sizes.sum = fp + fs f + (allocs σ (pre.flatMap (flEvs σ))).sum := by
    rw [hal]
  rw [hb'] at hk
  have hcl : (calls (pre.flatMap (flEvs σ))).length ≤ (namedP fs names Bs Ps).length := by
    rw [i4]
    show (flatCalls pre σ).length ≤ _
    rw [kdbt_callsMatch_length hcm, kidsAt_length _ _ _ hlen,
      namedP_length (hn fp).length_eq (hkc fp).length.1 (hkc fp).length.2]
  obtain ⟨t, ⟨htn, htv, htb, htp, htt, htl, htd⟩, ks, rfl, hkT⟩ :=
    relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := RegionL [])
    (Dk := fun i => False ∨ outRegion (kidsAt (kids fp) [] outs) outs i) (N := N)
    (fp := fp) coreProgram_wf hf (Or.inl hl) hp hw hr hes (by rw [hal, i1]; exact hbuf)
    (by rw [i3, haddrs]; simp) _ hk (fun A hA => by
      rw [i5] at hA
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
      obtain ⟨i, hi, h | h | h⟩ := hld q (filterMap_of_loadsEv hni hq)
      · exact ⟨i, hi, Or.inr (Or.inl h)⟩
      · exact ⟨i, hi, Or.inl (hown' i h)⟩
      · exact ⟨i, hi, Or.inr (Or.inr (Or.inr h))⟩)
    (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  refine ⟨_, ⟨htn, htv, htb, htp, by rw [htt, hal], htl, htd⟩, σ, ks, by rw [hal], hQ,
    fun fn' es' vs' hf' hw' => ?_, ?_, ?_⟩
  · rw [hf, Option.some.injEq] at hf'
    subst hf'
    rw [hw, Out.ret.injEq] at hw'
    rw [← hw'.1, i4]
    rfl
  · rw [i4] at hcl; exact hcl
  · rw [i4] at hkT; exact hkT

end
end LeanVM.Guest.B1
