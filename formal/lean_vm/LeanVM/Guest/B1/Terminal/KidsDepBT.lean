/-
  LeanVM.Guest.B1.Terminal.KidsDepBT

  `KidsDepB`'s lift with the node's shape exposed: a flat function with dependent callees, each
  within its bound, is complete within its bound by a node whose `j`-th entered callee is a call of
  its `j`-th name within its `j`-th bound (`Budget.FlatShape`).
-/

module

public import LeanVM.Guest.B1.Terminal.KidsDepB
public import LeanVM.Guest.Budget.FlatShape
public import LeanVM.Guest.Budget.Bounded

/-!
# Dependent callees within their bounds, by name

`kidsFromInT_of_depB`: `kidsFromIn_of_depB` with the callees' trees exposed, callee `j` a call of
`names[j]` (every callee `j` calls `names[j]` on every result before it) within `Bs[j]` words.
`completeAt_flatDepRBT`: `completeAt_flatDepRB` by a node of `Budget.FlatShape` for those
predicates.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- A run within `B` words, by a call of `f`. -/
theorem relAtIn_named {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    {B : ℕ} (h : RelAtIn coreProgram fs cert rd R D fp n f args rets) (hB : n ≤ B) :
    RelAtInT coreProgram fs cert rd R D fp n f args rets (Budget.NamedWithin fs f B) :=
  let ⟨t, ht⟩ := h
  ⟨t, ht, ht.1, by rw [ht.2.2.2.2.1]; exact hB⟩

/-- Matching frames are as many as the callees. -/
theorem kdbt_callsMatch_length {σ : Val} : ∀ {cs : List Call} {ks : List Kid}
    {outs : List (List E × Layout)}, CallsMatch σ cs ks outs → cs.length = ks.length
  | [], [], [], _ => rfl
  | _ :: _, _ :: _, _ :: _, h => by rw [List.length_cons, List.length_cons, kdbt_callsMatch_length h.2.2.2]
  | [], [], _ :: _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, [], h => h.elim

theorem kidsAt_length : ∀ (ks : List KidD) (prev outs : List (List E × Layout)),
    outs.length = ks.length → (kidsAt ks prev outs).length = ks.length
  | [], _, _, _ => by simp [kidsAt]
  | _ :: _, _, [], h => by simp at h
  | _ :: ks, prev, _ :: outs, h => by
    simp only [kidsAt, List.length_cons, kidsAt_length ks _ outs (by simpa using h)]

/-- **Dependent callees by name, within their bounds**: `kidsFromIn_of_depB` with callee `j`'s
tree a call of `names[j]` within `Bs[j]` words. -/
theorem kidsFromInT_of_depB (κ : ℕ) : ∀ (ks : List KidD) (names : List String) (Bs : List ℕ)
    (prev : List (List E × Layout)), List.Forall₂ (fun k n ↦ ∀ pv, (k pv).f = n) ks names →
    KidsDepB fs cert κ ks Bs → ∀ b : ℕ,
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), N ≤ Bs.sum ∧
      outs.length = ks.length ∧
      OutsOk (kidsAt ks prev outs) outs ∧ Within L b N ∧ DisjL L ∧
      OutsIn (kidsAt ks prev outs) outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop),
        CallsMatch σ cs (kidsAt ks prev outs) outs → LowDef κ rd → MemL rd L →
        MemL rd (Kid.lins (kidsAt ks prev outs)) → RegionsOk R Dacc (kidsAt ks prev outs) outs →
        KidsFromInT coreProgram fs cert rd σ R Dacc cs (List.zipWith (Budget.NamedWithin fs) names Bs)
          b N (fun i => Dacc i ∨ outRegion (kidsAt ks prev outs) outs i)
  | [], [], [], _, _, _, b => ⟨0, [], [], le_rfl, rfl, trivial, fun _ h => by simp at h, disj_nil,
      trivial, fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | [], [], _ :: _, _, _, h, _ => by simp [KidsDepB] at h
  | _ :: _, _ :: _, [], _, _, h, _ => by simp [KidsDepB] at h
  | [], _ :: _, _, _, hn, _, _ => by simp at hn
  | _ :: _, [], _, _, hn, _, _ => by simp at hn
  | kf :: ks, nm :: names, bk :: Bs, prev, hn, ⟨hok, hoks⟩, b => by
    obtain ⟨hnm, hns⟩ := List.forall₂_cons.mp hn
    by_cases ht : (kf prev).taken = true
    · obtain ⟨n, Lown, rets, Lout, hout, hw, hd, hnb, hrel⟩ := (hok prev).1 ht b
      obtain ⟨N, L, outs, hNb, hlen, ho, hW, hD, hI, hK⟩ :=
        kidsFromInT_of_depB κ ks names Bs (prev ++ [(rets, Lout)]) hns hoks (b + n)
      refine ⟨n + N, Lout ++ Lown ++ L, (rets, Lout) :: outs, by simp only [List.sum_cons]; omega,
        by simp [hlen], ⟨fun _ => hout, ho⟩, ?_, disj_append hd hD hw hW le_rfl,
        ⟨fun _ q hq => by simp [hq], hI.mono fun q hq => by simp [hq]⟩, ?_⟩
      · rw [within_append]
        exact ⟨hw.mono le_rfl (by omega), hW.mono (by omega) (by omega)⟩
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
            have h := relAtIn_named (B := bk) (hrel rd hlow (Main.memL_append.mpr ⟨hL1, hLk⟩)) hnb
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
      obtain ⟨N, L, outs, hNb, hlen, ho, hW, hD, hI, hK⟩ :=
        kidsFromInT_of_depB κ ks names Bs (prev ++ [([], [])]) hns hoks (b + fs (kf prev).f)
      refine ⟨fs (kf prev).f + N, L, ([], []) :: outs, by simp only [List.sum_cons]; omega,
        by simp [hlen], ⟨fun h => absurd h ht, ho⟩,
        hW.mono (by omega) (by omega), hD, ⟨fun h => absurd h ht, hI⟩, ?_⟩
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

/-- **`completeAt_flatDepRB` by a node of `FlatShape`**: within `fs f + sizes.sum + Bs.sum`, by a
node of `f` whose `j`-th entered callee is a call of `names[j]` within `Bs[j]` words. -/
theorem completeAt_flatDepRBT {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (hni : pre.all notIteB = true)
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes) (kids : ℕ → List KidD)
    (names : List String) (Bs : List ℕ)
    (hn : ∀ fp, List.Forall₂ (fun k n ↦ ∀ pv, (k pv).f = n) (kids fp) names)
    (hkc : ∀ fp, KidsDepB fs cert κ (kids fp) Bs)
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
        Stmt.HoldsList (fun _ _ _ => True) rd σ fn.body False (fun r => r = rets) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (addressOfIndex b)) ∧
        CallsMatch σ ((pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
          (kidsAt (kids fp) [] outs) outs ∧
        ∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 =
            addressOfIndex i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp)) i ∨
            outRegion (kidsAt (kids fp) [] outs) outs i)) :
    CompleteAtDTB fs cert κ f Lin args (Returns rets)
      (Budget.FlatShape coreProgram f (List.zipWith (Budget.NamedWithin fs) names Bs))
      (fs f + sizes.sum + Bs.sum) := by
  intro fp
  obtain ⟨N, L, outs, hNb, hlen, ho, hW, hD, hI, hK⟩ := kidsFromInT_of_depB (fs := fs) (cert := cert) κ
    (kids fp) names Bs [] (hn fp) (hkc fp) (fp + fs f + sizes.sum)
  refine ⟨fs f + sizes.sum + N, bufL (fp + fs f) sizes (own fp) ++ L, rets, [], by omega, ⟨rfl, rfl⟩,
    ?_, by simpa using disj_append (bufL_disj _ _ _ (hown fp)) hD (bufL_within _ _ _ (hown fp)) hW le_rfl,
    fun rd hlow hL => ?_⟩
  · simp only [List.nil_append, within_append]
    exact ⟨(bufL_within _ _ _ (hown fp)).mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hL
  obtain ⟨hLm, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hB, hLk⟩ := Main.memL_append.mp hLm
  have hLo := memL_outsL hI hLk
  obtain ⟨σ, hp, hdo, hh, hsz, hbuf, hcm, hld⟩ := hσ fp outs hlen ho rd hlow hB hLin hLo
  have hw := walk_flat σ vs pre hst hdo
  rw [← hb] at hw
  obtain ⟨i1, i2, i3, i4, i5⟩ := flat_parts σ pre hst
  have hsat := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
  rw [hw] at hsat
  have hes : ∀ e ∈ pre.flatMap (flEvs σ), e.Holds rd σ := fun e he => (hsat.1 e he).1
  have hr : vs.map σ = rets := hsat.2
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
  -- the number of calls
  have hcl : (calls (pre.flatMap (flEvs σ))).length ≤
      (List.zipWith (Budget.NamedWithin fs) names Bs).length := by
    rw [i4, kdbt_callsMatch_length hcm, kidsAt_length _ _ _ hlen, List.length_zipWith,
      ← (hn fp).length_eq, (hkc fp).length, Nat.min_self]
  obtain ⟨t, ⟨htn, htv, htb, htp, htt, htl, htd⟩, ks, rfl, hkT⟩ :=
    relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun i => False ∨ outRegion (kidsAt (kids fp) [] outs) outs i) (N := N)
    (fp := fp) coreProgram_wf hf (Or.inl hl) hp hw hr hes (by rw [hal, i1]; exact hbuf)
    (by rw [i3, haddrs]; simp) _ hk (fun A hA => by
      rw [i5] at hA
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
      obtain ⟨i, hi, h | h | h⟩ := hld q (filterMap_of_loadsEv hni hq)
      · exact ⟨i, hi, Or.inr (Or.inl h)⟩
      · exact ⟨i, hi, Or.inl (hown' i h)⟩
      · exact ⟨i, hi, Or.inr (Or.inr (Or.inr h))⟩)
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  refine ⟨_, ⟨htn, htv, htb, htp, by rw [htt, hal], htl, htd⟩, σ, _, ks, rfl,
    fun fn' es' vs' hf' hw' ↦ ?_⟩
  rw [hf] at hf'
  cases hf'
  rw [hw] at hw'
  cases hw'
  exact ⟨hcl, hkT⟩

end
end LeanVM.Guest.B1
