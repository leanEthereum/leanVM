/-
  LeanVM.Guest.B1.Terminal.KidsDepB

  `KidsDep`'s lifts within a bound (`CompleteAtB`): dependent callees, each within its bound, and a
  flat function with them within its frame, its buffers and its callees' bounds.
-/

module

public import LeanVM.Guest.B1.Terminal.KidsDep

/-!
# Dependent callees, placed, within a bound

`KidsDepB fs cert κ ks Bs`: callee `j` (a function of the results before it, `KidD`) has the bound
`Bs[j]`, on every result before it: entered, it is `CompleteAtB` within `Bs[j]`; skipped, its frame
`fs` is at most `Bs[j]`. The callees then take at most `Bs.sum` words (`kidsFromIn_of_depB`), and a
flat function with them at most `fs f + sizes.sum + Bs.sum` (`completeAt_flatDepB`,
`completeAt_flatDepRB`: `completeAt_flatDep`, `completeAt_flatDepR` within that bound).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- **The dependent callees within their bounds**: callee `j`, on every result before it, entered
within `Bs[j]` words (`CompleteAtB`), skipped with its frame at most `Bs[j]`; one bound per
callee. -/
def KidsDepB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) : List KidD → List ℕ → Prop
  | k :: ks, b :: Bs => (∀ pv, ((k pv).taken = true →
        CompleteAtB fs cert κ (k pv).f (k pv).Lin (k pv).args (k pv).Out b) ∧
      ((k pv).taken = false → fs (k pv).f ≤ b)) ∧ KidsDepB fs cert κ ks Bs
  | [], [] => True
  | _, _ => False

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem KidsDepB.append {κ : ℕ} : ∀ {ks ks' : List KidD} {Bs Bs' : List ℕ},
    KidsDepB fs cert κ ks Bs → KidsDepB fs cert κ ks' Bs' → KidsDepB fs cert κ (ks ++ ks') (Bs ++ Bs')
  | [], _, [], _, _, h' => h'
  | _ :: _, _, _ :: _, _, ⟨h, hs⟩, h' => ⟨h, KidsDepB.append hs h'⟩
  | [], _, _ :: _, _, h, _ => by simp [KidsDepB] at h
  | _ :: _, _, [], _, h, _ => by simp [KidsDepB] at h

/-- **Callees with one bound `b`.** -/
theorem kidsDepB_replicate {κ : ℕ} {b : ℕ} : ∀ {ks : List KidD},
    (∀ k ∈ ks, ∀ pv, ((k pv).taken = true →
        CompleteAtB fs cert κ (k pv).f (k pv).Lin (k pv).args (k pv).Out b) ∧
      ((k pv).taken = false → fs (k pv).f ≤ b)) →
    KidsDepB fs cert κ ks (List.replicate ks.length b)
  | [], _ => trivial
  | k :: _, h => ⟨h k List.mem_cons_self, kidsDepB_replicate fun k' hk' => h k' (List.mem_cons_of_mem _ hk')⟩

theorem KidsDepB.length {κ : ℕ} : ∀ {ks : List KidD} {Bs : List ℕ}, KidsDepB fs cert κ ks Bs →
    ks.length = Bs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, hs⟩ => by simp [hs.length]
  | [], _ :: _, h => by simp [KidsDepB] at h
  | _ :: _, [], h => by simp [KidsDepB] at h

/-- The dependent callees, as `kidsFromIn_of_dep`'s hypothesis. -/
theorem KidsDepB.toD {κ : ℕ} : ∀ {ks : List KidD} {Bs : List ℕ}, KidsDepB fs cert κ ks Bs →
    ∀ k ∈ ks, ∀ pv, (k pv).taken = true →
      CompleteAtD fs cert κ (k pv).f (k pv).Lin (k pv).args (k pv).Out
  | [], _, _, _, h, _, _ => absurd h (by simp)
  | _ :: _, [], h, _, _, _, _ => by simp [KidsDepB] at h
  | k :: ks, _ :: _, ⟨h, hs⟩, k', hk', pv, ht => by
    rcases List.mem_cons.mp hk' with rfl | hk'
    · exact ((h pv).1 ht).toCompleteAtD
    · exact hs.toD k' hk' pv ht

/-- **Dependent callees at their running offsets, within their bounds**: `kidsFromIn_of_dep`
with the callees' words at most `Bs.sum`. -/
theorem kidsFromIn_of_depB (κ : ℕ) : ∀ (ks : List KidD) (Bs : List ℕ) (prev : List (List E × Layout)),
    KidsDepB fs cert κ ks Bs → ∀ b : ℕ,
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), N ≤ Bs.sum ∧
      outs.length = ks.length ∧
      OutsOk (kidsAt ks prev outs) outs ∧ Within L b N ∧ DisjL L ∧
      OutsIn (kidsAt ks prev outs) outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop),
        CallsMatch σ cs (kidsAt ks prev outs) outs → LowDef κ rd → MemL rd L →
        MemL rd (Kid.lins (kidsAt ks prev outs)) → RegionsOk R Dacc (kidsAt ks prev outs) outs →
        KidsFromIn coreProgram fs cert rd σ R Dacc cs b N
          (fun i => Dacc i ∨ outRegion (kidsAt ks prev outs) outs i)
  | [], [], _, _, b => ⟨0, [], [], le_rfl, rfl, trivial, fun _ h => by simp at h, disj_nil, trivial,
      fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | [], _ :: _, _, h, _ => by simp [KidsDepB] at h
  | _ :: _, [], _, h, _ => by simp [KidsDepB] at h
  | kf :: ks, bk :: Bs, prev, ⟨hok, hoks⟩, b => by
    by_cases ht : (kf prev).taken = true
    · obtain ⟨n, Lown, rets, Lout, hout, hw, hd, hnb, hrel⟩ := (hok prev).1 ht b
      obtain ⟨N, L, outs, hNb, hlen, ho, hW, hD, hI, hK⟩ :=
        kidsFromIn_of_depB κ ks Bs (prev ++ [(rets, Lout)]) hoks (b + n)
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
            exact hrel rd hlow (Main.memL_append.mpr ⟨hL1, hLk⟩)
          · refine kidsFromIn_dend cs _ _ _ ?_ (hK rd σ cs R _ hc hlow hL2 hLs ?_)
            · intro i hi
              rcases hi with hi | ⟨_, hi⟩ | hi
              · exact Or.inl (Or.inl hi)
              · exact Or.inl (Or.inr ⟨by rw [hct]; exact ht, hi⟩)
              · exact Or.inr hi
            · simpa [hct] using hR2
    · have ht' : (kf prev).taken = false := by simpa using ht
      have hfb := (hok prev).2 ht'
      obtain ⟨N, L, outs, hNb, hlen, ho, hW, hD, hI, hK⟩ :=
        kidsFromIn_of_depB κ ks Bs (prev ++ [([], [])]) hoks (b + fs (kf prev).f)
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
        · refine kidsFromIn_dend cs _ _ _ ?_ (hK rd σ cs R _ hc hlow hL (Main.memL_append.mp hLin).2 ?_)
          · intro i hi
            rcases hi with hi | ⟨h, _⟩ | hi
            · exact Or.inl (Or.inl hi)
            · exact absurd h ht
            · exact Or.inr hi
          · have := hRg.2
            simp only [hct, ht, Bool.false_eq_true, false_and, or_false] at this ⊢
            exact this

/-- **`completeAt_flatDepR` within a bound**: returning no buffer, within its frame, its
`HeapBuf`s (`sizes`) and its callees' bounds `Bs` (`KidsDepB`): `fs f + sizes.sum + Bs.sum`. -/
theorem completeAt_flatDepRB {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (hni : pre.all notIteB = true)
    (sizes : List ℕ) (own : ℕ → List (List E))
    (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes) (kids : ℕ → List KidD)
    (Bs : List ℕ) (hkc : ∀ fp, KidsDepB fs cert κ (kids fp) Bs)
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
    CompleteAtB fs cert κ f Lin args (Returns rets) (fs f + sizes.sum + Bs.sum) := by
  intro fp
  obtain ⟨N, L, outs, hNb, hlen, ho, hW, hD, hI, hK⟩ := kidsFromIn_of_depB (fs := fs) (cert := cert) κ
    (kids fp) Bs [] (hkc fp) (fp + fs f + sizes.sum)
  refine ⟨fs f + sizes.sum + N, bufL (fp + fs f) sizes (own fp) ++ L, rets, [], ⟨rfl, rfl⟩, ?_,
    by simpa using disj_append (bufL_disj _ _ _ (hown fp)) hD (bufL_within _ _ _ (hown fp)) hW le_rfl,
    by omega, fun rd hlow hL => ?_⟩
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
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun i => False ∨ outRegion (kidsAt (kids fp) [] outs) outs i) (N := N)
    (fp := fp) coreProgram_wf hf (Or.inl hl) hp hw hr hes (by rw [hal, i1]; exact hbuf)
    (by rw [i3, haddrs]; simp) hk (fun A hA => ?_) (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rw [hal] at h
    exact h
  · rw [i5] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, h | h | h⟩ := hld q (filterMap_of_loadsEv hni hq)
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩
    · exact ⟨i, hi, Or.inl (hown' i h)⟩
    · exact ⟨i, hi, Or.inr (Or.inr (Or.inr h))⟩

end
end LeanVM.Guest.B1
