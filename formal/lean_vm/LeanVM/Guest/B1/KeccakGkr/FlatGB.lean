/-
  LeanVM.Guest.B1.KeccakGkr.FlatGB

  `completeAt_flatG` within a bound (`CompleteAtB`): the function's frame, its buffers and its
  callees' bounds.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.FlatG
public import LeanVM.Guest.B1.KeccakGkr.FlatFB

/-!
# Callees reading earlier callees' buffers, within a bound

* `KidsGB fs cert κ ks Bs`: each entered call of `ks` is complete within its bound in `Bs` (in
  order), at every prefix of frame pointers (`CompleteAtFB`).
* `kidsGBound fs ks Bs`: the callees' words, an entered call's bound, a skipped call's frame.
* `kidsFromIn_of_kidsGB`: `kidsFromIn_of_kidsG` with the total at most `kidsGBound`.
* `completeAt_flatGB`: `completeAt_flatG` within `fs f + sizes.sum + NB`, the callees' words at most
  `NB` at every frame pointer.

The proofs are `kidsFromIn_of_kidsG`'s and `completeAt_flatG`'s with the bounds carried along.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- The entered calls are complete within their bounds `Bs` (in order), at every prefix of frame
pointers. -/
def KidsGB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) : List KidG → List ℕ → Prop
  | k :: ks, Bs => (k.taken = true → ∀ ps, CompleteAtFB fs cert κ k.f (fun p => k.Lin (ps ++ [p]))
      (k.args ps) (fun p => k.Out (ps ++ [p])) (Bs.headD 0)) ∧ KidsGB fs cert κ ks Bs.tail
  | [], _ => True

/-- The callees' words: an entered call's bound, a skipped call's frame. -/
def kidsGBound (fs : String → ℕ) : List KidG → List ℕ → ℕ
  | k :: ks, Bs => (if k.taken then Bs.headD 0 else fs k.f) + kidsGBound fs ks Bs.tail
  | [], _ => 0

/-- **`kidsFromIn_of_kidsG` within the callees' bounds** (`Bs`, an entered call's; a skipped call's
frame): the total `N` at most `kidsGBound fs ks Bs`. -/
theorem kidsFromIn_of_kidsGB (κ : ℕ) : ∀ (pre : List ℕ) (ks : List KidG) (Bs : List ℕ),
    KidsGB fs cert κ ks Bs →
    ∀ b : ℕ, ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)) (fps : List ℕ),
      N ≤ kidsGBound fs ks Bs ∧ fps.length = ks.length ∧ (∀ p ∈ fps, b ≤ p) ∧
      OutsOk (atAllG pre ks fps) outs ∧ Within L b N ∧ DisjL L ∧
      OutsIn (atAllG pre ks fps) outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop),
        CallsMatch σ cs (atAllG pre ks fps) outs → LowDef κ rd → MemL rd L →
        MemL rd (Kid.lins (atAllG pre ks fps)) → RegionsOk R Dacc (atAllG pre ks fps) outs →
        KidsFromIn coreProgram fs cert rd σ R Dacc cs b N
          (fun i => Dacc i ∨ outRegion (atAllG pre ks fps) outs i)
  | _, [], _, _, b => ⟨0, [], [], [], le_rfl, rfl, fun _ h => by simp at h, trivial, fun _ h => by simp at h,
      disj_nil, trivial, fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | pre, k :: ks, Bs, hok, b => by
    by_cases ht : k.taken = true
    · obtain ⟨n, Lown, rets, Lout, hnB, hout, hw, hd, hrel⟩ := hok.1 ht pre b
      obtain ⟨N, L, outs, fps, hNB, hlen, hge, ho, hW, hD, hI, hK⟩ :=
        kidsFromIn_of_kidsGB κ (pre ++ [b]) ks Bs.tail hok.2 (b + n)
      refine ⟨n + N, Lout ++ Lown ++ L, (rets, Lout) :: outs, b :: fps,
        by simp only [kidsGBound, ht, ↓reduceIte]; omega, by simp [hlen],
        fun p hp => ?_, ⟨fun _ => hout, ho⟩, ?_, disj_append hd hD hw hW le_rfl,
        ⟨fun _ q hq => by simp [hq], hI.mono fun q hq => by simp [hq]⟩, ?_⟩
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact le_rfl
        · have := hge p hp; omega
      · rw [within_append]
        exact ⟨hw.mono le_rfl (by omega), hW.mono (by omega) (by omega)⟩
      · intro rd σ cs R Dacc hc hlow hL hLin hRg
        match cs, hc with
        | c :: cs, ⟨hf, hct, hcar, hc⟩ =>
          obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
          simp only [atAllG, Kid.lins, List.flatMap_cons] at hLin
          obtain ⟨hLk, hLs⟩ := Main.memL_append.mp hLin
          obtain ⟨hR1, hR2⟩ := hRg
          obtain ⟨ha, hr⟩ := hcar ht
          refine ⟨n, N, RegionL (k.Lin (pre ++ [b])), RegionL Lout, rfl, hR1 ht, ?_, ?_⟩
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
            · simpa [hct, atAllG] using hR2
    · obtain ⟨N, L, outs, fps, hNB, hlen, hge, ho, hW, hD, hI, hK⟩ :=
        kidsFromIn_of_kidsGB κ (pre ++ [b]) ks Bs.tail hok.2 (b + fs k.f)
      refine ⟨fs k.f + N, L, ([], []) :: outs, b :: fps,
        by simp only [kidsGBound, ht, Bool.false_eq_true, ↓reduceIte]; omega, by simp [hlen],
        fun p hp => ?_,
        ⟨fun h => absurd h ht, ho⟩, hW.mono (by omega) (by omega), hD, ⟨fun h => absurd h ht, hI⟩,
        ?_⟩
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact le_rfl
        · have := hge p hp; omega
      intro rd σ cs R Dacc hc hlow hL hLin hRg
      match cs, hc with
      | c :: cs, ⟨hf, hct, _, hc⟩ =>
        simp only [atAllG, Kid.lins, List.flatMap_cons] at hLin
        refine ⟨fs k.f, N, fun _ => False, fun _ => False, rfl, fun _ h => h.elim, ?_, ?_⟩
        · have ht' : k.taken = false := by simpa using ht
          rw [hct]
          simp only [ht', Bool.false_eq_true, ↓reduceIte]
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

/-- **`completeAt_flatG` within `fs f + sizes.sum + NB` words**: the callees within `Bs`, their
words (`kidsGBound`) at most `NB` at every frame pointer. -/
theorem completeAt_flatGB {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (hnl : pre.all noLoadIte = true)
    (sizes : List ℕ) (own : ℕ → List ℕ → List (List E))
    (hown : ∀ fp fps, List.Forall₂ (fun c s => c.length ≤ s) (own fp fps) sizes)
    (kids : ℕ → List KidG) (Bs : List ℕ) (NB : ℕ) (hkc : ∀ fp, KidsGB fs cert κ (kids fp) Bs)
    (hkB : ∀ fp, kidsGBound fs (kids fp) Bs ≤ NB)
    (hσ : ∀ fp (fps : List ℕ) (outs : List (List E × Layout)), fps.length = (kids fp).length →
      (∀ p ∈ fps, fp + fs f + sizes.sum ≤ p) → OutsOk (atAllG [] (kids fp) fps) outs →
      ∀ rd, LowDef κ rd → MemL rd (bufL (fp + fs f) sizes (own fp fps)) → MemL rd Lin →
      MemL rd (takenOuts (atAllG [] (kids fp) fps) outs) →
      MemL rd (Kid.lins (atAllG [] (kids fp) fps)) ∧
      RegionsOk (fun i => RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp fps)) i)
        (fun _ => False) (atAllG [] (kids fp) fps) outs ∧
      ∃ σ : Val, fn.params.map σ = args ∧ (∀ s ∈ pre, DispOk σ s) ∧
        Stmt.HoldsList (fun _ _ _ => True) rd σ fn.body False (fun r => r = rets) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (addressOfIndex b)) ∧
        CallsMatch σ ((pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
          (atAllG [] (kids fp) fps) outs ∧
        ∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 =
            addressOfIndex i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp fps)) i ∨
            outRegion (atAllG [] (kids fp) fps) outs i)) :
    CompleteAtB fs cert κ f Lin args (Returns rets) (fs f + sizes.sum + NB) := by
  intro fp
  obtain ⟨N, L, outs, fps, hNB, hlen, hge, ho, hW, hD, hI, hK⟩ := kidsFromIn_of_kidsGB (fs := fs)
    (cert := cert) κ [] (kids fp) Bs (hkc fp) (fp + fs f + sizes.sum)
  have hdj := disj_append (bufL_disj _ _ _ (hown fp fps)) hD (bufL_within _ _ _ (hown fp fps)) hW
    le_rfl
  refine ⟨fs f + sizes.sum + N, bufL (fp + fs f) sizes (own fp fps) ++ L, rets, [], ⟨rfl, rfl⟩, ?_,
    by simpa using hdj, by have := hkB fp; omega, fun rd hlow hL => ?_⟩
  · simp only [List.nil_append, within_append]
    exact ⟨(bufL_within _ _ _ (hown fp fps)).mono (by omega) (by omega),
      hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hL
  obtain ⟨hLm, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hB, hLk⟩ := Main.memL_append.mp hLm
  have hto : MemL rd (takenOuts (atAllG [] (kids fp) fps) outs) :=
    fun q hq => hLk q (takenOuts_sub hI q hq)
  obtain ⟨hlins, hreg, σ, hp, hdo, hh, hsz, hbuf, hcm, hld⟩ :=
    hσ fp fps outs hlen hge ho rd hlow hB hLin hto
  have hw := walk_flat σ vs pre hst hdo
  rw [← hb] at hw
  obtain ⟨i1, i2, i3, i4, i5⟩ := flat_parts σ pre hst
  have hsat := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
  rw [hw] at hsat
  have hes : ∀ e ∈ pre.flatMap (flEvs σ), e.Holds rd σ := fun e he => (hsat.1 e he).1
  have hr : vs.map σ = rets := hsat.2
  have hal : allocs σ (pre.flatMap (flEvs σ)) = sizes := by rw [i2, hsz]
  have hown' : ∀ i, RegionL (bufL (fp + fs f) sizes (own fp fps)) i →
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i :=
    fun i hi => Or.inl (by rw [hal]; exact bufL_region _ _ _ (hown fp fps) i hi)
  have hk := hK rd σ (calls (pre.flatMap (flEvs σ))) (fun i => RegionL Lin i ∨
      ownData cert fp (fp + fs f) f (allocs σ (pre.flatMap (flEvs σ))) (pre.flatMap (flEvs σ)) i)
    (fun _ => False) (by rw [i4]; exact hcm) hlow hLk hlins
    (regionsOk_mono (fun i h => h.imp_right (hown' i)) hreg)
  have hb' : fp + fs f + sizes.sum = fp + fs f + (allocs σ (pre.flatMap (flEvs σ))).sum := by
    rw [hal]
  rw [hb'] at hk
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := RegionL [])
    (Dk := fun i => False ∨ outRegion (atAllG [] (kids fp) fps) outs i) (N := N) (fp := fp)
    coreProgram_wf hf (Or.inl hl) hp hw hr hes (by rw [hal, i1]; exact hbuf)
    (by rw [i3, haddrs]; simp) hk (fun A hA => ?_) (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rw [hal] at h
    exact h
  · rw [i5, flatMap_loadsEv σ pre hnl] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, h | h | h⟩ := hld q hq
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩
    · exact ⟨i, hi, Or.inl (hown' i h)⟩
    · exact ⟨i, hi, Or.inr (Or.inr (Or.inr h))⟩

end
end LeanVM.Guest.B1
