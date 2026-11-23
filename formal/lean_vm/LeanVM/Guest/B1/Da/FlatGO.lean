/-
  LeanVM.Guest.B1.Da.FlatGO

  `completeAt_flatGB` returning its own buffers and its callees' returned buffers.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.FlatGB
public import LeanVM.Guest.B1.Da.FlatOut

/-!
# Placed callees, returned buffers

`da_weights` holds pointers into its callees' frames (`completeAt_flatGB`: its own buffers'
words depend on the callees' frame pointers), and returns its buffer and theirs to `da_verify`.

* `kidsFromIn_of_kidsGBP`: `kidsFromIn_of_kidsGB` with the callees' layout a permutation of their
  returned buffers (`takenOuts`) and the rest.
* `completeAt_flatGOutB`: `completeAt_flatGB` returning words of the frame pointers and, as its
  layout, its own buffers and its callees' returned buffers (`Res (rets fp fps) (bufL … ++
  takenOuts …)`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem takenOuts_eq_outsL : ∀ (ks : List Kid) (outs : List (List E × Layout)),
    takenOuts ks outs = outsL ks outs
  | _ :: ks, _ :: os => by simp only [takenOuts, outsL, takenOuts_eq_outsL ks os]
  | [], _ => by simp [takenOuts, outsL]
  | _ :: _, [] => by simp [takenOuts, outsL]

/-- **`kidsFromIn_of_kidsGB`, the callees' layout a permutation of their returned buffers and the
rest.** -/
theorem kidsFromIn_of_kidsGBP (κ : ℕ) : ∀ (pre : List ℕ) (ks : List KidG) (Bs : List ℕ),
    KidsGB fs cert κ ks Bs →
    ∀ b : ℕ, ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)) (fps : List ℕ),
      N ≤ kidsGBound fs ks Bs ∧ fps.length = ks.length ∧ (∀ p ∈ fps, b ≤ p) ∧
      OutsOk (atAllG pre ks fps) outs ∧ Within L b N ∧ DisjL L ∧
      OutsIn (atAllG pre ks fps) outs L ∧ (∃ Lw, L.Perm (takenOuts (atAllG pre ks fps) outs ++ Lw)) ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop),
        CallsMatch σ cs (atAllG pre ks fps) outs → LowDef κ rd → MemL rd L →
        MemL rd (Kid.lins (atAllG pre ks fps)) → RegionsOk R Dacc (atAllG pre ks fps) outs →
        KidsFromIn coreProgram fs cert rd σ R Dacc cs b N
          (fun i => Dacc i ∨ outRegion (atAllG pre ks fps) outs i)
  | _, [], _, _, b => ⟨0, [], [], [], le_rfl, rfl, fun _ h => by simp at h, trivial, fun _ h => by simp at h,
      disj_nil, trivial, ⟨[], by simp [atAllG, takenOuts]⟩, fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | pre, k :: ks, Bs, hok, b => by
    by_cases ht : k.taken = true
    · obtain ⟨n, Lown, rets, Lout, hnB, hout, hw, hd, hrel⟩ := hok.1 ht pre b
      obtain ⟨N, L, outs, fps, hNB, hlen, hge, ho, hW, hD, hI, ⟨Lw, hP⟩, hK⟩ :=
        kidsFromIn_of_kidsGBP κ (pre ++ [b]) ks Bs.tail hok.2 (b + n)
      refine ⟨n + N, Lout ++ Lown ++ L, (rets, Lout) :: outs, b :: fps,
        by simp only [kidsGBound, ht, ↓reduceIte]; omega, by simp [hlen],
        fun p hp => ?_, ⟨fun _ => hout, ho⟩, ?_, disj_append hd hD hw hW le_rfl,
        ⟨fun _ q hq => by simp [hq], hI.mono fun q hq => by simp [hq]⟩, ⟨Lown ++ Lw, ?_⟩, ?_⟩
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact le_rfl
        · have := hge p hp; omega
      · rw [within_append]
        exact ⟨hw.mono le_rfl (by omega), hW.mono (by omega) (by omega)⟩
      · simp only [atAllG, takenOuts, ht, ↓reduceIte, List.append_assoc]
        refine List.Perm.append_left Lout ?_
        exact (List.Perm.append_left Lown hP).trans (by
          rw [← List.append_assoc, ← List.append_assoc]
          exact List.Perm.append_right Lw List.perm_append_comm)
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
    · obtain ⟨N, L, outs, fps, hNB, hlen, hge, ho, hW, hD, hI, ⟨Lw, hP⟩, hK⟩ :=
        kidsFromIn_of_kidsGBP κ (pre ++ [b]) ks Bs.tail hok.2 (b + fs (tailKey k.f))
      refine ⟨fs (tailKey k.f) + N, L, ([], []) :: outs, b :: fps,
        by simp only [kidsGBound, ht, Bool.false_eq_true, ↓reduceIte]; omega, by simp [hlen],
        fun p hp => ?_,
        ⟨fun h => absurd h ht, ho⟩, hW.mono (by omega) (by omega), hD, ⟨fun h => absurd h ht, hI⟩,
        ⟨Lw, by simpa [atAllG, takenOuts, ht] using hP⟩, ?_⟩
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact le_rfl
        · have := hge p hp; omega
      intro rd σ cs R Dacc hc hlow hL hLin hRg
      match cs, hc with
      | c :: cs, ⟨hf, hct, _, hc⟩ =>
        simp only [atAllG, Kid.lins, List.flatMap_cons] at hLin
        refine ⟨fs (tailKey k.f), N, fun _ => False, fun _ => False, rfl, fun _ h => h.elim, ?_, ?_⟩
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

/-- **`completeAt_flatGB` returning its buffers**: its words `rets fp fps` and, as its layout, its
own buffers and its callees' returned buffers. -/
theorem completeAt_flatGOutB {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args : List E)
    (rets : ℕ → List ℕ → List E) (Res : List E → Layout → Prop)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (hnl : pre.all noLoadIte = true)
    (sizes : List ℕ) (own : ℕ → List ℕ → List (List E))
    (hown : ∀ fp fps, List.Forall₂ (fun c s => c.length ≤ s) (own fp fps) sizes)
    (kids : ℕ → List KidG) (Bs : List ℕ) (NB : ℕ) (hkc : ∀ fp, KidsGB fs cert κ (kids fp) Bs)
    (hkB : ∀ fp, kidsGBound fs (kids fp) Bs ≤ NB)
    (hout : ∀ fp (fps : List ℕ) (outs : List (List E × Layout)), fps.length = (kids fp).length →
      OutsOk (atAllG [] (kids fp) fps) outs →
      Res (rets fp fps) (bufL (fp + fs f) sizes (own fp fps) ++ takenOuts (atAllG [] (kids fp) fps) outs))
    (hσ : ∀ fp (fps : List ℕ) (outs : List (List E × Layout)), fps.length = (kids fp).length →
      (∀ p ∈ fps, fp + fs f + sizes.sum ≤ p) → OutsOk (atAllG [] (kids fp) fps) outs →
      ∀ rd, LowDef κ rd → MemL rd (bufL (fp + fs f) sizes (own fp fps)) → MemL rd Lin →
      MemL rd (takenOuts (atAllG [] (kids fp) fps) outs) →
      MemL rd (Kid.lins (atAllG [] (kids fp) fps)) ∧
      RegionsOk (fun i => RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp fps)) i)
        (fun _ => False) (atAllG [] (kids fp) fps) outs ∧
      ∃ σ : Val, fn.params.map σ = args ∧ (∀ s ∈ pre, DispOk σ s) ∧
        Stmt.HoldsList (fun _ _ _ => True) rd σ fn.body False (fun r => r = rets fp fps) ∧
        (pre.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) = sizes ∧
        ((pre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases (fp + fs f) sizes).map (fun b => ofK (addressOfIndex b)) ∧
        CallsMatch σ ((pre.filterMap (Stmt.callSF σ)).map (Main.mkCall σ))
          (atAllG [] (kids fp) fps) outs ∧
        ∀ q ∈ pre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * addressOfIndex q.2 =
            addressOfIndex i ∧
          (RegionL Lin i ∨ RegionL (bufL (fp + fs f) sizes (own fp fps)) i ∨
            outRegion (atAllG [] (kids fp) fps) outs i)) :
    CompleteAtB fs cert κ f Lin args Res (fs f + sizes.sum + NB) := by
  intro fp
  obtain ⟨N, L, outs, fps, hNB, hlen, hge, ho, hW, hD, hI, ⟨Lw, hP⟩, hK⟩ := kidsFromIn_of_kidsGBP
    (fs := fs) (cert := cert) κ [] (kids fp) Bs (hkc fp) (fp + fs f + sizes.sum)
  set B := bufL (fp + fs f) sizes (own fp fps) with hBdef
  set T := takenOuts (atAllG [] (kids fp) fps) outs with hTdef
  have hdj := disj_append (bufL_disj _ _ _ (hown fp fps)) hD (bufL_within _ _ _ (hown fp fps)) hW
    le_rfl
  have hPf : (B ++ L).Perm (B ++ T ++ Lw) := by
    rw [List.append_assoc]; exact hP.append_left _
  refine ⟨fs f + sizes.sum + N, Lw, rets fp fps, B ++ T, hout fp fps outs hlen ho, ?_,
    disjL_perm hPf hdj, by have := hkB fp; omega, fun rd hlow hL => ?_⟩
  · refine within_perm hPf ?_
    rw [within_append]
    exact ⟨(bufL_within _ _ _ (hown fp fps)).mono (by omega) (by omega),
      hW.mono (by omega) (by omega)⟩
  obtain ⟨hLm, hLin⟩ := Main.memL_append.mp hL
  obtain ⟨hB, hLk⟩ := Main.memL_append.mp (memL_perm hPf.symm hLm)
  have hto : MemL rd T := fun q hq => hLk q (takenOuts_sub hI q hq)
  obtain ⟨hlins, hreg, σ, hp, hdo, hh, hsz, hbuf, hcm, hld⟩ :=
    hσ fp fps outs hlen hge ho rd hlow hB hLin hto
  have hw := walk_flat σ vs pre hst hdo
  rw [← hb] at hw
  obtain ⟨i1, i2, i3, i4, i5⟩ := flat_parts σ pre hst
  have hsat := walk_sat (P := coreProgram) fn.body (coreProgram_wf fn (List.mem_of_find?_eq_some hf)) hh
  rw [hw] at hsat
  have hes : ∀ e ∈ pre.flatMap (flEvs σ), e.Holds rd σ := fun e he => (hsat.1 e he).1
  have hr : vs.map σ = rets fp fps := hsat.2
  have hal : allocs σ (pre.flatMap (flEvs σ)) = sizes := by rw [i2, hsz]
  have hown' : ∀ i, RegionL B i →
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
    (D := RegionL (B ++ T))
    (Dk := fun i => False ∨ outRegion (atAllG [] (kids fp) fps) outs i) (N := N) (fp := fp)
    coreProgram_wf hf (Or.inl hl) hp hw hr hes (by rw [hal, i1]; exact hbuf)
    (by rw [i3, haddrs]; simp) hk (fun A hA => ?_) (fun i hi => ?_)
  · rw [hal] at h
    exact h
  · rw [i5, flatMap_loadsEv σ pre hnl] at hA
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
    obtain ⟨i, hi, h | h | h⟩ := hld q hq
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩
    · exact ⟨i, hi, Or.inl (hown' i h)⟩
    · exact ⟨i, hi, Or.inr (Or.inr (Or.inr h))⟩
  · obtain ⟨q, hq, h1, h2⟩ := hi
    rcases List.mem_append.mp hq with hq | hq
    · exact Or.inl (hown' i ⟨q, hq, h1, h2⟩)
    · rw [hTdef, takenOuts_eq_outsL] at hq
      exact Or.inr (Or.inr (outRegion_of_outsL ⟨q, hq, h1, h2⟩))

end
end LeanVM.Guest.B1
