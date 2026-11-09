/-
  LeanVM.Guest.B1.KeccakGkr.FlatG

  Flat bodies placed when a callee's caller's words depend on the frame pointers of the callees
  before it (and its own), and the caller's own words on all of them.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.FlatF

/-!
# Callees reading earlier callees' buffers

`verify_keccak`'s layers each read the buffers the previous layer returned, which sit in that
layer's frame; and `verify_keccak`'s own claim records hold pointers into them. So a callee's
caller's words depend on the frame pointers of the callees up to it (`KidG.Lin ps`, `ps` the
frame pointers so far, its own last), and the caller's own words on all of them. A callee's
arguments may hold pointers into earlier callees' buffers too (`KidG.args ps`, `ps` the frame
pointers before it).

* `atAllG pre ks fps`: the calls placed at `fps`, each reading its words at the prefix of frame
  pointers so far (after `pre`).
* `kidsFromIn_of_kidsG`: `kidsFromIn_of_kidsF` for them.
* `completeAt_flatG`: a flat function is complete, placed, its own buffers' words depending on the
  callees' frame pointers, its callees reading the caller's words, its own buffers and the earlier
  callees' results, its statements holding with any calls' relation (the callees are placed apart).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- A call whose arguments depend on the frame pointers of the calls before it, and whose caller's
words on those up to it. -/
structure KidG where
  f : String
  taken : Bool
  args : List ℕ → List E
  Lin : List ℕ → Layout
  Out : List ℕ → List E → Layout → Prop

/-- The calls placed at `fps`, after the frame pointers `pre`. -/
def atAllG : List ℕ → List KidG → List ℕ → List Kid
  | pre, k :: ks, p :: ps =>
    ⟨k.f, k.taken, k.args pre, k.Lin (pre ++ [p]), k.Out (pre ++ [p])⟩ :: atAllG (pre ++ [p]) ks ps
  | _, _, _ => []

/-- The buffers the entered calls return. -/
def takenOuts : List Kid → List (List E × Layout) → Layout
  | k :: ks, o :: os => (if k.taken then o.2 else []) ++ takenOuts ks os
  | _, _ => []

theorem takenOuts_sub : ∀ {ks : List Kid} {outs : List (List E × Layout)} {L : Layout},
    OutsIn ks outs L → ∀ q ∈ takenOuts ks outs, q ∈ L
  | k :: ks, o :: os, L, ⟨h, hs⟩, q, hq => by
    simp only [takenOuts, List.mem_append] at hq
    rcases hq with hq | hq
    · split at hq
      · rename_i ht; exact h ht q hq
      · simp at hq
    · exact takenOuts_sub hs q hq
  | [], _, _, _, q, hq => by simp [takenOuts] at hq
  | _ :: _, [], _, _, q, hq => by simp [takenOuts] at hq

theorem regionsOk_mono {R R' : ℕ → Prop} (hR : ∀ i, R i → R' i) :
    ∀ {Dacc : ℕ → Prop} {ks : List Kid} {outs : List (List E × Layout)},
      RegionsOk R Dacc ks outs → RegionsOk R' Dacc ks outs
  | _, _ :: _, _ :: _, ⟨h, hs⟩ => ⟨fun ht i hi => (h ht i hi).imp_left (hR i), regionsOk_mono hR hs⟩
  | _, [], _, _ => trivial
  | _, _ :: _, [], _ => trivial

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`kidsFromIn_of_kidsF` for calls reading at the frame pointers so far.** -/
theorem kidsFromIn_of_kidsG (κ : ℕ) : ∀ (pre : List ℕ) (ks : List KidG),
    (∀ k ∈ ks, k.taken = true → ∀ ps,
      CompleteAtF fs cert κ k.f (fun p => k.Lin (ps ++ [p])) (k.args ps)
        (fun p => k.Out (ps ++ [p]))) →
    ∀ b : ℕ, ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)) (fps : List ℕ),
      fps.length = ks.length ∧ (∀ p ∈ fps, b ≤ p) ∧
      OutsOk (atAllG pre ks fps) outs ∧ Within L b N ∧ DisjL L ∧
      OutsIn (atAllG pre ks fps) outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop),
        CallsMatch σ cs (atAllG pre ks fps) outs → LowDef κ rd → MemL rd L →
        MemL rd (Kid.lins (atAllG pre ks fps)) → RegionsOk R Dacc (atAllG pre ks fps) outs →
        KidsFromIn coreProgram fs cert rd σ R Dacc cs b N
          (fun i => Dacc i ∨ outRegion (atAllG pre ks fps) outs i)
  | _, [], _, b => ⟨0, [], [], [], rfl, fun _ h => by simp at h, trivial, fun _ h => by simp at h,
      disj_nil, trivial, fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | pre, k :: ks, hok, b => by
    by_cases ht : k.taken = true
    · obtain ⟨n, Lown, rets, Lout, hout, hw, hd, hrel⟩ := hok k (by simp) ht pre b
      obtain ⟨N, L, outs, fps, hlen, hge, ho, hW, hD, hI, hK⟩ := kidsFromIn_of_kidsG κ (pre ++ [b]) ks
        (fun k' hk' => hok k' (by simp [hk'])) (b + n)
      refine ⟨n + N, Lout ++ Lown ++ L, (rets, Lout) :: outs, b :: fps, by simp [hlen],
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
    · obtain ⟨N, L, outs, fps, hlen, hge, ho, hW, hD, hI, hK⟩ := kidsFromIn_of_kidsG κ (pre ++ [b]) ks
        (fun k' hk' => hok k' (by simp [hk'])) (b + fs k.f)
      refine ⟨fs k.f + N, L, ([], []) :: outs, b :: fps, by simp [hlen], fun p hp => ?_,
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

/-- **A flat function is complete, placed, its callees reading earlier callees' results.** -/
theorem completeAt_flatG {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (κ : ℕ) (Lin : Layout) (args rets : List E)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hst : pre.all Stmt.flat = true) (haddrs : pre.filterMap Main.Stmt.addrS = [])
    (hnl : pre.all noLoadIte = true)
    (sizes : List ℕ) (own : ℕ → List ℕ → List (List E))
    (hown : ∀ fp fps, List.Forall₂ (fun c s => c.length ≤ s) (own fp fps) sizes)
    (kids : ℕ → List KidG)
    (hkc : ∀ fp, ∀ k ∈ kids fp, k.taken = true → ∀ ps,
      CompleteAtF fs cert κ k.f (fun p => k.Lin (ps ++ [p])) (k.args ps)
        (fun p => k.Out (ps ++ [p])))
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
    CompleteAtD fs cert κ f Lin args (Returns rets) := by
  intro fp
  obtain ⟨N, L, outs, fps, hlen, hge, ho, hW, hD, hI, hK⟩ := kidsFromIn_of_kidsG (fs := fs)
    (cert := cert) κ [] (kids fp) (hkc fp) (fp + fs f + sizes.sum)
  have hdj := disj_append (bufL_disj _ _ _ (hown fp fps)) hD (bufL_within _ _ _ (hown fp fps)) hW
    le_rfl
  refine ⟨fs f + sizes.sum + N, bufL (fp + fs f) sizes (own fp fps) ++ L, rets, [], ⟨rfl, rfl⟩, ?_,
    by simpa using hdj, fun rd hlow hL => ?_⟩
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
