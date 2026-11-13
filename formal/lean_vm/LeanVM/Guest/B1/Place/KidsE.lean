/-
  LeanVM.Guest.B1.Place.KidsE

  Callees complete by trees of exactly given words, placed in sequence: their total is the sum.
-/

module

public import LeanVM.Guest.B1.Place.HelperAt

/-!
# Exact callees in sequence

`kidsFromIn_of_kidsE`: `kidsFromIn_of_kidsD` for callees each `CompleteAtE` at `ns k` words: the
callees' total is `kidsN fs ns ks` (an entered callee's `ns k`, a skipped one's frame).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- The callees' total: an entered callee's `ns k` words, a skipped one's frame. -/
def kidsN (fs : String → ℕ) (ns : Kid → ℕ) (ks : List Kid) : ℕ :=
  (ks.map fun k ↦ if k.taken then ns k else fs k.f).sum

/-- **Callees complete by trees of exactly `ns k` words, placed in sequence from `b`.** -/
theorem kidsFromIn_of_kidsE (κ : ℕ) (ns : Kid → ℕ) : ∀ (ks : List Kid),
    (∀ k ∈ ks, k.taken = true → CompleteAtE fs cert κ k.f k.Lin k.args k.Out (ns k)) → ∀ b : ℕ,
    ∃ (L : Layout) (outs : List (List E × Layout)), OutsOk ks outs ∧ Within L b (kidsN fs ns ks) ∧
      DisjL L ∧ OutsIn ks outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop), CallsMatch σ cs ks outs →
        LowDef κ rd → MemL rd L → MemL rd (Kid.lins ks) → RegionsOk R Dacc ks outs →
        KidsFromIn coreProgram fs cert rd σ R Dacc cs b (kidsN fs ns ks)
          (fun i => Dacc i ∨ outRegion ks outs i)
  | [], _, b => ⟨[], [], trivial, fun _ h => by simp at h, disj_nil, trivial,
      fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | k :: ks, hok, b => by
    have hN : kidsN fs ns (k :: ks) = (if k.taken then ns k else fs k.f) + kidsN fs ns ks := by
      simp [kidsN]
    by_cases ht : k.taken = true
    · obtain ⟨Lown, rets, Lout, hout, hw, hd, hrel⟩ := hok k (by simp) ht b
      obtain ⟨L, outs, ho, hW, hD, hI, hK⟩ := kidsFromIn_of_kidsE κ ns ks
        (fun k' hk' => hok k' (by simp [hk'])) (b + ns k)
      rw [hN]
      simp only [ht, ↓reduceIte]
      refine ⟨Lout ++ Lown ++ L, (rets, Lout) :: outs, ⟨fun _ => hout, ho⟩, ?_,
        disj_append hd hD hw hW le_rfl,
        ⟨fun _ q hq => by simp [hq], hI.mono fun q hq => by simp [hq]⟩, ?_⟩
      · rw [within_append]
        exact ⟨hw.mono le_rfl (by omega), hW.mono (by omega) (by omega)⟩
      · intro rd σ cs R Dacc hc hlow hL hLin hRg
        match cs, hc with
        | c :: cs, ⟨hf, hct, hcar, hc⟩ =>
          obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
          simp only [Kid.lins, List.flatMap_cons] at hLin
          obtain ⟨hLk, hLs⟩ := Main.memL_append.mp hLin
          obtain ⟨hR1, hR2⟩ := hRg
          obtain ⟨ha, hr⟩ := hcar ht
          refine ⟨ns k, kidsN fs ns ks, RegionL k.Lin, RegionL Lout, rfl, hR1 ht, ?_, ?_⟩
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
    · obtain ⟨L, outs, ho, hW, hD, hI, hK⟩ := kidsFromIn_of_kidsE κ ns ks
        (fun k' hk' => hok k' (by simp [hk'])) (b + fs k.f)
      rw [hN]
      simp only [ht, Bool.false_eq_true, ↓reduceIte]
      refine ⟨L, ([], []) :: outs, ⟨fun h => absurd h ht, ho⟩,
        hW.mono (by omega) (by omega), hD, ⟨fun h => absurd h ht, hI⟩, ?_⟩
      intro rd σ cs R Dacc hc hlow hL hLin hRg
      match cs, hc with
      | c :: cs, ⟨hf, hct, _, hc⟩ =>
        simp only [Kid.lins, List.flatMap_cons] at hLin
        refine ⟨fs k.f, kidsN fs ns ks, fun _ => False, fun _ => False, rfl, fun _ h => h.elim, ?_,
          ?_⟩
        · have ht' : k.taken = false := by simpa using ht
          rw [hct, ht']
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

end
end LeanVM.Guest.B1
