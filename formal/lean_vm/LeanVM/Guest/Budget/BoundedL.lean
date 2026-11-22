/-
  LeanVM.Guest.Budget.BoundedL

  A loop helper complete from an iteration on by a tree satisfying a predicate of the memory (`CompleteAtLR`).
-/

module

public import LeanVM.Guest.Budget.BoundedR

/-!
# Loops by trees of a predicate of the memory

`CompleteAtLR`: `CompleteAtL` by a tree satisfying a predicate of the memory; `CompleteAtLR.mono`, `toDTBR` (a loop
entered fresh), `completeAtLR_tail` (the rest of a loop).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- **`CompleteAtL` by a tree satisfying a predicate of the memory.** -/
def CompleteAtLR (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String) (Lin : Layout)
    (args : List E) (Out : List E → Layout → Prop) (T : Reader → Tree → Prop) (Bd : ℕ → Prop) : Prop :=
  ∃ B, ∀ fp c, fp + B ≤ c → ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout),
    Bd (B + n) ∧ Out rets Lout ∧ Within (Lout ++ Lown) c n ∧ DisjL (Lout ++ Lown) ∧
    ∀ rd, LowDef k rd → MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInCT coreProgram fs cert rd (RegionL Lin) (RegionL Lout) fp c B n f args rets (T rd)

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem CompleteAtLR.mono {k : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {T T' : Reader → Tree → Prop} {Bd Bd' : ℕ → Prop}
    (h : CompleteAtLR fs cert k f Lin args Out T Bd) (hBd : ∀ x, Bd x → Bd' x)
    (hT : ∀ rd t, T rd t → T' rd t) : CompleteAtLR fs cert k f Lin args Out T' Bd' :=
  let ⟨B, hB⟩ := h
  ⟨B, fun fp c hc =>
    let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := hB fp c hc
    ⟨n, Lown, rets, Lout, hBd _ hn, ho, hw, hd, fun rd hl hm =>
      let ⟨t, ht, hTt⟩ := hr rd hl hm
      ⟨t, ht, hT rd t hTt⟩⟩⟩

/-- **A loop entered fresh, within `B` words.** -/
theorem CompleteAtLR.toDTBR {k : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {T : Reader → Tree → Prop} {B : ℕ}
    (h : CompleteAtLR fs cert k f Lin args Out T (· ≤ B)) : CompleteAtDTBR fs cert k f Lin args Out T B :=
  fun fp =>
    let ⟨Bl, hB⟩ := h
    let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := hB fp (fp + Bl) le_rfl
    ⟨Bl + n, Lown, rets, Lout, hn, ho, hw.mono (by omega) (by omega), hd,
      fun rd hl hm => (hr rd hl hm).relAtInT⟩

/-- **The rest of a loop**: `completeAtL_tail`, the trees satisfying a predicate of the memory. -/
theorem completeAtLR_tail {k : ℕ} {f g : String} {Lin : Layout} {args : List E} {T : Reader → Tree → Prop}
    {Bd : ℕ → Prop} {last : Prop} [Decidable last]
    (h : ¬ last → CompleteAtLR fs cert k f Lin args (Returns []) T Bd) :
    ∃ Bt, ∀ fp c, fp + Bt ≤ c → ∃ (nt : ℕ) (Lt : Layout),
      (last → Bt = fs g ∧ nt = 0) ∧ (¬ last → Bd (Bt + nt)) ∧ Within Lt c nt ∧ DisjL Lt ∧
      ∀ rd, LowDef k rd → MemL rd (Lt ++ Lin) →
        if decide (¬ last) = true then
          RelAtInCT coreProgram fs cert rd (RegionL Lin) (RegionL []) fp c Bt nt f args [] (T rd)
        else Bt = fs g ∧ nt = 0 := by
  by_cases hl : last
  · exact ⟨fs g, fun fp c _ => ⟨0, [], fun _ => ⟨rfl, rfl⟩, fun h' => absurd hl h',
      fun q hq => by simp at hq, List.Pairwise.nil, fun _ _ _ => by simp [hl]⟩⟩
  · obtain ⟨B, hB⟩ := h hl
    refine ⟨B, fun fp c hc => ?_⟩
    obtain ⟨nt, Lt, rt, Lot, hBd, ⟨rfl, rfl⟩, hW, hD, hR⟩ := hB fp c hc
    refine ⟨nt, Lt, fun h' => absurd h' hl, fun _ => hBd, by simpa using hW, by simpa using hD,
      fun rd hlw hm => ?_⟩
    simp only [hl, not_false_eq_true, decide_true, ↓reduceIte]
    exact hR rd hlw (by simpa using hm)

end
end LeanVM.Guest.B1
