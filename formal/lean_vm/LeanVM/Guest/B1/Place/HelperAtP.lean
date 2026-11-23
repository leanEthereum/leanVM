/-
  LeanVM.Guest.B1.Place.HelperAtP

  Placed completeness by a tree of exactly given words popping given entries, and such callees placed in sequence.
-/

module

public import LeanVM.Guest.B1.Place.KidsE
public import LeanVM.Guest.B1.Main.CompleteP

/-!
# Exact trees with their pops

* `CompleteAtEP … n ps`: `CompleteAtE … n` by a tree popping `ps rd` on the memory `rd` (`toDP`, `toE`);
* `completeAtEP_of_node`: every call instance pops `ps`;
* `CompleteAtOP … Bd ps`: `CompleteAtO … Bd` by a tree popping `ps rd` (`toO`, from `CompleteAtEP` within the bound);
* `kidsFromInP_of_kidsEP`: `kidsFromInP_of_kidsD` for callees each `CompleteAtEP` at `ns k` words, their total `kidsN`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- **`CompleteAtE … n` by a tree popping `ps rd` on the memory `rd`.** -/
def CompleteAtEP (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String) (Lin : Layout)
    (args : List E) (Out : List E → Layout → Prop) (n : ℕ) (ps : Reader → List Pop) : Prop :=
  ∀ fp, ∃ (Lown : Layout) (rets : List E) (Lout : Layout), Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ ∀ rd, LowDef k rd →
      MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInP coreProgram fs cert rd (RegionL Lin) (RegionL Lout) fp n f args rets (ps rd)

variable {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ} {f : String} {Lin : Layout} {args : List E}
  {Out : List E → Layout → Prop} {n : ℕ} {ps : Reader → List Pop}

theorem CompleteAtEP.toDP (h : CompleteAtEP fs cert k f Lin args Out n ps) :
    CompleteAtDP fs cert k f Lin args Out ps := fun fp =>
  let ⟨Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩

theorem CompleteAtEP.toE (h : CompleteAtEP fs cert k f Lin args Out n ps) :
    CompleteAtE fs cert k f Lin args Out n := fun fp =>
  let ⟨Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  ⟨Lown, rets, Lout, ho, hw, hd, fun rd hl hm => (hr rd hl hm).relAtIn⟩

/-- `CompleteAtEP` from a tree whose size is shown equal to `B`. -/
theorem CompleteAtEP.of_eq {B : ℕ}
    (h : ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), Out rets Lout ∧
      Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ n = B ∧ ∀ rd, LowDef k rd →
        MemL rd (Lout ++ Lown ++ Lin) →
        RelAtInP coreProgram fs cert rd (RegionL Lin) (RegionL Lout) fp n f args rets (ps rd)) :
    CompleteAtEP fs cert k f Lin args Out B ps := fun fp =>
  let ⟨_, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := h fp
  hn ▸ ⟨Lown, rets, Lout, ho, hw, hd, hr⟩

/-- **`CompleteAtO … Bd` by a tree popping `ps rd` on the memory `rd`.** -/
def CompleteAtOP (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String) (Lin : Layout)
    (args : List E) (Out : List E → Layout → Prop) (Bd : Option ℕ) (ps : Reader → List Pop) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ (∀ B ∈ Bd, n ≤ B) ∧ ∀ rd, LowDef k rd →
      MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInP coreProgram fs cert rd (RegionL Lin) (RegionL Lout) fp n f args rets (ps rd)

theorem CompleteAtOP.toO {Bd : Option ℕ} (h : CompleteAtOP fs cert k f Lin args Out Bd ps) :
    CompleteAtO fs cert k f Lin args Out Bd := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, hn, fun rd hl hm => (hr rd hl hm).relAtIn⟩

theorem CompleteAtEP.toOP {Bd : Option ℕ} (h : CompleteAtEP fs cert k f Lin args Out n ps)
    (hn : ∀ B ∈ Bd, n ≤ B) : CompleteAtOP fs cert k f Lin args Out Bd ps := fun fp =>
  let ⟨Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩

/-- **A function every call instance of which pops `ps`.** -/
theorem completeAtEP_of_node (h : CompleteAtE fs cert k f Lin args Out n)
    (hn : ∀ rd τ bufs kids, (Memory.Tree.node f τ bufs kids).pops coreProgram rd = ps rd) :
    CompleteAtEP fs cert k f Lin args Out n ps := fun fp =>
  let ⟨Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  ⟨Lown, rets, Lout, ho, hw, hd, fun rd hl hm => relAtInP_of_node (hr rd hl hm) (hn rd)⟩

/-- The entered callees are `CompleteAtEP` at `ns k` words and their entries, a skipped one's are `[]`. -/
def KidsEP (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (ns : Kid → ℕ) :
    List Kid → List (Reader → List Pop) → Prop
  | k :: ks, p :: pss => (k.taken = true → CompleteAtEP fs cert κ k.f k.Lin k.args k.Out (ns k) p) ∧
      (k.taken = false → ∀ rd, p rd = []) ∧ KidsEP fs cert κ ns ks pss
  | [], [] => True
  | _, _ => False

/-- **Callees by trees of exactly `ns k` words with their entries, placed in sequence from `b`.** -/
theorem kidsFromInP_of_kidsEP (κ : ℕ) (ns : Kid → ℕ) : ∀ (ks : List Kid) (pss : List (Reader → List Pop)),
    KidsEP fs cert κ ns ks pss → ∀ b : ℕ,
    ∃ (L : Layout) (outs : List (List E × Layout)), OutsOk ks outs ∧ Within L b (kidsN fs ns ks) ∧ DisjL L ∧
      OutsIn ks outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop), CallsMatch σ cs ks outs →
        LowDef κ rd → MemL rd L → MemL rd (Kid.lins ks) → RegionsOk R Dacc ks outs →
        KidsFromInP coreProgram fs cert rd σ R Dacc cs (pss.map (· rd)) b (kidsN fs ns ks)
          (fun i => Dacc i ∨ outRegion ks outs i)
  | [], [], _, b => ⟨[], [], trivial, fun _ h => by simp at h, disj_nil, trivial,
      fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | k :: ks, p :: pss, hok, b => by
    have hN : kidsN fs ns (k :: ks) = (if k.taken then ns k else fs k.f) + kidsN fs ns ks := by
      simp [kidsN]
    by_cases ht : k.taken = true
    · obtain ⟨Lown, rets, Lout, hout, hw, hd, hrel⟩ := hok.1 ht b
      obtain ⟨L, outs, ho, hW, hD, hI, hK⟩ := kidsFromInP_of_kidsEP κ ns ks pss hok.2.2 (b + ns k)
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
          · refine kidsFromInP_dend cs _ _ _ _ ?_ (hK rd σ cs R _ hc hlow hL2 hLs ?_)
            · intro i hi
              rcases hi with hi | ⟨_, hi⟩ | hi
              · exact Or.inl (Or.inl hi)
              · exact Or.inl (Or.inr ⟨by rw [hct]; exact ht, hi⟩)
              · exact Or.inr hi
            · simpa [hct] using hR2
    · obtain ⟨L, outs, ho, hW, hD, hI, hK⟩ := kidsFromInP_of_kidsEP κ ns ks pss hok.2.2 (b + fs k.f)
      rw [hN]
      simp only [ht, Bool.false_eq_true, ↓reduceIte]
      refine ⟨L, ([], []) :: outs, ⟨fun h => absurd h ht, ho⟩,
        hW.mono (by omega) (by omega), hD, ⟨fun h => absurd h ht, hI⟩, ?_⟩
      intro rd σ cs R Dacc hc hlow hL hLin hRg
      have ht' : k.taken = false := by simpa using ht
      match cs, hc with
      | c :: cs, ⟨hf, hct, _, hc⟩ =>
        simp only [Kid.lins, List.flatMap_cons] at hLin
        refine ⟨fs k.f, kidsN fs ns ks, fun _ => False, fun _ => False, rfl, fun _ h => h.elim, ?_, ?_⟩
        · rw [hct, ht']
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨by rw [hf], hok.2.1 ht' rd⟩
        · refine kidsFromInP_dend cs _ _ _ _ ?_
            (hK rd σ cs R _ hc hlow hL (Main.memL_append.mp hLin).2 ?_)
          · intro i hi
            rcases hi with hi | ⟨h, _⟩ | hi
            · exact Or.inl (Or.inl hi)
            · exact absurd h ht
            · exact Or.inr hi
          · have := hRg.2
            simp only [hct, ht, Bool.false_eq_true, false_and, or_false] at this ⊢
            exact this
  | [], _ :: _, h, _ | _ :: _, [], h, _ => h.elim

end
end LeanVM.Guest.B1
