/-
  LeanVM.Guest.Budget.BoundedR

  Bounded placed completeness by trees satisfying predicates of the memory, along a caller's calls (`KidsDTBR`), and the two ways a callee's pops reach such a predicate.
-/

module

public import LeanVM.Guest.Budget.Bounded
public import LeanVM.Guest.B1.Main.CompleteP

/-!
# Bounded completeness with predicates of the memory

* `KidsDTBR ks Ts Bs`: `KidsDTB` with the callees' predicates a function of the memory, `Ts rd` the list on `rd`; `KidsDTB.toR`: a constant one. `kidsFromInT_of_kidsDTBR`: `kidsFromInT_of_kidsDTB`, the callees' trees satisfying `Ts rd` on each memory `rd`.
* `CompleteAtDTB.withPops`, `CompleteAtDTBR.withPops`: a tree predicate and validity, on the memories the callee serves, giving the pops `ps rd` add them to the predicate; `CompleteAtDTBR.lowMono`.
* `completeAtDTBR_of_relAtInP`: a callee placed at every frame pointer in a size fixed before the memory, popping `ps rd`, its valid trees within `B` words (`TotalLe`, `TotalLeOn`), is complete within `B` by trees popping `ps rd`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- **The entered callees within their bounds `Bs`, by trees satisfying `Ts rd` on each memory `rd`.** -/
def KidsDTBR (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) :
    List Kid → (Reader → List (Tree → Prop)) → List ℕ → Prop
  | k :: ks, Ts, Bs => (k.taken = true → CompleteAtDTBR fs cert κ k.f k.Lin k.args k.Out
      (fun rd => (Ts rd).headD fun _ => True) (Bs.headD 0)) ∧ KidsDTBR fs cert κ ks (fun rd => (Ts rd).tail) Bs.tail
  | [], _, _ => True

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- Predicates of the tree alone are predicates of the memory. -/
theorem KidsDTB.toR {κ : ℕ} : ∀ {ks : List Kid} {Ts : List (Tree → Prop)} {Bs : List ℕ},
    KidsDTB fs cert κ ks Ts Bs → KidsDTBR fs cert κ ks (fun _ => Ts) Bs
  | [], _, _, _ => trivial
  | _ :: _, _, _, ⟨h, hs⟩ => ⟨fun ht => (h ht).toR, hs.toR⟩

/-- **The callees at their running offsets, within their bounds, by trees of their predicates of the memory.** -/
theorem kidsFromInT_of_kidsDTBR (κ : ℕ) : ∀ (ks : List Kid) (Ts : Reader → List (Tree → Prop)) (Bs : List ℕ),
    KidsDTBR fs cert κ ks Ts Bs → ∀ b : ℕ,
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), N ≤ kidsBoundL fs ks Bs ∧
      OutsOk ks outs ∧ Within L b N ∧ DisjL L ∧ OutsIn ks outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop), CallsMatch σ cs ks outs →
        LowDef κ rd → MemL rd L → MemL rd (Kid.lins ks) → RegionsOk R Dacc ks outs →
        KidsFromInT coreProgram fs cert rd σ R Dacc cs (Ts rd) b N (fun i => Dacc i ∨ outRegion ks outs i)
  | [], _, _, _, b => ⟨0, [], [], le_rfl, trivial, fun _ h => by simp at h, disj_nil, trivial,
      fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | k :: ks, Ts, Bs, hok, b => by
    by_cases ht : k.taken = true
    · obtain ⟨n, Lown, rets, Lout, hnB, hout, hw, hd, hrel⟩ := hok.1 ht b
      obtain ⟨N, L, outs, hNB, ho, hW, hD, hI, hK⟩ :=
        kidsFromInT_of_kidsDTBR κ ks (fun rd => (Ts rd).tail) Bs.tail hok.2 (b + n)
      refine ⟨n + N, Lout ++ Lown ++ L, (rets, Lout) :: outs, ?_, ⟨fun _ => hout, ho⟩, ?_,
        disj_append hd hD hw hW le_rfl,
        ⟨fun _ q hq => by simp [hq], hI.mono fun q hq => by simp [hq]⟩, ?_⟩
      · simp only [kidsBoundL, ht, ↓reduceIte]
        omega
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
          refine ⟨n, N, RegionL k.Lin, RegionL Lout, rfl, hR1 ht, ?_, ?_⟩
          · rw [hct]
            simp only [ht, ↓reduceIte]
            rw [hf, ha, hr]
            exact hrel rd hlow (Main.memL_append.mpr ⟨hL1, hLk⟩)
          · refine kidsFromInT_dend cs _ _ _ _ ?_ (hK rd σ cs R _ hc hlow hL2 hLs ?_)
            · intro i hi
              rcases hi with hi | ⟨_, hi⟩ | hi
              · exact Or.inl (Or.inl hi)
              · exact Or.inl (Or.inr ⟨by rw [hct]; exact ht, hi⟩)
              · exact Or.inr hi
            · simpa [hct] using hR2
    · obtain ⟨N, L, outs, hNB, ho, hW, hD, hI, hK⟩ :=
        kidsFromInT_of_kidsDTBR κ ks (fun rd => (Ts rd).tail) Bs.tail hok.2 (b + fs k.f)
      refine ⟨fs k.f + N, L, ([], []) :: outs, ?_, ⟨fun h => absurd h ht, ho⟩,
        hW.mono (by omega) (by omega), hD, ⟨fun h => absurd h ht, hI⟩, ?_⟩
      · simp only [kidsBoundL, ht, Bool.false_eq_true, ↓reduceIte]
        omega
      intro rd σ cs R Dacc hc hlow hL hLin hRg
      match cs, hc with
      | c :: cs, ⟨hf, hct, _, hc⟩ =>
        simp only [Kid.lins, List.flatMap_cons] at hLin
        refine ⟨fs k.f, N, fun _ => False, fun _ => False, rfl, fun _ h => h.elim, ?_, ?_⟩
        · have ht' : k.taken = false := by simpa using ht
          rw [hct, ht']
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hf]
        · refine kidsFromInT_dend cs _ _ _ _ ?_ (hK rd σ cs R _ hc hlow hL (Main.memL_append.mp hLin).2 ?_)
          · intro i hi
            rcases hi with hi | ⟨h, _⟩ | hi
            · exact Or.inl (Or.inl hi)
            · exact absurd h ht
            · exact Or.inr hi
          · have := hRg.2
            simp only [hct, ht, Bool.false_eq_true, false_and, or_false] at this ⊢
            exact this

/-! ## Pops in the predicate -/

variable {k : ℕ} {f : String} {Lin : Layout} {args : List E} {Out : List E → Layout → Prop} {B : ℕ}
  {ps : Reader → List Pop}

/-- A bounded completeness on memories defined below `2^k` holds on those defined below `2^k'`, `k ≤ k'`. -/
theorem CompleteAtDTBR.lowMono {k' : ℕ} {T : Reader → Tree → Prop} (h : CompleteAtDTBR fs cert k f Lin args Out T B)
    (hk : k ≤ k') : CompleteAtDTBR fs cert k' f Lin args Out T B := fun fp =>
  let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm => hr rd (hl.mono hk) hm⟩

/-- **A tree predicate whose valid trees pop `ps rd`** on the memories the callee serves, the pops added to it. -/
theorem CompleteAtDTBR.withPops {T : Reader → Tree → Prop} (h : CompleteAtDTBR fs cert k f Lin args Out T B)
    (hp : ∀ rd, LowDef k rd → MemL rd Lin → ∀ t rets, t.Valid coreProgram rd args rets → T rd t →
      t.pops coreProgram rd = ps rd) :
    CompleteAtDTBR fs cert k f Lin args Out (fun rd t => T rd t ∧ t.pops coreProgram rd = ps rd) B := fun fp =>
  let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm =>
    let ⟨t, ht, hT⟩ := hr rd hl hm
    ⟨t, ht, hT, hp rd hl (Main.memL_append.mp hm).2 t rets ht.2.1 hT⟩⟩

/-- **`CompleteAtDTB T` with pops**: `T` and validity give the pops `ps rd`. -/
theorem CompleteAtDTB.withPops {T : Tree → Prop} (h : CompleteAtDTB fs cert k f Lin args Out T B)
    (hp : ∀ rd, LowDef k rd → MemL rd Lin → ∀ t rets, t.Valid coreProgram rd args rets → T t →
      t.pops coreProgram rd = ps rd) :
    CompleteAtDTBR fs cert k f Lin args Out (fun rd t => T t ∧ t.pops coreProgram rd = ps rd) B :=
  h.toR.withPops hp

/-- **A callee placed with its pops in a size fixed before the memory, its valid trees within `B`**, is complete
within `B` by trees popping `ps rd`. -/
theorem completeAtDTBR_of_relAtInP {rets : List E}
    (h : ∀ fp, ∃ n, ∀ rd, LowDef k rd → MemL rd Lin →
      RelAtInP coreProgram fs cert rd (RegionL Lin) (RegionL []) fp n f args rets (ps rd))
    (hB : ∀ (rd : Reader) (t : Tree) (rets' : List E), t.name = f → t.Valid coreProgram rd args rets' →
      t.BufsOk coreProgram → t.total fs ≤ B) :
    CompleteAtDTBR fs cert k f Lin args (Returns rets) (fun rd t => t.pops coreProgram rd = ps rd) B := by
  intro fp
  classical
  obtain ⟨n, hn⟩ := h fp
  by_cases hex : ∃ rd, LowDef k rd ∧ MemL rd Lin
  · obtain ⟨rd1, hl1, hL1⟩ := hex
    obtain ⟨t, ⟨hnm, hv, hb, -, ht, -⟩, -⟩ := hn rd1 hl1 hL1
    exact ⟨n, [], rets, [], ht ▸ hB rd1 t rets hnm hv hb, ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      fun rd hl hL => hn rd hl (by simpa using hL)⟩
  · exact ⟨0, [], rets, [], Nat.zero_le _, ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      fun rd hl hL => absurd ⟨rd, hl, by simpa using hL⟩ hex⟩

/-- `completeAtDTBR_of_relAtInP` on a precondition's bound (`TotalLeOn`). -/
theorem completeAtDTBR_of_relAtInP_on {rets : List E} {Pre : List E → Prop} {Bf : List E → ℕ}
    (h : ∀ fp, ∃ n, ∀ rd, LowDef k rd → MemL rd Lin →
      RelAtInP coreProgram fs cert rd (RegionL Lin) (RegionL []) fp n f args rets (ps rd))
    (hT : TotalLeOn coreProgram fs f Pre Bf) (hpre : Pre args) (hB : Bf args ≤ B) :
    CompleteAtDTBR fs cert k f Lin args (Returns rets) (fun rd t => t.pops coreProgram rd = ps rd) B :=
  completeAtDTBR_of_relAtInP h fun rd t rets' hn hv hb => (hT rd t args rets' hn hpre hv hb).trans hB

end
end LeanVM.Guest.B1
