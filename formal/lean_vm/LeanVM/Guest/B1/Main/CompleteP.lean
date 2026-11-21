/-
  LeanVM.Guest.B1.Main.CompleteP

  Uniform placed completeness by trees whose pops are given (`CompleteAtP`, `CompleteAtDP`, the loop form `CompleteAtLP`), its composition along a caller's calls (`kidsFromInP_of_kids'`), and its bridges: to the forms without pops, and from them for a function with no witness hint in its subtree (`[]`).
-/

module

public import LeanVM.Guest.B1.Main.RelAtInP
public import LeanVM.Guest.Memory.NoWitness

/-!
# Completeness with pops

`CompleteAtP … ps`: `CompleteAt` by a tree popping `ps rd` on each memory `rd` it serves; `CompleteAtDP` the same of `CompleteAtD`, `CompleteAtLP` of `CompleteAtL` (a loop helper from an iteration on). The entries are a function of the reader, as a heap witness hint's are read through it; the honest ones are usually constant.

* `kidsFromInP_of_kids'`: `kidsFromIn_of_kids'`, each entered callee `CompleteAtP` its entries, a skipped one's `[]` (`KidsP`), giving `KidsFromInP` with the entries at the memory;
* `toCompleteAt`, `toD`, `toP`, `toL`, `toDP`: forgetting the pops, the disjointness, or entering a loop fresh;
* `relAtInP_nil`, `completeAtP_nil`, `completeAtDP_nil`, `completeAtLP_nil`: a function passing `noWitness` pops `[]`, for free; `RelAtInT.and_pops_nil` adds `∀ rd, t.pops coreProgram rd = []` to any tree predicate, a predicate independent of the memory, so the `T` forms (`CompleteAtDT`, `CompleteAtDTB`, `CompleteAtL`, `KidsT`) carry it as they are.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- **`CompleteAt` by a tree popping `ps rd` on the memory `rd`.** -/
def CompleteAtP (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String) (Lin : Layout)
    (args : List E) (Out : List E → Layout → Prop) (ps : Reader → List Pop) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ ∀ rd, LowDef k rd → MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInP coreProgram fs cert rd (RegionL Lin) (RegionL Lout) fp n f args rets (ps rd)

/-- **`CompleteAtD` by a tree popping `ps rd` on the memory `rd`.** -/
def CompleteAtDP (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String) (Lin : Layout)
    (args : List E) (Out : List E → Layout → Prop) (ps : Reader → List Pop) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ ∀ rd, LowDef k rd → MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInP coreProgram fs cert rd (RegionL Lin) (RegionL Lout) fp n f args rets (ps rd)

/-- **`CompleteAtL` by a tree popping `ps rd` on the memory `rd`**: a loop helper from an iteration on. -/
def CompleteAtLP (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String) (Lin : Layout)
    (args : List E) (Out : List E → Layout → Prop) (ps : Reader → List Pop) (Bd : ℕ → Prop) : Prop :=
  ∃ B, ∀ fp c, fp + B ≤ c → ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout),
    Bd (B + n) ∧ Out rets Lout ∧ Within (Lout ++ Lown) c n ∧ DisjL (Lout ++ Lown) ∧
    ∀ rd, LowDef k rd → MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInCP coreProgram fs cert rd (RegionL Lin) (RegionL Lout) fp c B n f args rets (ps rd)

variable {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ} {f : String} {Lin : Layout} {args : List E}
  {Out : List E → Layout → Prop} {ps : Reader → List Pop}

/-! ## Forgetting -/

theorem CompleteAtP.toCompleteAt (h : CompleteAtP fs cert k f Lin args Out ps) :
    CompleteAt fs cert k f Lin args Out := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, fun rd hl hm => (hr rd hl hm).relAtIn⟩

theorem CompleteAtDP.toP (h : CompleteAtDP fs cert k f Lin args Out ps) : CompleteAtP fs cert k f Lin args Out ps :=
  fun fp =>
    let ⟨n, Lown, rets, Lout, ho, hw, _, hr⟩ := h fp
    ⟨n, Lown, rets, Lout, ho, hw, hr⟩

theorem CompleteAtDP.toD (h : CompleteAtDP fs cert k f Lin args Out ps) : CompleteAtD fs cert k f Lin args Out :=
  fun fp =>
    let ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
    ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hm => (hr rd hl hm).relAtIn⟩

theorem CompleteAtLP.toL {Bd : ℕ → Prop} (h : CompleteAtLP fs cert k f Lin args Out ps Bd) :
    CompleteAtL fs cert k f Lin args Out (fun _ => True) Bd :=
  let ⟨B, hB⟩ := h
  ⟨B, fun fp c hc =>
    let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := hB fp c hc
    ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm => (hr rd hl hm).relAtInC.relAtInCT⟩⟩

/-- **A loop entered fresh**, with its pops. -/
theorem CompleteAtLP.toDP {Bd : ℕ → Prop} (h : CompleteAtLP fs cert k f Lin args Out ps Bd) :
    CompleteAtDP fs cert k f Lin args Out ps := fun fp =>
  let ⟨B, hB⟩ := h
  let ⟨n, Lown, rets, Lout, _, ho, hw, hd, hr⟩ := hB fp (fp + B) le_rfl
  ⟨B + n, Lown, rets, Lout, ho, hw.mono (by omega) (by omega), hd, fun rd hl hm => (hr rd hl hm).relAtInP⟩

/-! ## No witness hint -/

/-- **A tree predicate gains `pops = []`** for a function passing `noWitness`, on every memory. -/
theorem RelAtInT.and_pops_nil {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {rets : List E} {T : Tree → Prop}
    (h : RelAtInT coreProgram fs cert rd R D fp n f args rets T) (hg : NoWitG f) :
    RelAtInT coreProgram fs cert rd R D fp n f args rets fun t => T t ∧ ∀ rd', t.pops coreProgram rd' = [] :=
  let ⟨t, ht, hT⟩ := h
  ⟨t, ht, hT, pops_nil_of_noWitness hg ht.2.1 ht.1⟩

theorem RelAtInCT.and_pops_nil {rd : Reader} {R D : ℕ → Prop} {fp c B n : ℕ} {rets : List E} {T : Tree → Prop}
    (h : RelAtInCT coreProgram fs cert rd R D fp c B n f args rets T) (hg : NoWitG f) :
    RelAtInCT coreProgram fs cert rd R D fp c B n f args rets fun t => T t ∧ ∀ rd', t.pops coreProgram rd' = [] :=
  let ⟨t, ht, hT⟩ := h
  ⟨t, ht, hT, pops_nil_of_noWitness hg ht.2.1 ht.1⟩

/-- **A function passing `noWitness` pops `[]`.** -/
theorem relAtInP_nil {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {rets : List E}
    (h : RelAtIn coreProgram fs cert rd R D fp n f args rets) (hg : NoWitG f) :
    RelAtInP coreProgram fs cert rd R D fp n f args rets [] :=
  let ⟨t, ht, _, hp⟩ := RelAtInT.and_pops_nil h.relAtInT hg
  ⟨t, ht, hp rd⟩

theorem relAtInCP_nil {rd : Reader} {R D : ℕ → Prop} {fp c B n : ℕ} {rets : List E}
    (h : RelAtInC coreProgram fs cert rd R D fp c B n f args rets) (hg : NoWitG f) :
    RelAtInCP coreProgram fs cert rd R D fp c B n f args rets [] :=
  let ⟨t, ht, _, hp⟩ := RelAtInCT.and_pops_nil h.relAtInCT hg
  ⟨t, ht, hp rd⟩

theorem completeAtP_nil (h : CompleteAt fs cert k f Lin args Out) (hg : NoWitG f) :
    CompleteAtP fs cert k f Lin args Out fun _ => [] := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, fun rd hl hm => relAtInP_nil (hr rd hl hm) hg⟩

theorem completeAtDP_nil (h : CompleteAtD fs cert k f Lin args Out) (hg : NoWitG f) :
    CompleteAtDP fs cert k f Lin args Out fun _ => [] := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hm => relAtInP_nil (hr rd hl hm) hg⟩

theorem completeAtLP_nil {T : Tree → Prop} {Bd : ℕ → Prop} (h : CompleteAtL fs cert k f Lin args Out T Bd)
    (hg : NoWitG f) : CompleteAtLP fs cert k f Lin args Out (fun _ => []) Bd :=
  let ⟨B, hB⟩ := h
  ⟨B, fun fp c hc =>
    let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := hB fp c hc
    ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm => relAtInCP_nil (hr rd hl hm).relAtInC hg⟩⟩

/-! ## Composition -/

/-- The entered callees are `CompleteAtP` their entries, a skipped one's are `[]`. -/
def KidsP (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) : List Kid → List (Reader → List Pop) → Prop
  | k :: ks, p :: pss => (k.taken = true → CompleteAtP fs cert κ k.f k.Lin k.args k.Out p) ∧
      (k.taken = false → ∀ rd, p rd = []) ∧ KidsP fs cert κ ks pss
  | [], [] => True
  | _, _ => False

theorem kidsFromInP_dend {rd : Reader} {σ : Val} {R : ℕ → Prop} :
    ∀ (cs : List Call) (pss : List (List Pop)) (Dacc : ℕ → Prop) (b n : ℕ) {D D' : ℕ → Prop}, (∀ i, D' i → D i) →
      KidsFromInP coreProgram fs cert rd σ R Dacc cs pss b n D →
      KidsFromInP coreProgram fs cert rd σ R Dacc cs pss b n D'
  | [], [], _, _, _, _, _, hD, ⟨hn, h⟩ => ⟨hn, fun i hi => h i (hD i hi)⟩
  | _ :: cs, _ :: pss, _, _, _, _, _, hD, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩ =>
      ⟨m, n', Rk, Dk, hn, hR, hc, kidsFromInP_dend cs pss _ _ _ hD hk⟩
  | [], _ :: _, _, _, _, _, _, _, h | _ :: _, [], _, _, _, _, _, _, h => h.elim

/-- **The callees at their running offsets, with their entries**: `kidsFromIn_of_kids'`, each entered callee
popping its entries at the memory. -/
theorem kidsFromInP_of_kids' (κ : ℕ) : ∀ (ks : List Kid) (pss : List (Reader → List Pop)),
    KidsP fs cert κ ks pss → ∀ b : ℕ,
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), OutsOk ks outs ∧ Within L b N ∧
      OutsIn ks outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop), CallsMatch σ cs ks outs →
        LowDef κ rd → MemL rd L → MemL rd (Kid.lins ks) → RegionsOk R Dacc ks outs →
        KidsFromInP coreProgram fs cert rd σ R Dacc cs (pss.map (· rd)) b N
          (fun i => Dacc i ∨ outRegion ks outs i)
  | [], [], _, b => ⟨0, [], [], trivial, fun _ h => by simp at h, trivial, fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | k :: ks, p :: pss, hok, b => by
    by_cases ht : k.taken = true
    · obtain ⟨n, Lown, rets, Lout, hout, hw, hrel⟩ := hok.1 ht b
      obtain ⟨N, L, outs, ho, hW, hI, hK⟩ := kidsFromInP_of_kids' κ ks pss hok.2.2 (b + n)
      refine ⟨n + N, Lout ++ Lown ++ L, (rets, Lout) :: outs, ⟨fun _ => hout, ho⟩, ?_,
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
          refine ⟨n, N, RegionL k.Lin, RegionL Lout, rfl, hR1 ht, ?_, ?_⟩
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
    · obtain ⟨N, L, outs, ho, hW, hI, hK⟩ := kidsFromInP_of_kids' κ ks pss hok.2.2 (b + fs k.f)
      refine ⟨fs k.f + N, L, ([], []) :: outs, ⟨fun h => absurd h ht, ho⟩,
        hW.mono (by omega) (by omega), ⟨fun h => absurd h ht, hI⟩, ?_⟩
      intro rd σ cs R Dacc hc hlow hL hLin hRg
      have ht' : k.taken = false := by simpa using ht
      match cs, hc with
      | c :: cs, ⟨hf, hct, _, hc⟩ =>
        simp only [Kid.lins, List.flatMap_cons] at hLin
        refine ⟨fs k.f, N, fun _ => False, fun _ => False, rfl, fun _ h => h.elim, ?_, ?_⟩
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

/-! ## Disjoint callees -/

/-- The entered callees are `CompleteAtDP` their entries, a skipped one's are `[]`. -/
def KidsDP (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) : List Kid → List (Reader → List Pop) → Prop
  | k :: ks, p :: pss => (k.taken = true → CompleteAtDP fs cert κ k.f k.Lin k.args k.Out p) ∧
      (k.taken = false → ∀ rd, p rd = []) ∧ KidsDP fs cert κ ks pss
  | [], [] => True
  | _, _ => False

/-- **The callees at their running offsets, disjoint, with their entries**: `kidsFromIn_of_kidsD`, each entered
callee popping its entries at the memory. -/
theorem kidsFromInP_of_kidsD (κ : ℕ) : ∀ (ks : List Kid) (pss : List (Reader → List Pop)),
    KidsDP fs cert κ ks pss → ∀ b : ℕ,
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), OutsOk ks outs ∧ Within L b N ∧ DisjL L ∧
      OutsIn ks outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop), CallsMatch σ cs ks outs →
        LowDef κ rd → MemL rd L → MemL rd (Kid.lins ks) → RegionsOk R Dacc ks outs →
        KidsFromInP coreProgram fs cert rd σ R Dacc cs (pss.map (· rd)) b N
          (fun i => Dacc i ∨ outRegion ks outs i)
  | [], [], _, b => ⟨0, [], [], trivial, fun _ h => by simp at h, disj_nil, trivial,
      fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | k :: ks, p :: pss, hok, b => by
    by_cases ht : k.taken = true
    · obtain ⟨n, Lown, rets, Lout, hout, hw, hd, hrel⟩ := hok.1 ht b
      obtain ⟨N, L, outs, ho, hW, hD, hI, hK⟩ := kidsFromInP_of_kidsD κ ks pss hok.2.2 (b + n)
      refine ⟨n + N, Lout ++ Lown ++ L, (rets, Lout) :: outs, ⟨fun _ => hout, ho⟩, ?_,
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
          refine ⟨n, N, RegionL k.Lin, RegionL Lout, rfl, hR1 ht, ?_, ?_⟩
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
    · obtain ⟨N, L, outs, ho, hW, hD, hI, hK⟩ := kidsFromInP_of_kidsD κ ks pss hok.2.2 (b + fs k.f)
      refine ⟨fs k.f + N, L, ([], []) :: outs, ⟨fun h => absurd h ht, ho⟩,
        hW.mono (by omega) (by omega), hD, ⟨fun h => absurd h ht, hI⟩, ?_⟩
      intro rd σ cs R Dacc hc hlow hL hLin hRg
      have ht' : k.taken = false := by simpa using ht
      match cs, hc with
      | c :: cs, ⟨hf, hct, _, hc⟩ =>
        simp only [Kid.lins, List.flatMap_cons] at hLin
        refine ⟨fs k.f, N, fun _ => False, fun _ => False, rfl, fun _ h => h.elim, ?_, ?_⟩
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

/-! ## Regions and nodes -/

theorem RelAtInP.dmono {rd : Reader} {R D D' : ℕ → Prop} {fp n : ℕ} {rets : List E} {ps : List Pop}
    (h : RelAtInP coreProgram fs cert rd R D fp n f args rets ps) (hD : ∀ i, D' i → D i) :
    RelAtInP coreProgram fs cert rd R D' fp n f args rets ps :=
  let ⟨t, ⟨hn, hv, hb, hp, ht, hl, hd⟩, hT⟩ := h
  ⟨t, ⟨hn, hv, hb, hp, ht, hl, fun i hi => hd i (hD i hi)⟩, hT⟩

/-- **A function every call instance of which pops `ps`.** -/
theorem relAtInP_of_node {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {rets : List E} {ps : List Pop}
    (h : RelAtIn coreProgram fs cert rd R D fp n f args rets)
    (hn : ∀ τ bufs kids, (Memory.Tree.node f τ bufs kids).pops coreProgram rd = ps) :
    RelAtInP coreProgram fs cert rd R D fp n f args rets ps := by
  obtain ⟨t, ht, -⟩ := h.relAtInT
  refine ⟨t, ht, ?_⟩
  obtain ⟨hname, hv, -⟩ := ht
  cases t with
  | node g τ bufs kids => cases hname; exact hn τ bufs kids
  | phantom => exact hv.elim

theorem completeAtDP_of_node (h : CompleteAtD fs cert k f Lin args Out)
    (hn : ∀ rd τ bufs kids, (Memory.Tree.node f τ bufs kids).pops coreProgram rd = ps rd) :
    CompleteAtDP fs cert k f Lin args Out ps := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hm => relAtInP_of_node (hr rd hl hm) (hn rd)⟩

end
end LeanVM.Guest.B1
