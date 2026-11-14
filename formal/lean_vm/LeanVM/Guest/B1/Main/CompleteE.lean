/-
  LeanVM.Guest.B1.Main.CompleteE

  Uniform placed completeness by trees whose pops are given and whose every node satisfies a predicate of the memory
  (`CompleteAtPE`, `CompleteAtDPE`, `CompleteAtLPE`), its composition along a caller's calls (`kidsFromInPE_of_kids'`,
  `kidsFromInPE_of_kidsD`), its bridges to the forms without the predicate, and the lifts of a callee all of whose valid
  trees satisfy it, such as one exact for free (`exactFree`).
-/

module

public import LeanVM.Guest.B1.Main.CompleteP
public import LeanVM.Guest.B1.Main.RelAtInE
public import LeanVM.Guest.Exact.Free

/-!
# Completeness with pops, every node satisfying `Q`

`CompleteAtPE … ps Q`: `CompleteAtP … ps` by a tree also satisfying `Tree.Every (Q rd)` on each memory `rd` it serves;
`CompleteAtDPE`, `CompleteAtLPE` the same of `CompleteAtDP`, `CompleteAtLP`. `Q` is a predicate of the memory, as
exactness is (a heap destination's words are read through it).

* `kidsFromInPE_of_kids'`, `kidsFromInPE_of_kidsD`: `kidsFromInP_of_kids'`, `kidsFromInP_of_kidsD`, the entered callees
  `CompleteAtPE` (`KidsPE`), `CompleteAtDPE` (`KidsDPE`), giving `KidsFromInPE`;
* `toP`, `toDP`, `toLP`, `toPE`, `toDPE`: forgetting `Q`, the disjointness, or entering a loop fresh;
* `withEvery`: a `P` form whose function's valid trees all satisfy `Every (Q rd)` on the memories it serves (`EveryOn`)
  is an `E` form; `everyOn_exact`: a function passing `exactFree` is exact on every memory; `completeAtPE_nil`,
  `completeAtDPE_nil`, `completeAtLPE_nil`: with `noWitness`, from the forms without pops.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- **`CompleteAtP` by a tree satisfying `Every (Q rd)` on the memory `rd`.** -/
def CompleteAtPE (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String) (Lin : Layout)
    (args : List E) (Out : List E → Layout → Prop) (ps : Reader → List Pop) (Q : Reader → String → Val → Prop) :
    Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ ∀ rd, LowDef k rd → MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInPE coreProgram fs cert rd (Q rd) (RegionL Lin) (RegionL Lout) fp n f args rets (ps rd)

/-- **`CompleteAtDP` by a tree satisfying `Every (Q rd)` on the memory `rd`.** -/
def CompleteAtDPE (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String) (Lin : Layout)
    (args : List E) (Out : List E → Layout → Prop) (ps : Reader → List Pop) (Q : Reader → String → Val → Prop) :
    Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ ∀ rd, LowDef k rd → MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInPE coreProgram fs cert rd (Q rd) (RegionL Lin) (RegionL Lout) fp n f args rets (ps rd)

/-- **`CompleteAtLP` by a tree satisfying `Every (Q rd)` on the memory `rd`**: a loop helper from an iteration on. -/
def CompleteAtLPE (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String) (Lin : Layout)
    (args : List E) (Out : List E → Layout → Prop) (ps : Reader → List Pop) (Q : Reader → String → Val → Prop)
    (Bd : ℕ → Prop) : Prop :=
  ∃ B, ∀ fp c, fp + B ≤ c → ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout),
    Bd (B + n) ∧ Out rets Lout ∧ Within (Lout ++ Lown) c n ∧ DisjL (Lout ++ Lown) ∧
    ∀ rd, LowDef k rd → MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInCPE coreProgram fs cert rd (Q rd) (RegionL Lin) (RegionL Lout) fp c B n f args rets (ps rd)

variable {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ} {f : String} {Lin : Layout} {args : List E}
  {Out : List E → Layout → Prop} {ps : Reader → List Pop} {Q : Reader → String → Val → Prop}

/-! ## Forgetting -/

theorem CompleteAtPE.toP (h : CompleteAtPE fs cert k f Lin args Out ps Q) : CompleteAtP fs cert k f Lin args Out ps :=
  fun fp =>
    let ⟨n, Lown, rets, Lout, ho, hw, hr⟩ := h fp
    ⟨n, Lown, rets, Lout, ho, hw, fun rd hl hm => (hr rd hl hm).toP⟩

theorem CompleteAtDPE.toDP (h : CompleteAtDPE fs cert k f Lin args Out ps Q) :
    CompleteAtDP fs cert k f Lin args Out ps := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hm => (hr rd hl hm).toP⟩

theorem CompleteAtDPE.toPE (h : CompleteAtDPE fs cert k f Lin args Out ps Q) :
    CompleteAtPE fs cert k f Lin args Out ps Q := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, _, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hr⟩

theorem CompleteAtLPE.toLP {Bd : ℕ → Prop} (h : CompleteAtLPE fs cert k f Lin args Out ps Q Bd) :
    CompleteAtLP fs cert k f Lin args Out ps Bd :=
  let ⟨B, hB⟩ := h
  ⟨B, fun fp c hc =>
    let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := hB fp c hc
    ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm => (hr rd hl hm).toP⟩⟩

/-- **A loop entered fresh**, with its pops and `Every (Q rd)`. -/
theorem CompleteAtLPE.toDPE {Bd : ℕ → Prop} (h : CompleteAtLPE fs cert k f Lin args Out ps Q Bd) :
    CompleteAtDPE fs cert k f Lin args Out ps Q := fun fp =>
  let ⟨B, hB⟩ := h
  let ⟨n, Lown, rets, Lout, _, ho, hw, hd, hr⟩ := hB fp (fp + B) le_rfl
  ⟨B + n, Lown, rets, Lout, ho, hw.mono (by omega) (by omega), hd, fun rd hl hm => (hr rd hl hm).relAtInPE⟩

/-! ## Callees whose every valid tree satisfies `Q` -/

/-- **Every valid tree of `f` at `args` satisfies `Every (Q rd)`**, on every memory `rd` of the caller's words. -/
def EveryOn (k : ℕ) (f : String) (Lin : Layout) (args : List E) (Q : Reader → String → Val → Prop) : Prop :=
  ∀ rd, LowDef k rd → MemL rd Lin → ∀ (t : Tree) (rets : List E), t.name = f → t.Valid coreProgram rd args rets →
    t.Every (Q rd)

/-- **A function passing `exactFree` is exact**, on every memory. -/
theorem everyOn_exact (hg : ExactFreeG f) : EveryOn k f Lin args fun rd => ExactAt coreProgram rd :=
  fun rd _ _ _ _ hn hv => every_exact_of_free hg hv hn rd

theorem CompleteAtP.withEvery (h : CompleteAtP fs cert k f Lin args Out ps) (hQ : EveryOn k f Lin args Q) :
    CompleteAtPE fs cert k f Lin args Out ps Q := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, fun rd hl hm =>
    (hr rd hl hm).withEvery fun t hn hv => hQ rd hl (Main.memL_append.mp hm).2 t rets hn hv⟩

theorem CompleteAtDP.withEvery (h : CompleteAtDP fs cert k f Lin args Out ps) (hQ : EveryOn k f Lin args Q) :
    CompleteAtDPE fs cert k f Lin args Out ps Q := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hm =>
    (hr rd hl hm).withEvery fun t hn hv => hQ rd hl (Main.memL_append.mp hm).2 t rets hn hv⟩

theorem CompleteAtLP.withEvery {Bd : ℕ → Prop} (h : CompleteAtLP fs cert k f Lin args Out ps Bd)
    (hQ : EveryOn k f Lin args Q) : CompleteAtLPE fs cert k f Lin args Out ps Q Bd :=
  let ⟨B, hB⟩ := h
  ⟨B, fun fp c hc =>
    let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := hB fp c hc
    ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm =>
      (hr rd hl hm).withEvery fun t hn hv => hQ rd hl (Main.memL_append.mp hm).2 t rets hn hv⟩⟩

/-- **A function passing `noWitness` whose valid trees satisfy `Every (Q rd)`** pops `[]` and satisfies it. -/
theorem completeAtPE_nil (h : CompleteAt fs cert k f Lin args Out) (hg : NoWitG f) (hQ : EveryOn k f Lin args Q) :
    CompleteAtPE fs cert k f Lin args Out (fun _ => []) Q :=
  (completeAtP_nil h hg).withEvery hQ

theorem completeAtDPE_nil (h : CompleteAtD fs cert k f Lin args Out) (hg : NoWitG f) (hQ : EveryOn k f Lin args Q) :
    CompleteAtDPE fs cert k f Lin args Out (fun _ => []) Q :=
  (completeAtDP_nil h hg).withEvery hQ

theorem completeAtLPE_nil {T : Tree → Prop} {Bd : ℕ → Prop} (h : CompleteAtL fs cert k f Lin args Out T Bd)
    (hg : NoWitG f) (hQ : EveryOn k f Lin args Q) : CompleteAtLPE fs cert k f Lin args Out (fun _ => []) Q Bd :=
  (completeAtLP_nil h hg).withEvery hQ

/-! ## Composition -/

/-- The entered callees are `CompleteAtPE` their entries, a skipped one's are `[]`. -/
def KidsPE (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) :
    List Kid → List (Reader → List Pop) → (Reader → String → Val → Prop) → Prop
  | k :: ks, p :: pss, Q => (k.taken = true → CompleteAtPE fs cert κ k.f k.Lin k.args k.Out p Q) ∧
      (k.taken = false → ∀ rd, p rd = []) ∧ KidsPE fs cert κ ks pss Q
  | [], [], _ => True
  | _, _, _ => False

/-- The entered callees are `CompleteAtDPE` their entries, a skipped one's are `[]`. -/
def KidsDPE (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) :
    List Kid → List (Reader → List Pop) → (Reader → String → Val → Prop) → Prop
  | k :: ks, p :: pss, Q => (k.taken = true → CompleteAtDPE fs cert κ k.f k.Lin k.args k.Out p Q) ∧
      (k.taken = false → ∀ rd, p rd = []) ∧ KidsDPE fs cert κ ks pss Q
  | [], [], _ => True
  | _, _, _ => False

theorem kidsFromInPE_dend {rd : Reader} {σ : Val} {R : ℕ → Prop} :
    ∀ (cs : List Call) (pss : List (List Pop)) (Dacc : ℕ → Prop) (b n : ℕ) {D D' : ℕ → Prop}, (∀ i, D' i → D i) →
      KidsFromInPE coreProgram fs cert rd σ (Q rd) R Dacc cs pss b n D →
      KidsFromInPE coreProgram fs cert rd σ (Q rd) R Dacc cs pss b n D'
  | [], [], _, _, _, _, _, hD, ⟨hn, h⟩ => ⟨hn, fun i hi => h i (hD i hi)⟩
  | _ :: cs, _ :: pss, _, _, _, _, _, hD, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩ =>
      ⟨m, n', Rk, Dk, hn, hR, hc, kidsFromInPE_dend cs pss _ _ _ hD hk⟩
  | [], _ :: _, _, _, _, _, _, _, h | _ :: _, [], _, _, _, _, _, _, h => h.elim

/-- **The callees at their running offsets, with their entries**: `kidsFromInP_of_kids'`, each entered callee's
tree satisfying `Every (Q rd)` on the memory `rd`. -/
theorem kidsFromInPE_of_kids' (κ : ℕ) : ∀ (ks : List Kid) (pss : List (Reader → List Pop)),
    KidsPE fs cert κ ks pss Q → ∀ b : ℕ,
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), OutsOk ks outs ∧ Within L b N ∧
      OutsIn ks outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop), CallsMatch σ cs ks outs →
        LowDef κ rd → MemL rd L → MemL rd (Kid.lins ks) → RegionsOk R Dacc ks outs →
        KidsFromInPE coreProgram fs cert rd σ (Q rd) R Dacc cs (pss.map (· rd)) b N
          (fun i => Dacc i ∨ outRegion ks outs i)
  | [], [], _, b => ⟨0, [], [], trivial, fun _ h => by simp at h, trivial, fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | k :: ks, p :: pss, hok, b => by
    by_cases ht : k.taken = true
    · obtain ⟨n, Lown, rets, Lout, hout, hw, hrel⟩ := hok.1 ht b
      obtain ⟨N, L, outs, ho, hW, hI, hK⟩ := kidsFromInPE_of_kids' κ ks pss hok.2.2 (b + n)
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
          · refine kidsFromInPE_dend cs _ _ _ _ ?_ (hK rd σ cs R _ hc hlow hL2 hLs ?_)
            · intro i hi
              rcases hi with hi | ⟨_, hi⟩ | hi
              · exact Or.inl (Or.inl hi)
              · exact Or.inl (Or.inr ⟨by rw [hct]; exact ht, hi⟩)
              · exact Or.inr hi
            · simpa [hct] using hR2
    · obtain ⟨N, L, outs, ho, hW, hI, hK⟩ := kidsFromInPE_of_kids' κ ks pss hok.2.2 (b + fs k.f)
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
        · refine kidsFromInPE_dend cs _ _ _ _ ?_
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


/-- **The callees at their running offsets, disjoint, with their entries**: `kidsFromInP_of_kidsD`, each
entered callee's tree satisfying `Every (Q rd)` on the memory `rd`. -/
theorem kidsFromInPE_of_kidsD (κ : ℕ) : ∀ (ks : List Kid) (pss : List (Reader → List Pop)),
    KidsDPE fs cert κ ks pss Q → ∀ b : ℕ,
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), OutsOk ks outs ∧ Within L b N ∧ DisjL L ∧
      OutsIn ks outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop), CallsMatch σ cs ks outs →
        LowDef κ rd → MemL rd L → MemL rd (Kid.lins ks) → RegionsOk R Dacc ks outs →
        KidsFromInPE coreProgram fs cert rd σ (Q rd) R Dacc cs (pss.map (· rd)) b N
          (fun i => Dacc i ∨ outRegion ks outs i)
  | [], [], _, b => ⟨0, [], [], trivial, fun _ h => by simp at h, disj_nil, trivial,
      fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | k :: ks, p :: pss, hok, b => by
    by_cases ht : k.taken = true
    · obtain ⟨n, Lown, rets, Lout, hout, hw, hd, hrel⟩ := hok.1 ht b
      obtain ⟨N, L, outs, ho, hW, hD, hI, hK⟩ := kidsFromInPE_of_kidsD κ ks pss hok.2.2 (b + n)
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
          · refine kidsFromInPE_dend cs _ _ _ _ ?_ (hK rd σ cs R _ hc hlow hL2 hLs ?_)
            · intro i hi
              rcases hi with hi | ⟨_, hi⟩ | hi
              · exact Or.inl (Or.inl hi)
              · exact Or.inl (Or.inr ⟨by rw [hct]; exact ht, hi⟩)
              · exact Or.inr hi
            · simpa [hct] using hR2
    · obtain ⟨N, L, outs, ho, hW, hD, hI, hK⟩ := kidsFromInPE_of_kidsD κ ks pss hok.2.2 (b + fs k.f)
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
        · refine kidsFromInPE_dend cs _ _ _ _ ?_
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
