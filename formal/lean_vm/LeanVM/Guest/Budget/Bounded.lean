/-
  LeanVM.Guest.Budget.Bounded

  Placed completeness with a size bound independent of the memory (`n ≤ B`), for the budget's
  words: `CompleteAtDTB`, its composition along a caller's calls, and the bounded lifts of pure
  functions and leaves.
-/

module

public import LeanVM.Guest.Budget.Strengthen
public import LeanVM.Guest.Memory.LiftPure

/-!
# Bounded placed completeness

`main`'s words must be bounded before any memory exists (the honest memory is built from them),
so each callee's size `n` must be bounded in its existential, before the memory: `CompleteAtDTB …
T B` is `CompleteAtDT … T` with `n ≤ B` (mumbai's `CompleteAtB`, with a tree predicate); `CompleteAtDTBR` takes a predicate of the memory, for what a tree reads through it (its pops).

* `kidsFromInT_of_kidsDTB`: callees with bounds `Bs` give a total `N` at most `kidsBoundL`: each
  entered call's bound, each other call's frame.
* `completeAtDTB_of_relIn`: a pure function loading the caller's words, every valid tree of it at
  `args` of at most `B` words (`TotalLe`, from the static certificates), is complete within `B`.
* `completeAtDTB_leaf`: a leaf with its `HeapBuf`s, within its frame and buffers.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- **`CompleteAtDT` within `B` words**: at every frame pointer, a size at most `B`, before the
memory. -/
def CompleteAtDTB (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String) (Lin : Layout)
    (args : List E) (Out : List E → Layout → Prop) (T : Tree → Prop) (B : ℕ) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), n ≤ B ∧ Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ ∀ rd, LowDef k rd →
      MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInT coreProgram fs cert rd (RegionL Lin) (RegionL Lout) fp n f args rets T

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem CompleteAtDTB.toDT {k : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {T : Tree → Prop} {B : ℕ}
    (h : CompleteAtDTB fs cert k f Lin args Out T B) : CompleteAtDT fs cert k f Lin args Out T :=
  fun fp =>
    let ⟨n, Lown, rets, Lout, _, ho, hw, hd, hr⟩ := h fp
    ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩

/-- **A loop entered fresh, within `B` words.** -/
theorem CompleteAtL.toDTB {k : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {T : Tree → Prop} {B : ℕ}
    (h : CompleteAtL fs cert k f Lin args Out T (· ≤ B)) : CompleteAtDTB fs cert k f Lin args Out T B :=
  fun fp =>
    let ⟨Bl, hB⟩ := h
    let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := hB fp (fp + Bl) le_rfl
    ⟨Bl + n, Lown, rets, Lout, hn, ho, hw.mono (by omega) (by omega), hd,
      fun rd hl hm => (hr rd hl hm).relAtInT⟩

/-- A bounded completeness on memories defined below `2^k` holds on those defined below
`2^k'`, `k ≤ k'`. -/
theorem CompleteAtDTB.lowMono {k k' : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {T : Tree → Prop} {B : ℕ}
    (h : CompleteAtDTB fs cert k f Lin args Out T B) (hk : k ≤ k') :
    CompleteAtDTB fs cert k' f Lin args Out T B := fun fp =>
  let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm => hr rd (hl.mono hk) hm⟩

/-- A bounded completeness with a tree predicate forgets the predicate (`CompleteAtB`). -/
theorem CompleteAtDTB.toCompleteAtB {k : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {T : Tree → Prop} {B : ℕ}
    (h : CompleteAtDTB fs cert k f Lin args Out T B) : CompleteAtB fs cert k f Lin args Out B :=
  fun fp =>
    let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
    ⟨n, Lown, rets, Lout, ho, hw, hd, hn, fun rd hl hm => (hr rd hl hm).relAtIn⟩

theorem CompleteAtDTB.mono {k : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {T T' : Tree → Prop} {B B' : ℕ}
    (h : CompleteAtDTB fs cert k f Lin args Out T B) (hB : B ≤ B') (hT : ∀ t, T t → T' t) :
    CompleteAtDTB fs cert k f Lin args Out T' B' := fun fp =>
  let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, le_trans hn hB, ho, hw, hd, fun rd hl hm =>
    let ⟨t, ht, hTt⟩ := hr rd hl hm
    ⟨t, ht, hT t hTt⟩⟩

/-- **`CompleteAtDTB` by a tree satisfying a predicate of the memory.** -/
def CompleteAtDTBR (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String) (Lin : Layout)
    (args : List E) (Out : List E → Layout → Prop) (T : Reader → Tree → Prop) (B : ℕ) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), n ≤ B ∧ Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ ∀ rd, LowDef k rd →
      MemL rd (Lout ++ Lown ++ Lin) →
      RelAtInT coreProgram fs cert rd (RegionL Lin) (RegionL Lout) fp n f args rets (T rd)

theorem CompleteAtDTBR.mono {k : ℕ} {f : String} {Lin : Layout} {args : List E} {Out : List E → Layout → Prop}
    {T T' : Reader → Tree → Prop} {B B' : ℕ} (h : CompleteAtDTBR fs cert k f Lin args Out T B) (hB : B ≤ B')
    (hT : ∀ rd t, T rd t → T' rd t) : CompleteAtDTBR fs cert k f Lin args Out T' B' := fun fp =>
  let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn.trans hB, ho, hw, hd, fun rd hl hm =>
    let ⟨t, ht, hT'⟩ := hr rd hl hm
    ⟨t, ht, hT rd t hT'⟩⟩

/-- **Forgetting the memory**: a predicate holding on every memory. -/
theorem CompleteAtDTBR.toDTB {k : ℕ} {f : String} {Lin : Layout} {args : List E} {Out : List E → Layout → Prop}
    {T : Reader → Tree → Prop} {T' : Tree → Prop} {B : ℕ} (h : CompleteAtDTBR fs cert k f Lin args Out T B)
    (hT : ∀ rd t, T rd t → T' t) : CompleteAtDTB fs cert k f Lin args Out T' B := fun fp =>
  let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm =>
    let ⟨t, ht, hT'⟩ := hr rd hl hm
    ⟨t, ht, hT rd t hT'⟩⟩

/-- A predicate of the tree alone is one of the memory. -/
theorem CompleteAtDTB.toR {k : ℕ} {f : String} {Lin : Layout} {args : List E} {Out : List E → Layout → Prop}
    {T : Tree → Prop} {B : ℕ} (h : CompleteAtDTB fs cert k f Lin args Out T B) :
    CompleteAtDTBR fs cert k f Lin args Out (fun _ ↦ T) B := h

/-- **A node's valid trees satisfy the predicate**, from its validity. -/
theorem CompleteAtDTBR.monoV {k : ℕ} {f : String} {Lin : Layout} {args : List E} {Out : List E → Layout → Prop}
    {T T' : Reader → Tree → Prop} {B B' : ℕ} (h : CompleteAtDTBR fs cert k f Lin args Out T B) (hB : B ≤ B')
    (hT : ∀ rd t rets, t.Valid coreProgram rd args rets → T rd t → T' rd t) :
    CompleteAtDTBR fs cert k f Lin args Out T' B' := fun fp =>
  let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn.trans hB, ho, hw, hd, fun rd hl hm =>
    let ⟨t, ht, hT'⟩ := hr rd hl hm
    ⟨t, ht, hT rd t rets ht.2.1 hT'⟩⟩

/-- Uniform's `CompleteAtB` is `CompleteAtDTB` with no predicate. -/
theorem CompleteAtB.toDTB {k : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} (h : CompleteAtB fs cert k f Lin args Out B) :
    CompleteAtDTB fs cert k f Lin args Out (fun _ => True) B := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm => (hr rd hl hm).relAtInT⟩

/-- **Strengthening by a property of every valid tree on the memories it runs on.** -/
theorem CompleteAtDTB.and_valid_on {k : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {T Q : Tree → Prop} {B : ℕ}
    (h : CompleteAtDTB fs cert k f Lin args Out T B)
    (hQ : ∀ (rd : Reader), LowDef k rd → MemL rd Lin → ∀ (t : Tree) (rets : List E), t.name = f →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram → Q t) :
    CompleteAtDTB fs cert k f Lin args Out (fun t => T t ∧ Q t) B := fun fp =>
  let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm =>
    let ⟨t, ⟨hn', hv, hb, hrest⟩, hT⟩ := hr rd hl hm
    ⟨t, ⟨hn', hv, hb, hrest⟩, hT, hQ rd hl (Main.memL_append.mp hm).2 t rets hn' hv hb⟩⟩

/-- **The tree within the bound**: a `CompleteAtDTB` tree's words are its size, at most `B`. -/
theorem CompleteAtDTB.with_total {k : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {T : Tree → Prop} {B : ℕ}
    (h : CompleteAtDTB fs cert k f Lin args Out T B) :
    CompleteAtDTB fs cert k f Lin args Out (fun t => T t ∧ t.total fs ≤ B) B := fun fp =>
  let ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hm =>
    let ⟨t, ⟨hn', hv, hb, hp, ht, hrest⟩, hT⟩ := hr rd hl hm
    ⟨t, ⟨hn', hv, hb, hp, ht, hrest⟩, hT, ht ▸ hn⟩⟩

/-! ## Composition -/

/-- The entered callees are complete within their bounds `Bs`, by trees satisfying `Ts`. -/
def KidsDTB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) :
    List Kid → List (Tree → Prop) → List ℕ → Prop
  | k :: ks, Ts, Bs => (k.taken = true → CompleteAtDTB fs cert κ k.f k.Lin k.args k.Out
      (Ts.headD fun _ => True) (Bs.headD 0)) ∧ KidsDTB fs cert κ ks Ts.tail Bs.tail
  | [], _, _ => True

/-- The callees' words: an entered call's bound, another's frame. -/
def kidsBoundL (fs : String → ℕ) : List Kid → List ℕ → ℕ
  | k :: ks, Bs => (if k.taken then Bs.headD 0 else fs k.f) + kidsBoundL fs ks Bs.tail
  | [], _ => 0

theorem KidsDTB.lowMono {κ κ' : ℕ} (hk : κ ≤ κ') : ∀ {ks : List Kid} {Ts : List (Tree → Prop)}
    {Bs : List ℕ}, KidsDTB fs cert κ ks Ts Bs → KidsDTB fs cert κ' ks Ts Bs
  | [], _, _, _ => trivial
  | _ :: _, _, _, ⟨h, hs⟩ => ⟨fun ht => (h ht).lowMono hk, hs.lowMono hk⟩

theorem KidsDTB.toDT {κ : ℕ} : ∀ {ks : List Kid} {Ts : List (Tree → Prop)} {Bs : List ℕ},
    KidsDTB fs cert κ ks Ts Bs → KidsDT fs cert κ ks Ts
  | [], _, _, _ => trivial
  | _ :: _, _, _, ⟨h, hs⟩ => ⟨fun ht => (h ht).toDT, hs.toDT⟩

/-- **The callees at their running offsets, within their bounds**: `kidsFromInT_of_kidsDT` with
the total at most `kidsBoundL`. -/
theorem kidsFromInT_of_kidsDTB (κ : ℕ) : ∀ (ks : List Kid) (Ts : List (Tree → Prop)) (Bs : List ℕ),
    KidsDTB fs cert κ ks Ts Bs → ∀ b : ℕ,
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), N ≤ kidsBoundL fs ks Bs ∧
      OutsOk ks outs ∧ Within L b N ∧ DisjL L ∧ OutsIn ks outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop), CallsMatch σ cs ks outs →
        LowDef κ rd → MemL rd L → MemL rd (Kid.lins ks) → RegionsOk R Dacc ks outs →
        KidsFromInT coreProgram fs cert rd σ R Dacc cs Ts b N (fun i => Dacc i ∨ outRegion ks outs i)
  | [], _, _, _, b => ⟨0, [], [], le_rfl, trivial, fun _ h => by simp at h, disj_nil, trivial,
      fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | k :: ks, Ts, Bs, hok, b => by
    by_cases ht : k.taken = true
    · obtain ⟨n, Lown, rets, Lout, hnB, hout, hw, hd, hrel⟩ := hok.1 ht b
      obtain ⟨N, L, outs, hNB, ho, hW, hD, hI, hK⟩ :=
        kidsFromInT_of_kidsDTB κ ks Ts.tail Bs.tail hok.2 (b + n)
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
        kidsFromInT_of_kidsDTB κ ks Ts.tail Bs.tail hok.2 (b + fs k.f)
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

/-! ## Pure functions and leaves -/

/-- **A pure function loading the caller's words, within `B`**: `completeAtD_of_relIn`, its size
the words of a valid tree of it at `args` (or `0` when no memory holds the caller's words). -/
theorem completeAtDTB_of_relIn {S : List String} (hS : coreProgram.PureIn S) {g : String}
    (hg : g ∈ S) {κ : ℕ} {Lin : Layout} {args rets : List E} {B : ℕ}
    (hB : ∀ (rd : Reader) (t : Tree) (rets' : List E), t.name = g →
      t.Valid coreProgram rd args rets' → t.BufsOk coreProgram → t.total fs ≤ B)
    (h : ∀ rd, LowDef κ rd → MemL rd Lin → coreProgram.RelIn rd (RegionL Lin) g args rets) :
    CompleteAtDTB fs cert κ g Lin args (Returns rets) (fun _ => True) B := by
  intro fp
  classical
  by_cases hex : ∃ rd1, LowDef κ rd1 ∧ MemL rd1 Lin
  swap
  · refine ⟨0, [], rets, [], Nat.zero_le _, ⟨rfl, rfl⟩, by simp [Within], disj_nil,
      fun rd hl hL => absurd ⟨rd, hl, ?_⟩ hex⟩
    simpa using hL
  obtain ⟨rd1, hl1, hL1⟩ := hex
  obtain ⟨t, hn, hv, hb, hlr⟩ := h _ (Lift.lowLin_low (Lin := Lin) hl1) (Lift.lowLin_memL hL1)
  refine ⟨t.total fs, [], rets, [], hB _ t rets hn hv hb, ⟨rfl, rfl⟩, by simp [Within], disj_nil,
    fun rd hl hL => ?_⟩
  have hL' : MemL rd Lin := by simpa using hL
  have hr := relAtIn_transfer (fs := fs) (cert := cert) (D := fun _ => False) (fp := fp)
    coreProgram_fresh hn hv hb (placed_of_pure hS t hv hb (hn ▸ hg) _)
    (loadsIn_of_loadsR t _ _ hlr) (fun _ h => h.elim) rd
    (fun i hi => hi.elim (fun hi => ?_) fun hd => (not_data_of_pure hS t hv hb (hn ▸ hg) _ i hd).elim)
    (fun A hA => ?_)
  · refine (relAtIn_dmono hr fun i hi => ?_).relAtInT
    obtain ⟨q, hq, _⟩ := hi; simp at hq
  · rw [Lift.lowLin, B1.Main.restrict_of ⟨i, rfl, Or.inl hi⟩, B1.Main.memL_agree hL' hL1 i hi]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hA
    obtain ⟨i, rfl, hi | hi⟩ := B1.Main.restrict_supp' rd1 _ _ _ hv
    · rw [B1.Main.memL_agree hL' hL1 i hi, ← B1.Main.restrict_of (rd := rd1)
        (S := fun i => RegionL Lin i ∨ i < 2 ^ κ) ⟨i, rfl, Or.inl hi⟩]
      exact Option.isSome_iff_exists.mpr ⟨v, hv⟩
    · exact hl i hi

end
end LeanVM.Guest.B1
