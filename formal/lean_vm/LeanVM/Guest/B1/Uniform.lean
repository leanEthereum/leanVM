/-
  LeanVM.Guest.B1.Uniform

  The uniform placed form of a function's completeness (`CompleteAt`), its composition along a
  caller's calls, and its lift from the `Rel`-level completeness of pure functions.
-/

module

public import LeanVM.Guest.B1.Main.Restrict
public import LeanVM.Guest.Memory.Retemp
public import LeanVM.Guest.Memory.GuestFresh
public import LeanVM.Guest.Memory.GuestWf

/-!
# Uniform placed completeness

`CompleteAt fs cert f Lin args Out`: at every frame pointer `fp`, one size `n`, one layout `Lown`
of `f`'s own words and one result (`rets` and the layout `Lout` of the buffers `f` returns,
satisfying `Out`) serve every memory holding `Lout ++ Lown` and the caller's words `Lin`:
`f` holds of `args` and `rets` by a tree placed at `fp`, of `n` words, loading from its own data
or from `Lin`, its data containing `Lout`. Both layouts lie in `[fp, fp + n)` (`Within`), so a
caller's honest memory can hold them with its own.

* `kidsFromIn_of_kids`: the callees of a caller (`Kid`: callee, taken or not, arguments, the words
  it reads, what it returns), each `CompleteAt` and placed at the running offsets from `b`, give
  `KidsFromIn` on every memory holding their layouts, the size and layouts chosen first;
* `completeAt_of_rel_pure`: a function of a pure set whose relation holds on every memory holding
  `Lin` is `CompleteAt` with fixed returns and no buffers.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- The layout lies in `[b, b + n)`. -/
def Within (L : Layout) (b n : ℕ) : Prop := ∀ q ∈ L, b ≤ q.1 ∧ q.1 + q.2.length ≤ b + n

/-- The memory is defined at the addresses below `2^k`, where range checks `log x < K ≤ 2^k`
read (any memory image of at least `2^k` words). -/
def LowDef (k : ℕ) (rd : Reader) : Prop := ∀ i < 2 ^ k, (rd (gpow i)).isSome

theorem LowDef.mono {k k' : ℕ} {rd : Reader} (h : LowDef k rd) (hk : k' ≤ k) : LowDef k' rd :=
  fun i hi => h i (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by decide) hk))

/-- **`f` is complete at every frame pointer, uniformly in the memory.** -/
def CompleteAt (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String) (Lin : Layout)
    (args : List E) (Out : List E → Layout → Prop) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ ∀ rd, LowDef k rd → MemL rd (Lout ++ Lown ++ Lin) →
      RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL Lout) fp n f args rets

/-- What a function returning `rets` and no buffer returns. -/
def Returns (rets : List E) : List E → Layout → Prop := fun r L => r = rets ∧ L = []

/-- **`f` is complete on every precondition `Pre` the caller's words `Lin` make true**, returning the
words `Pre` names and no buffer. -/
def CompleteRel (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String)
    (Pre : Reader → List E → List E → Prop) : Prop :=
  ∀ (args rets : List E) (Lin : Layout), (∀ rd, LowDef k rd → MemL rd Lin → Pre rd args rets) →
    CompleteAt fs cert k f Lin args (Returns rets)

/-! ## Composition -/

/-- A call of a caller: the callee, whether it is entered, its argument words, the caller's words
it reads, and what it returns. -/
structure Kid where
  f : String
  taken : Bool
  args : List E
  Lin : Layout
  Out : List E → Layout → Prop

/-- The words the callees read. -/
def Kid.lins (ks : List Kid) : Layout := ks.flatMap (·.Lin)

/-- The buffers the entered callees return. -/
def outRegion : List Kid → List (List E × Layout) → ℕ → Prop
  | k :: ks, o :: os => fun i => (k.taken = true ∧ RegionL o.2 i) ∨ outRegion ks os i
  | _, _ => fun _ => False

/-- Each entered callee reads within the caller's region `R`, the data `Dacc` claimed before the
callees, and the buffers the earlier callees return. -/
def RegionsOk (R : ℕ → Prop) : (ℕ → Prop) → List Kid → List (List E × Layout) → Prop
  | Dacc, k :: ks, o :: os => (k.taken = true → ∀ i, RegionL k.Lin i → R i ∨ Dacc i) ∧
      RegionsOk R (fun i => Dacc i ∨ (k.taken = true ∧ RegionL o.2 i)) ks os
  | _, _, _ => True

/-- The frames match the callees and their results. -/
def CallsMatch (σ : Val) : List Call → List Kid → List (List E × Layout) → Prop
  | c :: cs, k :: ks, o :: os => c.f = k.f ∧ c.taken = k.taken ∧
      (k.taken = true → c.args.map σ = k.args ∧ c.rets.map σ = o.1) ∧ CallsMatch σ cs ks os
  | [], [], [] => True
  | _, _, _ => False

/-- The results of the callees satisfy their `Out`. -/
def OutsOk : List Kid → List (List E × Layout) → Prop
  | k :: ks, o :: os => (k.taken = true → k.Out o.1 o.2) ∧ OutsOk ks os
  | [], [] => True
  | _, _ => False

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem CompleteAt.mono {k k' : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} (h : CompleteAt fs cert k' f Lin args Out) (hk : k' ≤ k) :
    CompleteAt fs cert k f Lin args Out := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, fun rd hl hm => hr rd (hl.mono hk) hm⟩


theorem kidsFromIn_dend {rd : Reader} {σ : Val} {R : ℕ → Prop} :
    ∀ (cs : List Call) (Dacc : ℕ → Prop) (b n : ℕ) {D D' : ℕ → Prop}, (∀ i, D' i → D i) →
      KidsFromIn coreProgram fs cert rd σ R Dacc cs b n D →
      KidsFromIn coreProgram fs cert rd σ R Dacc cs b n D'
  | [], _, _, _, _, _, hD, ⟨hn, h⟩ => ⟨hn, fun i hi => h i (hD i hi)⟩
  | _ :: cs, _, _, _, _, _, hD, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩ =>
      ⟨m, n', Rk, Dk, hn, hR, hc, kidsFromIn_dend cs _ _ _ hD hk⟩

theorem within_append {L L' : Layout} {b n : ℕ} :
    Within (L ++ L') b n ↔ Within L b n ∧ Within L' b n := by
  simp only [Within, List.mem_append]
  exact ⟨fun h => ⟨fun q hq => h q (Or.inl hq), fun q hq => h q (Or.inr hq)⟩,
    fun h q hq => hq.elim (h.1 q) (h.2 q)⟩

theorem Within.mono {L : Layout} {b n b' n' : ℕ} (h : Within L b n) (h1 : b' ≤ b)
    (h2 : b + n ≤ b' + n') : Within L b' n' := fun q hq => by
  have := h q hq; omega

/-- **The callees at their running offsets**: from `b`, one total `N`, one layout and one result
per callee serve every memory holding the layouts and the words the callees read. -/
theorem kidsFromIn_of_kids (κ : ℕ) : ∀ (ks : List Kid),
    (∀ k ∈ ks, k.taken = true → CompleteAt fs cert κ k.f k.Lin k.args k.Out) → ∀ b : ℕ,
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), OutsOk ks outs ∧ Within L b N ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop), CallsMatch σ cs ks outs →
        LowDef κ rd → MemL rd L → MemL rd (Kid.lins ks) → RegionsOk R Dacc ks outs →
        KidsFromIn coreProgram fs cert rd σ R Dacc cs b N (fun i => Dacc i ∨ outRegion ks outs i)
  | [], _, b => ⟨0, [], [], trivial, fun _ h => by simp at h, fun rd σ cs R Dacc hc _ _ _ _ => by
      match cs, hc with
      | [], _ => exact ⟨rfl, fun i hi => hi.elim id fun h => h.elim⟩⟩
  | k :: ks, hok, b => by
    by_cases ht : k.taken = true
    · obtain ⟨n, Lown, rets, Lout, hout, hw, hrel⟩ := hok k (by simp) ht b
      obtain ⟨N, L, outs, ho, hW, hK⟩ := kidsFromIn_of_kids κ ks (fun k' hk' => hok k' (by simp [hk']))
        (b + n)
      refine ⟨n + N, Lout ++ Lown ++ L, (rets, Lout) :: outs, ⟨fun _ => hout, ho⟩, ?_, ?_⟩
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
          · refine kidsFromIn_dend cs _ _ _ ?_ (hK rd σ cs R _ hc hlow hL2 hLs ?_)
            · intro i hi
              rcases hi with hi | ⟨_, hi⟩ | hi
              · exact Or.inl (Or.inl hi)
              · exact Or.inl (Or.inr ⟨by rw [hct]; exact ht, hi⟩)
              · exact Or.inr hi
            · simpa [hct] using hR2
    · obtain ⟨N, L, outs, ho, hW, hK⟩ := kidsFromIn_of_kids κ ks (fun k' hk' => hok k' (by simp [hk']))
        (b + fs k.f)
      refine ⟨fs k.f + N, L, ([], []) :: outs, ⟨fun h => absurd h ht, ho⟩,
        hW.mono (by omega) (by omega), ?_⟩
      intro rd σ cs R Dacc hc hlow hL hLin hRg
      match cs, hc with
      | c :: cs, ⟨hf, hct, _, hc⟩ =>
        simp only [Kid.lins, List.flatMap_cons] at hLin
        refine ⟨fs k.f, N, fun _ => False, fun _ => False, rfl, fun _ h => h.elim, ?_, ?_⟩
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

/-! ## Pure functions -/

theorem relAtIn_dmono {rd : Reader} {R D D' : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    (h : RelAtIn coreProgram fs cert rd R D fp n f args rets) (hD : ∀ i, D' i → D i) :
    RelAtIn coreProgram fs cert rd R D' fp n f args rets :=
  let ⟨t, hn, hv, hb, hp, ht, hl, hd⟩ := h
  ⟨t, hn, hv, hb, hp, ht, hl, fun i hi => hd i (hD i hi)⟩

/-- **A pure function complete on every memory holding `Lin` is `CompleteAt`**, returning `rets`
and no buffer. -/
theorem completeAt_of_rel_pure {S : List String} (hS : coreProgram.PureIn S) {g : String}
    (hg : g ∈ S) {Lin : Layout} {args rets : List E}
    (h : ∀ rd, MemL rd Lin → coreProgram.Rel rd g args rets) (k : ℕ) :
    CompleteAt fs cert k g Lin args (Returns rets) := by
  intro fp
  classical
  by_cases hex : ∃ rd1, MemL rd1 Lin
  swap
  · exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], fun rd _ hL => absurd ⟨rd, by simpa using hL⟩ hex⟩
  obtain ⟨rd1, h1⟩ := hex
  set rd0 := Main.restrict rd1 (RegionL Lin)
  have h0 : MemL rd0 Lin := Main.memL_restrict h1 fun i hi => hi
  have hsupp := Main.restrict_supp' rd1 (RegionL Lin)
  obtain ⟨n, hn⟩ := relAtIn_uniform_pure (fs := fs) (cert := cert) coreProgram_fresh hS hg
    (Main.relIn_of_rel_supp coreProgram_wf hsupp (h rd0 h0))
  refine ⟨n, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], fun rd _ hL => ?_⟩
  have hL' : MemL rd Lin := by simpa using hL
  refine relAtIn_dmono (hn fp rd (fun i hi => ?_) (fun A hA => ?_)) (fun i hi => ?_)
  · rw [Main.memL_agree hL' h1 i hi, Main.restrict_of ⟨i, rfl, hi⟩]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hA
    obtain ⟨i, rfl, hi⟩ := hsupp _ _ hv
    rw [Main.memL_agree hL' h1 i hi, ← Main.restrict_of (rd := rd1) (S := RegionL Lin) ⟨i, rfl, hi⟩, hv]
    rfl
  · obtain ⟨q, hq, _⟩ := hi; simp at hq

end
end LeanVM.Guest.B1
