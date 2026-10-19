/-
  LeanVM.Guest.B1.Uniform

  The uniform placed form of a function's completeness (`CompleteAt`), its composition along a
  caller's calls, and its lift from the `Rel`-level completeness of pure functions.
-/

module

public import LeanVM.Guest.B1.Main.Restrict
public import LeanVM.Guest.B1.Main.Straight
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

/-! ## Range checks on a memory defined below `2^k` -/

/-- A range check's auxiliary words for `x = g^e` against `g^(K-1)`: the complement `g^(K-1-e)`
and the words the memory holds at both. -/
noncomputable def rcLow (rd : Reader) (e K : ℕ) : E × E × E :=
  (ofK (gpow (K - 1 - e)), (rd (gpow e)).getD 0, (rd (gpow (K - 1 - e))).getD 0)

theorem loadHolds_low {k : ℕ} {rd : Reader} (hl : LowDef k rd) {i : ℕ} (hi : i < 2 ^ k) :
    LoadHolds rd (ofK (gpow i)) 0 ((rd (gpow i)).getD 0) := by
  refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
  rw [Main.addr_ofK, Nat.add_zero]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hl i hi)
  rw [hv]; rfl

/-- **A range check passes** on a memory defined below `2^k`, for `x = g^e`, `e < K ≤ 2^k`. -/
theorem rc_complete_low {k : ℕ} {rd : Reader} (hl : LowDef k rd) {K e : ℕ} (hK : K ≤ 2 ^ k)
    (he : e < K) :
    LoadHolds rd (ofK (gpow e)) 0 (rcLow rd e K).2.1 ∧
      ofK (gpow (K - 1)) = ofK (gpow e) * (rcLow rd e K).1 ∧
      LoadHolds rd (rcLow rd e K).1 0 (rcLow rd e K).2.2 := by
  refine ⟨loadHolds_low hl (by omega), ?_, loadHolds_low hl (by omega)⟩
  rw [rcLow, ← ofK_mul, gpow, gpow, ← pow_add]
  congr 2
  omega

/-! ## A function's own buffers -/

/-- `HeapBuf`s of the given sizes from `b`, holding `cs`. -/
def bufL (b : ℕ) (sizes : List ℕ) (cs : List (List E)) : Layout := (bases b sizes).zip cs

theorem bufL_region : ∀ (b : ℕ) (sizes : List ℕ) (cs : List (List E)),
    List.Forall₂ (fun c s => c.length ≤ s) cs sizes → ∀ i, RegionL (bufL b sizes cs) i →
      ∃ q ∈ sizes.zip (bases b sizes), q.2 ≤ i ∧ i < q.2 + q.1
  | _, [], _, _, _, ⟨_, hq, _⟩ => by simp [bufL, bases] at hq
  | b, s :: sizes, [], h, _, _ => by cases h
  | b, s :: sizes, c :: cs, h, i, ⟨q, hq, h1, h2⟩ => by
    obtain ⟨hc, h⟩ := List.forall₂_cons.mp h
    simp only [bufL, bases, List.zip_cons_cons, List.mem_cons] at hq ⊢
    rcases hq with rfl | hq
    · exact ⟨(s, b), Or.inl rfl, h1, by simp only at h2 ⊢; omega⟩
    · obtain ⟨q', hq', h1', h2'⟩ := bufL_region (b + s) sizes cs h i ⟨q, hq, h1, h2⟩
      exact ⟨q', Or.inr hq', h1', h2'⟩

theorem bufL_within : ∀ (b : ℕ) (sizes : List ℕ) (cs : List (List E)),
    List.Forall₂ (fun c s => c.length ≤ s) cs sizes → Within (bufL b sizes cs) b sizes.sum
  | _, [], _, _ => fun q hq => by simp [bufL, bases] at hq
  | b, s :: sizes, [], h => by cases h
  | b, s :: sizes, c :: cs, h => by
    obtain ⟨hc, h⟩ := List.forall₂_cons.mp h
    intro q hq
    simp only [bufL, bases, List.zip_cons_cons, List.mem_cons] at hq
    rcases hq with rfl | hq
    · simp only [List.sum_cons]; omega
    · have := bufL_within (b + s) sizes cs h q hq
      simp only [List.sum_cons]; omega

/-- **A function calling nothing is complete** when, at every frame pointer and on every memory
holding its buffers' honest words `own fp` and the caller's words, a valuation walks its body with
no call and no `frameAddr`, its `HeapBuf` hints of the sizes `sizes` from `fp + fs f`, loading from
its buffers or `Lin`. -/
theorem completeAt_leaf {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hl : coreProgram.loop f = false) (k : ℕ) (Lin : Layout) (args rets : List E) (sizes : List ℕ)
    (own : ℕ → List (List E)) (hown : ∀ fp, List.Forall₂ (fun c s => c.length ≤ s) (own fp) sizes)
    (hσ : ∀ fp rd, LowDef k rd → MemL rd (bufL (fp + fs f) sizes (own fp)) → MemL rd Lin →
      ∃ (σ : Val) (es : List Ev) (vs : List V), fn.params.map σ = args ∧
        walk σ fn.body = .ret es vs ∧ vs.map σ = rets ∧ (∀ e ∈ es, e.Holds rd σ) ∧
        calls es = [] ∧ addrs es = [] ∧ allocs σ es = sizes ∧
        (allocDsts es).map σ = (bases (fp + fs f) sizes).map (fun b => ofK (gpow b)) ∧
        ∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧
          (RegionL (bufL (fp + fs f) sizes (own fp)) i ∨ RegionL Lin i)) :
    CompleteAt fs cert k f Lin args (Returns rets) := by
  intro fp
  refine ⟨fs f + sizes.sum, bufL (fp + fs f) sizes (own fp), rets, [], ⟨rfl, rfl⟩,
    by simpa using (bufL_within _ _ _ (hown fp)).mono (by omega) (by omega), fun rd hlow hL => ?_⟩
  simp only [List.nil_append] at hL
  obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
  obtain ⟨σ, es, vs, hp, hw, hr, hes, hc, ha, hal, hbuf, hload⟩ := hσ fp rd hlow hL1 hL2
  have h := relAtIn_of_walk (P := coreProgram) (fs := fs) (cert := cert) (R := RegionL Lin)
    (D := RegionL []) (Dk := fun _ => False) (N := 0) (fp := fp) coreProgram_wf hf (Or.inl hl) hp hw
    hr hes (by rw [hal]; exact hbuf) (by rw [ha]; simp) (by rw [hc]; exact ⟨rfl, fun _ h => h⟩) (fun A hA => ?_)
    (fun i hi => by obtain ⟨q, hq, _⟩ := hi; simp at hq)
  · rw [hal] at h; simpa using h
  · obtain ⟨i, hi, h | h⟩ := hload A hA
    · exact ⟨i, hi, Or.inl (Or.inl (by rw [hal]; exact bufL_region _ _ _ (hown fp) i h))⟩
    · exact ⟨i, hi, Or.inr (Or.inl h)⟩

/-! ## Loads of a straight-line body -/

/-- A `load`: its pointer and offset. -/
def Stmt.loadS : Stmt → Option (V × ℕ)
  | .atom (.load _ p off) => some (p, off)
  | _ => none

theorem loadAddrs_straight (σ : Val) : ∀ pre : List Stmt, pre.all Main.Stmt.straight = true →
    loadAddrs σ (pre.flatMap (Main.slEvs σ)) =
      (pre.filterMap Stmt.loadS).map fun q => (σ q.1).limb 0 * gpow q.2
  | [], _ => rfl
  | s :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := loadAddrs_straight σ pre h.2
    simp only [loadAddrs, List.flatMap_cons, List.filterMap_append] at ih ⊢
    rw [ih]
    match s, h.1 with
    | .atom a, _ =>
      cases a <;> simp [Main.slEvs, Ev.loadAddr?, Stmt.loadS, List.filterMap_cons]
    | .call .., _ => simp [Main.slEvs, Ev.loadAddr?, Stmt.loadS, List.filterMap_cons]
    | .callIf c _ _, _ =>
      by_cases hc : σ c = 0 <;> simp [Main.slEvs, hc, Ev.loadAddr?, Stmt.loadS, List.filterMap_cons]

/-! ## Walks with a dispatch -/

theorem Out.pre_pre (es es' : List Ev) : ∀ o : Out, (o.pre es').pre es = o.pre (es ++ es')
  | .fall _ => by simp [Out.pre]
  | .ret _ _ => by simp [Out.pre]
  | .stuck => rfl

/-- **A straight-line prefix walks each statement**, then the rest. -/
theorem walk_pre_straight (σ : Val) (rest : List Stmt) : ∀ pre : List Stmt,
    pre.all Main.Stmt.straight = true → walk σ (pre ++ rest) = (walk σ rest).pre (pre.flatMap (Main.slEvs σ))
  | [], _ => by simp only [List.nil_append, List.flatMap_nil]; cases walk σ rest <;> rfl
  | s :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.cons_append, walk, walk_pre_straight σ rest pre h.2, Main.walk1_straight σ s h.1, Out.seq,
      Out.pre_pre, List.flatMap_cons]

/-- **A dispatch on `g^j` enters callee `j`**, the first arm with that power. -/
theorem pick_eq (σ : Val) (x : V) (args rets : List V) : ∀ (fs : List String) (i j : ℕ),
    i ≤ j → (hj : j - i < fs.length) → j < 2 ^ 64 - 1 → σ x = ofK (gpow j) →
      pick σ x args rets i fs = .fall [.call fs[j - i] args rets]
  | [], _, _, _, hj, _, _ => absurd hj (by simp)
  | f :: fs, i, j, hij, hj, hj64, hx => by
    unfold pick
    by_cases he : i = j
    · subst he; simp [hx]
    · have hne : σ x ≠ ofK (gpow i) := by
        rw [hx]; intro h
        have := gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
          (ofK_injective h)
        omega
      simp only [hne, ↓reduceIte]
      rw [pick_eq σ x args rets fs (i + 1) j (by omega) (by simp at hj ⊢; omega) hj64 hx]
      congr 3
      have e : j - i = (j - (i + 1)) + 1 := by omega
      simp only [e, List.getElem_cons_succ]

/-! ## Callees in batches -/

theorem kidsFromIn_dacc {rd : Reader} {σ : Val} {R : ℕ → Prop} :
    ∀ (cs : List Call) (Dacc Dacc' : ℕ → Prop) (b n : ℕ) (D : ℕ → Prop), (∀ i, Dacc i → Dacc' i) →
      KidsFromIn coreProgram fs cert rd σ R Dacc cs b n D →
      KidsFromIn coreProgram fs cert rd σ R Dacc' cs b n D
  | [], _, _, _, _, _, h, ⟨hn, hD⟩ => ⟨hn, fun i hi => h i (hD i hi)⟩
  | _ :: cs, _, _, _, _, _, h, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩ =>
      ⟨m, n', Rk, Dk, hn, fun i hi => (hR i hi).imp_right (h i), hc,
        kidsFromIn_dacc cs _ _ _ _ _ (fun i hi => hi.imp_left (h i)) hk⟩

/-- **Two batches of callees in sequence**: the second from any data that contains the first's
claims. -/
theorem kidsFromIn_append {rd : Reader} {σ : Val} {R : ℕ → Prop} :
    ∀ (cs1 cs2 : List Call) (Dacc : ℕ → Prop) (b n1 n2 : ℕ) (D1 D : ℕ → Prop),
      KidsFromIn coreProgram fs cert rd σ R Dacc cs1 b n1 D1 →
      (∀ Dacc' : ℕ → Prop, (∀ i, D1 i → Dacc' i) →
        KidsFromIn coreProgram fs cert rd σ R Dacc' cs2 (b + n1) n2 D) →
      KidsFromIn coreProgram fs cert rd σ R Dacc (cs1 ++ cs2) b (n1 + n2) D
  | [], cs2, Dacc, b, n1, n2, D1, D, ⟨hn, hD⟩, h2 => by
    subst hn; simpa using h2 Dacc hD
  | _ :: cs1, cs2, Dacc, b, n1, n2, D1, D, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩, h2 =>
    ⟨m, n' + n2, Rk, Dk, by omega, hR, hc,
      kidsFromIn_append cs1 cs2 _ (b + m) n' n2 D1 D hk fun Dacc' h => by
        rw [show b + m + n' = b + n1 by omega]; exact h2 Dacc' h⟩

end
end LeanVM.Guest.B1
