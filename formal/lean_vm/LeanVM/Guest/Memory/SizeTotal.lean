/-
  LeanVM.Guest.Memory.SizeTotal

  The words a call tree allocates, bounded by a weight: `total_le_weight`.
-/

module

public import LeanVM.Guest.Memory.Size

/-!
# Words from weights

An instance of `f` allocates its frame `fs f`, its `HeapBuf`s and, for each `callIf` it does
not take, a phantom of the callee's frame: what its path's events add to the frame is
`Ev.words`. A weight `ω` that bounds `fs f` plus that, on every path of every function of a set
`S` the paths' calls stay in (`LocLe`, `CallsIn`), bounds the words of a tree of a function of
`S` (`total_le_weight`), so `TotalLe` follows from `WeightLe` (`totalLe_of_weightLe`).

Both hypotheses follow from the syntax. `Stmt.blockWords` bounds the words of a block's paths
by `c + Σ fs gs`, independently of `fs`: a `HeapBuf(n)` costs `n`, a `callIf` its callee's frame,
a branch both sides; a dynamic `HeapBuf` has no bound (`none`). `Stmt.blockCallees` lists the functions a block can
call (`locLe_of_words`, `callsIn_of_callees`). A function whose paths call only itself (a loop
helper, or a leaf) weighs `ω f` per instance (`weight_self`), so its instances are counted by any
weight that is positive on it.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- The words an event adds to its instance's frame: a `HeapBuf`'s size, an untaken call's
frame. -/
noncomputable def Ev.words (fs : String → ℕ) (σ : Val) (e : Ev) : ℕ :=
  (e.alloc? σ).getD 0 + match e.call? with
    | some c => if c.taken then 0 else fs c.f
    | none => 0

/-- The frames of the untaken calls. -/
def skipWords (fs : String → ℕ) : List Call → ℕ
  | [] => 0
  | c :: cs => (if c.taken then 0 else fs c.f) + skipWords fs cs

theorem sum_words (fs : String → ℕ) (σ : Val) : ∀ es : List Ev,
    (es.map (Ev.words fs σ)).sum = (allocs σ es).sum + skipWords fs (calls es)
  | [] => rfl
  | e :: es => by
      have ih := sum_words fs σ es
      simp only [allocs, calls] at ih ⊢
      simp only [List.map_cons, List.sum_cons, List.filterMap_cons, Ev.words, ih]
      rcases e.alloc? σ with _ | n <;> rcases e.call? with _ | c <;>
        simp only [Option.getD_none, Option.getD_some, List.sum_cons, skipWords] <;> omega

/-- `fs f` and the words of a path bounded by `ω f`, for every function of `S`. -/
def LocLe (P : Core.Program) (fs ω : String → ℕ) (S : String → Prop) : Prop :=
  ∀ f, S f → ∀ fn, P.find? f = some fn → ∀ σ es vs, walk σ fn.body = .ret es vs →
    fs f + (es.map (Ev.words fs σ)).sum ≤ ω f

/-- The paths of the functions of `S` call only functions of `S`. -/
def CallsIn (P : Core.Program) (S : String → Prop) : Prop :=
  ∀ f, S f → ∀ fn, P.find? f = some fn → ∀ σ es vs, walk σ fn.body = .ret es vs →
    ∀ c ∈ calls es, S c.f

/-- `TotalLe` on the arguments satisfying `Pre`. -/
def TotalLeOn (P : Core.Program) (fs : String → ℕ) (f : String) (Pre : List E → Prop)
    (B : List E → ℕ) : Prop :=
  ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = f → Pre args → t.Valid P rd args rets →
    t.BufsOk P → t.total fs ≤ B args

section Total

variable {P : Core.Program} {fs ω : String → ℕ} {S : String → Prop} {rd : Reader}

mutual
/-- **A weight bounds the words.** -/
theorem total_le_weight (hl : LocLe P fs ω S) (hc : CallsIn P S) :
    ∀ (t : Tree) {args rets : List E}, S t.name → t.Valid P rd args rets → t.BufsOk P →
      t.total fs ≤ t.weight ω
  | .node f σ bufs kids, args, rets, hs, hv, hb => by
      obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv
      simp only [Tree.BufsOk] at hb
      obtain ⟨hbufs, hbk⟩ := hb
      have he : (Tree.node f σ bufs kids).events P = es := by
        simp only [Tree.events, Tree.name, Tree.val, hf, hw]
      have hloc := hl f hs fn hf σ es vs hw
      rw [sum_words] at hloc
      have hkk := totalKids_le_weight hl hc kids hk hbk (hc f hs fn hf σ es vs hw)
      rw [Tree.total, Tree.weight, hbufs, he]
      omega
  | .phantom .., _, _, _, hv, _ => hv.elim

theorem totalKids_le_weight (hl : LocLe P fs ω S) (hc : CallsIn P S) :
    ∀ (ks : List Tree) {σ : Val} {cs : List Call}, Tree.KidsValid P rd σ cs ks →
      Tree.BufsOkKids P ks → (∀ c ∈ cs, S c.f) →
      Tree.totalKids fs ks ≤ Tree.weightKids ω ks + skipWords fs cs
  | [], _, [], _, _, _ => by simp only [Tree.totalKids, Tree.weightKids, skipWords]; omega
  | [], _, _ :: _, hv, _, _ => hv.elim
  | _ :: _, _, [], hv, _, _ => hv.elim
  | k :: ks, σ, c :: cs, hv, hb, hs => by
      obtain ⟨hn, hk, hv'⟩ := hv
      simp only [Tree.BufsOkKids] at hb
      have ih := totalKids_le_weight hl hc ks hv' hb.2 fun c' hc' => hs c' (List.mem_cons_of_mem _ hc')
      rw [Tree.totalKids, Tree.weightKids, skipWords]
      by_cases ht : c.taken = true
      · simp only [ht, ↓reduceIte] at hk ⊢
        have := total_le_weight hl hc k (hn ▸ hs c List.mem_cons_self) hk hb.1
        omega
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk ⊢
        obtain ⟨⟨f', σ', rfl⟩, -⟩ := hk
        simp only [Tree.name] at hn
        rw [Tree.total, Tree.weight, hn]
        omega
end

/-- **TotalLe from WeightLe.** -/
theorem totalLe_of_weightLe (hl : LocLe P fs ω S) (hc : CallsIn P S) {f : String} (hf : S f)
    {B : List E → ℕ} (hw : WeightLe P ω f B) : TotalLe P fs f B :=
  fun rd t args rets hn hv hb => (total_le_weight hl hc t (hn ▸ hf) hv hb).trans (hw rd t args rets hn hv hb)

mutual
/-- **A function calling only itself weighs `ω f` per instance.** -/
theorem weight_self {f : String} (hc : CallsIn P (· = f)) :
    ∀ (t : Tree) {args rets : List E}, t.name = f → t.Valid P rd args rets →
      t.weight ω = ω f * t.weight (fun _ => 1)
  | .node g σ bufs kids, args, rets, hn, hv => by
      simp only [Tree.name] at hn
      subst hn
      obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv
      rw [Tree.weight, Tree.weight, weightKids_self hc kids hk (hc g rfl fn hf σ es vs hw)]
      ring
  | .phantom .., _, _, _, hv => hv.elim

theorem weightKids_self {f : String} (hc : CallsIn P (· = f)) :
    ∀ (ks : List Tree) {σ : Val} {cs : List Call}, Tree.KidsValid P rd σ cs ks → (∀ c ∈ cs, c.f = f) →
      Tree.weightKids ω ks = ω f * Tree.weightKids (fun _ => 1) ks
  | [], _, [], _, _ => by simp [Tree.weightKids]
  | [], _, _ :: _, hv, _ => hv.elim
  | _ :: _, _, [], hv, _ => hv.elim
  | k :: ks, σ, c :: cs, hv, hs => by
      obtain ⟨hn, hk, hv'⟩ := hv
      have ih := weightKids_self hc ks hv' fun c' hc' => hs c' (List.mem_cons_of_mem _ hc')
      rw [Tree.weightKids, Tree.weightKids, ih, Nat.mul_add]
      congr 1
      by_cases ht : c.taken = true
      · simp only [ht, ↓reduceIte] at hk
        exact weight_self hc k (hn.trans (hs c List.mem_cons_self)) hk
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk
        obtain ⟨⟨f', σ', rfl⟩, -⟩ := hk
        simp [Tree.weight]
end

/-- **The words of a function calling only itself**, by its instances: `n` instances at most
weigh `n * ω f`, at most `n * ω' f` words. -/
theorem total_le_self {f : String} {ω' : String → ℕ} (hl : LocLe P fs ω' (· = f))
    (hc : CallsIn P (· = f)) {t : Tree} {args rets : List E} (hn : t.name = f)
    (hv : t.Valid P rd args rets) (hb : t.BufsOk P) {n : ℕ} (hω : 0 < ω f)
    (hw : t.weight ω ≤ n * ω f) : t.total fs ≤ n * ω' f := by
  have h1 := total_le_weight hl hc t hn hv hb
  rw [weight_self (ω := ω') hc t hn hv] at h1
  rw [weight_self (ω := ω) hc t hn hv, Nat.mul_comm] at hw
  have := Nat.le_of_mul_le_mul_right hw hω
  calc t.total fs ≤ ω' f * t.weight (fun _ => 1) := h1
    _ ≤ ω' f * n := Nat.mul_le_mul_left _ this
    _ = n * ω' f := Nat.mul_comm _ _

end Total

/-! ## From the syntax -/

/-- The words an atom's event adds; `none` for a dynamic `HeapBuf`. -/
def atomWords? : Atom → Option ℕ
  | .hint (.alloc _ n) => some n
  | .hint (.allocDyn _ _) => none
  | _ => some 0

/-- Words `c + Σ fs gs` as `(c, gs)`: added, `none` if either is. -/
def Option.addW : Option (ℕ × List String) → Option (ℕ × List String) → Option (ℕ × List String)
  | some a, some b => some (a.1 + b.1, a.2 ++ b.2)
  | _, _ => none

mutual
/-- A bound `(c, gs)` on the words of a statement's paths, `c + Σ fs gs`: the `HeapBuf`s'
sizes, the `callIf`s' callees, both sides of a branch. -/
def Stmt.words : Stmt → Option (ℕ × List String)
  | .atom a => (atomWords? a).map fun n => (n, [])
  | .ite _ z n => Option.addW (Stmt.blockWords z) (Stmt.blockWords n)
  | .match_ _ arms => Stmt.armsWords arms
  | .callIf _ f _ => some (0, [f])
  | _ => some (0, [])

/-- A bound on the words of a block's paths. -/
def Stmt.blockWords : List Stmt → Option (ℕ × List String)
  | [] => some (0, [])
  | s :: ss => Option.addW (Stmt.words s) (Stmt.blockWords ss)

/-- A bound on the words of any arm's paths. -/
def Stmt.armsWords : List (List Stmt) → Option (ℕ × List String)
  | [] => some (0, [])
  | a :: as => Option.addW (Stmt.blockWords a) (Stmt.armsWords as)
end

/-- The words `(c, gs)` stands for. -/
def wordsVal (fs : String → ℕ) (w : ℕ × List String) : ℕ := w.1 + (w.2.map fs).sum

mutual
/-- The functions a statement can call. -/
def Stmt.callees : Stmt → List String
  | .ite _ z n => Stmt.blockCallees z ++ Stmt.blockCallees n
  | .match_ _ arms => Stmt.armsCallees arms
  | .call f _ _ => [f]
  | .callIf _ f _ => [f]
  | .dispatch _ fs _ _ => fs
  | _ => []

/-- The functions a block can call. -/
def Stmt.blockCallees : List Stmt → List String
  | [] => []
  | s :: ss => Stmt.callees s ++ Stmt.blockCallees ss

/-- The functions any arm can call. -/
def Stmt.armsCallees : List (List Stmt) → List String
  | [] => []
  | a :: as => Stmt.blockCallees a ++ Stmt.armsCallees as
end

section Syntax

variable {fs : String → ℕ} {σ : Val}

/-- The words of an outcome's events. -/
noncomputable def Out.words (fs : String → ℕ) (σ : Val) (o : Out) : ℕ := (o.evs.map (Ev.words fs σ)).sum

theorem Out.words_seq (o k : Out) : (o.seq k).words fs σ ≤ o.words fs σ + k.words fs σ := by
  rcases o with es | ⟨es, vs⟩ | _ <;> rcases k with es' | ⟨es', vs'⟩ | _ <;>
    simp [Out.seq, Out.pre, Out.words, Out.evs]

theorem Out.calls_seq {o k : Out} {c : Call} (h : c ∈ calls (o.seq k).evs) :
    c ∈ calls o.evs ∨ c ∈ calls k.evs := by
  rcases o with es | ⟨es, vs⟩ | _ <;> rcases k with es' | ⟨es', vs'⟩ | _ <;>
    simp_all [Out.seq, Out.pre, Out.evs, calls, List.filterMap_append]

theorem Out.words_pre_inK (c : V) (o : Out) : (o.pre [.inK c]).words fs σ = o.words fs σ := by
  rcases o with es | ⟨es, vs⟩ | _ <;> simp [Out.pre, Out.words, Out.evs, Ev.words, Ev.alloc?, Ev.call?]

theorem Out.calls_pre_inK (c : V) (o : Out) : calls (o.pre [.inK c]).evs = calls o.evs := by
  rcases o with es | ⟨es, vs⟩ | _ <;> simp [Out.pre, Out.evs, calls, Ev.call?, List.filterMap_cons]

theorem atom_words {a : Atom} {n : ℕ} (h : atomWords? a = some n) : (Ev.atom a).words fs σ = n := by
  cases a with
  | hint hh =>
      cases hh <;> simp_all [atomWords?, Ev.words, Ev.alloc?, Ev.call?]
  | _ => simp_all [atomWords?, Ev.words, Ev.alloc?, Ev.call?]

theorem pick_words {x : V} {args rets : List V} : ∀ (gs : List String) (j : ℕ),
    (pick σ x args rets j gs).words fs σ = 0 ∧ ∀ c ∈ calls (pick σ x args rets j gs).evs, c.f ∈ gs
  | [], _ => by simp [pick, Out.words, Out.evs, calls]
  | g :: gs, j => by
      unfold pick
      split_ifs
      · simp [Out.words, Out.evs, calls, Ev.words, Ev.alloc?, Ev.call?]
      · obtain ⟨h1, h2⟩ := pick_words gs (j + 1)
        exact ⟨h1, fun c hc => List.mem_cons_of_mem _ (h2 c hc)⟩

theorem Option.addW_eq {a b : Option (ℕ × List String)} {w : ℕ × List String}
    (h : Option.addW a b = some w) :
    ∃ x y, a = some x ∧ b = some y ∧ ∀ fs, wordsVal fs w = wordsVal fs x + wordsVal fs y := by
  rcases a with _ | x <;> rcases b with _ | y <;> simp only [Option.addW, reduceCtorEq] at h
  cases h
  refine ⟨x, y, rfl, rfl, fun fs => ?_⟩
  simp only [wordsVal, List.map_append, List.sum_append]
  omega

mutual
/-- **The words of a statement's path.** -/
theorem walk1_words : ∀ (s : Stmt) {w : ℕ × List String}, Stmt.words s = some w →
    (walk1 σ s).words fs σ ≤ wordsVal fs w
  | .atom a, w, h => by
      simp only [Stmt.words, Option.map_eq_some_iff] at h
      obtain ⟨n, hn, rfl⟩ := h
      simp [walk1, Out.words, Out.evs, atom_words hn, wordsVal]
  | .ite c z m, w, h => by
      simp only [Stmt.words] at h
      obtain ⟨x, y, hx, hy, he⟩ := Option.addW_eq h
      rw [walk1, Out.words_pre_inK, he]
      split_ifs
      · exact (walk_words z hx).trans (Nat.le_add_right _ _)
      · exact (walk_words m hy).trans (Nat.le_add_left _ _)
  | .match_ x arms, w, h => by
      simp only [Stmt.words] at h
      rw [walk1]
      exact walkArms_words x arms 0 h
  | .call .., w, _ => by simp [walk1, Out.words, Out.evs, Ev.words, Ev.alloc?, Ev.call?]
  | .callIf c f args, w, h => by
      simp only [Stmt.words, Option.some.injEq] at h
      subst h
      rw [walk1]
      split_ifs <;> simp [Out.words, Out.evs, Ev.words, Ev.alloc?, Ev.call?, wordsVal]
  | .dispatch x gs args rets, w, _ => by
      rw [walk1, (pick_words gs 0).1]; exact Nat.zero_le _
  | .ret _, w, _ => by simp [walk1, Out.words, Out.evs]

/-- **The words of a block's path.** -/
theorem walk_words : ∀ (ss : List Stmt) {w : ℕ × List String}, Stmt.blockWords ss = some w →
    (walk σ ss).words fs σ ≤ wordsVal fs w
  | [], w, h => by simp [walk, Out.words, Out.evs]
  | s :: ss, w, h => by
      simp only [Stmt.blockWords] at h
      obtain ⟨x, y, hx, hy, he⟩ := Option.addW_eq h
      rw [walk, he]
      exact (Out.words_seq _ _).trans (Nat.add_le_add (walk1_words s hx) (walk_words ss hy))

theorem walkArms_words (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) {w : ℕ × List String},
    Stmt.armsWords arms = some w → (walkArms σ x j arms).words fs σ ≤ wordsVal fs w
  | [], _, w, _ => by simp [walkArms, Out.words, Out.evs]
  | a :: as, j, w, h => by
      simp only [Stmt.armsWords] at h
      obtain ⟨u, v, hu, hv, he⟩ := Option.addW_eq h
      rw [he]
      unfold walkArms
      split_ifs
      · exact (walk_words a hu).trans (Nat.le_add_right _ _)
      · exact (walkArms_words x as (j + 1) hv).trans (Nat.le_add_left _ _)
end

mutual
/-- **A statement's path calls its callees.** -/
theorem walk1_callees : ∀ (s : Stmt) {c : Call}, c ∈ calls (walk1 σ s).evs → c.f ∈ Stmt.callees s
  | .atom a, c, h => by simp [walk1, Out.evs, calls, Ev.call?] at h
  | .ite b z m, c, h => by
      rw [walk1, Out.calls_pre_inK] at h
      simp only [Stmt.callees, List.mem_append]
      split_ifs at h
      · exact Or.inl (walk_callees z h)
      · exact Or.inr (walk_callees m h)
  | .match_ x arms, c, h => by
      rw [walk1] at h
      exact walkArms_callees x arms 0 h
  | .call f args rets, c, h => by
      simp only [walk1, Out.evs, calls, List.filterMap_cons, Ev.call?, List.filterMap_nil,
        List.mem_cons, List.not_mem_nil, or_false] at h
      subst h; simp [Stmt.callees]
  | .callIf b f args, c, h => by
      rw [walk1] at h
      split_ifs at h <;>
        simp only [Out.evs, calls, List.filterMap_cons, Ev.call?, List.filterMap_nil,
          List.mem_cons, List.not_mem_nil, or_false] at h <;> subst h <;> simp [Stmt.callees]
  | .dispatch x gs args rets, c, h => by
      rw [walk1] at h
      exact (pick_words (fs := fun _ => 0) gs 0).2 c h
  | .ret _, c, h => by simp [walk1, Out.evs, calls] at h

/-- **A block's path calls its callees.** -/
theorem walk_callees : ∀ (ss : List Stmt) {c : Call}, c ∈ calls (walk σ ss).evs →
    c.f ∈ Stmt.blockCallees ss
  | [], c, h => by simp [walk, Out.evs, calls] at h
  | s :: ss, c, h => by
      rw [walk] at h
      simp only [Stmt.blockCallees, List.mem_append]
      rcases Out.calls_seq h with h | h
      · exact Or.inl (walk1_callees s h)
      · exact Or.inr (walk_callees ss h)

theorem walkArms_callees (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) {c : Call},
    c ∈ calls (walkArms σ x j arms).evs → c.f ∈ Stmt.armsCallees arms
  | [], _, c, h => by simp [walkArms, Out.evs, calls] at h
  | a :: as, j, c, h => by
      unfold walkArms at h
      simp only [Stmt.armsCallees, List.mem_append]
      split_ifs at h
      · exact Or.inl (walk_callees a h)
      · exact Or.inr (walkArms_callees x as (j + 1) h)
end

end Syntax

/-- **`LocLe` from the syntax**: every function of `S` has a words bound `w` with
`fs f + wordsVal fs w ≤ ω f`. -/
theorem locLe_of_words {P : Core.Program} {fs ω : String → ℕ} {S : String → Prop}
    (h : ∀ f, S f → ∀ fn, P.find? f = some fn →
      ∃ w, Stmt.blockWords fn.body = some w ∧ fs f + wordsVal fs w ≤ ω f) :
    LocLe P fs ω S := by
  intro f hs fn hf σ es vs hw
  obtain ⟨w, hn, hle⟩ := h f hs fn hf
  have := walk_words (σ := σ) (fs := fs) fn.body hn
  rw [hw] at this
  exact (Nat.add_le_add_left this _).trans hle

/-- **`CallsIn` from the syntax.** -/
theorem callsIn_of_callees {P : Core.Program} {S : String → Prop}
    (h : ∀ f, S f → ∀ fn, P.find? f = some fn → ∀ g ∈ Stmt.blockCallees fn.body, S g) :
    CallsIn P S := by
  intro f hs fn hf σ es vs hw c hc
  have := walk_callees (σ := σ) fn.body (c := c) (by rw [hw]; exact hc)
  exact h f hs fn hf c.f this

end
end LeanVM.Guest.Memory
