/-
  LeanVM.Guest.Budget.Kids

  A node's callees' weights and words, bounded call by call: an entered call by its callee's
  bound on its valid trees at the call's arguments, a call not entered by its phantom.
-/

module

public import LeanVM.Guest.Memory.Size
public import LeanVM.Guest.B1.Main.KidsT

/-!
# The callees' weights and words

`kids_weight_le`, `kids_total_le`: for the callees `ks` of the calls `cs` (`Tree.KidsValid`), the
weight is at most the sum over the entered calls of a bound `W c` on their callees' valid trees at
the call's arguments, and the words at most the sum of a bound `T c` over the entered calls and of
the callee's frame over the others (a phantom allocates its frame).
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- The bounds of the entered calls. -/
def callsW (W : Call → ℕ) (cs : List Call) : ℕ := (cs.map fun c => if c.taken then W c else 0).sum

/-- The words of the calls: a bound for an entered call, the callee's frame for the others. -/
def callsT (fs : String → ℕ) (T : Call → ℕ) (cs : List Call) : ℕ :=
  (cs.map fun c => if c.taken then T c else fs c.f).sum

variable {P : Core.Program} {rd : Reader} {σ : Val}

/-! ## With the callees' predicates

The same, a call's bound holding of its callee's valid trees that satisfy the call's predicate
(`KidsT`: an entered call's callee satisfies its predicate). -/

theorem kids_weight_leT (ω : String → ℕ) (W : Call → ℕ) :
    ∀ (cs : List Call) (Ts : List (Tree → Prop)) (ks : List Tree), Tree.KidsValid P rd σ cs ks →
      Tree.BufsOkKids P ks → cs.length ≤ Ts.length → KidsT cs Ts ks →
      (∀ c T, (c, T) ∈ cs.zip Ts → c.taken = true → ∀ (t : Tree) (rets : List E), t.name = c.f →
        t.Valid P rd (c.args.map σ) rets → t.BufsOk P → T t → t.weight ω ≤ W c) →
      Tree.weightKids ω ks ≤ callsW W cs
  | [], _, [], _, _, _, _, _ => by simp [Tree.weightKids, callsW]
  | [], _, _ :: _, hk, _, _, _, _ => hk.elim
  | _ :: _, _, [], hk, _, _, _, _ => hk.elim
  | _ :: _, [], _ :: _, _, _, hl, _, _ => by simp at hl
  | c :: cs, T :: Ts, k :: ks, ⟨hn, hk, hks⟩, ⟨hb, hbs⟩, hl, ⟨hT, hTs⟩, hB => by
    have ih := kids_weight_leT ω W cs Ts ks hks hbs (by simpa using hl) hTs
      fun c' T' hc' => hB c' T' (by simp [hc'])
    rw [Tree.weightKids]
    unfold callsW at ih ⊢
    rw [List.map_cons, List.sum_cons]
    by_cases ht : c.taken = true
    · simp only [ht, ↓reduceIte] at hk ⊢
      exact Nat.add_le_add (hB c T (by simp) ht k _ hn hk hb (hT ht)) ih
    · simp only [Bool.not_eq_true] at ht
      simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk ⊢
      obtain ⟨⟨f, σ', rfl⟩, -⟩ := hk
      rw [Tree.weight]
      omega

theorem kids_total_leT (fs : String → ℕ) (T : Call → ℕ) :
    ∀ (cs : List Call) (Ts : List (Tree → Prop)) (ks : List Tree), Tree.KidsValid P rd σ cs ks →
      Tree.BufsOkKids P ks → cs.length ≤ Ts.length → KidsT cs Ts ks →
      (∀ c Q, (c, Q) ∈ cs.zip Ts → c.taken = true → ∀ (t : Tree) (rets : List E), t.name = c.f →
        t.Valid P rd (c.args.map σ) rets → t.BufsOk P → Q t → t.total fs ≤ T c) →
      Tree.totalKids fs ks ≤ callsT fs T cs
  | [], _, [], _, _, _, _, _ => by simp [Tree.totalKids, callsT]
  | [], _, _ :: _, hk, _, _, _, _ => hk.elim
  | _ :: _, _, [], hk, _, _, _, _ => hk.elim
  | _ :: _, [], _ :: _, _, _, hl, _, _ => by simp at hl
  | c :: cs, Q :: Ts, k :: ks, ⟨hn, hk, hks⟩, ⟨hb, hbs⟩, hl, ⟨hT, hTs⟩, hB => by
    have ih := kids_total_leT fs T cs Ts ks hks hbs (by simpa using hl) hTs
      fun c' T' hc' => hB c' T' (by simp [hc'])
    rw [Tree.totalKids]
    unfold callsT at ih ⊢
    rw [List.map_cons, List.sum_cons]
    by_cases ht : c.taken = true
    · simp only [ht, ↓reduceIte] at hk ⊢
      exact Nat.add_le_add (hB c Q (by simp) ht k _ hn hk hb (hT ht)) ih
    · simp only [Bool.not_eq_true] at ht
      simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk ⊢
      obtain ⟨⟨f, σ', rfl⟩, -⟩ := hk
      simp only [Tree.name] at hn
      subst hn
      rw [Tree.total]
      omega

/-! ## A node -/

/-- A valid node's callees, at the calls `cs` its walk makes. -/
theorem node_kids {f : String} {bufs : List ℕ} {ks : List Tree} {args rets : List E} {cs : List Call}
    (hv : (Memory.Tree.node f σ bufs ks).Valid P rd args rets) (hb : (Memory.Tree.node f σ bufs ks).BufsOk P)
    (hc : ∀ fn es vs, P.find? f = some fn → walk σ fn.body = .ret es vs → calls es = cs) :
    Tree.KidsValid P rd σ cs ks ∧ Tree.BufsOkKids P ks := by
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv
  rw [hc fn es vs hf hw] at hk
  exact ⟨hk, hb.2⟩

/-- **A node's weight**: its frame's, and its callees' bounds call by call. -/
theorem node_weight_le (ω : String → ℕ) (W : Call → ℕ) (Ts : List (Tree → Prop)) {f : String}
    {bufs : List ℕ} {ks : List Tree} {args rets : List E} {cs : List Call}
    (hv : (Memory.Tree.node f σ bufs ks).Valid P rd args rets) (hb : (Memory.Tree.node f σ bufs ks).BufsOk P)
    (hc : ∀ fn es vs, P.find? f = some fn → walk σ fn.body = .ret es vs → calls es = cs)
    (hl : cs.length ≤ Ts.length) (hT : KidsT cs Ts ks)
    (hB : ∀ c T, (c, T) ∈ cs.zip Ts → c.taken = true → ∀ (t : Tree) (rets : List E), t.name = c.f →
      t.Valid P rd (c.args.map σ) rets → t.BufsOk P → T t → t.weight ω ≤ W c) :
    (Memory.Tree.node f σ bufs ks).weight ω ≤ ω f + callsW W cs := by
  obtain ⟨hk, hbk⟩ := node_kids hv hb hc
  rw [Tree.weight]
  exact Nat.add_le_add_left (kids_weight_leT ω W cs Ts ks hk hbk hl hT hB) _

/-- **A node's words**: its frame, its `HeapBuf`s, and its callees' bounds call by call. -/
theorem node_total_le (fs : String → ℕ) (T : Call → ℕ) (Ts : List (Tree → Prop)) {f : String}
    {bufs : List ℕ} {ks : List Tree} {args rets : List E} {cs : List Call}
    (hv : (Memory.Tree.node f σ bufs ks).Valid P rd args rets) (hb : (Memory.Tree.node f σ bufs ks).BufsOk P)
    (hc : ∀ fn es vs, P.find? f = some fn → walk σ fn.body = .ret es vs → calls es = cs)
    (hl : cs.length ≤ Ts.length) (hT : KidsT cs Ts ks)
    (hB : ∀ c Q, (c, Q) ∈ cs.zip Ts → c.taken = true → ∀ (t : Tree) (rets : List E), t.name = c.f →
      t.Valid P rd (c.args.map σ) rets → t.BufsOk P → Q t → t.total fs ≤ T c) :
    (Memory.Tree.node f σ bufs ks).total fs ≤ fs f + callsT fs T cs + bufs.sum := by
  obtain ⟨hk, hbk⟩ := node_kids hv hb hc
  rw [Tree.total]
  have := kids_total_leT fs T cs Ts ks hk hbk hl hT hB
  omega

/-! ## A node's honest shape

What a callee's completeness exposes of the tree it builds, for the budget: the node of `f` at a
valuation `σ` satisfying `Q` (the words its loops' ends and `HeapBuf` sizes are read from), its
walk's calls `cs σ`, its `HeapBuf`s `bs σ`, and its callees satisfying their predicates `Ts`
(`KidsT`: an entered call's callee satisfies its predicate). -/

/-- **A node's honest shape.** -/
def NodeHonest (P : Core.Program) (f : String) (Q : Val → Prop) (cs : Val → List Call)
    (bs : Val → List ℕ) (Ts : List (Tree → Prop)) (t : Tree) : Prop :=
  ∃ σ ks, t = .node f σ (bs σ) ks ∧ Q σ ∧
    (∀ fn es vs, P.find? f = some fn → walk σ fn.body = .ret es vs → calls es = cs σ) ∧
    (cs σ).length ≤ Ts.length ∧ KidsT (cs σ) Ts ks

/-- **A node of honest shape weighs at most** its frame and its callees' bounds. -/
theorem NodeHonest.weight_le {f : String} {Q : Val → Prop} {cs : Val → List Call}
    {bs : Val → List ℕ} {Ts : List (Tree → Prop)} {t : Tree} {args rets : List E}
    (ω : String → ℕ) (W : Val → Call → ℕ) (h : NodeHonest P f Q cs bs Ts t)
    (hv : t.Valid P rd args rets) (hb : t.BufsOk P)
    (hB : ∀ σ, Q σ → ∀ c T, (c, T) ∈ (cs σ).zip Ts → c.taken = true → ∀ (t : Tree) (rets : List E),
      t.name = c.f → t.Valid P rd (c.args.map σ) rets → t.BufsOk P → T t → t.weight ω ≤ W σ c) :
    ∃ σ, Q σ ∧ t.weight ω ≤ ω f + callsW (W σ) (cs σ) := by
  obtain ⟨σ, ks, rfl, hQ, hc, hl, hT⟩ := h
  exact ⟨σ, hQ, node_weight_le ω (W σ) Ts hv hb hc hl hT (hB σ hQ)⟩

/-- **A node of honest shape allocates at most** its frame, its `HeapBuf`s and its callees'
bounds. -/
theorem NodeHonest.total_le {f : String} {Q : Val → Prop} {cs : Val → List Call}
    {bs : Val → List ℕ} {Ts : List (Tree → Prop)} {t : Tree} {args rets : List E}
    (fs : String → ℕ) (T : Val → Call → ℕ) (h : NodeHonest P f Q cs bs Ts t)
    (hv : t.Valid P rd args rets) (hb : t.BufsOk P)
    (hB : ∀ σ, Q σ → ∀ c R, (c, R) ∈ (cs σ).zip Ts → c.taken = true → ∀ (t : Tree) (rets : List E),
      t.name = c.f → t.Valid P rd (c.args.map σ) rets → t.BufsOk P → R t → t.total fs ≤ T σ c) :
    ∃ σ, Q σ ∧ t.total fs ≤ fs f + callsT fs (T σ) (cs σ) + (bs σ).sum := by
  obtain ⟨σ, ks, rfl, hQ, hc, hl, hT⟩ := h
  exact ⟨σ, hQ, node_total_le fs (T σ) Ts hv hb hc hl hT (hB σ hQ)⟩

/-! ## Bounds by position

The callees' bounds as a list aligned with the calls (`Ws[i]` for call `i`), the form a chain of
loop iterations takes (the tail call's bound is the next iterations'). -/

theorem kids_weight_leL (ω : String → ℕ) :
    ∀ (cs : List Call) (Ts : List (Tree → Prop)) (Ws : List ℕ) (ks : List Tree),
      Tree.KidsValid P rd σ cs ks → Tree.BufsOkKids P ks → KidsT cs Ts ks →
      cs.length ≤ Ts.length → cs.length ≤ Ws.length →
      (∀ i (hi : i < cs.length) (hT : i < Ts.length) (hW : i < Ws.length), cs[i].taken = true →
        ∀ (t : Tree) (rets : List E), t.name = cs[i].f → t.Valid P rd (cs[i].args.map σ) rets →
          t.BufsOk P → Ts[i] t → t.weight ω ≤ Ws[i]) →
      Tree.weightKids ω ks ≤ Ws.sum
  | [], _, Ws, [], _, _, _, _, _, _ => by simp [Tree.weightKids]
  | [], _, _, _ :: _, hk, _, _, _, _, _ => hk.elim
  | _ :: _, _, _, [], hk, _, _, _, _, _ => hk.elim
  | _ :: _, [], _, _ :: _, _, _, _, hl, _, _ => by simp at hl
  | _ :: _, _ :: _, [], _ :: _, _, _, _, _, hw, _ => by simp at hw
  | c :: cs, T :: Ts, w :: Ws, k :: ks, ⟨hn, hk, hks⟩, ⟨hb, hbs⟩, ⟨hT, hTs⟩, hl, hw, hB => by
    have ih := kids_weight_leL ω cs Ts Ws ks hks hbs hTs (by simpa using hl) (by simpa using hw)
      fun i hi hTi hWi => hB (i + 1) (by simpa using hi) (by simpa using hTi) (by simpa using hWi)
    rw [Tree.weightKids, List.sum_cons]
    refine Nat.add_le_add ?_ ih
    by_cases ht : c.taken = true
    · simp only [ht, ↓reduceIte] at hk
      exact hB 0 (by simp) (by simp) (by simp) ht k _ hn hk hb (hT ht)
    · simp only [Bool.not_eq_true] at ht
      simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk
      obtain ⟨⟨f, σ', rfl⟩, -⟩ := hk
      rw [Tree.weight]
      omega

theorem kids_total_leL (fs : String → ℕ) :
    ∀ (cs : List Call) (Ts : List (Tree → Prop)) (Ws : List ℕ) (ks : List Tree),
      Tree.KidsValid P rd σ cs ks → Tree.BufsOkKids P ks → KidsT cs Ts ks →
      cs.length ≤ Ts.length → cs.length ≤ Ws.length →
      (∀ i (hi : i < cs.length) (hW : i < Ws.length), cs[i].taken = false → fs cs[i].f ≤ Ws[i]) →
      (∀ i (hi : i < cs.length) (hT : i < Ts.length) (hW : i < Ws.length), cs[i].taken = true →
        ∀ (t : Tree) (rets : List E), t.name = cs[i].f → t.Valid P rd (cs[i].args.map σ) rets →
          t.BufsOk P → Ts[i] t → t.total fs ≤ Ws[i]) →
      Tree.totalKids fs ks ≤ Ws.sum
  | [], _, Ws, [], _, _, _, _, _, _, _ => by simp [Tree.totalKids]
  | [], _, _, _ :: _, hk, _, _, _, _, _, _ => hk.elim
  | _ :: _, _, _, [], hk, _, _, _, _, _, _ => hk.elim
  | _ :: _, [], _, _ :: _, _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, _ :: _, [], _ :: _, _, _, _, _, hw, _, _ => by simp at hw
  | c :: cs, T :: Ts, w :: Ws, k :: ks, ⟨hn, hk, hks⟩, ⟨hb, hbs⟩, ⟨hT, hTs⟩, hl, hw, hU, hB => by
    have ih := kids_total_leL fs cs Ts Ws ks hks hbs hTs (by simpa using hl) (by simpa using hw)
      (fun i hi hWi => hU (i + 1) (by simpa using hi) (by simpa using hWi))
      fun i hi hTi hWi => hB (i + 1) (by simpa using hi) (by simpa using hTi) (by simpa using hWi)
    rw [Tree.totalKids, List.sum_cons]
    refine Nat.add_le_add ?_ ih
    by_cases ht : c.taken = true
    · simp only [ht, ↓reduceIte] at hk
      exact hB 0 (by simp) (by simp) (by simp) ht k _ hn hk hb (hT ht)
    · simp only [Bool.not_eq_true] at ht
      simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk
      obtain ⟨⟨f, σ', rfl⟩, -⟩ := hk
      simp only [Tree.name] at hn
      subst hn
      rw [Tree.total]
      exact hU 0 (by simp) (by simp) ht

end
end LeanVM.Guest.Budget
