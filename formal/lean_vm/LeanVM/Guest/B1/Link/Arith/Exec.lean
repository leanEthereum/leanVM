/-
  LeanVM.Guest.B1.Link.Arith.Exec

  A symbolic run of a list of core IR statements: each value's expression over the values it does
  not define and the memory words it loads, sound at every valuation satisfying the atoms.
-/

module

public import LeanVM.Guest.B1.Link.Arith.Norm
public import LeanVM.Guest.Core
public import LeanVM.Guest.Renumber

/-!
# Symbolic execution of the core IR

`execStmts cut ss`: walks the statements `ss`, giving each value `.n d` that an atom first defines
(a constant, a sum, a product, a copy, a load) its expression (`Trie`, keyed by `d`), unless
`cut d` keeps it a variable. The variables: value `n` is `vnX n`, the word at `(base value b,
offset o)` is `memX b o` (`o < 2^16`); `irEnv rd σ` gives them their values. A later atom on a
defined value (a store, a division's `mul`) constrains, defines nothing.

`exec_eval`: on a valuation where every atom of `ss` holds, every value is its expression's value
(`symOf`), an undefined one trivially.
-/

namespace LeanVM.Guest.B1.Link.Arith

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-! ## Tries -/

/-- A binary trie of expressions: node `k`'s children are `2k + 1` and `2k + 2`. -/
inductive Trie where
  | nil
  | node (v : Option Ex) (l r : Trie)

/-- The entry at `k`, within `f` levels. -/
def Trie.get : ℕ → Trie → ℕ → Option Ex
  | _, .nil, _ => none
  | 0, .node v _ _, k => if k = 0 then v else none
  | f + 1, .node v l r, k =>
    if k = 0 then v else if k % 2 = 1 then Trie.get f l (k / 2) else Trie.get f r (k / 2 - 1)

/-- The root and children of a trie, `nil`'s empty. -/
def Trie.parts : Trie → Option Ex × Trie × Trie
  | .nil => (none, .nil, .nil)
  | .node v l r => (v, l, r)

/-- A node whose child is `c`, the child matched first: the kernel evaluates the child before it
builds the node, so a run's tries hold no chain of pending updates. -/
def Trie.withLeft (v : Option Ex) (c r : Trie) : Trie :=
  match c with
  | .nil => .node v .nil r
  | .node a b d => .node v (.node a b d) r

def Trie.withRight (v : Option Ex) (l c : Trie) : Trie :=
  match c with
  | .nil => .node v l .nil
  | .node a b d => .node v l (.node a b d)

theorem Trie.withLeft_eq (v : Option Ex) (c r : Trie) : Trie.withLeft v c r = .node v c r := by
  cases c <;> rfl

theorem Trie.withRight_eq (v : Option Ex) (l c : Trie) : Trie.withRight v l c = .node v l c := by
  cases c <;> rfl

/-- The trie with `x` at `k`, within `f` levels (unchanged past them). -/
def Trie.set : ℕ → Trie → ℕ → Ex → Trie
  | 0, t, k, x => if k = 0 then .node (some x) t.parts.2.1 t.parts.2.2 else t
  | f + 1, t, k, x =>
    if k = 0 then .node (some x) t.parts.2.1 t.parts.2.2
    else if k % 2 = 1 then Trie.withLeft t.parts.1 (Trie.set f t.parts.2.1 (k / 2) x) t.parts.2.2
    else Trie.withRight t.parts.1 t.parts.2.1 (Trie.set f t.parts.2.2 (k / 2 - 1) x)

theorem Trie.get_nil (f k : ℕ) : Trie.get f .nil k = none := by cases f <;> rfl

theorem Trie.get_node_parts (f : ℕ) (t : Trie) (j : ℕ) :
    Trie.get (f + 1) (.node t.parts.1 t.parts.2.1 t.parts.2.2) j = Trie.get (f + 1) t j := by
  cases t with
  | nil =>
    simp only [Trie.parts, Trie.get]
    split_ifs <;> simp
  | node v l r => rfl

theorem Trie.get_parts_zero (t : Trie) (j : ℕ) :
    Trie.get 0 (.node t.parts.1 t.parts.2.1 t.parts.2.2) j = Trie.get 0 t j := by
  cases t with
  | nil => simp [Trie.parts, Trie.get]
  | node v l r => rfl

/-- A lookup after a store finds the stored entry or an old one. -/
theorem Trie.get_set : ∀ (f : ℕ) (t : Trie) (k : ℕ) (x : Ex) (j : ℕ) (e : Ex),
    Trie.get f (Trie.set f t k x) j = some e → (j = k ∧ e = x) ∨ Trie.get f t j = some e
  | 0, t, k, x, j, e, h => by
    simp only [Trie.set] at h
    split_ifs at h with hk
    · simp only [Trie.get] at h
      split_ifs at h with hj
      · exact Or.inl ⟨by omega, (Option.some.inj h).symm⟩
    · exact Or.inr h
  | f + 1, t, k, x, j, e, h => by
    simp only [Trie.set, Trie.withLeft_eq, Trie.withRight_eq] at h
    split_ifs at h with hk hodd
    · simp only [Trie.get] at h
      split_ifs at h with hj hjo
      · exact Or.inl ⟨by omega, (Option.some.inj h).symm⟩
      · right; rw [← Trie.get_node_parts]; simp only [Trie.get]; rw [ite_eq_right hj, ite_eq_left hjo]; exact h
      · right; rw [← Trie.get_node_parts]; simp only [Trie.get]; rw [ite_eq_right hj, ite_eq_right hjo]; exact h
    · simp only [Trie.get] at h
      split_ifs at h with hj hjo
      · right; rw [← Trie.get_node_parts]; simp only [Trie.get]; rw [ite_eq_left hj]; exact h
      · rcases Trie.get_set f _ _ x _ e h with ⟨hjk, rfl⟩ | h'
        · exact Or.inl ⟨by omega, rfl⟩
        · right; rw [← Trie.get_node_parts]; simp only [Trie.get]; rw [ite_eq_right hj, ite_eq_left hjo]; exact h'
      · right; rw [← Trie.get_node_parts]; simp only [Trie.get]; rw [ite_eq_right hj, ite_eq_right hjo]; exact h
    · simp only [Trie.get] at h
      split_ifs at h with hj hjo
      · right; rw [← Trie.get_node_parts]; simp only [Trie.get]; rw [ite_eq_left hj]; exact h
      · right; rw [← Trie.get_node_parts]; simp only [Trie.get]; rw [ite_eq_right hj, ite_eq_left hjo]; exact h
      · rcases Trie.get_set f _ _ x _ e h with ⟨hjk, rfl⟩ | h'
        · exact Or.inl ⟨by omega, rfl⟩
        · right; rw [← Trie.get_node_parts]; simp only [Trie.get]; rw [ite_eq_right hj, ite_eq_right hjo]; exact h'

/-! ## The variables -/

/-- The levels the tries use. -/
abbrev fuel : ℕ := 32

/-- Value `n` as a variable. -/
def vnX (n : ℕ) : Ex := .v (2 * n)

/-- The code of the word at `(b, o)`. -/
def memCode (b o : ℕ) : ℕ := 2 * (b * 65536 + o) + 1

/-- The word at offset `o` from value `b`, as a variable. -/
def memX (b o : ℕ) : Ex := .v (memCode b o)

/-- The memory's word at `p·g^off` (`0` where it has none). -/
def rdw (rd : Reader) (p : E) (off : ℕ) : E := (rd (p.limb 0 * addressOfIndex off)).getD 0

/-- The variables' values: a value's, a memory word's. -/
def irEnv (rd : Reader) (σ : Val) (i : ℕ) : E :=
  if i % 2 = 0 then σ (.n (i / 2)) else rdw rd (σ (.n (i / 2 / 65536))) (i / 2 % 65536)

theorem irEnv_vn (rd : Reader) (σ : Val) (n : ℕ) : irEnv rd σ (2 * n) = σ (.n n) := by
  simp [irEnv]

theorem irEnv_mem (rd : Reader) (σ : Val) (b o : ℕ) (ho : o < 65536) :
    irEnv rd σ (memCode b o) = rdw rd (σ (.n b)) o := by
  have h1 : (2 * (b * 65536 + o) + 1) % 2 = 1 := by omega
  have h2 : (2 * (b * 65536 + o) + 1) / 2 = b * 65536 + o := by omega
  have h3 : (b * 65536 + o) / 65536 = b := by omega
  have h4 : (b * 65536 + o) % 65536 = o := by omega
  simp only [irEnv, memCode, h1, h2, h3, h4, one_ne_zero, ite_false]

/-! ## The run -/

/-- A value's number, for the values `.n n`. -/
def vnOf : V → Option ℕ
  | ⟨[], 0, n⟩ => some n
  | _ => none

theorem vnOf_eq : ∀ {v : V} {n : ℕ}, vnOf v = some n → v = .n n
  | ⟨[], 0, _⟩, _, h => by simp only [vnOf, Option.some.injEq] at h; rw [h]
  | ⟨[], _ + 1, _⟩, _, h => by simp [vnOf] at h
  | ⟨_ :: _, _, _⟩, _, h => by simp [vnOf] at h

/-- Value `n`'s expression in the trie, or its variable. -/
def symOf (t : Trie) (n : ℕ) : Ex := (t.get fuel n).getD (vnX n)

/-- Whether an atom may define value `n`: not cut, not defined yet. -/
def freshIn (cut : ℕ → Bool) (t : Trie) (n : ℕ) : Bool := !cut n && (t.get fuel n).isNone

/-- One atom's definition. -/
def execAtom (cut : ℕ → Bool) (t : Trie) : Atom → Trie
  | .const d c =>
    match vnOf d with
    | some n => if freshIn cut t n then t.set fuel n (.c c) else t
    | none => t
  | .add d a b =>
    match vnOf d, vnOf a, vnOf b with
    | some n, some x, some y => if freshIn cut t n then t.set fuel n (.add (symOf t x) (symOf t y)) else t
    | _, _, _ => t
  | .mul d a b =>
    match vnOf d, vnOf a, vnOf b with
    | some n, some x, some y => if freshIn cut t n then t.set fuel n (.mul (symOf t x) (symOf t y)) else t
    | _, _, _ => t
  | .copy d s =>
    match vnOf d, vnOf s with
    | some n, some x => if freshIn cut t n then t.set fuel n (symOf t x) else t
    | _, _ => t
  | .load d p off =>
    match vnOf d, vnOf p with
    | some n, some b => if freshIn cut t n && decide (off < 65536) then t.set fuel n (memX b off) else t
    | _, _ => t
  | _ => t

/-- The run over statements: their atoms, in order, each step's trie matched before the next. -/
def execStmts (cut : ℕ → Bool) : List Stmt → Trie → Trie
  | [], t => t
  | .atom a :: ss, t =>
    match execAtom cut t a with
    | .nil => execStmts cut ss .nil
    | .node v l r => execStmts cut ss (.node v l r)
  | _ :: ss, t => execStmts cut ss t

theorem execStmts_atom (cut : ℕ → Bool) (a : Atom) (ss : List Stmt) (t : Trie) :
    execStmts cut (.atom a :: ss) t = execStmts cut ss (execAtom cut t a) := by
  simp only [execStmts]
  split <;> rename_i h <;> rw [h]

/-! ## Soundness -/

section

variable {rd : Reader} {σ : Val}

/-- Every entry is its value's expression. -/
def TrieSound (rd : Reader) (σ : Val) (t : Trie) : Prop :=
  ∀ n e, t.get fuel n = some e → e.eval (irEnv rd σ) = σ (.n n)

theorem symOf_eval {t : Trie} (h : TrieSound rd σ t) (n : ℕ) :
    (symOf t n).eval (irEnv rd σ) = σ (.n n) := by
  unfold symOf
  cases hg : t.get fuel n with
  | none => simp only [Option.getD_none, vnX, Ex.eval, irEnv_vn]
  | some e => exact h n e hg

theorem set_sound {t : Trie} (h : TrieSound rd σ t) {n : ℕ} {x : Ex}
    (hx : x.eval (irEnv rd σ) = σ (.n n)) : TrieSound rd σ (t.set fuel n x) := by
  intro j e hj
  rcases Trie.get_set fuel t n x j e hj with ⟨rfl, rfl⟩ | h'
  · exact hx
  · exact h j e h'

theorem execAtom_sound (cut : ℕ → Bool) {t : Trie} (h : TrieSound rd σ t) {a : Atom}
    (ha : a.Holds rd σ) : TrieSound rd σ (execAtom cut t a) := by
  cases a with
  | const d c =>
    simp only [execAtom]
    split
    · rename_i n hn
      split_ifs
      · refine set_sound h ?_
        have : σ d = c := ha
        rw [vnOf_eq hn] at this
        simp [Ex.eval, this]
      · exact h
    · exact h
  | add d a b =>
    simp only [execAtom]
    split
    · rename_i n x y hn hx hy
      split_ifs
      · refine set_sound h ?_
        have : σ d = σ a + σ b := ha
        rw [vnOf_eq hn, vnOf_eq hx, vnOf_eq hy] at this
        simp only [Ex.eval, symOf_eval h, this]
      · exact h
    · exact h
  | mul d a b =>
    simp only [execAtom]
    split
    · rename_i n x y hn hx hy
      split_ifs
      · refine set_sound h ?_
        have : σ d = σ a * σ b := ha
        rw [vnOf_eq hn, vnOf_eq hx, vnOf_eq hy] at this
        simp only [Ex.eval, symOf_eval h, this]
      · exact h
    · exact h
  | copy d s =>
    simp only [execAtom]
    split
    · rename_i n x hn hx
      split_ifs
      · refine set_sound h ?_
        have : σ d = σ s := ha
        rw [vnOf_eq hn, vnOf_eq hx] at this
        rw [symOf_eval h, this]
      · exact h
    · exact h
  | load d p off =>
    simp only [execAtom]
    split
    · rename_i n b hn hb
      split_ifs with hf
      · refine set_sound h ?_
        have hoff : off < 65536 := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
          exact hf.2
        have hl : LoadHolds rd (σ p) off (σ d) := ha
        rw [vnOf_eq hn, vnOf_eq hb] at hl
        simp only [memX, Ex.eval, irEnv_mem rd σ b off hoff, rdw, hl.2]
        rfl
      · exact h
    · exact h
  | _ => exact h

theorem execStmts_sound (cut : ℕ → Bool) :
    ∀ {ss : List Stmt} {t : Trie}, (∀ a, Stmt.atom a ∈ ss → a.Holds rd σ) → TrieSound rd σ t →
      TrieSound rd σ (execStmts cut ss t)
  | [], _, _, h => h
  | .atom a :: ss, t, hA, h => by
    rw [execStmts_atom]
    exact execStmts_sound cut (fun a' ha' ↦ hA a' (List.mem_cons_of_mem _ ha'))
      (execAtom_sound cut h (hA a (List.mem_cons_self ..)))
  | .ite .. :: ss, _, hA, h | .match_ .. :: ss, _, hA, h | .call .. :: ss, _, hA, h
  | .callIf .. :: ss, _, hA, h | .dispatch .. :: ss, _, hA, h | .ret .. :: ss, _, hA, h => by
    simp only [execStmts]
    exact execStmts_sound cut (fun a' ha' ↦ hA a' (List.mem_cons_of_mem _ ha')) h

/-- **The run is sound**: on a valuation satisfying the atoms of `ss`, value `n` is its
expression's value. -/
theorem exec_eval (cut : ℕ → Bool) {ss : List Stmt} (hA : ∀ a, Stmt.atom a ∈ ss → a.Holds rd σ)
    (n : ℕ) : σ (.n n) = (symOf (execStmts cut ss .nil) n).eval (irEnv rd σ) :=
  (symOf_eval (execStmts_sound cut hA fun _ _ h ↦ by simp [Trie.get_nil] at h) n).symm

end

/-! ## Renaming and variables -/

/-- An expression with its variables renamed. -/
def Ex.rename (f : ℕ → ℕ) : Ex → Ex
  | .v i => .v (f i)
  | .c x => .c x
  | .add a b => .add (a.rename f) (b.rename f)
  | .mul a b => .mul (a.rename f) (b.rename f)

theorem eval_rename (f : ℕ → ℕ) (ρ : ℕ → E) : ∀ e : Ex, (e.rename f).eval ρ = e.eval (ρ ∘ f)
  | .v _ => rfl
  | .c _ => rfl
  | .add a b => by simp only [Ex.rename, Ex.eval, eval_rename f ρ a, eval_rename f ρ b]
  | .mul a b => by simp only [Ex.rename, Ex.eval, eval_rename f ρ a, eval_rename f ρ b]

/-- Whether every variable satisfies `p`. -/
def Ex.allVars (p : ℕ → Bool) : Ex → Bool
  | .v i => p i
  | .c _ => true
  | .add a b => a.allVars p && b.allVars p
  | .mul a b => a.allVars p && b.allVars p

/-- Valuations agreeing on the variables give one value. -/
theorem eval_congr {p : ℕ → Bool} {ρ ρ' : ℕ → E} (hp : ∀ i, p i = true → ρ i = ρ' i) :
    ∀ e : Ex, e.allVars p = true → e.eval ρ = e.eval ρ'
  | .v i, h => hp i h
  | .c _, _ => rfl
  | .add a b, h => by
    simp only [Ex.allVars, Bool.and_eq_true] at h
    simp only [Ex.eval, eval_congr hp a h.1, eval_congr hp b h.2]
  | .mul a b, h => by
    simp only [Ex.allVars, Bool.and_eq_true] at h
    simp only [Ex.eval, eval_congr hp a h.1, eval_congr hp b h.2]

end

end LeanVM.Guest.B1.Link.Arith
