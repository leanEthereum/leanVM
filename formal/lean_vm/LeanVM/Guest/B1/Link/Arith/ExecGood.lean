/-
  LeanVM.Guest.B1.Link.Arith.ExecGood

  The symbolic run is sound on a valuation satisfying only the defining equations of its atoms
  (`Fwd.Good`), when every definition the run makes is one an equation gives.
-/

module

public import LeanVM.Guest.B1.Link.Arith.Exec
public import LeanVM.Guest.B1.Fwd.Eval

/-!
# The run from the defining equations

`execStmts` defines a value by a constant, a sum, a product, a copy or a load. On a forward
valuation (`Fwd.ev`) every atom satisfies `Fwd.Good`, which is the atom's relation except for a
division (a `mul` whose operand is newer than its product: `Good` gives the quotient) and a store
(a load into an older value: `Good` gives nothing). `chkRun cut Sd X ss t` checks, along the run,
that every definition the run makes is by neither, or by an atom of `X`: a `mul` it defines has
older operands, a load it defines is not among the stores, whose `(value, pointer, offset)` `Sd`
lists (`stTriple`).

`chkRun_sound`: then the run is sound (`TrieSound`) on every valuation whose atoms satisfy `Good`
and whose atoms of `X` hold. `exec_evalG`: `exec_eval` from these.
-/

namespace LeanVM.Guest.B1.Link.Arith

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- Whether `(n, b, o)` is in `l`. -/
def memT : List (ℕ × ℕ × ℕ) → ℕ → ℕ → ℕ → Bool
  | [], _, _, _ => false
  | q :: l, n, b, o => (decide (q.1 = n) && decide (q.2.1 = b) && decide (q.2.2 = o)) || memT l n b o

theorem memT_of_mem : ∀ {l : List (ℕ × ℕ × ℕ)} {n b o : ℕ}, (n, b, o) ∈ l → memT l n b o = true
  | [], _, _, _, h => absurd h List.not_mem_nil
  | q :: l, n, b, o, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp [memT]
    · simp [memT, memT_of_mem h]

/-- A store's value, pointer and offset are listed in `Sd` (when both are numbered values). -/
def stTriple (Sd : List (ℕ × ℕ × ℕ)) : Atom → Bool
  | .load d p off =>
    match vnOf d, vnOf p with
    | some n, some b => memT Sd n b off
    | _, _ => true
  | _ => true

/-- Whether the run's definition by `a` follows from `a`'s defining equation, or `a` is in `X`: a
`mul` it defines has older operands, a load it defines is not listed in `Sd`. -/
def defOk (cut : ℕ → Bool) (Sd : List (ℕ × ℕ × ℕ)) (X : List Atom) (t : Trie) : Atom → Bool
  | .mul d a b =>
    match vnOf d, vnOf a, vnOf b with
    | some n, some x, some y => !freshIn cut t n || decide (x < n ∧ y < n) || decide (Atom.mul d a b ∈ X)
    | _, _, _ => true
  | .load d p off =>
    match vnOf d, vnOf p with
    | some n, some b =>
      !(freshIn cut t n && decide (off < 65536)) || !memT Sd n b off || decide (Atom.load d p off ∈ X)
    | _, _ => true
  | _ => true

/-- The check along the run, each step's trie matched before the next (as `execStmts`). -/
def chkRun (cut : ℕ → Bool) (Sd : List (ℕ × ℕ × ℕ)) (X : List Atom) : List Stmt → Trie → Bool
  | [], _ => true
  | .atom a :: ss, t =>
    defOk cut Sd X t a &&
      match execAtom cut t a with
      | .nil => chkRun cut Sd X ss .nil
      | .node v l r => chkRun cut Sd X ss (.node v l r)
  | _ :: ss, t => chkRun cut Sd X ss t

theorem chkRun_atom (cut : ℕ → Bool) (Sd : List (ℕ × ℕ × ℕ)) (X : List Atom) (a : Atom) (ss : List Stmt)
    (t : Trie) :
    chkRun cut Sd X (.atom a :: ss) t = (defOk cut Sd X t a && chkRun cut Sd X ss (execAtom cut t a)) := by
  simp only [chkRun]
  split <;> rename_i h <;> rw [h]

section

variable {rd : Reader} {σ : Val} {S : List Atom} {w : ℕ → E}

theorem not_mem_stores {Sd : List (ℕ × ℕ × ℕ)} (hS : ∀ a ∈ S, stTriple Sd a = true) {d p : V} {off n b : ℕ}
    (hd : vnOf d = some n) (hp : vnOf p = some b) (hm : memT Sd n b off = false) : Atom.load d p off ∉ S := by
  intro h
  have := hS _ h
  simp only [stTriple, hd, hp] at this
  rw [hm] at this
  exact Bool.false_ne_true this

/-- **One step**: a definition the check admits keeps the trie sound. -/
theorem defOk_sound (cut : ℕ → Bool) (Sd : List (ℕ × ℕ × ℕ)) (X : List Atom)
    (hS : ∀ a ∈ S, stTriple Sd a = true) (hX : ∀ a ∈ X, a.Holds rd σ) {t : Trie} (h : TrieSound rd σ t)
    {a : Atom} (hg : Fwd.Good rd S w σ a) (hd : defOk cut Sd X t a = true) : TrieSound rd σ (execAtom cut t a) := by
  by_cases hx : a ∈ X
  · exact execAtom_sound cut h (hX a hx)
  cases a with
  | const d c => exact execAtom_sound cut h hg
  | add d x y => exact execAtom_sound cut h hg
  | copy d s => exact execAtom_sound cut h hg
  | mul d x y =>
    simp only [execAtom]
    split
    · rename_i n i j hn hi hj
      split_ifs with hf
      · refine set_sound h ?_
        have hlt : i < n ∧ j < n := by
          simp only [defOk, hn, hi, hj, hf, Bool.not_true, Bool.false_or, Bool.or_eq_true,
            decide_eq_true_eq] at hd
          rcases hd with hd | hd
          · exact hd
          · exact absurd hd hx
        obtain rfl := vnOf_eq hn
        obtain rfl := vnOf_eq hi
        obtain rfl := vnOf_eq hj
        have hg' : σ (.n n) = σ (.n i) * σ (.n j) := by simpa [Fwd.Good, hlt.1, hlt.2] using hg
        simp only [Ex.eval, symOf_eval h, hg']
      · exact h
    · exact h
  | load d p off =>
    simp only [execAtom]
    split
    · rename_i n b hn hb
      split_ifs with hf
      · refine set_sound h ?_
        rw [Bool.and_eq_true] at hf
        have hoff : off < 65536 := of_decide_eq_true hf.2
        have hm : memT Sd n b off = false := by
          simp only [defOk, hn, hb, hf.1, hf.2, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true,
            decide_eq_true_eq] at hd
          rcases hd with hd | hd
          · simpa using hd
          · exact absurd hd hx
        have hnS := not_mem_stores hS hn hb hm
        have hg' : σ d = Fwd.rdAt rd (σ p) off := by
          simp only [Fwd.Good] at hg
          rcases hg with hg | hg
          · exact absurd hg hnS
          · exact hg
        obtain rfl := vnOf_eq hn
        obtain rfl := vnOf_eq hb
        simp only [memX, Ex.eval, irEnv_mem rd σ b off hoff, hg', rdw, Fwd.rdAt]
      · exact h
    · exact h
  | _ => exact h

/-- **The check makes the run sound**: on a valuation whose atoms satisfy their defining equations and
whose atoms of `X` hold. -/
theorem chkRun_sound (cut : ℕ → Bool) (Sd : List (ℕ × ℕ × ℕ)) (X : List Atom)
    (hS : ∀ a ∈ S, stTriple Sd a = true) (hX : ∀ a ∈ X, a.Holds rd σ) :
    ∀ {ss : List Stmt} {t : Trie}, (∀ a, Stmt.atom a ∈ ss → Fwd.Good rd S w σ a) → chkRun cut Sd X ss t = true →
      TrieSound rd σ t → TrieSound rd σ (execStmts cut ss t)
  | [], _, _, _, h => h
  | .atom a :: ss, t, hG, hc, h => by
    rw [chkRun_atom, Bool.and_eq_true] at hc
    rw [execStmts_atom]
    exact chkRun_sound cut Sd X hS hX (fun a' ha' ↦ hG a' (List.mem_cons_of_mem _ ha')) hc.2
      (defOk_sound cut Sd X hS hX h (hG a (List.mem_cons_self ..)) hc.1)
  | .ite .. :: ss, _, hG, hc, h | .match_ .. :: ss, _, hG, hc, h | .call .. :: ss, _, hG, hc, h
  | .callIf .. :: ss, _, hG, hc, h | .dispatch .. :: ss, _, hG, hc, h | .ret .. :: ss, _, hG, hc, h => by
    simp only [execStmts, chkRun] at hc ⊢
    exact chkRun_sound cut Sd X hS hX (fun a' ha' ↦ hG a' (List.mem_cons_of_mem _ ha')) hc h

/-- **The run from the defining equations**: `exec_eval` on a valuation whose atoms satisfy `Good`, the check
passing. -/
theorem exec_evalG (cut : ℕ → Bool) (Sd : List (ℕ × ℕ × ℕ)) (X : List Atom)
    (hS : ∀ a ∈ S, stTriple Sd a = true) (hX : ∀ a ∈ X, a.Holds rd σ) {ss : List Stmt}
    (hG : ∀ a, Stmt.atom a ∈ ss → Fwd.Good rd S w σ a) (hc : chkRun cut Sd X ss .nil = true) :
    TrieSound rd σ (execStmts cut ss .nil) :=
  chkRun_sound cut Sd X hS hX hG hc fun _ _ h ↦ by simp [Trie.get_nil] at h

end

end

end LeanVM.Guest.B1.Link.Arith
