/-
  LeanVM.Guest.Backend.Guest.B2.Locs

  The test of one function's places against its certificate's cells, as a function of the
  places, written so that the kernel evaluates the places and the cells once.
-/

module

public import LeanVM.Guest.Glob
public import LeanVM.Guest.Backend.Guest.B2.Residual

/-!
# One function's places against its cells

`agreeWith locs j` is function `j`'s places `locs`, its certificate's cells and its residual
entries (`resOf`); `locsOkAt i locs` is `Agree.fnOk` of entry `i` of the back end's input
(function `i + 1`) on the places `locs`. `Bridge.lean`'s `LocsAgree` is `locsOkAt i` of each
function's placed locations.

The kernel shares no evaluation between the copies of a term, and `fnOk` reads the places and
the cells once for each value. So `locsOkAt` evaluates the places' trie before handing it on
(`withMap`), and reads the cells from a trie keyed by position, built once (`idxTrie`), rather than
from the certificate's list.
-/

namespace LeanVM.Guest.Backend.B2

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- The residual entries of function `f` (`residual`). -/
def resOf (f : String) : List (V × Res) := ((residual.find? (·.1 == f)).map (·.2.2)).getD []

/-- Function `j`'s places `locs` against its certificate's cells and its residual entries. -/
noncomputable def agreeWith (locs : VMap Loc) (j : ℕ) : Agree :=
  ⟨fun v => locs[v]?, fun n => (certOf j).locs.getD n 0, resOf (coreOf j).name⟩

/-! ## Evaluated once -/

/-- `k m`, the trie of `m` evaluated first. -/
def withMap {α β : Type} (m : VMap α) (k : VMap α → β) : β := m.t.seq fun t => k ⟨t⟩

theorem withMap_eq {α β : Type} (m : VMap α) (k : VMap α → β) : withMap m k = k m := by
  cases m
  exact Trie.seq_eq _ _

/-- Store the elements of `l` from position `i` on into `t`, each position evaluated. -/
noncomputable def idxGo (l : List ℕ) : ℕ → Trie ℕ → Trie ℕ :=
  List.rec (motive := fun _ => ℕ → Trie ℕ → Trie ℕ) (fun _ t => t)
    (fun c _ go i t => (t.set i c).seq fun t =>
      Nat.rec (motive := fun _ => Trie ℕ) t (fun m _ => go (m + 1) t) (i + 1)) l

/-- The list `l` as a trie keyed by position. -/
noncomputable def idxTrie (l : List ℕ) : Trie ℕ := idxGo l 0 .nil

theorem idxGo_cons (c : ℕ) (l : List ℕ) (i : ℕ) (t : Trie ℕ) :
    idxGo (c :: l) i t = idxGo l (i + 1) (t.set i c) := by
  show (t.set i c).seq _ = _
  rw [Trie.seq_eq]
  rfl

theorem idxGo_get : ∀ (l : List ℕ) (i : ℕ) (t : Trie ℕ) (n : ℕ),
    (idxGo l i t).get n = if i ≤ n ∧ n < i + l.length then l[n - i]? else t.get n
  | [], i, t, n => by
      show t.get n = _
      rw [ite_eq_right (by simp)]
  | c :: l, i, t, n => by
      rw [idxGo_cons, idxGo_get l, Trie.get_set]
      by_cases h1 : i + 1 ≤ n ∧ n < i + 1 + l.length
      · rw [ite_eq_left h1, ite_eq_left (by simp; omega)]
        obtain ⟨k, rfl⟩ : ∃ k, n = i + 1 + k := ⟨n - (i + 1), by omega⟩
        rw [show i + 1 + k - (i + 1) = k by omega, show i + 1 + k - i = k + 1 by omega]
        rfl
      · rw [ite_eq_right h1]
        by_cases h2 : n = i
        · subst h2
          rw [ite_eq_left rfl, ite_eq_left (by simp), Nat.sub_self]
          rfl
        · rw [ite_eq_right h2, ite_eq_right (by simp; omega)]

theorem idxTrie_get (l : List ℕ) (n : ℕ) : ((idxTrie l).get n).getD 0 = l.getD n 0 := by
  unfold idxTrie
  rw [idxGo_get, Nat.sub_zero, Nat.zero_add, List.getD_eq_getElem?_getD]
  by_cases h : n < l.length
  · rw [ite_eq_left ⟨Nat.zero_le _, h⟩]
  · rw [ite_eq_right (by omega), List.getElem?_eq_none (by omega)]
    rfl

/-- `agreeWith`, its cells read from the evaluated trie `cl`. -/
noncomputable def agreeT (locs : VMap Loc) (cl : Trie ℕ) (j : ℕ) : Agree :=
  ⟨fun v => locs[v]?, fun n => (cl.get n).getD 0, resOf (coreOf j).name⟩

theorem agreeT_eq (locs : VMap Loc) (j : ℕ) : agreeT locs (idxTrie (certOf j).locs) j = agreeWith locs j := by
  unfold agreeT agreeWith
  congr 1
  funext n
  exact idxTrie_get _ n

/-- **The test of entry `i` of the back end's input** (function `i + 1`) on the places `locs`:
`Agree.fnOk` of `agreeWith locs (i + 1)`, its places and cells evaluated once. -/
noncomputable def locsOkAt (i : ℕ) (locs : VMap Loc) : Bool :=
  withMap locs fun m => (idxTrie (certOf (i + 1)).locs).seq fun cl =>
    (agreeT m cl (i + 1)).fnOk (coreOf (i + 1))

theorem locsOkAt_eq (i : ℕ) (locs : VMap Loc) :
    locsOkAt i locs = (agreeWith locs (i + 1)).fnOk (coreOf (i + 1)) := by
  unfold locsOkAt
  rw [withMap_eq, Trie.seq_eq, agreeT_eq]

/-! ## A function's test by parts -/

namespace Agree

variable (A : Agree)

/-- The cells a block sets, from `known`. -/
def afterList (known : List (ℕ × ℕ × ℕ)) (ss : List Stmt) : List (ℕ × ℕ × ℕ) := ss.foldl A.after known

theorem blockOk_append : ∀ (known : List (ℕ × ℕ × ℕ)) (l₁ l₂ : List Stmt),
    A.blockOk known (l₁ ++ l₂) = (A.blockOk known l₁ && A.blockOk (A.afterList known l₁) l₂)
  | known, [], l₂ => by simp [blockOk, afterList]
  | known, s :: l₁, l₂ => by
      simp only [List.cons_append, blockOk, afterList, List.foldl_cons, Bool.and_assoc]
      rw [blockOk_append (A.after known s) l₁ l₂]
      rfl

/-- The test of statements `a ..< a + n` of a body, from the cells the statements before set. -/
def segOk (body : List Stmt) (a n : ℕ) : Bool :=
  A.blockOk (A.afterList [] (body.take a)) ((body.drop a).take n)

theorem segOk_glue {body : List Stmt} {a n m : ℕ} (h₁ : A.segOk body a n = true)
    (h₂ : A.segOk body (a + n) m = true) : A.segOk body a (n + m) = true := by
  unfold segOk at *
  have e : (body.drop a).take (n + m) = (body.drop a).take n ++ (body.drop (a + n)).take m := by
    rw [List.take_add, List.drop_drop]
  have e2 : body.take (a + n) = body.take a ++ (body.drop a).take n := List.take_add ..
  rw [e, blockOk_append, h₁, Bool.true_and]
  rw [e2] at h₂
  simpa [afterList, List.foldl_append] using h₂

theorem fnOk_of_segs {f : Fn} {L : ℕ} (hp : f.params.all A.eqv = true) (hs : A.segOk f.body 0 L = true)
    (hL : f.body.length ≤ L) : A.fnOk f = true := by
  unfold segOk at hs
  rw [List.take_zero, List.drop_zero, List.take_of_length_le hL] at hs
  simp only [fnOk, hp, Bool.true_and]
  exact hs

end Agree

/-- The parameters' part of `locsOkAt`. -/
noncomputable def locsHeadAt (i : ℕ) (locs : VMap Loc) : Bool :=
  withMap locs fun m => (idxTrie (certOf (i + 1)).locs).seq fun cl =>
    (coreOf (i + 1)).params.all (agreeT m cl (i + 1)).eqv

/-- Statements `a ..< a + n` of `locsOkAt`. -/
noncomputable def locsSegAt (i a n : ℕ) (locs : VMap Loc) : Bool :=
  withMap locs fun m => (idxTrie (certOf (i + 1)).locs).seq fun cl =>
    (agreeT m cl (i + 1)).segOk (coreOf (i + 1)).body a n

theorem locsHeadAt_eq (i : ℕ) (locs : VMap Loc) :
    locsHeadAt i locs = (coreOf (i + 1)).params.all (agreeWith locs (i + 1)).eqv := by
  unfold locsHeadAt
  rw [withMap_eq, Trie.seq_eq, agreeT_eq]

theorem locsSegAt_eq (i a n : ℕ) (locs : VMap Loc) :
    locsSegAt i a n locs = (agreeWith locs (i + 1)).segOk (coreOf (i + 1)).body a n := by
  unfold locsSegAt
  rw [withMap_eq, Trie.seq_eq, agreeT_eq]

theorem locsSeg_glue {i a n b m k : ℕ} {locs : VMap Loc} (h₁ : locsSegAt i a n locs = true)
    (hb : a + n = b) (h₂ : locsSegAt i b m locs = true) (hk : n + m = k) :
    locsSegAt i a k locs = true := by
  subst hb hk
  rw [locsSegAt_eq] at *
  exact Agree.segOk_glue _ h₁ h₂

/-- **`locsOkAt` from its parts**: the parameters and the statements `0 ..< L`, `L` past the body. -/
theorem locsOk_of_segs {i L : ℕ} {locs : VMap Loc} (hh : locsHeadAt i locs = true)
    (hs : locsSegAt i 0 L locs = true) (hL : (coreOf (i + 1)).body.length ≤ L) :
    locsOkAt i locs = true := by
  rw [locsOkAt_eq]
  rw [locsHeadAt_eq] at hh
  rw [locsSegAt_eq] at hs
  exact Agree.fnOk_of_segs _ hh hs hL

theorem range_step {f : ℕ → Bool} {a n b m k : ℕ} (h1 : (List.range' a n).all f = true)
    (hb : a + n = b) (h2 : (List.range' b m).all f = true) (hk : n + m = k) :
    (List.range' a k).all f = true := by
  subst hb hk
  rw [← List.range'_append_1, List.all_append, h1, h2]
  rfl

theorem range_one {f : ℕ → Bool} {j : ℕ} (h : f j = true) : (List.range' j 1).all f = true := by
  simp [h]

end
end LeanVM.Guest.Backend.B2
