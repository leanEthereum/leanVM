module

public import LeanVM.Guest.ExecCore

/-!
# Lists by key

A list's elements filed in a trie by a key (`buckets`), so that a membership test scans only the
elements of one key (`anyB`): where `eq x y` implies equal keys, `anyB` decides `l.any (eq x)` in the
time of one bucket. The walk's joins and cuts compare lists of hundreds of facts this way
(`Mode/Abs.lean`). A key past the trie's depth is dropped, which only makes `anyB` answer `false`.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Guest.Exec

@[expose] public section

/-- The elements of `l` by `key`: key `k`'s bucket lists the elements of key `k`. -/
noncomputable def buckets {α : Type} (key : α → ℕ) (l : List α) : Trie (List α) :=
  List.rec (motive := fun _ ↦ Trie (List α)) .nil
    (fun x _ t ↦ t.seq fun t ↦ t.set (x :: (t.get (key x)).getD []) envDepth (key x)) l

/-- `buckets` by structural recursion, for compiled code (`@[csimp]`); the kernel unfolds the
recursor's form. -/
def bucketsC {α : Type} (key : α → ℕ) : List α → Trie (List α)
  | [] => .nil
  | x :: l => (bucketsC key l).seq fun t ↦ t.set (x :: (t.get (key x)).getD []) envDepth (key x)

/-- `k l`, `l` evaluated to its first constructor, as `Trie.seq`: a state's lists are values, not
chains of projections through earlier states. -/
def lseq {α β : Type} (l : List α) (k : List α → β) : β :=
  match l with
  | [] => k []
  | a :: as => k (a :: as)

/-- Some element of bucket `k` satisfies `f`. -/
def anyB {α : Type} (T : Trie (List α)) (f : α → Bool) (k : ℕ) : Bool :=
  ((T.get k).getD []).any f

end

public section

theorem lseq_eq {α β : Type} (l : List α) (k : List α → β) : lseq l k = k l := by cases l <;> rfl

@[csimp] theorem buckets_eq_bucketsC : @buckets = @bucketsC := by
  funext α key l
  induction l with
  | nil => rfl
  | cons x l ih => simp only [buckets, bucketsC] at ih ⊢; rw [ih]

theorem mem_buckets {α : Type} {key : α → ℕ} : ∀ {l : List α} {k : ℕ} {y : α},
    y ∈ ((buckets key l).get k).getD [] → y ∈ l
  | [], k, y, h => by
    have : (buckets key ([] : List α)).get k = none := by
      show (Trie.nil : Trie (List α)).get k = none
      rfl
    rw [this] at h; cases h
  | x :: l, k, y, h => by
    have e : buckets key (x :: l) =
        (buckets key l).set (x :: ((buckets key l).get (key x)).getD []) envDepth (key x) := by
      show (buckets key l).seq (fun t ↦ t.set (x :: (t.get (key x)).getD []) envDepth (key x)) = _
      rw [Trie.seq_eq]
    rw [e] at h
    rcases hg : ((buckets key l).set (x :: ((buckets key l).get (key x)).getD []) envDepth (key x)).get k
      with _ | v
    · rw [hg] at h; cases h
    rw [hg, Option.getD_some] at h
    rcases Trie.get_set hg with ⟨rfl, rfl⟩ | h'
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (mem_buckets h)
    · exact List.mem_cons_of_mem _ (mem_buckets (k := k) (by rw [h', Option.getD_some]; exact h))

/-- `anyB` over `l`'s buckets: some element of `l` satisfies `f`. -/
theorem any_of_anyB {α : Type} {key : α → ℕ} {l : List α} {f : α → Bool} {k : ℕ}
    (h : anyB (buckets key l) f k = true) : l.any f = true := by
  obtain ⟨y, hy, he⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨y, mem_buckets hy, he⟩

/-- `anyB` over `l`'s buckets with an `eq` that is equality: `x ∈ l`. -/
theorem mem_of_anyB {α : Type} {key : α → ℕ} {eq : α → α → Bool} (heq : ∀ x y, eq x y = true → x = y)
    {l : List α} {x : α} {k : ℕ} (h : anyB (buckets key l) (eq x) k = true) : x ∈ l := by
  obtain ⟨y, hy, he⟩ := List.any_eq_true.mp h
  rw [heq x y he]
  exact mem_buckets hy

end

end LeanVM.Guest.Mode
