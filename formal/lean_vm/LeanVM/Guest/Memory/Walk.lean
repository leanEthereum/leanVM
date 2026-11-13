/-
  LeanVM.Guest.Memory.Walk

  A check of each element of a list with its index, in one walk (`walkOk`).
-/

module

namespace LeanVM.Guest.Memory

@[expose] public section

/-- `chk` holds of each element of a list, the first numbered `j`. -/
def walkOk {α : Type} (chk : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | j, x :: xs => chk j x && walkOk chk (j + 1) xs

theorem walkOk_append {α : Type} (chk : Nat → α → Bool) : ∀ (j : Nat) (l l' : List α),
    walkOk chk j (l ++ l') = (walkOk chk j l && walkOk chk (j + l.length) l')
  | j, [], l' => by simp [walkOk]
  | j, x :: l, l' => by
      rw [List.cons_append, walkOk, walkOk, walkOk_append chk (j + 1) l l', Bool.and_assoc]
      simp [Nat.add_assoc, Nat.add_comm 1]

theorem walkOk_get {α : Type} {chk : Nat → α → Bool} : ∀ {j : Nat} {l : List α} {k : Nat} {fn : α},
    walkOk chk j l = true → l[k]? = some fn → chk (j + k) fn = true
  | _, [], _, _, _, h => by simp at h
  | j, f :: l, 0, fn, h, hk => by
      simp only [walkOk, Bool.and_eq_true] at h
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk; simpa using h.1
  | j, f :: l, k + 1, fn, h, hk => by
      simp only [walkOk, Bool.and_eq_true] at h
      simp only [List.getElem?_cons_succ] at hk
      have := walkOk_get h.2 hk
      rwa [Nat.add_assoc, Nat.add_comm 1 k] at this

end
end LeanVM.Guest.Memory
