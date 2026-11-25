/-
  LeanVM.Guest.B1.Place.FreeMask

  A caller's callees checked by their indices' bits in a mask, each distinct callee's check decided
  once for every caller.
-/

module

public import LeanVM.Guest.Exact.Free
public import LeanVM.Guest.Memory.NoWitness

/-!
# Callees by a mask

A caller's check per callee name (`noWitCallee j g`, `exactCallee j g`, a table lookup by name)
reruns, for every caller and every call, the callee's whole subtree check or a string search. When
the callees' facts are decided once over the list `ks` of their indices (`∀ k ∈ ks, ∃ d, noWitJ d k`,
...), a caller checks each callee by its index's bit in `listMask ks` (`maskCallee`): one name
lookup (`calleeIdx`) and a bit test. `maskCallee_mem`: a callee passing it is named by an index of `ks`;
`maskCallee_append`: over two lists of indices with different facts, it has its list's.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- The mask of a list's numbers. -/
def listMask : List ℕ → ℕ
  | [] => 0
  | k :: ks => listMask ks ||| 2 ^ k

theorem mem_of_testBit_listMask : ∀ {ks : List ℕ} {k : ℕ}, (listMask ks).testBit k = true → k ∈ ks
  | [], k, h => by simp [listMask] at h
  | j :: ks, k, h => by
    rw [listMask, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow] at h
    rcases h with h | h
    · exact List.mem_cons_of_mem _ (mem_of_testBit_listMask h)
    · rw [of_decide_eq_true h]
      exact List.mem_cons_self

/-- Function `j`'s callee `g` has its index's bit in the mask `N`. -/
def maskCallee (N j : ℕ) (g : String) : Bool :=
  match calleeIdx j g with
  | some k => N.testBit k
  | none => false

/-- **A callee passing the mask of `ks` is named by an index of `ks`.** -/
theorem maskCallee_mem {ks : List ℕ} {N j : ℕ} {g : String} (hN : N = listMask ks)
    (h : maskCallee N j g = true) :
    ∃ k ∈ ks, (coreProgram[k]?).map Fn.name = some g ∧ Data.nameT.find k = some g := by
  unfold maskCallee at h
  split at h
  · next k hk =>
    subst hN
    have hn := List.find?_some hk
    simp only [decide_eq_true_eq] at hn
    exact ⟨k, mem_of_testBit_listMask h, calleeIdx_spec hk, hn⟩
  · exact absurd h Bool.false_ne_true

/-- **A callee passing the mask of `A ++ B`** passes `p` when `B`'s names do, or is a function of `A`
passing `J` at some depth when `A`'s do. -/
theorem maskCallee_append {A B : List ℕ} {N j : ℕ} {g : String} {J : ℕ → ℕ → Bool} {p : String → Bool}
    (hN : N = listMask (A ++ B)) (hA : ∀ k ∈ A, ∃ d, J d k = true)
    (hB : ∀ k ∈ B, (Data.nameT.find k).all p = true) (h : maskCallee N j g = true) :
    p g = true ∨ ∃ d k, (coreProgram[k]?).map Fn.name = some g ∧ J d k = true := by
  obtain ⟨k, hk, hn, hn'⟩ := maskCallee_mem hN h
  rcases List.mem_append.mp hk with hk | hk
  · obtain ⟨d, hd⟩ := hA k hk
    exact .inr ⟨d, k, hn, hd⟩
  · exact .inl (by simpa [hn'] using hB k hk)

/-! ## Subtrees by call depth

`noWitJ` and `exactJ` are `recJ P` for the body checks `P = Stmt.noWitList` and
`P = Stmt.blockNextOk isComputed pinsInverse` (`noWitJ_eq_recJ`, `exactJ_eq_recJ`). Deciding it for each of many callees walks the subtrees they share again;
`recJ_level` walks them once, by call depth: when every function of the mask `M` passes `recJ P D`
and each function of `L` passes `stepOk P M` (its body passes `P`, its callees but itself are
`M`'s), every function of `M ||| listMask L` passes `recJ P (D + 1)`. -/

/-- **Function `j` and its callees, `d` calls deep, pass `P` on their bodies.** -/
noncomputable def recJ (P : List Stmt → Bool) : ℕ → ℕ → Bool
  | 0, _ => false
  | d + 1, j => match coreProgram[j]? with
    | none => false
    | some fn => P fn.body && (Stmt.blockCallees fn.body).all (fun g => (calleeIdx j g).isSome) &&
        (Data.calleesJ j).all fun k => k == j || recJ P d k

theorem noWitJ_eq_recJ : ∀ d j, noWitJ d j = recJ Stmt.noWitList d j
  | 0, _ => rfl
  | d + 1, j => by
    rw [noWitJ, recJ]
    rcases coreProgram[j]? with _ | fn
    · rfl
    · simp only [noWitJ_eq_recJ d]

theorem exactJ_eq_recJ : ∀ d j, exactJ d j = recJ (Stmt.blockNextOk isComputed pinsInverse) d j
  | 0, _ => rfl
  | d + 1, j => by
    rw [exactJ, recJ]
    rcases coreProgram[j]? with _ | fn
    · rfl
    · simp only [exactJ_eq_recJ d]

theorem recJ_succ (P : List Stmt → Bool) : ∀ {d j}, recJ P d j = true → recJ P (d + 1) j = true
  | 0, _, h => by simp [recJ] at h
  | d + 1, j, h => by
    rw [recJ] at h ⊢
    rcases hj : coreProgram[j]? with _ | fn
    · simp [hj] at h
    · simp only [hj, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at h ⊢
      exact ⟨h.1, fun k hk => (h.2 k hk).imp_right (recJ_succ P)⟩

/-- Function `j`'s body passes `P`, its callees have indices, and those but `j` are the mask `M`'s. -/
noncomputable def stepOk (P : List Stmt → Bool) (M j : ℕ) : Bool :=
  match coreProgram[j]? with
  | none => false
  | some fn => P fn.body && (Stmt.blockCallees fn.body).all (fun g => (calleeIdx j g).isSome) &&
      (Data.calleesJ j).all fun k => k == j || M.testBit k

theorem recJ_of_step {P : List Stmt → Bool} {M j D : ℕ} (hM : ∀ k, M.testBit k = true → recJ P D k = true)
    (h : stepOk P M j = true) : recJ P (D + 1) j = true := by
  unfold stepOk at h
  rw [recJ]
  rcases hj : coreProgram[j]? with _ | fn
  · simp [hj] at h
  · simp only [hj, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at h ⊢
    exact ⟨h.1, fun k hk => (h.2 k hk).imp_right (hM k)⟩

/-- **One call depth more.** -/
theorem recJ_level {P : List Stmt → Bool} {M M' D : ℕ} {L : List ℕ}
    (hM : ∀ k, M.testBit k = true → recJ P D k = true) (heq : M' = M ||| listMask L)
    (hL : ∀ j ∈ L, stepOk P M j = true) : ∀ k, M'.testBit k = true → recJ P (D + 1) k = true := by
  intro k hk
  subst heq
  rw [Nat.testBit_or, Bool.or_eq_true] at hk
  rcases hk with hk | hk
  · exact recJ_succ P (hM k hk)
  · exact recJ_of_step hM (hL k (mem_of_testBit_listMask hk))

end
end LeanVM.Guest.Memory
