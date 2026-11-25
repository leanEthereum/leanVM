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
the callees' facts are decided once over the list `ks` of their indices (`∀ k ∈ ks, noWitJ 8 k`,
...), a caller checks each callee by its index's bit in `listMask ks` (`maskCallee`): one name
lookup (`calleeIdx`) and a bit test. `maskCallee_mem`: a callee passing it is named by an index of `ks`.
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

/-- A callee passing the mask of `ks`, whose indices pass `noWitJ 8`, has no witness hint below it. -/
theorem noWitG_of_maskCallee {ks : List ℕ} {N j : ℕ} {g : String} (hN : N = listMask ks)
    (hks : ∀ k ∈ ks, noWitJ 8 k = true) (h : maskCallee N j g = true) : NoWitG g := by
  obtain ⟨k, hk, hn, -⟩ := maskCallee_mem hN h
  exact ⟨8, k, hn, hks k hk⟩

/-- A callee passing the mask of `ks`, whose indices pass `exactJ 8`, is exact for free. -/
theorem exactFreeG_of_maskCallee {ks : List ℕ} {N j : ℕ} {g : String} (hN : N = listMask ks)
    (hks : ∀ k ∈ ks, exactJ 8 k = true) (h : maskCallee N j g = true) : ExactFreeG g := by
  obtain ⟨k, hk, hn, -⟩ := maskCallee_mem hN h
  exact ⟨8, k, hn, hks k hk⟩

/-- A callee passing the mask of `ks`, whose indices' names pass `p`, passes `p`. -/
theorem of_maskCallee {ks : List ℕ} {N j : ℕ} {g : String} {p : String → Bool} (hN : N = listMask ks)
    (hks : ∀ k ∈ ks, (Data.nameT.find k).all p = true) (h : maskCallee N j g = true) : p g = true := by
  obtain ⟨k, hk, -, hn⟩ := maskCallee_mem hN h
  simpa [hn] using hks k hk

end
end LeanVM.Guest.Memory
