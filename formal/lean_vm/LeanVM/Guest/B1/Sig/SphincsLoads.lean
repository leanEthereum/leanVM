/-
  LeanVM.Guest.B1.Sig.SphincsLoads

  Where a body's loads read, by a check of its atoms: through its first argument at an offset below
  `4`, or through given pointers at offset `0` (`verify_sig_lean_sphincs`'s claim and byte reads).
-/

module

public import LeanVM.Guest.B1.Sig.SphincsCompleteSpec

/-!
# A check of a body's loads

* `loadOkB`, `stmtLoadsB`: a load reads through the argument `n0` at an offset below `4`, or through
  one of the given values at offset `0`; `walk_loadOk`: the path of a block passing the check
  loads only so; `loadAddrs_of_loadOk`, `loads_of_walk`: the addresses it loads from.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Guest.Memory

@[expose] public section

/-! ## A check of the loads -/

/-- A load reads through `n0` at an offset below `4`, or through one of `ptrs` at offset `0`. -/
def loadOkB (ptrs : List Nat) : Atom → Bool
  | .load _ p off => (p == .n 0 && decide (off < 4)) || (off == 0 && ptrs.any fun q => p == .n q)
  | _ => true

mutual
/-- `loadOkB` of every atom of a statement, through its branches and arms. -/
def stmtLoadsB (ptrs : List Nat) : Stmt → Bool
  | .atom a => loadOkB ptrs a
  | .ite _ z n => listLoadsB ptrs z && listLoadsB ptrs n
  | .match_ _ arms => armsLoadsB ptrs arms
  | .call .. => true
  | .callIf .. => true
  | .dispatch .. => true
  | .ret _ => true

/-- `stmtLoadsB` of a block. -/
def listLoadsB (ptrs : List Nat) : List Stmt → Bool
  | [] => true
  | s :: ss => stmtLoadsB ptrs s && listLoadsB ptrs ss

/-- `stmtLoadsB` of arms. -/
def armsLoadsB (ptrs : List Nat) : List (List Stmt) → Bool
  | [] => true
  | a :: as => listLoadsB ptrs a && armsLoadsB ptrs as
end

/-- An event whose atom passes `loadOkB`. -/
def Ev.loadOk (ptrs : List Nat) : Ev → Prop
  | .atom a => loadOkB ptrs a = true
  | _ => True

variable {σ : Val}

theorem pick_loadOk (ptrs : List Nat) {x : V} {args rets : List V} :
    ∀ (gs : List String) (j : ℕ), (pick σ x args rets j gs).All (Ev.loadOk ptrs)
  | [], _ => trivial
  | g :: gs, j => by
      unfold pick
      split_ifs
      · intro e he
        rw [List.mem_singleton] at he
        subst he
        trivial
      · exact pick_loadOk ptrs gs (j + 1)

mutual
theorem walk1_loadOk (ptrs : List Nat) : ∀ (s : Stmt), stmtLoadsB ptrs s = true →
    (walk1 σ s).All (Ev.loadOk ptrs)
  | .atom _, h => by
      intro e he
      rw [List.mem_singleton] at he
      subst he
      exact h
  | .ite c z n, h => by
      simp only [stmtLoadsB, Bool.and_eq_true] at h
      rw [walk1]
      refine Out.all_pre (fun e he => by rw [List.mem_singleton] at he; subst he; trivial) ?_
      split_ifs
      · exact walk_loadOk ptrs z h.1
      · exact walk_loadOk ptrs n h.2
  | .match_ x arms, h => walkArms_loadOk ptrs x arms 0 h
  | .call .., _ => by
      intro e he
      rw [List.mem_singleton] at he
      subst he
      trivial
  | .callIf c f args, _ => by
      rw [walk1]
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · trivial
      · split_ifs <;> trivial
  | .dispatch x fs args rets, _ => pick_loadOk ptrs fs 0
  | .ret _, _ => fun _ he => (List.not_mem_nil he).elim

theorem walk_loadOk (ptrs : List Nat) : ∀ (ss : List Stmt), listLoadsB ptrs ss = true →
    (walk σ ss).All (Ev.loadOk ptrs)
  | [], _ => fun _ he => (List.not_mem_nil he).elim
  | s :: ss, h => by
      simp only [listLoadsB, Bool.and_eq_true] at h
      rw [walk]
      exact Out.all_seq (walk_loadOk ptrs ss h.2) (walk1_loadOk ptrs s h.1)

theorem walkArms_loadOk (ptrs : List Nat) (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ),
    armsLoadsB ptrs arms = true → (walkArms σ x j arms).All (Ev.loadOk ptrs)
  | [], _, _ => trivial
  | a :: as, j, h => by
      simp only [armsLoadsB, Bool.and_eq_true] at h
      unfold walkArms
      split_ifs
      · exact walk_loadOk ptrs a h.1
      · exact walkArms_loadOk ptrs x as (j + 1) h.2
end

/-- **The addresses a checked path loads from.** -/
theorem loadAddrs_of_loadOk {ptrs : List Nat} {es : List Ev} (h : ∀ e ∈ es, Ev.loadOk ptrs e) :
    ∀ A ∈ loadAddrs σ es, (∃ k < 4, A = (σ (.n 0)).limb 0 * addressOfIndex k) ∨
      ∃ q ∈ ptrs, A = (σ (.n q)).limb 0 := by
  intro A hA
  obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
  have hok := h e he
  rcases e with ⟨_ | _ | _ | _ | ⟨d, p, off⟩ | _ | _ | _ | _ | _ | _ | _⟩ | _ | _ | _ <;>
    simp only [Ev.loadAddr?, reduceCtorEq] at hea
  simp only [Option.some.injEq] at hea
  subst hea
  simp only [Ev.loadOk, loadOkB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.any_eq_true] at hok
  rcases hok with ⟨rfl, hoff⟩ | ⟨rfl, q, hq, rfl⟩
  · exact Or.inl ⟨off, hoff, rfl⟩
  · exact Or.inr ⟨q, hq, by simp [addressOfIndex]⟩

/-- A checked block's returning path loads only so. -/
theorem loads_of_walk {ptrs : List Nat} {ss : List Stmt} (h : listLoadsB ptrs ss = true) {es : List Ev}
    {vs : List V} (hw : walk σ ss = .ret es vs) : ∀ e ∈ es, Ev.loadOk ptrs e := by
  have := walk_loadOk (σ := σ) ptrs ss h
  rw [hw] at this
  exact this

theorem limb_mul_ofK {bb : E} (hK : IsInK bb) (v : Nat) :
    (bb * ofK (addressOfIndex v)).limb 0 = bb.limb 0 * addressOfIndex v := by
  have e : bb * ofK (addressOfIndex v) = ofK (bb.limb 0 * addressOfIndex v) :=
      by rw [ofK_mul, ← eq_ofK_limb hK]
  rw [e]
  simp

end
end LeanVM.Guest.B1.Sig
