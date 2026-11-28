/-
  LeanVM.Guest.B1.VsC.CstWalk

  `check_stack_terminal`'s walk: its selectors' dispatch taken at the stack's size, the rest straight.
-/

module

public import LeanVM.Guest.B1.VsC.CstVal
public import LeanVM.Guest.B1.Fwd.Eval
public import LeanVM.Guest.Memory.Straight

/-!
# `check_stack_terminal`, walked

The body is straight but for one dispatch, on `.n 42 = gmv·g^-16`, to `stack_selectors__L{n}`
(`cstArms`). At `.n 42 = g^j`, `j < 15`, the walk is that of `cstPreJ j`, the body with the dispatch
replaced by the call of arm `j` (`walk_cst`). The forward checker accepts the body (`cst_chk`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Stack LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The dispatch's arguments. -/
def cstArgsV : List V := [.n 2, .n 3, .n 17, .n 18, .n 0]

/-- The header before the dispatch. -/
def cstH0 : List Stmt := cstHead.take 20

/-- The header after the dispatch. -/
def cstH1 : List Stmt := cstHead.drop 21

theorem cstHead_split : cstHead = cstH0 ++ .dispatch (.n 42) cstArms cstArgsV [.n 43] :: cstH1 := rfl

/-- The statements after the dispatch, before the `ret`. -/
def cstRest : List Stmt :=
  cstH1 ++ cstRowSum ++ cstRq ++ cstRing ++ cstMem ++ cstSent 633 629 sentList.reverse ++ cstTail

/-- The body before its `ret`, the dispatch taken at arm `j`. -/
def cstPreJ (j : ℕ) : List Stmt := cstH0 ++ .call (cstArms.getD j "") cstArgsV [.n 43] :: cstRest

theorem cstBody_split :
    cstBody = cstH0 ++ .dispatch (.n 42) cstArms cstArgsV [.n 43] :: (cstRest ++ [.ret []]) := by
  simp only [cstBody, cstBodyA, cstHead_split, cstRest, List.append_assoc, List.cons_append]

set_option maxRecDepth 100000 in
theorem cst_straight : cstH0.all Stmt.straight = true ∧ cstRest.all Stmt.straight = true := by
  decide +kernel

theorem cstPreJ_straight (j : ℕ) : (cstPreJ j).all Stmt.straight = true := by
  simp only [cstPreJ, List.all_append, List.all_cons, cst_straight.1, cst_straight.2, Stmt.straight,
    Bool.and_self]

/-- A straight block, then the rest. -/
theorem cst_walk_pre (σ : Val) : ∀ (pre rest : List Stmt), pre.all Stmt.straight = true →
    walk σ (pre ++ rest) = (walk σ rest).pre (pre.flatMap (slEvs σ))
  | [], rest, _ => by rw [List.nil_append]; cases walk σ rest <;> rfl
  | s :: pre, rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.cons_append, walk, cst_walk_pre σ pre rest h.2, walk1_straight σ s h.1, List.flatMap_cons]
    cases walk σ rest <;> simp [Out.seq, Out.pre]

/-- **`check_stack_terminal`'s walk**, its dispatch at arm `j`. -/
theorem walk_cst (σ : Val) {j : ℕ} (hj : j < 15) (hx : σ (.n 42) = ofK (addressOfIndex j)) :
    walk σ cstBody = .ret ((cstPreJ j).flatMap (slEvs σ)) [] := by
  have hp := pick_eq σ (.n 42) cstArgsV [.n 43] cstArms 0 j (by simp [cstArms]; omega) (by simp [cstArms])
    (by rw [hx, Nat.zero_add])
  have hg : cstArms[j]! = cstArms.getD j "" := by
    rw [getElem!_pos _ _ (by simp [cstArms]; omega), List.getD_eq_getElem _ _ (by simp [cstArms]; omega)]
  rw [hg] at hp
  rw [cstBody_split, cst_walk_pre σ _ _ cst_straight.1, walk, walk1, hp, walk_straight σ [] cstRest cst_straight.2]
  simp only [Out.seq, Out.pre, cstPreJ, List.flatMap_append, List.flatMap_cons, slEvs,
    List.singleton_append]

set_option maxRecDepth 100000 in
/-- The forward checker accepts the body. -/
theorem cst_chk : (chk 23 cstBody).isSome = true := by decide +kernel

end
end LeanVM.Guest.B1.VsC
