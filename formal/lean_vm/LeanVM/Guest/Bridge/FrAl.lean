/-
  LeanVM.Guest.Bridge.FrAl

  The frame hints' `aligned` flags: each the aligned flag `al` of every callee a call through its
  call site names, by `decide +kernel` per function on its plumbing, body and advice.
-/

module

public import LeanVM.Guest.Bridge.CurChk

/-!
# The frame hints' aligned flags

Hotwire's executor starts a callee frame at `allocBase aligned` of the bump pointer, `aligned` the
frame hint's flag, and the honest layout (`Memory/AllocA`) at `allocBase (al k)` for the callee `k`.
`frAlChk al P body d`: for every statement of the body (`blockAllS`) and every frame hint of the
advice with pointer `p` (`frameFlag`, `allocPtr`), every callee a call through a site of cell `p`
names (`siteCallees`: a `call`'s, a `callIf`'s, every arm of a `dispatch`'s, the site's values the
call's) has `al` the hint's flag. So the arms of a `dispatch` share one flag. `frAl_of` states it.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- An allocation hint's `aligned` flag, when it can reserve a callee's frame. -/
def frameFlag : Prover.Exec.Hint → Option Bool
  | .alloc _ _ a | .allocArm _ _ _ a | .allocFrames _ _ _ _ _ a => some a
  | _ => none

/-- The callees a call statement through call site `s` names: a `call`'s, a `callIf`'s, every arm of a
`dispatch`'s, when the site's values are the call's. -/
def siteCallees (s : B2C.Site) : Stmt → List String
  | .call g args rets => bif s.args == args.map (·.idx) && s.rets == rets.map (·.idx) then [g] else []
  | .callIf _ g args => bif s.args == args.map (·.idx) && s.rets == [] then [g] else []
  | .dispatch _ fs args rets => bif s.args == args.map (·.idx) && s.rets == rets.map (·.idx) then fs else []
  | _ => []

/-- Every statement of a block, nested ones included, passes `ok`: by the recursor, for the kernel. -/
noncomputable def blockAllS (ok : Stmt → Bool) : List Stmt → Bool :=
  Stmt.rec_1 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun a ↦ ok (.atom a)) (fun c z n hz hn ↦ ok (.ite c z n) && hz && hn) (fun x arms ha ↦ ok (.match_ x arms) && ha)
    (fun f args rets ↦ ok (.call f args rets)) (fun c f args ↦ ok (.callIf c f args))
    (fun x fs args rets ↦ ok (.dispatch x fs args rets)) (fun vs ↦ ok (.ret vs)) true (fun _ _ hs hss ↦ hs && hss) true
    (fun _ _ ha has ↦ ha && has)

/-- `blockAllS` of a statement. -/
noncomputable def stmtAllS (ok : Stmt → Bool) : Stmt → Bool :=
  Stmt.rec (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun a ↦ ok (.atom a)) (fun c z n hz hn ↦ ok (.ite c z n) && hz && hn) (fun x arms ha ↦ ok (.match_ x arms) && ha)
    (fun f args rets ↦ ok (.call f args rets)) (fun c f args ↦ ok (.callIf c f args))
    (fun x fs args rets ↦ ok (.dispatch x fs args rets)) (fun vs ↦ ok (.ret vs)) true (fun _ _ hs hss ↦ hs && hss) true
    (fun _ _ ha has ↦ ha && has)

/-- `blockAllS` of arms. -/
noncomputable def armsAllS (ok : Stmt → Bool) : List (List Stmt) → Bool :=
  Stmt.rec_2 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun a ↦ ok (.atom a)) (fun c z n hz hn ↦ ok (.ite c z n) && hz && hn) (fun x arms ha ↦ ok (.match_ x arms) && ha)
    (fun f args rets ↦ ok (.call f args rets)) (fun c f args ↦ ok (.callIf c f args))
    (fun x fs args rets ↦ ok (.dispatch x fs args rets)) (fun vs ↦ ok (.ret vs)) true (fun _ _ hs hss ↦ hs && hss) true
    (fun _ _ ha has ↦ ha && has)

/-- A call statement. -/
def isCallS : Stmt → Bool
  | .call .. | .callIf .. | .dispatch .. => true
  | _ => false

/-- **The frame hints' flags check**: every callee a call through a frame hint's site names has `al` the
hint's flag. -/
noncomputable def frAlChk (al : String → Bool) (P : B2C.Plumb) (body : List Stmt)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Bool :=
  Exec.listSeq (allocHints d) fun hs ↦
  blockAllS (fun st ↦ !isCallS st || P.sites.all fun s ↦ (siteCallees s st).isEmpty || hs.all fun q ↦
    match frameFlag q.2, allocPtr q.2 with
    | some b, some p => !(Nat.beq s.q p) || (siteCallees s st).all fun g ↦ al g == b
    | _, _ => true) body

end

public section

section All

variable (ok : Stmt → Bool)

theorem stmtAllS_self (s : Stmt) (h : stmtAllS ok s = true) : ok s = true := by
  cases s with
  | ite c z n => change (ok _ && blockAllS ok z && blockAllS ok n) = true at h; simp only [Bool.and_eq_true] at h; exact h.1.1
  | match_ x arms => change (ok _ && armsAllS ok arms) = true at h; simp only [Bool.and_eq_true] at h; exact h.1
  | atom _ => exact h
  | call _ _ _ => exact h
  | callIf _ _ _ => exact h
  | dispatch _ _ _ _ => exact h
  | ret _ => exact h

mutual
theorem blockAllS_mem : ∀ (ss : List Stmt), blockAllS ok ss = true → ∀ s ∈ stmtsOf ss, ok s = true
  | [], _, s, hs => by simp [stmtsOf] at hs
  | s' :: ss, h, s, hs => by
    change (stmtAllS ok s' && blockAllS ok ss) = true at h
    rw [Bool.and_eq_true] at h
    rw [stmtsOf, List.mem_cons, List.mem_append] at hs
    rcases hs with rfl | hs | hs
    · exact stmtAllS_self ok _ h.1
    · exact stmtAllS_mem s' h.1 s hs
    · exact blockAllS_mem ss h.2 s hs

theorem stmtAllS_mem : ∀ (s' : Stmt), stmtAllS ok s' = true → ∀ s ∈ stmtsSub s', ok s = true
  | .ite c' z n, h, s, hs => by
    change (ok _ && blockAllS ok z && blockAllS ok n) = true at h
    simp only [Bool.and_eq_true] at h
    simp only [stmtsSub, List.mem_append] at hs
    rcases hs with hs | hs
    · exact blockAllS_mem z h.1.2 s hs
    · exact blockAllS_mem n h.2 s hs
  | .match_ x arms, h, s, hs => by
    change (ok _ && armsAllS ok arms) = true at h
    rw [Bool.and_eq_true] at h
    exact armsAllS_mem arms h.2 s hs
  | .atom _, _, _, hs | .call .., _, _, hs | .callIf .., _, _, hs | .dispatch .., _, _, hs | .ret _, _, _, hs => by
    simp [stmtsSub] at hs

theorem armsAllS_mem : ∀ (arms : List (List Stmt)), armsAllS ok arms = true → ∀ s ∈ stmtsArms arms, ok s = true
  | [], _, s, hs => by simp [stmtsArms] at hs
  | a :: as, h, s, hs => by
    change (blockAllS ok a && armsAllS ok as) = true at h
    rw [Bool.and_eq_true] at h
    rw [stmtsArms, List.mem_append] at hs
    rcases hs with hs | hs
    · exact blockAllS_mem a h.1 s hs
    · exact armsAllS_mem as h.2 s hs
end

end All

/-- **What the flags check gives**: a frame hint's flag is `al` of every callee a call through its
site names. -/
theorem frAl_of {al : String → Bool} {P : B2C.Plumb} {body : List Stmt}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (h : frAlChk al P body d = true)
    {q : ℕ × Prover.Exec.Hint} (hq : q ∈ allocHints d) {b : Bool} {p : ℕ} (hb : frameFlag q.2 = some b)
    (hp : allocPtr q.2 = some p) {s : B2C.Site} (hs : s ∈ P.sites) (hsq : s.q = p) {st : Stmt}
    (hst : st ∈ stmtsOf body) {g : String} (hg : g ∈ siteCallees s st) : al g = b := by
  rw [frAlChk, Exec.listSeq_eq] at h
  have hc : isCallS st = true := by
    cases st <;> simp_all [siteCallees, isCallS]
  have hne : (siteCallees s st).isEmpty = false := by
    cases h' : siteCallees s st with
    | nil => rw [h'] at hg; cases hg
    | cons _ _ => rfl
  have h0 := blockAllS_mem _ body h st hst
  rw [hc, Bool.not_true, Bool.false_or] at h0
  have h1 := List.all_eq_true.mp h0 s hs
  rw [hne, Bool.false_or] at h1
  have h2 := List.all_eq_true.mp h1 q hq
  rw [hb, hp] at h2
  simp only [hsq, Nat.beq_refl, Bool.not_true, Bool.false_or, List.all_eq_true] at h2
  simpa using h2 g hg

/-- **The arms of a `dispatch` through a frame hint's site share its flag.** -/
theorem frAl_dispatch {al : String → Bool} {P : B2C.Plumb} {body : List Stmt}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (h : frAlChk al P body d = true)
    {q : ℕ × Prover.Exec.Hint} (hq : q ∈ allocHints d) {b : Bool} {p : ℕ} (hb : frameFlag q.2 = some b)
    (hp : allocPtr q.2 = some p) {s : B2C.Site} (hs : s ∈ P.sites) (hsq : s.q = p) {x : V} {fs : List String}
    {args rets : List V} (hst : Stmt.dispatch x fs args rets ∈ stmtsOf body) (ha : s.args = args.map (·.idx))
    (hr : s.rets = rets.map (·.idx)) : ∀ g ∈ fs, al g = b := fun g hg ↦
  frAl_of h hq hb hp hs hsq hst (by simp [siteCallees, ha, hr, hg])

end

end LeanVM.Guest.Bridge
