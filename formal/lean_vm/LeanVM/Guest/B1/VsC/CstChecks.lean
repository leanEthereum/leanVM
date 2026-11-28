/-
  LeanVM.Guest.B1.VsC.CstChecks

  What the kernel checks of `check_stack_terminal`'s template for its completeness.
-/

module

public import LeanVM.Guest.B1.VsC.CstWalk
public import LeanVM.Guest.B1.VsC.EqTreeC
public import LeanVM.Guest.B1.VsC.FwdCalls
public import LeanVM.Guest.Memory.HintsCheck

/-!
# `check_stack_terminal`'s template, checked

`cstAtomsOk`: every atom before the final assertion (`cstAtomsB`) is a load or needs no side
condition, and each load is of one of these kinds, by its pointer and offset:

* a store (`cstS`): into `rq` (`.n 33`), its word `rho` times a word of `eq_q`; into `pmask`
  (`.n 32`), its word a selector or a slot's weight times `q_keccak`'s selector; into `pi_pt`
  (`.n 38`), `rm` or `0`; into `tq` (`.n 39`), one of `eqtree`'s stores;
* a fresh load (`cstFreshB`): through `kappa_base`, `kaps`, `eq_q`, the selectors, `q_keccak`'s
  ring row, `tq` or the point's slots' coordinates, within their lengths; or through a product of a
  prefix chain and a word fixing its index (`cstDerivB`).

`cstNodeOk`: the body with the dispatch taken is atoms and calls (`cstH0`, `cstRest`), its ten
allocations in `cstH0`, no `frameAddr`, every atom exact, quiet and no heap hint, its calls
`cstRestCalls` after the dispatch.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Stack LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link

@[expose] public section

/-- The atoms before the final assertion. -/
def cstAtomsB : List Atom := atomsOf (cstBodyB ++ cstTail0)

/-- `check_stack_terminal`'s stores. -/
def cstS : List Atom := storesOf 23 cstBody

/-- A store into `rq` at `q`: `rho` times the word of `eq_q` at `62 + q`. -/
def cstRqB (S B : List Atom) (d : V) (q : ℕ) : Bool :=
  decide (d = .n d.idx) && decide (13 < d.idx) && decide (q < 33) &&
    decide (Atom.mul d (.n 13) (.n (d.idx - 1)) ∈ B) && decide (Atom.load (.n (d.idx - 1)) (.n 11) (62 + q) ∈ B) &&
    !decide (Atom.load (.n (d.idx - 1)) (.n 11) (62 + q) ∈ S)

/-- A store into `pmask` at `q`: pointer `q`'s mask. -/
def cstMaskB (S B : List Atom) (d : V) (q : ℕ) : Bool :=
  decide (q < 33) && (if ptrKinds.getD q 0 < 52 then
    decide (Atom.load d (.n 43) (ptrKinds.getD q 0) ∈ B) && !decide (Atom.load d (.n 43) (ptrKinds.getD q 0) ∈ S)
  else decide (d = .n d.idx) && decide (52 < d.idx) && decide (Atom.mul d (.n (d.idx - 1)) (.n 52) ∈ B) &&
    decide (Atom.load (.n (d.idx - 1)) (.n 39) (ptrKinds.getD q 0 + 10) ∈ B) &&
    !decide (Atom.load (.n (d.idx - 1)) (.n 39) (ptrKinds.getD q 0 + 10) ∈ S))

/-- A store into `pi_pt` at `off`: `rm`, then zeros. -/
def cstPiB (B : List Atom) (d : V) (off : ℕ) : Bool :=
  (decide (d = .n 9) && decide (off = 0)) ||
    (decide (1 ≤ off) && decide (off < 31) && decide (Atom.const d (word 0 0) ∈ B))

/-- The value `.n m` is the `kaps` word of a sent column below `52`. -/
def cstSentKB (S B : List Atom) (m : ℕ) : Bool :=
  sentList.any fun k => decide (k < 52) && decide (Atom.load (.n m) (.n 3) k ∈ B) &&
    !decide (Atom.load (.n m) (.n 3) k ∈ S)

/-- A load through a prefix chain times the word fixing its index. -/
def cstDerivB (S B : List Atom) (p : V) (off : ℕ) : Bool :=
  decide (p = .n p.idx) && decide (52 < p.idx) &&
    ((decide (off = 0) && decide (Atom.mul p (.n 36) (.n 8) ∈ B)) ||
      (decide (off = 0) && decide (Atom.mul p (.n 37) (.n 8) ∈ B)) ||
      (decide (off = 0) && decide (Atom.mul p (.n 40) (.n 4) ∈ B)) ||
      (decide (off = 6) && decide (Atom.mul p (.n 35) (.n 51) ∈ B)) ||
      (decide (off = 0) && decide (Atom.mul p (.n 34) (.n 51) ∈ B)) ||
      (decide (off = 0) && decide (Atom.mul p (.n 34) (.n (p.idx - 1)) ∈ B) && cstSentKB S B (p.idx - 1)))

/-- A fresh load's pointer and offset. -/
def cstFreshB (S B : List Atom) (p : V) (off : ℕ) : Bool :=
  (decide (p = .n 1) && decide (off < 8)) || (decide (p = .n 3) && decide (off < 52)) ||
    (decide (p = .n 11) && decide (62 ≤ off) && decide (off < 95)) || (decide (p = .n 43) && decide (off < 52)) ||
    (decide (p = .n 59) && decide (off < 64)) || (decide (p = .n 39) && decide (off < 126)) ||
    (decide (p = .n 254) && decide (off < 6)) || cstDerivB S B p off

/-- An atom's kind. -/
def cstAtomB (S B : List Atom) : Atom → Bool
  | .load d p off =>
    if decide (Atom.load d p off ∈ S) then
      (decide (p = .n 33) && cstRqB S B d off) || (decide (p = .n 32) && cstMaskB S B d off) ||
        (decide (p = .n 38) && cstPiB B d off) ||
        (decide (p = .n 39) && decide (Atom.load d p off ∈ eqStoresAt (.n 39) 0 255 6))
    else cstFreshB S B p off
  | a => !needsSide a

/-- **What the kernel checks of the atoms.** -/
def cstAtomsOk : Bool :=
  cstAtomsB.all (cstAtomB cstS cstAtomsB) && (eqReadsAt (.n 254) (.n 39) 0 0 255 6).all (fun a => !decide (a ∈ cstS))

set_option maxRecDepth 100000 in
theorem cstAtomsOk_ok : cstAtomsOk = true := by decide +kernel

/-- The calls after the dispatch. -/
def cstRestCalls : List Call :=
  [⟨"rs_eq_run", [.n 56, .n 18, .n 58, .n 12], [.n 59], true⟩,
    ⟨"ring_rows", [.n 31, .n 5, .n 18, .n 12, .n 6], [], true⟩,
    ⟨"ring_cols__L5", [.n 470, .n 33, .n 32], [.n 471], true⟩,
    ⟨"ring_cols__L5", [.n 483, .n 485, .n 487], [.n 488], true⟩,
    ⟨"ring_cols__L3", [.n 499, .n 501, .n 503], [.n 504], true⟩,
    ⟨"ring_cols__L5", [.n 517, .n 519, .n 521], [.n 522], true⟩,
    ⟨"ring_cols__L5", [.n 535, .n 537, .n 539], [.n 540], true⟩,
    ⟨"ring_cols__L10", [.n 564, .n 566, .n 568], [.n 569], true⟩,
    ⟨"eq_prefix_chain", [.n 36, .n 572, .n 7, .n 18, .n 8], [], true⟩,
    ⟨"eq_prefix_chain", [.n 37, .n 609, .n 38, .n 18, .n 8], [], true⟩,
    ⟨"eq_prefix_chain", [.n 35, .n 612, .n 10, .n 18, .n 614], [], true⟩,
    ⟨"eq_prefix_chain", [.n 40, .n 615, .n 22, .n 18, .n 4], [], true⟩,
    ⟨"eq_prefix_chain", [.n 34, .n 616, .n 5, .n 18, .n 6], [], true⟩]

/-- The allocations. -/
def cstAllocs : List (V × (ℕ ⊕ V)) :=
  [(.n 31, .inr (.n 30)), (.n 32, .inl 33), (.n 33, .inl 33), (.n 34, .inl 42), (.n 35, .inl 42),
    (.n 36, .inl 42), (.n 37, .inl 42), (.n 38, .inl 31), (.n 39, .inl 126), (.n 40, .inl 31)]

/-- An atom exact, quiet, with no heap hint. -/
def cstPlainB (a : Atom) : Bool :=
  (match a with
    | .hint (.alloc ..) | .hint (.allocDyn ..) => true
    | .hint _ => false
    | _ => true) && (atomHeapDest? a).isNone

/-- **What the kernel checks of the node.** -/
def cstNodeOk : Bool :=
  cstH0.all atomOrCall && cstRest.all atomOrCall && decide (cstH0.filterMap Stmt.allocSz = cstAllocs) &&
    decide (cstRest.filterMap Stmt.allocSz = []) && decide (cstH0.filterMap Stmt.addrS = []) &&
    decide (cstRest.filterMap Stmt.addrS = []) && (atomsOf (cstH0 ++ cstRest)).all cstPlainB

set_option maxRecDepth 100000 in
theorem cstNodeOk_ok : cstNodeOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cstH0_calls : callsOfB cstH0 = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem cstRest_calls : callsOfB cstRest = cstRestCalls := rfl

/-! ## Membership -/

theorem cstBodyA_split : cstBodyA = cstH0 ++ .dispatch (.n 42) cstArms cstArgsV [.n 43] :: cstRest := by
  have h := cstBody_split
  rw [cstBody] at h
  have h' : cstBodyA ++ [.ret []] = (cstH0 ++ .dispatch (.n 42) cstArms cstArgsV [.n 43] :: cstRest) ++ [.ret []] := by
    rw [h]; simp
  exact List.append_cancel_right h'

theorem mem_cstBody_of_B {s : Stmt} (h : s ∈ cstBodyB ++ cstTail0) : s ∈ cstBody := by
  rw [cstBody, cstBodyA_eq]
  exact List.mem_append_left _ (List.mem_append_left _ h)

/-- An atom of the body with the dispatch taken is one before the assertion, or the assertion. -/
theorem mem_B_of_preJ {j : ℕ} {a : Atom} (h : Stmt.atom a ∈ cstPreJ j) :
    Stmt.atom a ∈ cstBodyB ++ cstTail0 ∨ a = .assertEq (.n 924) (.n 21) := by
  have hA : Stmt.atom a ∈ cstBodyA := by
    rw [cstBodyA_split]
    simp only [cstPreJ, List.mem_append, List.mem_cons] at h ⊢
    rcases h with h | h | h
    · exact Or.inl h
    · cases h
    · exact Or.inr (Or.inr h)
  rw [cstBodyA_eq, List.mem_append, List.mem_singleton] at hA
  rcases hA with h | h
  · exact Or.inl h
  · exact Or.inr (Stmt.atom.inj h)

theorem mem_body_of_preJ {j : ℕ} {a : Atom} (h : Stmt.atom a ∈ cstPreJ j) : Stmt.atom a ∈ cstBody := by
  rcases mem_B_of_preJ h with h | rfl
  · exact mem_cstBody_of_B h
  · rw [cstBody, cstBodyA_eq]; simp

end
end LeanVM.Guest.B1.VsC
