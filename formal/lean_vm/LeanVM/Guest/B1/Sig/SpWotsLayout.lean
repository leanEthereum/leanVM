/-
  LeanVM.Guest.B1.Sig.SpWotsLayout

  Where `sp_wots`'s template (`SpWotsT`) puts its groups, its arms and its chains' starts: the
  groups' running product, encoding and base, the arms' bases, and the value each chain's start is
  hinted into, for given arms.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsT
public import LeanVM.Guest.B1.Sig.WotsGroup
public import LeanVM.Core.Renumber

/-!
# `sp_wots`'s layout

Group `p`'s dispatch selects on its digit word `n(16 + p)` among the `64` arms `armsM spW`, laid out
from its base `vb + 6`: arm `k` is `armM spW`, which below `4^n` is the shared arm `armT spW`.

* `spArmK`, `spArmsT`, `spArmBase`, `spArmB`: arm `k` of the group from base `vb`, from base `b`;
  the arms; the base arm `k + j` starts from; the base of arm `k`;
* `spState`, `spMatch`, `spGroupsT_eq`, `spGroupsT_fst`: group `p`'s running product, encoding and
  base; its dispatch; the dispatches from the states;
* `spStartAt K i`: the value chain `i`'s start is hinted into when group `p = i / 3` takes arm `K p`;
* `spZero`, `spR`, `spRen`, `spBody`: the steps without an address constant (chain `0`'s first, in
  the first group's arms `k` with `k % 4 = 0`), each leaving two of its template's three values
  unused, and the guest's numbering: the template's with those removed, `sp_wots`'s body the
  template renamed.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Core LeanVM.Parameters

@[expose] public section

/-! ## The arms -/

/-- Arm `k` of the group from base `vb`, from base `b`: `armM spW`. -/
def spArmK (first n : Nat) (fold : Bool) (vb : Nat) (prodIn encIn : V) (k b : Nat) : List Stmt × Nat :=
  armM spW (spSlot fold vb) first n fold prodIn encIn (.n (spProd fold n vb)) (.n (spEnc fold n vb)) k b

/-- The arms `k ..< k + m` of the group from base `vb`, from base `b`. -/
def spArmsT (first n : Nat) (fold : Bool) (vb : Nat) (prodIn encIn : V) (m k b : Nat) :
    List (List Stmt) × Nat :=
  armsM spW (spSlot fold vb) first n fold prodIn encIn (.n (spProd fold n vb)) (.n (spEnc fold n vb)) m k b

/-- The base arm `k + j` of `spArmsT` from arm `k` at `b` starts from. -/
def spArmBase (first n : Nat) (fold : Bool) (vb : Nat) (prodIn encIn : V) (k j b : Nat) : Nat :=
  armBaseM spW (spSlot fold vb) first n fold prodIn encIn (.n (spProd fold n vb)) (.n (spEnc fold n vb))
    k j b

/-- The base of arm `k` of the group from base `vb`. -/
def spArmB (first n : Nat) (fold : Bool) (vb : Nat) (prodIn encIn : V) (k : Nat) : Nat :=
  spArmBase first n fold vb prodIn encIn 0 k (vb + 6)

theorem spGroupArms_eq (p : Nat) (prodIn encIn : V) (vb : Nat) :
    spGroupArms p prodIn encIn vb = spArmsT (3 * p) (spN p) (p == 0) vb prodIn encIn 64 0 (vb + 6) := rfl

/-! ## The groups -/

/-- Group `p`'s running product's and encoding's cells and its base. -/
def spState : Nat → V × V × Nat
  | 0 => (.n 0, .n 0, spPad)
  | p + 1 =>
      let st := spState p
      (.n (spProd (p == 0) (spN p) st.2.2), .n (spEnc (p == 0) (spN p) st.2.2),
        (spGroupArms p st.1 st.2.1 st.2.2).2 - 6)

theorem spState_zero : spState 0 = (.n 0, .n 0, spPad) := by rw [spState]

theorem spState_succ (p : Nat) : spState (p + 1) =
    (.n (spProd (p == 0) (spN p) (spState p).2.2), .n (spEnc (p == 0) (spN p) (spState p).2.2),
      (spGroupArms p (spState p).1 (spState p).2.1 (spState p).2.2).2 - 6) := by
  rw [spState]

/-- Group `p`'s dispatch. -/
def spMatch (p : Nat) : Stmt :=
  .match_ (.n (spDg + p)) (spGroupArms p (spState p).1 (spState p).2.1 (spState p).2.2).1

theorem spGroupsT_fst : ∀ (m p : Nat),
    (spGroupsT m p (spState p).1 (spState p).2.1 (spState p).2.2).1 =
      (List.range m).map (fun q => spMatch (p + q))
  | 0, _ => rfl
  | m + 1, p => by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [spGroupsT]
      have := spGroupsT_fst m (p + 1)
      rw [spState_succ p] at this
      rw [this]
      congr 1
      refine List.map_congr_left fun q _ => ?_
      simp only [Function.comp_apply, show p + 1 + q = p + (q + 1) by omega]

theorem spGroupsT_eq : ∀ (m p : Nat),
    (spGroupsT m p (spState p).1 (spState p).2.1 (spState p).2.2).2 =
      ((spState (p + m)).2.2, (List.range m).flatMap (fun j => (List.range (spN (p + j))).map fun r =>
        V.n (spSlot (p + j == 0) (spState (p + j)).2.2 r 2)),
        (spState (p + m)).1, (spState (p + m)).2.1)
  | 0, p => by rw [spGroupsT]; simp
  | m + 1, p => by
      have ih := spGroupsT_eq m (p + 1)
      rw [spState_succ p] at ih
      simp only [spGroupsT]
      rw [ih, show p + 1 + m = p + (m + 1) by omega]
      simp only [Prod.mk.injEq, true_and, and_true]
      rw [List.range_succ_eq_map (n := m), List.flatMap_cons, List.flatMap_map]
      simp only [Nat.add_zero]
      congr 1
      apply List.flatMap_congr
      intro j _
      simp only [show p + 1 + j = p + (j + 1) by omega]

/-- `spGs` from the states: the codeword's base after its 22 dispatches, the tips, product and
encoding. -/
theorem spGs_eq : spGs.2 = ((spState 22).2.2, (List.range 22).flatMap (fun j => (List.range (spN j)).map
    fun r => V.n (spSlot (j == 0) (spState j).2.2 r 2)), (spState 22).1, (spState 22).2.1) := by
  have h := spGroupsT_eq 22 0
  rw [spState_zero] at h
  simp only [Nat.zero_add] at h
  unfold spGs
  rw [h]

theorem spGs_fst : spGs.1 = (List.range 22).map spMatch := by
  have h := spGroupsT_fst 22 0
  rw [spState_zero] at h
  simp only [Nat.zero_add] at h
  unfold spGs
  rw [h]

theorem spC_eq : spC = (spState 22).2.2 + 6 := by rw [spC, spGs_eq]

/-- **Where chain `i`'s start is hinted** when group `p = i / 3` takes arm `K p`: arm `K p`'s start
of chain `i % 3` (`armStart`). -/
def spStartAt (K : Nat → Nat) (i : Nat) : V :=
  let p := i / 3
  let st := spState p
  let k := K p
  armStart spW (spSlot (p == 0) st.2.2) (p == 0) k (spArmB (3 * p) (spN p) (p == 0) st.2.2 st.1 st.2.1 k)
    (i % 3)

/-! ## The guest's numbering -/

/-- The constant cells of the steps without an address constant: chain `0`'s first step in the
first group's arm `4j`, one above the arm's base (the chain's hint)
(`spZero_eq`). -/
def spZero : List Nat :=
  [133, 245, 334, 411, 472, 561, 638, 703, 752, 829, 894, 947, 984, 1045, 1094, 1131]

theorem spZero_eq : spZero = (List.range 16).map fun j => spArmB 0 3 true spPad (.n 0) (.n 0) (4 * j) + 1 := by
  decide +kernel

/-- The guest's number of the template's value `i`: two fewer for each step without an address
constant below it. -/
def spR (i : Nat) : Nat := i - 2 * spZero.countP (· < i)

/-- The guest's numbering, on values. -/
def spRen (v : V) : V := ⟨v.path, v.tag, spR v.idx⟩

/-- **`sp_wots`'s body**: the template, renumbered as the guest numbers it. -/
def spBody : List Stmt := Stmt.renameList spRen spBodyT

theorem renameList_append (r : V → V) : ∀ (a b : List Stmt),
    Stmt.renameList r (a ++ b) = Stmt.renameList r a ++ Stmt.renameList r b
  | [], _ => rfl
  | s :: a, b => by
      simp only [List.cons_append, Stmt.renameList, renameList_append r a b]

theorem renameList_length (r : V → V) : ∀ (a : List Stmt), (Stmt.renameList r a).length = a.length
  | [] => rfl
  | s :: a => by simp only [Stmt.renameList, List.length_cons, renameList_length r a]

/-! ## The template's parts -/

/-- The codeword's checks after the dispatches and the leaf's `A1`. -/
def spChecks : List Stmt :=
  [.atom (.assertEq spGs.2.2.2.2 (.n 3)), cst spC spTarget,
    .atom (.assertEq spGs.2.2.2.1 (.n spC)), cst (spC + 1) spPkC,
    addS (.n (spC + 2)) (.n 2) (.n (spC + 1))]

/-- The copies `at = [a0, a1]`. -/
def spCopies : List Stmt := [copyS (.n 4) (.n 1), copyS (.n 5) (.n 2)]

/-- The powers `g^s` at `n(6 + s)`. -/
def spPowers : List Stmt := (List.range 10).map fun s => cst (6 + s) (word (2 ^ s) 0)

/-- What the body sets before its dispatches: the copies, the powers, the hints, the range checks,
the padding run and the hoisted constant. -/
def spPre : List Stmt :=
  spCopies ++ spPowers ++ spHints ++ spRanges ++ padRun spPad ++ [cst (spPad + 5) closeLane]

/-- The body before its checks: what it sets first and the dispatches. -/
def spHeadT : List Stmt := spPre ++ spGs.1

/-- The body from its checks, the leaf's message `L`: the checks, the message, the copy and the
return. -/
def spTailOf (L : List Stmt × Nat × Nat) : List Stmt :=
  spChecks ++ L.1 ++ [copyS (.n L.2.1) (.n L.2.2), .ret [.n L.2.1]]

theorem spBodyT_split : spBodyT = spHeadT ++ spTailOf spLeafK := by
  simp only [spBodyT, spHeadT, spTailOf, spChecks, spPre, spCopies, spPowers, List.append_assoc,
    List.cons_append, List.nil_append]

end
end LeanVM.Guest.B1.Sig
