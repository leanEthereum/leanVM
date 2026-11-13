/-
  LeanVM.Guest.B1.Sig.SpWotsLayout

  Where `sp_wots`'s template (`SpWotsT`) puts its groups, its arms and its chains' starts: the
  groups' running product, encoding and base, the arms' bases, and the value each chain's start is
  hinted into, for given digit words.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsT
public import LeanVM.Guest.B1.Sig.WotsGroup
public import LeanVM.Guest.Renumber

/-!
# `sp_wots`'s layout

A group of `sp_wots` is the shared group (`groupD`) over `spW`, its digit word at its base `B`, its
arms laid out from `spL fold B`: so its arms are the shared arms (`armT spW`).

* `spArmK`, `spArmB`, `spArmBase`, `spArmsT`: arm `k` of the group from `B`, from base `b`; the base
  of arm `k`; the base arm `k + j` starts from; the arms (`groupArmsT`);
* `spState`, `spGroupsT_eq`: group `p`'s running product, encoding and base (`cwState` for `sp_wots`);
* `spN`, `spStartAt K i`: group `p`'s digits and the value chain `i`'s start is hinted into when
  group `p` takes arm `K p`;
* `spZero`, `spR`, `spRen`, `spBody`: the steps without an address constant (chain `0`'s first, in
  the first group's arms `k` with `k % 4 = 0`), each leaving two of its template's three values
  unused, and the guest's numbering: the template's with those removed, `sp_wots`'s body the
  template renamed.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-! ## The arms -/

/-- Arm `k` of the group from `B`, from base `b`: the shared arm over `spW`. -/
def spArmK (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k b : Nat) : List Stmt × Nat :=
  armT spW (spSlot fold B) first n fold prodIn encIn (.n (spProd fold n B)) (.n (spEnc fold n B)) k b

/-- The arms `k ..< k + m` of the group from `B`, from base `b`. -/
def spArmsT (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (m k b : Nat) :
    List (List Stmt) × Nat :=
  armsT spW (spSlot fold B) first n fold prodIn encIn (.n (spProd fold n B)) (.n (spEnc fold n B)) m k b

/-- The base arm `k + j` of `spArmsT` from arm `k` at `b` starts from. -/
def spArmBase (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k j b : Nat) : Nat :=
  armBase spW (spSlot fold B) first n fold prodIn encIn (.n (spProd fold n B)) (.n (spEnc fold n B)) k j b

/-- The base of arm `k` of the group from `B`. -/
def spArmB (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k : Nat) : Nat :=
  armB spW first n fold prodIn encIn (spL fold B) k

theorem spArmB_eq (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k : Nat) :
    spArmB first n fold B prodIn encIn k = spArmBase first n fold B prodIn encIn 0 k (spL fold B + 6) := rfl

theorem spGroupT_end (first n : Nat) (fold : Bool) (prodIn encIn : V) (B : Nat) :
    (spGroupT first n fold prodIn encIn B).2 = spArmB first n fold B prodIn encIn (4 ^ n) := by
  simp only [spGroupT, groupD, groupArmsT]
  rw [armsT_snd]
  rfl

/-! ## The groups -/

/-- Group `p`'s running product's and encoding's cells and its base. -/
def spState : Nat → V × V × Nat
  | 0 => (.n 0, .n 0, 16)
  | p + 1 =>
      let st := spState p
      (.n (spProd (p == 0) 3 st.2.2), .n (spEnc (p == 0) 3 st.2.2),
        (spGroupT (3 * p) 3 (p == 0) st.1 st.2.1 st.2.2).2)

theorem spState_zero : spState 0 = (.n 0, .n 0, 16) := by rw [spState]

theorem spState_succ (p : Nat) : spState (p + 1) =
    (.n (spProd (p == 0) 3 (spState p).2.2), .n (spEnc (p == 0) 3 (spState p).2.2),
      (spGroupT (3 * p) 3 (p == 0) (spState p).1 (spState p).2.1 (spState p).2.2).2) := by
  rw [spState]

theorem spGroupsT_succ (m p : Nat) (prod enc : V) (B : Nat) : spGroupsT (m + 1) p prod enc B =
    ((spGroupT (3 * p) 3 (p == 0) prod enc B).1 ++
        (spGroupsT m (p + 1) (.n (spProd (p == 0) 3 B)) (.n (spEnc (p == 0) 3 B))
          (spGroupT (3 * p) 3 (p == 0) prod enc B).2).1,
      (spGroupsT m (p + 1) (.n (spProd (p == 0) 3 B)) (.n (spEnc (p == 0) 3 B))
          (spGroupT (3 * p) 3 (p == 0) prod enc B).2).2.1,
      (List.range 3).map (fun r => V.n (spSlot (p == 0) B r 2)) ++
        (spGroupsT m (p + 1) (.n (spProd (p == 0) 3 B)) (.n (spEnc (p == 0) 3 B))
          (spGroupT (3 * p) 3 (p == 0) prod enc B).2).2.2.1,
      (spGroupsT m (p + 1) (.n (spProd (p == 0) 3 B)) (.n (spEnc (p == 0) 3 B))
          (spGroupT (3 * p) 3 (p == 0) prod enc B).2).2.2.2) := by
  rw [spGroupsT]

theorem spGroupsT_eq : ∀ (m p : Nat),
    (spGroupsT m p (spState p).1 (spState p).2.1 (spState p).2.2).2 =
      ((spState (p + m)).2.2, (List.range m).flatMap (fun j => (List.range 3).map fun r =>
        V.n (spSlot (p + j == 0) (spState (p + j)).2.2 r 2)),
        (spState (p + m)).1, (spState (p + m)).2.1)
  | 0, p => by rw [spGroupsT]; simp
  | m + 1, p => by
      have ih := spGroupsT_eq m (p + 1)
      rw [spState_succ p] at ih
      rw [spGroupsT_succ, ih, show p + 1 + m = p + (m + 1) by omega]
      simp only [Prod.mk.injEq, true_and, and_true]
      rw [List.range_succ_eq_map (n := m), List.flatMap_cons, List.flatMap_map]
      simp only [Nat.add_zero]
      congr 1
      apply List.flatMap_congr
      intro j _
      simp only [show p + 1 + j = p + (j + 1) by omega]

theorem spGroupsT_fst (m p : Nat) :
    (spGroupsT (m + 1) p (spState p).1 (spState p).2.1 (spState p).2.2).1 =
      (spGroupT (3 * p) 3 (p == 0) (spState p).1 (spState p).2.1 (spState p).2.2).1 ++
        (spGroupsT m (p + 1) (spState (p + 1)).1 (spState (p + 1)).2.1 (spState (p + 1)).2.2).1 := by
  rw [spGroupsT_succ, spState_succ p]

/-- `spGs` from the states: the codeword's base after its 21 groups, the tips, product and encoding. -/
theorem spGs_eq : spGs.2 = ((spState 21).2.2, (List.range 21).flatMap (fun j => (List.range 3).map
    fun r => V.n (spSlot (j == 0) (spState j).2.2 r 2)), (spState 21).1, (spState 21).2.1) := by
  have h := spGroupsT_eq 21 0
  rw [spState_zero] at h
  simp only [Nat.zero_add] at h
  unfold spGs
  rw [h]

theorem spGs_fst : spGs.1 = (spGroupsT 21 0 (spState 0).1 (spState 0).2.1 (spState 0).2.2).1 := by
  rw [spState_zero]; rfl

/-- The digits of group `p`: three, the last chain's one. -/
def spN (p : Nat) : Nat := if p < 21 then 3 else 1

/-- **Where chain `i`'s start is hinted** when group `p = i / 3` takes arm `K p`: arm `K p`'s start of
chain `i % 3` (`armStart`). -/
def spStartAt (K : Nat → Nat) (i : Nat) : V :=
  let p := i / 3
  let st := spState p
  let k := K p
  armStart spW (spSlot (p == 0) st.2.2) (p == 0) k (spArmB (3 * p) (spN p) (p == 0) st.2.2 st.1 st.2.1 k)
    (i % 3)

/-! ## The guest's numbering -/

/-- The constant cells of the steps without an address constant: chain `0`'s first step in the
first group's arm `4j`, two above the arm's base (its encoding's `0`, then the chain's hint)
(`spZero_eq`). -/
def spZero : List Nat :=
  [29, 148, 245, 330, 399, 496, 581, 654, 711, 796, 869, 930, 975, 1044, 1101, 1146]

theorem spZero_eq : spZero = (List.range 16).map fun j => spArmB 0 3 true 16 (.n 0) (.n 0) (4 * j) + 2 := by
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

/-- The codeword's checks after the last group and the leaf's `A1`. -/
def spChecks : List Stmt :=
  [.atom (.assertEq (.n (spEnc false 1 spGs.2.1)) (.n 3)), cst spC spTarget,
    .atom (.assertEq (.n (spProd false 1 spGs.2.1)) (.n spC)), cst (spC + 1) spPkC,
    addS (.n (spC + 2)) (.n 2) (.n (spC + 1))]

/-- The body before its checks: the copies, the powers and the codeword's groups. -/
def spHeadT : List Stmt :=
  [copyS (.n 4) (.n 1), copyS (.n 5) (.n 2)] ++
    (List.range 10).map (fun s => cst (6 + s) (word (2 ^ s) 0)) ++ spGs.1 ++ spLast.1

/-- The body from its checks, the leaf's message `L`: the checks, the message, the copy and the
return. -/
def spTailOf (L : List Stmt × Nat × Nat) : List Stmt :=
  spChecks ++ L.1 ++ [copyS (.n L.2.1) (.n L.2.2), .ret [.n L.2.1]]

theorem spBodyT_split : spBodyT = spHeadT ++ spTailOf spLeafK := by
  simp only [spBodyT, spHeadT, spTailOf, spChecks, List.append_assoc, List.cons_append,
    List.nil_append]

end
end LeanVM.Guest.B1.Sig
