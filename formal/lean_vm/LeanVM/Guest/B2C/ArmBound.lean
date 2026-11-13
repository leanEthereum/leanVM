/-
  LeanVM.Guest.B2C.ArmBound

  `__loop2`'s separately counted arms, bounded for every valuation: `costW` within the sum
  over its counted `match`es of their largest arm (`costMaxW`), `xmssArmC` per opcode, the
  hypothesis `hC` of `cnt_le_weight_arm` (`xmssArmC_spec`).
-/

module

public import LeanVM.Guest.B2C.CntWeight

/-!
# `__loop2`'s arms, bounded

`costW acs σ ss op` adds, along the path `σ` takes through `ss`, the count of each separately
counted arm it passes. Whatever the path, it is at most `costMaxW acs op ss`: an `ite` its larger
side, a `match` its table's largest arm and its larger arm's own (`costMaxArms`). On
`__loop2`'s body (`Data.armFn`) this is `xmssArmC op`, the values `guest-cert` computes
(`Data.armMax`; by `decide +kernel`, every opcode in one walk), so `cnt_le_weight_arm` holds at
`C := xmssArmC`.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- A counted `match`'s largest arm at `op`, `0` if not counted. -/
def keyMax (key : Option (List (List ℕ))) (op : Opcode) : ℕ :=
  match key with
  | some cs => (cs.map fun l => l.getD (opIdx op) 0).foldr max 0
  | none => 0

mutual
/-- The separately counted arms a statement can pass, at most. -/
def costMax1 (acs : List (ℕ × List (List ℕ))) (op : Opcode) : Stmt → ℕ
  | .ite _ z n => max (costMaxW acs op z) (costMaxW acs op n)
  | .match_ x arms => keyMax (armRaw acs x.idx) op + costMaxArms acs op arms
  | _ => 0

/-- The separately counted arms a block can pass, at most. -/
def costMaxW (acs : List (ℕ × List (List ℕ))) (op : Opcode) : List Stmt → ℕ
  | [] => 0
  | s :: ss => costMax1 acs op s + costMaxW acs op ss

/-- The separately counted arms an arm of a `match` can pass, at most. -/
def costMaxArms (acs : List (ℕ × List (List ℕ))) (op : Opcode) : List (List Stmt) → ℕ
  | [] => 0
  | a :: as => max (costMaxW acs op a) (costMaxArms acs op as)
end

theorem nth_getD_le_foldr (i : ℕ) : ∀ (cs : List (List ℕ)) (k : ℕ),
    (listElementOrDefault cs k []).getD i 0 ≤ (cs.map fun l => l.getD i 0).foldr max 0
  | [], _ => by simp [listElementOrDefault]
  | c :: cs, 0 => by simp [listElementOrDefault]
  | c :: cs, k + 1 => by
    simp only [listElementOrDefault, List.map_cons, List.foldr_cons]
    exact (nth_getD_le_foldr i cs k).trans (le_max_right _ _)

section Le

variable (acs : List (ℕ × List (List ℕ))) (σ : Val) (op : Opcode)

mutual
theorem cost1_le_max : ∀ s : Stmt, cost1 acs σ s op ≤ costMax1 acs op s
  | .atom _ => Nat.zero_le _
  | .ite c z n => by
    rw [cost1, costMax1]
    split
    · exact (costW_le_max z).trans (le_max_left _ _)
    · exact (costW_le_max n).trans (le_max_right _ _)
  | .match_ x arms => by
    rw [cost1, costMax1]
    exact costArms_le_max x arms 0 (armRaw acs x.idx)
  | .call .. => Nat.zero_le _
  | .callIf .. => Nat.zero_le _
  | .dispatch .. => Nat.zero_le _
  | .ret _ => Nat.zero_le _

theorem costW_le_max : ∀ ss : List Stmt, costW acs σ ss op ≤ costMaxW acs op ss
  | [] => by rw [costW, costMaxW]; exact Nat.zero_le _
  | s :: ss => by
    rw [costW, costMaxW, Pi.add_apply]
    exact Nat.add_le_add (cost1_le_max s) (costW_le_max ss)

theorem costArms_le_max (x : V) : ∀ (arms : List (List Stmt)) (k : ℕ) (key : Option (List (List ℕ))),
    costArms acs σ x key k arms op ≤ keyMax key op + costMaxArms acs op arms
  | [], _, _ => by rw [costArms]; exact Nat.zero_le _
  | a :: as, k, key => by
    rw [costArms, costMaxArms]
    split
    · rw [Pi.add_apply]
      refine Nat.add_le_add ?_ ((costW_le_max a).trans (le_max_left _ _))
      cases key with
      | none => exact Nat.zero_le _
      | some cs => exact nth_getD_le_foldr _ cs k
    · exact (costArms_le_max x as (k + 1) key).trans
        (Nat.add_le_add_left (le_max_right _ _) _)
end

end Le

/-! ## Every opcode at once

`costMaxW` at each opcode is one walk of the block; `costMaxCW` takes the six in one walk (`C6`),
and agrees with it at each (`costMaxCW_at`). -/

/-- A count per opcode, in `opIdx`'s order. -/
structure C6 where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  c4 : ℕ
  c5 : ℕ
  deriving DecidableEq

/-- The count at an opcode. -/
def C6.at (c : C6) : Opcode → ℕ
  | .xor => c.c0
  | .mulNative => c.c1
  | .setConstant => c.c2
  | .deref => c.c3
  | .jump => c.c4
  | .keccak => c.c5

def C6.zero : C6 := ⟨0, 0, 0, 0, 0, 0⟩

def C6.max (a b : C6) : C6 :=
  ⟨Nat.max a.c0 b.c0, Nat.max a.c1 b.c1, Nat.max a.c2 b.c2, Nat.max a.c3 b.c3, Nat.max a.c4 b.c4,
    Nat.max a.c5 b.c5⟩

def C6.add (a b : C6) : C6 :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3, a.c4 + b.c4, a.c5 + b.c5⟩

/-- The counts of a list in `opIdx`'s order. -/
def C6.ofList (l : List ℕ) : C6 := ⟨l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0, l.getD 5 0⟩

theorem C6.at_zero (op : Opcode) : C6.zero.at op = 0 := by cases op <;> rfl

theorem C6.at_max (a b : C6) (op : Opcode) : (a.max b).at op = Max.max (a.at op) (b.at op) := by
  cases op <;> rfl

theorem C6.at_add (a b : C6) (op : Opcode) : (a.add b).at op = a.at op + b.at op := by
  cases op <;> rfl

theorem C6.at_ofList (l : List ℕ) (op : Opcode) : (C6.ofList l).at op = l.getD (opIdx op) 0 := by
  cases op <;> rfl

/-- `keyMax` at every opcode. -/
def keyMaxC (key : Option (List (List ℕ))) : C6 :=
  match key with
  | some cs => cs.foldr (fun l acc ↦ (C6.ofList l).max acc) C6.zero
  | none => C6.zero

theorem keyMaxC_at (key : Option (List (List ℕ))) (op : Opcode) : (keyMaxC key).at op = keyMax key op := by
  rcases key with _ | cs
  · exact C6.at_zero op
  · induction cs with
    | nil => exact C6.at_zero op
    | cons l cs ih =>
      simp only [keyMaxC, keyMax, List.foldr_cons, List.map_cons] at ih ⊢
      rw [C6.at_max, C6.at_ofList, ih]

mutual
/-- `costMax1` at every opcode. -/
def costMaxC1 (acs : List (ℕ × List (List ℕ))) : Stmt → C6
  | .ite _ z n => (costMaxCW acs z).max (costMaxCW acs n)
  | .match_ x arms => (keyMaxC (armRaw acs x.idx)).add (costMaxCArms acs arms)
  | _ => C6.zero

/-- `costMaxW` at every opcode. -/
def costMaxCW (acs : List (ℕ × List (List ℕ))) : List Stmt → C6
  | [] => C6.zero
  | s :: ss => (costMaxC1 acs s).add (costMaxCW acs ss)

/-- `costMaxArms` at every opcode. -/
def costMaxCArms (acs : List (ℕ × List (List ℕ))) : List (List Stmt) → C6
  | [] => C6.zero
  | a :: as => (costMaxCW acs a).max (costMaxCArms acs as)
end

section At

variable (acs : List (ℕ × List (List ℕ))) (op : Opcode)

mutual
theorem costMaxC1_at : ∀ s : Stmt, (costMaxC1 acs s).at op = costMax1 acs op s
  | .atom _ => C6.at_zero op
  | .ite _ z n => by rw [costMaxC1, costMax1, C6.at_max, costMaxCW_at z, costMaxCW_at n]
  | .match_ x arms => by rw [costMaxC1, costMax1, C6.at_add, keyMaxC_at, costMaxCArms_at arms]
  | .call .. => C6.at_zero op
  | .callIf .. => C6.at_zero op
  | .dispatch .. => C6.at_zero op
  | .ret _ => C6.at_zero op

theorem costMaxCW_at : ∀ ss : List Stmt, (costMaxCW acs ss).at op = costMaxW acs op ss
  | [] => C6.at_zero op
  | s :: ss => by rw [costMaxCW, costMaxW, C6.at_add, costMaxC1_at s, costMaxCW_at ss]

theorem costMaxCArms_at : ∀ arms : List (List Stmt), (costMaxCArms acs arms).at op = costMaxArms acs op arms
  | [] => C6.at_zero op
  | a :: as => by rw [costMaxCArms, costMaxArms, C6.at_max, costMaxCW_at a, costMaxCArms_at as]
end

end At

/-- **`__loop2`'s separately counted arms, per opcode** (leanXMSS's check, inline in it): the sum
of its counted `match`es' largest arms, as `guest-cert` computes them (`Data.armMax`). -/
def xmssArmC (op : Opcode) : ℕ := Data.armMax.getD (opIdx op) 0

-- a kernel evaluation over the body of the function with counted arms (`Data.armFn`)
set_option maxRecDepth 100000 in
theorem costMaxCW_arm :
    costMaxCW (listElementOrDefault Data.cplArms Data.armFn []) (coreOf Data.armFn).body =
      C6.ofList Data.armMax := by
  decide +kernel

theorem costMaxW_xmss (op : Opcode) :
    costMaxW (listElementOrDefault Data.cplArms Data.armFn []) op (coreOf Data.armFn).body = xmssArmC op := by
  rw [← costMaxCW_at, costMaxCW_arm, C6.at_ofList]
  rfl

/-- **`cnt_le_weight_arm`'s `hC` at `xmssArmC`**: `__loop2`'s arms within `xmssArmC`, on
every valuation. -/
theorem xmssArmC_spec : ∀ op σ bufs kids rd args rets,
    (Memory.Tree.node "__loop2" σ bufs kids).Valid coreProgram rd args rets →
      costW (listElementOrDefault Data.cplArms Data.armFn []) σ (coreOf Data.armFn).body op ≤ xmssArmC op :=
  fun op σ _ _ _ _ _ _ => (costW_le_max _ σ op _).trans (costMaxW_xmss op).le

end
end LeanVM.Guest.B2C
