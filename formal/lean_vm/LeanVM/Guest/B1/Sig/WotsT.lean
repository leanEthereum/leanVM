/-
  LeanVM.Guest.B1.Sig.WotsT

  The WOTS+C codeword groups both signature verifiers share, as templates (`walk`, `walk_group`,
  the digit dispatch, `lean_ethereum.py`).
-/

module

public import LeanVM.Guest.B1.Sig.Shapes

/-!
# WOTS+C groups, as templates

Both verifiers walk their chains with the same code (`walk`, `walk_group`) and differ only in a
chain step (`WotsT.step`): leanXMSS hashes `P`, the step's address computed once per signature, the
value and the chain index (one constant before the outputs, `size = 1`); leanSPHINCS computes the
address from the index, the chain and the step and hashes `P`, it and the value, 48 bytes (three
values before the outputs, `size = 3`).

* `walkT`: chain `i` from digit `d`: the hinted start at the base, then steps `d, …, 2`, step `s`
  writing slot `s` of the chain in `walks` (one cell, `walks[o:o + 1]`); the step's constants
  `stride` apart (`size + 1` in the arm that lays out the slots, `size` elsewhere); at `d = 3` the start is hinted into the tip;
* `armT`, `armsT`, `groupArmsT`, `groupD`: arm `k` of a group's dispatch (the walks at the
  base-4 digits of `k`, then the digit sum folded into the product, in the exponent, and the digits
  into the encoding), the `4^n` arms laid out from `b + 6`, and the group with its hint, its range
  check, what it sets before its dispatch (`pre`: `sp_wots`'s padding run), the `2^63` the compiler
  hoists above an all-`@inline` `match` (`closeLane`, unread: each arm sets its own) and the
  `match`; `fold` marks the first
  group, each of whose arms sets its product to its power and its encoding to its literal.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-- A scheme's chain step and powers. -/
structure WotsT where
  /-- Step `s` of chain `i` on value `v`: its statements, its fresh values from the base, then the
  `KECCAK` writing the slot from `o`. -/
  step : Nat → Nat → V → Nat → Nat → List Stmt
  /-- The fresh values of a step before its outputs. -/
  size : Nat
  /-- The cell holding `g^s`. -/
  power : Nat → V
  /-- The constant arm `k` of a group of `n` digits from digit `first` adds to the encoding: by
  default the base-4 number `k·4^first` (leanXMSS's, low digit first); leanSPHINCS's places each
  digit most significant first in its byte (`base_2b`). -/
  enc : Nat → Nat → Nat → Nat := fun first _ k => k * 4 ^ first
  /-- Arm `0` adds nothing (it copies the running encoding). -/
  enc_zero : ∀ first n, enc first n 0 = 0 := by intros; simp

/-- Chain `i`'s walk from digit `d` (`walk`). -/
def walkT (W : WotsT) (i : Nat) (slot : Nat → Nat) (stride d b : Nat) : List Stmt :=
  if d = 3 then [hintW "chain_starts" [.n (slot 2)]]
  else hintW "chain_starts" [.n b] :: (List.range (3 - d)).flatMap fun j =>
    W.step i (d + j) (if j = 0 then .n b else .n (slot (d + j - 1))) (b + 1 + j * stride)
      (slot (d + j))

/-- The fresh values of a walk. -/
def walkSize (stride d : Nat) : Nat := if d = 3 then 0 else 1 + (3 - d) * stride

/-- The walks of chains `first + r`, `r ..< r + m`, at the base-4 digits of `k`, from `b`. -/
def walksT (W : WotsT) (slots : Nat → Nat → Nat) (first k stride : Nat) :
    Nat → Nat → Nat → List Stmt × Nat
  | 0, _, b => ([], b)
  | m + 1, r, b =>
      let d := k / 4 ^ r % 4
      let rest := walksT W slots first k stride m (r + 1) (b + walkSize stride d)
      (walkT W (first + r) (slots r) stride d b ++ rest.1, rest.2)

/-- Arm `k` of a group from base `b`: the walks, then the product and the encoding folded in. -/
def armT (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) (k b : Nat) : List Stmt × Nat :=
  let ws := walksT W slots first k (if k = 0 then W.size + 1 else W.size) n 0 b
  if fold then
    (ws.1 ++ [copyS prodOut (W.power (digitSum k n)), .atom (.const encOut (lit (W.enc first n k)))], ws.2)
  else if k = 0 then (ws.1 ++ [mulS prodOut prodIn (W.power (digitSum k n)), copyS encOut encIn], ws.2)
  else (ws.1 ++ [mulS prodOut prodIn (W.power (digitSum k n)), cst ws.2 (lit (W.enc first n k)),
    addS encOut encIn (.n ws.2)], ws.2 + 1)

/-- Arms `k ..< k + m` from base `b`; arm `0` allocates the outputs after its walks. -/
def armsT (W : WotsT) (slots : Nat → Nat → Nat) (first n : Nat) (fold : Bool)
    (prodIn encIn prodOut encOut : V) : Nat → Nat → Nat → List (List Stmt) × Nat
  | 0, _, b => ([], b)
  | m + 1, k, b =>
      let a := armT W slots first n fold prodIn encIn prodOut encOut k b
      let rest := armsT W slots first n fold prodIn encIn prodOut encOut m (k + 1)
        (if k = 0 then a.2 + 2 else a.2)
      (a.1 :: rest.1, rest.2)

/-- Where arm `0` of a group from base `b` starts its first walk. -/
def groupStart (_fold : Bool) (b : Nat) : Nat := b + 6
/-- The fresh values of a chain in arm `0`. -/
def chainStride (W : WotsT) : Nat := 1 + 3 * (W.size + 1)
/-- The slot of chain `r`'s step `s` in a group from base `b`. -/
def slotsT (W : WotsT) (fold : Bool) (b : Nat) (r s : Nat) : Nat :=
  groupStart fold b + chainStride W * r + 1 + (W.size + 1) * s + W.size
def prodT (W : WotsT) (fold : Bool) (n b : Nat) : V := .n (groupStart fold b + chainStride W * n)
def encT (W : WotsT) (fold : Bool) (n b : Nat) : V := .n (groupStart fold b + chainStride W * n + 1)

/-- The `2^63` a group sets above its dispatch: the compiler hoists the arms' common constants
(the two-to-one closing lane of `walk`'s one-block `keccak`) above an all-`@inline` `match`; the
arms set their own, so this one is unread. -/
def closeLane : E := word (2 ^ 63) 0

/-- The `4^n` arms of a group laid out from base `b`: arm `0` from `b + 6`. -/
def groupArmsT (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (b : Nat) :
    List (List Stmt) × Nat :=
  armsT W (slotsT W fold b) first n fold prodIn encIn (prodT W fold n b) (encT W fold n b) (4 ^ n) 0
    (b + 6)

/-- A group of `n` digits, its digit word hinted at `d`, its arms laid out from base `b`: the
digit hint, its range check, the statements `pre`, the hoisted constant at `b + 5` and the dispatch
over the `4^n` digit values; the statements and the next base. -/
def groupD (W : WotsT) (first n : Nat) (fold : Bool) (prodIn encIn : V) (d : Nat) (pre : List Stmt)
    (b : Nat) : List Stmt × Nat :=
  (hintW "digits" [.n d] :: rangeS (.n d) (word (2 ^ (4 ^ n - 1)) 0) (d + 1) ++ pre ++
    [cst (b + 5) closeLane, .match_ (.n d) (groupArmsT W first n fold prodIn encIn b).1],
    (groupArmsT W first n fold prodIn encIn b).2)

end
end LeanVM.Guest.B1.Sig
