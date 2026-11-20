/-
  LeanVM.Guest.B1.Sig.SpWotsLayout

  Where `sp_wots`'s template (`SpWotsT`) puts its groups, its arms and its chains' starts: the
  groups' base, the arms' bases, and the value each chain's start is hinted into, for given digit
  words, in the guest's numbering.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsT
public import LeanVM.Guest.B1.Sig.WotsGroup

/-!
# `sp_wots`'s layout

A group of `sp_wots` is the shared group (`groupD`) over `spW`, its digit word at its base `B`, its
arms laid out from `spL fold B`: so its arms are the shared arms (`armT spW`). This layout is what
the signature's decoder reads (`SphincsSig.lean`, `Guest/Fast/`).

The body is tied to it through `Guest/Fast`'s tables (`spSel`, `spTabOf`, equal to this layout by
`Fast/SpWotsTablesCheck.lean`): `sp_owners` (`SpWotsLinks1`) checks that the values they name own
the reference function's hints. So `B1/Sig/SpWotsLinks` imports `Guest/Fast`, a layer above it;
nothing is trusted of the tables, which are checked.

* `spArmK`, `spArmB`, `spArmBase`: arm `k` of the group from `B`, from base `b`; the base of arm
  `k`; the base arm `k + j` starts from;
* `spState`: group `p`'s running product, encoding and base;
* `spN`, `spStartAt K i`: group `p`'s digits and the value chain `i`'s start is hinted into when
  group `p` takes arm `K p`;
* `spZero`, `spR`, `spRen`: the steps without an address constant (chain `0`'s first, in the first
  group's arms `k` with `k % 4 = 0`), each leaving two of its template's three values unused, and
  the guest's numbering: the template's with those removed.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-! ## The arms -/

/-- Arm `k` of the group from `B`, from base `b`: the shared arm over `spW`. -/
def spArmK (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k b : Nat) : List Stmt × Nat :=
  armT spW (spSlot fold B) first n fold prodIn encIn (.n (spProd fold n B)) (.n (spEnc fold n B)) k b

/-- The base arm `k + j` of the group starts from, arm `k` at `b`. -/
def spArmBase (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k j b : Nat) : Nat :=
  armBase spW (spSlot fold B) first n fold prodIn encIn (.n (spProd fold n B)) (.n (spEnc fold n B)) k j b

/-- The base of arm `k` of the group from `B`. -/
def spArmB (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k : Nat) : Nat :=
  armB spW first n fold prodIn encIn (spL fold B) k

theorem spArmB_eq (first n : Nat) (fold : Bool) (B : Nat) (prodIn encIn : V) (k : Nat) :
    spArmB first n fold B prodIn encIn k = spArmBase first n fold B prodIn encIn 0 k (spL fold B + 6) := rfl

/-! ## The groups -/

/-- Group `p`'s running product's and encoding's cells and its base. -/
def spState : Nat → V × V × Nat
  | 0 => (.n 0, .n 0, 16)
  | p + 1 =>
      let st := spState p
      (.n (spProd (p == 0) 3 st.2.2), .n (spEnc (p == 0) 3 st.2.2),
        (spGroupT (3 * p) 3 (p == 0) st.1 st.2.1 st.2.2).2)

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
first group's arm `4j`, one above the arm's base (the chain's hint). -/
def spZero : List Nat :=
  [28, 140, 229, 306, 367, 456, 533, 598, 647, 724, 789, 842, 879, 940, 989, 1026]

/-- The guest's number of the template's value `i`: two fewer for each step without an address
constant below it. -/
def spR (i : Nat) : Nat := i - 2 * spZero.countP (· < i)

/-- The guest's numbering, on values. -/
def spRen (v : V) : V := ⟨v.path, v.tag, spR v.idx⟩

end
end LeanVM.Guest.B1.Sig
