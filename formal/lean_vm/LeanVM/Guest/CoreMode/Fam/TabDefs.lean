/-
  LeanVM.Guest.CoreMode.Fam.TabDefs

  The generator's hints to the facts carried to callees: sub-spines picked by a bitset, and name tables pinned to their
  lists. Their facts are `Fam/ResWalk.lean`.
-/

module

public import LeanVM.Guest.Memory.Static
public import LeanVM.Guest.NameIx
public import LeanVM.Guest.ExecCore

/-!
# Sub-spines and name tables

The checks of the facts carried to callees search a function's whole spine for each value they pin, and compare each
call site's callee with every entry of a list of names. At the generator's hints they take instead:

* a **sub-spine**: the events at the set bits of a number (`pickB`), the events a search uses;
* **name tables**: a list of entries keyed by name as a search tree by the name's code (`encS`, `NTab`), each entry's
  payload under its name's code, written by the generator and checked against its list once (`tabOk`), or for a short
  list built by the kernel from it (`NTab.ofNamed`).
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Exec (natSeq)

@[expose] public section

/-- **The elements of `l` at the set bits of `b`**, bit `0` the first: by the recursor, for the kernel. -/
def pickB {α : Type} (b : ℕ) (l : List α) : List α :=
  List.rec (motive := fun _ ↦ ℕ → List α) (fun _ ↦ [])
    (fun x _ ih b ↦ bif Nat.beq (Nat.mod b 2) 1 then x :: ih (Nat.div b 2) else ih (Nat.div b 2)) l b

/-- **A name table**: under a name's code (`encS`), the payloads of the entries of that name. -/
abbrev NTab (α : Type) := NTree (List α)

/-- The payloads under a code, the code evaluated first. -/
def NTab.at {α : Type} (t : NTab α) (k : ℕ) : List α := natSeq k fun k ↦ (t.find k).getD []

/-- `a` added under key `k`. -/
def NTab.ins {α : Type} (k : ℕ) (a : α) : NTab α → NTab α
  | .leaf => .node k [a] .leaf .leaf
  | .node k' v l r => if Nat.beq k k' then .node k' (a :: v) l r
      else if Nat.blt k k' then .node k' v (NTab.ins k a l) r else .node k' v l (NTab.ins k a r)

/-- **The table of a list of keyed payloads**, built by the kernel. -/
def NTab.ofList {α : Type} (l : List (ℕ × α)) : NTab α := l.foldr (fun p t ↦ NTab.ins p.1 p.2 t) .leaf

/-- **The table of a list of named entries**: each entry's payload `φ` under its name's code. -/
def NTab.ofNamed {α β : Type} (φ : β → α) (L : List (String × β)) : NTab α :=
  NTab.ofList (L.map fun c ↦ (encS c.1, φ c.2))

/-- A function's hint by its index, `0` when it has none, the index evaluated first. -/
def witAt (t : NTree ℕ) (j : ℕ) : ℕ := natSeq j fun j ↦ (t.find j).getD 0

/-- Every entry of a search tree passes `p` of its key and value. -/
def NTree.allK {α : Type} (p : ℕ → α → Bool) : NTree α → Bool
  | .leaf => true
  | .node k v l r => p k v && NTree.allK p l && NTree.allK p r

/-- **A table holds a list**: each entry's payload under its name's code. -/
def tabIn {α β : Type} [BEq α] (L : List (String × β)) (t : NTab α) (φ : β → α) : Bool :=
  L.all fun c ↦ (t.at (encS c.1)).contains (φ c.2)

/-- **A table of a list**: it holds the list (`tabIn`), and each payload under a code is an entry's of a name of that
code. -/
def tabOk {α β : Type} [BEq α] (L : List (String × β)) (t : NTab α) (φ : β → α) : Bool :=
  tabIn L t φ &&
    NTree.allK (fun k is ↦ is.all fun i ↦ L.any fun c ↦ Nat.beq (encS c.1) k && φ c.2 == i) t

end

end LeanVM.Guest.Res
