/-
  LeanVM.Guest.B1.Digest.Lists

  Straight-line `KECCAK` chains over loaded cells, checked by evaluation.
-/

module

public import LeanVM.Guest.B1.Digest.Chain

/-!
# Chains over loaded cells

A straight-line body (`splitBody`: atoms, then a `ret`) that loads its message cells through a
pointer (`loadsOk`), hashes them by a padded chain (`ChainSpec.check`) and returns copies of the
digest's cells (`retOk`) returns the digest of the cells read (`straight_digest`). `find_of_idx`:
a function found by its core index.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Straight-line bodies -/

/-- A body of atoms then a `ret`: the atoms and the returned values. -/
def splitBody : List Stmt → Option (List Atom × List V)
  | [.ret vs] => some ([], vs)
  | .atom a :: rest => (splitBody rest).map fun p => (a :: p.1, p.2)
  | _ => none

theorem splitBody_eq : ∀ {body : List Stmt} {as : List Atom} {vs : List V},
    splitBody body = some (as, vs) → body = as.map Stmt.atom ++ [Stmt.ret vs]
  | [], _, _, h => by simp [splitBody] at h
  | [.ret vs'], as, vs, h => by
    simp only [splitBody, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .atom a :: rest, as, vs, h => by
    simp only [splitBody, Option.map_eq_some_iff, Prod.exists] at h
    obtain ⟨as', vs', h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    rw [splitBody_eq h1]
    rfl
  | .ret _ :: _ :: _, _, _, h | .ite .. :: _, _, _, h | .match_ .. :: _, _, _, h
  | .call .. :: _, _, _, h | .callIf .. :: _, _, _, h | .dispatch .. :: _, _, _, h => by
    simp [splitBody] at h

/-- The blocks of the `KECCAK` atoms of a list, in order. -/
def keccakBlocks (atoms : List Atom) : List (List V × List V) :=
  atoms.filterMap fun a => match a with
    | .keccak i o _ _ => some (i, o)
    | _ => none

/-! ## Loads -/

/-- `x` is loaded through `p` at offset `o`. -/
def isLoadAt (x p : V) (o : ℕ) : Atom → Bool
  | .load d q off => decide (d = x) && decide (q = p) && off == o
  | _ => false

theorem load_sound {rd : Reader} {σ : Val} {atoms : List Atom} {x p : V} {o : ℕ}
    (h : atoms.any (isLoadAt x p o) = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    LoadHolds rd (σ p) o (σ x) := by
  obtain ⟨a, hp, ha⟩ := any_holds h hat
  cases a <;> simp only [isLoadAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hp
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp
  exact ha

/-- Every message cell `i` is a value loaded through `p` at offset `i`. -/
def loadsOk (atoms : List Atom) (p : V) (msg : List (Option V)) : Bool :=
  (List.range msg.length).all fun i => match msg.getD i none with
    | some v => atoms.any (isLoadAt v p i)
    | none => false

theorem loads_sound {rd : Reader} {σ : Val} {atoms : List Atom} {p : V} {msg : List (Option V)}
    (h : loadsOk atoms p msg = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    ReadsAt rd (σ p) (msg.map (srcVal σ)) := by
  intro i hi
  rw [List.length_map] at hi
  simp only [loadsOk, List.all_eq_true, List.mem_range] at h
  have hi' := h i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at hi'
  rw [List.getElem_map]
  revert hi'
  cases msg[i] with
  | none => simp
  | some v => intro hv; exact load_sound hv hat

/-! ## Straight-line digests -/

/-- The returned values are copies of the chain's digest cells. -/
def retOk (atoms : List Atom) (s : ChainSpec) (r0 r1 : V) : Bool :=
  atoms.any (isCopyAt r0 (s.outV (s.nb - 1) 0)) && atoms.any (isCopyAt r1 (s.outV (s.nb - 1) 1))

/-- **A straight-line padded chain from the zero state returns the digest of its cells.** -/
theorem straight_digest {rd : Reader} {σ : Val} {atoms : List Atom} {s : ChainSpec} {r0 r1 : V}
    (hc : s.check atoms = true) (hfin : s.final = true) (hinit : s.init = none)
    (hr : retOk atoms s r0 r1 = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    [σ r0, σ r1] = digestCells (keccak256 (cellsBytes ((s.vals σ).take (s.len / 16)))) ∧
      AllCanonical ((s.vals σ).take (s.len / 16)) := by
  have h0 : ∀ c : Fin 13, s.initCell σ c =
      cellsOfState (absorbChunks 0 zeroState []) false c := fun c => by
    rw [ChainSpec.initCell, hinit]
    exact (cellsOfState_zero false c).symm
  obtain ⟨hd, hcan⟩ := chain_final hc hfin hat (pre := []) (n := 0) rfl h0
  rw [List.nil_append] at hd
  simp only [retOk, Bool.and_eq_true] at hr
  refine ⟨?_, hcan⟩
  rw [copy_sound hr.1 hat, copy_sound hr.2 hat, digestCells, ← hd]

theorem find_of_idx {name : String} {j : ℕ} (h : coreProgram.indexOf? name = some j)
    (hj : j < coreProgram.length) : coreProgram.find? name = some (coreProgram.getD j default) := by
  refine Program.find?_of_indexOf? h ?_
  rw [List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

end
end LeanVM.Guest.B1.Digest
