/-
  LeanVM.Guest.Backend.Guest.Cpl.Placed

  The guest's world at no memory, and each of its functions placed as the world places it, the
  placement the per-function checks evaluate.
-/

module

public import LeanVM.Guest.Backend.Guest.Cpl.At
public import LeanVM.Guest.Backend.Guest.Compiled
public import LeanVM.Guest.Backend.Guest.B2.Facts
public import LeanVM.Guest.Backend.Complete.Spec

/-!
# The guest's placed functions

`W0` is the guest's world (`guestWorld`) on the memory of one word: the completeness instance's
frame words are chosen on it, once for every memory (`Complete.FrameConsistentStmt` chooses them
before the memory). `placedG i` is entry `i` placed (`placedAt`), and `guest_placed`: it is what
the world places (`World.PlacedAs`), from the jump tables the entries before it leave, as the
compiled pieces show (`guest_pieces`).
-/

namespace LeanVM.Guest.Backend.Cpl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core GuestPiece

@[expose] public section

/-- **The guest's world on the memory of one word.** -/
noncomputable def W0 : World 0 := guestWorld guestFns guestSlots (fun _ => 0) (fun _ _ => True)

theorem W0_compiled : W0.Compiled := guestWorld_compiled guest_compiles

theorem W0_p : W0.p = guestTraced := guestWorld_p

/-- A placed function of no instruction. -/
def noPlaced : Placed := ⟨⟨"", [], 0⟩, {}⟩

/-- **Entry `i` placed.** -/
noncomputable def placedG (i : ℕ) : Placed := (placedAt i).getD noPlaced

/-- The placement of a program compiled from its pieces lists, at `j`, function `j` placed from
the jump tables the functions before it leave (`placed_locs_of_pieces`). -/
theorem placed_of_pieces {p : List TracedFn} {os : List FnOut} {cfs : List CompiledFunction}
    {loops : Loops} {sigs : SMap (ℕ × ℕ)} {l : Layout}
    (hloops : loopTable p = loops) (hsigs : sigTable p = sigs) (hchecks : progChecks p loops = true)
    (hos : os.length = p.length) (hcfs : cfs.length = p.length)
    (hpieces : ∀ j < p.length, pieceAt loops sigs l p os cfs j = true) {j : ℕ} (hj : j < p.length) :
    ∃ placed tables pf t', placeProgram p = .ok (placed, tables) ∧ placed[j]? = some pf ∧
      placeFn loops sigs (tablesAt os j) (p.getD j default) = .ok (pf, t') := by
  set n := (tablesEnd os).len
  have hfrs : (framesOf n os).length = p.length := by
    cases os <;> simp [framesOf] at hos ⊢ <;> omega
  have hchain : Chain loops sigs l {} n p os (framesOf n os) cfs :=
    chain_of_forall p os _ cfs {} n hos hfrs hcfs fun j hj => hpieces j hj
  obtain ⟨placed, hplace, -⟩ := placeFns_of_chain _ _ _ _ _ _ hchain
  simp only [progChecks, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hchecks
  obtain ⟨⟨⟨hmain, hjtn⟩, hdist⟩, hloopm⟩ := hchecks
  have hpp : placeProgram p = .ok (placed, tablesEnd os) := by
    unfold placeProgram
    simp only [hmain, hjtn, hdist, hloopm, bne_self_eq_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, hloops, hsigs]
    exact hplace
  have hall : ∀ j < p.length, ∃ pf, placeFn loops sigs ((os.take j).foldl Tables.after {})
      (p.getD j default) = .ok (pf, (os.take (j + 1)).foldl Tables.after {}) := by
    intro i hi
    obtain ⟨pf, hpf, -⟩ := pieceOk_spec (hpieces i hi)
    refine ⟨pf, ?_⟩
    rw [tablesAt] at hpf
    rw [hpf]
    have hi' : i < os.length := hos ▸ hi
    rw [List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some, List.foldl_append]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  obtain ⟨pf, hget, hpf⟩ := placeFns_getElem p os {} placed _ hos hplace hall j hj
  exact ⟨placed, _, pf, _, hpp, hget, hpf⟩

/-- **Function `j` of a world compiled from its pieces lists** is placed as the world places it,
from the jump tables the functions before it leave. -/
theorem placedAs_of_pieces {κ : ℕ} (W : World κ) {p : List TracedFn} {os : List FnOut}
    {cfs : List CompiledFunction} {loops : Loops} {sigs : SMap (ℕ × ℕ)} {l : Layout} (hp : W.p = p)
    (hloops : loopTable p = loops) (hsigs : sigTable p = sigs) (hchecks : progChecks p loops = true)
    (hos : os.length = p.length) (hcfs : cfs.length = p.length)
    (hpieces : ∀ j < p.length, pieceAt loops sigs l p os cfs j = true) {j : ℕ} (hj : j < p.length) :
    ∃ pf t', Complete.World.PlacedAs W (p.getD j default) pf ∧
      placeFn loops sigs (tablesAt os j) (p.getD j default) = .ok (pf, t') := by
  obtain ⟨placed, tables, pf, t', hpp, hget, hpf⟩ :=
    placed_of_pieces hloops hsigs hchecks hos hcfs hpieces hj
  refine ⟨pf, t', ⟨?_, ?_⟩, hpf⟩
  · unfold World.placed
    rw [hp, hpp]
    exact List.mem_of_getElem? hget
  · obtain ⟨st', -, rfl, -⟩ := Backend.placeFn_ok hpf
    rfl

/-- **Entry `i` as the world places it**: placed from the jump tables the entries before it leave,
the world's placement of its function. -/
theorem guest_placed {i : ℕ} (hi : i < guestTraced.length) :
    placedAt i = some (placedG i) ∧ Complete.World.PlacedAs W0 (guestTraced.getD i default) (placedG i) ∧
      ∃ t', placeFn loopsG sigsG (tablesAt outsG i) (guestTraced.getD i default) = .ok (placedG i, t') := by
  obtain ⟨pf, t', hpa, hpf⟩ := placedAs_of_pieces W0 W0_p loopsG_eq sigsG_eq checks_ok
    outs_length cfs_length guest_pieces hi
  have hat : placedAt i = some pf := placedAt_of hpf
  have hG : placedG i = pf := by rw [placedG, hat]; rfl
  rw [hG]
  exact ⟨hat, hpa, t', hpf⟩

theorem tf_mem {i : ℕ} (hi : i < guestTraced.length) : guestTraced.getD i default ∈ W0.p := by
  rw [W0_p, List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

/-- **Entry `i`'s places** are `placedLocs i`. -/
theorem placedG_locs {i : ℕ} (hi : i < guestTraced.length) : (placedG i).locs = placedLocs i := by
  obtain ⟨-, -, t', hpf⟩ := guest_placed hi
  unfold placedLocs placedLocsAt
  rw [hpf]

/-- The loops of the guest's world are `loopsG`. -/
theorem W0_loops : loopTable W0.p = loopsG := loopsG_eq

end
end LeanVM.Guest.Backend.Cpl
