/-
  LeanVM.Guest.B1.VerifySub.CPlaced1

  `verify_sub` placed: the path of its body under a valuation, and its parts.
-/

module

public import LeanVM.Guest.B1.VerifySub.CPlaced0

/-!
# `verify_sub`'s path

`vs_walk`: under a valuation whose dispatch selector is `g^sel`, `sel < 28`, the body walks the
prefix, enters `open_stacked__L{sel}`, then walks the suffix and returns. `vs_parts`: its
`HeapBuf` hints, frames, calls and loads are the statements'.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory

@[expose] public section

/-- The dispatch's frame at `sel`. -/
def vsOpenEv (sel : ℕ) : Memory.Ev :=
  .call (openNames.getD sel "") [.n 1171, .n 1172, .n 1627, .n 419, .n 434, .n 726]
    [.n 1648, .n 1649, .n 1650, .n 1651]

/-- The path's events. -/
noncomputable def vsEvs (σ : Val) (sel : ℕ) : List Memory.Ev :=
  vsPre1.flatMap (Main.slEvs σ) ++ vsOpenEv sel :: vsPost2.flatMap (Main.slEvs σ)

theorem openNames_length : openNames.length = 28 := rfl

/-- **The body's path.** -/
theorem vs_walk (σ : Val) {sel : ℕ} (hsel : sel < 28) (hx : σ (.n 1643) = ofK (Parameters.gpow sel)) :
    walk σ (vsBody ++ [.ret []]) = .ret (vsEvs σ sel) [] := by
  rw [vsBody_split, List.append_assoc, List.cons_append, walk_pre_straight σ _ vsPre1 vsPre1_straight,
    walk, Main.walk_straight σ [] vsPost2 vsPost2_straight]
  have hp := pick_eq σ (.n 1643) [.n 1171, .n 1172, .n 1627, .n 419, .n 434, .n 726]
    [.n 1648, .n 1649, .n 1650, .n 1651] openNames 0 sel (by omega)
    (by rw [openNames_length]; omega) (by omega) hx
  simp only [vsDisp, walk1, hp, Out.seq, Out.pre, vsEvs, vsOpenEv, Nat.sub_zero,
    List.getD_eq_getElem _ _ (show sel < openNames.length by rw [openNames_length]; exact hsel)]
  simp

theorem vs_parts (σ : Val) (sel : ℕ) :
    allocDsts (vsEvs σ sel) = (vsPre1.filterMap Main.Stmt.allocSz).map Prod.fst ∧
      allocs σ (vsEvs σ sel) =
        (vsPre1.filterMap Main.Stmt.allocSz).map (fun x => x.2.elim id fun s => logG (σ s)) ∧
      addrs (vsEvs σ sel) = [] ∧
      calls (vsEvs σ sel) = (vsPre1.filterMap Main.Stmt.callS).map (Main.mkCall σ) ++
        ⟨openNames.getD sel "", [.n 1171, .n 1172, .n 1627, .n 419, .n 434, .n 726],
          [.n 1648, .n 1649, .n 1650, .n 1651], true⟩ ::
        (vsPost2.filterMap Main.Stmt.callS).map (Main.mkCall σ) ∧
      loadAddrs σ (vsEvs σ sel) = ((vsPre1.filterMap Stmt.loadS).map fun q => (σ q.1).limb 0 * Parameters.gpow q.2) ++
        (vsPost2.filterMap Stmt.loadS).map fun q => (σ q.1).limb 0 * Parameters.gpow q.2 := by
  obtain ⟨a1, a2, a3, a4⟩ := Main.straight_parts σ vsPre1 vsPre1_straight
  obtain ⟨b1, b2, b3, b4⟩ := Main.straight_parts σ vsPost2 vsPost2_straight
  have l1 := loadAddrs_straight σ vsPre1 vsPre1_straight
  have l2 := loadAddrs_straight σ vsPost2 vsPost2_straight
  rw [vsPost2_allocs] at b1 b2
  rw [vsPre1_addrs] at a3
  rw [vsPost2_addrs] at b3
  simp only [allocDsts, allocs, addrs, calls, loadAddrs, vsEvs, List.filterMap_append,
    List.filterMap_cons, vsOpenEv, Ev.allocDst?, Ev.alloc?, Ev.addr?, Ev.call?, Ev.loadAddr?] at *
  simp only [a1, a2, a3, a4, b1, b2, b3, b4, l1, l2, List.map_nil, List.append_nil,
    and_self]

end
end LeanVM.Guest.B1.VerifySub
