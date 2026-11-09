/-
  LeanVM.Guest.B1.Da.OffCChk

  `da_column_offsets`, evaluated (by kernel evaluation): its values defined in order, its stores
  the zeros and the steps, its loads of three shapes, its statements atoms and its seven loops'
  calls, its `HeapBuf`s the offsets and seven steps' runs.
-/

module

public import LeanVM.Guest.B1.Da.OffsetsChk
public import LeanVM.Guest.B1.Fwd.Canon
public import LeanVM.Guest.B1.Tables.FlatAt

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- A statement's atom. -/
def atomOfS : Stmt → Option Atom
  | .atom a => some a
  | _ => none

/-- `da_column_offsets`' atoms. -/
def offAtoms : List Atom := offP.filterMap atomOfS

/-- Its stores: the eight zeros, then each bit's steps. -/
def offStores : List Atom :=
  (List.range 8).map (fun j => .load (.n (2 + j)) (.n 1) j) ++
    (List.range 7).flatMap fun b => (List.range 8).map fun j =>
      .load (.n (offB b + 1 + 3 * j + 2)) (.n (offB b)) j

/-- A load of one of its three shapes: a zero into `offsets[j]`, `zs[j]` for a bit's step, a
step into `steps[j]`. -/
def isOffLoad (d p : V) (off : ℕ) : Bool :=
  decide (off < 8) && ((decide (p = .n 1) && decide (d = .n (2 + off))) ||
    (decide (p = .n 0) && (List.range 7).any fun b => decide (d = .n (offB b + 1 + 3 * off))) ||
    (List.range 7).any fun b => decide (p = .n (offB b)) && decide (d = .n (offB b + 1 + 3 * off + 2)))

/-- Bit `b`'s loop call. -/
def offCallS (b : ℕ) : Stmt :=
  .callIf (.n (offB b + 27)) (offLoopName b) [.n (offB b + 28), .n (offB b + 29), .n 1, .n (offB b)]

/-- A statement of `da_column_offsets`: an atom or a loop's call. -/
def isOffStmt : Stmt → Bool
  | .atom _ => true
  | s => (List.range 7).any fun b => stmtsEqb [s] [offCallS b]

/-- Its `HeapBuf`s. -/
def offAllocs : List (V × (ℕ ⊕ V)) := (.n 1, .inl 1024) :: (List.range 7).map fun b => (.n (offB b), .inl 8)

/-- Its calls. -/
def offCalls : List (Option V × String × List V × List V) := (List.range 7).map fun b =>
  (some (.n (offB b + 27)), offLoopName b, [.n (offB b + 28), .n (offB b + 29), .n 1, .n (offB b)], [])

/-- **`da_column_offsets`, evaluated.** -/
def offCOk : Bool :=
  (chk 1 offP).isSome && atomsEqb (storesOf 1 offP) offStores && canonChk [] offAtoms &&
  offAtoms.all (fun a => !needsSide a || (atomLoad? a).isSome) &&
  offAtoms.all (fun a => match a with | .load d p off => isOffLoad d p off | _ => true) &&
  offP.all isOffStmt && offP.all Core.Stmt.flat && decide (offP.filterMap Stmt.addrS = []) &&
  decide (offP.filterMap Stmt.allocSz = offAllocs) && decide (offP.filterMap Main.Stmt.callS = offCalls) &&
  offP.all B1.noLoadIte

set_option maxRecDepth 100000 in
theorem off_cok : offCOk = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
