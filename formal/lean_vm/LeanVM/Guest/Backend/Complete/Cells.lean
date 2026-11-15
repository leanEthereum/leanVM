/-
  LeanVM.Guest.Backend.Complete.Cells

  The cells of its own frame a placed function's instructions name, and the placements whose range
  check temporaries have cells of their own (`TmpsApart`).
-/

module

public import LeanVM.Guest.Backend.Place
public import LeanVM.Guest.Backend.Sound.Ops
public import LeanVM.Guest.Memory.Fresh

/-!
# Cells

`opCells` lists the cells of this frame an instruction names (a `KECCAK` names its runs; the
destination of `mulNextFrame` is a cell of the next frame and is not listed); `locBase` is the
cell a place is read from.

**Temporaries apart.** The words of a range check's temporaries are chosen last, from the final
memory (`Memory/Retemp.lean`), so the completeness proof needs their cells to be theirs alone:
`TmpsApart tf pf` says the function's temporaries are fresh (`Fn.freshB`), each is placed in a
cell, no other value the body or the parameters name is placed at a temporary's cell, and each
temporary's cell is named by exactly one instruction of the placed body (its own `DEREF`).
`tmpsApartB` decides it.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- The cells of this frame an instruction names. -/
def opCells : LOp → List Cell
  | .mulNextFrame a b _ => [a, b]
  | .set o _ => [o]
  | .xor a b c => [a, b, c]
  | .mul a b c => [a, b, c]
  | .deref o1 _ o3 _ => [o1, o3]
  | .jump oc od of => [oc, od, of]
  | .slot x _ dst => [x, dst]
  | .keccak m0 m1 m2 m3 tail b8 cap out _ _ oc =>
      [m0, m1, m2, m3, b8] ++ (List.range 4).map (tail + ·) ++ (List.range 4).map (cap + ·) ++
        (List.range oc.cellCount).map (out + ·)

/-- The cell a place is read from. -/
def locBase : Loc → Cell
  | .cell n => n
  | .shifted n _ => n

/-- A value's cell: `.shifted` and unplaced values have none. -/
def cellP (locs : VMap Loc) (v : V) : Option Cell :=
  match locs[v]? with
  | some (.cell n) => some n
  | _ => none

/-- The cells of the temporaries, as a set. -/
def tmpCellSet (locs : VMap Loc) (ts : List V) : NMap Unit :=
  ts.foldl (fun m t => match cellP locs t with
    | some n => m.insert n ()
    | none => m) {}

/-- How many times the instructions name each cell of the set. -/
def cellCounts (set : NMap Unit) (ops : List LOp) : NMap ℕ :=
  ops.foldl (fun m o => (opCells o).foldl (fun m c =>
    if set.contains c then m.insert c ((m.get? c).getD 0 + 1) else m) m) {}

/-- `k n`, `n` evaluated first (the kernel then shares it). -/
def natSeq {β : Type} (n : ℕ) (k : ℕ → β) : β :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

theorem natSeq_eq {β : Type} (n : ℕ) (k : ℕ → β) : natSeq n k = k n := by cases n <;> rfl

/-- `k m`, the trie of `m` evaluated first. -/
def nmapSeq {α β : Type} (m : NMap α) (k : NMap α → β) : β := m.t.seq fun t => k ⟨t⟩

theorem nmapSeq_eq {α β : Type} (m : NMap α) (k : NMap α → β) : nmapSeq m k = k m := by
  cases m
  exact Trie.seq_eq _ _

/-- The temporaries are fresh (`Fn.freshB`), the mask of the uses computed once. -/
def freshOnce (tf : TracedFn) (ts : List V) : Bool :=
  idxNodup ts 0 && natSeq (idxMask (Stmt.usesList tf.core.body ++ tf.core.params)) fun m =>
    ts.all fun t => !m.testBit t.idx

/-- The places and counts checks of `tmpsApartB`, the set and the counts given. -/
def apartWith (tf : TracedFn) (pf : Placed) (ts : List V) (set : NMap Unit) (counts : NMap ℕ) :
    Bool :=
  ts.all (fun t => (cellP pf.locs t).isSome) &&
    (Stmt.usesList tf.core.body ++ tf.core.params).all (fun v =>
      match pf.locs[v]? with
      | some l => !set.contains (locBase l)
      | none => true) &&
    ts.all (fun t => match cellP pf.locs t with
      | some n => counts.get? n == some 1
      | none => false)

/-- **Temporaries apart, decided**, each intermediate evaluated once. -/
def tmpsApartB (tf : TracedFn) (pf : Placed) : Bool :=
  freshOnce tf (Stmt.tmpsList tf.core.body) &&
    nmapSeq (tmpCellSet pf.locs (Stmt.tmpsList tf.core.body)) fun set =>
      nmapSeq (cellCounts set (blockOps pf.fn.body 0)) fun counts =>
        apartWith tf pf (Stmt.tmpsList tf.core.body) set counts

theorem freshOnce_eq (tf : TracedFn) : freshOnce tf (Stmt.tmpsList tf.core.body) = tf.core.freshB := by
  rw [freshOnce, natSeq_eq]
  rfl

/-- **The temporaries of a placed function have cells of their own.** -/
def TmpsApart (tf : TracedFn) (pf : Placed) : Prop := tmpsApartB tf pf = true

/-- Placements with temporaries apart have fresh temporaries. -/
theorem TmpsApart.fresh {tf : TracedFn} {pf : Placed} (h : TmpsApart tf pf) : tf.core.Fresh := by
  unfold TmpsApart tmpsApartB at h
  rw [Bool.and_eq_true, freshOnce_eq] at h
  exact fn_fresh_of_freshB h.1

end
end LeanVM.Guest.Backend.Complete
