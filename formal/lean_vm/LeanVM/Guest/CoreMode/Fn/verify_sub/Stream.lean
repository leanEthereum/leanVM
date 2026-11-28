/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.Stream

  `verify_sub`'s proof stream family: its reads and its callees' runs placed in the stream `hint_stream` writes, made
  up from its residue runs. Sound given `EndExec.VsStreamQ` (`StreamA.lean`).
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings

namespace LeanVM.Guest.CoreMode.Own.verify_sub

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **The proof stream's run** `⟨stream, 1, g^0, stream_chunks^STREAM_CHUNK⟩` (values `55`, `42`): the cells
`stream·g^(256j + d)`, `j < e(stream_chunks)`, `d < 256`, `hint_stream`'s `256` residue runs, merged
(`callcres.merged_runs`). -/
def streamQ : CRun := ⟨⟨[(55, 1)], 0⟩, 1, .num 0, .mono ⟨[(42, 256)], 0⟩⟩

/-- Arm `j` of the selector `x` among the branch conditions, if any. -/
def armOf (g : List CCond) (x : ℕ) : Option ℕ :=
  g.findSome? fun
    | .arm y j => if y = x then some j else none
    | _ => none

/-- `open_stacked__L{m}`'s reads past `cursor@4` (value `2920`) under its arm `m` of `size_sel` (value `489`): the
last offset, by `m < 15`. -/
def osRoom : List ℕ := [103, 109, 119, 137, 132, 138, 148, 166, 161, 167, 177, 195, 190, 196, 206]

/-- `link_row_side__L{6 + a}`'s arm `a` of its selector (value `1070`): its stride `S` (the cursor's advance a row,
`([115]·[412])^S`) and the last offset of the reads past it. -/
def lrsRoom : List (ℕ × ℕ) := [(8, 57), (10, 63), (11, 75), (12, 81)]

/-- **A read it places in the stream** under the branch conditions `g`: the link's sent values and pointer slices
`cursor@3·g^j` (`1076`), `j < 144`; `open_stacked`'s nonce `cursor@4` (`2920`) and, under its arm `m`, its words
`cursor@4·g^j`, `1 ≤ j ≤ osRoom[m]`; `link_rounds`' returned cursor `stream·[108]^2·[460]^2·g^15`; under
`link_row_side`'s arm `a`, the words past its rows, `stream·[108]^2·[460]^2·([115]·[412])^S·g^j`,
`16 ≤ j ≤ K`, `(S, K) = lrsRoom[a]`. -/
def streamCell (g : List CCond) (c : CCell) : Bool :=
  (decide (c.bases = [(1076, 1)]) && Nat.blt c.off 144) ||
  (decide (c.bases = [(2920, 1)]) && (Nat.beq c.off 0 || match armOf g 489 with
    | some m => Nat.ble 1 c.off && Nat.ble c.off (osRoom.getD m 0) && Nat.blt m 15
    | none => false)) ||
  decide (c = ⟨[(55, 1), (108, 2), (460, 2)], 15⟩) ||
  (match armOf g 1070 with
    | some a => Nat.blt a 4 && decide (c.bases = [(55, 1), (108, 2), (115, (lrsRoom.getD a (0, 0)).1),
        (412, (lrsRoom.getD a (0, 0)).1), (460, 2)]) && Nat.ble 16 c.off && Nat.ble c.off (lrsRoom.getD a (0, 0)).2
    | none => false)

/-- **A callee's run it places in the stream** under the branch conditions `g`: `link_rounds`' words
`stream·g^(o + 2i)`, `o ∈ {13, 14}`, `i < e([108]·[460]·g)`; `verify_keccak`'s, its `24` residue runs
`cursor@3·g^(o + 24i)`, `144 ≤ o < 168`, `i < e(kb[7]) + 44` (value `120`); under `link_row_side`'s arm `a`, its
rows' residues `stream·[108]^2·[460]^2·g^(o + S·i)`, `16 ≤ o < 16 + S`, `i < e([115]·[412])`, `S = lrsRoom[a].1`. -/
def streamRun (g : List CCond) (q : CRun) : Bool :=
  (decide (q.base.bases = [(55, 1)]) && (Nat.beq q.base.off 13 || Nat.beq q.base.off 14) && Nat.beq q.stride 2 &&
    decide (q.lo = .num 0) && decide (q.hi = .mono ⟨[(108, 1), (460, 1)], 1⟩)) ||
  (decide (q.base.bases = [(1076, 1)]) && Nat.ble 144 q.base.off && Nat.blt q.base.off 168 && Nat.beq q.stride 24 &&
    decide (q.lo = .num 0) && decide (q.hi = .mono ⟨[(120, 1)], 44⟩)) ||
  (match armOf g 1070 with
    | some a => Nat.blt a 4 && decide (q.base.bases = [(55, 1), (108, 2), (460, 2)]) &&
        Nat.beq q.stride (lrsRoom.getD a (0, 0)).1 && Nat.ble 16 q.base.off &&
        Nat.blt q.base.off (16 + q.stride) && decide (q.lo = .num 0) && decide (q.hi = .mono ⟨[(115, 1), (412, 1)], 0⟩)
    | none => false)

/-- **The stream family** under the branch conditions `g`: also `0 < e(stream_chunks)`, the stream not empty (a read
at its first cell lies before the end, so the end is past it). -/
def streamFamU (g : List CCond) : CRes → Bool
  | .sub c q => decide (q = streamQ) && streamCell g c
  | .subR q r => decide (r = streamQ) && streamRun g q
  | .under g' r => streamFamU (g ++ g') r
  | .lt a b => decide (a = .num 0) && decide (b = .val 42)
  | _ => false

/-- **The stream family**: a read or a callee's run the solver places in the stream (`streamCell`, `streamRun`),
under its site's branch conditions. -/
def streamFam (r : CRes) : Bool := streamFamU [] r

end

end LeanVM.Guest.CoreMode.Own.verify_sub
