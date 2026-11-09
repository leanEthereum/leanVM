/-
  LeanVM.Guest.B1.Tables.Vt.FormsPad

  The guest's baked `COORD_PADDING` is the value of every table block's coordinate on its table's
  padding row, on the push and count sides, and the pull side's flushes take the push side's
  values there: kernel evaluation over `K`, `keccakF` of zeros replaced by its value.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.FormsTie5

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (canon refSideC FormC termsEval)

@[expose] public section

/-- `paddingRow` over `K`. -/
def paddingRowK (t : Table) : List K :=
  (List.range t.width).map fun i ↦
    if t.opcode = opKeccak ∧ keccakOut ≤ i ∧ i < keccakOut + 25 then
      K.ofBits (Keccak.lane Keccak.keccakFZero (i - keccakOut)).toNat
    else 0

theorem paddingRow_eq (t : Table) : paddingRow t = (paddingRowK t).map ofK := by
  unfold paddingRow paddingRowK
  rw [List.map_map]
  refine List.map_congr_left fun i _ ↦ ?_
  simp only [Function.comp_apply]
  split_ifs
  · rfl
  · exact ofK_zero.symm

/-- The padding tie of a side, as a boolean. -/
def vtPadTieCheck (spec : List (List FormC)) (pads : List (List ℕ)) (row : List K) : Bool :=
  decide (spec.length = pads.length) &&
    (List.zip spec pads).all fun p ↦ decide (p.1.length = p.2.length) &&
      (List.zip p.1 p.2).all fun q ↦
        decide (K.ofBits q.2 = termsEval (row.getD · 0) q.1.termsK)

def vtPads00 : List (List ℕ) :=
  [[1, 0, 0], [4, 0, 0, 1, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0],
    [2, 0, 0, 0, 0, 0]]

def vtPads01 : List (List ℕ) :=
  [[1, 0, 0], [4, 0, 0, 2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0],
    [2, 0, 0, 0, 0, 0]]

def vtPads02 : List (List ℕ) :=
  [[1, 0, 0], [4, 0, 0, 4, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0]]

def vtPads03 : List (List ℕ) :=
  [[1, 0, 0], [4, 0, 0, 8, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0],
    [2, 0, 0, 0, 0, 0]]

def vtPads04 : List (List ℕ) :=
  [[1, 0, 0], [4, 0, 0, 16, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0],
    [2, 0, 0, 0, 0, 0]]

def vtPads05 : List (List ℕ) :=
  [[1, 0, 0], [4, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0],
    [2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0],
    [2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0],
    [2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0], [2, 0, 0, 0, 0, 0],
    [2, 0, 0, 17376452488221285863, 9571781953733019530, 0],
    [2, 0, 0, 15391093639620504046, 13624874521033984333, 0],
    [2, 0, 0, 10027350355371872343, 18417369716475457492, 0],
    [2, 0, 0, 10448040663659726788, 10113917136857017974, 0],
    [2, 0, 0, 12479658147685402012, 3500241080921619556, 0],
    [2, 0, 0, 16959053435453822517, 12224711289652453635, 0],
    [2, 0, 0, 9342009439668884831, 4879704952849025062, 0],
    [2, 0, 0, 140226327413610143, 424854978622500449, 0], [2, 0, 0, 7259519967065370866, 0, 0],
    [2, 0, 0, 7004910057750291985, 13293599522548616907, 0],
    [2, 0, 0, 10105770293752443592, 10668034807192757780, 0],
    [2, 0, 0, 1747952066141424100, 1654286879329379778, 0],
    [2, 0, 0, 8500057116360352059, 16929593379567477321, 0]]

def vtPads20 : List (List ℕ) :=
  [[0], [0], [0], [0]]

def vtPads21 : List (List ℕ) :=
  [[0], [0], [0], [0]]

def vtPads22 : List (List ℕ) :=
  [[0], [0]]

def vtPads23 : List (List ℕ) :=
  [[0], [0], [0], [0]]

def vtPads24 : List (List ℕ) :=
  [[0], [0], [0], [0]]

def vtPads25 : List (List ℕ) :=
  [[0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0],
    [0], [0], [0], [0], [0], [0], [0], [0]]

theorem vtPadTie00 : vtPadTieCheck (refSideC 0 .push) vtPads00
    (paddingRowK (tables.getD 0 default)) = true := by decide +kernel

theorem vtPadTie10 : vtPadTieCheck (refSideC 0 .pull) vtPads00
    (paddingRowK (tables.getD 0 default)) = true := by decide +kernel

theorem vtPadTie01 : vtPadTieCheck (refSideC 1 .push) vtPads01
    (paddingRowK (tables.getD 1 default)) = true := by decide +kernel

theorem vtPadTie11 : vtPadTieCheck (refSideC 1 .pull) vtPads01
    (paddingRowK (tables.getD 1 default)) = true := by decide +kernel

theorem vtPadTie02 : vtPadTieCheck (refSideC 2 .push) vtPads02
    (paddingRowK (tables.getD 2 default)) = true := by decide +kernel

theorem vtPadTie12 : vtPadTieCheck (refSideC 2 .pull) vtPads02
    (paddingRowK (tables.getD 2 default)) = true := by decide +kernel

theorem vtPadTie03 : vtPadTieCheck (refSideC 3 .push) vtPads03
    (paddingRowK (tables.getD 3 default)) = true := by decide +kernel

theorem vtPadTie13 : vtPadTieCheck (refSideC 3 .pull) vtPads03
    (paddingRowK (tables.getD 3 default)) = true := by decide +kernel

theorem vtPadTie04 : vtPadTieCheck (refSideC 4 .push) vtPads04
    (paddingRowK (tables.getD 4 default)) = true := by decide +kernel

theorem vtPadTie14 : vtPadTieCheck (refSideC 4 .pull) vtPads04
    (paddingRowK (tables.getD 4 default)) = true := by decide +kernel

theorem vtPadTie05 : vtPadTieCheck (refSideC 5 .push) vtPads05
    (paddingRowK (tables.getD 5 default)) = true := by decide +kernel

theorem vtPadTie15 : vtPadTieCheck (refSideC 5 .pull) vtPads05
    (paddingRowK (tables.getD 5 default)) = true := by decide +kernel

/-- The tables' count columns (`refCountColumns`). -/
def vtCountCols : List (List ℕ) :=
  [[11, 12, 13, 14], [11, 12, 13, 14], [6, 7], [11, 12, 13, 14], [8, 9, 10, 11],
    (List.range 27).map (65 + ·)]

/-- The count columns are zero on their table's padding row. -/
theorem vtPadCount : (List.range 6).all (fun t ↦ (vtCountCols.getD t []).all fun l ↦
    decide ((paddingRowK (tables.getD t default)).getD l 0 = 0)) = true := by decide +kernel

end
end LeanVM.Guest.B1.Tables
