/-
  LeanVM.Guest.B1.Digest.MonoDefs

  The checks `child_claim_list_mono`'s proof evaluates (G:4209-4277; TRIAGE #89): a claim of the
  gap walk (`child_claims_mono`), the walk's records, the frame loops' bodies, the specializations
  `child_claim_list_mono_last__L{k}`, and the windows of the 64-block frame loop `__loop19`.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListDefs

/-!
# `child_claim_list_mono`: the checks

`child_claims_mono` (G:4209-4227) walks a list by hinted gaps: claim `j`'s gap `g^e` is a power
of `g` (`assert_gpow`, a touch through it), the coverage pointer moves on to `cov · g^e` and the
table pointer to `ent · g^(4e)`, the mark is written at `cov · g^j` and the four cells read at
`ent · g^(4j + c)`. Its eleven atoms sit at `p0 + 11 j` with the gap at `.n (g0 + 10 j)`
(`monoClaimOk`, checked on its window `monoWin`, `monoRecs`). A frame loop's record (`MONO_REC`
= 15 cells: the sponge state, the coverage pointer at 13, the table pointer at 14) is at
`chain · x^15` (`.n 10`); the frame writes the next record at offset 15 (`monoOk`). The last
`k < 17` claims (`mlOk`) end with the bound: the walk's end pointer `cov_end = t · region` with
`t` range-checked against `limit` (G:4276).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-! ## A claim of the gap walk -/

/-- Some touch cell is loaded through `p` (`assert_gpow`). -/
def isDerefOf (p : V) : Atom → Bool
  | .touch _ q => decide (q = p)
  | _ => false

/-- The coverage pointer before claim `j`: `.n cov0`, else the previous claim's. -/
def mCov (g0 cov0 j : ℕ) : ℕ := if j = 0 then cov0 else g0 + 10 * (j - 1) + 2

/-- The table pointer before claim `j`: `.n ent0`, else the previous claim's. -/
def mEnt (g0 ent0 j : ℕ) : ℕ := if j = 0 then ent0 else g0 + 10 * (j - 1) + 5

/-- **Claim `j` of the walk**, its gap at `.n gap` (`gap = g0 + 10 j`): the gap dereferenced,
`cov = pc · gap` (`.n (gap + 2)`), `ent = pe · (gap²)²` (`.n (gap + 5)`), the mark loaded at
`cov · g^j`, the cells `.n (gap + 6 + c)` at `ent · g^(4j + c)`. -/
def monoClaimOk (atoms : List Atom) (j gap pc pe : ℕ) (mark : V) : Bool :=
  atoms.any (isDerefOf (.n gap)) &&
  decide (mulOf atoms (.n (gap + 2)) = some (.n pc, .n gap)) &&
  decide (mulOf atoms (.n (gap + 3)) = some (.n gap, .n gap)) &&
  decide (mulOf atoms (.n (gap + 4)) = some (.n (gap + 3), .n (gap + 3))) &&
  decide (mulOf atoms (.n (gap + 5)) = some (.n pe, .n (gap + 4))) &&
  atoms.any (isLoadAt mark (.n (gap + 2)) j) &&
  (List.range 4).all fun c => atoms.any (isLoadAt (.n (gap + 6 + c)) (.n (gap + 5)) (4 * j + c))

/-- Claim `j`'s eleven atoms, the first claim's at `p0`. -/
def monoWin (atoms : List Atom) (p0 j : ℕ) : List Atom := (atoms.drop (p0 + 11 * j)).take 11

/-- Claims `lo ≤ j < lo + w` of `n` (those from `n` on pass). -/
def monoRecs (atoms : List Atom) (p0 g0 cov0 ent0 : ℕ) (mark : V) (n lo w : ℕ) : Bool :=
  (List.range' lo w).all fun j => decide (n ≤ j) ||
    monoClaimOk (monoWin atoms p0 j) j (g0 + 10 * j) (mCov g0 cov0 j) (mEnt g0 ent0 j) mark

/-- The message of `n` claims of the walk: their cells, in order. -/
def monoMsg (g0 n : ℕ) : List (Option V) :=
  (List.range (4 * n)).map fun i => some (.n (g0 + 10 * (i / 4) + 6 + i % 4))

/-- The value `.n o`, written at offset `off` of `rec`, is `.n last · c` with `c` the constant
`word w`. -/
def outOk (atoms : List Atom) (rec : V) (off o last w : ℕ) : Bool :=
  atoms.any (isLoadAt (.n o) rec off) &&
  match mulOf atoms (.n o) with
  | some (a, c) => decide (a = .n last) && atoms.any (isConstAt c w 0)
  | none => false

/-! ## The frame loops -/

/-- The chain of a frame loop of `m` claims: their cells, `final=0`, from the state `anySt st0`. -/
def monoSpec (m st0 : ℕ) (atoms : List Atom) : ChainSpec :=
  ⟨monoMsg 13 m, 0, false, some (anySt st0), keccakBlocks atoms⟩

/-- `monoOk` but the chain's blocks and the claims (`monoOk_of_parts`). -/
def monoHead (fn : Fn) (f : String) (m st0 cw ew : ℕ) : Bool :=
  loopShape fn f && decide (fn.params.length = 4) &&
    (monoSpec m st0 (loopAtoms fn)).shapeOk &&
    stLoadsOk (loopAtoms fn) (V.n 10) (anySt st0) 0 &&
    stLoadsOk (loopAtoms fn) (V.n 10)
      ((List.range 13).map ((monoSpec m st0 (loopAtoms fn)).outV
        ((monoSpec m st0 (loopAtoms fn)).nb - 1))) 15 &&
    monoIs (loopAtoms fn) (V.n 10) (V.n 2) (V.n 0) 15 &&
    (loopAtoms fn).any (isLoadAt (.n 11) (.n 10) 13) &&
    (loopAtoms fn).any (isLoadAt (.n 12) (.n 10) 14) &&
    outOk (loopAtoms fn) (.n 10) 28 (13 + 10 * m + 1) (mCov 13 11 m) cw &&
    outOk (loopAtoms fn) (.n 10) 29 (13 + 10 * m + 3) (mEnt 13 12 m) ew

/-- **A frame loop's body** `[x, N, chain, mark]`: the record at `chain · x^15` (`.n 10`), its
state, coverage pointer (`.n 11`) and table pointer (`.n 12`) loaded, `m` claims of the walk
from the hint at `p0`, the next record at offset 15 (state; pointers `cov · g^m` at 28,
`ent · g^(4m)` at 29, the constants `word cw`, `word ew`). -/
def monoOk (fn : Fn) (f : String) (m p0 st0 cw ew : ℕ) : Bool :=
  monoHead fn f m st0 cw ew && (monoSpec m st0 (loopAtoms fn)).check (loopAtoms fn) &&
    monoRecs (loopAtoms fn) p0 13 11 12 (.n 3) m 0 m

/-- **The claims from windows** of `w` claims covering the `n`. -/
theorem monoRecs_of_wins {atoms : List Atom} {p0 g0 cov0 ent0 : ℕ} {mark : V} {n w W : ℕ}
    (hn : n ≤ w * W) (h : ∀ i < W, monoRecs atoms p0 g0 cov0 ent0 mark n (w * i) w = true) :
    monoRecs atoms p0 g0 cov0 ent0 mark n 0 n = true := by
  simp only [monoRecs, List.all_eq_true, List.mem_range', Bool.or_eq_true, decide_eq_true_eq]
  rintro k ⟨i, hi, rfl⟩
  right
  have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hk : i / w < W := by
    rw [Nat.div_lt_iff_lt_mul hw]; rw [Nat.mul_comm] at hn; omega
  have := h (i / w) hk
  simp only [monoRecs, List.all_eq_true, List.mem_range', Bool.or_eq_true,
    decide_eq_true_eq] at this
  have hdm := Nat.div_add_mod i w
  rcases this (0 + 1 * i) ⟨i % w, Nat.mod_lt _ hw, by omega⟩ with h' | h'
  · omega
  · exact h'

/-- **`monoOk` from its parts**: the head, windows of `w` blocks covering the chain, windows of
`v` claims covering the `m`. -/
theorem monoOk_of_parts {fn : Fn} {f : String} {m p0 st0 cw ew w W v U : ℕ}
    (hh : monoHead fn f m st0 cw ew = true)
    (hnb : (monoSpec m st0 (loopAtoms fn)).nb ≤ w * W)
    (hb : ∀ i < W, (monoSpec m st0 (loopAtoms fn)).blocksOk (loopAtoms fn) (w * i) w = true)
    (hm : m ≤ v * U)
    (hr : ∀ i < U, monoRecs (loopAtoms fn) p0 13 11 12 (.n 3) m (v * i) v = true) :
    monoOk fn f m p0 st0 cw ew = true := by
  have h3 : (monoSpec m st0 (loopAtoms fn)).shapeOk = true := by
    simp only [monoHead, Bool.and_eq_true] at hh
    exact hh.1.1.1.1.1.1.1.2
  simp only [monoOk, hh, ChainSpec.check_of_blocks h3 hnb hb, monoRecs_of_wins hm hr,
    Bool.and_self]

/-! ## `child_claim_list_mono_last__L{k}` -/

/-- The names of `child_claim_list_mono_last`'s specializations, `k ≤ 16`. -/
def mlNames : List String :=
  ["child_claim_list_mono_last__L0", "child_claim_list_mono_last__L1",
   "child_claim_list_mono_last__L2", "child_claim_list_mono_last__L3",
   "child_claim_list_mono_last__L4", "child_claim_list_mono_last__L5",
   "child_claim_list_mono_last__L6", "child_claim_list_mono_last__L7",
   "child_claim_list_mono_last__L8", "child_claim_list_mono_last__L9",
   "child_claim_list_mono_last__L10", "child_claim_list_mono_last__L11",
   "child_claim_list_mono_last__L12", "child_claim_list_mono_last__L13",
   "child_claim_list_mono_last__L14", "child_claim_list_mono_last__L15",
   "child_claim_list_mono_last__L16"]

/-- The state cells `child_claim_list_mono_last__L{k}` loads. -/
def mlSt (k : ℕ) : List V := anySt (if k = 0 then 4 else 10 * k + 10)

/-- The walk's end pointer of `child_claim_list_mono_last__L{k}`: `rec[13]` (`k = 0`), else
`cov · g^k`. -/
def mlEnd (k : ℕ) : ℕ := if k = 0 then 27 else 10 * k + 7

/-- The chain of `child_claim_list_mono_last__L{k}`: the `k` claims' cells, padded. -/
def mlSpec (k : ℕ) (atoms : List Atom) : ChainSpec :=
  ⟨monoMsg 6 k, 64 * k, true, some (mlSt k), keccakBlocks atoms⟩

/-- The value `t` of the bound's `MUL`: `cov_end = t · region` (`.n 1`). -/
def endOf (atoms : List Atom) (ce : V) : Option V :=
  atoms.findSome? fun a => match a with
    | .mul d t r => if d = ce ∧ r = V.n 1 then some t else none
    | _ => none

/-- **`child_claim_list_mono_last__L{k}`'s body** `[rec, region, mark, limit]`: the state at
`rec`, the pointers at `rec · g^13` (`.n 4`) and `rec · g^14` (`.n 5`), `k` claims of the walk
from the hint at 2, the end pointer `cov · g^k` (or `rec[13]`), `t` with `cov_end = t · region`
range-checked against `limit`, the digest returned. -/
def mlOk (k : ℕ) (f : Fn) : Bool :=
  decide (f.params = [V.n 0, V.n 1, V.n 2, V.n 3]) &&
  match splitBody f.body with
  | some (atoms, [r0, r1]) =>
    (mlSpec k atoms).check atoms && retOk atoms (mlSpec k atoms) r0 r1 &&
      stLoadsOk atoms (V.n 0) (mlSt k) 0 &&
      (if k = 0 then atoms.any (isLoadAt (.n 27) (.n 0) 13) else
        atoms.any (isLoadAt (.n 4) (.n 0) 13) && atoms.any (isLoadAt (.n 5) (.n 0) 14) &&
        monoRecs atoms 2 6 4 5 (.n 2) k 0 k &&
        (match mulOf atoms (.n (mlEnd k)) with
         | some (a, c) => decide (a = .n (mCov 6 4 k)) && atoms.any (isConstAt c (2 ^ k) 0)
         | none => false)) &&
      (match endOf atoms (.n (mlEnd k)) with
       | some t => decide (rcOf atoms t = some (.n 3))
       | none => false)
  | _ => false

/-! ## The big frame loop `__loop19` (136 claims, 64 blocks), in sixteen windows -/

/-- `__loop19`'s atoms. -/
noncomputable def mono136Atoms : List Atom := loopAtoms (coreProgram.getD 384 default)

/-- `__loop19`'s chain. -/
noncomputable def mono136Spec : ChainSpec := monoSpec 136 1377 mono136Atoms

/-- Window `i` of `__loop19`: blocks `4i … 4i + 3`, claims `9i … 9i + 8`. -/
noncomputable def monoWinOk (i : ℕ) : Bool :=
  mono136Spec.blocksOk mono136Atoms (4 * i) 4 &&
    monoRecs mono136Atoms 9 13 11 12 (.n 3) 136 (9 * i) 9

end
end LeanVM.Guest.B1.Digest
