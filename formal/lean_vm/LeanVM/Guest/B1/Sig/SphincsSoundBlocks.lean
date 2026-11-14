/-
  LeanVM.Guest.B1.Sig.SphincsSoundBlocks

  The body of `verify_sig_lean_sphincs` (`lean_ethereum.py:4142-4243`) as four
  blocks of atoms around its three calls of `sp_wots`.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsT
public import LeanVM.Guest.B1.Sig.KeccakMsg

/-!
# `verify_sig_lean_sphincs` around its calls

A layer (`sLayerAt l a0 a1 signed`, `sp_layer`) is its counter and its encoding (`sLayerPre`), the
call of `sp_wots` (`sLayerCall`: `sp_wots(pp, a0, a1, enc)`, its leaf `sLayerLeaf`), then its path
(`sLayerPath`): `sLayerAt_eq`. So the body (`sBody_split`) is

* `sBlockA`: the digest block, FORS, the bottom layer's counter and encoding;
* `sBlockB`: the bottom path, the middle layer's addresses, counter and encoding;
* `sBlockC`: the middle path, the top layer's addresses, counter and encoding;
* `sBlockD`: the top path and `root[0] == pk_root`,

around the three calls, then `return`; each block is atoms only (`sBlockA_atoms`, …).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

/-! ## A layer around its call -/

/-- Layer `l`'s counter: its four bytes read (`sp_from_bytes`). -/
def sLayerCtr (l : Nat) : List Stmt × Nat × V := sFromMarks (sLayerBase l) 4 (sLayerBase l + 4)

/-- Layer `l`'s encoding: `KECCAK` of `[pp, a0, enc_at, signed, counter]`, 68 bytes. -/
def sLayerK (l : Nat) (a0 signed : V) : List Stmt × Nat × Nat :=
  kMsg sPad [.cell sPP, .cell a0, .cell (.n ((sLayerCtr l).2.1 + 1)), .cell signed,
    .cell (sLayerCtr l).2.2] 68 false none ((sLayerCtr l).2.1 + 2)

/-- Layer `l` before its call: the counter hinted and read, `enc_at = a1 + WOTS_ENC`, the
encoding. -/
def sLayerPre (l : Nat) (a0 a1 signed : V) : List Stmt :=
  [hintW "sp_counter" (runV (sLayerBase l) 4)] ++ (sLayerCtr l).1 ++
    [cst (sLayerCtr l).2.1 (lit (7 * 2 ^ 24)),
      addS (.n ((sLayerCtr l).2.1 + 1)) a1 (.n (sLayerCtr l).2.1)] ++
    (sLayerK l a0 signed).1

/-- Layer `l`'s call of `sp_wots`. -/
def sLayerCall (l : Nat) (a0 a1 signed : V) : Stmt :=
  .call "sp_wots" [sPP, a0, a1, .n (sLayerK l a0 signed).2.2] [.n (sLayerK l a0 signed).2.1]

/-- Layer `l`'s path, from the leaf `sp_wots` returns. -/
def sLayerPath (l : Nat) (a0 signed : V) : List Stmt × Nat × V :=
  sPath sPad sPP a0 sLeafBit sLVal (sOffOf l) (sHeightOf l) 0 (.n (sLayerK l a0 signed).2.1)
    ((sLayerK l a0 signed).2.1 + 1)

/-- **A layer around its call.** -/
theorem sLayerAt_eq (l : Nat) (a0 a1 signed : V) :
    sLayerAt l a0 a1 signed = (sLayerPre l a0 a1 signed ++
      sLayerCall l a0 a1 signed :: (sLayerPath l a0 signed).1, (sLayerPath l a0 signed).2.1,
      (sLayerPath l a0 signed).2.2) := by
  simp only [sLayerAt, sHtLayer, sLayerPre, sLayerCall, sLayerPath, sLayerK, sLayerCtr,
    List.append_assoc, List.cons_append, List.nil_append]

/-- The call's positions: the encoding digest at `sEncOf l`, the leaf at `sLeafOf l`, the counter
at `sCtrOf l`. -/
theorem sLayerK_out (l : Nat) (a0 signed : V) :
    (sLayerK l a0 signed).2.2 = sLayerBase l + 46 ∧
      (sLayerK l a0 signed).2.1 = sLayerBase l + 47 := by
  constructor <;> rfl

theorem sLayerCtr_out (l : Nat) :
    (sLayerCtr l).2.2 = sCtrOf l ∧ (sLayerCtr l).2.1 = sLayerBase l + 37 := by
  constructor <;> rfl

/-! ## The body around its calls -/

/-- The digest block, FORS, the bottom layer's counter and encoding. -/
def sBlockA : List Stmt := sDigestBlock ++ sForsAddrs ++ sForsB.1 ++ sLayerPre 0 sA0B sKeyB sForsPk

/-- The bottom path, the middle layer's addresses, counter and encoding. -/
def sBlockB : List Stmt :=
  (sLayerPath 0 sA0B sForsPk).1 ++ sMidAddrs ++ sLayerPre 1 (sA0Of 1) (sA1Of 1) sLayerB.2.2

/-- The middle path, the top layer's addresses, counter and encoding. -/
def sBlockC : List Stmt :=
  (sLayerPath 1 (sA0Of 1) sLayerB.2.2).1 ++ sTopAddrs ++ sLayerPre 2 (sA0Of 2) (sA1Of 2) sLayerM.2.2

/-- The top path and the root's check. -/
def sBlockD : List Stmt :=
  (sLayerPath 2 (sA0Of 2) sLayerM.2.2).1 ++ [.atom (.assertEq sLayerT.2.2 sRoot)]

theorem sLayerB_root : sLayerB.2.2 = (sLayerPath 0 sA0B sForsPk).2.2 := by
  rw [sLayerB, sLayerAt_eq]

theorem sLayerM_root : sLayerM.2.2 = (sLayerPath 1 (sA0Of 1) sLayerB.2.2).2.2 := by
  rw [sLayerM, sLayerAt_eq]

theorem sLayerT_root : sLayerT.2.2 = (sLayerPath 2 (sA0Of 2) sLayerM.2.2).2.2 := by
  rw [sLayerT, sLayerAt_eq]

/-- **The body around its three calls.** -/
theorem sBody_split : sBody = sBlockA ++ sLayerCall 0 sA0B sKeyB sForsPk :: (sBlockB ++
    sLayerCall 1 (sA0Of 1) (sA1Of 1) sLayerB.2.2 :: (sBlockC ++
      sLayerCall 2 (sA0Of 2) (sA1Of 2) sLayerM.2.2 :: (sBlockD ++ [.ret []]))) := by
  have eB : sLayerB.1 = sLayerPre 0 sA0B sKeyB sForsPk ++ sLayerCall 0 sA0B sKeyB sForsPk ::
      (sLayerPath 0 sA0B sForsPk).1 := by rw [sLayerB, sLayerAt_eq]
  have eM : sLayerM.1 = sLayerPre 1 (sA0Of 1) (sA1Of 1) sLayerB.2.2 ++
      sLayerCall 1 (sA0Of 1) (sA1Of 1) sLayerB.2.2 :: (sLayerPath 1 (sA0Of 1) sLayerB.2.2).1 := by
    rw [sLayerM, sLayerAt_eq]
  have eT : sLayerT.1 = sLayerPre 2 (sA0Of 2) (sA1Of 2) sLayerM.2.2 ++
      sLayerCall 2 (sA0Of 2) (sA1Of 2) sLayerM.2.2 :: (sLayerPath 2 (sA0Of 2) sLayerM.2.2).1 := by
    rw [sLayerT, sLayerAt_eq]
  rw [sBody, sAfterDigest, eB, eM, eT]
  simp only [sBlockA, sBlockB, sBlockC, sBlockD, List.append_assoc, List.cons_append,
    List.nil_append]

theorem sBlockA_atoms : atomsOnly sBlockA = true := by decide +kernel
theorem sBlockB_atoms : atomsOnly sBlockB = true := by decide +kernel
theorem sBlockC_atoms : atomsOnly sBlockC = true := by decide +kernel
theorem sBlockD_atoms : atomsOnly sBlockD = true := by decide +kernel

end
end LeanVM.Guest.B1.Sig
