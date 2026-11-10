import Rv64Verifier.Proofs.Pcs.VsoRowed

/-!
# `verify_stacked_opening`'s level loop: the glue's contract

After the level's intro message is pushed onto the pending claims (`Vec<(Vec<E>, GluedWeight)>`
at `S - 616`), the loop at `0x8000b650`..`0x8000b824` glues them (`glueRust`): per claim,
`scalar *= lam` (`scalar` at `S - 408`, `lam`'s limbs at `S - 976`, `S - 984`, `S - 992`), the
intro added to the running quadratic in place (its buffer at `S - 896`, its length in `s7`), the
`GluedClaim` (the weight, the scalar, `fold_start` = the folds' length at `S - 672`) pushed onto
`glued` (`Vec<GluedClaim>` at `S - 664`, `grow_one` at `0x8000db78`). It leaves at `0x8000b510`.

`GlueIn` is the state at `0x8000b650`, `GlueOut` at `0x8000b510`; `GlueSpec` is the loop's
contract.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

/-- The pending claim `i`'s address. -/
@[rv_addr] def pAddr (g s : MachineState) (i : ℕ) : Word :=
  vecPtr g (s.getReg .x2 - 616) + BitVec.ofNat 64 (80 * i)

/-- What the glue reads at `g`: the pending claims' buffer, their intros' buffers, their weights'
buffers, and the glued claims' weights' buffers. -/
def GlueReads (s g : MachineState) (y : Word) : Prop :=
  Within y (vecPtr g (s.getReg .x2 - 616)) (80 * (vecLen g (s.getReg .x2 - 616)).toNat) ∨
    (∃ i < (vecLen g (s.getReg .x2 - 616)).toNat,
      Within y (vecPtr g (pAddr g s i)) (24 * (vecLen g (pAddr g s i)).toNat) ∨
        InBufs g (pAddr g s i + 24) y) ∨
    ∃ i < (vecLen g (s.getReg .x2 - 664)).toNat, InBufs g (gAddr g s i) y

/-- At `0x8000b650`, the pending claims `pend` to glue with powers of `lam` into `Wl`. -/
structure GlueIn (s g : MachineState) (lam : E) (Wl : Model.Pcs.WhirLocals)
    (pend : List (List E × Model.Pcs.GluedWeightRust)) : Prop where
  pc : g.pc = 0x8000b650
  sp : g.getReg .x2 = s.getReg .x2 - 1040
  inv : InvR s g (g.getMem nextAddr)
  heap : HeapOk g
  /-- The pending claims: `x18` their buffer, `x22` their count. -/
  x18 : g.getReg .x18 = vecPtr g (s.getReg .x2 - 616)
  x22 : g.getReg .x22 = vecLen g (s.getReg .x2 - 616)
  npos : 0 < pend.length
  pnd : pendAt g (vecPtr g (s.getReg .x2 - 616)) (vecLen g (s.getReg .x2 - 616)).toNat = pend
  pbuf : (vecPtr g (s.getReg .x2 - 616)).toNat % 8 = 0 ∧
    heapStart ≤ (vecPtr g (s.getReg .x2 - 616)).toNat ∧
    (vecPtr g (s.getReg .x2 - 616)).toNat + 80 * (vecLen g (s.getReg .x2 - 616)).toNat ≤ heapNext g
  intro : ∀ i < (vecLen g (s.getReg .x2 - 616)).toNat, VecOk g (pAddr g s i) 24 8
  /-- The running quadratic: its buffer at `S - 896`, its length in `x23`. -/
  quad : eListAt g (g.getMem (s.getReg .x2 - 896)) (g.getReg .x23).toNat = Wl.runningQuad ∧
    (g.getMem (s.getReg .x2 - 896)).toNat % 8 = 0 ∧ ((g.getReg .x23).toNat = 0 ∨
      heapNext s ≤ (g.getMem (s.getReg .x2 - 896)).toNat ∧
      (g.getMem (s.getReg .x2 - 896)).toNat + 24 * (g.getReg .x23).toNat ≤ heapNext g)
  folds : g.getMem (s.getReg .x2 - 672) = BitVec.ofNat 64 Wl.folds.length
  flen : Wl.folds.length < 2 ^ 64
  lam : (g.getMem (s.getReg .x2 - 976), g.getMem (s.getReg .x2 - 984),
    g.getMem (s.getReg .x2 - 992)) = Model.limbs lam
  one : eAt g (s.getReg .x2 - 408) = 1
  glued : VecOk g (s.getReg .x2 - 664) 88 8 ∧
    gluedListAt g (vecPtr g (s.getReg .x2 - 664)) (vecLen g (s.getReg .x2 - 664)).toNat = Wl.glued ∧
    (vecCap g (s.getReg .x2 - 664) = 0 ∨ heapNext s ≤ (vecPtr g (s.getReg .x2 - 664)).toNat)
  /-- The glued claims' and the pending claims' weights, their buffers aligned. -/
  galigned : ∀ i < (vecLen g (s.getReg .x2 - 664)).toNat, WeightAligned g (gAddr g s i)
  paligned : ∀ i < (vecLen g (s.getReg .x2 - 616)).toNat, WeightAligned g (pAddr g s i + 24)
  /-- The quadratic's and the glued claims' buffers apart, and apart from what the glue reads. -/
  apart : Apart (g.getMem (s.getReg .x2 - 896)) (24 * (g.getReg .x23).toNat)
    (vecPtr g (s.getReg .x2 - 664)) ((vecCap g (s.getReg .x2 - 664)).toNat * 88)
  reads : ∀ y, GlueReads s g y → heapStart ≤ y.toNat ∧ y.toNat < heapNext g ∧
    ¬ Within y (g.getMem (s.getReg .x2 - 896)) (24 * (g.getReg .x23).toNat) ∧
    ¬ Within y (vecPtr g (s.getReg .x2 - 664)) ((vecCap g (s.getReg .x2 - 664)).toNat * 88)

/-- What the glue writes from `g` on: the quadratic's buffer, the glued claims' buffer and
header, the scratch `S - 464`..`S - 304` and `S - 160`, the callees' stacks, `NEXT`, the heap
allocated since `g`. -/
def GlueW (s g z : MachineState) (a : Word) : Prop :=
  Within a (g.getMem (s.getReg .x2 - 896)) (24 * (g.getReg .x23).toNat) ∨
    Within a (vecPtr g (s.getReg .x2 - 664)) ((vecCap g (s.getReg .x2 - 664)).toNat * 88) ∨
    Within a (s.getReg .x2 - 664) 24 ∨ Within a (s.getReg .x2 - 464) 160 ∨
    Within a (s.getReg .x2 - 160) 24 ∨ Within a (s.getReg .x2 - 2464) 1424 ∨
    Within a nextAddr 8 ∨ Fresh g z a

/-- At `0x8000b510`, from `g`: the quadratic and the glued claims of `Wl'`. -/
structure GlueOut (s g z : MachineState) (Wl' : Model.Pcs.WhirLocals) : Prop where
  pc : z.pc = 0x8000b510
  sp : z.getReg .x2 = s.getReg .x2 - 1040
  regs : ∀ q ∈ [Reg.x9, .x25, .x26], z.getReg q = g.getReg q
  inv : InvR s z (z.getMem nextAddr)
  heap : HeapOk z
  mono : heapNext g ≤ heapNext z
  fr : DFrame g z (GlueW s g z)
  quad : eListAt z (g.getMem (s.getReg .x2 - 896)) (g.getReg .x23).toNat = Wl'.runningQuad
  glued : VecOk z (s.getReg .x2 - 664) 88 8 ∧
    gluedListAt z (vecPtr z (s.getReg .x2 - 664)) (vecLen z (s.getReg .x2 - 664)).toNat =
      Wl'.glued ∧
    ((vecPtr z (s.getReg .x2 - 664) = vecPtr g (s.getReg .x2 - 664) ∧
        vecCap z (s.getReg .x2 - 664) = vecCap g (s.getReg .x2 - 664)) ∨
      NewBuf g z (vecPtr z (s.getReg .x2 - 664)) ((vecCap z (s.getReg .x2 - 664)).toNat * 88) 8)
  aligned : ∀ i < (vecLen z (s.getReg .x2 - 664)).toNat, WeightAligned z (gAddr z s i)
  /-- Every glued claim's weight points where a pending or a glued claim's did at `g`. -/
  bufs : ∀ i < (vecLen z (s.getReg .x2 - 664)).toNat, ∀ y, InBufs z (gAddr z s i) y →
    GlueReads s g y

/-- **The glue**, from `0x8000b650` to `0x8000b510`, or a dead end. -/
def GlueSpec : Prop :=
  ∀ (s g : MachineState) (lam : E) (Wl : Model.Pcs.WhirLocals)
    (pend : List (List E × Model.Pcs.GluedWeightRust)), VsoPre s → GlueIn s g lam Wl pend →
    ∃ z, Reaches Image.code g z ∧ (Dead Image.code z ∨ GlueOut s g z (Model.Pcs.glueRust lam Wl pend))

end Rv64Verifier.Proofs.Pcs.Vso
