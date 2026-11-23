module

public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Tools

/-!
# `verify_keccak` after the layers: the model's steps and the states

The model from the first opening on, step by step (`afterOpen1`, `afterWord`, `afterSum`,
`afterOpen2`) with the runs of a step's `some` and `none`. The states: `AtR` after the committed
outputs' word (`b44`), `AtW` after its check (`b47`), `AtS` after the column claim (`b55`), `AtV`
after the second opening (`b59`), `AtX` after the final check (`b66`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt)
open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- The committed outputs' column claim. -/
def outsOf (inst sl : Array EW) (word : EW) : Array ColumnClaimW :=
  #[⟨qkeccak, inst.extract 0 4 ++ inst.extract 4 inst.size ++ sl, word⟩]

/-- After the committed outputs' word: its check, then `restSum`. -/
def afterWord (L : Nat) (inst : Array EW) (claim : KeccakClaimW) (sl ws : Array EW) (v w : EW) :
    VM Res := do
  require (ws.getD 0 0 * w == v)
  restSum L claim (outsOf inst sl w)

/-- After the first opening. -/
def afterOpen1 (L : Nat) (inst : Array EW) (claim : KeccakClaimW) (sl ws : Array EW) (v : EW) :
    VM Res := do
  let word ← readScalar
  afterWord L inst claim sl ws v word

/-- After the second opening: the slices, the final check. -/
def afterOpen2 (L : Nat) (claim : KeccakClaimW) (outs : Array ColumnClaimW) (low sl ws : Array EW)
    (v : EW) : VM Res := do
  let slices ← readScalars kBits
  require (multilinearEval claim.mu low * dot ws slices == v)
  pure (outs, low ++ claim.point.extract 0 (L - 4) ++ sl, slices)

/-- After the sumcheck over the pack's instances. -/
def afterSum (L : Nat) (claim : KeccakClaimW) (outs : Array ColumnClaimW) (low : Array EW)
    (v : EW) : VM Res := do
  let (slot, weights, value) ← keccakOpen L claim 0 keccakSegments v
  afterOpen2 L claim outs low slot weights value

end

public section

variable {L : Nat} {inst : Array EW} {first claim : KeccakClaimW} {c v w : EW} {s s1 : TState}
  {sl ws low : Array EW} {outs : Array ColumnClaimW}

theorem segs_eq : keccakSegments = 2 := by decide

theorem restOpen_some (h : (keccakOpen L first 1 1 c).run s = some ((sl, ws, v), s1)) :
    (restOpen L inst first c claim).run s = (afterOpen1 L inst claim sl ws v).run s1 := by
  unfold restOpen afterOpen1 afterWord outsOf
  rw [segs_eq]
  exact run_bind_some (a := (sl, ws, v)) (s' := s1) h

theorem restOpen_none (h : (keccakOpen L first 1 1 c).run s = none) :
    (restOpen L inst first c claim).run s = none := by
  unfold restOpen
  rw [segs_eq]
  exact run_bind_none h

theorem afterOpen1_some (h : readScalar.run s = some (w, s1)) :
    (afterOpen1 L inst claim sl ws v).run s = (afterWord L inst claim sl ws v w).run s1 :=
  run_bind_some h

theorem afterOpen1_none (h : readScalar.run s = none) :
    (afterOpen1 L inst claim sl ws v).run s = none :=
  run_bind_none h

theorem afterWord_true (h : (ws.getD 0 0 * w == v) = true) :
    (afterWord L inst claim sl ws v w).run s = (restSum L claim (outsOf inst sl w)).run s :=
  run_bind_some (require_true h s)

theorem afterWord_false (h : (ws.getD 0 0 * w == v) = false) :
    (afterWord L inst claim sl ws v w).run s = none :=
  run_bind_none (require_false h s)

theorem restSum_some (h : (sumcheckPlain claim.value 3 4).run s = some ((low, v), s1)) :
    (restSum L claim outs).run s = (afterSum L claim outs low v).run s1 := by
  unfold restSum afterSum afterOpen2
  exact run_bind_some (a := (low, v)) (s' := s1) h

theorem restSum_none (h : (sumcheckPlain claim.value 3 4).run s = none) :
    (restSum L claim outs).run s = none := by
  unfold restSum
  exact run_bind_none h

theorem afterSum_some (h : (keccakOpen L claim 0 2 v).run s = some ((sl, ws, w), s1)) :
    (afterSum L claim outs low v).run s = (afterOpen2 L claim outs low sl ws w).run s1 := by
  unfold afterSum
  rw [segs_eq]
  exact run_bind_some (a := (sl, ws, w)) (s' := s1) h

theorem afterSum_none (h : (keccakOpen L claim 0 2 v).run s = none) :
    (afterSum L claim outs low v).run s = none := by
  unfold afterSum
  rw [segs_eq]
  exact run_bind_none h

theorem afterOpen2_none (h : (readScalars 64).run s = none) :
    (afterOpen2 L claim outs low sl ws v).run s = none :=
  run_bind_none h

theorem afterOpen2_false {xs : Array EW}
    (h : (readScalars 64).run s = some (xs, s1))
    (hf : (multilinearEval claim.mu low * dot ws xs == v) = false) :
    (afterOpen2 L claim outs low sl ws v).run s = none := by
  unfold afterOpen2
  exact (run_bind_some (x := readScalars kBits) (a := xs) (s' := s1) h).trans
    (run_bind_none (require_false hf s1))

theorem afterOpen2_true {xs : Array EW}
    (h : (readScalars 64).run s = some (xs, s1))
    (ht : (multilinearEval claim.mu low * dot ws xs == v) = true) :
    (afterOpen2 L claim outs low sl ws v).run s =
      some ((outs, low ++ claim.point.extract 0 (L - 4) ++ sl, xs), s1) := by
  unfold afterOpen2
  exact (run_bind_some (x := readScalars kBits) (a := xs) (s' := s1) h).trans
    ((run_bind_some (require_true ht s1)).trans rfl)

end

@[expose] public section

variable [Labels]

/-- **After the committed outputs' word** (`b44`): the first opening's slot point at 2496, its
rows at the scratch's `rows`, its value in X29, X19; the word's `Option<EW>` at 2592. -/
structure AtR (a : DecArea) (s : TState) (cs : Array ColumnClaimW) (inst output : Array EW)
    (m0 m : MachineData) (s' : TState) (cj : KeccakClaimW) (sl ws : Array EW) (v w : EW) :
    Prop where
  mid : Mid m0 m
  x28 : (m.regs.getXReg .X28).toBitVec = scA m0 + BitVec.ofNat 64 139264
  x29 : m.regs.getXReg .X29 = v.c0
  x19 : m.regs.getXReg .X19 = v.c1
  w40 : NativeRustcVm.WordAt m.dmem (loc m0 40) (UInt64.ofBitVec (loc m0 1248))
  w64 : NativeRustcVm.WordAt m.dmem (loc m0 64) (UInt64.ofBitVec (scA m0 + BitVec.ofNat 64 140288))
  w72 : NativeRustcVm.WordAt m.dmem (loc m0 72) m0.regs.X7
  ts : TStateAt m.dmem (tA m0) a s'
  cls : NativeRustcVm.Layout.ClaimsWAt m.dmem (clA m0) cs
  claim : ClaimAt m.dmem (loc m0 960) cj
  wts : WeightsAt m.dmem (scA m0 + BitVec.ofNat 64 25600) cj
  psz : cj.point.size = inst.size - 4 + 1
  slsz : sl.size = 6
  slot : NativeRustcVm.EWsAt m.dmem (loc m0 2496) sl.toList
  wsz : ws.size = 64
  rows : NativeRustcVm.EWsAt m.dmem (scA m0 + BitVec.ofNat 64 140288) ws.toList
  word : OptEWAt m.dmem (loc m0 2592) (some w)
  run : run0 s inst output m0 = (afterWord m0.regs.X1.toNat inst cj sl ws v w).run s'

/-- **After the word's check** (`b47`): the word in X28 and at 80. -/
structure AtW (a : DecArea) (s : TState) (cs : Array ColumnClaimW) (inst output : Array EW)
    (m0 m : MachineData) (s' : TState) (cj : KeccakClaimW) (sl : Array EW) (w : EW) : Prop where
  mid : Mid m0 m
  x28 : m.regs.getXReg .X28 = w.c0
  w80 : NativeRustcVm.WordAt m.dmem (loc m0 80) w.c1
  w40 : NativeRustcVm.WordAt m.dmem (loc m0 40) (UInt64.ofBitVec (loc m0 1248))
  w64 : NativeRustcVm.WordAt m.dmem (loc m0 64) (UInt64.ofBitVec (scA m0 + BitVec.ofNat 64 140288))
  w72 : NativeRustcVm.WordAt m.dmem (loc m0 72) m0.regs.X7
  ts : TStateAt m.dmem (tA m0) a s'
  cls : NativeRustcVm.Layout.ClaimsWAt m.dmem (clA m0) cs
  claim : ClaimAt m.dmem (loc m0 960) cj
  wts : WeightsAt m.dmem (scA m0 + BitVec.ofNat 64 25600) cj
  psz : cj.point.size = inst.size - 4 + 1
  slsz : sl.size = 6
  slot : NativeRustcVm.EWsAt m.dmem (loc m0 2496) sl.toList
  run : run0 s inst output m0 = (restSum m0.regs.X1.toNat cj (outsOf inst sl w)).run s'

/-- **After the column claim** (`b55`). -/
structure AtS (a : DecArea) (s : TState) (cs : Array ColumnClaimW) (inst output : Array EW)
    (m0 m : MachineData) (s' : TState) (cj : KeccakClaimW) (outs : Array ColumnClaimW) :
    Prop where
  mid : Mid m0 m
  w40 : NativeRustcVm.WordAt m.dmem (loc m0 40) (UInt64.ofBitVec (loc m0 1248))
  w64 : NativeRustcVm.WordAt m.dmem (loc m0 64) (UInt64.ofBitVec (scA m0 + BitVec.ofNat 64 140288))
  w72 : NativeRustcVm.WordAt m.dmem (loc m0 72) m0.regs.X7
  ts : TStateAt m.dmem (tA m0) a s'
  cls : NativeRustcVm.Layout.ClaimsWAt m.dmem (clA m0) (cs ++ outs)
  claim : ClaimAt m.dmem (loc m0 960) cj
  wts : WeightsAt m.dmem (scA m0 + BitVec.ofNat 64 25600) cj
  psz : cj.point.size = inst.size - 4 + 1
  run : run0 s inst output m0 = (restSum m0.regs.X1.toNat cj outs).run s'

/-- **After the second opening** (`b59`): the low point at 3176, the slot point at 2496, the rows
at the scratch's `rows`, the value's `Option<EW>` at 3240; X23, X24 the claim's point. -/
structure AtV (a : DecArea) (s : TState) (cs : Array ColumnClaimW) (inst output : Array EW)
    (m0 m : MachineData) (s' : TState) (cj : KeccakClaimW) (outs : Array ColumnClaimW)
    (low sl ws : Array EW) (v : EW) : Prop where
  fr : VFr m0 m
  x20 : m.regs.getXReg .X20 = m0.regs.X0
  x23 : (m.regs.getXReg .X23).toBitVec = loc m0 1248
  x24 : (m.regs.getXReg .X24).toNat = cj.point.size
  w64 : NativeRustcVm.WordAt m.dmem (loc m0 64) (UInt64.ofBitVec (scA m0 + BitVec.ofNat 64 140288))
  w72 : NativeRustcVm.WordAt m.dmem (loc m0 72) m0.regs.X7
  pk : NativeRustcVm.WordAt m.dmem (loc m0 88) (packW m0)
  ts : TStateAt m.dmem (tA m0) a s'
  cls : NativeRustcVm.Layout.ClaimsWAt m.dmem (clA m0) (cs ++ outs)
  claim : ClaimAt m.dmem (loc m0 960) cj
  psz : cj.point.size = inst.size - 4 + 1
  lowsz : low.size = 4
  lowv : NativeRustcVm.EWsAt m.dmem (loc m0 3176) low.toList
  slsz : sl.size = 6
  slot : NativeRustcVm.EWsAt m.dmem (loc m0 2496) sl.toList
  wsz : ws.size = 64
  rows : NativeRustcVm.EWsAt m.dmem (scA m0 + BitVec.ofNat 64 140288) ws.toList
  val : OptEWAt m.dmem (loc m0 3240) (some v)
  run : run0 s inst output m0 = (afterOpen2 m0.regs.X1.toNat cj outs low sl ws v).run s'

/-- **After the final check** (`b66`): the slices at the `KeccakOutW`'s. -/
structure AtX (a : DecArea) (s : TState) (cs : Array ColumnClaimW) (inst output : Array EW)
    (m0 m : MachineData) (s' : TState) (cj : KeccakClaimW) (outs : Array ColumnClaimW)
    (low sl xs : Array EW) : Prop where
  fr : VFr m0 m
  x23 : (m.regs.getXReg .X23).toBitVec = loc m0 1248
  x24 : (m.regs.getXReg .X24).toNat = cj.point.size
  w72 : NativeRustcVm.WordAt m.dmem (loc m0 72) m0.regs.X7
  pk : NativeRustcVm.WordAt m.dmem (loc m0 88) (packW m0)
  ts : TStateAt m.dmem (tA m0) a s'
  cls : NativeRustcVm.Layout.ClaimsWAt m.dmem (clA m0) (cs ++ outs)
  claim : ClaimAt m.dmem (loc m0 960) cj
  psz : cj.point.size = inst.size - 4 + 1
  lowsz : low.size = 4
  lowv : NativeRustcVm.EWsAt m.dmem (loc m0 3176) low.toList
  slsz : sl.size = 6
  slot : NativeRustcVm.EWsAt m.dmem (loc m0 2496) sl.toList
  xsz : xs.size = 64
  slices : NativeRustcVm.EWsAt m.dmem (oA m0 + BitVec.ofNat 64 584) xs.toList
  run : run0 s inst output m0 =
    some ((outs, low ++ cj.point.extract 0 (m0.regs.X1.toNat - 4) ++ sl, xs), s')

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
