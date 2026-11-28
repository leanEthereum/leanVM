module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Model

/-!
# `verify_keccak`'s back half in the model (x86-64)

`restOpen` (the opening of the committed outputs, the committed word, `restSum`) step by step, in
the order of the Rust's calls: each step's `none` is the phase's `none`, its `some` the rest's run.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol.Verifier

public section

theorem segs_eq : keccakSegments = 2 := by decide

theorem segs1 : keccakSegments - 1 = 1 := by decide

theorem slotBits_eq : qkeccakSlotBits = 6 := by decide

theorem kBits_eq : kBits = 64 := by decide

theorem qkeccak_eq : qkeccak = 4 := by decide

/-- The column claim of the committed outputs. -/
@[expose] def outClaim (inst slot : Array EW) (word : EW) : ColumnClaimW :=
  ⟨qkeccak, inst.extract 0 4 ++ inst.extract 4 inst.size ++ slot, word⟩

variable {L : Nat} {inst : Array EW} {first cl : KeccakClaimW} {cm : EW} {s s1 s2 s3 s4 : TState}

theorem restOpen_none (h : (keccakOpen L first 1 1 cm).run s = none) :
    (restOpen L inst first cm cl).run s = none := by
  rw [restOpen, StateT.run_bind, segs1, h]; rfl

theorem restOpen_some {sl ws : Array EW} {v : EW}
    (h : (keccakOpen L first 1 1 cm).run s = some ((sl, ws, v), s1)) :
    (restOpen L inst first cm cl).run s = (restWord L inst sl ws v cl).run s1 := by
  rw [restOpen, StateT.run_bind, segs1, h]; rfl

variable {sl ws : Array EW} {v : EW}

theorem restWord_none (h : readScalar.run s = none) :
    (restWord L inst sl ws v cl).run s = none := by
  unfold restWord; exact run_bind_none h

theorem restWord_bad {w : EW} (h : readScalar.run s = some (w, s1))
    (hb : (ws.getD 0 0 * w == v) = false) : (restWord L inst sl ws v cl).run s = none := by
  unfold restWord
  rw [run_bind_some h, run_bind_none (require_false hb s1)]

theorem restWord_ok {w : EW} (h : readScalar.run s = some (w, s1))
    (hb : (ws.getD 0 0 * w == v) = true) :
    (restWord L inst sl ws v cl).run s = (restSum L cl #[outClaim inst sl w]).run s1 := by
  unfold restWord
  rw [run_bind_some h, run_bind_some (require_true hb s1)]
  rfl

variable {outs : Array ColumnClaimW}

theorem restSum_none (h : (sumcheckPlain cl.value 3 4).run s = none) :
    (restSum L cl outs).run s = none := by
  unfold restSum; exact run_bind_none h

theorem restSum_open_none {low : Array EW} {v1 : EW}
    (h : (sumcheckPlain cl.value 3 4).run s = some ((low, v1), s1))
    (h1 : (keccakOpen L cl 0 2 v1).run s1 = none) : (restSum L cl outs).run s = none := by
  unfold restSum
  rw [run_bind_some h]
  show ((keccakOpen L cl 0 keccakSegments v1 >>= _)).run s1 = none
  rw [segs_eq]
  exact run_bind_none h1

theorem restSum_read_none {low : Array EW} {v1 : EW} {sl2 ws2 : Array EW} {v2 : EW}
    (h : (sumcheckPlain cl.value 3 4).run s = some ((low, v1), s1))
    (h1 : (keccakOpen L cl 0 2 v1).run s1 = some ((sl2, ws2, v2), s2))
    (h2 : (readScalars 64).run s2 = none) : (restSum L cl outs).run s = none := by
  unfold restSum
  rw [run_bind_some h]
  show ((keccakOpen L cl 0 keccakSegments v1 >>= _)).run s1 = none
  rw [segs_eq, run_bind_some h1]
  show ((readScalars kBits >>= _)).run s2 = none
  rw [kBits_eq]
  exact run_bind_none h2

theorem restSum_bad {low : Array EW} {v1 : EW} {sl2 ws2 : Array EW} {v2 : EW} {sls : Array EW}
    (h : (sumcheckPlain cl.value 3 4).run s = some ((low, v1), s1))
    (h1 : (keccakOpen L cl 0 2 v1).run s1 = some ((sl2, ws2, v2), s2))
    (h2 : (readScalars 64).run s2 = some (sls, s3))
    (hb : (multilinearEval cl.mu low * dot ws2 sls == v2) = false) :
    (restSum L cl outs).run s = none := by
  unfold restSum
  rw [run_bind_some h]
  show ((keccakOpen L cl 0 keccakSegments v1 >>= _)).run s1 = none
  rw [segs_eq, run_bind_some h1]
  show ((readScalars kBits >>= _)).run s2 = none
  rw [kBits_eq, run_bind_some h2]
  exact run_bind_none (require_false hb s3)

theorem restSum_ok {low : Array EW} {v1 : EW} {sl2 ws2 : Array EW} {v2 : EW} {sls : Array EW}
    (h : (sumcheckPlain cl.value 3 4).run s = some ((low, v1), s1))
    (h1 : (keccakOpen L cl 0 2 v1).run s1 = some ((sl2, ws2, v2), s2))
    (h2 : (readScalars 64).run s2 = some (sls, s3))
    (hb : (multilinearEval cl.mu low * dot ws2 sls == v2) = true) :
    (restSum L cl outs).run s =
      some ((outs, low ++ cl.point.extract 0 (L - 4) ++ sl2, sls), s3) := by
  unfold restSum
  rw [run_bind_some h]
  show ((keccakOpen L cl 0 keccakSegments v1 >>= _)).run s1 = _
  rw [segs_eq, run_bind_some h1]
  show ((readScalars kBits >>= _)).run s2 = _
  rw [kBits_eq, run_bind_some h2, run_bind_some (require_true hb s3)]
  rfl

/-- `EW`'s `==` limb by limb. -/
theorem ew_beq (x y : EW) : (x == y) = (x.c0 == y.c0 && x.c1 == y.c1) := rfl

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
