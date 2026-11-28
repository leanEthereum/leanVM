module

public import NativeRustcVmArm.Transcript.Glue
public import NativeRustcVmArm.Code.Vm.DecodedStreamElement
public meta import NativeRustcVmArm.Code.Vm.DecodedStreamElement
public meta import NativeRustcVmArm.Transcript.Glue

/-!
# `Decoded::stream_element`'s blocks, run by the symbolic executor

`regsS` (no region) at `b0` (the slice empty?) and `b2` (`2 i + 3` against the length); `countS`
at `b1`: region 0 the stream's count (X1), compared with `i` (X3); `noneS` at `b3`: region 0 the
output (X0), its tag word zeroed; `someS` at `b4`: region 0 the output (X0), region 1 element `i`
at `words + 8 (1 + 2 i)` (`elemAddr`, the address `b4` computes from X1 and X8 = `2 i`, minus `8`).
-/

namespace NativeRustcVmArm.Transcript.StreamElement

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.DecodedStreamElement

@[expose] public section

/-- No region. -/
def regsS : SState := init [] .sp

/-- At `b1`: the stream's count (region 0, X1). -/
def countS : SState := init [(8, false)] .sp [(.X1, .ptr 0 0)]

/-- At `b3`: the output (region 0, X0). -/
def noneS : SState := init [(24, false)] .sp [(.X0, .ptr 0 0)]

/-- `x1 + (x8 << 3)`. -/
def elemAddr : Sym := .bin .add .W64 (.reg .X1) (.un (.shift .LSL 3) .W64 (.reg .X8))

/-- At `b4`: the output (region 0, X0), the element (region 1, 8 bytes past `elemAddr`). -/
def someS : SState :=
  init [(24, false), (16, false)] .sp [(.X0, .ptr 0 0)] (aliases := [(elemAddr, (1, -8))])

/-- What `b4` leaves: the tag `1`, the element's limbs. -/
def SomeOk (S : SState) : Prop :=
  (∀ t < 8, findWrite 0 t S.mem = some (.lit 1, t)) ∧
    (∀ t < 8, findWrite 0 (8 + t) S.mem = some (.load 1 0 8, t)) ∧
    (∀ t < 8, findWrite 0 (16 + t) S.mem = some (.load 1 8 8, t)) ∧
    (∀ w ∈ S.mem, w.r = 0 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 24) ∧ keeps someS S = true ∧
    S.reg .X30 = some (.reg .X30)

instance (S : SState) : Decidable (SomeOk S) := by unfold SomeOk; infer_instance

/-- What `b3` leaves: the tag `0`. -/
def NoneOk (S : SState) : Prop :=
  (∀ t < 8, findWrite 0 t S.mem = some (.lit 0, t)) ∧
    (∀ w ∈ S.mem, w.r = 0 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 24) ∧ keeps noneS S = true ∧
    S.reg .X30 = some (.reg .X30)

instance (S : SState) : Decidable (NoneOk S) := by unfold NoneOk; infer_instance

end

set_option Elab.async false

sym_block run_b0 := exec b0 regsS
sym_block run_b1 := exec b1 countS
sym_block run_b2 := exec b2 regsS
sym_block run_b3 := exec b3 noneS
sym_block run_b4 := exec b4 someS

public theorem keeps_b0 : keeps regsS (after b0 regsS) = true := by decide +kernel
public theorem keeps_b1 : keeps countS (after b1 countS) = true := by decide +kernel
public theorem keeps_b2 : keeps regsS (after b2 regsS) = true := by decide +kernel
public theorem none_b3 : NoneOk (after b3 noneS) := by decide +kernel
public theorem some_b4 : SomeOk (after b4 someS) := by decide +kernel

end NativeRustcVmArm.Transcript.StreamElement
