module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.DecodedStreamElement
public import NativeRustcVmX64.Code.Vm.DecodedStreamElement.Names
public meta import NativeRustcVmX64.Code.Vm.DecodedStreamElement
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `Decoded::stream_element`'s blocks, run by the symbolic executor (x86-64)

`regsS` (no region) at `b0` (the slice empty?) and `b2` (`2 i + 3` against the length, with its
carry); `countS` at `b1`: region 0 the stream's count (RSI), compared with `i` (RCX); `noneS` at
`b3` but its `ret`: region 0 the output (RDI), its tag word zeroed; `someS` at `b4` but its `ret`:
region 0 the output (RDI), region 1 element `i` at `words + 8 (1 + 2 i)` (`elemAddr`, the address
`b4` computes from RSI and RCX = `2 i`, minus `8`); `retS` at the `ret`s: region 0 the return
address.
-/

namespace NativeRustcVmX64.Transcript.StreamElement

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.DecodedStreamElement

@[expose] public section

/-- No region. -/
def regsS : SState := init []

/-- At `b1`: the stream's count (region 0, RSI). -/
def countS : SState := init [8] [(.rsi, .ptr 0 0)]

/-- At `b3`: the output (region 0, RDI). -/
def noneS : SState := init [24] [(.rdi, .ptr 0 0)]

/-- `rsi + 8 rcx`. -/
def elemAddr : Sym := .bin .add .W64 (.reg .rsi) (.bin .mul .W64 (.reg .rcx) (.lit 8))

/-- At `b4`: the output (region 0, RDI), the element (region 1, 8 bytes past `elemAddr`). -/
def someS : SState :=
  init [24, 16] [(.rdi, .ptr 0 0)] (aliases := [(elemAddr, (1, -8))])

/-- At a `ret`: the return address (region 0, RSP). -/
def retS : SState := init [8] [(.rsp, .ptr 0 0)]

/-- `2 i + 3`, as `b2` computes it. -/
def sum3 : Sym :=
  .bin .sub .W64 (.bin .add .W64 (.reg .rcx) (.reg .rcx)) (.lit 18446744073709551613)

/-- `b2`'s exit condition: neither `2 i + 3` past the length nor its carry. -/
def condB2 : SBool :=
  .cmp .eq .W8
    (.bin .or .W8
      (.bin .merge .W8 sum3
        (.ite ((SBool.cmp .ult .W64 sum3 (.reg .rdx)).not.and (SBool.cmp .eq .W64 sum3 (.reg .rdx)).not)
          (.lit 1) (.lit 0)))
      (.bin .merge .W8 (.reg .r8)
        (.ite (SBool.cmp .ult .W64 (.bin .add .W64 (.reg .rcx) (.reg .rcx))
          (.lit 18446744073709551613)).not (.lit 1) (.lit 0))))
    (.lit 0)

/-- What `b4` leaves: the tag `1`, the element's limbs. -/
def SomeOk (S : SState) : Prop :=
  (∀ t < 8, findWrite 0 t S.mem = some (.lit 1, t)) ∧
    (∀ t < 8, findWrite 0 (8 + t) S.mem = some (.load 1 0 8, t)) ∧
    (∀ t < 8, findWrite 0 (16 + t) S.mem = some (.load 1 8 8, t)) ∧
    (∀ w ∈ S.mem, w.r = 0 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 24) ∧ keeps someS S = true ∧
    S.reg .rsp = some (.reg .rsp)

instance (S : SState) : Decidable (SomeOk S) := by unfold SomeOk; infer_instance

/-- What `b3` leaves: the tag `0`. -/
def NoneOk (S : SState) : Prop :=
  (∀ t < 8, findWrite 0 t S.mem = some (.lit 0, t)) ∧
    (∀ w ∈ S.mem, w.r = 0 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 24) ∧ keeps noneS S = true ∧
    S.reg .rsp = some (.reg .rsp)

instance (S : SState) : Decidable (NoneOk S) := by unfold NoneOk; infer_instance

end

set_option Elab.async false

sym_block run_b0 := exec b0 regsS
sym_block run_b1 := exec b1 countS
sym_block run_b2 := exec b2 regsS
sym_block run_b3 := exec (b3.take 3) noneS
sym_block run_b3r := exec (b3.drop 3) retS
sym_block run_b4 := exec (b4.take 7) someS
sym_block run_b4r := exec (b4.drop 7) retS

public theorem ok_b0 : keeps regsS (after b0 regsS) = true ∧ (after b0 regsS).mem = [] ∧
    (∀ r ∈ allRegs, (after b0 regsS).reg r = some (.reg r)) := by
  decide +kernel
public theorem ok_b1 : keeps countS (after b1 countS) = true ∧ (after b1 countS).mem = [] ∧
    (after b1 countS).reg .rsi = some (.ptr 0 0) ∧
    (∀ r ∈ allRegs, r ≠ .rsi → (after b1 countS).reg r = some (.reg r)) := by
  decide +kernel
public theorem exit_b2 : exec b2 regsS = some (after b2 regsS, .cond condB2 NativeRustcVmX64.Vm.DecodedStreamElement.label_6) :=
  run_b2.trans (by rw [after_eq run_b2]; rfl)
public theorem ok_b2 : keeps regsS (after b2 regsS) = true ∧ (after b2 regsS).mem = [] ∧
    (after b2 regsS).reg .rsp = some (.reg .rsp) ∧ (after b2 regsS).reg .rdi = some (.reg .rdi) ∧
    (after b2 regsS).reg .rsi = some (.reg .rsi) ∧
    (after b2 regsS).reg .rcx = some (.bin .add .W64 (.reg .rcx) (.reg .rcx)) := by
  decide +kernel
public theorem none_b3 : NoneOk (after (b3.take 3) noneS) := by decide +kernel
public theorem some_b4 : SomeOk (after (b4.take 7) someS) := by decide +kernel
public theorem ok_ret : EpiOk 0 [] (after (b3.drop 3) retS) = true ∧ (after (b3.drop 3) retS).mem = [] ∧
    EpiOk 0 [] (after (b4.drop 7) retS) = true ∧ (after (b4.drop 7) retS).mem = [] := by
  decide +kernel

end NativeRustcVmX64.Transcript.StreamElement
