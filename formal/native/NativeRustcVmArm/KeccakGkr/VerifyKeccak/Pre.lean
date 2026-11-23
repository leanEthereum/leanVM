module

public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Keep
public import NativeVm.Equiv.KeccakRmfe

/-!
# `verify_keccak`: what its callees' preconditions share

In a state of the frame (`VFr`), for a callee using `N'` bytes of stack: its `StackOk`
(`stackOk_of`), the round constants (`rcAt_of`), `RMFE_PROJECT` and `KECCAK_RHO`
(`projectAt_of`, `rhoAt_of`), the `TState`'s footprint (`tok_of`), an output in the frame
(`outOk_loc`) or in an output region (`frame_ok`, `out_ok`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (scratchBytes outBytes)
open NativeRustcVm (Region)

public section

variable [Labels] {a : DecArea} {s : TState} {cs : Array ColumnClaimW} {inst output : Array EW}
  {m0 st : MachineData}

theorem stackOk_of (hn : Nums a inst m0) (hfr : VFr m0 st) {N' : Nat} (hN' : N' ≤ 3648) :
    StackOk st N' :=
  hfr.stackOk hn.stk (by decide) (by rw [stack_eq]; omega)

/-- The frame's bytes from `o` are data memory. -/
theorem frame_mapped' (hn : Nums a inst m0) (hfr : VFr m0 st) {o n : Nat} (ho : o + n ≤ 3360) :
    Mapped st.dmem (loc m0 o) n :=
  Mapped.kept' (NativeRustcVm.Mapped.sub (frame_mapped hn.stk (by decide)) ho) hfr.kept

theorem loc_noWrap (hn : Nums a inst m0) {o n : Nat} (ho : o + n ≤ 3360) : NoWrap (loc m0 o) n := by
  have := hn.hN; have := m0.regs.SP.toNat_lt
  unfold NoWrap; rw [loc_toNat hn.hN (by omega)]; omega

omit [Labels] in
/-- A part of a region the entry's facts make data memory. -/
theorem mapped_of {A : BitVec 64} {n : Nat} (h : Mapped m0.dmem A n) (hfr : VFr m0 st) {o k : Nat}
    (hk : o + k ≤ n) : Mapped st.dmem (A + BitVec.ofNat 64 o) k :=
  Mapped.kept' (NativeRustcVm.Mapped.sub h hk) hfr.kept

theorem ok_t (h : P0 a s cs inst output m0) : Mapped m0.dmem (tA m0) 760 :=
  (Areas.ok h.areas (r := ⟨tA m0, tstateBytes⟩) (Or.inl (by simp [wsOf]))).1
theorem ok_sc (h : P0 a s cs inst output m0) : Mapped m0.dmem (scA m0) 205824 :=
  (Areas.ok h.areas (r := ⟨scA m0, scratchBytes⟩) (Or.inl (by simp [wsOf]))).1
theorem ok_cl (h : P0 a s cs inst output m0) : Mapped m0.dmem (clA m0) 97288 :=
  (Areas.ok h.areas (r := ⟨clA m0, NativeRustcVm.Layout.claimsBytes⟩) (Or.inl (by simp [wsOf]))).1
theorem ok_out (h : P0 a s cs inst output m0) : Mapped m0.dmem (oA m0) 1608 :=
  (Areas.ok h.areas (r := ⟨oA m0, outBytes⟩) (Or.inl (by simp [wsOf]))).1
theorem ok_w (h : P0 a s cs inst output m0) : Mapped m0.dmem a.words (8 * a.len) :=
  (Areas.ok h.areas (r := a.region) (Or.inr (by simp [rsOf]))).1
theorem ok_ip (h : P0 a s cs inst output m0) : Mapped m0.dmem (ipA m0) (16 * inst.size) :=
  (Areas.ok h.areas (r := ewsRegion (ipA m0) inst.size) (Or.inr (by simp [rsOf]))).1
theorem ok_op (h : P0 a s cs inst output m0) : Mapped m0.dmem (opA m0) 400 :=
  (Areas.ok h.areas (r := ewsRegion (opA m0) 25) (Or.inr (by simp [rsOf]))).1

theorem rcAt_of (h : P0 a s cs inst output m0) (hn : Nums a inst m0) (hfr : VFr m0 st)
    {N' : Nat} (hN' : N' ≤ 3648) : RcAt st N' := by
  have := hn.hN; have := hn.rcS; have := hn.rcW
  refine ⟨bytes_m0 hn hfr h.rc.1 ?_ ?_ ?_, h.rc.2.1, ?_⟩
  · rw [NativeRustcVm.length_flatMap_const NativeRustcVm.length_wordBytes]; exact hn.rcW
  · rw [NativeRustcVm.length_flatMap_const NativeRustcVm.length_wordBytes]; exact hn.rcS
  · rw [NativeRustcVm.length_flatMap_const NativeRustcVm.length_wordBytes]
    intro q hq
    have := hn.t_rc; have := hn.s_rc; have := hn.c_rc; have := hn.o_rc
    have : LeanVM.Parameters.keccakRC.length = 24 := rfl
    rcases outs_nat hn hq with _ | _ | _ | _ <;> omega
  · unfold Apart; rw [sb_toNat hn.hN hfr hN']; omega

theorem projectAt_of (h : P0 a s cs inst output m0) (hn : Nums a inst m0) (hfr : VFr m0 st) :
    ProjectAt st := by
  have hl : rmfeProjectW.toList.length = 16 := by
    simp [rmfeProjectW, NativeVm.Equiv.rmfeProject_length]
  refine bytes_m0 hn hfr h.proj ?_ ?_ ?_
  · rw [NativeRustcVm.length_flatMap_const NativeRustcVm.length_wordBytes, hl]; exact hn.pjW
  · rw [NativeRustcVm.length_flatMap_const NativeRustcVm.length_wordBytes, hl]; exact hn.pjS
  · rw [NativeRustcVm.length_flatMap_const NativeRustcVm.length_wordBytes]
    intro q hq
    have := hn.t_pj; have := hn.s_pj; have := hn.c_pj; have := hn.o_pj
    rcases outs_nat hn hq with _ | _ | _ | _ <;> omega

theorem rhoAt_of (h : P0 a s cs inst output m0) (hn : Nums a inst m0) (hfr : VFr m0 st) :
    RhoAt st := by
  have hl : rhoBytes.length = 100 := by decide
  refine bytes_m0 hn hfr h.rho (by rw [hl]; exact hn.rhW) (by rw [hl]; exact hn.rhS) ?_
  rw [hl]
  intro q hq
  have := hn.t_rh; have := hn.s_rh; have := hn.c_rh; have := hn.o_rh
  rcases outs_nat hn hq with _ | _ | _ | _ <;> omega

theorem tok_of (hn : Nums a inst m0) (hfr : VFr m0 st) {N' : Nat} (hN' : N' ≤ 3648) :
    TStateOk st (tA m0) a N' := by
  have := hn.hN; have := hn.tS; have := hn.wS; have := hn.t_rc
  have e : tstateBytes = 760 := rfl
  refine ⟨?_, ?_, this⟩ <;> unfold Apart <;> rw [sb_toNat hn.hN hfr hN'] <;> omega

/-- **An output in the frame**, below the slots. -/
theorem outOk_loc (hn : Nums a inst m0) (hfr : VFr m0 st)
    {N' o n : Nat} (hN' : N' ≤ 3648) (ho : o + n ≤ 3264) :
    OutOk st (tA m0) a (loc m0 o) n N' := by
  have := hn.hN; have := hn.tS; have := hn.wS; have := hn.rcS
  have e : tstateBytes = 760 := rfl
  have hl := loc_toNat (m0 := m0) hn.hN (o := o) (by omega)
  refine ⟨frame_mapped' hn hfr (by omega), loc_noWrap hn (by omega), ?_, ?_, ?_, ?_⟩ <;>
    unfold Apart <;> (try rw [sb_toNat hn.hN hfr hN']) <;> rw [hl] <;> omega

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
