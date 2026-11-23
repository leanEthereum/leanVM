module

public import NativeRustcVmX64.Keccak.KeccakF.RoundLanes
public import NativeRustcVmX64.Code.Vm.KeccakF.Names

/-!
# One turn of `keccak_f`'s round loop (x86-64)

`round_step`: from the loop head after `i < 24` rounds (`At m0 i`), the machine inevitably reaches
the loop invariant after `i + 1` rounds, back at the loop head (`NativeRustcVmX64.Vm.KeccakF.label_1`) or, after the 24th,
at the epilogue. The loop body runs in a fresh environment of the machine at the head (region: the
frame; the counter's value the variable 0), computes the round (`body_lanes`, the lanes by
`lane_round`) with the round constant it loads from the frame's copy, and keeps the state pointer,
the pushed registers, the round constants and memory outside the frame.
-/

namespace NativeRustcVmX64.KeccakF

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
  LeanVM.Parameters
open NativeRustcX64.KeccakF (WordAt wordAt_of_eq wordAt_write wordAt_keep same_region
  load_of_wordAt allOf_imp)
open NativeRustcVmX64.Keccak

public section


theorem stAfter_succ (m0 : MachineData) {i : Nat} (hi : i < 24) :
    stAfter m0 (i + 1) = Keccak.round (stAfter m0 i) (keccakRC.getD i 0) :=
  roundsTo_succ _ hi

variable [Host]

/-- **One round of the loop.** -/
theorem round_step {k : Nat} (hp : Placed Vm.KeccakF.code k) {m0 : MachineData}
    (hstk : StackOk m0 NativeRustcVmX64.keccakFStack) {i : Nat} (hi : i < 24) {m : MachineData}
    (hA : At m0 i m) :
    Eventually (step1 Host.exe) (fun st => At m0 (i + 1) st.data ∧
      st.pc = if i + 1 = 24 then Host.addrOf (k + NativeRustcVmX64.Vm.KeccakF.b3Offset) else Host.addrOf (k + NativeRustcVmX64.Vm.KeccakF.b2Offset))
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.KeccakF.b2Offset)⟩ := by
  have hk : Vm.KeccakF.b2.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.KeccakF.b2Offset) :=
    Vm.KeccakF.b2_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let env := Env.ofMachine m [(frame m0, 488)] fun _ => BitVec.ofNat 64 (2 + i)
  have hv : env.vars 0 = BitVec.ofNat 64 (2 + i) := rfl
  have hwf : env.WF :=
    Env.wf_of ⟨⟨fun j hj => hA.kept _ (hstk.2.2 j hj), frame_noWrap hstk⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm : Match env startBody m :=
    match_ofMachine ⟨rfl, trivial⟩
      ⟨show rspOf m = _ from hA.rsp.trans rfl, hA.ctr, trivial⟩ trivial
      ⟨show (BitVec.ofNat 64 (2 + i)).toNat < 26 by simp; omega, trivial⟩ trivial
  have hb0 : env.regions[0]? = some (frame m0, 488) := rfl
  have hrcl : rcSym.eval env = (keccakRC.getD i 0).toBitVec := by
    have hidx : 224 + ((Sym.bin .mul .W64 (.var 0) (.lit 8)).eval env).toNat = 240 + 8 * i := by
      simp only [Sym.eval, BinOp.apply, hv]
      simp
      omega
    show env.load 0 (224 + ((Sym.bin .mul .W64 (.var 0) (.lit 8)).eval env).toNat) 8 = _
    rw [hidx]
    exact load_rc_at hA.rc hi
  refine exec_then hk body hwf nofun hm fun st hm' hpc => .done _ ⟨?_, ?_⟩
  · obtain ⟨hregs, hslots⟩ := body_lanes body hm' hb0 hA.regs
      (allOf_imp (fun p _ h => load_of_wordAt (r := 0) h) hA.slots) hrcl
    have hl : ∀ p ∈ laneRegs, p.2 < 25 := by decide
    have hs : ∀ p ∈ laneSlots, p.2 < 25 := by decide
    have hsv := hA.saved
    simp only [AllOf, savedSlots] at hsv
    obtain ⟨s0, s1, s2, s3, s4, s5, -⟩ := hsv
    refine ⟨(hm'.regs .rsp _ rfl).trans rfl, ?_, wordAt_keep hm' hb0 (by decide) rfl hA.ptr,
      ?_, ?_,
      ⟨wordAt_keep hm' hb0 (by decide) rfl s0, wordAt_keep hm' hb0 (by decide) rfl s1,
        wordAt_keep hm' hb0 (by decide) rfl s2, wordAt_keep hm' hb0 (by decide) rfl s3,
        wordAt_keep hm' hb0 (by decide) rfl s4, wordAt_keep hm' hb0 (by decide) rfl s5, trivial⟩,
      bytesAt_keep hm' hb0 (by rw [length_rcBytes]; decide) (by rw [length_rcBytes]; rfl) hA.rc,
      fun p hp => (same_region hm' hwf hb0 (by decide) (by decide) p hp).trans (hA.same p hp),
      fun p h => hm'.kept hwf p (hA.kept p h)⟩
    · rw [hm'.regs .rax _ rfl]
      sym_simp
      rw [hv, BitVec.ofNat_add_ofNat]
      rfl
    · exact allOf_imp (fun p hp h => by
        rw [stAfter_succ m0 hi, lane_round _ _ (hl p hp), par_eq]
        exact h) hregs
    · exact allOf_imp (fun p hp h => by
        rw [stAfter_succ m0 hi, lane_round _ _ (hs p hp), par_eq]
        exact h) hslots
  · have hlab : Labels.label NativeRustcVmX64.Vm.KeccakF.label_1 = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakF.b2Offset) := hp.label NativeRustcVmX64.Vm.KeccakF.label_1_at
    simp only [PcOk] at hpc
    rw [hpc, hlab]
    sym_simp
    rw [hv, NativeRustcVmX64.Vm.KeccakF.b2_length]
    by_cases h : i + 1 = 24
    · obtain rfl : i = 23 := by omega
      rfl
    · have hne : BitVec.ofNat 64 (2 + i) + 1#64 ≠ 26#64 := by
        intro he
        have := congrArg BitVec.toNat he
        simp at this
        omega
      simp [hne, h]

end

end NativeRustcVmX64.KeccakF
