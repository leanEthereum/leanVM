module

public import NativeRustcVmArm.Code.Vm.KeccakF.Names
public import NativeRustcVmArm.Keccak.KeccakF.RoundLanes

/-!
# One turn of `keccak_f`'s round loop

`round_step`: from the loop head after `i < 24` rounds (`At m0 i`), the machine inevitably reaches
the loop invariant after `i + 1` rounds, back at the loop head (`.LKeccakF_1`) or, after the 24th,
at the epilogue. The loop body runs in a fresh environment of the machine at the head (region: the
frame; the counter's value the variable 0), computes the round (`body_lanes`, the lanes by
`lane_round`) with the round constant it loads from the frame's copy, and keeps the saved slots,
the round constants and memory outside the frame.
-/

namespace NativeRustcVmArm.KeccakF

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
  LeanVM.Parameters NativeRustcArm
open NativeRustcArm.KeccakF (WordAt wordAt_keep same_region load_of_wordAt allOf_imp)
open NativeRustcVmArm.Keccak

public section

theorem stAfter_succ (m0 : MachineData) {i : Nat} (hi : i < 24) :
    stAfter m0 (i + 1) = Keccak.round (stAfter m0 i) (keccakRC.getD i 0) :=
  roundsTo_succ _ hi

theorem rc_index (i : Nat) (hi : i < 24) :
    96 + (UnOp.apply (.memExtend { type := .UXTX, amount := .E0 }) .W64
      (BitVec.ofNat 64 (16 + 8 * i))).toNat = 112 + 8 * i := by
  simp [UnOp.apply, BitVec.apply_mem_extend, BitVec.unsigned]
  omega

variable [Host]

/-- **One round of the loop.** -/
theorem round_step {k : Nat} (hp : Placed Vm.KeccakF.code k) {m0 : MachineData}
    (hstk : StackOk m0 NativeRustcVmArm.keccakFStack) {i : Nat} (hi : i < 24) {m : MachineData}
    (hA : At m0 i m) :
    Eventually (step1 Host.exe) (fun st => At m0 (i + 1) st.data ∧
      st.pc = if i + 1 = 24 then Host.addrOf (k + NativeRustcVmArm.Vm.KeccakF.b3Offset) else Host.addrOf (k + NativeRustcVmArm.Vm.KeccakF.b2Offset))
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.KeccakF.b2Offset)⟩ := by
  have hk : Vm.KeccakF.b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.KeccakF.b2Offset) :=
    Vm.KeccakF.b2_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let env := Env.ofMachine m [(frame m0, 400)] fun _ => BitVec.ofNat 64 (16 + 8 * i)
  have hwf : env.WF :=
    Env.wf_of ⟨⟨fun j hj => hA.kept _ (hstk.2.2 j hj), frame_noWrap hstk⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm : Match env startBody m :=
    match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, trivial⟩
      (by rw [hA.sp]; simp [Sym.eval])
      ⟨hA.ctr, trivial⟩ trivial
      ⟨show (BitVec.ofNat 64 (16 + 8 * i)).toNat < 201 by simp; omega, trivial⟩ trivial
  have hb0 : env.regions[0]? = some (frame m0, 400) := rfl
  have hrcl : env.load 0 (96 + (UnOp.apply (.memExtend { type := .UXTX, amount := .E0 }) .W64
      (env.vars 0)).toNat) 8 = (keccakRC.getD i 0).toBitVec := by
    rw [show env.vars 0 = BitVec.ofNat 64 (16 + 8 * i) from rfl, rc_index i hi]
    exact load_rc_at hA.rc hi
  refine exec_then hk body hwf hm fun st hm' hpc => .done _ ⟨?_, ?_⟩
  · obtain ⟨hregs, hslots⟩ := body_lanes body hm' hb0 hA.regs
      (allOf_imp (fun p _ h => load_of_wordAt (r := 0) h) hA.slots) hrcl
    have hl : ∀ p ∈ laneRegs, p.2 < 25 := by decide
    have hs : ∀ p ∈ laneSlots, p.2 < 25 := by decide
    refine ⟨(Match.sp_eq hm hm' rfl ▸ hA.sp), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm'.regs .X9 _ rfl]
      sym_simp
      rw [show env.vars 0 = BitVec.ofNat 64 (16 + 8 * i) from rfl, BitVec.ofNat_add_ofNat]
      congr 1
    · exact allOf_imp (fun p hp h => by
        rw [stAfter_succ m0 hi, lane_round _ _ (hl p hp), par_eq]
        exact h) hregs
    · exact allOf_imp (fun p hp h => by
        rw [stAfter_succ m0 hi, lane_round _ _ (hs p hp), par_eq]
        exact h) hslots
    · have hsv := hA.saved
      simp only [AllOf, savedSlots] at hsv ⊢
      obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, -⟩ := hsv
      exact ⟨wordAt_keep hm' hb0 (by decide) rfl s0, wordAt_keep hm' hb0 (by decide) rfl s1,
        wordAt_keep hm' hb0 (by decide) rfl s2, wordAt_keep hm' hb0 (by decide) rfl s3,
        wordAt_keep hm' hb0 (by decide) rfl s4, wordAt_keep hm' hb0 (by decide) rfl s5,
        wordAt_keep hm' hb0 (by decide) rfl s6, wordAt_keep hm' hb0 (by decide) rfl s7,
        wordAt_keep hm' hb0 (by decide) rfl s8, wordAt_keep hm' hb0 (by decide) rfl s9,
        wordAt_keep hm' hb0 (by decide) rfl s10, wordAt_keep hm' hb0 (by decide) rfl s11,
        wordAt_keep hm' hb0 (by decide) rfl s12, trivial⟩
    · exact bytesAt_keep hm' hb0 (by rw [length_rcBytes]; decide)
        (by rw [length_rcBytes]; rfl) hA.rc
    · exact fun p hp => (same_region hm' hwf hb0 (by decide) p hp).trans (hA.same p hp)
    · exact fun p h => hm'.kept hwf p (hA.kept p h)
  · have hlab : Labels.label NativeRustcVmArm.Vm.KeccakF.label_1 = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakF.b2Offset) := hp.label (j := NativeRustcVmArm.Vm.KeccakF.b2Offset) NativeRustcVmArm.Vm.KeccakF.label_1_at
    simp only [PcOk] at hpc
    rw [hpc, hlab]
    sym_simp
    rw [show env.vars 0 = BitVec.ofNat 64 (16 + 8 * i) from rfl,
      Vm.KeccakF.b2_length, Vm.KeccakF.b2Length]
    by_cases h : i + 1 = 24
    · obtain rfl : i = 23 := by omega
      rfl
    · have hne : BitVec.ofNat 64 (16 + 8 * i) + 8#64 ≠ 208#64 := by
        intro he
        have := congrArg BitVec.toNat he
        simp at this
        omega
      simp [hne, h]

end

end NativeRustcVmArm.KeccakF
