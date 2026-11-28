module

public import NativeRustcArm.Code.Common.KeccakF.Names

public import NativeRustcArm.KeccakF.RoundLanes

/-!
# One turn of `keccak_f`'s round loop

`round_step`: from the loop head after `i < 24` rounds (`At m0 i`), the machine inevitably reaches
the loop invariant after `i + 1` rounds, back at the loop head (`.LKeccakF_1`) or, after the 24th,
at the epilogue. The loop body runs in a fresh environment of the machine at the head (regions:
the frame and the round constants, the counter's value the variable 0), computes the round
(`body_lanes`, the lanes by `lane_round`, the parities by `par_round`), keeps the saved slots,
X29 and memory outside the frame.
-/

namespace NativeRustcArm.KeccakF

open NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics LeanVM.Parameters NativeRustcArm

public section

theorem stAfter_succ (m0 : MachineData) {i : Nat} (hi : i < 24) :
    stAfter m0 (i + 1) = Keccak.round (stAfter m0 i) (keccakRC.getD i 0) :=
  roundsTo_succ _ hi

theorem rc_offset (i : Nat) (hi : i < 24) :
    0 + (BitVec.ofInt 64 ((BitVec.ofNat 64 (8 * i)).apply_mem_extend
      { type := .UXTX, amount := .E0 })).toNat = 8 * i := by
  simp [BitVec.apply_mem_extend, BitVec.unsigned]
  omega

section
variable [Labels]

/-- At the loop head, the round constants are the entry's. -/
theorem rcAt_of_at {m0 m : MachineData} {i : Nat} (hpre : KeccakFPre m0) (hA : At m0 i m) :
    BytesAt m.dmem rcAddr rcBytes := by
  obtain ⟨hstk, ⟨hrc, hnw, hap⟩, -⟩ := hpre
  intro p hp
  have hlen : rcBytes.length = 192 := by
    rw [show rcBytes = Native.Keccak.wordsBytes keccakRC from rfl,
      Native.Keccak.Proof.length_wordsBytes]
    rfl
  rw [hA.same _ ?_]
  · exact hrc p hp
  have hf := frame_noWrap hstk
  rw [inRange_iff hf, toNat_add_ofNat _ _ (by unfold NoWrap at hnw; omega)]
  unfold Apart at hap
  unfold frame
  simp only [keccakFStack] at hap ⊢
  omega

end

variable [Host]

/-- **One round of the loop.** -/
theorem round_step {k : Nat} (hp : Placed Common.KeccakF.code k) {m0 : MachineData}
    (hpre : KeccakFPre m0) {i : Nat} (hi : i < 24) {m : MachineData} (hA : At m0 i m) :
    Eventually (step1 Host.exe) (fun st => At m0 (i + 1) st.data ∧
      st.pc = if i + 1 = 24 then Host.addrOf (k + NativeRustcArm.Common.KeccakF.b2Offset) else Host.addrOf (k + NativeRustcArm.Common.KeccakF.b1Offset))
      ⟨m, Host.addrOf (k + NativeRustcArm.Common.KeccakF.b1Offset)⟩ := by
  have hstk := hpre.1
  have hrc := rcAt_of_at hpre hA
  have hnw := hpre.2.1.2.1
  have hap := hpre.2.1.2.2
  have hk : Common.KeccakF.b1.IsInfixAt Host.prog (k + NativeRustcArm.Common.KeccakF.b1Offset) :=
    Common.KeccakF.b1_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let env := Env.ofMachine m [(frame m0, 192), (rcAddr, 192)] fun _ => BitVec.ofNat 64 (8 * i)
  have hwf : env.WF := by
    refine Env.wf_of ⟨⟨fun j hj => hA.kept _ (hstk.2.2 j hj), frame_noWrap hstk⟩,
      ⟨fun j hj => ?_, hnw⟩, trivial⟩ (List.pairwise_pair.mpr hap.symm)
    have := hrc j (by
      rw [show rcBytes = Native.Keccak.wordsBytes keccakRC from rfl,
        Native.Keccak.Proof.length_wordsBytes]
      exact hj)
    show (m.dmem.get? _).isSome
    rw [this]
    rfl
  have hm : Match env startBody m :=
    match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, rfl, fun h => absurd h (by decide), trivial⟩
      (by rw [hA.sp]; simp [Sym.eval, Env.base])
      ⟨hA.ctr, trivial⟩ ⟨rfl, trivial⟩ ⟨show (BitVec.ofNat 64 (8 * i)).toNat < 185 by simp; omega, trivial⟩ trivial
  have hb0 : env.regions[0]? = some (frame m0, 192) := rfl
  have hrcl : env.load 1 (0 + (BitVec.ofInt 64 ((env.vars 0).apply_mem_extend
      { type := .UXTX, amount := .E0 })).toNat) 8 = (keccakRC.getD i 0).toBitVec := by
    rw [show env.vars 0 = BitVec.ofNat 64 (8 * i) from rfl, rc_offset i hi]
    exact load_rc hrc hi
  refine exec_then hk body hwf hm fun st hm' hpc => .done _ ⟨?_, ?_⟩
  · obtain ⟨hregs, hslots, hpar⟩ := body_lanes body hm' hb0 hA.regs
      (allOf_imp (fun p _ h => load_of_wordAt (r := 0) h) hA.slots) hA.par hrcl
    have hl : ∀ p ∈ laneRegs, p.2 < 25 := by decide
    have hs : ∀ p ∈ laneSlots, p.2 < 25 := by decide
    have hc : ∀ p ∈ parRegs, p.2 < 5 := by decide
    refine ⟨(Match.sp_eq hm hm' rfl ▸ hA.sp), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm'.regs .X17 _ rfl]
      sym_simp
      rw [show env.vars 0 = BitVec.ofNat 64 (8 * i) from rfl, BitVec.ofNat_add_ofNat]
      congr 1
    · exact allOf_imp (fun p hp h => by
        rw [stAfter_succ m0 hi, lane_round _ _ (hl p hp)]
        exact h) hregs
    · exact allOf_imp (fun p hp h => by
        rw [stAfter_succ m0 hi, lane_round _ _ (hs p hp)]
        exact h) hslots
    · exact allOf_imp (fun p hp h => by
        rw [stAfter_succ m0 hi, par_round _ _ (hc p hp)]
        exact h) hpar
    · have hsv := hA.saved
      simp only [AllOf, savedSlots] at hsv ⊢
      obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, -⟩ := hsv
      exact ⟨wordAt_keep hm' hb0 (by decide) rfl s0, wordAt_keep hm' hb0 (by decide) rfl s1,
        wordAt_keep hm' hb0 (by decide) rfl s2, wordAt_keep hm' hb0 (by decide) rfl s3,
        wordAt_keep hm' hb0 (by decide) rfl s4, wordAt_keep hm' hb0 (by decide) rfl s5,
        wordAt_keep hm' hb0 (by decide) rfl s6, wordAt_keep hm' hb0 (by decide) rfl s7,
        wordAt_keep hm' hb0 (by decide) rfl s8, wordAt_keep hm' hb0 (by decide) rfl s9,
        wordAt_keep hm' hb0 (by decide) rfl s10, wordAt_keep hm' hb0 (by decide) rfl s11, trivial⟩
    · exact (Match.reg_eq hm hm' rfl rfl).trans hA.x29
    · exact fun p hp => (same_region hm' hwf hb0 (by decide) p hp).trans (hA.same p hp)
    · exact fun p h => hm'.kept hwf p (hA.kept p h)
  · have hlab : Labels.label NativeRustcArm.Common.KeccakF.label_1 = Host.addrOf (k + NativeRustcArm.Common.KeccakF.b1Offset) := hp.label NativeRustcArm.Common.KeccakF.label_1_at
    simp only [PcOk] at hpc
    rw [hpc, hlab]
    sym_simp
    rw [show env.vars 0 = BitVec.ofNat 64 (8 * i) from rfl,
      Nat.add_assoc, NativeRustcArm.Common.KeccakF.b1_next]
    by_cases h : i + 1 = 24
    · obtain rfl : i = 23 := by omega
      rfl
    · have hne : BitVec.ofNat 64 (8 * i) + 8#64 ≠ 192#64 := by
        intro he
        have := congrArg BitVec.toNat he
        simp at this
        omega
      simp [hne, h]

end

end NativeRustcArm.KeccakF
