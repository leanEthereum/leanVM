module

public import NativeRustcX64.Code.Common.KeccakF.Names

public import NativeRustcX64.KeccakF.RoundLanes

/-!
# One turn of `keccak_f`'s round loop (x86-64)

`round_step`: from the loop head after `i` rounds, with two rounds left, the machine reaches
the invariant after `i + 2` rounds, back at the loop head or at the epilogue after round 24.
The round-constant region is the current 16-byte subrange of the table; the indexed address
aliases its offset 8. The body computes both rounds, advances the saved counter, and keeps
the state pointer, pushed registers and memory outside the frame.
-/

namespace NativeRustcX64.KeccakF

open NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics LeanVM.Parameters

public section

theorem stAfter_succ (m0 : MachineData) {i : Nat} (hi : i < 24) :
    stAfter m0 (i + 1) = Keccak.round (stAfter m0 i) (keccakRC.getD i 0) :=
  roundsTo_succ _ hi

theorem length_rcBytes : rcBytes.length = 192 := by
  rw [show rcBytes = Native.Keccak.wordsBytes keccakRC from rfl,
    Native.Keccak.Proof.length_wordsBytes]
  rfl

section
variable [Labels]

/-- The round constants are outside every write made by either half. -/
theorem rcAt_of_same {m0 m : MachineData} (hpre : KeccakFPre m0)
    (hsame : SameOutside m0.dmem m.dmem (InRange (frame m0) keccakFStack)) :
    BytesAt m.dmem rcAddr rcBytes := by
  obtain ⟨hstk, ⟨hrc, hnw, hap⟩, -⟩ := hpre
  intro p hp
  rw [hsame _ ?_]
  · exact hrc p hp
  have hf := frame_noWrap hstk
  rw [length_rcBytes] at hp
  rw [inRange_iff (by unfold NoWrap at hf; omega), toNat_add_ofNat _ _ (by unfold NoWrap at hnw; omega)]
  unfold Apart at hap
  unfold frame
  simp only [keccakFStack] at hap ⊢
  omega

@[expose] def roundEnv (m0 m : MachineData) (i : Nat) : Env :=
  Env.ofMachine m [(frame m0, 296), (rcAddr + BitVec.ofNat 64 (8 * i), 16)]

theorem roundEnv_wf {m0 m : MachineData} {i : Nat} (hpre : KeccakFPre m0)
    (hi : i + 1 < 24) (hkept : Kept m0.dmem m.dmem)
    (hsame : SameOutside m0.dmem m.dmem (InRange (frame m0) keccakFStack)) :
    (roundEnv m0 m i).WF := by
  have hstk := hpre.1
  have hrc := rcAt_of_same hpre hsame
  have hnw := hpre.2.1.2.1
  have hap := hpre.2.1.2.2
  let rcBase := rcAddr + BitVec.ofNat 64 (8 * i)
  have hbase : rcBase.toNat = rcAddr.toNat + 8 * i :=
    toNat_add_ofNat _ _ (by unfold NoWrap at hnw; omega)
  have hnw' : NoWrap rcBase 16 := by
    unfold NoWrap at hnw ⊢
    rw [hbase]
    omega
  have hap' : Apart rcBase 16 (frame m0) 296 := by
    unfold Apart at hap ⊢
    rw [hbase]
    change rcAddr.toNat + 192 ≤ (frame m0).toNat ∨
      (frame m0).toNat + 296 ≤ rcAddr.toNat at hap
    rcases hap with h | h
    · left; omega
    · right; omega
  refine Env.wf_of ⟨⟨fun j hj => hkept _ (hstk.2.2 j hj), frame_noWrap hstk⟩,
    ⟨fun j hj => ?_, hnw'⟩, trivial⟩ (List.pairwise_pair.mpr hap'.symm)
  have hbyte := hrc (8 * i + j) (by rw [length_rcBytes]; omega)
  change (m.dmem.get? ((rcAddr + BitVec.ofNat 64 (8 * i)) + BitVec.ofNat 64 j)).isSome
  rw [addr_add, hbyte]
  rfl

end

variable [ElfHost]

theorem halves_placed {sec k : Nat} (hp : PlacedIn Common.KeccakF.code sec k) :
    (firstHalf ++ secondHalf).IsInfixAt (ElfHost.sectionProg sec) (k + Common.KeccakF.b1Offset) := by
  rw [firstHalf, secondHalf, List.take_append_drop]
  exact Common.KeccakF.b1_in_code.trans hp.1 (List.cons_ne_nil _ _)

omit [ElfHost] in
theorem second_next : Common.KeccakF.b1Offset + firstHalf.length + secondHalf.length =
    Common.KeccakF.b2Offset := by decide +kernel

/-- The first unrolled round ends at the intermediate lane layout. -/
theorem first_step {sec k : Nat} (hp : PlacedIn Common.KeccakF.code sec k) {m0 : MachineData}
    (hpre : KeccakFPre m0) {i : Nat} (hi : i + 1 < 24) {m : MachineData} (hA : At m0 i m) :
    Eventually (elfStep1 ElfHost.exe) (fun st => MidAt m0 (i + 1) st.data ∧
      st.pc = ElfHost.addrOf sec (k + (Common.KeccakF.b1Offset + firstHalf.length)))
      ⟨m, ElfHost.addrOf sec (k + Common.KeccakF.b1Offset)⟩ := by
  let env := roundEnv m0 m i
  have hwf : env.WF := roundEnv_wf hpre hi hA.kept hA.same
  have hb0 : env.regions[0]? = some (frame m0, 296) := rfl
  have hctr : env.load 0 176 8 = BitVec.ofNat 64 (8 * i + 8) := load_of_wordAt (r := 0) hA.ctr
  have hm : Match env startBody m := by
    refine match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨show rspOf m = _ from hA.rsp.trans rfl, trivial⟩ trivial trivial ⟨?_, trivial⟩
    sym_simp
    change env.load 0 176 8 + rcAddr = env.base 1 + 8#64
    rw [hctr]
    change BitVec.ofNat 64 (8 * i + 8) + rcAddr =
      (rcAddr + BitVec.ofNat 64 (8 * i)) + 8#64
    rw [BitVec.ofNat_add, BitVec.add_comm _ rcAddr, BitVec.add_assoc]
  have hrcl : env.load 1 0 8 = (keccakRC.getD i 0).toBitVec :=
    load_rc_at (rcAt_of_same hpre hA.same) (BitVec.add_zero _) (by omega)
  refine exec_then_elf (List.IsInfixAt.append (halves_placed hp)).1 firstBody hwf nofun hm
    fun st hm' hpc => .done _ ⟨?_, ?_⟩
  · have hslots₀ : AllOf (fun p : Nat × Nat =>
        env.load 0 p.1 8 = (Keccak.lane (stAfter m0 i) p.2).toBitVec) laneSlots :=
      allOf_imp (fun p _ h => load_of_wordAt (env := env) (r := 0) (off := p.1) h) hA.slots
    have hregs := first_regs firstBody hm' hb0 hA.regs hslots₀ hA.par hrcl
    have hslots := first_slots firstBody hm' hb0 hA.regs hslots₀ hA.par hrcl
    have hpar := first_par firstBody hm' hb0 hA.regs hslots₀ hA.par hrcl
    have hrot := first_rot_r9 firstBody hm' hb0 hA.regs hslots₀ hA.par hrcl
    have hl : ∀ p ∈ midLaneRegs, p.2 < 25 := by decide
    have hs : ∀ p ∈ midLaneSlots, p.2 < 25 := by decide
    have hc : ∀ p ∈ midParRegs, p.2 < 5 := by decide
    have hsv := hA.saved
    simp only [AllOf, savedSlots] at hsv
    obtain ⟨s0, s1, s2, s3, s4, s5, -⟩ := hsv
    refine ⟨(hm'.regs .rsp _ rfl).trans rfl, ?_, wordAt_keep hm' hb0 (by decide) rfl hA.ptr,
      ?_, ?_, ?_, ?_,
      ⟨wordAt_keep hm' hb0 (by decide) rfl s0, wordAt_keep hm' hb0 (by decide) rfl s1,
        wordAt_keep hm' hb0 (by decide) rfl s2, wordAt_keep hm' hb0 (by decide) rfl s3,
        wordAt_keep hm' hb0 (by decide) rfl s4, wordAt_keep hm' hb0 (by decide) rfl s5, trivial⟩,
      fun p hp => (same_region hm' hwf hb0 (by decide) (by decide) p hp).trans (hA.same p hp),
      fun p h => hm'.kept hwf p (hA.kept p h)⟩
    · simpa only [Nat.mul_add, Nat.mul_one] using
        wordAt_keep hm' hb0 (by decide) rfl hA.ctr
    · exact allOf_imp (fun p hp h => by
        rw [stAfter_succ m0 (by omega), lane_round _ _ (hl p hp)]
        exact h) hregs
    · exact allOf_imp (fun p hp h => by
        rw [stAfter_succ m0 (by omega), lane_round _ _ (hs p hp)]
        exact h) hslots
    · exact allOf_imp (fun p hp h => by
        rw [stAfter_succ m0 (by omega), par_round _ _ (hc p hp)]
        exact h) hpar
    · rw [stAfter_succ m0 (by omega), par_round _ _ (by decide : 3 < 5)]
      exact hrot
  · simpa only [PcOk, Nat.add_assoc] using hpc

/-- The second unrolled round returns to the loop-head layout. -/
theorem second_step {sec k : Nat} (hp : PlacedIn Common.KeccakF.code sec k) {m0 : MachineData}
    (hpre : KeccakFPre m0) {i : Nat} (hi : i + 1 < 24) {m : MachineData}
    (hA : MidAt m0 (i + 1) m) :
    Eventually (elfStep1 ElfHost.exe) (fun st => At m0 (i + 2) st.data ∧
      st.pc = if i + 2 = 24 then ElfHost.addrOf sec (k + Common.KeccakF.b2Offset)
        else ElfHost.addrOf sec (k + Common.KeccakF.b1Offset))
      ⟨m, ElfHost.addrOf sec (k + (Common.KeccakF.b1Offset + firstHalf.length))⟩ := by
  let env := roundEnv m0 m i
  have hwf : env.WF := roundEnv_wf hpre hi hA.kept hA.same
  have hb0 : env.regions[0]? = some (frame m0, 296) := rfl
  have hctr : env.load 0 176 8 = BitVec.ofNat 64 (8 * (i + 1)) :=
    load_of_wordAt (r := 0) hA.ctr
  have hm : Match env startMid m := by
    refine match_ofMachine ⟨rfl, rfl, trivial⟩
      ⟨show rspOf m = _ from hA.rsp.trans rfl, trivial⟩ trivial trivial ⟨?_, trivial⟩
    sym_simp
    change env.load 0 176 8 + rcAddr = env.base 1 + 8#64
    rw [hctr]
    change BitVec.ofNat 64 (8 * (i + 1)) + rcAddr =
      (rcAddr + BitVec.ofNat 64 (8 * i)) + 8#64
    rw [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add,
      BitVec.add_comm _ rcAddr, BitVec.add_assoc]
  have hrcl : env.load 1 8 8 = (keccakRC.getD (i + 1) 0).toBitVec := by
    apply load_rc_at (rcAt_of_same hpre hA.same) ?_ hi
    change (rcAddr + BitVec.ofNat 64 (8 * i)) + 8#64 = _
    rw [addr_add, Nat.mul_add]
  have hpsec : secondHalf.IsInfixAt (ElfHost.sectionProg sec)
      (k + (Common.KeccakF.b1Offset + firstHalf.length)) := by
    simpa only [Nat.add_assoc] using (List.IsInfixAt.append (halves_placed hp)).2
  refine exec_then_elf hpsec secondBody hwf nofun hm
    fun st hm' hpc => .done _ ⟨?_, ?_⟩
  · have hslots₀ : AllOf (fun p : Nat × Nat =>
        env.load 0 p.1 8 = (Keccak.lane (stAfter m0 (i + 1)) p.2).toBitVec) midLaneSlots :=
      allOf_imp (fun p _ h => load_of_wordAt (env := env) (r := 0) (off := p.1) h) hA.slots
    have hregs := second_regs secondBody hm' hb0 hA.regs hslots₀ hA.par hrcl hA.rot
    have hslots := second_slots secondBody hm' hb0 hA.regs hslots₀ hA.par hrcl hA.rot
    have hpar := second_par secondBody hm' hb0 hA.regs hslots₀ hA.par hrcl hA.rot
    have hl : ∀ p ∈ laneRegs, p.2 < 25 := by decide
    have hs : ∀ p ∈ laneSlots, p.2 < 25 := by decide
    have hc : ∀ p ∈ parRegs, p.2 < 5 := by decide
    have hsv := hA.saved
    simp only [AllOf, savedSlots] at hsv
    obtain ⟨s0, s1, s2, s3, s4, s5, -⟩ := hsv
    refine ⟨(hm'.regs .rsp _ rfl).trans rfl, ?_, wordAt_keep hm' hb0 (by decide) rfl hA.ptr,
      ?_, ?_, ?_,
      ⟨wordAt_keep hm' hb0 (by decide) rfl s0, wordAt_keep hm' hb0 (by decide) rfl s1,
        wordAt_keep hm' hb0 (by decide) rfl s2, wordAt_keep hm' hb0 (by decide) rfl s3,
        wordAt_keep hm' hb0 (by decide) rfl s4, wordAt_keep hm' hb0 (by decide) rfl s5, trivial⟩,
      fun p hp => (same_region hm' hwf hb0 (by decide) (by decide) p hp).trans (hA.same p hp),
      fun p h => hm'.kept hwf p (hA.kept p h)⟩
    · refine wordAt_of_eq (wordAt_write hm' hb0 (by decide) rfl) ?_
      sym_simp
      rw [hctr, BitVec.ofNat_add_ofNat]
      congr 1
      omega
    · exact allOf_imp (fun p hp h => by
        rw [show i + 2 = (i + 1) + 1 by omega, stAfter_succ m0 hi, lane_round _ _ (hl p hp)]
        exact h) hregs
    · exact allOf_imp (fun p hp h => by
        rw [show i + 2 = (i + 1) + 1 by omega, stAfter_succ m0 hi, lane_round _ _ (hs p hp)]
        exact h) hslots
    · exact allOf_imp (fun p hp h => by
        rw [show i + 2 = (i + 1) + 1 by omega, stAfter_succ m0 hi, par_round _ _ (hc p hp)]
        exact h) hpar
  · have hlab : Labels.label Common.KeccakF.label_1 =
        ElfHost.addrOf sec (k + Common.KeccakF.b1Offset) :=
      hp.label Common.KeccakF.label_1_at
    simp only [PcOk] at hpc
    rw [hpc, hlab]
    sym_simp
    rw [hctr, Nat.add_assoc, second_next]
    by_cases h : i + 2 = 24
    · obtain rfl : i = 22 := by omega
      rfl
    · have hne : 16#64 + BitVec.ofNat 64 (8 * (i + 1)) ≠ 200#64 := by
        intro he
        have := congrArg BitVec.toNat he
        simp at this
        omega
      have hb : (16#64 + BitVec.ofNat 64 (8 * (i + 1)) == 200#64) = false := beq_false_of_ne hne
      simp only [hb, h, Bool.not_false, ↓reduceIte]

/-- **One pair of rounds of the loop.** -/
theorem round_step {sec k : Nat} (hp : PlacedIn Common.KeccakF.code sec k) {m0 : MachineData}
    (hpre : KeccakFPre m0) {i : Nat} (hi : i + 1 < 24) {m : MachineData} (hA : At m0 i m) :
    Eventually (elfStep1 ElfHost.exe) (fun st => At m0 (i + 2) st.data ∧
      st.pc = if i + 2 = 24 then ElfHost.addrOf sec (k + Common.KeccakF.b2Offset)
        else ElfHost.addrOf sec (k + Common.KeccakF.b1Offset))
      ⟨m, ElfHost.addrOf sec (k + Common.KeccakF.b1Offset)⟩ := by
  refine Eventually.bind_elf (first_step hp hpre hi hA) fun st ⟨hmid, hpc⟩ => ?_
  obtain ⟨m', pc⟩ := st
  simp only at hpc
  subst hpc
  exact second_step hp hpre hi hmid

end

end NativeRustcX64.KeccakF
