module

public import NativeRustcVmArm.Code.Vm.Seed.Names
public import NativeRustcVmArm.Top.Verify.Basic

/-!
# `verify`: the seed

From the entry, the prologue (`b0`) saves the callee-saved registers in the frame's last 64
bytes and `seed` writes the sponge's lanes at the `TState`'s start: `stageA`, to `SA`.
-/

namespace NativeRustcVmArm.Top.Verify

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Verify NativeVm.Model
open NativeRustcVm.Transcript
open NativeRustcVm (WordsAt Region wordsOf wordOf)

public section

variable [Host] {k : Nat}

theorem stageA (hp : Placed code k) (hseed : Spec (Labels.label NativeRustcVmArm.Vm.Seed.entryLabel) SeedPre SeedPost)
    {a : DecArea} {stream : Array EW} {openings : Array (Array OpeningW)} {m0 : MachineData}
    (hpre : VerifyPre a stream openings m0) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Verify.b1Offset) ∧ SA m0 st.data)
      ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.Verify.b0Offset)⟩ := by
  have g := geo_of hpre
  obtain ⟨⟨-, -, hmap⟩, hrod, -, -, -, ⟨hbcM, -⟩, ⟨hpubM, -⟩, -, -, -, -, -, -⟩ := hpre
  have hs := g.s
  have hal := g.al
  have hF := g.F
  have hT := g.T
  have hsb0 := g.sb
  have hn32 := g.n32
  have hpubN := g.pubN
  have hbcN := g.bcN
  have hS := verifyStack_eq
  have hSS : seedStack = 928 := rfl
  have hsl := m0.regs.SP.toBitVec.isLt
  have e1 : m0.regs.X1.toNat = m0.regs.X1.toBitVec.toNat := rfl
  set F := frameOf m0 with hFdef
  have hFm : Mapped m0.dmem F 832 :=
    Mapped.within hmap (by rw [hsb0]; omega) (by rw [hsb0, hF]; omega) (by rw [hsb0, hF]; omega)
  -- The prologue.
  have hwf0 : (Env.ofMachine m0 [(F, 832)]).WF :=
    Env.wf_of ⟨⟨hFm, show F.toNat + 832 ≤ 2 ^ 64 by omega⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm0 : Match (Env.ofMachine m0 [(F, 832)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ show F.toNat % 16 = 0 by omega, trivial⟩
      (show m0.regs.SP.toBitVec = F + BitVec.ofInt 64 832 by
        rw [show BitVec.ofInt 64 832 = BitVec.ofNat 64 832 from rfl, hFdef, frameOf,
          BitVec.sub_add_cancel])
      trivial trivial trivial trivial
  refine exec_then (hb0 hp) run_b0 hwf0 hm0 fun st1 hm1 hpc1 ↦ ?_
  have hB1 : Body m0 832 slots (InStack m0 verifyStack) st1.data := by
    refine ⟨?_, fun p hp ↦ ?_, fun r hr hn ↦ ?_, fun q hq ↦ ?_, hm1.kept hwf0⟩
    · rw [hm1.sp]; show F + BitVec.ofInt 64 0 = F; simp
    · have hw := b0_slots p hp
      rw [after_eq run_b0] at hw
      have hsl' : p.1 + 8 ≤ 832 := by
        simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with h | h | h | h | h | h | h <;> rw [h] <;> decide
      exact hm1.bytesAt_write (r := 0) (b := F) (sz := 832) rfl hsl' hw
    · have hr' := nonslot hr hn
      have h := b0_regs r hr'
      rw [after_eq run_b0] at h
      exact UInt64.toBitVec_inj.mp (hm1.regs r _ h)
    · refine hm1.get?_mem0 hwf0 fun hw ↦ hq ?_
      have hb0m := b0_mem
      rw [after_eq run_b0] at hb0m
      have := written_sub (env := Env.ofMachine m0 [(F, 832)]) (r := 0) rfl hb0m hw
      unfold InStack
      omega
  have hsp1 : st1.data.regs.SP.toBitVec = F := hB1.sp
  have hX0_1 : st1.data.regs.X0.toBitVec = tOf m0 := hm1.regs .X0 _ rfl
  have hX1_1 : st1.data.regs.X1 = m0.regs.X0 := UInt64.toBitVec_inj.mp (hm1.regs .X1 _ rfl)
  have hX2_1 : st1.data.regs.X2 = m0.regs.X1 := UInt64.toBitVec_inj.mp (hm1.regs .X2 _ rfl)
  have hX3_1 : st1.data.regs.X3 = m0.regs.X2 := UInt64.toBitVec_inj.mp (hm1.regs .X3 _ rfl)
  have hX19_1 : st1.data.regs.X19 = m0.regs.X3 := UInt64.toBitVec_inj.mp (hm1.regs .X19 _ rfl)
  have hX20_1 : st1.data.regs.X20 = m0.regs.X4 := UInt64.toBitVec_inj.mp (hm1.regs .X20 _ rfl)
  have hX21_1 : st1.data.regs.X21 = m0.regs.X2 := UInt64.toBitVec_inj.mp (hm1.regs .X21 _ rfl)
  have hX22_1 : st1.data.regs.X22 = m0.regs.X1 := UInt64.toBitVec_inj.mp (hm1.regs .X22 _ rfl)
  have hX23_1 : st1.data.regs.X23 = m0.regs.X0 := UInt64.toBitVec_inj.mp (hm1.regs .X23 _ rfl)
  have hsb1 : (stackBelow st1.data seedStack).toNat = m0.regs.SP.toBitVec.toNat - 1760 := by
    show (st1.data.regs.SP.toBitVec - BitVec.ofNat 64 928).toNat = _
    rw [hsp1, toNat_subAddr (by rw [hF]; omega), hF]; omega
  have hsb1' : (st1.data.regs.SP.toBitVec - BitVec.ofNat 64 seedStack).toNat =
      m0.regs.SP.toBitVec.toNat - 1760 := hsb1
  have hbc : WordsAt st1.data.dmem m0.regs.X0.toBitVec (bcOf m0) := by
    by_cases hn0 : m0.regs.X1.toBitVec.toNat = 0
    · rw [show bcOf m0 = [] from List.eq_nil_of_length_eq_zero ((length_bcOf m0).trans hn0)]
      exact NativeRustcVm.wordsAt_nil _ _
    · have hap := g.bc (by omega)
      exact wordsAt_keep (wordsAt_bcOf hbcM) hB1.same (by rw [length_bcOf]; omega)
        fun q hq ↦ by unfold InStack at hq; rw [length_bcOf]; omega
  have hpub : WordsAt st1.data.dmem m0.regs.X2.toBitVec (pubOf m0).toList := by
    have hap := g.pub
    exact wordsAt_keep (wordsAt_pubOf hpubM) hB1.same (by rw [Vector.length_toList]; omega)
      fun q hq ↦ by unfold InStack at hq; rw [Vector.length_toList]; omega
  -- `seed`.
  have hpre1 : SeedPre st1.data := by
    refine ⟨⟨?_, ?_, ?_⟩, RodataAt.rcAt (rodataAt_body hrod hB1 (by omega) hsp1 (by
      rw [hS]; decide)), ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · show st1.data.regs.SP.toBitVec.toNat % 16 = 0
      rw [hsp1, hF]; omega
    · show 928 ≤ st1.data.regs.SP.toBitVec.toNat
      rw [hsp1, hF]; omega
    · exact Mapped.kept (Mapped.within hmap (by omega) (by omega) (by omega)) hB1.kept
    · show 9 + 8 * st1.data.regs.X2.toNat < 2 ^ 32
      rw [hX2_1]; exact hn32
    · show Mapped st1.data.dmem st1.data.regs.X1.toBitVec (8 * st1.data.regs.X2.toNat)
      rw [hX1_1, hX2_1]; exact Mapped.kept hbcM hB1.kept
    · show st1.data.regs.X1.toBitVec.toNat + 8 * st1.data.regs.X2.toNat ≤ 2 ^ 64
      rw [hX1_1, hX2_1]; exact hbcN
    · show Mapped st1.data.dmem st1.data.regs.X3.toBitVec 32
      rw [hX3_1]; exact Mapped.kept hpubM hB1.kept
    · show st1.data.regs.X3.toBitVec.toNat + 32 ≤ 2 ^ 64
      rw [hX3_1]; exact hpubN
    · show Mapped st1.data.dmem st1.data.regs.X0.toBitVec 200
      rw [hX0_1]
      exact Mapped.kept (Mapped.within hFm (by omega) (by unfold tOf at hT ⊢; omega)
        (by unfold tOf at hT ⊢; omega)) hB1.kept
    · show st1.data.regs.X0.toBitVec.toNat + 200 ≤ 2 ^ 64
      rw [hX0_1]; omega
    · refine List.pairwise_pair.mpr ?_
      show NativeRustcVm.Apart (stackBelow st1.data seedStack) seedStack st1.data.regs.X3.toBitVec 32
      have := g.pub
      unfold NativeRustcVm.Apart
      rw [hX3_1, hsb1]; omega
    · refine List.pairwise_pair.mpr ?_
      show NativeRustcVm.Apart (stackBelow st1.data seedStack) seedStack
        st1.data.regs.X0.toBitVec 200
      unfold NativeRustcVm.Apart
      rw [hX0_1, hsb1]; omega
    · intro hn0
      show _ ∨ _
      have hap := g.bc (by rw [← hX2_1]; exact hn0)
      rw [hX1_1, hX2_1]
      omega
  refine call_then hpc1 hseed hpre1 fun st2 hpc2 hpost2 ↦ ?_
  obtain ⟨hseed2, hsame2, hsaved2⟩ := hpost2
  have hB2 : Body m0 832 slots (InStack m0 verifyStack) st2.data := by
    refine hB1.call slotsIn
      (by show 832 ≤ m0.regs.SP.toBitVec.toNat; omega) hsame2 hsaved2 fun q hq ↦ ?_
    rcases hq with hq | hq
    · rw [hX0_1] at hq
      change InRange (tOf m0) 200 q at hq
      rw [inRange_nat (by omega)] at hq
      unfold InStack; omega
    · change InRange (st1.data.regs.SP.toBitVec - BitVec.ofNat 64 928) 928 q at hq
      rw [inRange_below (by rw [hsp1, hF]; omega), hsp1, hF] at hq
      unfold InStack; omega
  have hsd := hseed2 (bcOf m0) (by rw [length_bcOf, hX2_1]) (by rw [hX1_1]; exact hbc)
    (pubOf m0) (by rw [hX3_1]; exact hpub)
  rw [hX0_1] at hsd
  rw [show k + NativeRustcVmArm.Vm.Verify.b0Offset + b0.length = k + NativeRustcVmArm.Vm.Verify.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.Verify.b0_next]] at hpc2
  refine Eventually.done _ ⟨hpc2, hB2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hsaved2.1 .X19 rfl).trans hX19_1
  · exact (hsaved2.1 .X20 rfl).trans hX20_1
  · exact (hsaved2.1 .X21 rfl).trans hX21_1
  · exact (hsaved2.1 .X22 rfl).trans hX22_1
  · exact (hsaved2.1 .X23 rfl).trans hX23_1
  · exact hsd

end

end NativeRustcVmArm.Top.Verify
