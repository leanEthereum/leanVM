module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Code.Vm.TStateSampleChallenges.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Sample
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Branch

/-!
# `verify_keccak` up to the first claim

The prologue and the grind (`stepEntry`), its branch (`stepGrind`), the segment and lane
challenges (`b3`, `b4`), the committed outputs' value (`b5`, its branch `b6`): at `b7` (`AtC`),
the segment at frame offset 96, the lanes at 112, the value's `Option<EW>` at 960, the model's run
the rest from the first claim (`afterCommitted`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak

@[expose] public section

/-- **At the first claim** (`b7`). -/
structure AtC [Labels] (a : DecArea) (s : TState) (cs : Array ColumnClaimW) (inst output : Array EW)
    (m0 m : MachineData) (s4 : TState) (seg lp : Array EW) (c : EW) : Prop where
  mid : Mid m0 m
  x19 : m.regs.getXReg .X19 = m0.regs.X4
  x28 : m.regs.getXReg .X28 = m0.regs.X3
  x29 : m.regs.getXReg .X29 = m0.regs.X7
  ts : TStateAt m.dmem (tA m0) a s4
  cls : NativeRustcVm.Layout.ClaimsWAt m.dmem (clA m0) cs
  segSz : seg.size = 1
  segv : NativeRustcVm.EWsAt m.dmem (loc m0 96) seg.toList
  lpSz : lp.size = 5
  lpv : NativeRustcVm.EWsAt m.dmem (loc m0 112) lp.toList
  cv : OptEWAt m.dmem (loc m0 960) (some c)
  run : run0 s inst output m0 =
    (afterCommitted m0.regs.X1.toNat inst (keccakFirstClaim inst seg lp output c) c).run s4

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW} {m0 : MachineData}

theorem frame_keep {d d' : Mem 64} {o n o' n' : Nat} (hn : Nums a inst m0) (hs : TKeep m0 o n d d')
    (hle : o' + n' ≤ 3360) (hap : o' + n' ≤ o ∨ o + n ≤ o') {A : BitVec 64} (hA : A = loc m0 o')
    {bs : List UInt8} (hl : bs.length = n') (hb : NativeRustcVm.BytesAt d A bs) :
    NativeRustcVm.BytesAt d' A bs := by
  subst hA
  have := hn.hN; have := hn.tS; have := m0.regs.SP.toNat_lt
  refine NativeRustcVm.Layout.BytesAt.of_same hb (same_num hs (by
    rw [loc_toNat hn.hN (by omega), hl]; omega) (fun q hq ↦ ?_)) le_rfl
  rw [loc_toNat hn.hN (by omega), hl]
  rcases hq with h1 | h1 | h1 <;> omega

omit [Host] in
theorem ews16 (xs : List EW) : (xs.flatMap NativeRustcVm.ewBytes).length = 16 * xs.length :=
  NativeRustcVm.length_ewsBytes xs

/-- **Up to the first claim.** -/
theorem stepFront (hp : Placed code k) (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hbl : Spec (Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (cont : ∀ m s4 seg lp c, AtC a s cs inst output m0 m s4 seg lp c →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b7Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b0Offset)⟩ := by
  have hrun0 : run0 s inst output m0 =
      (grind gBits >>= fun _ ↦ afterGrind m0.regs.X1.toNat inst output).run s := by
    unfold run0; rw [verifyKeccak_grind]
  refine stepEntry hp h hn hbl hgr fun m2 hmid2 h19 h28 h29 hx0 hnext hcl2 ↦ ?_
  cases hg : (grind gBits).run s with
  | none =>
    rw [hg] at hx0
    exact stepGrind (b := false) hp hn hmid2 hx0 (fun _ ↦ by rw [hrun0, run_bind_none hg])
      fun hf ↦ nomatch hf
  | some p =>
    obtain ⟨⟨⟩, s1⟩ := p
    rw [hg] at hx0
    have hts1 := hnext () s1 hg
    have hr1 : run0 s inst output m0 = (afterGrind m0.regs.X1.toNat inst output).run s1 := by
      rw [hrun0, run_bind_some hg]
    refine stepGrind (b := true) hp hn hmid2 hx0 (fun hf ↦ nomatch hf)
      fun _ m3 hmid3 hd3 hcs3 ↦ ?_
    rw [← hd3] at hts1 hcl2
    refine scStep h hn hsc (b3_in_code.trans hp.1 (by simp [b3])) run_b3 hmid3 hts1 hcl2 rfl
      (by decide) (by decide) (by decide) rfl rfl rfl (o := 96) (n := 1) (by decide) (by decide)
      (by decide) fun m4 seg s2 hsr hmid4 hts4 hcl4 hseg hk4 hcs4 ↦ ?_
    refine scStep h hn hsc (b4_in_code.trans hp.1 (by simp [b4])) run_b4 hmid4 hts4 hcl4 rfl
      (by decide) (by decide) (by decide) rfl rfl rfl (o := 112) (n := 5) (by decide) (by decide)
      (by decide) fun m5 lp s3 hlr hmid5 hts5 hcl5 hlp hk5 hcs5 ↦ ?_
    refine rsStep h hn hrs (b5_in_code.trans hp.1 (by simp [b5])) run_b5 hmid5 hts5 hcl5 rfl rfl
      (by decide) rfl rfl (o := 960) (by decide) (by decide)
      fun st6 m6 hm6 hv hnx hmid6 hcl6 hk6 hcs6 ↦ ?_
    have hss : seg.size = 1 := Bus.Gkr.sampleChallenges_size hsr
    have hls : lp.size = 5 := Bus.Gkr.sampleChallenges_size hlr
    have hr2 : run0 s inst output m0 = (afterLane m0.regs.X1.toNat inst output seg lp).run s3 := by
      rw [hr1, afterGrind_run hsr, afterSeg_run hlr]
    have hseg6 : NativeRustcVm.EWsAt m6.dmem (loc m0 96) seg.toList :=
      frame_keep (o' := 96) (n' := 16) hn hk6 (by omega) (by omega) rfl
        (by rw [ews16, Array.length_toList, hss])
        (frame_keep (o' := 96) (n' := 16) hn hk5 (by omega) (by omega) rfl
          (by rw [ews16, Array.length_toList, hss]) hseg)
    have hlp6 : NativeRustcVm.EWsAt m6.dmem (loc m0 112) lp.toList :=
      frame_keep (o' := 112) (n' := 80) hn hk6 (by omega) (by omega) rfl
        (by rw [ews16, Array.length_toList, hls]) hlp
    rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b3Offset + b3.length + b4.length + b5.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b6Offset from by
      rw [← b5_next, ← b4_next, ← b3_next]
      simp only [Nat.add_assoc]]
    refine failBranch hp hn (b6_in_code.trans hp.1 (by simp [b6])) run_b6 hmid6 rfl rfl
      (by decide) (by decide) (b := ((readScalar.run s3).map (·.1)).isSome)
      (cond8 (o := 960) (r := (readScalar.run s3).map (·.1)) hv) (fun hf ↦ ?_)
      fun ht m7 hmid7 hd7 hcs7 ↦ ?_
    · cases hrs3 : readScalar.run s3 with
      | none => rw [hr2, afterLane_none hrs3]
      | some q => rw [hrs3] at hf; cases hf
    · obtain ⟨⟨c, s4⟩, hrs3⟩ : ∃ q, readScalar.run s3 = some q := by
        cases hq : readScalar.run s3 with
        | none => rw [hq] at ht; cases ht
        | some q => exact ⟨q, rfl⟩
      rw [hrs3] at hv hnx
      refine cont m7 s4 seg lp c ⟨hmid7, ?_, ?_, ?_, ?_, ?_, hss, ?_, hls, ?_, ?_, ?_⟩
      · rw [hcs7 .X19 rfl, hcs6 .X19 rfl, Match.reg_eq (matchM hn hmid5.fr) hm6 (r := .X19) rfl rfl,
          hcs5 .X19 rfl, hcs4 .X19 rfl, hcs3 .X19 rfl, h19]
      · rw [hcs7 .X28 rfl, hcs6 .X28 rfl, Match.reg_eq (matchM hn hmid5.fr) hm6 (r := .X28) rfl rfl,
          hcs5 .X28 rfl, hcs4 .X28 rfl, hcs3 .X28 rfl, h28]
      · rw [hcs7 .X29 rfl, hcs6 .X29 rfl, Match.reg_eq (matchM hn hmid5.fr) hm6 (r := .X29) rfl rfl,
          hcs5 .X29 rfl, hcs4 .X29 rfl, hcs3 .X29 rfl, h29]
      · rw [hd7]; exact hnx (c, s4).1 s4 rfl
      · rw [hd7]; exact hcl6
      · rw [hd7]; exact hseg6
      · rw [hd7]; exact hlp6
      · rw [hd7]; exact hv
      · rw [hr2, afterLane_run hrs3]

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
