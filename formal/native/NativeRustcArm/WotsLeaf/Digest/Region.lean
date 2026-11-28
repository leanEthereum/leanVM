module

public import NativeRustcArm.WotsLeaf.Digest.Prologue
public import NativeRustcArm.WotsLeaf.Epilogue

/-!
# Region 1: the message digest

From the entry to `b6` (directive 48): the prologue (`b0`), `memset` of the hasher at 32,
`update` with `P`, the address at 1776, the message, the randomizer (`b1 .. b4`), `finalize` into
1776 (`b5`). Exit: `AtCheck`, the digest's 32 bytes at 1776.
-/

namespace NativeRustcArm.WotsLeafProof

open NativeRustc NativeRustc.Keccak NativeRustc.Xmss NativeRustcArm.Sym LeanVM.Protocol.KeccakHash
open NativeRustcArm.Xmss.WotsLeaf Digest

@[expose] public section

/-- The slots at `b6`: `e`, `hi`, the digest. -/
def Run.checkSlots (r : Run) : List Slot := r.prologueSlots ++ [(1776, 32, r.digest32)]

/-- **At `b6`**: the digest's 32 bytes at 1776, `e` and `hi` at 24 and 28; X19 `out`, X20 `P`'s
address, X22 the chain values'. -/
def Run.AtCheck (r : Run) (m : MachineData) : Prop :=
  Keep r r.checkSlots m ∧ Run.RegIs m .X19 r.out ∧ Run.RegIs m .X20 r.m0.regs.X1.toBitVec ∧
    Run.RegIs m .X22 r.m0.regs.X7.toBitVec

end

public section

theorem length_hashBytes (d : List UInt8) : (hashBytes d).length = 32 := by
  rw [hashBytes, show digestBytes (keccak256 d) = Native.Keccak.wordsBytes (keccak256 d).toList
    from rfl, Native.Keccak.Proof.length_wordsBytes]
  simp

theorem length_digest32 (r : Run) : r.digest32.length = 32 := length_hashBytes _

/-- The callee-saved registers the digest's blocks keep. -/
theorem regs_of_saved {m m' : MachineData} (hS : Saved m m') {a b c d e f : BitVec 64}
    (h : Run.RegIs m .X19 a ∧ Run.RegIs m .X20 b ∧ Run.RegIs m .X22 c ∧ Run.RegIs m .X23 d ∧
      Run.RegIs m .X24 e ∧ Run.RegIs m .X25 f) :
    Run.RegIs m' .X19 a ∧ Run.RegIs m' .X20 b ∧ Run.RegIs m' .X22 c ∧ Run.RegIs m' .X23 d ∧
      Run.RegIs m' .X24 e ∧ Run.RegIs m' .X25 f :=
  ⟨RegIs.of_saved hS rfl h.1, RegIs.of_saved hS rfl h.2.1, RegIs.of_saved hS rfl h.2.2.1,
    RegIs.of_saved hS rfl h.2.2.2.1, RegIs.of_saved hS rfl h.2.2.2.2.1,
    RegIs.of_saved hS rfl h.2.2.2.2.2⟩

/-- The registers a block of the frame does not set. -/
theorem regs_of_block [Labels] {r : Run} {m m' : MachineData} {S : SState}
    (hm : Match (r.env m) S m') (h19 : S.reg .X19 = some (.reg .X19))
    (h20 : S.reg .X20 = some (.reg .X20)) (h22 : S.reg .X22 = some (.reg .X22))
    (h23 : S.reg .X23 = some (.reg .X23)) (h24 : S.reg .X24 = some (.reg .X24))
    (h25 : S.reg .X25 = some (.reg .X25)) {a b c d e f : BitVec 64}
    (h : Run.RegIs m .X19 a ∧ Run.RegIs m .X20 b ∧ Run.RegIs m .X22 c ∧ Run.RegIs m .X23 d ∧
      Run.RegIs m .X24 e ∧ Run.RegIs m .X25 f) :
    Run.RegIs m' .X19 a ∧ Run.RegIs m' .X20 b ∧ Run.RegIs m' .X22 c ∧ Run.RegIs m' .X23 d ∧
      Run.RegIs m' .X24 e ∧ Run.RegIs m' .X25 f :=
  ⟨regIs_reg hm h19 h.1, regIs_reg hm h20 h.2.1, regIs_reg hm h22 h.2.2.1,
    regIs_reg hm h23 h.2.2.2.1, regIs_reg hm h24 h.2.2.2.2.1, regIs_reg hm h25 h.2.2.2.2.2⟩

/-- A register a block sets to another's atom. -/
theorem regIs_of_reg [Labels] {r : Run} {m m' : MachineData} {S : SState} (hm : Match (r.env m) S m')
    {y x : XReg} (h : S.reg y = some (.reg x)) {v : BitVec 64} (hv : Run.RegIs m x v) :
    Run.RegIs m' y v := by
  unfold Run.RegIs at *
  rw [hm.regs y _ h]
  exact hv

variable [NativeRustcArm.Host]

/-- **Region 1, the message digest.** -/
theorem digest_region : RegionSpec (fun r m ↦ m = r.m0) NativeRustcArm.Xmss.WotsLeaf.b0Offset fun r st ↦ st.pc = r.pc NativeRustcArm.Xmss.WotsLeaf.b6Offset ∧
    r.AtCheck st.data := by
  intro r hp hc hpre m hm0
  subst hm0
  -- The prologue.
  have hwf0 : (r.env r.m0).WF := by
    have h := r.frame_mapped_kept hpre (m := r.m0) (fun _ h ↦ h) (a := 0) (n := 2752) (by decide)
    rw [Run.off_zero] at h
    exact Env.wf_of ⟨h, trivial⟩ (List.pairwise_singleton _ _)
  have hm0 : Match (r.env r.m0) entryS r.m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ r.base_aligned hpre, trivial⟩
      (by show r.m0.regs.SP.toBitVec = r.base + BitVec.ofInt 64 2752; rw [r.base_add_frame hpre])
      trivial trivial trivial trivial
  refine blk r hp b0_in_code (List.cons_ne_nil _ _) run_b0 hwf0 hm0 fun st hm1 hpc ↦ ?_
  have hF1 := frame_of_entry hpre hm1 hwf0 rfl rfl (by decide) (by decide)
  have hS1 := prologue_slots hm1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hK1 : Keep r (r.prologueSlots ++ [(1776, 16, r.addr 12 0)]) st.data := ⟨hF1, hS1⟩
  have hR1 : Run.RegIs st.data .X19 r.out ∧ Run.RegIs st.data .X20 r.m0.regs.X1.toBitVec ∧
      Run.RegIs st.data .X22 r.m0.regs.X7.toBitVec ∧ Run.RegIs st.data .X23 r.m0.regs.X6.toBitVec ∧
      Run.RegIs st.data .X24 r.m0.regs.X5.toBitVec ∧ Run.RegIs st.data .X25 r.m0.regs.X4.toBitVec :=
    ⟨hm1.regs .X19 _ rfl, hm1.regs .X20 _ rfl, hm1.regs .X22 _ rfl, hm1.regs .X23 _ rfl,
      hm1.regs .X24 _ rfl, hm1.regs .X25 _ rfl⟩
  refine callAt hpc hc.2.1 ?_
  obtain ⟨hpre1, hpost1⟩ := memsetFrame hpre hK1 (regIs_ptr hm1 rfl) (x1_zero hm1 rfl)
    (x2_eq hm1 rfl (by decide)) (by decide) rfl
  refine ⟨hpre1, fun m2 hQ2 ↦ ?_⟩
  obtain ⟨hK2, hS2, -, hB2⟩ := hpost1 m2 hQ2
  have hH2 : HasherAt r m2 32 [] := ⟨_, hB2, holds_new⟩
  have hR2 := regs_of_saved hS2 hR1
  -- `update` with `P`.
  refine frameCall r hp hpre b1_in_code (List.cons_ne_nil _ _) run_b1 (by decide) rfl hK2
    trivial hc.2.2.1 fun m3 hm3 hK3 _ ↦ ?_
  have hR3 := regs_of_block hm3 rfl rfl rfl rfl rfl rfl hR2
  obtain ⟨hpre3, hpost3⟩ := updateInput hpre hK3 (regIs_ptr hm3 rfl) (regIs_of_reg hm3 rfl hR2.2.1)
    (x2_eq hm3 rfl (by decide)) (r.pre_pp hpre) (by decide) rfl
    (hH2.keepB (kb_of_block hpre hm3 (r.frame_wf hpre hK2.1 _)) (by decide) (by decide))
  refine ⟨hpre3, fun m4 hQ4 ↦ ?_⟩
  obtain ⟨hK4, hS4, -, hH4⟩ := hpost3 m4 hQ4
  have hR4 := regs_of_saved hS4 hR3
  -- `update` with the address.
  refine frameCall r hp hpre b2_in_code (List.cons_ne_nil _ _) run_b2 (by decide) rfl hK4
    trivial hc.2.2.1 fun m5 hm5 hK5 hkb5 ↦ ?_
  have hR5 := regs_of_block hm5 rfl rfl rfl rfl rfl rfl hR4
  have hA5 : BytesAt m5.dmem (r.off 1776) (r.addr 12 0) := hK5.2.2.2.1.2.2
  obtain ⟨hpre5, hpost5⟩ := updateFrame hpre hK5 (regIs_ptr hm5 rfl) (regIs_ptr hm5 rfl)
    (x2_eq hm5 rfl (by decide)) (by decide) (by decide) (by decide) rfl
    (hH4.keepB hkb5 (by decide) (by decide)) hK5.2.2.2.1.1 hA5
  refine ⟨hpre5, fun m6 hQ6 ↦ ?_⟩
  obtain ⟨hK6, hS6, -, hH6⟩ := hpost5 m6 hQ6
  have hR6 := regs_of_saved hS6 hR5
  -- `update` with the message.
  refine frameCall r hp hpre b3_in_code (List.cons_ne_nil _ _) run_b3 (by decide) rfl hK6
    trivial hc.2.2.1 fun m7 hm7 hK7 hkb7 ↦ ?_
  have hR7 := regs_of_block hm7 rfl rfl rfl rfl rfl rfl hR6
  have hX2 : m7.regs.X2.toNat = r.m0.regs.X5.toNat := by
    have := regIs_of_reg hm7 (y := .X2) rfl hR6.2.2.2.2.1
    exact congrArg BitVec.toNat this
  obtain ⟨hpre7, hpost7⟩ := updateInput hpre hK7 (regIs_ptr hm7 rfl)
    (regIs_of_reg hm7 rfl hR6.2.2.2.2.2) hX2 (r.pre_msg hpre) (by decide) rfl
    (hH6.keepB hkb7 (by decide) (by decide))
  refine ⟨hpre7, fun m8 hQ8 ↦ ?_⟩
  obtain ⟨hK8, hS8, -, hH8⟩ := hpost7 m8 hQ8
  have hR8 := regs_of_saved hS8 hR7
  -- `update` with the randomizer.
  refine frameCall r hp hpre b4_in_code (List.cons_ne_nil _ _) run_b4 (by decide) rfl hK8
    trivial hc.2.2.1 fun m9 hm9 hK9 hkb9 ↦ ?_
  have hR9 := regs_of_block hm9 rfl rfl rfl rfl rfl rfl hR8
  obtain ⟨hpre9, hpost9⟩ := updateInput hpre hK9 (regIs_ptr hm9 rfl)
    (regIs_of_reg hm9 rfl hR8.2.2.2.1) (x2_eq hm9 rfl (by decide)) (r.pre_rnd hpre) (by decide)
    rfl (hH8.keepB hkb9 (by decide) (by decide))
  refine ⟨hpre9, fun m10 hQ10 ↦ ?_⟩
  obtain ⟨hK10, hS10, -, hH10⟩ := hpost9 m10 hQ10
  have hR10 := regs_of_saved hS10 hR9
  -- `finalize` into 1776.
  have hK10' : Keep r r.prologueSlots m10 := ⟨hK10.1, allOf_left hK10.2⟩
  refine frameCall r hp hpre b5_in_code (List.cons_ne_nil _ _) run_b5 (by decide) rfl
    hK10' trivial hc.2.2.2.1 fun m11 hm11 hK11 hkb11 ↦ ?_
  have hR11 := regs_of_block hm11 rfl rfl rfl rfl rfl rfl hR10
  obtain ⟨hpre11, hpost11⟩ := finalizeFrame hpre hK11 (regIs_ptr hm11 rfl) (regIs_ptr hm11 rfl)
    (by decide) (by decide) (by decide) rfl (hH10.keepB hkb11 (by decide) (by decide))
  refine ⟨hpre11, fun m12 hQ12 ↦ ?_⟩
  obtain ⟨hK12, hS12, -, hD⟩ := hpost11 m12 hQ12
  have hR12 := regs_of_saved hS12 hR11
  refine .done _ ⟨rfl, ⟨hK12.1, allOf_append hK12.2 ⟨⟨length_digest32 r, by norm_num, ?_⟩, trivial⟩⟩,
    hR12.1, hR12.2.1, hR12.2.2.1⟩
  simpa [Run.digest32, Run.pp, Run.msg, Run.rnd, WotsLeafPre.pp, WotsLeafPre.message,
    WotsLeafPre.randomizer, List.append_assoc] using hD

end

end NativeRustcArm.WotsLeafProof
