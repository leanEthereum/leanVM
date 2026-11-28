module

public import NativeRustcX64.WotsLeaf.Digest.Prologue

/-!
# Region 1: the message digest

From the entry to `b6` (directive 47): the prologue (`b0`) and `memset` of the hasher at `2008`,
`update` with `P` (its address kept at `104`), the address at `112`, the message, the randomizer
(`b1 .. b4`), `finalize` into `112` (`b5`). Exit: `AtCheck`, the digest's 32 bytes at `112`.
-/

namespace NativeRustcX64.WotsLeafProof

open NativeRustc NativeRustc.Keccak NativeRustc.Xmss NativeRustcX64.Sym LeanVM.Protocol.KeccakHash
open NativeRustcX64.Xmss.WotsLeaf Digest

@[expose] public section

/-- The slots at `b6`: the layer, `e`, `out`, `P`'s address, the digest. -/
def Run.checkSlots (r : Run) : List Slot :=
  r.prologueSlots ++ [(104, 8, regBytes (reg r.m0 .rsi)), (112, 32, r.digest32)]

/-- **At `b6`**: what the frame keeps, the digest's 32 bytes at `112`. -/
def Run.AtCheck (r : Run) (m : MachineData) : Prop := Keep r r.checkSlots m

end

public section

theorem length_hashBytes (d : List UInt8) : (hashBytes d).length = 32 := by
  rw [hashBytes, show digestBytes (keccak256 d) = Native.Keccak.wordsBytes (keccak256 d).toList
    from rfl, Native.Keccak.Proof.length_wordsBytes]
  simp

theorem length_digest32 (r : Run) : r.digest32.length = 32 := length_hashBytes _

/-- The registers the digest's blocks read across calls: the hasher's address, `P`'s, the
message's and its length, the randomizer's. -/
def DigestRegs (r : Run) (m : MachineData) : Prop :=
  Run.RegIs m .r12 (r.off 2008) ∧ Run.RegIs m .r13 (reg r.m0 .rsi) ∧
    Run.RegIs m .r14 (reg r.m0 .r9) ∧ Run.RegIs m .r15 (reg r.m0 .r8) ∧
    Run.RegIs m .rbx (WotsLeafPre.rndPtr r.m0)

theorem DigestRegs.of_saved {r : Run} {m m' : MachineData} (hS : Saved m m')
    (h : DigestRegs r m) : DigestRegs r m' :=
  ⟨RegIs.of_saved hS rfl h.1, RegIs.of_saved hS rfl h.2.1, RegIs.of_saved hS rfl h.2.2.1,
    RegIs.of_saved hS rfl h.2.2.2.1, RegIs.of_saved hS rfl h.2.2.2.2⟩

theorem DigestRegs.of_block [Labels] {r : Run} {m m' : MachineData} {ret : BitVec 64}
    {S : SState} (hm : Match (r.envR m [] ret) S m') (h12 : S.reg .r12 = some (.reg .r12))
    (h13 : S.reg .r13 = some (.reg .r13)) (h14 : S.reg .r14 = some (.reg .r14))
    (h15 : S.reg .r15 = some (.reg .r15)) (hbx : S.reg .rbx = some (.reg .rbx))
    (h : DigestRegs r m) : DigestRegs r m' :=
  ⟨regIs_reg hm h12 h.1, regIs_reg hm h13 h.2.1, regIs_reg hm h14 h.2.2.1,
    regIs_reg hm h15 h.2.2.2.1, regIs_reg hm hbx h.2.2.2.2⟩

variable [Host]

/-- RSP at the entry: the frame's byte `2760`. -/
theorem Run.base_add_frame (r : Run) (hpre : r.Pre) :
    r.base + BitVec.ofInt 64 2760 = rspOf r.m0 := by
  have hb := r.base_toNat hpre
  apply BitVec.eq_of_toNat_eq
  rw [show BitVec.ofInt 64 2760 = BitVec.ofNat 64 2760 from rfl,
    Sym.toNat_add_ofNat _ _ (by omega)]
  omega

/-- **Region 1, the message digest.** -/
theorem digest_region : RegionSpec (fun r m ↦ m = r.m0) NativeRustcX64.Xmss.WotsLeaf.b0Offset fun r st ↦ st.pc = r.pc NativeRustcX64.Xmss.WotsLeaf.b6Offset ∧
    r.AtCheck st.data := by
  intro r hp hc hpre m hm0
  subst hm0
  -- The prologue.
  have hwf0 := envR_wf hpre (m := r.m0) (fun _ h ↦ h) extraOK_nil
    (r.pc (NativeRustcX64.Xmss.WotsLeaf.b0Offset + b0.length)).toBitVec
  have hm0 : Match (r.envR r.m0 [] (r.pc (NativeRustcX64.Xmss.WotsLeaf.b0Offset + b0.length)).toBitVec) entryS r.m0 := by
    apply Match.withKnownBytes
    · apply Match.withKnownBytes
      · apply match_ofMachine
        · exact ⟨rfl, rfl, rfl, rfl, trivial⟩
        · exact ⟨by show rspOf r.m0 = r.base + BitVec.ofInt 64 2760; rw [r.base_add_frame hpre], trivial⟩
        · exact trivial
        · exact trivial
        · refine ⟨?_, ?_, ?_, trivial⟩
          · change r.base + BitVec.ofInt 64 (-8) = r.base - 8#64 + BitVec.ofInt 64 0
            simp [BitVec.sub_eq_add_neg]
          · simp [Sym.eval, Env.base, gotAddr]
          · simp [Sym.eval, Env.base, gotAddr]
      · intro i hi
        simpa [Sym.eval, Run.envR, Run.env, Env.base] using
          (r.got hpre).byte (by simp : "memcpy" ∈ _) hi
    · intro i hi
      simpa [Sym.eval, Run.envR, Run.env, Env.base] using
        (r.got hpre).byte (by simp : "memset" ∈ _) hi
  refine blk r hp b0_in_code (List.cons_ne_nil _ _) run_b0 hwf0 rfl hm0 fun st hm1 hpc ↦ ?_
  have hF1 := frame_of_entry hpre hm1 hwf0 rfl (by decide) (by decide)
  have hS1 := prologue_slots hm1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hK1 : CallKeep r (r.prologueSlots ++ [(112, 16, r.addr 12 0)]) st.data := ⟨hF1, hS1⟩
  have hR1 : DigestRegs r st.data := by
    refine ⟨regIs_ptr hm1 rfl, regIs_of_reg hm1 rfl rfl, regIs_of_reg hm1 rfl rfl,
      regIs_of_reg hm1 rfl rfl, ?_⟩
    unfold Run.RegIs reg
    rw [hm1.regs .rbx _ rfl]
    exact r.load_rndPtr hpre (fun _ _ ↦ rfl)
  refine callAt hpc hc.2.1 ?_
  obtain ⟨hpre1, hpost1⟩ := memsetFrame hpre hK1 (regIs_ptr hm1 rfl) (byte_zero hm1 rfl)
    (toNat_of_lit hm1 rfl (by decide)) (by decide) rfl
  refine ⟨hpre1, fun m2 hsp2 hQ2 ↦ ?_⟩
  obtain ⟨hK2, hS2, -, hB2⟩ := hpost1 m2 hsp2 hQ2
  have hH2 : HasherAt r m2 2008 [] := ⟨_, hB2, holds_new⟩
  have hR2 := hR1.of_saved hS2
  -- `update` with `P`.
  refine frameCall r hp hpre b1_in_code (List.cons_ne_nil _ _) run_b1 (by decide) rfl hK2
    trivial extraOK_nil trivial trivial trivial hc.2.2.1 fun m3 hm3 hK3 hkb3 ↦ ?_
  have hR3 := hR2.of_block hm3 rfl rfl rfl rfl rfl
  have h104 : BytesAt m3.dmem (r.off 104) (regBytes (reg r.m0 .rsi)) := by
    have := frame_covers hm3 (o := 104) (n := 8) (by decide) (v := .reg .r13) (by decide)
    rwa [show (Sym.reg .r13).eval (r.envR m2 [] (r.pc (NativeRustcX64.Xmss.WotsLeaf.b1Offset + b1.length)).toBitVec) = reg r.m0 .rsi
      from hR2.2.1] at this
  have hK3' : CallKeep r (r.prologueSlots ++ [(112, 16, r.addr 12 0), (104, 8,
      regBytes (reg r.m0 .rsi))]) m3 :=
    ⟨hK3.1, hK3.2.1, hK3.2.2.1, hK3.2.2.2.1, hK3.2.2.2.2.1,
      ⟨length_regBytes _, by norm_num, h104⟩, trivial⟩
  obtain ⟨hpre3, hpost3⟩ := updateInput hpre hK3' (regIs_of_reg hm3 rfl hR2.1)
    (regIs_of_reg hm3 rfl hR2.2.1) (toNat_of_lit hm3 rfl (by decide)) (r.pre_pp hpre) (by decide)
    rfl (((r.got hpre).1 "memcpy" (by simp)).2.2.2 (reg r.m0 .rsi, 16) (by simp))
    (hH2.keepB hkb3 (by decide) (by decide))
  refine ⟨hpre3, fun m4 hsp4 hQ4 ↦ ?_⟩
  obtain ⟨hK4, hS4, -, hH4⟩ := hpost3 m4 hsp4 hQ4
  have hR4 := hR3.of_saved hS4
  -- `update` with the address.
  refine frameCall r hp hpre b2_in_code (List.cons_ne_nil _ _) run_b2 (by decide) rfl hK4
    trivial extraOK_nil trivial trivial trivial hc.2.2.1 fun m5 hm5 hK5 hkb5 ↦ ?_
  have hR5 := hR4.of_block hm5 rfl rfl rfl rfl rfl
  obtain ⟨hpre5, hpost5⟩ := updateFrame hpre hK5 (regIs_of_reg hm5 rfl hR4.1) (regIs_ptr hm5 rfl)
    (toNat_of_lit hm5 rfl (by decide)) (by decide) (by decide) (by decide) rfl
    (hH4.keepB hkb5 (by decide) (by decide)) hK5.2.2.2.2.1.1 hK5.2.2.2.2.1.2.2
  refine ⟨hpre5, fun m6 hsp6 hQ6 ↦ ?_⟩
  obtain ⟨hK6, hS6, -, hH6⟩ := hpost5 m6 hsp6 hQ6
  have hR6 := hR5.of_saved hS6
  -- `update` with the message.
  refine frameCall r hp hpre b3_in_code (List.cons_ne_nil _ _) run_b3 (by decide) rfl hK6
    trivial extraOK_nil trivial trivial trivial hc.2.2.1 fun m7 hm7 hK7 hkb7 ↦ ?_
  have hR7 := hR6.of_block hm7 rfl rfl rfl rfl rfl
  obtain ⟨hpre7, hpost7⟩ := updateInput hpre hK7 (regIs_of_reg hm7 rfl hR6.1)
    (regIs_of_reg hm7 rfl hR6.2.2.2.1)
    (congrArg BitVec.toNat (regIs_of_reg hm7 (y := .rdx) rfl hR6.2.2.1)) (r.pre_msg hpre)
    (by decide) rfl (((r.got hpre).1 "memcpy" (by simp)).2.2.2
      (reg r.m0 .r8, (reg r.m0 .r9).toNat) (by simp))
    (hH6.keepB hkb7 (by decide) (by decide))
  refine ⟨hpre7, fun m8 hsp8 hQ8 ↦ ?_⟩
  obtain ⟨hK8, hS8, -, hH8⟩ := hpost7 m8 hsp8 hQ8
  have hR8 := hR7.of_saved hS8
  -- `update` with the randomizer.
  refine frameCall r hp hpre b4_in_code (List.cons_ne_nil _ _) run_b4 (by decide) rfl hK8
    trivial extraOK_nil trivial trivial trivial hc.2.2.1 fun m9 hm9 hK9 hkb9 ↦ ?_
  have hR9 := hR8.of_block hm9 rfl rfl rfl rfl rfl
  obtain ⟨hpre9, hpost9⟩ := updateInput hpre hK9 (regIs_of_reg hm9 rfl hR8.1)
    (regIs_of_reg hm9 rfl hR8.2.2.2.2) (toNat_of_lit hm9 rfl (by decide)) (r.pre_rnd hpre)
    (by decide) rfl (((r.got hpre).1 "memcpy" (by simp)).2.2.2
      (WotsLeafPre.rndPtr r.m0, 16) (by simp))
    (hH8.keepB hkb9 (by decide) (by decide))
  refine ⟨hpre9, fun m10 hsp10 hQ10 ↦ ?_⟩
  obtain ⟨hK10, hS10, -, hH10⟩ := hpost9 m10 hsp10 hQ10
  have hR10 := hR9.of_saved hS10
  -- `finalize` into 112.
  have hK10' : Keep r (r.prologueSlots ++ [(104, 8, regBytes (reg r.m0 .rsi))]) m10 :=
    ⟨hK10.1, hK10.2.1, hK10.2.2.1, hK10.2.2.2.1, hK10.2.2.2.2.2.1, trivial⟩
  refine frameCall r hp hpre b5_in_code (List.cons_ne_nil _ _) run_b5 (by decide) rfl hK10'
    trivial extraOK_nil trivial trivial trivial hc.2.2.2.1 fun m11 hm11 hK11 hkb11 ↦ ?_
  obtain ⟨hpre11, hpost11⟩ := finalizeFrame hpre hK11 (regIs_ptr hm11 rfl)
    (regIs_of_reg hm11 rfl hR10.1) (by decide) (by decide) (by decide) rfl
    (hH10.keepB hkb11 (by decide) (by decide))
  refine ⟨hpre11, fun m12 hsp12 hQ12 ↦ ?_⟩
  obtain ⟨hK12, -, -, hD⟩ := hpost11 m12 hsp12 hQ12
  refine .done _ ⟨rfl, hK12.1, hK12.2.1, hK12.2.2.1, hK12.2.2.2.1, hK12.2.2.2.2.1,
    ⟨length_digest32 r, by norm_num, ?_⟩, trivial⟩
  simpa [Run.digest32, Run.pp, Run.msg, Run.rnd, WotsLeafPre.pp, WotsLeafPre.message,
    WotsLeafPre.randomizer, List.append_assoc] using hD

end

end NativeRustcX64.WotsLeafProof
