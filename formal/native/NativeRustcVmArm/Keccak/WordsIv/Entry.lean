module

public import NativeRustcVmArm.Code.Vm.Memset.Names
public import NativeRustcVmArm.Keccak.WordsIv.Full
public import NativeRustcVmArm.Keccak.WordsHash.Entry

/-!
# `keccak256_words::<fiat_shamir_iv's closure>`: the entry

`setup_run`: from the entry, the entry block (`entry`, `b0`) saves X19 to X25, X29, X30 in the
frame and calls `memset` to zero the 25 lanes at the frame's byte 8; the setup block (`setup`,
`b1`) puts the whole blocks' words `17 (len / 136)` in X24, `len / 136` computed in 32 bits
(`nbI_val`, `len < 2 ^ 32`), and branches on `136 ≤ len` (`SetupAt`: `Ctx`, the lanes zero).
`entry_run`: then the head of the first whole block (`fullInit`, `b21`: X25 zero), or, with no
whole block, the last block's head (`TailStart`).
-/

namespace NativeRustcVmArm.WordsIv

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcArm.KeccakF (WordAt wordAt_of_eq wordAt_write wordAt_keep same_region)
open NativeRustcVmArm.Keccak (bytesAt_of_same)
open NativeRustcVmArm.WordsHash (frame nb Lanes lanes_congr frame_noWrap frame_mapped frame_aligned
  inStack_of_frame not_inRange_lanes inFrame_of_lanes wordAt_zero lane_replicate nb17_val)
open NativeRustcVm.Keccak (wordBlocks)
open Vm.Keccak256WordsOfFiatShamirIv

@[expose] public section

/-- **After the setup**: `Ctx`, the lanes zero, at the first whole block's set-up if `len` holds
one, else at the last block's head. -/
def SetupAt [Host] (m0 : MachineData) (k : Nat) (st : MachineState) : Prop :=
  Ctx m0 st.data ∧ Lanes m0 st.data (fun _ => 0) ∧
    st.pc = if 136 ≤ m0.regs.X2.toNat then Host.addrOf (k + NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.b21Offset) else Host.addrOf (k + NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.b2Offset)

end

public section

theorem lsr39 (v : BitVec 64) : (UnOp.apply (.ubfm 39 63) .W64 v).toNat = v.toNat / 2 ^ 39 := by
  simp only [UnOp.apply, Sym.low_W64, Sym.ext_W64, evalUBFM, BitVec.take]
  have hw : RegWidth.W64.bits = 64 := rfl
  simp only [hw]
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem trunc32_ofNat {x : Nat} (hx : x < 2 ^ 32) :
    (UnOp.apply .trunc .W32 (BitVec.ofNat 64 x)).toNat = x := by
  have h : (Sym.low .W32 (BitVec.ofNat 64 x)).toNat = x := by
    rw [Sym.low_W32, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    show x % 2 ^ 64 % 2 ^ 32 = x
    omega
  simp only [UnOp.apply, Sym.ext_W32, BitVec.toNat_setWidth, h]
  omega

/-- `⌊x c / 2 ^ 39⌋ = ⌊x / 136⌋` for `x < 2 ^ 32`, `c = ⌈2 ^ 39 / 136⌉`. -/
theorem div136_32 {x : Nat} (hx : x < 2 ^ 32) : x * 4042322161 / 2 ^ 39 = x / 136 := by
  obtain ⟨q, hq⟩ : ∃ q, q = x / 136 := ⟨_, rfl⟩
  have h1 : 136 * q ≤ x := by rw [hq]; exact Nat.mul_div_le x 136
  have h2 : x < 136 * q + 136 := by rw [hq]; omega
  rw [← hq]
  apply Nat.div_eq_of_lt_le
  · omega
  · omega

/-- **The whole blocks' count** in 32 bits, by the product with `⌈2 ^ 39 / 136⌉`. -/
theorem nbI_val (x : Nat) (hx : x < 2 ^ 32) :
    UnOp.apply (.ubfm 39 63) .W64 (BinOp.apply .mul .W64 (UnOp.apply .trunc .W32
      (BitVec.ofNat 64 x)) (BitVec.ofNat 64 4042322161)) = BitVec.ofNat 64 (x / 136) := by
  apply BitVec.eq_of_toNat_eq
  have hm : (BinOp.apply .mul .W64 (UnOp.apply .trunc .W32 (BitVec.ofNat 64 x))
      (BitVec.ofNat 64 4042322161)).toNat = x * 4042322161 := by
    simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]
    rw [BitVec.toNat_mul, trunc32_ofNat hx, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 4042322161 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (by omega)]
  rw [lsr39, hm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x / 136 < 2 ^ 64 by omega)]
  exact div136_32 hx

variable [Host]

/-- **The entry and the setup.** -/
theorem setup_run (hms : Spec (label NativeRustcVmArm.Vm.Memset.entryLabel) MemsetPre MemsetPost) {k : Nat}
    (hp : Placed code k) {m0 : MachineData} (g : Geo m0) :
    Eventually (step1 Host.exe) (SetupAt m0 k) ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.b0Offset)⟩ := by
  have hstk := g.stk
  have hf := frame_noWrap hstk
  unfold NoWrap at hf
  have h8 : (frame m0 + BitVec.ofNat 64 8).toNat = (frame m0).toNat + 8 :=
    toNat_add_ofNat _ _ (by omega)
  let env0 := Env.ofMachine m0 [(frame m0, 288)]
  have hwf0 : env0.WF :=
    Env.wf_of ⟨⟨frame_mapped hstk fun _ h => h, frame_noWrap hstk⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm0 : Match env0 startEntry m0 :=
    match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, trivial⟩
      (by
        show _ = frame m0 + BitVec.ofInt 64 288
        simp only [frame]
        exact (BitVec.sub_add_cancel _ _).symm) trivial trivial trivial trivial
  have hb0 : env0.regions[0]? = some (frame m0, 288) := rfl
  refine exec_then (ic hp b0_in_code (List.cons_ne_nil _ _)) entry hwf0 hm0
    fun st1 hm1 hpc1 => ?_
  have hx0 : st1.data.regs.X0.toBitVec = frame m0 + BitVec.ofNat 64 8 :=
    (hm1.regs .X0 _ rfl).trans (by simp [Sym.eval, env0])
  have hx1 : st1.data.regs.X1 = 0 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X1 _ rfl).trans (by simp [Sym.eval]))
  have hx2 : st1.data.regs.X2.toNat = 200 := by
    have := hm1.regs .X2 _ rfl
    simp only [Sym.eval] at this
    rw [← UInt64.toNat_toBitVec]
    exact (congrArg BitVec.toNat this).trans (by simp)
  have hsp1 : st1.data.regs.SP.toBitVec = frame m0 := hm1.sp.trans (by simp [Sym.eval, env0])
  have hpre1 : MemsetPre st1.data := by
    unfold MemsetPre
    rw [hx0, hx2]
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [addr_add]
      exact frame_mapped hstk (hm1.kept hwf0) _ (by omega)
    · unfold NoWrap
      rw [h8]
      omega
  refine call_then hpc1 hms hpre1 fun st2 hpc2 hpost => ?_
  obtain ⟨-, hzero, hsame2, hsaved2⟩ := hpost
  simp only [hx0, hx1, hx2] at hzero hsame2
  rw [NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.b0_length, NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.b0Length, NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.b0Offset, Nat.add_zero] at hpc2
  let env2 := Env.ofMachine st2.data [(frame m0, 288)]
  have hwf2 : env2.WF :=
    Env.wf_of ⟨⟨frame_mapped hstk fun p h => hsaved2.2.2 p (hm1.kept hwf0 p h),
      frame_noWrap hstk⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm2 : Match env2 startMain st2.data :=
    match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, trivial⟩
      (by rw [hsaved2.2.1, hsp1]; simp [Sym.eval]) trivial trivial trivial trivial
  have hb2 : env2.regions[0]? = some (frame m0, 288) := rfl
  have r2 : ∀ r, calleeSaved r = true →
      (st2.data.regs.getXReg r).toBitVec = (st1.data.regs.getXReg r).toBitVec :=
    fun r hr => by rw [hsaved2.1 r hr]
  have e20 : (st2.data.regs.getXReg .X20).toBitVec = BitVec.ofNat 64 m0.regs.X2.toNat := by
    rw [r2 .X20 rfl, hm1.regs .X20 _ rfl]
    show m0.regs.X2.toBitVec = _
    simp
  have hlt : m0.regs.X2.toNat < 2 ^ 32 := by have := g.len; have := g.small; omega
  refine exec_at (ic hp b1_in_code (List.cons_ne_nil _ _)) setup hwf2 hpc2 hm2
    fun st3 hm3 hpc3 => .done _ ⟨?_, ?_, ?_⟩
  · have hslot : ∀ {o : Nat} {w : BitVec 64}, 208 ≤ o → o + 8 ≤ 288 →
        WordAt st1.data.dmem (frame m0 + BitVec.ofNat 64 o) w →
        WordAt st3.data.dmem (frame m0 + BitVec.ofNat 64 o) w := fun ho ho' h =>
      wordAt_keep hm3 hb2 ho' rfl (bytesAt_of_same hsame2 h fun i hi =>
        not_inRange_lanes hstk ho ho' i (by simpa using hi))
    refine ⟨hm3.sp.trans (by simp [Sym.eval, env2]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
    · exact (hm3.regs .X19 _ rfl).trans ((r2 .X19 rfl).trans (hm1.regs .X19 _ rfl))
    · exact (hm3.regs .X20 _ rfl).trans ((r2 .X20 rfl).trans (hm1.regs .X20 _ rfl))
    · exact (hm3.regs .X21 _ rfl).trans ((r2 .X21 rfl).trans (hm1.regs .X21 _ rfl))
    · exact (hm3.regs .X22 _ rfl).trans ((r2 .X22 rfl).trans (hm1.regs .X22 _ rfl))
    · exact (hm3.regs .X23 _ rfl).trans ((r2 .X23 rfl).trans (hm1.regs .X23 _ rfl))
    · refine (hm3.regs .X24 _ rfl).trans ?_
      simp only [Sym.eval, env2, Env.ofMachine_regs]
      rw [e20, nbI_val _ hlt, nb17_val]
      rfl
    · exact (Match.reg_eq hm2 hm3 rfl rfl).trans
        ((hsaved2.1 .X26 rfl).trans (Match.reg_eq hm0 hm1 rfl rfl))
    · exact (Match.reg_eq hm2 hm3 rfl rfl).trans
        ((hsaved2.1 .X27 rfl).trans (Match.reg_eq hm0 hm1 rfl rfl))
    · exact (Match.reg_eq hm2 hm3 rfl rfl).trans
        ((hsaved2.1 .X28 rfl).trans (Match.reg_eq hm0 hm1 rfl rfl))
    · simp only [AllOf, savedSlots]
      exact ⟨hslot (by decide) (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        hslot (by decide) (by decide) (wordAt_of_eq (wordAt_write hm1 hb0 (by decide) rfl) rfl),
        trivial⟩
    · intro p hp
      have hpf : ¬ InRange (frame m0) 288 p := fun h => hp (inStack_of_frame hstk h)
      exact (same_region hm3 hwf2 hb2 (fun w hw => by cases hw) p hpf).trans
        ((hsame2 p fun h => hpf (inFrame_of_lanes hstk h)).trans
          (same_region hm1 hwf0 hb0 (by decide) p hpf))
    · exact fun p h => hm3.kept hwf2 p (hsaved2.2.2 p (hm1.kept hwf0 p h))
  · intro i hi
    have h := wordAt_zero (by rfl) hzero hi
    rw [addr_add] at h
    exact wordAt_keep hm3 hb2 (by omega) rfl h
  · have hlt' := m0.regs.X2.toNat_lt
    simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, Sym.low_W64, env2, Env.ofMachine_regs]
      at hpc3
    rw [hpc3, e20]
    by_cases h : 136 ≤ m0.regs.X2.toNat
    · have hu : (BitVec.ofNat 64 m0.regs.X2.toNat).ult (BitVec.ofNat 64 136) = false := by
        simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt', decide_eq_false_iff_not]
        omega
      simp only [hu, Bool.not_false, ↓reduceIte, h]
      exact label_at hp b21_in_code rfl
    · have hu : (BitVec.ofNat 64 m0.regs.X2.toNat).ult (BitVec.ofNat 64 136) = true := by
        simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt', decide_eq_true_eq]
        omega
      simp only [hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h]
      rfl

/-- **The entry**: to the head of the first whole block, or with none, of the last block. -/
theorem entry_run (hms : Spec (label NativeRustcVmArm.Vm.Memset.entryLabel) MemsetPre MemsetPost) {k : Nat}
    (hp : Placed code k) {m0 : MachineData} (g : Geo m0) :
    Eventually (step1 Host.exe) (fun st => FullHead m0 k 0 st ∨ TailStart m0 k st)
      ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.b0Offset)⟩ := by
  refine Eventually.bind (setup_run hms hp g) fun st h => ?_
  obtain ⟨hc, hl, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hpc
  by_cases h : 136 ≤ m0.regs.X2.toNat
  · simp only [h, ↓reduceIte] at hpc
    subst hpc
    obtain ⟨hwf, hm⟩ := frame_env g hc
    refine exec_then (ic hp b21_in_code (List.cons_ne_nil _ _)) fullInit hwf hm
      fun st hm' hpc => .done _ (.inl ⟨?_, ?_, ?_, ?_, ?_⟩)
    · exact ctx_step g.stk hc hm' hwf rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
        (fun w hw => by cases hw)
    · exact fun i hi => wordAt_of_eq (wordAt_keep (r := 0) (sz := 288) hm' rfl (by omega) rfl
        (hl i hi)) (by rw [show wordBlocks (wv m0) 0 = Vector.replicate 25 0 from rfl,
          lane_replicate])
    · exact (hm'.regs .X25 _ rfl).trans (by simp [Sym.eval])
    · unfold nb
      omega
    · simp only [PcOk] at hpc
      rw [hpc]
      exact label_at hp b25_in_code rfl
  · simp only [h, ↓reduceIte] at hpc
    refine .done _ (.inr ⟨hc, ?_, hpc⟩)
    have h0 : nb m0 = 0 := by unfold nb; omega
    show Lanes m0 m (Keccak.lane (wordBlocks (wv m0) (nb m0)))
    rw [h0]
    exact lanes_congr hl fun i _ => (lane_replicate i).symm

end

end NativeRustcVmArm.WordsIv
