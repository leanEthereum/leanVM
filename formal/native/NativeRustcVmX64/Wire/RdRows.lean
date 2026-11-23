module

public import NativeRustcVmX64.Wire.RdRows.CallB
public import NativeRustcVmX64.Code.Vm.RdRows.Names
public import NativeRustcVmX64.Code.Vm.ReaderWords.Names

/-!
# `rd_rows` meets its contract (x86-64)

`rdRows_spec`: the prologue and the width check (`b0`, `rw ≤ lw` always), the set-up (`b3`), then
rows of `rw > 0` words (`b4`, `loopA`) or none (`b12`, `loopB`).
-/

namespace NativeRustcVmX64.Wire.RdRows

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.RdRows
open NativeRustcVmX64.Transcript (Frame frameEnv frame_wf frame_mapped frame_noWrap match_rsp
  Frame.of_prologue Frame.of_block after after_eq MidOk wordAt_write sameOutside_low)
open NativeRustcVm.Transcript (off off_zero off_add off_off)
open NativeRustcVm (WordAt WordsAt)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open NativeRustcVmX64.Wire (pc_cond ite_t ite_f eq64 ult64 toNat_sub64)

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}

theorem shl9 (x : BitVec 64) :
    BinOp.apply .shl .W64 x (BitVec.ofNat 64 9) = BitVec.ofNat 64 (512 * x.toNat) := by
  have hs : shiftCount .W64 (BitVec.ofNat 64 9) = 9 := by decide
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, low_W64, ext_W64, hs, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat]
  omega

theorem shl3 (x : BitVec 64) :
    BinOp.apply .shl .W64 x (BitVec.ofNat 64 3) = BitVec.ofNat 64 (8 * x.toNat) := by
  have hs : shiftCount .W64 (BitVec.ofNat 64 3) = 3 := by decide
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, low_W64, ext_W64, hs, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat]
  omega

theorem flag_nil : flag [] = 1 := by
  unfold flag; rw [ite_t]; intro x hx; cases hx

variable [Host] {k : Nat}

/-- **From the entry.** -/
theorem entry_spec (hp : Placed code k) (g : Geo m0 bp B.length)
    (hw : Spec (Labels.label NativeRustcVmX64.Vm.ReaderWords.entryLabel) ReaderWordsPre ReaderWordsPost)
    (hR0 : ReaderAt m0.dmem (rdr m0) bp B c) :
    Eventually (step1 Host.exe) (Post m0) ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.RdRows.b0Offset)⟩ := by
  have hst := g.g.st
  have h0 := g.s0
  have hsb := g.sb_toNat
  have h64 := g.lw64
  have hrl := g.rwlw
  have hn := g.n256
  have hlw : lw m0 = (reg m0 .rdx).toNat := rfl
  have hrw : rw m0 = (reg m0 .rcx).toNat := rfl
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 80) (rest := []) (vars := fun _ ↦ 0) (ret := 0)
    ⟨frame_mapped hst (by decide), frame_noWrap hst (by decide)⟩ (by simp)
    (List.pairwise_singleton _ _)
  have hm0 : Match (frameEnv m0 m0 80 []) entryS m0 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial
  refine exec_then (Wire.infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 nofun hm0
    fun s1 hm1 hpc1 ↦ ?_
  obtain ⟨hpro, hws1, hfw8, hfw16, hrbx1, hK1⟩ := ok_b0
  have hf1 : Frame m0 80 slots 8 s1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le (by decide)
  have hs1 : NativeRustcVm.SameOutside m0.dmem s1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 80) 80) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hws1
  have hR80 : ∀ q, NativeRustcVm.InRange (stackBelow m0 80) 80 q →
      (rspOf m0).toNat - 80 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat := fun q hq ↦ by
    rw [NativeRustcVm.inRange_iff (by unfold NativeRustcVm.NoWrap; rw [hsb]; omega), hsb] at hq
    omega
  have hloc : Loc m0 s1.data.dmem :=
    ⟨wordAt_write hm1 (r := 0) (o := 8) rfl (by decide) (v := .reg .rdx) hfw8,
      wordAt_write hm1 (r := 0) (o := 16) rfl (by decide) (v := .reg .rdi) hfw16⟩
  have hkp1 : Kp m0 bp B c 0 [] c s1.data.dmem :=
    ⟨rfl, g.reader hR0 hs1 fun q hq ↦ .inl (by have := hR80 q hq; rw [g.Stk_iff]; omega),
      fun _ h ↦ absurd h (by simp), hloc, fun q hq ↦ hs1 q fun h ↦ hq (.inl (by
        have := hR80 q h; rw [g.Stk_iff]; omega))⟩
  have hk1 := regs_kept hK1 fun r v h ↦ hm1.regs r v h
  have hpc2 := pc_cond hpc1 (P := rw m0 ≤ lw m0) (by
    show (!(CmpOp.apply .ult .W64 (reg m0 .rdx) (reg m0 .rcx))) = _
    rw [ult64, Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    omega)
  rw [ite_t hrl, hp.label NativeRustcVmX64.Vm.RdRows.label_2_at] at hpc2
  have hr15 : reg s1.data .r15 = BinOp.apply .sub .W64 (reg m0 .rdx) (reg m0 .rcx) :=
    hm1.regs .r15 (.bin .sub .W64 (.reg .rdx) (.reg .rcx)) (by
      rw [after_eq exit_b0]; exact (after_eq run_b0).symm ▸ rfl)
  -- `b3`: the set-up.
  obtain ⟨hok3, hrbp3, hr12_3, hr14_3, hK3⟩ := ok_b3
  refine fr_step hp g (j := NativeRustcVmX64.Vm.RdRows.b3Offset) b3_in_code (by simp [b3]) exit_b3 nofun hok3 hpc2 hf1
    fun s3 hf3 hd3 hr3 hpc3 ↦ ?_
  have hk3 := regs_kept hK3 hr3
  have hkp3 : Kp m0 bp B c 0 [] c s3.data.dmem := by rw [hd3]; exact hkp1
  have hr14 : reg s3.data .r14 = off (lv m0) (512 * 0) := by
    rw [hr3 .r14 _ hr14_3, Nat.mul_zero, off_zero]
    exact hk1 .r8 (by simp)
  have hr12 : reg s3.data .r12 = off (lv m0) (512 * nr m0) := by
    rw [hr3 .r12 _ hr12_3]
    show BinOp.apply .add .W64 (reg s1.data .r8) (BinOp.apply .shl .W64 (reg s1.data .rsi)
      (BitVec.ofNat 64 9)) = _
    rw [hk1 .r8 (by simp), hk1 .rsi (by simp), shl9]
    simp only [BinOp.apply, low_W64, ext_W64]
  have hrbp : reg s3.data .rbp = reg m0 .rcx := by
    rw [hr3 .rbp _ hrbp3]; exact hk1 .rcx (by simp)
  have hpc4 := pc_cond hpc3 (P := rw m0 = 0) (by
    show CmpOp.apply .eq .W64 (BinOp.apply .and .W64 (reg s1.data .rcx) (reg s1.data .rcx))
      (BitVec.ofNat 64 0) = _
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.and_self]
    rw [hk1 .rcx (by simp), eq64, BitVec.toNat_ofNat])
  by_cases h0w : rw m0 = 0
  · -- `b12`: leaves without a row.
    rw [ite_t h0w, hp.label NativeRustcVmX64.Vm.RdRows.label_9_at] at hpc4
    obtain ⟨hmid12, hmem12, hr13_12, hrbp12, hr15_12, hK12⟩ := ok_b12
    have hwf := fr_wf g hf3 (vars := fun _ ↦ 0) (ret := 0)
    have hm := fr_match hf3 (vars := fun _ ↦ 0) (ret := 0)
    refine exec_at (Wire.infix_of b12_in_code (by simp [b12]) hp) exit_b12 hwf nofun hpc4 hm
      fun s4 hm4 hpc5 ↦ ?_
    have hf4 : Frame m0 80 slots 8 s4.data := Frame.of_block hf3 hwf hm4 hmid12 slots_le
    have hs4 := Wire.Match.sameOutside_in hm4 hwf (r0 := 0) (o := 24) (n := 8) rfl (by decide)
      (by rw [hmem12]; intro w hw; simp only [List.mem_singleton] at hw; subst hw; decide)
    have hR24 : ∀ q, NativeRustcVm.InRange (stackBelow m0 80 + BitVec.ofNat 64 24) 8 q →
        (rspOf m0).toNat - 56 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - 48 := fun q hq ↦ by
      have e := g.off_sb (o := 24) (by decide)
      rw [NativeRustcVm.inRange_iff (by
        unfold NativeRustcVm.NoWrap; rw [show stackBelow m0 80 + BitVec.ofNat 64 24 = off (sb m0) 24
          from rfl, e]; omega), show stackBelow m0 80 + BitVec.ofNat 64 24 = off (sb m0) 24 from rfl,
        e] at hq
      omega
    have hkp4 : Kp m0 bp B c 0 [] c s4.data.dmem :=
      hkp3.keep g (by omega) hs4 fun q hq ↦ by have := hR24 q hq; unfold Mov; omega
    have hload : (frameEnv m0 s3.data 80 []).load 0 8 8 = reg m0 .rdx := hkp3.hloc.load_lw
    have hk4 := regs_kept hK12 fun r v h ↦ hm4.regs r v h
    have hl24 : WordAt s4.data.dmem (off (sb m0) 24) (UInt64.ofNat (8 * lw m0)) := by
      have := wordAt_write hm4 (r := 0) (o := 24) rfl (by decide) (v := e8) fun u hu ↦ by
        rw [hmem12]; exact findWrite_head hu
      rw [e8_eval _ hload] at this
      exact this
    simp only [PcOk] at hpc5
    have hH : HeadB k m0 bp B c 0 [] c s4 :=
      ⟨hpc5.trans (congrArg Host.addrOf rfl),
        ⟨hf4, (hk4 .r14 (by simp)).trans hr14, (hk4 .r12 (by simp)).trans hr12,
          fun hp0 ↦ (hm4.regs .r13 _ hr13_12).trans (rem8_eval _ hload (by omega) hp0),
          fun hp0 ↦ (hm4.regs .rbp _ hrbp12).trans (rbp8_eval _ hload (by omega) hp0),
          fun hp0 ↦ (hm4.regs .r15 _ hr15_12).trans (e8m_eval _ hload (by omega) hp0),
          hl24, g.n0, h0w⟩, hkp4⟩
    exact loopB hp g hw hR0 hH
  · -- `b4`: rows of `rw > 0` words.
    rw [ite_f h0w] at hpc4
    obtain ⟨hok4, hrbx4, hr15_4, hK4⟩ := ok_b4
    refine fr_step hp g (j := NativeRustcVmX64.Vm.RdRows.b4Offset) b4_in_code (by simp [b4]) exit_b4 nofun hok4
      (hpc4.trans (congrArg Host.addrOf rfl)) hf3 fun s4 hf4 hd4 hr4 hpc5 ↦ ?_
    have hk4 := regs_kept hK4 hr4
    simp only [PcOk] at hpc5
    have hH : HeadA k m0 bp B c 0 [] c s4 :=
      ⟨hpc5.trans (congrArg Host.addrOf rfl),
        ⟨hf4, (hk4 .r14 (by simp)).trans hr14, (hk4 .r12 (by simp)).trans hr12,
          (hk4 .rbp (by simp)).trans hrbp, by
            rw [hr4 .r15 _ hr15_4]
            show BinOp.apply .shl .W64 (reg s3.data .r15) (BitVec.ofNat 64 3) = _
            have hzc : zc m0 = (reg m0 .rdx).toNat - (reg m0 .rcx).toNat := rfl
            have e15 : reg s3.data .r15 = BitVec.ofNat 64 (zc m0) := by
              rw [hk3 .r15 (by simp), hr15]
              apply BitVec.eq_of_toNat_eq
              rw [toNat_sub64 (by omega), BitVec.toNat_ofNat]
              omega
            rw [e15, shl3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)], by
            rw [hr4 .rbx _ hrbx4, flag_nil]; exact merge_val _ (v := 1) (by decide), g.n0,
            by omega⟩,
        by rw [hd4]; exact hkp3⟩
    exact loopA hp g hw hR0 hH

/-- **`rd_rows` meets its contract.** -/
theorem rdRows_spec (hp : Placed code k)
    (hw : Spec (Labels.label NativeRustcVmX64.Vm.ReaderWords.entryLabel) ReaderWordsPre ReaderWordsPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.RdRows.entryLabel) RdRowsPre RdRowsPost := by
  intro m0 ⟨hst, hn0, hn, hlw, hrw, hout, bp, B, c, hR, hd⟩
  rw [hp.label NativeRustcVmX64.Vm.RdRows.entry_at]
  exact entry_spec hp (geo_of hst hn0 hn hlw hrw hout hR hd) hw hR

end

end NativeRustcVmX64.Wire.RdRows
