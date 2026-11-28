module

public import NativeRustcVmX64.Wire.RdRows.LoopB
public import NativeRustcVmX64.Code.Vm.ReaderWords.Names

/-!
# `rd_rows`' calls for leaves without a row (`rw = 0`) (x86-64)

`Reader::words` reads no word (`b21`; it cannot fail, `b22`), the next leaf (`b23`): the loop's
head again or the return with `1` (`b24`): `callB_step`; the loop over the leaves (`loopB`).
-/

namespace NativeRustcVmX64.Wire.RdRows

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.RdRows
open NativeRustcVmX64.Transcript (Frame frameEnv after after_eq MidOk)
open NativeRustcVm.Transcript (off off_zero off_add off_off)
open NativeRustcVm (WordAt WordsAt)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open NativeRustcVmX64.Wire (pc_cond ite_t ite_f eq64)

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}

variable [Host] {k : Nat}

section
variable (hp : Placed code k) (g : Geo m0 bp B.length)
  (hw : Spec (Labels.label NativeRustcVmX64.Vm.ReaderWords.entryLabel) ReaderWordsPre ReaderWordsPost)
  (hR0 : ReaderAt m0.dmem (rdr m0) bp B c)
include hp g hw hR0

/-- **A leaf without a row** (`b21`, the call, `b22`, `b23`): the return, or the loop's head at
the next leaf. -/
theorem callB_step {i : Nat} {rows : List (List K)} {ci : Nat} {st : MachineState}
    (hI : CallB k m0 bp B c i rows ci st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨ ∃ rows' ci',
      HeadB k m0 bp B c (i + 1) rows' ci' st') st := by
  have hli := hI.rb.lt
  have hrw0 := hI.rb.rw0
  have h64 := g.lw64
  have hlv := g.lvNw
  have hS := g.lvS
  have hrW := g.rW
  have hrS := g.rS
  have h0 := g.s0
  obtain ⟨hmid21, hlow21, hrdi21, hrdx21, hK21⟩ := ok_b21
  have hin : 512 * i + 8 * lw m0 + 8 * 0 ≤ 512 * nr m0 := by omega
  refine call_block hp hw g (j := NativeRustcVmX64.Vm.RdRows.b21Offset) b21_in_code (by simp [b21]) exit_b21 hmid21 hlow21 hrdi21
    (keeps_of hK21 .rsi (by simp)) hrdx21 hI.pc hI.rb.fr hI.kp.hloc hI.kp.hrd hin hI.rsi rfl
    fun m2 hf2 hreg2 hs2 hres2 ↦ ?_
  have hci := hI.kp.hrd.c_le
  have hrd0 : rdWords B (rw m0) ci = some ([], ci) := by rw [hrw0]; exact rdWords_zero hci
  rw [rdWords_zero hci] at hres2
  obtain ⟨hb1, -, hR2⟩ := hres2
  have hk2 : ∀ x ∈ [Reg64.rbp, .r12, .r13, .r14, .r15], reg m2 x = reg st.data x :=
    fun x hx ↦ hreg2 x _ (keeps_of hK21 x (mem_of_all (by decide) hx)) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> rfl)
  have hcall : ∀ q, (((lv m0).toNat + (512 * i + 8 * lw m0) ≤ q.toNat ∧
      q.toNat < (lv m0).toNat + (512 * i + 8 * lw m0) + 8 * 0) ∨
      ((rdr m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (rdr m0).toNat + 24) ∨
      ((rspOf m0).toNat - 128 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - 72)) →
      Mov m0 i q ∨ ((rdr m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (rdr m0).toNat + 24) := by
    intro q hq
    unfold Mov
    omega
  have hrb2 : RB m0 i m2 := hI.rb.keep g hf2 hk2 hs2 fun q hq ↦ by omega
  have hleaf : WordsAt m2.dmem (off (lv m0) (512 * i)) ((paddedLeaf [] (lw m0)).map K.lane) := by
    rw [map_lane_paddedLeaf]
    simp only [List.length_nil, Nat.sub_zero, List.map_nil, List.append_nil]
    exact g.words_keep (by simp; omega) hI.zs hs2 fun q hq ↦ by
      simp only [List.length_replicate]; omega
  have hkp : Kp m0 bp B c (i + 1) (rows ++ [[]]) ci m2.dmem :=
    Kp.succ g hI.kp hli hrd0 hs2 hcall hR2 hleaf
  have hlen := rows_len hkp.hrows
  have hchg2 : Chg m0 m2.dmem := hkp.hchg
  -- `b22`: the tag (`Some`).
  obtain ⟨hok22, hK22⟩ := ok_b22
  refine fr_step hp g (j := NativeRustcVmX64.Vm.RdRows.b22Offset) b22_in_code (by simp [b22]) exit_b22 nofun hok22 rfl hf2
    fun s22 hf22 hd22 hr22 hpc22 ↦ ?_
  have hk22 := regs_kept hK22 hr22
  have hpc22' := pc_cond hpc22 (P := boolRet m2 = 0) (by
    show CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (reg m2 .rax) (reg m2 .rax))
      (BitVec.ofNat 64 0) = _
    rw [al_zero]; rfl)
  rw [ite_f (by omega)] at hpc22'
  have hrb22 : RB m0 i s22.data :=
    hrb2.keepEq g hf22 (fun x hx ↦ hk22 x (mem_of_all (by decide) hx)) hd22
  -- `b23`: the next leaf.
  obtain ⟨hok23, hr14_23, hK23⟩ := ok_b23
  refine fr_step hp g (j := NativeRustcVmX64.Vm.RdRows.b23Offset) b23_in_code (by simp [b23]) exit_b23 nofun hok23
    (hpc22'.trans (congrArg Host.addrOf rfl)) hf22 fun s23 hf23 hd23 hr23 hpc23 ↦ ?_
  have hk23 := regs_kept hK23 hr23
  have hr14 : reg s23.data .r14 = off (lv m0) (512 * (i + 1)) := by
    rw [hr23 .r14 _ hr14_23]
    show BinOp.apply .add .W64 (BitVec.ofNat 64 512) (reg s22.data .r14) = _
    rw [hrb22.r14, lit_add_off, show 512 * i + 512 = 512 * (i + 1) by omega]
  have hd : s23.data.dmem = m2.dmem := hd23.trans hd22
  have hpc24 := pc_cond hpc23 (P := i + 1 ≠ nr m0) (by
    show (!(CmpOp.apply .eq .W64 (BinOp.apply .add .W64 (BitVec.ofNat 64 512)
      (reg s22.data .r14)) (reg s22.data .r12))) = _
    rw [hrb22.r14, hrb22.r12, lit_add_off, eq64, Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    rw [g.off_eq (by omega) (by omega)]
    omega)
  by_cases hlast : i + 1 ≠ nr m0
  · rw [ite_t hlast, hp.label NativeRustcVmX64.Vm.RdRows.label_10_at] at hpc24
    refine .done _ (.inr ⟨_, _, hpc24, ⟨hf23, hr14,
      (hk23 .r12 (by simp)).trans hrb22.r12,
      fun h ↦ (hk23 .r13 (by simp)).trans (hrb22.r13 h),
      fun h ↦ (hk23 .rbp (by simp)).trans (hrb22.rbp h),
      fun h ↦ (hk23 .r15 (by simp)).trans (hrb22.r15 h),
      by rw [hd23]; exact hrb22.l24, by omega, hrw0⟩, by rw [hd]; exact hkp⟩)
  · rw [ite_f hlast] at hpc24
    have hn : i + 1 = nr m0 := by omega
    obtain ⟨hok24, hrbx24⟩ := ok_b24
    refine Eventually.mono (fr_step hp g (j := NativeRustcVmX64.Vm.RdRows.b24Offset) b24_in_code (by simp [b24]) exit_b24 nofun
      hok24 (hpc24.trans (congrArg Host.addrOf rfl)) hf23 fun s24 hf24 hd24 hr24 hpc25 ↦ ?_)
      fun _ h ↦ .inl h
    simp only [PcOk] at hpc25
    rw [hp.label NativeRustcVmX64.Vm.RdRows.label_21_at] at hpc25
    rw [hn] at hkp
    refine fin hp g hR0 hpc25 hf24 (res_some (by rw [hd24, hd]; exact hkp) ?_)
      (by rw [hd24, hd]; exact hchg2)
    rw [hr24 .rbx _ hrbx24, flag_empty fun x hx ↦ by rw [hlen.2 x hx, hrw0]]
    exact merge_val _ (v := 1) (by decide)

/-- **The loop over the leaves** without a row. -/
theorem loopB {i : Nat} {rows : List (List K)} {ci : Nat} {st : MachineState}
    (hI : HeadB k m0 bp B c i rows ci st) : Eventually (step1 Host.exe) (Post m0) st := by
  refine Sym.loop (fun n st ↦ ∃ i rows ci, n = nr m0 - i ∧ HeadB k m0 bp B c i rows ci st)
    (fun n st ⟨i, rows, ci, hn, hI⟩ ↦ ?_) ⟨i, rows, ci, rfl, hI⟩
  subst hn
  refine Eventually.bind (toCallB hp g hI) fun st' hC ↦ Eventually.mono (callB_step hp g hw hR0 hC)
    fun st'' h ↦ ?_
  rcases h with h | ⟨rows', ci', hH⟩
  · exact .inl h
  · exact .inr ⟨nr m0 - (i + 1), by have := hI.rb.lt; omega, i + 1, rows', ci', rfl, hH⟩

end

end

end NativeRustcVmX64.Wire.RdRows
