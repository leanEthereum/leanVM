module

public import NativeRustcVmX64.Wire.RdRows.RowB

/-!
# `rd_rows`' loop over leaves without a row (`rw = 0`) (x86-64)

The eight-zero loop (`b18`, `b19`, `b20`: `mB_step`, `zB8_step`), the zeros of a leaf from the
loop's head (`toCallB`), the call reading no word (`b21`, `b22`) and the next leaf (`b23`): the
head again or the return with `1` (`b24`): `callB_step`; the loop over the leaves (`loopB`).
-/

namespace NativeRustcVmX64.Wire.RdRows

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.RdRows
open NativeRustcVmX64.Transcript (Frame frameEnv after after_eq MidOk wordAt_write)
open NativeRustcVm.Transcript (off off_zero off_add off_off)
open NativeRustcVm (WordAt WordsAt)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open NativeRustcVmX64.Wire (pc_cond ite_t ite_f eq64 ult64 eq32_zero toNat_add64)

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}

theorem rdWords_zero {ci : Nat} (h : ci ≤ B.length) : rdWords B 0 ci = some ([], ci) := by
  simp [rdWords, h]

variable [Host] {k : Nat}

section
variable (hp : Placed code k) (g : Geo m0 bp B.length)
include hp g

/-- **Eight zeros** (`b20`) of leaf `i`: the loop again or the call. -/
theorem zB8_step {i t : Nat} {rows : List (List K)} {ci : Nat} {st : MachineState}
    (hI : ZB8 k m0 bp B c i t rows ci st) :
    Eventually (step1 Host.exe) (fun st' ↦ CallB k m0 bp B c i rows ci st' ∨
      ZB8 k m0 bp B c i (t + 8) rows ci st') st := by
  have hle := hI.le
  have hmd := hI.md
  have hli := hI.rb.lt
  have h64 := g.lw64
  have hlv := g.lvNw
  have h0 := g.s0
  have hS := g.lvS
  obtain ⟨hmid, hmem, hfw, hrax, hK⟩ := ok_b20
  have hin : 512 * i + 8 * t + 64 ≤ 512 * nr m0 := by omega
  refine rg_step hp g (j := NativeRustcVmX64.Vm.RdRows.b20Offset) (y := .reg .rax) (sz := 64) b20_in_code (by simp [b20]) exit_b20
    nofun hmid (fun w hw ↦ by
      obtain ⟨h1, h2, -, -, h5⟩ := hmem w hw
      exact ⟨h1, Nat.zero_le _, by omega⟩) (o := 512 * i + 8 * t) (by decide) hin rfl hI.pc
    hI.rb.fr hI.rax fun st' hf' hs' hm' _ hpc' ↦ ?_
  have hk : ∀ x ∈ Reg64.rsi :: loopRegs, reg st'.data x = reg st.data x :=
    regs_kept hK fun r v h ↦ hm'.regs r v h
  have hW : WordsAt st'.data.dmem (off (lv m0) (512 * i + 8 * t)) (List.replicate 8 0) := by
    refine NativeRustcVm.wordsAt_iff.mpr fun j hj ↦ ?_
    simp only [List.length_replicate] at hj
    rw [List.getElem_replicate]
    exact wordAt_write hm' (r := 1) (o := 8 * j) (b := off (lv m0) (512 * i + 8 * t)) rfl
      (by omega) (v := .lit 0) fun u hu ↦ hfw j hj u hu
  have hRin : ∀ q, NativeRustcVm.InRange (off (lv m0) (512 * i + 8 * t)) 64 q →
      (lv m0).toNat + (512 * i + 8 * t) ≤ q.toNat ∧
        q.toNat < (lv m0).toNat + (512 * i + 8 * t) + 64 :=
    fun q hq ↦ (inW_iff g hin (by decide)).mp hq
  have hzs : WordsAt st'.data.dmem (off (lv m0) (512 * i)) (List.replicate (t + 8) 0) := by
    rw [List.replicate_add, NativeRustcVm.wordsAt_append_iff, List.length_replicate, off_add]
    refine ⟨g.words_keep (by simp; omega) hI.zs hs' fun q hq ↦ ?_, hW⟩
    have := hRin q hq; simp only [List.length_replicate]; omega
  have hkp : Kp m0 bp B c i rows ci st'.data.dmem :=
    hI.kp.keep g (le_of_lt hli) hs' fun q hq ↦ by
      have := hRin q hq; unfold Mov; omega
  have hrb : RB m0 i st'.data := hI.rb.keep g hf' (fun x hx ↦ hk x (mem_of_all (by decide) hx))
    hs' fun q hq ↦ by have := hRin q hq; omega
  have hrsi : reg st'.data .rsi = off (lv m0) (512 * i + 8 * lw m0) :=
    (hk .rsi (by simp)).trans hI.rsi
  have hrax' : reg st'.data .rax = off (lv m0) (512 * i + 8 * (t + 8)) := by
    rw [show reg st'.data .rax = _ from hm'.regs .rax _ hrax]
    show BinOp.apply .add .W64 (BitVec.ofNat 64 64) (reg st.data .rax) = _
    rw [hI.rax, lit_add_off, show 512 * i + 8 * t + 64 = 512 * i + 8 * (t + 8) by omega]
  have hpc2 := pc_cond hpc' (P := t + 8 ≠ lw m0) (by
    show (!(CmpOp.apply .eq .W64 (BinOp.apply .add .W64 (BitVec.ofNat 64 64) (reg st.data .rax))
      (reg st.data .rsi))) = _
    rw [hI.rax, hI.rsi, lit_add_off, eq64, Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    rw [g.off_eq (by omega) (by omega)]
    omega)
  by_cases hz : t + 8 ≠ lw m0
  · rw [ite_t hz, hp.label NativeRustcVmX64.Vm.RdRows.label_16_at] at hpc2
    exact .done _ (.inr ⟨hpc2, hrb, hkp, hrsi, hrax', by omega, by omega, hzs⟩)
  · rw [ite_f hz] at hpc2
    have he : t + 8 = lw m0 := by omega
    rw [he] at hzs
    exact .done _ (.inl ⟨hpc2.trans (congrArg Host.addrOf rfl), hrb, hkp, hrsi, hzs⟩)

/-- **The eight-zero loop** from its set-up (`b18`, `b19`) to the call. -/
theorem mB_step {i t : Nat} {rows : List (List K)} {ci : Nat} {st : MachineState}
    (hI : MB k m0 bp B c i t rows ci st) :
    Eventually (step1 Host.exe) (CallB k m0 bp B c i rows ci) st := by
  have ht := hI.ht
  have hpos := hI.pos
  obtain ⟨hok18, hK18⟩ := ok_b18
  refine fr_step hp g (j := NativeRustcVmX64.Vm.RdRows.b18Offset) b18_in_code (by simp [b18]) exit_b18 nofun hok18 hI.pc hI.rb.fr
    fun s1 hf1 hd1 hr1 hpc1 ↦ ?_
  have hk1 := regs_kept hK18 hr1
  have hrb1 : RB m0 i s1.data :=
    hI.rb.keepEq g hf1 (fun x hx ↦ hk1 x (mem_of_all (by decide) hx)) hd1
  have h64 := g.lw64
  have hpc2 := pc_cond hpc1 (P := lw m0 < 8) (by
    show CmpOp.apply .ult .W64 (reg st.data .r15) (BitVec.ofNat 64 56) = _
    rw [hI.rb.r15 hpos, ult64, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [decide_eq_decide]
    omega)
  have hrsi1 := (hk1 .rsi (by simp)).trans hI.rsi
  by_cases h8 : lw m0 < 8
  · rw [ite_t h8, hp.label NativeRustcVmX64.Vm.RdRows.label_17_at] at hpc2
    have : t = lw m0 := by omega
    subst this
    exact .done _ ⟨hpc2, hrb1, by rw [hd1]; exact hI.kp, hrsi1, by rw [hd1]; exact hI.zs⟩
  rw [ite_f h8] at hpc2
  obtain ⟨hok19, hK19⟩ := ok_b19
  refine fr_step hp g (j := NativeRustcVmX64.Vm.RdRows.b19Offset) b19_in_code (by simp [b19]) exit_b19 nofun hok19
    (hpc2.trans (congrArg Host.addrOf rfl)) hf1 fun s2 hf2 hd2 hr2 hpc3 ↦ ?_
  have hk2 := regs_kept hK19 hr2
  simp only [PcOk] at hpc3
  have hZ : ZB8 k m0 bp B c i t rows ci s2 :=
    ⟨hpc3.trans (congrArg Host.addrOf rfl),
      hrb1.keepEq g hf2 (fun x hx ↦ hk2 x (mem_of_all (by decide) hx)) hd2,
      by rw [hd2, hd1]; exact hI.kp, (hk2 .rsi (by simp)).trans hrsi1,
      (hk2 .rax (by simp)).trans ((hk1 .rax (by simp)).trans hI.rax), by omega, by omega,
      by rw [hd2, hd1]; exact hI.zs⟩
  refine Sym.loop (fun n st ↦ ∃ t, n = lw m0 - t ∧ ZB8 k m0 bp B c i t rows ci st)
    (fun n st ⟨t, hn, hZ⟩ ↦ ?_) ⟨t, rfl, hZ⟩
  subst hn
  refine Eventually.mono (zB8_step hp g hZ) fun st' h ↦ ?_
  rcases h with h | h
  · exact .inl h
  · exact .inr ⟨lw m0 - (t + 8), by have := hZ.le; omega, t + 8, rfl, h⟩

/-- **The zeros of leaf `i`**: from the loop's head to the call. -/
theorem toCallB {i : Nat} {rows : List (List K)} {ci : Nat} {st : MachineState}
    (hI : HeadB k m0 bp B c i rows ci st) :
    Eventually (step1 Host.exe) (CallB k m0 bp B c i rows ci) st := by
  have h64 := g.lw64
  have hli := hI.rb.lt
  have hlw : lw m0 = (reg m0 .rdx).toNat := rfl
  obtain ⟨hok13, hrsi13, hK13⟩ := ok_b13
  refine fr_step hp g (j := NativeRustcVmX64.Vm.RdRows.b13Offset) b13_in_code (by simp [b13]) exit_b13 nofun hok13 hI.pc hI.rb.fr
    fun s1 hf1 hd1 hr1 hpc1 ↦ ?_
  have hk1 := regs_kept hK13 hr1
  have hrb1 : RB m0 i s1.data :=
    hI.rb.keepEq g hf1 (fun x hx ↦ hk1 x (mem_of_all (by decide) hx)) hd1
  have hkp1 : Kp m0 bp B c i rows ci s1.data.dmem := by rw [hd1]; exact hI.kp
  have hrsi1 : reg s1.data .rsi = off (lv m0) (512 * i + 8 * lw m0) := by
    rw [hr1 .rsi _ hrsi13]
    show BinOp.apply .add .W64 (reg st.data .r14) ((frameEnv m0 st.data 80 []).load 0 24 8) = _
    rw [Wire.load_word hI.rb.l24, show (UInt64.ofNat (8 * lw m0)).toBitVec =
      BitVec.ofNat 64 (8 * lw m0) from rfl, hI.rb.r14, off_add']
  have hpc2 := pc_cond hpc1 (P := lw m0 = 0) (by
    show CmpOp.apply .eq .W64 ((frameEnv m0 st.data 80 []).load 0 8 8) (BitVec.ofNat 64 0) = _
    rw [hI.kp.hloc.load_lw, eq64, BitVec.toNat_ofNat])
  by_cases h0 : lw m0 = 0
  · rw [ite_t h0, hp.label NativeRustcVmX64.Vm.RdRows.label_17_at] at hpc2
    exact .done _ ⟨hpc2, hrb1, hkp1, hrsi1, by rw [h0]; exact NativeRustcVm.wordsAt_nil _ _⟩
  rw [ite_f h0] at hpc2
  have hpos : 0 < lw m0 := by omega
  -- `b14`
  obtain ⟨hok14, hrax14, hK14⟩ := ok_b14
  refine fr_step hp g (j := NativeRustcVmX64.Vm.RdRows.b14Offset) b14_in_code (by simp [b14]) exit_b14 nofun hok14
    (hpc2.trans (congrArg Host.addrOf rfl)) hf1 fun s2 hf2 hd2 hr2 hpc3 ↦ ?_
  have hk2 := regs_kept hK14 hr2
  have hrb2 : RB m0 i s2.data :=
    hrb1.keepEq g hf2 (fun x hx ↦ hk2 x (mem_of_all (by decide) hx)) hd2
  have hkp2 : Kp m0 bp B c i rows ci s2.data.dmem := by rw [hd2]; exact hkp1
  have hrsi2 := (hk2 .rsi (by simp)).trans hrsi1
  have hpc4 := pc_cond hpc3 (P := lw m0 % 8 = 0) (by
    show CmpOp.apply .eq .W64 (BinOp.apply .and .W64 (reg s1.data .r13) (reg s1.data .r13))
      (BitVec.ofNat 64 0) = _
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.and_self]
    rw [hrb1.r13 hpos, eq64, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [decide_eq_decide]
    omega)
  by_cases hm : lw m0 % 8 = 0
  · rw [ite_t hm, hp.label NativeRustcVmX64.Vm.RdRows.label_15_at] at hpc4
    exact mB_step hp g (t := 0) ⟨hpc4, hrb2, hkp2, hrsi2, by
      rw [hr2 .rax _ hrax14]
      show reg s1.data .r14 = _
      rw [hrb1.r14]; rfl, by omega, hpos, by
      rw [hd2, hd1]; exact NativeRustcVm.wordsAt_nil _ _⟩
  rw [ite_f hm] at hpc4
  -- `b15`
  obtain ⟨hok15, hrax15, hK15⟩ := ok_b15
  refine fr_step hp g (j := NativeRustcVmX64.Vm.RdRows.b15Offset) b15_in_code (by simp [b15]) exit_b15 nofun hok15
    (hpc4.trans (congrArg Host.addrOf rfl)) hf2 fun s3 hf3 hd3 hr3 hpc5 ↦ ?_
  have hk3 := regs_kept hK15 hr3
  simp only [PcOk] at hpc5
  have hZ : ZB1 k m0 bp B c i 0 rows ci s3 :=
    ⟨hpc5.trans (congrArg Host.addrOf rfl),
      hrb2.keepEq g hf3 (fun x hx ↦ hk3 x (mem_of_all (by decide) hx)) hd3,
      by rw [hd3]; exact hkp2, (hk3 .rsi (by simp)).trans hrsi2, hr3 .rax _ hrax15, by omega,
      NativeRustcVm.wordsAt_nil _ _⟩
  refine Eventually.bind (Sym.loop (Q := fun st ↦ ∃ t, MB k m0 bp B c i t rows ci st)
    (fun n st ↦ ∃ t, n = lw m0 % 8 - t ∧ ZB1 k m0 bp B c i t rows ci st)
    (fun n st ⟨t, hn, hZ⟩ ↦ ?_) ⟨0, rfl, hZ⟩) fun st' ⟨t, hM⟩ ↦ mB_step hp g hM
  subst hn
  refine Eventually.mono (zB1_step hp g hZ) fun st' h ↦ ?_
  rcases h with h | h
  · exact .inl ⟨_, h⟩
  · exact .inr ⟨lw m0 % 8 - (t + 1), by have := hZ.lt; omega, t + 1, rfl, h⟩

end

end

end NativeRustcVmX64.Wire.RdRows
