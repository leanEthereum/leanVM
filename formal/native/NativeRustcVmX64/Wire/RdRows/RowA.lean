module

public import NativeRustcVmX64.Wire.RdRows.Call

/-!
# `rd_rows`' rows of `rw > 0` words (x86-64)

The loop's registers after `i` rows (`RA`: R14 leaf `i`, R12 the leaves' end, RBP `rw`, R15
`8 zc`, BL the flag so far). From the loop's head (`HeadA`, `b5`): no zeros (`zc = 0`) or one zero
at a time (`b6`, `b7`, `ZA`) up to the call (`CallA`, `toCall`); `Reader::words` reads the row
(`b8`), `None` (`b9`, `b1`, the return with `2`) or the flag updated and the next leaf (`b10`):
the head again or the return (`b11`): `callA_step`; the loop over the leaves (`loopA`).
-/

namespace NativeRustcVmX64.Wire.RdRows

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.RdRows
open NativeRustcVmX64.Transcript (Frame frameEnv after after_eq MidOk wordAt_write)
open NativeRustcVm.Transcript (off off_zero off_add off_off)
open NativeRustcVm (WordAt WordsAt)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open NativeRustcVmX64.Wire (pc_cond ite_t ite_f eq64 toNat_add64)

@[expose] public section

/-- The registers of the loop over rows of `rw > 0` words, after `i` rows. -/
structure RA (m0 : MachineData) (i : Nat) (rows : List (List K)) (s : MachineData) : Prop where
  fr : Frame m0 80 slots 8 s
  r14 : reg s .r14 = off (lv m0) (512 * i)
  r12 : reg s .r12 = off (lv m0) (512 * nr m0)
  rbp : reg s .rbp = reg m0 .rcx
  r15 : reg s .r15 = BitVec.ofNat 64 (8 * zc m0)
  bl : (reg s .rbx).toNat % 256 = flag rows
  lt : i < nr m0
  rw0 : 0 < rw m0

variable [Host] (k : Nat) (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c : Nat)

/-- The loop's head (`b5`) at leaf `i`. -/
structure HeadA (i : Nat) (rows : List (List K)) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.RdRows.b5Offset)
  ra : RA m0 i rows st.data
  kp : Kp m0 bp B c i rows ci st.data.dmem

/-- The zeros' loop (`b7`) after `t` zeros of leaf `i`. -/
structure ZA (i t : Nat) (rows : List (List K)) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.RdRows.b7Offset)
  ra : RA m0 i rows st.data
  kp : Kp m0 bp B c i rows ci st.data.dmem
  rax : reg st.data .rax = BitVec.ofNat 64 (8 * t)
  lt : t < zc m0
  zs : WordsAt st.data.dmem (off (lv m0) (512 * i)) (List.replicate t 0)

/-- The call (`b8`) for leaf `i`, its zeros written. -/
structure CallA (i : Nat) (rows : List (List K)) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.RdRows.b8Offset)
  ra : RA m0 i rows st.data
  kp : Kp m0 bp B c i rows ci st.data.dmem
  zs : WordsAt st.data.dmem (off (lv m0) (512 * i)) (List.replicate (zc m0) 0)

end

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}

theorem RA.keep {i : Nat} {rows : List (List K)} {s s' : MachineData} (h : RA m0 i rows s)
    (hf : Frame m0 80 slots 8 s')
    (hk : ∀ x ∈ [Reg64.rbx, .rbp, .r12, .r14, .r15], reg s' x = reg s x) : RA m0 i rows s' :=
  ⟨hf, (hk .r14 (by simp)).trans h.r14, (hk .r12 (by simp)).trans h.r12,
    (hk .rbp (by simp)).trans h.rbp, (hk .r15 (by simp)).trans h.r15,
    by rw [hk .rbx (by simp)]; exact h.bl, h.lt, h.rw0⟩

/-- The registers a block keeps (`Keeps`), from its registers' values. -/
theorem regs_kept [Labels] {S : SState} {xs : List Reg64} (hK : Keeps xs S = true) {s s' : MachineData}
    {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    (hr : ∀ r v, S.reg r = some v → reg s' r = v.eval (Env.ofMachine s rs vars ret)) :
    ∀ x ∈ xs, reg s' x = reg s x :=
  fun x hx ↦ hr x _ (keeps_of hK x hx)

/-- `ofNat` sums. -/
theorem add_ofNat (a b : Nat) :
    BinOp.apply .add .W64 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (a + b) := by
  simp only [BinOp.apply, low_W64, ext_W64]
  exact (BitVec.ofNat_add a b).symm

theorem off_add' (b : BitVec 64) (o i : Nat) :
    BinOp.apply .add .W64 (off b o) (BitVec.ofNat 64 i) = off b (o + i) := by
  simp only [BinOp.apply, low_W64, ext_W64]
  exact off_add b o i

theorem flag_snoc' (rows : List (List K)) (x : List K) {v : Nat} (hv : v = flag rows) :
    (if x.getD 0 0 = 0 then v else 0) = flag (rows ++ [x]) := by
  rw [flag_snoc, hv]

variable [Host] {k : Nat}

section
variable (hp : Placed code k) (g : Geo m0 bp B.length)
include hp g

/-- **A zero** (`b7`) of leaf `i`: the loop again or the call. -/
theorem zA_step {i t : Nat} {rows : List (List K)} {ci : Nat} {st : MachineState}
    (hI : ZA k m0 bp B c i t rows ci st) :
    Eventually (step1 Host.exe) (fun st' ↦ CallA k m0 bp B c i rows ci st' ∨
      ZA k m0 bp B c i (t + 1) rows ci st') st := by
  have hlt := hI.lt
  have hli := hI.ra.lt
  have h64 := g.lw64
  have hlv := g.lvNw
  obtain ⟨hmid, hmem, hrax, hK⟩ := ok_b7
  have hzc : zc m0 ≤ lw m0 := Nat.sub_le _ _
  have hin : 512 * i + 8 * t + 8 ≤ 512 * nr m0 := by omega
  refine rg_step hp g (j := NativeRustcVmX64.Vm.RdRows.b7Offset) (y := .bin .add .W64 (.reg .r14) (.reg .rax)) (sz := 8)
    b7_in_code (by simp [b7]) exit_b7 nofun hmid (fun w hw ↦ by
      have h' : w ∈ (after b7 zS).mem := hw
      rw [hmem] at h'
      simp only [List.mem_singleton] at h'
      subst h'
      decide) (o := 512 * i + 8 * t) (by decide) hin rfl hI.pc hI.ra.fr (by
      show BinOp.apply .add .W64 (reg st.data .r14) (reg st.data .rax) = _
      rw [hI.ra.r14, hI.rax, off_add']) fun st' hf' hs' hm' _ hpc' ↦ ?_
  have hreg := fun r v (h : (after b7 zS).reg r = some v) ↦ hm'.regs r v h
  have hk : ∀ x ∈ loopRegs, reg st'.data x = reg st.data x := regs_kept hK hreg
  have hW : WordAt st'.data.dmem (off (lv m0) (512 * i + 8 * t)) 0 := by
    have := wordAt_write hm' (r := 1) (o := 0) (b := off (lv m0) (512 * i + 8 * t)) rfl
      (by decide) (v := .lit 0) fun u hu ↦ by
        show findWrite 1 (0 + u) (after b7 zS).mem = _
        rw [hmem]
        exact findWrite_head hu
    rwa [off_zero] at this
  have hRin : ∀ q, NativeRustcVm.InRange (off (lv m0) (512 * i + 8 * t)) 8 q →
      (lv m0).toNat + (512 * i + 8 * t) ≤ q.toNat ∧ q.toNat < (lv m0).toNat + (512 * i + 8 * t) + 8 :=
    fun q hq ↦ (inW_iff g hin (by decide)).mp hq
  have hzs : WordsAt st'.data.dmem (off (lv m0) (512 * i)) (List.replicate (t + 1) 0) := by
    refine zeros_snoc (g.words_keep (by simp; omega) hI.zs hs' fun q hq ↦ ?_) ?_
    · have := hRin q hq; simp only [List.length_replicate]; omega
    · rw [off_off]; exact hW
  have hkp : Kp m0 bp B c i rows ci st'.data.dmem :=
    hI.kp.keep g (le_of_lt hli) hs' fun q hq ↦ by
      have := hRin q hq; unfold Mov; omega
  have hra : RA m0 i rows st'.data := hI.ra.keep hf' fun x hx ↦ hk x (by
    simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
  have hrax' : reg st'.data .rax = BitVec.ofNat 64 (8 * (t + 1)) := by
    rw [show reg st'.data .rax = _ from hm'.regs .rax _ hrax]
    show BinOp.apply .add .W64 (BitVec.ofNat 64 8) (reg st.data .rax) = _
    rw [hI.rax, add_ofNat]
    congr 1
    omega
  have hpc2 := pc_cond hpc' (P := t + 1 ≠ zc m0) (by
    show (!(CmpOp.apply .eq .W64 (reg st.data .r15)
      (BinOp.apply .add .W64 (BitVec.ofNat 64 8) (reg st.data .rax)))) = _
    rw [hI.ra.r15, hI.rax, add_ofNat, eq64, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    omega)
  by_cases hz : t + 1 ≠ zc m0
  · rw [ite_t hz, hp.label NativeRustcVmX64.Vm.RdRows.label_6_at] at hpc2
    exact .done _ (.inr ⟨hpc2, hra, hkp, hrax', by omega, hzs⟩)
  · rw [ite_f hz] at hpc2
    have he : t + 1 = zc m0 := by omega
    rw [he] at hzs
    exact .done _ (.inl ⟨hpc2.trans (congrArg Host.addrOf rfl), hra, hkp, hzs⟩)

/-- **The zeros of leaf `i`**: from the loop's head to the call. -/
theorem toCall {i : Nat} {rows : List (List K)} {ci : Nat} {st : MachineState}
    (hI : HeadA k m0 bp B c i rows ci st) :
    Eventually (step1 Host.exe) (CallA k m0 bp B c i rows ci) st := by
  obtain ⟨hok5, hK5⟩ := ok_b5
  refine fr_step hp g (j := NativeRustcVmX64.Vm.RdRows.b5Offset) b5_in_code (by simp [b5]) exit_b5 nofun hok5 hI.pc hI.ra.fr
    fun s1 hf1 hd1 hr1 hpc1 ↦ ?_
  have hk1 := regs_kept hK5 hr1
  have hra1 : RA m0 i rows s1.data := hI.ra.keep hf1 fun x hx ↦ hk1 x (by
    simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
  have hkp1 : Kp m0 bp B c i rows ci s1.data.dmem := by rw [hd1]; exact hI.kp
  have hrl := g.rwlw
  have hzc : zc m0 = lw m0 - rw m0 := rfl
  have hrw : rw m0 = (reg m0 .rcx).toNat := rfl
  have hlw : lw m0 = (reg m0 .rdx).toNat := rfl
  have hpc2 := pc_cond hpc1 (P := zc m0 = 0) (by
    show CmpOp.apply .eq .W64 ((frameEnv m0 st.data 80 []).load 0 8 8) (reg st.data .rbp) = _
    rw [hI.kp.hloc.load_lw, hI.ra.rbp, eq64, Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    omega)
  by_cases hz : zc m0 = 0
  · rw [ite_t hz, hp.label NativeRustcVmX64.Vm.RdRows.label_7_at] at hpc2
    exact .done _ ⟨hpc2, hra1, hkp1, by rw [hz]; exact NativeRustcVm.wordsAt_nil _ _⟩
  rw [ite_f hz] at hpc2
  obtain ⟨hok6, hrax6, hK6⟩ := ok_b6
  refine fr_step hp g (j := NativeRustcVmX64.Vm.RdRows.b6Offset) b6_in_code (by simp [b6]) exit_b6 nofun hok6
    (hpc2.trans (congrArg Host.addrOf rfl)) hra1.fr fun s2 hf2 hd2 hr2 hpc3 ↦ ?_
  have hk2 := regs_kept hK6 hr2
  have hra2 : RA m0 i rows s2.data := hra1.keep hf2 fun x hx ↦ hk2 x (by
    simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
  simp only [PcOk] at hpc3
  have hZ : ZA k m0 bp B c i 0 rows ci s2 :=
    ⟨hpc3.trans (congrArg Host.addrOf rfl), hra2, by rw [hd2]; exact hkp1,
      hr2 .rax _ hrax6, by omega, NativeRustcVm.wordsAt_nil _ _⟩
  refine Sym.loop (fun n st ↦ ∃ t, n = zc m0 - t ∧ ZA k m0 bp B c i t rows ci st)
    (fun n st ⟨t, hn, hZ⟩ ↦ ?_) ⟨0, rfl, hZ⟩
  subst hn
  refine Eventually.mono (zA_step hp g hZ) fun st' h ↦ ?_
  rcases h with h | h
  · exact .inl h
  · exact .inr ⟨zc m0 - (t + 1), by have := hZ.lt; omega, t + 1, rfl, h⟩

end

end

end NativeRustcVmX64.Wire.RdRows
