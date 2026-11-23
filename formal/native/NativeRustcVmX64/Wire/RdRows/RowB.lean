module

public import NativeRustcVmX64.Wire.RdRows.LoopA

/-!
# `rd_rows`' leaves without a row (`rw = 0`): the zeros (x86-64)

The values `b12` computes from `lw` (`e8_eval`, `rem8_eval`, `rbp8_eval`). The loop's registers
after `i` leaves (`RB`: R14 leaf `i`, R12 the leaves' end, R13 `lw % 8`, RBP `8 (lw % 8)`, R15
`8 lw - 8`, the frame's word `8 lw` at `24`). From the loop's head (`HeadB`, `b13`): no zeros
(`lw = 0`), or one zero at a time (`b14`, `b15`, `b16`, `ZB1`) up to `lw % 8`, then eight at a time
(`b17`, `b18`, `b20`, `ZB8`) up to the call (`CallB`): `toCallB`.
-/

namespace NativeRustcVmX64.Wire.RdRows

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmX64.Vm.RdRows
open NativeRustcVmX64.Transcript (Frame frameEnv after after_eq MidOk wordAt_write)
open NativeRustcVm.Transcript (off off_zero off_add off_off)
open NativeRustcVm (WordAt WordsAt)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open NativeRustcVmX64.Wire (pc_cond ite_t ite_f eq64 ult64 toNat_add64)

@[expose] public section

/-- The registers of the loop over leaves without a row, after `i` leaves. -/
structure RB (m0 : MachineData) (i : Nat) (s : MachineData) : Prop where
  fr : Frame m0 80 slots 8 s
  r14 : reg s .r14 = off (lv m0) (512 * i)
  r12 : reg s .r12 = off (lv m0) (512 * nr m0)
  r13 : 0 < lw m0 → reg s .r13 = BitVec.ofNat 64 (lw m0 % 8)
  rbp : 0 < lw m0 → reg s .rbp = BitVec.ofNat 64 (8 * (lw m0 % 8))
  r15 : 0 < lw m0 → reg s .r15 = BitVec.ofNat 64 (8 * lw m0 - 8)
  l24 : WordAt s.dmem (off (sb m0) 24) (UInt64.ofNat (8 * lw m0))
  lt : i < nr m0
  rw0 : rw m0 = 0

variable [Host] (k : Nat) (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c : Nat)

/-- The loop's head (`b13`) at leaf `i`. -/
structure HeadB (i : Nat) (rows : List (List K)) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.RdRows.b13Offset)
  rb : RB m0 i st.data
  kp : Kp m0 bp B c i rows ci st.data.dmem

/-- The one-zero loop (`b16`) after `t` zeros of leaf `i`. -/
structure ZB1 (i t : Nat) (rows : List (List K)) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.RdRows.b16Offset)
  rb : RB m0 i st.data
  kp : Kp m0 bp B c i rows ci st.data.dmem
  rsi : reg st.data .rsi = off (lv m0) (512 * i + 8 * lw m0)
  rax : reg st.data .rax = BitVec.ofNat 64 (8 * t)
  lt : t < lw m0 % 8
  zs : WordsAt st.data.dmem (off (lv m0) (512 * i)) (List.replicate t 0)

/-- Before the eight-zero loop (`b18`), `t = lw % 8` zeros written. -/
structure MB (i t : Nat) (rows : List (List K)) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.RdRows.b18Offset)
  rb : RB m0 i st.data
  kp : Kp m0 bp B c i rows ci st.data.dmem
  rsi : reg st.data .rsi = off (lv m0) (512 * i + 8 * lw m0)
  rax : reg st.data .rax = off (lv m0) (512 * i + 8 * t)
  ht : t = lw m0 % 8
  pos : 0 < lw m0
  zs : WordsAt st.data.dmem (off (lv m0) (512 * i)) (List.replicate t 0)

/-- The eight-zero loop (`b20`) after `t` zeros of leaf `i`. -/
structure ZB8 (i t : Nat) (rows : List (List K)) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.RdRows.b20Offset)
  rb : RB m0 i st.data
  kp : Kp m0 bp B c i rows ci st.data.dmem
  rsi : reg st.data .rsi = off (lv m0) (512 * i + 8 * lw m0)
  rax : reg st.data .rax = off (lv m0) (512 * i + 8 * t)
  md : t % 8 = lw m0 % 8
  le : t + 8 ≤ lw m0
  zs : WordsAt st.data.dmem (off (lv m0) (512 * i)) (List.replicate t 0)

/-- The call (`b21`) for leaf `i`, its zeros written. -/
structure CallB (i : Nat) (rows : List (List K)) (ci : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.RdRows.b21Offset)
  rb : RB m0 i st.data
  kp : Kp m0 bp B c i rows ci st.data.dmem
  rsi : reg st.data .rsi = off (lv m0) (512 * i + 8 * lw m0)
  zs : WordsAt st.data.dmem (off (lv m0) (512 * i)) (List.replicate (lw m0) 0)

end

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat}

/-! ## The values of `b12` -/

theorem toNat_add32 (x y : BitVec 64) :
    (BinOp.apply .add .W32 x y).toNat = (x.toNat % 2 ^ 32 + y.toNat % 2 ^ 32) % 2 ^ 32 := by
  simp only [BinOp.apply, ext, low, BitVec.toNat_setWidth, BitVec.toNat_add, Width.bits]
  omega

theorem toNat_and7_32 (x : BitVec 64) :
    (BinOp.apply .and .W32 x (BitVec.ofNat 64 7)).toNat = x.toNat % 8 := by
  simp only [BinOp.apply, ext, low, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat,
    Width.bits]
  rw [show (7 : Nat) % 2 ^ 64 % 2 ^ 32 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem toNat_shr3_32 (x : BitVec 64) :
    (BinOp.apply .shr .W32 x (BitVec.ofNat 64 3)).toNat = x.toNat % 2 ^ 32 / 8 := by
  have hs : shiftCount .W32 (BitVec.ofNat 64 3) = 3 := by decide
  simp only [BinOp.apply, hs, ext, low, BitVec.toNat_setWidth, BitVec.ushiftRight_eq,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Width.bits]
  omega

theorem toNat_shl3_32 (x : BitVec 64) :
    (BinOp.apply .shl .W32 x (BitVec.ofNat 64 3)).toNat = x.toNat % 2 ^ 32 * 8 % 2 ^ 32 := by
  have hs : shiftCount .W32 (BitVec.ofNat 64 3) = 3 := by decide
  simp only [BinOp.apply, hs, ext, low, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, Width.bits]
  omega

theorem e8_eval [Labels] (env : Env) {x : BitVec 64} (h : env.load 0 8 8 = x) :
    e8.eval env = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  change (BinOp.apply .mul .W64 (env.load 0 8 8) (BitVec.ofNat 64 8)).toNat = _
  rw [h]
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem e8m_eval [Labels] (env : Env) {x : BitVec 64} (h : env.load 0 8 8 = x) (hx : x.toNat ≤ 64)
    (h0 : 0 < x.toNat) : e8m.eval env = BitVec.ofNat 64 (8 * x.toNat - 8) := by
  apply BitVec.eq_of_toNat_eq
  show (BinOp.apply .add .W64 (e8.eval env) (BitVec.ofNat 64 18446744073709551608)).toNat = _
  rw [toNat_add64, e8_eval env h, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem rem8_eval [Labels] (env : Env) {x : BitVec 64} (h : env.load 0 8 8 = x) (hx : x.toNat ≤ 64)
    (h0 : 0 < x.toNat) : rem8.eval env = BitVec.ofNat 64 (x.toNat % 8) := by
  apply BitVec.eq_of_toNat_eq
  show (BinOp.apply .and .W32 (BinOp.apply .add .W32 (BinOp.apply .shr .W32 (e8m.eval env)
    (BitVec.ofNat 64 3)) (BitVec.ofNat 64 1)) (BitVec.ofNat 64 7)).toNat = _
  rw [toNat_and7_32, toNat_add32, toNat_shr3_32, e8m_eval env h hx h0, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem rbp8_eval [Labels] (env : Env) {x : BitVec 64} (h : env.load 0 8 8 = x) (hx : x.toNat ≤ 64)
    (h0 : 0 < x.toNat) :
    (Sym.bin .shl .W32 rem8 (.lit 3)).eval env = BitVec.ofNat 64 (8 * (x.toNat % 8)) := by
  apply BitVec.eq_of_toNat_eq
  show (BinOp.apply .shl .W32 (rem8.eval env) (BitVec.ofNat 64 3)).toNat = _
  rw [toNat_shl3_32, rem8_eval env h hx h0, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-! ## The registers -/

theorem RB.keep {L : Nat} (g : Geo m0 bp L) {i : Nat} {s s' : MachineData} (h : RB m0 i s)
    (hf : Frame m0 80 slots 8 s')
    (hk : ∀ x ∈ [Reg64.rbp, .r12, .r13, .r14, .r15], reg s' x = reg s x)
    {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside s.dmem s'.dmem R)
    (hR : ∀ q, R q → ¬((rspOf m0).toNat - 56 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - 48)) :
    RB m0 i s' := by
  have := g.s0
  refine ⟨hf, (hk .r14 (by simp)).trans h.r14, (hk .r12 (by simp)).trans h.r12,
    fun h0 ↦ (hk .r13 (by simp)).trans (h.r13 h0), fun h0 ↦ (hk .rbp (by simp)).trans (h.rbp h0),
    fun h0 ↦ (hk .r15 (by simp)).trans (h.r15 h0),
    h.l24.of_sameOutside hs fun j hj hq ↦ hR _ hq ?_, h.lt, h.rw0⟩
  simp only [NativeRustcVm.length_wordBytes] at hj
  rw [off_add, g.off_sb (by omega)]
  omega

theorem RB.keepEq {L : Nat} (g : Geo m0 bp L) {i : Nat} {s s' : MachineData} (h : RB m0 i s)
    (hf : Frame m0 80 slots 8 s')
    (hk : ∀ x ∈ [Reg64.rbp, .r12, .r13, .r14, .r15], reg s' x = reg s x)
    (hd : s'.dmem = s.dmem) : RB m0 i s' :=
  h.keep g hf hk (R := fun _ ↦ False) (by rw [hd]; exact NativeRustcVm.SameOutside.refl _ _)
    fun _ h ↦ h.elim

/-- A list of registers within another. -/
theorem mem_of_all {xs ys : List Reg64} (h : (xs.all fun x ↦ ys.any (· == x)) = true) {x : Reg64}
    (hx : x ∈ xs) : x ∈ ys := by
  obtain ⟨y, hy, he⟩ := List.any_eq_true.mp (List.all_eq_true.mp h x hx)
  rwa [Reg64.eq_of_beq he] at hy

/-- No zero before an empty row. -/
theorem flag_empty {rows : List (List K)} (h : ∀ x ∈ rows, x.length = 0) : flag rows = 1 := by
  unfold flag
  rw [ite_t]
  intro x hx
  rw [List.length_eq_zero_iff.mp (h x hx)]
  rfl

variable [Host] {k : Nat}

section
variable (hp : Placed code k) (g : Geo m0 bp B.length)
include hp g

/-- **A zero** (`b16`) of leaf `i`: the loop again, or `b17` to `MB`. -/
theorem zB1_step {i t : Nat} {rows : List (List K)} {ci : Nat} {st : MachineState}
    (hI : ZB1 k m0 bp B c i t rows ci st) :
    Eventually (step1 Host.exe) (fun st' ↦ MB k m0 bp B c i (t + 1) rows ci st' ∨
      ZB1 k m0 bp B c i (t + 1) rows ci st') st := by
  have hlt := hI.lt
  have hli := hI.rb.lt
  have h64 := g.lw64
  have hlv := g.lvNw
  have h0 := g.s0
  have hS := g.lvS
  have hpos : 0 < lw m0 := by omega
  obtain ⟨hmid, hmem, hrax, hK⟩ := ok_b16
  have hin : 512 * i + 8 * t + 8 ≤ 512 * nr m0 := by omega
  refine rg_step hp g (j := NativeRustcVmX64.Vm.RdRows.b16Offset) (y := .bin .add .W64 (.reg .r14) (.reg .rax)) (sz := 8)
    b16_in_code (by simp [b16]) exit_b16 nofun hmid (fun w hw ↦ by
      have h' : w ∈ (after b16 zS).mem := hw
      rw [hmem] at h'
      simp only [List.mem_singleton] at h'
      subst h'
      decide) (o := 512 * i + 8 * t) (by decide) hin rfl hI.pc hI.rb.fr (by
      show BinOp.apply .add .W64 (reg st.data .r14) (reg st.data .rax) = _
      rw [hI.rb.r14, hI.rax, off_add']) fun st' hf' hs' hm' _ hpc' ↦ ?_
  have hk : ∀ x ∈ Reg64.rsi :: loopRegs, reg st'.data x = reg st.data x :=
    regs_kept hK fun r v h ↦ hm'.regs r v h
  have hW : WordAt st'.data.dmem (off (lv m0) (512 * i + 8 * t)) 0 := by
    have := wordAt_write hm' (r := 1) (o := 0) (b := off (lv m0) (512 * i + 8 * t)) rfl
      (by decide) (v := .lit 0) fun u hu ↦ by
        show findWrite 1 (0 + u) (after b16 zS).mem = _
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
  have hrb : RB m0 i st'.data := hI.rb.keep g hf' (fun x hx ↦ hk x (mem_of_all (by decide) hx)) hs'
    fun q hq ↦ by have := hRin q hq; omega
  have hrsi : reg st'.data .rsi = off (lv m0) (512 * i + 8 * lw m0) :=
    (hk .rsi (by simp)).trans hI.rsi
  have hrax' : reg st'.data .rax = BitVec.ofNat 64 (8 * (t + 1)) := by
    rw [show reg st'.data .rax = _ from hm'.regs .rax _ hrax]
    show BinOp.apply .add .W64 (BitVec.ofNat 64 8) (reg st.data .rax) = _
    rw [hI.rax, add_ofNat]
    congr 1
    omega
  have hpc2 := pc_cond hpc' (P := t + 1 ≠ lw m0 % 8) (by
    show (!(CmpOp.apply .eq .W64 (reg st.data .rbp)
      (BinOp.apply .add .W64 (BitVec.ofNat 64 8) (reg st.data .rax)))) = _
    rw [hI.rb.rbp hpos, hI.rax, add_ofNat, eq64, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    omega)
  by_cases hz : t + 1 ≠ lw m0 % 8
  · rw [ite_t hz, hp.label NativeRustcVmX64.Vm.RdRows.label_13_at] at hpc2
    exact .done _ (.inr ⟨hpc2, hrb, hkp, hrsi, hrax', by omega, hzs⟩)
  · rw [ite_f hz] at hpc2
    -- `b17`: the address of the next zero.
    obtain ⟨hok17, hrax17, hK17⟩ := ok_b17
    refine fr_step hp g (j := NativeRustcVmX64.Vm.RdRows.b17Offset) b17_in_code (by simp [b17]) exit_b17 nofun hok17
      (hpc2.trans (congrArg Host.addrOf rfl)) hf' fun s2 hf2 hd2 hr2 hpc3 ↦ ?_
    have hk2 := regs_kept hK17 hr2
    simp only [PcOk] at hpc3
    refine .done _ (.inl ⟨hpc3.trans (congrArg Host.addrOf rfl),
      hrb.keepEq g hf2 (fun x hx ↦ hk2 x (mem_of_all (by decide) hx)) hd2,
      by rw [hd2]; exact hkp, (hk2 .rsi (by simp)).trans hrsi, ?_, by omega, hpos,
      by rw [hd2]; exact hzs⟩)
    rw [hr2 .rax _ hrax17]
    show BinOp.apply .add .W64 (reg st'.data .r14) (reg st'.data .rax) = _
    rw [hrb.r14, hrax', off_add']

end

end

end NativeRustcVmX64.Wire.RdRows
