module

public import NativeRustcVmX64.Wire.PhaseM.Mid
public import NativeRustcVmX64.Code.Vm.RdRows.Names

/-!
# `phase_m`: the rows (x86-64)

`rows_run`: from `rd_rows`' call (`Pre23`, `b23`: the leaves' address to the frame's byte `56`),
`rd_rows`' contract reads the rows into the leaves at the working area's byte `352512`; the rows'
check (`b24`) to `None`, or the hashing's set-up (`b25`: `8 lw` to the frame's byte `64`) to the
first leaf's hash (`HashSt … 0`).
-/

namespace NativeRustcVmX64.Wire.PhaseM

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmX64.Vm.PhaseM
open NativeRustcVmX64.Transcript (Frame frameEnv after after_eq MidOk wordAt_write load_ofMachine
  stackOk_callee mapped_off low8_replaceLow)
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off Mapped.keeps)
open NativeRustcVmX64.Wire.Decode (eqv_eval ult_eval disjoint4)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **Before leaf `i`'s hash** (`b26`). -/
structure HashSt [Labels] [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8)
    (c k count : Nat) (qs : List Nat) (height lw : Nat) (rows : List (List K)) (c6 i : Nat)
    (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b26Offset)
  bod : Bod m0 8 st.data
  mid : Mid m0 B c count qs height lw rows c6 st.data.dmem
  rd : ReaderAt st.data.dmem (RD m0) bp B c6
  rbp : (reg st.data .rbp).toNat = (sortD qs).length
  rbx : reg st.data .rbx = wa m0 2048
  r9 : (reg st.data .r9).toNat = lw
  r13 : (reg st.data .r13).toNat = 513 + 5 * i
  r15 : (reg st.data .r15).toNat = i
  rcx : reg st.data .rcx = wa m0 (352512 + 512 * i)
  f64 : FW m0 st.data.dmem 64 (8 * lw).toUInt64
  ilt : i < (sortD qs).length
  nodes : NodesAt st.data.dmem (wa m0 4096) ((nodes0 qs lw rows).take i)

end

public section

theorem low8_of_mod {x : BitVec 64} {a : Nat} (h : x.toNat % 256 = a) :
    low .W8 x = BitVec.ofNat 8 a := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_low, BitVec.toNat_ofNat]
  show x.toNat % 2 ^ 8 = a % 2 ^ 8
  omega

/-- `b24`'s test: `rd_rows`' `None` (`2`), or its rows all zero (`1`) with a row width. -/
theorem c24_eval [Labels] (env : Sym.Env) {a : Nat} (ha : (env.regs .rax).toNat % 256 = a)
    (ha2 : a ≤ 2) :
    c24.eval env = (decide (a = 2) || (!decide ((env.regs .r15).toNat = 0) && decide (a = 1))) := by
  have hl := low8_of_mod ha
  by_cases hr : (env.regs .r15).toNat = 0
  · have hr' : env.regs .r15 = 0 := BitVec.eq_of_toNat_eq (by rw [hr]; rfl)
    simp only [c24, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
      BitVec.and_self, low8_replaceLow, low_ext, hl, hr']
    rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;> decide
  · have hb : (env.regs .r15 == BitVec.ofNat 64 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro h; apply hr; rw [h]; rfl
    simp only [c24, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
      BitVec.and_self, low8_replaceLow, low_ext, hl, hb, hr]
    rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;> decide

theorem shl3 (x : BitVec 64) (h : x.toNat < 2 ^ 32) :
    (BinOp.apply .shl .W64 x (BitVec.ofNat 64 3)).toNat = 8 * x.toNat := by
  have hs : shiftCount .W64 (BitVec.ofNat 64 3) = 3 := rfl
  simp only [BinOp.apply, low_W64, ext_W64, hs]
  show (x <<< 3).toNat = _
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} [Host] {k : Nat}

/-- **The rows.** -/
theorem rows_run (hp : Placed code k) (G : Geo m0 bp B.length)
    (hrows : Spec (Labels.label NativeRustcVmX64.Vm.RdRows.entryLabel) RdRowsPre RdRowsPost)
    (hR0 : ReaderAt m0.dmem (RD m0) bp B c) {count : Nat} {qs : List Nat}
    {height lw rw c5 : Nat} {st : MachineState} (h : Pre23 m0 bp B c k count qs height lw rw c5 st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      ∃ rows c6, HashSt m0 bp B c k count qs height lw rows c6 0 st') st := by
  obtain ⟨hpc, hchk, h32, h64, hrl, hlast⟩ := h
  obtain ⟨-, hbod, hmod, hql, hc0, hcnt, hqlt, hhl, hlwl, hrwl, hps0, hps256, hf40, hf32, hf16,
    -, hbp, -, hbx, h15, hqW, hpW, hrd⟩ := hchk
  have hsp := G.sp
  have htop := G.top
  have hwn := G.wNw
  have hsR := G.sR
  have hsB := G.sB
  have hsW := G.sW
  have hrW := G.rW
  have hbW := G.bW
  have hrB := G.rB
  have hrn := G.rNw
  have hbn := G.bNw
  have hne : sortD qs ≠ [] := List.ne_nil_of_length_pos hps0
  rw [tail_ok ⟨by unfold wireMaxHeight; omega, by unfold wireMaxLeafWords; omega, hrl, hne,
    hlast⟩] at hmod
  have hw0 := G.wa (o := 0) (by omega)
  have hw2 := G.wa (o := 2048) (by omega)
  have hw3 := G.wa (o := 352512) (by omega)
  -- `b23`: the leaves' address to `56`; `rd_rows`.
  obtain ⟨hmid23, hw23, h56, hdi23, hsi23, hdx23, hcx23, hr823, hk23⟩ := ok_b23
  have hk23' : ∀ x ∈ [Reg64.rbp, .r12, .r14, .r15], (after b23 frS).reg x = some (.reg x) :=
    fun x hx ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact (hk23 .rbp (by simp)).resolve_right (by decide)
      · exact (hk23 .r12 (by simp)).resolve_right (by decide)
      · exact (hk23 .r14 (by simp)).resolve_right (by decide)
      · exact (hk23 .r15 (by simp)).resolve_right (by decide)
  refine wblk hp G b23_in_code (by simp [b23]) exit_b23 hmid23
    (fun w hw ↦ by obtain ⟨h1, h2⟩ := hw23 w hw; exact ⟨h1, by omega, by omega⟩)
    (hk23' .r12 (by simp)) (hk23' .r14 (by simp)) hpc hbod
    fun s1 hb1 hs1 hkeep1 hm1 hpc1 ↦ ?_
  have hdi1 : reg s1.data .rdi = RD m0 := (hm1.regs .rdi _ hdi23).trans hbod.r12
  have hsi1 : (reg s1.data .rsi).toNat = (sortD qs).length := by
    rw [show reg s1.data .rsi = reg st.data .rbp from hm1.regs .rsi _ hsi23]; exact hbp
  have hlw : lw.toUInt64.toBitVec.toNat = lw := by
    rw [UInt64.toNat_toBitVec, toNat_toUInt64 (by omega)]
  have hdx1 : (reg s1.data .rdx).toNat = lw := by
    rw [show reg s1.data .rdx = _ from hm1.regs .rdx _ hdx23]
    simp only [Sym.eval]
    rw [load_ofMachine (o := 16) rfl hf16, hlw]
  have hcx1 : (reg s1.data .rcx).toNat = rw := by
    rw [show reg s1.data .rcx = reg st.data .r15 from hm1.regs .rcx _ hcx23]; exact h15
  have hr81 : reg s1.data .r8 = wa m0 352512 := by
    rw [show reg s1.data .r8 = _ from hm1.regs .r8 _ hr823]
    show BinOp.apply .add .W64 (reg st.data .r14) (BitVec.ofNat 64 352512) = _
    rw [hbod.r14, add_off]
  have hf56 : FW m0 s1.data.dmem 56 (UInt64.ofBitVec (wa m0 352512)) := by
    have := wordAt_write hm1 (r := 0) (o := 56) rfl (by omega) h56
    have e : (Sym.bin .add .W64 (.reg .r14) (.lit 352512)).eval (frameEnv m0 st.data 160 []
        (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b23Offset + b23.length)).toBitVec) = wa m0 352512 := by
      show BinOp.apply .add .W64 (reg st.data .r14) (BitVec.ofNat 64 352512) = _
      rw [hbod.r14, add_off]
    rw [e] at this
    exact this
  have hk1 : ∀ o v, o = 16 ∨ o = 32 ∨ o = 40 → FW m0 st.data.dmem o v → FW m0 s1.data.dmem o v :=
    fun o v ho hf ↦ hkeep1 o v (by omega) (fun w hw _ ↦ by have := hw23 w hw; omega) hf
  have hrd1 : ReaderAt s1.data.dmem (RD m0) bp B c5 :=
    reader_keep hrd hs1 (fun q hq ↦ by omega) (fun q hq ↦ by omega)
  have hqW1 : NativeRustcVm.WordsAt s1.data.dmem (wa m0 0) (qs.map Nat.toUInt64) := by
    refine wordsAt_keep hqW hs1 (by rw [List.length_map, hw0]; omega) fun q hq ↦ ?_
    rw [List.length_map, hw0]; omega
  have hpW1 : NativeRustcVm.WordsAt s1.data.dmem (wa m0 2048) ((sortD qs).map Nat.toUInt64) := by
    refine wordsAt_keep hpW hs1 (by rw [List.length_map, hw2]; omega) fun q hq ↦ ?_
    rw [List.length_map, hw2]; omega
  have hsp1 : rspOf s1.data = stackBelow m0 160 := by rw [hb1.fr.sp, off_zero]
  have hRS : rdRowsStack = 128 := rfl
  obtain ⟨hcs1, -⟩ := callee_toNat (n := rdRowsStack) hsp1 (by rw [hRS]; omega)
  have hpre : RdRowsPre s1.data := by
    refine ⟨stackOk_callee G.st hb1.fr.kept hsp1 (by rw [hRS]; omega), by rw [hsi1]; omega,
      by rw [hsi1]; omega, by rw [hdx1]; omega, by rw [hcx1, hdx1]; omega, ?_, bp, B, c5,
      by rw [hdi1]; exact hrd1, ?_⟩
    · rw [hr81, hsi1]
      exact ⟨mapped_off (N := 483584) (o := 352512) (k := 512 * (sortD qs).length)
        (Mapped.keeps G.wOk.1 hb1.fr.kept) (by omega),
        show (wa m0 352512).toNat + 512 * (sortD qs).length ≤ 2 ^ 64 by rw [hw3]; omega⟩
    · rw [hdi1, hr81, hsi1]
      exact disjoint4 (by rw [hcs1, hRS]; omega) (by rw [hcs1, hRS]; omega)
        (by rw [hcs1, hRS, hw3]; omega) (by omega) (by rw [hw3]; omega) (by rw [hw3]; omega)
  simp only [PcOk] at hpc1
  refine call_then (env := frameEnv m0 st.data 160 [] (fun _ ↦ 0)
    (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b23Offset + b23.length)).toBitVec)
    (l := NativeRustcVmX64.Vm.RdRows.entryLabel) ⟨hpc1.1, hpc1.2⟩ hrows hpre
    fun s2 hpc2 hrsp2 ⟨hres2, hso2, hsv2⟩ ↦ ?_
  rw [hdi1, hsi1, hcx1, hdx1, hr81] at hres2
  rw [hdi1] at hso2
  rw [hr81] at hso2
  rw [hsi1] at hso2
  have hres := hres2 bp B c5 hrd1
  have h16 : (off (RD m0) 16).toNat = (RD m0).toNat + 16 := toNat_off (by omega)
  have hso2' : NativeRustcVm.SameOutside s1.data.dmem s2.data.dmem (fun q ↦
      ((WK m0).toNat + 352512 ≤ q.toNat ∧
        q.toNat < (WK m0).toNat + 352512 + 512 * (sortD qs).length) ∨
      ((RD m0).toNat + 16 ≤ q.toNat ∧ q.toNat < (RD m0).toNat + 24) ∨
      (SP0 m0 - 288 ≤ q.toNat ∧ q.toNat < SP0 m0 - 160)) :=
    hso2.mono fun q ⟨R, hR, hq⟩ ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl | rfl
      · have hq' : NativeRustcVm.InRange (wa m0 352512) (512 * (sortD qs).length) q := hq
        have := iv_of_inRange (by rw [hw3]; omega) hq'
        rw [hw3] at this; exact .inl ⟨by omega, by omega⟩
      · have hq' : NativeRustcVm.InRange (off (RD m0) 16) 8 q := hq
        have := iv_of_inRange (by rw [h16]; omega) hq'
        rw [h16] at this; exact .inr (.inl ⟨by omega, by omega⟩)
      · have hq' : NativeRustcVm.InRange (stackBelow s1.data rdRowsStack) rdRowsStack q := hq
        have := iv_of_inRange (by rw [hcs1, hRS]; omega) hq'
        rw [hcs1, hRS] at this; exact .inr (.inr ⟨by omega, by omega⟩)
  have hb2 : Bod m0 8 s2.data := Bod.call G hb1 hsv2 hrsp2 hso2' fun q hq ↦
    ⟨by unfold Chg; omega, by omega⟩
  have hk2 : ∀ o v, o + 8 ≤ 168 → FW m0 s1.data.dmem o v → FW m0 s2.data.dmem o v :=
    fun o v ho hf ↦ hf.keep G ho hso2' fun q hq ↦ by omega
  have hqW2 : NativeRustcVm.WordsAt s2.data.dmem (wa m0 0) (qs.map Nat.toUInt64) := by
    refine wordsAt_keep hqW1 hso2' (by rw [List.length_map, hw0]; omega) fun q hq ↦ ?_
    rw [List.length_map, hw0]; omega
  have hpW2 : NativeRustcVm.WordsAt s2.data.dmem (wa m0 2048) ((sortD qs).map Nat.toUInt64) := by
    refine wordsAt_keep hpW1 hso2' (by rw [List.length_map, hw2]; omega) fun q hq ↦ ?_
    rw [List.length_map, hw2]; omega
  have rk2 : ∀ x ∈ [Reg64.rbp, .rbx, .r15], reg s2.data x = reg st.data x := fun x hx ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact (hsv2.1 .rbp rfl).trans (hm1.regs .rbp _ (hk23' .rbp (by simp)))
    · exact (hsv2.1 .rbx rfl).trans (hm1.regs .rbx (.reg .rbx) (by decide +kernel))
    · exact (hsv2.1 .r15 rfl).trans (hm1.regs .r15 _ (hk23' .r15 (by simp)))
  -- `b24`: the rows' check.
  obtain ⟨hok24, hk24⟩ := ok_b24
  refine fblk hp G b24_in_code (by simp [b24]) exit_b24 nofun hok24 (hk24 .r12 (by simp))
    (hk24 .r14 (by simp)) (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b23_next)) hb2
    fun s3 hb3 hd3 hm3 hpc3 ↦ ?_
  simp only [PcOk] at hpc3
  have h15e : ((frameEnv m0 s2.data 160 []).regs .r15).toNat = rw := by
    show (reg s2.data .r15).toNat = rw
    rw [rk2 .r15 (by simp)]; exact h15
  rcases hrr : rdRows B rw (sortD qs).length c5 with _ | ⟨rows, c6⟩
  · rw [hrr] at hres
    rw [c24_eval (frameEnv m0 s2.data 160 []) (a := 2)
      (show (reg s2.data .rax).toNat % 256 = 2 from hres) (by omega)] at hpc3
    simp only [decide_true, Bool.true_or, ↓reduceIte] at hpc3
    rw [hp.label NativeRustcVmX64.Vm.PhaseM.label_23_at] at hpc3
    refine Eventually.mono (none_run hp G hR0 hpc3 hb3 ?_) fun _ h ↦ .inl h
    rw [hmod, hrr]
  rw [hrr] at hres
  obtain ⟨hflag, hlv, hrd2⟩ := hres
  obtain ⟨hlen, hrw⟩ := rdRows_length (B := B) rw (sortD qs).length hrr
  have hc : c24.eval (frameEnv m0 s2.data 160 []) =
      decide (0 < rw ∧ ∀ x ∈ rows, x.getD 0 0 = 0) := by
    unfold boolRet at hflag
    split at hflag
    · next hz =>
      rw [c24_eval (frameEnv m0 s2.data 160 []) (a := 1) hflag (by omega), h15e]
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
        decide_eq_false_iff_not]
      constructor
      · rintro (h | ⟨h, -⟩)
        · omega
        · exact ⟨by omega, hz⟩
      · rintro ⟨h, -⟩
        exact .inr ⟨by omega, by simp⟩
    · next hz =>
      rw [c24_eval (frameEnv m0 s2.data 160 []) (a := 0) hflag (by omega)]
      have hf : decide (0 < rw ∧ ∀ x ∈ rows, x.getD 0 0 = 0) = false :=
        decide_eq_false fun h ↦ hz h.2
      rw [hf]
      simp
  rw [hc] at hpc3
  by_cases hbad : 0 < rw ∧ ∀ x ∈ rows, x.getD 0 0 = 0
  · rw [decide_eq_true hbad] at hpc3
    simp only [↓reduceIte] at hpc3
    rw [hp.label NativeRustcVmX64.Vm.PhaseM.label_23_at] at hpc3
    refine Eventually.mono (none_run hp G hR0 hpc3 hb3 ?_) fun _ h ↦ .inl h
    rw [hmod, hrr]
    exact ite_eq_left_of_eq_true _ _ (eq_true hbad)
  rw [decide_eq_false hbad] at hpc3
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc3
  have hmod' : phaseM B c = climbFin B qs height lw rows c6 := by
    rw [hmod, hrr]
    exact ite_eq_right_of_eq_false _ _ (eq_false hbad)
  -- `b25`: the hashing's set-up.
  obtain ⟨hmid25, hmem25, hw64, hcx25, hr925, h1325, h1525, hk25⟩ := ok_b25
  refine wblk hp G b25_in_code (by simp [b25]) exit_b25 hmid25
    (fun w hw ↦ by rw [hmem25] at hw; simp only [List.mem_singleton] at hw; subst hw; decide)
    (hk25 .r12 (by simp)) (hk25 .r14 (by simp))
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b24_next)) hb3 fun s4 hb4 hs4 hkeep4 hm4 hpc4 ↦ ?_
  have hmiss : ∀ o, o = 16 ∨ o = 32 ∨ o = 40 ∨ o = 56 → ∀ w ∈ (after b25 frS).mem, w.r = 0 →
      w.off + w.n ≤ o ∨ o + 8 ≤ w.off := fun o ho w hw _ ↦ by
    rw [hmem25] at hw; simp only [List.mem_singleton] at hw; subst hw
    rcases ho with rfl | rfl | rfl | rfl <;> decide
  have hk4 : ∀ o v, o = 16 ∨ o = 32 ∨ o = 40 ∨ o = 56 → FW m0 s1.data.dmem o v →
      FW m0 s4.data.dmem o v := fun o v ho hf ↦
    hkeep4 o v (by omega) (hmiss o ho) (by rw [hd3]; exact hk2 o v (by omega) hf)
  have hl16 : (frameEnv m0 s3.data 160 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b25Offset + b25.length)).toBitVec).load 0 16 8 = lw.toUInt64.toBitVec :=
    load_ofMachine (o := 16) rfl (by rw [hd3]; exact hk2 16 _ (by omega) (hk1 16 _ (by omega) hf16))
  have hf64 : FW m0 s4.data.dmem 64 (8 * lw).toUInt64 := by
    have := wordAt_write hm4 (r := 0) (o := 64) rfl (by omega) hw64
    simp only [Sym.eval] at this
    rw [hl16, toNat_reg_eq (shl3 _ (by rw [hlw]; omega)), hlw] at this
    exact this
  have hrange : ∀ q : BitVec 64, (SP0 m0 - 160 ≤ q.toNat ∧ q.toNat < SP0 m0 - 48) →
      q.toNat < (RD m0).toNat ∨ (RD m0).toNat + 24 ≤ q.toNat := fun q hq ↦ by omega
  have hrd4 : ReaderAt s4.data.dmem (RD m0) bp B c6 :=
    reader_keep (by rw [hd3]; exact hrd2) hs4 hrange (fun q hq ↦ by omega)
  have hmid : Mid m0 B c count qs height lw rows c6 s4.data.dmem := by
    refine ⟨hmod', hql, hc0, hcnt, hqlt, by omega, by omega, hps0, hps256, hlen,
      fun r hr ↦ by rw [hrw r hr]; exact hrl, hk4 16 _ (by omega) (hk1 16 _ (by omega) hf16),
      hk4 32 _ (by omega) (hk1 32 _ (by omega) hf32), hk4 40 _ (by omega) (hk1 40 _ (by omega) hf40),
      hk4 56 _ (by omega) hf56, ?_, ?_, ?_⟩
    · refine wordsAt_keep (by rw [hd3]; exact hqW2) hs4 (by rw [List.length_map, hw0]; omega)
        fun q hq ↦ ?_
      rw [List.length_map, hw0]; omega
    · refine wordsAt_keep (by rw [hd3]; exact hpW2) hs4 (by rw [List.length_map, hw2]; omega)
        fun q hq ↦ ?_
      rw [List.length_map, hw2]; omega
    · have hl : (leavesOf lw rows).length = (sortD qs).length := by simp [hlen]
      refine leaves_keep (by rw [hd3]; exact hlv) hs4 (fun x hx ↦ ?_) (by rw [hl, hw3]; omega)
        fun q hq ↦ ?_
      · simp only [leavesOf, List.mem_map] at hx
        obtain ⟨r, hr, rfl⟩ := hx
        rw [length_paddedLeaf (by rw [hrw r hr]; exact hrl)]; omega
      · rw [hl, hw3]; omega
  have rk4 : ∀ x ∈ [Reg64.rbp, .rbx], reg s4.data x = reg st.data x := fun x hx ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [show reg s4.data .rbp = reg s3.data .rbp from hm4.regs .rbp _ (hk25 .rbp (by simp)),
        show reg s3.data .rbp = reg s2.data .rbp from hm3.regs .rbp _ (hk24 .rbp (by simp))]
      exact rk2 .rbp (by simp)
    · rw [show reg s4.data .rbx = reg s3.data .rbx from hm4.regs .rbx (.reg .rbx) (by decide +kernel),
        show reg s3.data .rbx = reg s2.data .rbx from hm3.regs .rbx (.reg .rbx) (by decide +kernel)]
      exact rk2 .rbx (by simp)
  refine .done _ (.inr ⟨rows, c6, ⟨hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b25_next), hb4, hmid,
    hrd4, by rw [rk4 .rbp (by simp)]; exact hbp, by rw [rk4 .rbx (by simp)]; exact hbx, ?_, ?_, ?_,
    ?_, hf64, hps0, fun i hi ↦ absurd hi (by simp)⟩⟩)
  · rw [show reg s4.data .r9 = _ from hm4.regs .r9 _ hr925]
    simp only [Sym.eval]
    rw [hl16, hlw]
  · rw [show reg s4.data .r13 = _ from hm4.regs .r13 _ h1325]; rfl
  · rw [show reg s4.data .r15 = _ from hm4.regs .r15 _ h1525]; rfl
  · rw [show reg s4.data .rcx = _ from hm4.regs .rcx _ hcx25]
    show BinOp.apply .add .W64 (reg s3.data .r14) (BitVec.ofNat 64 352512) = _
    rw [hb3.r14, add_off]

end

end NativeRustcVmX64.Wire.PhaseM
