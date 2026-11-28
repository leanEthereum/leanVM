module

public import NativeRustcVmX64.Wire.PhaseM.Rest
public import NativeRustcVmX64.Code.Vm.ReaderLe.Names

/-!
# `phase_m`: the leaf width and the row width (x86-64)

`lw_run`: the leaf width (`b9`, `b10`: to the frame's byte `16`). `rw_run`: the row width and the
query count's check (`b11`, `b12`), stored at `24` with the sort's registers (`b13`), to the
sort's head (`SortSt … 0`). `reads_run`: every read, from the entry.
-/

namespace NativeRustcVmX64.Wire.PhaseM

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmX64.Vm.PhaseM
open NativeRustcVmX64.Transcript (Frame frameEnv after after_eq MidOk wordAt_write load_ofMachine)
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off)
open NativeRustcVmX64.Wire.Decode (eqv_eval)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- **The leaf width read** (`b11`). -/
structure At11 [Labels] [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c k : Nat)
    (count : Nat) (qs : List Nat) (height lw c4 : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b11Offset)
  bod : Bod m0 8 st.data
  model : phaseM B c = match rdU32 B c4 with
    | none => none
    | some (rw, c5) => tail B qs height lw rw c5
  len : qs.length = count
  cnt : count ≤ 256
  qlt : ∀ q ∈ qs, q < 2 ^ 32
  hlt : height < 2 ^ 32
  lwlt : lw < 2 ^ 32
  f40 : FW m0 st.data.dmem 40 count.toUInt64
  f32 : FW m0 st.data.dmem 32 height.toUInt64
  f16 : FW m0 st.data.dmem 16 lw.toUInt64
  r13 : (reg st.data .r13).toNat = 8 * count
  qsW : NativeRustcVm.WordsAt st.data.dmem (wa m0 0) (qs.map Nat.toUInt64)
  rd : ReaderAt st.data.dmem (RD m0) bp B c4

end

public section

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} [Host] {k : Nat}

/-- **The leaf width.** -/
theorem lw_run (hp : Placed code k) (G : Geo m0 bp B.length)
    (hle : Spec (Labels.label NativeRustcVmX64.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    (hR0 : ReaderAt m0.dmem (RD m0) bp B c) {count : Nat} {qs : List Nat} {height c3 : Nat}
    {st : MachineState} (h : At9 m0 bp B c k count qs height c3 st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      ∃ lw c4, At11 m0 bp B c k count qs height lw c4 st') st := by
  obtain ⟨hpc, hbod, hmod, hlen, hcnt, hqlt, hhl, hf40, hf32, h13, hqW, hrd⟩ := h
  have hsp := G.sp
  have htop := G.top
  have hwn := G.wNw
  have hsR := G.sR
  have hsB := G.sB
  have hsW := G.sW
  have hrW := G.rW
  have hrn := G.rNw
  -- `b9`: `Reader::le`.
  obtain ⟨hmid9, hw9, hsi9, hdi9, hk9⟩ := ok_b9
  refine le4 hp G hle b9_in_code (by simp [b9]) exit_b9 hmid9 hw9 hsi9 hdi9 (hk9 .r12 (by simp))
    (hk9 .r14 (by simp)) hpc hbod hrd fun s1 m2 hb2 hm1 hcs2 hs2 hr2 ↦ ?_
  have e13 : reg m2 .r13 = reg st.data .r13 :=
    (hcs2 .r13 rfl).trans (hm1.regs .r13 _ (hk9 .r13 (by simp)))
  -- `b10`: the leaf width to `16`, its tag.
  obtain ⟨hmid10, hmem10, hw16, hk10⟩ := ok_b10
  refine wblk hp G b10_in_code (by simp [b10]) exit_b10 hmid10
    (fun w hw ↦ by rw [hmem10] at hw; simp only [List.mem_singleton] at hw; subst hw; decide)
    (hk10 .r12 (by simp)) (hk10 .r14 (by simp)) (st := ⟨m2, _⟩) rfl hb2
    fun s3 hb3 hs3 hkeep3 hm3 hpc3 ↦ ?_
  simp only [PcOk] at hpc3
  have ea : (frameEnv m0 m2 160 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b10Offset + b10.length)).toBitVec).regs
      .rax = reg m2 .rax := rfl
  rcases read4_cases hr2 with ⟨hn, h0⟩ | ⟨lw, hv, h0, hdx, hll, hR4⟩
  · rw [rax_ne1_eval _ (by rw [ea]; exact .inl h0), ea, h0] at hpc3
    simp only [decide_true, ↓reduceIte] at hpc3
    rw [hp.label NativeRustcVmX64.Vm.PhaseM.label_23_at] at hpc3
    refine Eventually.mono (none_run hp G hR0 hpc3 hb3 ?_) fun _ h ↦ .inl h
    rw [hmod, hn]
  rw [rax_ne1_eval _ (by rw [ea]; exact .inr h0), ea, h0] at hpc3
  simp only [show ¬ ((1 : BitVec 64) = 0) by decide, decide_false, Bool.false_eq_true,
    ↓reduceIte] at hpc3
  have hmem : ∀ o, o = 32 ∨ o = 40 → ∀ w ∈ (after b10 frS).mem, w.r = 0 →
      w.off + w.n ≤ o ∨ o + 8 ≤ w.off := fun o ho w hw _ ↦ by
    rw [hmem10] at hw; simp only [List.mem_singleton] at hw; subst hw
    rcases ho with rfl | rfl <;> decide
  have hf16 : FW m0 s3.data.dmem 16 lw.toUInt64 := by
    have := wordAt_write hm3 (r := 0) (o := 16) rfl (by omega) hw16
    simp only [Sym.eval, Env.ofMachine_regs] at this
    rw [show m2.regs.get64 .rdx = reg m2 .rdx from rfl, toNat_reg_eq hdx] at this
    exact this
  have hkf : ∀ o v, o = 32 ∨ o = 40 → FW m0 st.data.dmem o v → FW m0 s3.data.dmem o v :=
    fun o v ho hf ↦ hkeep3 o v (by omega) (hmem o ho) (hf.keep G (by omega) hs2 fun q hq ↦ by
      rcases hq with hq | hq <;> omega)
  have hR3 : ReaderAt s3.data.dmem (RD m0) bp B (c3 + 4) :=
    reader_keep hR4 hs3 (fun q hq ↦ by omega) (fun q hq ↦ by omega)
  have hqW3 : NativeRustcVm.WordsAt s3.data.dmem (wa m0 0) (qs.map Nat.toUInt64) := by
    have hw0 := G.wa (o := 0) (by omega)
    refine wordsAt_keep hqW (hs2.trans hs3) (by rw [List.length_map, hw0]; omega) fun q hq ↦ ?_
    rw [List.length_map, hw0]
    rcases hq with (hq | hq) | hq <;> omega
  have e13' : reg s3.data .r13 = reg m2 .r13 := hm3.regs .r13 _ (hk10 .r13 (by simp))
  refine .done _ (.inr ⟨lw, c3 + 4, ⟨hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b10_next), hb3,
    by rw [hmod, hv]; rfl, hlen, hcnt, hqlt, hhl, hll, hkf 40 _ (.inr rfl) hf40, hkf 32 _ (.inl rfl) hf32,
    hf16, by rw [e13', e13]; exact h13, hqW3, hR3⟩⟩)

/-- **The row width**: to the sort's head. -/
theorem rw_run (hp : Placed code k) (G : Geo m0 bp B.length)
    (hle : Spec (Labels.label NativeRustcVmX64.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    (hR0 : ReaderAt m0.dmem (RD m0) bp B c) {count : Nat} {qs : List Nat} {height lw c4 : Nat}
    {st : MachineState} (h : At11 m0 bp B c k count qs height lw c4 st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      ∃ rw c5, SortSt m0 bp B c k count qs height lw rw c5 0 st') st := by
  obtain ⟨hpc, hbod, hmod, hlen, hcnt, hqlt, hhl, hll, hf40, hf32, hf16, h13, hqW, hrd⟩ := h
  have hsp := G.sp
  have htop := G.top
  have hwn := G.wNw
  have hsR := G.sR
  have hsB := G.sB
  have hsW := G.sW
  have hrW := G.rW
  have hrn := G.rNw
  -- `b11`: the query count's flag, `Reader::le`.
  obtain ⟨hmid11, hw11, hsi11, hdi11, hbp11, hk11⟩ := ok_b11
  refine le4 hp G hle b11_in_code (by simp [b11]) exit_b11 hmid11 hw11 hsi11 hdi11
    (hk11 .r12 (by simp)) (hk11 .r14 (by simp)) hpc hbod hrd fun s1 m2 hb2 hm1 hcs2 hs2 hr2 ↦ ?_
  have e13 : reg m2 .r13 = reg st.data .r13 :=
    (hcs2 .r13 rfl).trans (hm1.regs .r13 _ (hk11 .r13 (by simp)))
  have hl40 : ((frameEnv m0 st.data 160 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b11Offset + b11.length)).toBitVec).load 0 40 8).toNat = count := by
    rw [load_ofMachine (o := 40) rfl hf40, UInt64.toNat_toBitVec, toNat_toUInt64 (by omega)]
  have hbp2 : reg m2 .rbp = BinOp.apply .merge .W8 (reg st.data .rbp)
      (if CmpOp.apply .eq .W64 ((frameEnv m0 st.data 160 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b11Offset + b11.length)).toBitVec).load 0 40 8) (BitVec.ofNat 64 0) = true
        then BitVec.ofNat 64 1 else BitVec.ofNat 64 0) :=
    (hcs2 .rbp rfl).trans (hm1.regs .rbp _ hbp11)
  have hz : CmpOp.apply .eq .W64 ((frameEnv m0 st.data 160 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b11Offset + b11.length)).toBitVec).load 0 40 8) (BitVec.ofNat 64 0) =
      decide (count = 0) := by
    rw [eqv_eval, hl40]; rfl
  rw [hz] at hbp2
  -- `b12`: the tag, a query.
  obtain ⟨hok12, hk12⟩ := ok_b12
  refine fblk hp G b12_in_code (by simp [b12]) exit_b12 nofun hok12 (hk12 .r12 (by simp))
    (hk12 .r14 (by simp)) (st := ⟨m2, _⟩) (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b11_next) hb2
    fun s3 hb3 hd3 hm3 hpc3 ↦ ?_
  simp only [PcOk] at hpc3
  have ea : (frameEnv m0 m2 160 []).regs .rax = reg m2 .rax := rfl
  have eb : (frameEnv m0 m2 160 []).regs .rbp = reg m2 .rbp := rfl
  rcases read4_cases hr2 with ⟨hn, h0⟩ | ⟨rw, hv, h0, hdx, hrl, hR4⟩
  · rw [c12_eval _ (by rw [ea]; exact .inl h0) (by rw [eb]; exact hbp2), ea, h0] at hpc3
    simp only [show decide ((0 : BitVec 64) = 1) = false by decide, Bool.false_and,
      Bool.not_false, ↓reduceIte] at hpc3
    rw [hp.label NativeRustcVmX64.Vm.PhaseM.label_23_at] at hpc3
    refine Eventually.mono (none_run hp G hR0 hpc3 hb3 ?_) fun _ h ↦ .inl h
    rw [hmod, hn]
  rw [c12_eval _ (by rw [ea]; exact .inr h0) (by rw [eb]; exact hbp2), ea, h0] at hpc3
  by_cases hc0 : count = 0
  · simp only [hc0, decide_true, Bool.not_true, Bool.and_false, Bool.not_false,
      ↓reduceIte] at hpc3
    rw [hp.label NativeRustcVmX64.Vm.PhaseM.label_23_at] at hpc3
    refine Eventually.mono (none_run hp G hR0 hpc3 hb3 ?_) fun _ h ↦ .inl h
    rw [hmod, hv]
    simp only
    rw [List.eq_nil_of_length_eq_zero (hlen.trans hc0), tail_nil]
  simp only [hc0, decide_false, Bool.not_false, Bool.and_true, decide_true, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte] at hpc3
  have rk3 : ∀ x ∈ [Reg64.rdx, .r13], reg s3.data x = reg m2 x := fun x hx ↦
    hm3.regs x _ (hk12 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl <;> simp))
  -- `b13`: the row width to `24`, the sort's registers.
  obtain ⟨hmid13, hmem13, hw24, hdi13, hbp13, h15_13, hk13⟩ := ok_b13
  refine wblk hp G b13_in_code (by simp [b13]) exit_b13 hmid13
    (fun w hw ↦ by rw [hmem13] at hw; simp only [List.mem_singleton] at hw; subst hw; decide)
    (hk13 .r12 (by simp)) (hk13 .r14 (by simp)) (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b12_next))
    hb3 fun s4 hb4 hs4 hkeep4 hm4 hpc4 ↦ ?_
  have hmem : ∀ o, o = 16 ∨ o = 32 ∨ o = 40 → ∀ w ∈ (after b13 frS).mem, w.r = 0 →
      w.off + w.n ≤ o ∨ o + 8 ≤ w.off := fun o ho w hw _ ↦ by
    rw [hmem13] at hw; simp only [List.mem_singleton] at hw; subst hw
    rcases ho with rfl | rfl | rfl <;> decide
  have hkf : ∀ o v, o = 16 ∨ o = 32 ∨ o = 40 → FW m0 st.data.dmem o v → FW m0 s4.data.dmem o v :=
    fun o v ho hf ↦ hkeep4 o v (by omega) (hmem o ho) (by
      rw [hd3]; exact hf.keep G (by omega) hs2 fun q hq ↦ by rcases hq with hq | hq <;> omega)
  have hf24 : FW m0 s4.data.dmem 24 rw.toUInt64 := by
    have := wordAt_write hm4 (r := 0) (o := 24) rfl (by omega) hw24
    simp only [Sym.eval, Env.ofMachine_regs] at this
    rw [show s3.data.regs.get64 .rdx = reg s3.data .rdx from rfl, rk3 .rdx (by simp),
      toNat_reg_eq hdx] at this
    exact this
  have hR4' : ReaderAt s4.data.dmem (RD m0) bp B (c4 + 4) := by
    refine reader_keep (by rw [hd3]; exact hR4) hs4 (fun q hq ↦ by omega) (fun q hq ↦ by omega)
  have hqW4 : NativeRustcVm.WordsAt s4.data.dmem (wa m0 0) (qs.map Nat.toUInt64) := by
    have hw0 := G.wa (o := 0) (by omega)
    have hs4' := hs4
    rw [hd3] at hs4'
    have hs := hs2.trans hs4'
    refine wordsAt_keep hqW hs (by rw [List.length_map, hw0]; omega) fun q hq ↦ ?_
    rw [List.length_map, hw0]
    rcases hq with (hq | hq) | hq <;> omega
  have e13' : reg s4.data .r13 = reg s3.data .r13 := hm4.regs .r13 _ (hk13 .r13 (by simp))
  have erdi : reg s4.data .rdi = wa m0 2048 := by
    rw [show reg s4.data .rdi = _ from hm4.regs .rdi _ hdi13]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show s3.data.regs.get64 .r14 = reg s3.data .r14 from rfl, hb3.r14]
  have erbp : reg s4.data .rbp = BitVec.ofNat 64 0 := hm4.regs .rbp _ hbp13
  have er15 : reg s4.data .r15 = BitVec.ofNat 64 0 := hm4.regs .r15 _ h15_13
  refine .done _ (.inr ⟨rw, c4 + 4, ⟨hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b13_next), hb4,
    by rw [hmod, hv], hlen, by omega, hcnt, hqlt, hhl, hll, hrl, by omega,
    hkf 40 _ (.inr (.inr rfl)) hf40, hkf 32 _ (.inr (.inl rfl)) hf32, hkf 16 _ (.inl rfl) hf16, hf24,
    by rw [e13', rk3 .r13 (by simp), e13]; exact h13, by rw [er15]; rfl, by rw [erbp]; rfl, ?_,
    hqW4, NativeRustcVm.wordsAt_nil _ _, hR4'⟩⟩)
  exact erdi

/-- **Every read**, from the entry: to the sort's head or out. -/
theorem reads_run (hp : Placed code k) (G : Geo m0 bp B.length)
    (hle : Spec (Labels.label NativeRustcVmX64.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    (hR0 : ReaderAt m0.dmem (RD m0) bp B c) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      ∃ count qs height lw rw c5, SortSt m0 bp B c k count qs height lw rw c5 0 st')
      ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b0Offset)⟩ := by
  have h7 : ∀ st, (∃ count qs c2, At7 m0 bp B c k count qs c2 st) →
      Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
        ∃ count qs height lw rw c5, SortSt m0 bp B c k count qs height lw rw c5 0 st') st := by
    rintro st ⟨count, qs, c2, h⟩
    refine Eventually.bind (height_run hp G hle hR0 h) fun s1 h1 ↦ ?_
    rcases h1 with h1 | ⟨height, c3, h1⟩
    · exact .done _ (.inl h1)
    refine Eventually.bind (lw_run hp G hle hR0 h1) fun s2 h2 ↦ ?_
    rcases h2 with h2 | ⟨lw, c4, h2⟩
    · exact .done _ (.inl h2)
    exact Eventually.mono (rw_run hp G hle hR0 h2) fun _ h ↦ by
      rcases h with h | ⟨rw, c5, h⟩
      · exact .inl h
      · exact .inr ⟨count, qs, height, lw, rw, c5, h⟩
  refine Eventually.bind (first_run hp G hle hR0) fun s1 h1 ↦ ?_
  rcases h1 with h1 | ⟨count, h1⟩ | h1
  · exact .done _ (.inl h1)
  · refine Eventually.bind (qloop hp G hle hR0 h1) fun s2 h2 ↦ ?_
    rcases h2 with h2 | h2
    · exact .done _ (.inl h2)
    · exact h7 _ ⟨count, h2⟩
  · exact h7 _ h1

end

end NativeRustcVmX64.Wire.PhaseM
