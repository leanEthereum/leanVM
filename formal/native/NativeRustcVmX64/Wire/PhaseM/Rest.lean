module

public import NativeRustcVmX64.Wire.PhaseM.Queries
public import NativeRustcVmX64.Code.Vm.ReaderLe.Names

/-!
# `phase_m`: the three sizes (x86-64)

`rest_run`: from the height's read (`At7`), the height (`b7`, `b8`: to the frame's byte `32`),
the leaf width (`b9`, `b10`: to `16`), the row width (`b11`, `b12`: no query is `None`; `b13`: to
`24`), to the sort's head (`SortSt … 0`), the model's phase now `tail` of what was read, or to
`None`.
-/

namespace NativeRustcVmX64.Wire.PhaseM

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmX64.Vm.PhaseM
open NativeRustcVmX64.Transcript (Frame frameEnv after after_eq MidOk wordAt_write load_ofMachine
  low8_replaceLow)
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off)
open NativeRustcVmX64.Wire.Decode (eqv_eval)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

/-- `b12`'s test, by values: the tag `a`, the flag `b` (no query) in RBP's low byte. -/
theorem c12_val (a x : BitVec 64) (b : Bool) (ha : a = 0 ∨ a = 1) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (BinOp.apply .merge .W8
      (BinOp.apply .merge .W8 a (UnOp.apply .not .W8 a))
      (BinOp.apply .or .W8 (BinOp.apply .merge .W8 a (UnOp.apply .not .W8 a))
        (BinOp.apply .merge .W8 x (if b = true then BitVec.ofNat 64 1 else BitVec.ofNat 64 0))))
      (BitVec.ofNat 64 1)) (BitVec.ofNat 64 0) = (decide (a = 1) && !b) := by
  simp only [CmpOp.apply, BinOp.apply, UnOp.apply, low8_replaceLow, low_ext]
  cases b <;> rcases ha with rfl | rfl <;> decide

theorem c12_eval [Labels] (env : Sym.Env) (ha : env.regs .rax = 0 ∨ env.regs .rax = 1)
    {x : BitVec 64} {b : Bool}
    (hb : env.regs .rbp = BinOp.apply .merge .W8 x
      (if b = true then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)) :
    c12.eval env = !(decide (env.regs .rax = 1) && !b) := by
  simp only [c12, SBool.eval, Sym.eval, hb]
  rw [c12_val _ _ _ ha]

theorem rax_ne1_eval [Labels] (env : Sym.Env) (ha : env.regs .rax = 0 ∨ env.regs .rax = 1) :
    (SBool.cmp .eq .W64 (.reg .rax) (.lit 1)).not.eval env = decide (env.regs .rax = 0) := by
  simp only [SBool.eval, Sym.eval]
  rcases ha with h | h <;> rw [h] <;> decide

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} [Host] {k : Nat}

/-- **The height**: from `At7`, read and stored. -/
structure At9 [Labels] [Host] (m0 : MachineData) (bp : BitVec 64) (B : List UInt8) (c k : Nat)
    (count : Nat) (qs : List Nat) (height c3 : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b9Offset)
  bod : Bod m0 8 st.data
  model : phaseM B c = match rdU32 B c3 with
    | none => none
    | some (lw, c4) => match rdU32 B c4 with
      | none => none
      | some (rw, c5) => tail B qs height lw rw c5
  len : qs.length = count
  cnt : count ≤ 256
  qlt : ∀ q ∈ qs, q < 2 ^ 32
  hlt : height < 2 ^ 32
  f40 : FW m0 st.data.dmem 40 count.toUInt64
  f32 : FW m0 st.data.dmem 32 height.toUInt64
  r13 : (reg st.data .r13).toNat = 8 * count
  qsW : NativeRustcVm.WordsAt st.data.dmem (wa m0 0) (qs.map Nat.toUInt64)
  rd : ReaderAt st.data.dmem (RD m0) bp B c3

/-- **The height.** -/
theorem height_run (hp : Placed code k) (G : Geo m0 bp B.length)
    (hle : Spec (Labels.label NativeRustcVmX64.Vm.ReaderLe.entryLabel) ReaderLePre ReaderLePost)
    (hR0 : ReaderAt m0.dmem (RD m0) bp B c) {count : Nat} {qs : List Nat} {c2 : Nat}
    {st : MachineState} (h : At7 m0 bp B c k count qs c2 st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨
      ∃ height c3, At9 m0 bp B c k count qs height c3 st') st := by
  obtain ⟨hpc, hbod, h1, hcnt, hqs, hf40, h13, hqW, hrd⟩ := h
  have hsp := G.sp
  have htop := G.top
  have hwn := G.wNw
  have hsR := G.sR
  have hsB := G.sB
  have hsW := G.sW
  have hrW := G.rW
  have hrn := G.rNw
  have hmod := pm_eq_of h1 hcnt hqs
  have hlen := (rdU32s_len B count (c + 4) hqs).1
  have hqlt : ∀ q ∈ qs, q < 2 ^ 32 := rdU32s_lt B count (c + 4) hqs
  -- `b7`: `Reader::le`.
  obtain ⟨hmid7, hw7, hsi7, hdi7, hk7⟩ := ok_b7
  refine le4 hp G hle b7_in_code (by simp [b7]) exit_b7 hmid7 hw7 hsi7 hdi7 (hk7 .r12 (by simp))
    (hk7 .r14 (by simp)) hpc hbod hrd fun s1 m2 hb2 hm1 hcs2 hs2 hr2 ↦ ?_
  have e13 : reg m2 .r13 = reg st.data .r13 :=
    (hcs2 .r13 rfl).trans (hm1.regs .r13 _ (hk7 .r13 (by simp)))
  -- `b8`: the height to `32`, its tag.
  obtain ⟨hmid8, hmem8, hw32, hk8⟩ := ok_b8
  refine wblk hp G b8_in_code (by simp [b8]) exit_b8 hmid8
    (fun w hw ↦ by rw [hmem8] at hw; simp only [List.mem_singleton] at hw; subst hw; decide)
    (hk8 .r12 (by simp)) (hk8 .r14 (by simp)) (st := ⟨m2, _⟩) rfl hb2
    fun s3 hb3 hs3 hkeep3 hm3 hpc3 ↦ ?_
  simp only [PcOk] at hpc3
  have ea : (frameEnv m0 m2 160 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.PhaseM.b8Offset + b8.length)).toBitVec).regs
      .rax = reg m2 .rax := rfl
  rcases read4_cases hr2 with ⟨hn, h0⟩ | ⟨height, hv, h0, hdx, hhl, hR4⟩
  · rw [and1_eval _ (by rw [ea]; exact .inl h0), ea, h0] at hpc3
    simp only [decide_true, ↓reduceIte] at hpc3
    rw [hp.label NativeRustcVmX64.Vm.PhaseM.label_23_at] at hpc3
    refine Eventually.mono (none_run hp G hR0 hpc3 hb3 ?_) fun _ h ↦ .inl h
    rw [hmod, hn]
  rw [and1_eval _ (by rw [ea]; exact .inr h0), ea, h0] at hpc3
  simp only [show ¬ ((1 : BitVec 64) = 0) by decide, decide_false, Bool.false_eq_true,
    ↓reduceIte] at hpc3
  have hf32 : FW m0 s3.data.dmem 32 height.toUInt64 := by
    have := wordAt_write hm3 (r := 0) (o := 32) rfl (by omega) hw32
    simp only [Sym.eval, Env.ofMachine_regs] at this
    rw [show m2.regs.get64 .rdx = reg m2 .rdx from rfl, toNat_reg_eq hdx] at this
    exact this
  have hf40' : FW m0 s3.data.dmem 40 count.toUInt64 := by
    refine hkeep3 40 _ (by omega) (fun w hw hr ↦ by
      rw [hmem8] at hw; simp only [List.mem_singleton] at hw; subst hw; decide) ?_
    exact hf40.keep G (by omega) hs2 fun q hq ↦ by rcases hq with hq | hq <;> omega
  have hR3 : ReaderAt s3.data.dmem (RD m0) bp B (c2 + 4) :=
    reader_keep hR4 hs3 (fun q hq ↦ by omega) (fun q hq ↦ by omega)
  have hqW3 : NativeRustcVm.WordsAt s3.data.dmem (wa m0 0) (qs.map Nat.toUInt64) := by
    have hw0 := G.wa (o := 0) (by omega)
    refine wordsAt_keep hqW (hs2.trans hs3) (by rw [List.length_map, hw0]; omega) fun q hq ↦ ?_
    rw [List.length_map, hw0]
    rcases hq with (hq | hq) | hq <;> omega
  have e13' : reg s3.data .r13 = reg m2 .r13 := hm3.regs .r13 _ (hk8 .r13 (by simp))
  refine .done _ (.inr ⟨height, c2 + 4, ⟨hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.PhaseM.b8_next), hb3,
    by rw [hmod, hv]; rfl, hlen, hcnt, hqlt, hhl, hf40', hf32, by rw [e13', e13]; exact h13, hqW3,
    hR3⟩⟩)

end

end NativeRustcVmX64.Wire.PhaseM
