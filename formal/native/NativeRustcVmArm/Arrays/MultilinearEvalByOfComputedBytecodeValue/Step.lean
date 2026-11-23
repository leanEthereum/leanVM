module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Arrays.MultilinearEvalByOfComputedBytecodeValue.Push
public import NativeRustcVmArm.Arrays.MultilinearEvalByOfComputedBytecodeValue.Pair

/-!
# `multilinear_eval_by` (`computed_bytecode_value`'s closure): the loops run

`full[k]`'s test (`b8`) sends the inner loop to `pair` or `push` (`inner`); the inner loop runs
until the entry waits or reaches level `|point|` (`innerLoop`). The outer loop's set-up (`b4`,
`b5`: `words[i]`; `b7`) enters the inner loop at level `0` (`outer`).
-/

namespace NativeRustcVmArm.Arrays.MleOfComputedBytecodeValue

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue
open NativeVm.Model NativeRustcArm NativeRustcVmArm.Arrays.MleFrame
open NativeRustcVm (wordOf ewOf ewsOf)
open NativeRustcVm.Mle (stream cont setP)

public section

variable [Host] {k : Nat}

/-- **`full[k]`'s test** (`b8`): an entry waits (`pair`) or not (`push`). -/
theorem inner (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : LPre m0) {i kk : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b8Offset)) (hI : Inner m0 i kk s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ Post m0 s' ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b4Offset) ∧ Outer m0 (i + 1) s'.data) ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b8Offset) ∧ Inner m0 i (kk + 1) s'.data)) s := by
  have hS := hpre.1
  have hk64 : kk < 64 := by have := hI.hk; have := hpre.2.2.1; simp only [mm] at *; omega
  obtain ⟨st, pc⟩ := s
  simp only at hpc
  have hfl := frame_piece hS hI.fr.body.kept (o := 1072 + kk) (n := 1) (by omega)
  have hwf := wf_one hfl.1 hfl.2 (m := st)
  have hm : Match (Env.ofMachine st [(fbOf m0 + BitVec.ofNat 64 (1072 + kk), 1)]) flagS st :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl ⟨hI.x20.trans (BitVec.add_zero _).symm, trivial⟩
      trivial trivial trivial
  refine exec_at (hb8 hp) run_b8 hwf hpc hm fun s2 hm2 hpc2 ↦ ?_
  obtain ⟨fr2, hd2⟩ := hI.fr.block hm hm2 hwf rfl (after_eq run_b8 ▸ keeps.2.2.2.1)
  have hI2 : Inner m0 i kk s2.data := by
    have kq := regs_eq_of hm hm2 [.X21, .X20, .X28, .X19, .X22, .X23, .X29] (by decide)
    obtain ⟨-, hi, hk, h19, h20, h21, h22, h29, hval⟩ := hI
    refine ⟨fr2, hi, hk, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (s2.data.regs.getXReg .X21).toBitVec = _; rw [kq .X21 (by simp)]; exact h19
    · show (s2.data.regs.getXReg .X20).toBitVec = _; rw [kq .X20 (by simp)]; exact h20
    · show (s2.data.regs.getXReg .X28).toBitVec = _; rw [kq .X28 (by simp)]; exact h21
    · show (s2.data.regs.getXReg .X19).toNat = _; rw [kq .X19 (by simp)]; exact h22
    · show (s2.data.regs.getXReg .X29).toNat = _; rw [kq .X29 (by simp)]; exact h29
    · rw [hd2]
      show cont _ _ _ _ ⟨s2.data.regs.getXReg .X22, s2.data.regs.getXReg .X23⟩ = _
      rw [kq .X22 (by simp), kq .X23 (by simp)]
      exact hval
  simp only [PcOk] at hpc2
  have hc := pc_cond hpc2
  rcases flag_cases hk64 hI.fr.flags with ⟨hb, hn⟩ | ⟨hb, hs⟩
  · have hl := load_byte (env := Env.ofMachine st [(fbOf m0 + BitVec.ofNat 64 (1072 + kk), 1)])
      (r := 0) hb
    have hpc3 := hc.1 (by
      show (!(low .W32 ((Env.ofMachine st [(fbOf m0 + BitVec.ofNat 64 (1072 + kk), 1)]).load
        0 0 1)).getLsbD 0) = true
      rw [hl]; rfl)
    rw [← hd2] at hn
    exact Eventually.mono (push hp hpre (hpc3.trans (lbl_10 hp)) hI2 hn) fun _ h ↦ by
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · have hl := load_byte (env := Env.ofMachine st [(fbOf m0 + BitVec.ofNat 64 (1072 + kk), 1)])
      (r := 0) hb
    have hpc3 := hc.2 (by
      show ¬(!(low .W32 ((Env.ofMachine st [(fbOf m0 + BitVec.ofNat 64 (1072 + kk), 1)]).load
        0 0 1)).getLsbD 0) = true
      rw [hl]; decide)
    rw [← hd2] at hs
    simp only [NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b8_length, NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b8Length] at hpc3
    exact Eventually.mono (pair hp hmul hpre hpc3 hI2 hs) fun _ h ↦ by
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

/-- **The inner loop**: entry `i` carried until it waits (entry `i + 1` next) or is the result. -/
theorem innerLoop (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : LPre m0) {i : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b8Offset)) (hI : Inner m0 i 0 s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ Post m0 s' ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b4Offset) ∧ Outer m0 (i + 1) s'.data)) s := by
  refine Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b8Offset) ∧ ∃ kk, 64 - kk = n ∧ Inner m0 i kk s.data)
    (fun n s ⟨hpc, kk, hn, hI⟩ ↦ ?_) ⟨hpc, 0, rfl, hI⟩
  refine Eventually.mono (inner hp hmul hpre hpc hI) fun s' h ↦ ?_
  rcases h with h | h | ⟨hpc', hI'⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · have h1 := hI'.hk
    have h2 := hpre.2.2.1
    simp only [mm] at h1
    exact Or.inr ⟨64 - (kk + 1), by omega, hpc', kk + 1, rfl, hI'⟩

/-- **The outer loop's set-up** (`b4`, `b5`, `b7`): `words[i]` at level `0`. -/
theorem outer (hp : Placed code k) {m0 : MachineData} (hpre : LPre m0)
    {i : Nat} {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b4Offset)) (hO : Outer m0 i s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b8Offset) ∧ Inner m0 i 0 s'.data) s := by
  obtain ⟨hS, h02, h64, hrM, hrP⟩ := hpre
  obtain ⟨fr, hi, hpos, h29, hval⟩ := hO
  obtain ⟨st, pc⟩ := s
  simp only at hpc fr h29 hval
  have hi' : i < m0.regs.X2.toNat := hi
  obtain ⟨hwf, hm⟩ := fr.body.exit_match hS (by decide) rfl
  -- the test `i < |words|`
  refine exec_at (hb4 hp) run_b4 hwf hpc hm fun s1 hm1 hpc1 ↦ ?_
  obtain ⟨fr1, hd1⟩ := fr.block hm hm1 hwf rfl (after_eq run_b4 ▸ keeps.1)
  have hlen : (frameEnv m0 st 1232).load 0 32 8 = (m0.regs.getXReg .X2).toBitVec :=
    slot_load (r := 0) (o := 32) (x := .X2) (by rw [base0]; exact fr.body.frame) (by simp [slots])
  simp only [PcOk] at hpc1
  have hpc1' := (pc_cond hpc1).2 (by
    show ¬(!((low .W64 (st.regs.getXReg .X29).toBitVec).ult
      (low .W64 ((frameEnv m0 st 1232).load 0 32 8)))) = true
    rw [hlen, low_W64, low_W64]
    have e29 : (st.regs.getXReg .X29).toBitVec.toNat = i := h29
    have e2 : (m0.regs.getXReg .X2).toBitVec.toNat = m0.regs.X2.toNat := rfl
    have : (st.regs.getXReg .X29).toBitVec.ult (m0.regs.getXReg .X2).toBitVec = true :=
      BitVec.ult_iff_lt.mpr (BitVec.lt_def.mpr (by omega))
    rw [this]
    decide)
  simp only [NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b4_length, NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b4Length] at hpc1'
  have k1 := regs_eq_of hm hm1 [.X29] (by decide)
  -- `words[i]`
  have hfr := frame_piece hS fr1.body.kept (o := 0) (n := 1232) (by omega)
  rw [add_ofNat_zero] at hfr
  have hel := word_mapped hrM.1 fr1.body.kept hi'
  have hap := piece_offStack hS hrM.2 hrM.1.2 (j := 8 * i) (w := 8) (o := 0) (n := 1232)
    (by omega) (by omega) (by omega)
  rw [add_ofNat_zero] at hap
  have hwf4 := wf2 (st := s1.data) hfr hel (apart_comm hap)
  have e29 : (s1.data.regs.getXReg .X29).toBitVec.toNat = i := by rw [k1 .X29 (by simp)]; exact h29
  have hm4 : Match (Env.ofMachine s1.data [(fbOf m0, 1232),
      (m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * i), 8)]) elemS s1.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS (by decide) rfl, rfl, nofun, trivial⟩
      (fr1.body.sp.trans (BitVec.add_zero _).symm) trivial trivial trivial ⟨by
        have h8 : (Env.ofMachine s1.data [(fbOf m0, 1232),
            (m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * i), 8)]).load 0 8 8 =
            (m0.regs.getXReg .X1).toBitVec :=
          slot_load (r := 0) (o := 8) (x := .X1) (by rw [base0]; exact fr1.body.frame)
            (by simp [slots])
        show BinOp.apply .add .W64 (Env.load _ 0 8 8)
          (UnOp.apply (.memExtend ⟨.UXTX, .E3⟩) .W64 (s1.data.regs.getXReg .X29).toBitVec) =
          (m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * i)) + BitVec.ofInt 64 0
        rw [h8]
        simp only [BinOp.apply, UnOp.apply, ext_W64, low_W64, memExtend3, e29]
        exact (BitVec.add_zero _).symm, trivial⟩
  refine exec_at (hb5 hp) run_b5 hwf4 hpc1' hm4 fun s2 hm2 hpc2 ↦ ?_
  obtain ⟨fr2, hd2⟩ := fr1.block hm4 hm2 hwf4 rfl (after_eq run_b5 ▸ keeps.2.1)
  have hW : s2.data.regs.X22 =
      (NativeRustcVm.wordsOf m0.dmem m0.regs.X1.toBitVec m0.regs.X2.toNat)[i]'(by
        simp; exact hi') := by
    have he := word_of_apart fr1.body.same hS hrM.1.2 hrM.2 hi'
    show s2.data.regs.getXReg .X22 = _
    rw [reg_of hm2 (r := .X22) rfl, ← he]
    simp only [Sym.eval]
    rw [load8_eq]
    show UInt64.ofBitVec (wordOf s1.data.dmem
      ((m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * i)) + BitVec.ofNat 64 0)).toBitVec = _
    rw [add_ofNat_zero, UInt64.ofBitVec_toBitVec]
  have k2 := regs_eq_of hm4 hm2 [.X29] (by decide)
  simp only [PcOk] at hpc2
  -- the inner loop's set-up
  obtain ⟨hwf5, hm5⟩ := fr2.body.exit_match hS (by decide) rfl
  refine exec_at (hb7 hp) run_b7 hwf5 (hpc2.trans (lbl_7 hp)) hm5 fun s3 hm3 hpc3 ↦ ?_
  obtain ⟨fr3, hd3⟩ := fr2.block hm5 hm3 hwf5 rfl (after_eq run_b7 ▸ keeps.2.2.1)
  simp only [PcOk, NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b7_length, NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b7Length] at hpc3
  have k3 := regs_eq_of hm5 hm3 [.X22] (by decide)
  refine .done _ ⟨hpc3, fr3, hi, hpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hm3.regs .X21 _ rfl
    simp only [Sym.eval] at h
    rw [load8_eq, base0] at h
    show (s3.data.regs.getXReg .X21).toBitVec = m0.regs.X3.toBitVec + BitVec.ofNat 64 8
    rw [h]
    exact fr2.w24
  · have h := hm3.regs .X20 _ rfl
    simp only [Sym.eval, base0] at h
    show (s3.data.regs.getXReg .X20).toBitVec = fbOf m0 + BitVec.ofNat 64 1072
    rw [h]
    rfl
  · have h := hm3.regs .X28 _ rfl
    simp only [Sym.eval, base0] at h
    show (s3.data.regs.getXReg .X28).toBitVec = fbOf m0 + BitVec.ofNat 64 48
    rw [h]
    rfl
  · have h := hm3.regs .X19 _ rfl
    simp only [Sym.eval] at h
    rw [slot_load (r := 0) (o := 40) (x := .X4) (by rw [base0]; exact fr2.body.frame)
      (by simp [slots])] at h
    show (s3.data.regs.getXReg .X19).toBitVec.toNat = m0.regs.X4.toNat - 0
    rw [h]
    rfl
  · have h := hm3.regs .X29 _ rfl
    sym_simp at h
    simp only [Env.ofMachine_regs] at h
    show (s3.data.regs.getXReg .X29).toBitVec.toNat = i + 1
    rw [h, BitVec.toNat_add, k2 .X29 (by simp), e29]
    simp only [BitVec.toNat_ofNat]
    have := m0.regs.X2.toNat_lt
    omega
  · rw [hd3, hd2, hd1]
    have hE : (⟨s3.data.regs.X22, s3.data.regs.X23⟩ : EW) = (ents m0)[i]'(by simp; exact hi') := by
      rw [List.getElem_map, ← hW]
      show (⟨s3.data.regs.getXReg .X22, s3.data.regs.getXReg .X23⟩ : EW) =
        ⟨s2.data.regs.getXReg .X22, 0⟩
      rw [k3 .X22 (by simp), reg_of hm3 (r := .X23) rfl]
      rfl
    have hd : (ents m0).drop i = (ents m0)[i]'(by simp; exact hi') :: (ents m0).drop (i + 1) :=
      List.drop_eq_getElem_cons _
    rw [hE, ← hval, hd, NativeRustcVm.Mle.stream_cons]

end

end NativeRustcVmArm.Arrays.MleOfComputedBytecodeValue
