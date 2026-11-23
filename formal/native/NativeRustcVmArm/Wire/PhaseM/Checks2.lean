module

public import NativeRustcVmArm.Wire.PhaseM.Checks

/-!
# `phase_m`: the size checks, run

`sizes_run`: the height, the leaf width and the row width checked (`b20` to `b22`), then the last
position (`b23`), to `rd_rows`' call (`Pre24`) or to `None`.
-/

namespace NativeRustcVmArm.Wire.PhaseM

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVmArm.Vm.PhaseM
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

public section

theorem lsl_ofNat (n j : Nat) :
    UnOp.apply (.shift .LSL j) .W64 (BitVec.ofNat 64 n) = BitVec.ofNat 64 (n * 2 ^ j) := by
  apply BitVec.eq_of_toNat_eq
  simp [UnOp.apply, shiftW, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- A frame word loaded. -/
theorem load_fw {m0 : MachineData} {m : MachineData} {o : Nat} {v : UInt64} (h : FW m0 m.dmem o v) :
    (frEnv m0 m).load 0 o 8 = v.toBitVec := load_word h

variable {m0 : MachineData} {bp : BitVec 64} {B : List UInt8} {c : Nat} [Host] {k : Nat}

/-- **The size checks.** -/
theorem sizes_run (hp : Placed code k) (G : Geo m0 bp B) {count : Nat} {qs : List Nat}
    {height lw rw c5 : Nat} {st : MachineState} (h : Chk m0 bp B c k count qs height lw rw c5 st) :
    Eventually (step1 Host.exe) (fun st' ↦ AtNone m0 B c k st' ∨
      (Chk m0 bp B c k count qs height lw rw c5 ⟨st'.data, Host.addrOf (k + NativeRustcVmArm.Vm.PhaseM.b20Offset)⟩ ∧
        st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PhaseM.b24Offset) ∧ height ≤ 32 ∧ lw ≤ 64 ∧ rw ≤ lw ∧
        (sortD qs).getLastD 0 < 2 ^ height)) st := by
  have hc := h
  obtain ⟨hpc, hb, hmod, hql, hc0, hcnt, hqlt, hhl, hlwl, hrwl, hps0, hps256, x21, x24, x28, x26,
    f56, f48, hqW, hpW, hrd⟩ := h
  have hne : sortD qs ≠ [] := List.ne_nil_of_length_pos hps0
  -- the height
  refine chk_step hp G b20_in_code (by simp [b20]) run_b20 rfl rfl (fun r _ ↦ by cases r <;> rfl)
    hb hpc (a := height) (v := 32) (by simp only [Sym.eval, Env.ofMachine_regs]; exact x24)
    (by simp [Sym.eval]) fun s1 hb1 hd1 hr1 hpc1 ↦ ?_
  by_cases h1 : 32 < height
  · simp only [h1, ↓reduceIte] at hpc1
    exact .done _ (.inl ⟨hpc1, hb1, by
      rw [hmod]; exact tail_none_of (by unfold wireMaxHeight; omega)⟩)
  simp only [h1, ↓reduceIte] at hpc1
  -- the leaf width
  refine chk_step hp G b21_in_code (by simp [b21]) run_b21 rfl rfl (fun r hr ↦ by
    cases r <;> first | rfl | exact absurd rfl hr) hb1 hpc1 (a := lw) (v := 64)
    (by
      show ((frEnv m0 s1.data).load 0 56 8).toNat = lw
      rw [load_fw (by rw [hd1]; exact f56)]
      exact toNat_toUInt64_of_lt (by omega))
    (by simp [Sym.eval]) fun s2 hb2 hd2 hr2 hpc2 ↦ ?_
  by_cases h2 : 64 < lw
  · simp only [h2, ↓reduceIte] at hpc2
    exact .done _ (.inl ⟨hpc2, hb2, by
      rw [hmod]; exact tail_none_of (by unfold wireMaxLeafWords; omega)⟩)
  simp only [h2, ↓reduceIte] at hpc2
  -- the row width
  refine chk_step hp G b22_in_code (by simp [b22]) run_b22 rfl rfl (fun r hr ↦ by
    cases r <;> first | rfl | exact absurd rfl hr) hb2 hpc2 (a := rw) (v := lw)
    (by
      simp only [Sym.eval, Env.ofMachine_regs]
      rw [hr2 .X28 (by decide), hr1 .X28 (by decide)]; exact x28)
    (by
      show ((frEnv m0 s2.data).load 0 56 8).toNat = lw
      rw [load_fw (by rw [hd2, hd1]; exact f56)]
      exact toNat_toUInt64_of_lt (by omega)) fun s3 hb3 hd3 hr3 hpc3 ↦ ?_
  by_cases h3 : lw < rw
  · simp only [h3, ↓reduceIte] at hpc3
    exact .done _ (.inl ⟨hpc3, hb3, by rw [hmod]; exact tail_none_of (by omega)⟩)
  simp only [h3, ↓reduceIte] at hpc3
  -- the last position
  have hd : s3.data.dmem = st.data.dmem := hd3.trans (hd2.trans hd1)
  have hr : ∀ r : XReg, r ≠ .X8 → s3.data.regs.getXReg r = st.data.regs.getXReg r :=
    fun r hr' ↦ (hr3 r hr').trans ((hr2 r hr').trans (hr1 r hr'))
  set n := (sortD qs).length with hn
  have hon : 2048 + 8 * (n - 1) + 8 ≤ workBytes := by rw [workBytes_eq]; omega
  have hwf := G.al_wf (o := 2048 + 8 * (n - 1)) (n := 8) hon (by omega) hb3.fr
  have hmA := G.al_match (o := 2048 + 8 * (n - 1)) (n := 8) (a := lastAddr) (k := 8) hb3.fr (by
    simp only [lastAddr, Sym.eval, Env.ofMachine_regs]
    rw [hb3.x19, hr .X26 (by decide)]
    have : (st.data.regs.getXReg .X26).toBitVec = BitVec.ofNat 64 n := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact x26
    rw [this, lsl_ofNat, add_lit, add_lit, wa, NativeRustcVm.addr_add_add]
    rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add]
    congr 2
    omega)
  refine exec_at (infix_of b23_in_code (by simp [b23]) hp) run_b23 hwf hpc3 hmA
    fun s4 hm4 hpc4 ↦ ?_
  have hd4 : s4.data.dmem = s3.data.dmem := hm4.dmem_eq hwf rfl
  have hfr4 : Frm m0 s4.data := Fr.ofBlock hb3.fr hmA hm4 hwf rfl rfl rfl
    fun x hx ↦ absurd hx (by simp)
  have r4 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X24, .X26, .X28], s4.data.regs.getXReg r =
      s3.data.regs.getXReg r := regs_of hmA hm4 (by decide)
  have hb4 : Base m0 s4.data := hb3.of_regs hfr4 fun r hr' ↦ r4 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢
    rcases hr' with rfl | rfl | rfl <;> simp)
  have hlast : (alEnv m0 s3.data (wa m0 (2048 + 8 * (n - 1))) 8).load 1 0 8 =
      ((sortD qs).getLastD 0).toUInt64.toBitVec := by
    apply load_word
    rw [Env.ofMachine_mem0, Env.base_ofMachine _ _ _ rfl, NativeRustcVm.addr_add_zero, hd,
      getLastD_eq hps0]
    have := NativeRustcVm.WordsAt.getElem hpW (i := n - 1) (by simp; omega)
    simpa [wa, NativeRustcVm.addr_add_add] using this
  have hlt : (sortD qs).getLastD 0 < 2 ^ 32 := by
    rw [getLastD_eq hps0]
    exact sortD_lt hqlt _ (List.getElem_mem _)
  have hcond : (SBool.cmp .eq .W64 (.bin .lsrv .W64 (.load 1 0 8) (.reg .X24)) (.lit 0)).not.eval
      (alEnv m0 s3.data (wa m0 (2048 + 8 * (n - 1))) 8) =
      !decide ((sortD qs).getLastD 0 < 2 ^ height) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    rw [eq_apply, hlast, hr .X24 (by decide)]
    have h24 : (st.data.regs.getXReg .X24).toBitVec.toNat = height := x24
    rw [lsrv_apply _ _ (by rw [h24]; omega), h24, UInt64.toNat_toBitVec,
      toNat_toUInt64_of_lt (by omega)]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    rw [decide_eq_decide.mpr (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _))]
  simp only [PcOk, hcond] at hpc4
  by_cases h4 : (sortD qs).getLastD 0 < 2 ^ height
  · simp only [h4, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc4
    refine .done _ (.inr ⟨⟨rfl, hb4, hmod, hql, hc0, hcnt, hqlt, hhl, hlwl, hrwl, hps0, hps256,
      ?_, ?_, ?_, ?_, by rw [hd4, hd]; exact f56, by rw [hd4, hd]; exact f48,
      by rw [hd4, hd]; exact hqW, by rw [hd4, hd]; exact hpW, by rw [hd4, hd]; exact hrd⟩,
      hpc4, by omega, by omega, by omega, h4⟩)
    · rw [r4 .X21 (by simp), hr .X21 (by decide)]; exact x21
    · rw [r4 .X24 (by simp), hr .X24 (by decide)]; exact x24
    · rw [r4 .X28 (by simp), hr .X28 (by decide)]; exact x28
    · rw [r4 .X26 (by simp), hr .X26 (by decide)]; exact x26
  · simp only [h4, decide_false, Bool.not_false, ↓reduceIte] at hpc4
    exact .done _ (.inl ⟨hpc4.trans (hp.label (j := NativeRustcVmArm.Vm.PhaseM.b18Offset) NativeRustcVmArm.Vm.PhaseM.label_12_at), hb4, by
      rw [hmod]; exact tail_none_of (by tauto)⟩)

end

end NativeRustcVmArm.Wire.PhaseM
