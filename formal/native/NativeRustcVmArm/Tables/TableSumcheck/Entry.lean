module

public import NativeRustcVmArm.Tables.TableSumcheck.Defs

/-!
# `table_sumcheck`: the entry and the exits

`b0` saves the registers in the 720-byte frame, zeroes the challenges and takes the six heights'
maximum `n` into X25 (`maxS`); the heights are at most `30`, so it never leaves for
`.LTableSumcheck_7` and falls into `b1` (`start`). `b10` sets X0 to `0` (`fail10`), `b11` restores
the registers and returns (`exit11`).
-/

namespace NativeRustcVmArm.Tables.TableSumcheck

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TableSumcheck
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Tables

public section

/-- `csel … hi`: the larger. -/
theorem hmax_toNat [Labels] (env : Env) (a b : Sym) :
    ((hmax a b).eval env).toNat = max (a.eval env).toNat (b.eval env).toNat := by
  simp only [hmax, Sym.eval, SBool.eval, CmpOp.apply, low_W64]
  by_cases h1 : (b.eval env).toNat < (a.eval env).toNat
  · have : (b.eval env).ult (a.eval env) = true := by simp [BitVec.ult, h1]
    simp only [this, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    omega
  · by_cases h2 : b.eval env = a.eval env
    · simp only [h2, beq_self_eq_true, Bool.not_true, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte]
      omega
    · have : (b.eval env).ult (a.eval env) = false := by simp [BitVec.ult, h1]
      have h3 : (b.eval env == a.eval env) = false := by simpa using h2
      simp only [this, h3, Bool.not_false, Bool.and_self, ↓reduceIte]
      omega

/-- `b.hi` after `cmp x, #v`: `x > v`. -/
theorem hiS_eval [Labels] (env : Env) (x : Sym) {v : Nat} (hv : v < 2 ^ 64)
    (h : (x.eval env).toNat ≤ v) : (hiS x v).eval env = false := by
  simp only [hiS, SBool.eval, Sym.eval, CmpOp.apply, low_W64]
  rcases Nat.lt_or_eq_of_le h with h | h
  · have : (x.eval env).ult (BitVec.ofNat 64 v) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, decide_eq_true_eq]
      exact h
    simp [this]
  · have : x.eval env = BitVec.ofNat 64 v := BitVec.eq_of_toNat_eq (by
      rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv])
    simp [this]

section
variable [Host] {k : Nat} {a : DecArea} {s : TState} {heights : Array Nat} {bus : BusResultW}
  {m0 : MachineData}

/-- The heights' maximum `b0` computes. -/
theorem maxS_eval (hH : HeightsAt m0.dmem m0.regs.X1.toBitVec heights) :
    (maxS.eval (Env.ofMachine m0 [(fb m0, 720), (m0.regs.X1.toBitVec, 48)])).toNat =
      heights.foldl max 0 := by
  obtain ⟨hs, hle, hw⟩ := hH
  have hs6 : heights.size = 6 := hs
  have hl : ∀ j o (hj : j < 6), o = 8 * j → (Env.ofMachine m0 [(fb m0, 720),
      (m0.regs.X1.toBitVec, 48)]).load 1 o 8 = BitVec.ofNat 64 (heights[j]'(by omega)) := by
    intro j o hj ho
    subst ho
    rw [load_word (v := (heights[j]'(by omega)).toUInt64)]
    · apply BitVec.eq_of_toNat_eq
      rw [UInt64.toNat_toBitVec, toNat_toUInt64 (by
        have := hle _ (Array.getElem_mem (i := j) (by omega)); omega), BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := hle _ (Array.getElem_mem (i := j) (by omega)); omega)]
    · have := NativeRustcVm.wordsAt_getElem hw (i := j) (by simp [hs6]; omega)
      simpa using this
  have hlt : ∀ j (hj : j < 6), (heights[j]'(by omega)) < 2 ^ 64 := fun j hj ↦ by
    have := hle _ (Array.getElem_mem (i := j) (by omega)); omega
  simp only [maxS, hmax_toNat, Sym.eval]
  rw [foldl_max6 heights hs6, hl 0 0 (by omega) rfl, hl 1 8 (by omega) rfl,
    hl 2 16 (by omega) rfl, hl 3 24 (by omega) rfl, hl 4 32 (by omega) rfl,
    hl 5 40 (by omega) rfl]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (hlt 0 (by omega)), Nat.mod_eq_of_lt (hlt 1 (by omega)),
    Nat.mod_eq_of_lt (hlt 2 (by omega)), Nat.mod_eq_of_lt (hlt 3 (by omega)),
    Nat.mod_eq_of_lt (hlt 4 (by omega)), Nat.mod_eq_of_lt (hlt 5 (by omega))]

/-- **The exit** (`b11`): the registers restored, X0 kept, `ret`. -/
theorem exit11 (hp : Placed code k) (hS : StackOk m0 tableSumcheckStack) {m : MachineData}
    (hfr : Fr m0 720 tableSumcheckStack slots keep (outs m0) m)
    (hpost : ∀ m' : MachineData, m'.dmem = m.dmem → m'.regs.X0 = m.regs.X0 →
      m'.regs.X0 = okWord (res s heights bus m0).isSome ∧
      (∀ x s', res s heights bus m0 = some (x, s') → TableEvalsAt m'.dmem m0.regs.X7.toBitVec x) ∧
      NextAt m'.dmem m0.regs.X0.toBitVec a (res s heights bus m0)) :
    Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableSumcheck.b11Offset)⟩ := by
  have hwf := Bus.wf_frame hS N_ge hfr.kept
  have hm := Bus.match_frame hS N_ge rfl hfr.sp
  refine exec_then (b11_in_code.trans hp.1 (by simp [b11])) run_b11 hwf hm fun st hm' hpc ↦ ?_
  have hm'' : Match (Env.ofMachine m [(base m0 720, 720)]) (Bus.after b11 sF) st.data := by
    rw [Bus.after_eq run_b11]; exact hm'
  obtain ⟨hok, hmem, h0⟩ := ok_b11
  obtain ⟨hret, hsv⟩ := hfr.exit hm'' hwf hok
  have hd : st.data.dmem = m.dmem := hm''.dmem_eq hwf hmem
  obtain ⟨p1, p2, p3⟩ := hpost st.data hd (Bus.Gkr.reg_of hm'' h0)
  refine .done _ ⟨by simp only [PcOk] at hpc; rw [hpc, hret], p1, p2, p3, ?_, hsv⟩
  rw [hd]
  exact NativeRustcVm.SameOutside.mono hfr.same fun q hq ↦
    hq.elim (fun h ↦ .inr (.inr h)) fun h ↦ h.elim .inl (.inr ∘ .inl)

/-- **A rejection** (`b10`): X0 `0`, then the exit. -/
theorem fail10 (hp : Placed code k) (hS : StackOk m0 tableSumcheckStack) {m : MachineData}
    (hfr : Fr m0 720 tableSumcheckStack slots keep (outs m0) m)
    (hr : res s heights bus m0 = none) :
    Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableSumcheck.b10Offset)⟩ := by
  refine Bus.Gkr.Fr.runBlock hS N_ge rfl hfr (b10_in_code.trans hp.1 (by simp [b10])) run_b10 rfl
    rfl rfl rfl fun st hfr' _ hm hpc ↦ ?_
  have hm' : Match (Env.ofMachine m [(base m0 720, 720)]) (Bus.after b10 sF) st.data := by
    rw [Bus.after_eq run_b10]; exact hm
  obtain ⟨-, -, -, h0⟩ := ok_b10
  simp only [PcOk] at hpc
  refine Bus.Gkr.at_pc hpc (exit11 hp hS hfr' fun m' _ hx ↦ ⟨?_, fun x s' h ↦ (by
    rw [hr] at h; cases h), fun x s' h ↦ (by rw [hr] at h; cases h)⟩)
  rw [hx, hr]
  exact UInt64.toBitVec_inj.mp (Bus.Gkr.reg_lit hm' h0)

/-- **The entry** (`b0`): the prologue; the maximum `n` of the heights in X25, the arguments
kept. -/
theorem start (hp : Placed code k) (hpre : TableSumcheckPre a s heights bus m0)
    (cont : ∀ m : MachineData, Fr m0 720 tableSumcheckStack slots keep (outs m0) m →
      (∀ r ∈ [XReg.X0, .X1, .X2, .X3, .X4, .X5, .X6, .X7], m.regs.getXReg r = m0.regs.getXReg r) →
      (m.regs.getXReg .X25).toNat = heights.foldl max 0 →
      TStateAt m.dmem m0.regs.X0.toBitVec a s →
      Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TableSumcheck.b1Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s heights bus m0) ⟨m0, Host.addrOf k⟩ := by
  obtain ⟨hS, hrc, -, hts0, htok, -, -, -, hHin, hH, -⟩ := hpre
  have hN := hS.2.1
  have hwf : (Env.ofMachine m0 [(fb m0, 720), (m0.regs.X1.toBitVec, 48)]).WF :=
    Bus.wf_frame2 hS N_ge (fun _ h ↦ h) hHin.1 hHin.2.1
  have hm : Match (Env.ofMachine m0 [(fb m0, 720), (m0.regs.X1.toBitVec, 48)]) entryS m0 :=
    match_ofMachine (sregions := [(720, true), (48, false)])
      (regions := [(fb m0, 720), (m0.regs.X1.toBitVec, 48)])
      ⟨rfl, fun _ ↦ Bus.base_aligned hS N_ge rfl, rfl, nofun, trivial⟩
      (Bus.env0_sp (F := 720) [(m0.regs.X1.toBitVec, 48)])
      ⟨by simp [Sym.eval]; rfl, trivial⟩ trivial trivial trivial
  rw [show Host.addrOf k = Host.addrOf (k + NativeRustcVmArm.Vm.TableSumcheck.b0Offset) from rfl]
  refine exec_then (b0_in_code.trans hp.1 (by simp [b0])) run_b0' hwf hm fun st hm1 hpc ↦ ?_
  obtain ⟨hsp0, hsl0, hmem0, h0, h1, h2, h3, h4, h5, h6, h7, h25⟩ := ok_b0
  have hfr : Fr m0 720 tableSumcheckStack slots keep (outs m0) st.data :=
    Fr.ofPrologue hN N_ge hm1 hwf hsp0 hsl0 slots_le hmem0 nofun
  have hmax := maxS_eval hH
  have hle : heights.foldl max 0 ≤ 30 := foldl_max_le heights hH.1 hH.2.1
  simp only [PcOk, hiS_eval _ maxS (v := 30) (by decide) (by rw [hmax]; exact hle),
    Bool.false_eq_true, ↓reduceIte] at hpc
  rw [show k + NativeRustcVmArm.Vm.TableSumcheck.b0Offset + b0.length = k + NativeRustcVmArm.Vm.TableSumcheck.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TableSumcheck.b0_next]] at hpc
  have c : Sumcheck.Ctx m0 m0.regs.X0.toBitVec a tableSumcheckStack 720 :=
    Bus.Gkr.ctx_of hS hrc hts0 htok N_ge rfl
  have hts : TStateAt st.data.dmem m0.regs.X0.toBitVec a s :=
    tstate_keep c (fun q hq ↦ Bus.frame_inRange hN N_ge (Bus.Written.inRange rfl
      (base_noWrap (by have := N_ge; omega)) hmem0 hq)) hts0 (hm1.kept hwf) (hm1.sameOutside hwf)
  refine Bus.Gkr.at_pc hpc (cont st.data hfr (fun r hr ↦ ?_) ?_ hts)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Bus.Gkr.reg_of hm1 h0
    · apply UInt64.toBitVec_inj.mp
      rw [hm1.regs .X1 _ h1]
      simp [Sym.eval]
      rfl
    · exact Bus.Gkr.reg_of hm1 h2
    · exact Bus.Gkr.reg_of hm1 h3
    · exact Bus.Gkr.reg_of hm1 h4
    · exact Bus.Gkr.reg_of hm1 h5
    · exact Bus.Gkr.reg_of hm1 h6
    · exact Bus.Gkr.reg_of hm1 h7
  · show (st.data.regs.getXReg .X25).toBitVec.toNat = _
    rw [hm1.regs .X25 _ h25, hmax]

end

end

end NativeRustcVmArm.Tables.TableSumcheck
