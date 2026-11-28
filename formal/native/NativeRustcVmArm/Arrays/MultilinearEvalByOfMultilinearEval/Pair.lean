module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Arrays.MultilinearEvalByOfMultilinearEval.Loop

/-!
# `multilinear_eval_by` (`multilinear_eval`'s closure): an entry pairs

`pair`: an entry `a` waits at level `k` (`b8`): `full[k] = 0` (`pendOf_clear`), `a·(1 + r)` and
`v·r` by `EW::mul` (`b8`, `b9`), their sum carried to level `k + 1` (`b10`): back at the inner
loop's head, or, at level `|point|`, the result (`b11`, the epilogue).
-/

namespace NativeRustcVmArm.Arrays.MleOfMultilinearEval

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval
open NativeVm.Model NativeRustcArm NativeRustcVmArm.Arrays.MleFrame
open NativeRustcVm (wordOf ewOf ewsOf)
open NativeRustcVm.Mle (stream cont setP)

public section

variable [Host] {k : Nat}

/-- **An entry waits at level `kk`** (`b8`-`b10`): paired with `v`, carried to level `kk + 1`. -/
theorem pair (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : MleOfMultilinearEvalPre m0) {i kk : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b8Offset)) (hI : Inner m0 i kk s.data)
    (hsome : pendOf s.data.dmem (fbOf m0) kk =
      some (ewOf s.data.dmem (fbOf m0 + BitVec.ofNat 64 (48 + 16 * kk)))) :
    Eventually (step1 Host.exe) (fun s' ↦ Post m0 s' ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b7Offset) ∧ Inner m0 i (kk + 1) s'.data)) s := by
  obtain ⟨hS, h02, h64, -, hrP, hoP⟩ := hpre
  obtain ⟨fr, hi, hk, h19, h20, h21, h22, h29, hval⟩ := hI
  obtain ⟨st, pc⟩ := s
  simp only at hpc hsome fr h19 h20 h21 h22 h29 hval
  have hk64 : kk < 64 := by simp only [mm] at hk; omega
  have hk' : kk < m0.regs.X4.toNat := hk
  have hkP : kk < (pts m0).length := by simp only [pts, NativeRustcVm.length_ewsOf]; exact hk
  have hpt := elem_mapped hrP fr.body.kept hk
  have hsl := frame_piece hS fr.body.kept (o := 48 + 16 * kk) (n := 16) (by omega)
  have hfl := frame_piece hS fr.body.kept (o := 1072 + kk) (n := 1) (by omega)
  have a1 := piece_offStack hS hoP hrP.2 (j := 16 * kk) (w := 16) (o := 48 + 16 * kk) (n := 16)
    (by omega) (by omega) (by omega)
  have a2 := piece_offStack hS hoP hrP.2 (j := 16 * kk) (w := 16) (o := 1072 + kk) (n := 1)
    (by omega) (by omega) (by omega)
  have a3 := frame_apart hS (o := 48 + 16 * kk) (n := 16) (o' := 1072 + kk) (n' := 1)
    (by omega) (by omega)
  have hwf := wf3 (st := st) hpt hsl hfl a1 a2 a3
  have hm : Match (Env.ofMachine st [(m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * kk), 16),
      (fbOf m0 + BitVec.ofNat 64 (48 + 16 * kk), 16), (fbOf m0 + BitVec.ofNat 64 (1072 + kk), 1)])
      pairS st :=
    match_ofMachine ⟨rfl, nofun, rfl, nofun, rfl, nofun, trivial⟩ rfl
      ⟨h19.trans (by rw [← NativeRustcVm.addr_add]; rfl), h21.trans (BitVec.add_zero _).symm,
        h20.trans (BitVec.add_zero _).symm, trivial⟩ trivial trivial trivial
  refine exec_at (hb8 hp) run_b8 hwf hpc hm fun s2 hm2 hpc2 ↦ ?_
  -- the block wrote `full[kk] = 0` only
  have hW : ∀ p, Written (Env.ofMachine st [(m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * kk), 16),
      (fbOf m0 + BitVec.ofNat 64 (48 + 16 * kk), 16), (fbOf m0 + BitVec.ofNat 64 (1072 + kk), 1)])
      (after b8 pairS) p → p.toNat = (fbOf m0).toNat + (1072 + kk) := by
    have e1 := fb_add_toNat hS (o := 1072 + kk) (by omega)
    rw [after_eq run_b8]
    intro p ⟨w, hw, b, sz, hb, hlo, hhi⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    subst hw
    simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    simp only at hlo hhi
    omega
  rw [after_eq run_b8] at hW
  have hnw : ∀ j, j < 1232 → j ≠ 1072 + kk →
      s2.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) = st.dmem.get? (fbOf m0 + BitVec.ofNat 64 j) := by
    intro j hj h1
    refine hm2.get?_mem0 hwf fun hw ↦ ?_
    have := hW _ hw
    rw [fb_add_toNat hS (by omega)] at this
    omega
  have hflag : s2.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 (1072 + kk)) = some 0 := by
    have := hm2.mem 2 (fbOf m0 + BitVec.ofNat 64 (1072 + kk)) 1 rfl 0 (by decide)
    rw [add_ofNat_zero] at this
    rw [this]
    simp [memByte, findWrite, Sym.eval, byteOf]
  have bd2 : Body m0 1232 mleStack slots 0 0 s2.data :=
    body_of_frame_write fr.body hS hm hm2 hwf rfl
      (by rw [kept_nil.1]; exact after_eq run_b8 ▸ keeps.2.2.2.2.1)
      (fun p hp' ↦ by
        have := hW p hp'
        have := (fb_toNat hS).1
        exact frame_addr hS (lo := 48) (hi := 1136) (by omega) (by omega) (by decide))
      (by decide)
  have fr2 : Fr m0 s2.data := ⟨bd2, by
      rw [NativeRustcVm.wordOf_congr (d := st.dmem) fun j hj ↦ by
        rw [NativeRustcVm.addr_add]; exact hnw (24 + j) (by omega) (by omega)]
      exact fr.w24,
    flagsOk_clear fr.flags hflag fun j _ hj h1 ↦ hnw j (by omega) h1⟩
  have hP2 : pendOf s2.data.dmem (fbOf m0) = setP (pendOf st.dmem (fbOf m0)) kk none :=
    pendOf_clear hk64 hflag fun j _ hj h1 ↦ hnw j (by omega) h1
  -- the loads: `a = pending[kk]`, `r = point[kk]`, `1 + r`
  have hr : ewOf st.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * kk)) = (pts m0)[kk] :=
    elem_of_apart fr.body.same hS hrP.2 hoP (apart_zero _ _) noWrap_zero hk
  have hA : (⟨s2.data.regs.X0, s2.data.regs.X1⟩ : EW) =
      ewOf st.dmem (fbOf m0 + BitVec.ofNat 64 (48 + 16 * kk)) := by
    have h := ewOf_loads (Env.ofMachine st [(m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * kk), 16),
      (fbOf m0 + BitVec.ofNat 64 (48 + 16 * kk), 16), (fbOf m0 + BitVec.ofNat 64 (1072 + kk), 1)]) 1 0
    rw [add_ofNat_zero] at h
    show (⟨s2.data.regs.getXReg .X0, s2.data.regs.getXReg .X1⟩ : EW) = _
    rw [reg_of hm2 (r := .X0) rfl, reg_of hm2 (r := .X1) rfl]
    exact h.symm
  have hR : (⟨s2.data.regs.X25, s2.data.regs.X26⟩ : EW) = (pts m0)[kk] := by
    have h := ew_of_loads (off := 0) (lo := .X25) (hi := .X26) hm2 rfl rfl
    rw [add_ofNat_zero, hr] at h
    exact h
  have hR1 : (⟨s2.data.regs.X2, s2.data.regs.X3⟩ : EW) = 1 + (pts m0)[kk] := by
    rw [one_add, ← hR]
    have h2 := hm2.regs .X2 _ rfl
    have h3 := hm2.regs .X3 _ rfl
    have h25 := hm2.regs .X25 _ rfl
    have h26 := hm2.regs .X26 _ rfl
    sym_simp at h2 h3 h25 h26
    show (⟨s2.data.regs.getXReg .X2, s2.data.regs.getXReg .X3⟩ : EW) =
      ⟨s2.data.regs.getXReg .X25 ^^^ 1, s2.data.regs.getXReg .X26⟩
    congr 1
    · apply UInt64.toBitVec_inj.mp
      rw [UInt64.toBitVec_xor, h2, h25]
      rfl
    · apply UInt64.toBitVec_inj.mp
      rw [h3, h26]
  have k2 := regs_eq_of hm hm2 [.X19, .X22, .X23, .X24, .X29] (by decide)
  -- `a·(1 + r)`
  simp only [NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b8_length, NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b8Length] at hpc2
  refine call_then hpc2 hmul (bd2.ewMulPre hS (by decide) (by decide)) fun s3 hpc3 hpost3 ↦ ?_
  obtain ⟨fr3, hP3⟩ := fr2.call hS hpost3
  have k3 : ∀ r, calleeSaved r = true → s3.data.regs.getXReg r = s2.data.regs.getXReg r :=
    hpost3.2.2.2.1
  have ht1 : (⟨s3.data.regs.X0, s3.data.regs.X1⟩ : EW) =
      ewOf st.dmem (fbOf m0 + BitVec.ofNat 64 (48 + 16 * kk)) * (1 + (pts m0)[kk]) := by
    rw [hpost3.1, hpost3.2.1, ← hA, ← hR1]
    rfl
  -- `v·r`
  refine exec_at (hb9 hp) run_b9 (Env.wf_nil _) hpc3 (match_nil _) fun s4 hm4 hpc4 ↦ ?_
  obtain ⟨fr4, hd4⟩ := fr3.block (match_nil _) hm4 (Env.wf_nil _) rfl (after_eq run_b9 ▸ keeps.2.2.2.2.2.1)
  simp only [NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b9_length, NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b9Length] at hpc4
  refine call_then hpc4 hmul (fr4.body.ewMulPre hS (by decide) (by decide)) fun s5 hpc5 hpost5 ↦ ?_
  obtain ⟨fr5, hP5⟩ := fr4.call hS hpost5
  have k5 : ∀ r, calleeSaved r = true → s5.data.regs.getXReg r = s4.data.regs.getXReg r :=
    hpost5.2.2.2.1
  have k4 := regs_eq_of (match_nil _) hm4 [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X29]
    (by decide)
  have hX : (⟨s4.data.regs.X0, s4.data.regs.X1⟩ : EW) = ⟨st.regs.X23, st.regs.X24⟩ := by
    show (⟨s4.data.regs.getXReg .X0, s4.data.regs.getXReg .X1⟩ : EW) =
      ⟨st.regs.getXReg .X23, st.regs.getXReg .X24⟩
    rw [reg_of hm4 (r := .X0) rfl, reg_of hm4 (r := .X1) rfl]
    simp only [Sym.eval, Env.ofMachine_regs, UInt64.ofBitVec_toBitVec]
    rw [k3 .X23 rfl, k3 .X24 rfl, k2 .X23 (by simp), k2 .X24 (by simp)]
  have hY : (⟨s4.data.regs.X2, s4.data.regs.X3⟩ : EW) = ⟨s2.data.regs.X25, s2.data.regs.X26⟩ := by
    show (⟨s4.data.regs.getXReg .X2, s4.data.regs.getXReg .X3⟩ : EW) =
      ⟨s2.data.regs.getXReg .X25, s2.data.regs.getXReg .X26⟩
    rw [reg_of hm4 (r := .X2) rfl, reg_of hm4 (r := .X3) rfl]
    simp only [Sym.eval, Env.ofMachine_regs, UInt64.ofBitVec_toBitVec]
    rw [k3 .X25 rfl, k3 .X26 rfl]
  have ht2 : (⟨s5.data.regs.X0, s5.data.regs.X1⟩ : EW) =
      (⟨st.regs.X23, st.regs.X24⟩ : EW) * (pts m0)[kk] := by
    rw [hpost5.1, hpost5.2.1, ← hR, ← hX, ← hY]
    rfl
  -- the sum, the test
  refine exec_at (hb10 hp) run_b10 (Env.wf_nil _) hpc5 (match_nil _) fun s6 hm6 hpc6 ↦ ?_
  obtain ⟨fr6, hd6⟩ := fr5.block (match_nil _) hm6 (Env.wf_nil _) rfl
    (after_eq run_b10 ▸ keeps.2.2.2.2.2.2.1)
  have hv' : (⟨s6.data.regs.X23, s6.data.regs.X24⟩ : EW) =
      ewOf st.dmem (fbOf m0 + BitVec.ofNat 64 (48 + 16 * kk)) * (1 + (pts m0)[kk]) +
        (⟨st.regs.X23, st.regs.X24⟩ : EW) * (pts m0)[kk] := by
    rw [← ht1, ← ht2]
    have h23 := hm6.regs .X23 _ rfl
    have h24 := hm6.regs .X24 _ rfl
    sym_simp at h23 h24
    simp only [Env.ofMachine_regs] at h23 h24
    rw [k5 .X27 rfl, reg_of hm4 (r := .X27) rfl] at h23
    rw [k5 .X28 rfl, reg_of hm4 (r := .X28) rfl] at h24
    simp only [Sym.eval, Env.ofMachine_regs] at h23 h24
    show (⟨s6.data.regs.getXReg .X23, s6.data.regs.getXReg .X24⟩ : EW) =
      ⟨s3.data.regs.getXReg .X0 ^^^ s5.data.regs.getXReg .X0,
        s3.data.regs.getXReg .X1 ^^^ s5.data.regs.getXReg .X1⟩
    rw [toBitVec_eq h23, toBitVec_eq h24]
    congr 1 <;> exact UInt64.xor_comm _ _
  have hP6 : pendOf s6.data.dmem (fbOf m0) = setP (pendOf st.dmem (fbOf m0)) kk none := by
    rw [hd6, hP5, hd4, hP3, hP2]
  have hval' : cont (pts m0) ((ents m0).drop (i + 1)) (pendOf s6.data.dmem (fbOf m0)) (kk + 1)
      ⟨s6.data.regs.X23, s6.data.regs.X24⟩ = target m0 := by
    rw [hP6, hv', ← hval, NativeRustcVm.Mle.cont_some _ _ hkP hsome]
  have kk6 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X29],
      s5.data.regs.getXReg r = s2.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact (k5 _ rfl).trans ((k4 _ (by simp)).trans (k3 _ rfl))
  have hx22 : (s2.data.regs.getXReg .X22).toBitVec.toNat = m0.regs.X4.toNat - kk := by
    rw [k2 .X22 (by simp)]; exact h22
  simp only [PcOk] at hpc6
  sym_simp at hpc6
  have hpc6' := pc_ne hpc6
  have heq : (s5.data.regs.getXReg .X22).toBitVec = 1#64 ↔ kk + 1 = m0.regs.X4.toNat := by
    rw [kk6 .X22 (by simp)]
    constructor
    · intro h; have := congrArg BitVec.toNat h; rw [hx22] at this; simp at this; omega
    · intro h; apply BitVec.eq_of_toNat_eq; rw [hx22]; simp; omega
  by_cases hlast : kk + 1 = m0.regs.X4.toNat
  · have hpc7 := hpc6'.2 (heq.mpr hlast)
    simp only [NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b10_length, NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b10Length] at hpc7
    refine exec_at (hb11 hp) run_b11 (Env.wf_nil _) hpc7 (match_nil _) fun s7 hm7 hpc7' ↦ ?_
    obtain ⟨fr7, -⟩ := fr6.block (match_nil _) hm7 (Env.wf_nil _) rfl
      (after_eq run_b11 ▸ keeps.2.2.2.2.2.2.2.1)
    simp only [PcOk] at hpc7'
    refine Eventually.mono (finish hp hS b17_restores.2 (by simp [slots, slots0])
      (hpc7'.trans (lbl_13 hp)) fr7.body ?_) fun _ h ↦ Or.inl h
    rw [← hval', NativeRustcVm.Mle.cont_top _ (by
      simp only [pts, NativeRustcVm.length_ewsOf]; omega)]
    show (⟨s7.data.regs.getXReg .X23, s7.data.regs.getXReg .X24⟩ : EW) = _
    rw [Match.reg_eq (match_nil _) hm7 rfl rfl, Match.reg_eq (r := .X24) (match_nil _) hm7 rfl rfl]
    rfl
  · have hpc7 := hpc6'.1 (fun h ↦ hlast (heq.mp h))
    refine .done _ (Or.inr ⟨hpc7.trans (lbl_7 hp), fr6, hi, show kk + 1 < m0.regs.X4.toNat by omega,
      ?_, ?_, ?_, ?_, ?_, hval'⟩)
    · have h := hm6.regs .X19 _ rfl
      sym_simp at h
      simp only [Env.ofMachine_regs] at h
      show (s6.data.regs.getXReg .X19).toBitVec = _
      rw [h, kk6 .X19 (by simp), k2 .X19 (by simp)]
      show st.regs.X19.toBitVec + _ = _
      rw [h19, NativeRustcVm.addr_add, show 16 * kk + 8 + 16 = 16 * (kk + 1) + 8 by omega]
    · show (s6.data.regs.getXReg .X20).toBitVec = _
      rw [Match.reg_eq (match_nil _) hm6 rfl rfl, kk6 .X20 (by simp)]
      have h := hm2.regs .X20 _ rfl
      simp only [Sym.eval] at h
      rw [h]
      show fbOf m0 + BitVec.ofNat 64 (1072 + kk) + BitVec.ofInt 64 1 = _
      rw [show BitVec.ofInt 64 1 = BitVec.ofNat 64 1 from rfl, NativeRustcVm.addr_add,
        show 1072 + kk + 1 = 1072 + (kk + 1) by omega]
    · show (s6.data.regs.getXReg .X21).toBitVec = _
      rw [Match.reg_eq (match_nil _) hm6 rfl rfl, kk6 .X21 (by simp)]
      have h := hm2.regs .X21 _ rfl
      simp only [Sym.eval] at h
      rw [h]
      show fbOf m0 + BitVec.ofNat 64 (48 + 16 * kk) + BitVec.ofInt 64 16 = _
      rw [show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, NativeRustcVm.addr_add,
        show 48 + 16 * kk + 16 = 48 + 16 * (kk + 1) by omega]
    · have h := hm6.regs .X22 _ rfl
      sym_simp at h
      simp only [Env.ofMachine_regs] at h
      show (s6.data.regs.getXReg .X22).toBitVec.toNat = m0.regs.X4.toNat - (kk + 1)
      rw [h, kk6 .X22 (by simp), BitVec.toNat_sub, hx22]
      simp only [BitVec.toNat_ofNat]
      omega
    · show (s6.data.regs.getXReg .X29).toNat = _
      rw [Match.reg_eq (match_nil _) hm6 rfl rfl, kk6 .X29 (by simp), k2 .X29 (by simp)]
      exact h29

end

end NativeRustcVmArm.Arrays.MleOfMultilinearEval
