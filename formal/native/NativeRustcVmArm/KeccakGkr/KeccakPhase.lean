module

public import NativeRustcVmArm.Code.Vm.KeccakPhase.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Code.Vm.VerifyKeccak.Names
public import NativeRustcVmArm.KeccakGkr.KeccakPhase.Pre
public import NativeVm.Equiv.KeccakRmfe

/-!
# `keccak_phase` meets its contract

`b0` saves the registers in its 480-byte frame, zeroes the 25 output lanes at the frame's base
and reads `KECCAK`'s value count `n`; `present = min (n - 40) 25`; the branch to `b1` (`None`) is
never taken (`keccakOut ≤ n`). `b2` copies the `present` lanes from `values[40..]` (`memcpy`), `b3`
calls `verify_keccak` on `KECCAK`'s point and the lanes, `b4` returns its verdict.
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakPhase

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.KeccakPhase
open LeanVM.Protocol.Verifier (opKeccak keccakOut)
open NativeRustcVm.KeccakGkr (scratchBytes outBytes)
open NativeRustcVm (Region InAny)

public section

theorem opKeccak_eq : opKeccak = 5 := by decide +kernel

theorem slots_ge : ∀ p ∈ slots, 400 ≤ p.1 := by decide

theorem ofInt_0 : BitVec.ofInt 64 0 = 0#64 := rfl

variable [Host] {k : Nat}

/-- **`keccak_phase` meets its contract.** -/
theorem keccakPhase_spec (hp : Placed code k)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hvk : ∀ a s cs inst output, Spec (Labels.label NativeRustcVmArm.Vm.VerifyKeccak.entryLabel)
      (VerifyKeccakPre a s cs inst output) (VerifyKeccakPost a s cs inst output)) :
    ∀ a s cs layout evals, Spec (Labels.label NativeRustcVmArm.Vm.KeccakPhase.entryLabel)
      (KeccakPhasePre a s cs layout evals) (KeccakPhasePost a s cs layout evals) := by
  intro a s cs layout evals m0 hpre
  rw [show Labels.label NativeRustcVmArm.Vm.KeccakPhase.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakPhase.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.KeccakPhase.entryOffset) NativeRustcVmArm.Vm.KeccakPhase.entry_at]
  obtain ⟨hS, hrc, hpj, hrh, hts, hcl, hncs, hev, hlog, hpsz, h40, hA⟩ := hpre
  have hn : Nums a m0 := nums_of hS hA
  have hN := hn.hN
  have hSP := m0.regs.SP.toNat_lt
  have hfb := fb_toNat hn
  -- `KECCAK`'s entry.
  obtain ⟨hev6, hevi⟩ := hev
  have h5 : 5 < evals.size := by rw [hev6]; decide
  have hget : evals.getD opKeccak (#[], #[]) = evals[5] := by
    rw [opKeccak_eq, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h5, Option.getD_some]
  have he5 := hevi 5 h5
  rw [← hget] at he5
  have hrun : (keccakPhase layout evals).run s =
      (verifyKeccak m0.regs.X1.toNat (evals.getD opKeccak (#[], #[])).1
        (lanes (evals.getD opKeccak (#[], #[])).2)).run s := by
    rw [hlog]; rfl
  generalize evals.getD opKeccak (#[], #[]) = E at he5 hpsz h40 hrun
  obtain ⟨point, values⟩ := E
  dsimp only at hpsz h40 hrun
  rw [keccakOut_eq] at h40
  obtain ⟨⟨hpl, hpn, hpv⟩, ⟨hvl, hvn, hvv⟩⟩ := he5
  rw [Array.length_toList] at hpl hvl hpn hvn
  have hp30 : point.size ≤ 30 := hpl
  have ea : ∀ o i : Nat, m0.regs.X2.toBitVec + BitVec.ofNat 64 o + BitVec.ofNat 64 i =
      m0.regs.X2.toBitVec + BitVec.ofNat 64 (o + i) := fun o i ↦ NativeRustcVm.addr_add_add _ _ _
  have hpn' : NativeRustcVm.WordAt m0.dmem (m0.regs.X2.toBitVec + BitVec.ofNat 64 9840)
      point.size.toUInt64 := hpn
  have hpv' : NativeRustcVm.EWsAt m0.dmem (m0.regs.X2.toBitVec + BitVec.ofNat 64 9848)
      point.toList := by
    have := hpv; rw [ea] at this; exact this
  have hvn' : NativeRustcVm.WordAt m0.dmem (m0.regs.X2.toBitVec + BitVec.ofNat 64 10328)
      values.size.toUInt64 := by
    have := hvn; rw [ea] at this; exact this
  have hvv' : NativeRustcVm.EWsAt m0.dmem (m0.regs.X2.toBitVec + BitVec.ofNat 64 10336)
      values.toList := by
    have := hvv; rw [ea, ea] at this; exact this
  -- The entry's environment.
  have hfok := frame_ok hn hS
  have hevok : Mapped m0.dmem m0.regs.X2.toBitVec 11808 :=
    (Areas.ok hA (r := ⟨m0.regs.X2.toBitVec, NativeRustcVm.Tables.tableEvalsBytes⟩)
      (Or.inr (by simp))).1
  have hap0 : Apart (fb m0) 480 m0.regs.X2.toBitVec 11808 := by
    unfold Apart; rw [hfb, UInt64.toNat_toBitVec]; have := hn.eS; omega
  have hwf0 : (Env.ofMachine m0 [(fb m0, 480), (m0.regs.X2.toBitVec, 11808)]).WF :=
    Env.wf_of ⟨⟨hfok.1, hfok.2⟩, ⟨hevok, hn.eW⟩, trivial⟩
      (List.Pairwise.cons (fun e he ↦ by simp at he; subst he; exact hap0)
        (List.pairwise_singleton _ _))
  have hm0 : Match (Env.ofMachine m0 [(fb m0, 480), (m0.regs.X2.toBitVec, 11808)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS (by rw [stack_eq]; decide) (by decide),
      ⟨rfl, ⟨fun h ↦ absurd h (by decide), trivial⟩⟩⟩
      (by
        show m0.regs.SP.toBitVec = fb m0 + BitVec.ofInt 64 (480 : Nat)
        rw [BitVec.ofInt_natCast, base_add_eq])
      ⟨by
        show m0.regs.X2.toBitVec = m0.regs.X2.toBitVec + BitVec.ofInt 64 0
        rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
      trivial trivial trivial
  have hL : (Env.ofMachine m0 [(fb m0, 480), (m0.regs.X2.toBitVec, 11808)]).load 1 10328 8 =
      BitVec.ofNat 64 values.size := load_word hvn'
  -- `b0`: the prologue, the zeros, the bounds.
  refine exec_then (b0_in_code.trans hp.1 (by simp [b0])) run_b0 hwf0 hm0 fun st hm1 hpc ↦ ?_
  have hfr1 : Fr m0 480 keccakPhaseStack slots keep (fun _ ↦ False) st.data :=
    Fr.ofPrologue (rs := [(m0.regs.X2.toBitVec, 11808)]) hS.2.1 (by rw [stack_eq]; decide) hm1
      hwf0 rfl (by decide) slots_le (by decide) (by decide)
  have hz1 := zeros hm1 (b := fb m0) rfl (by decide)
  have hv92 : values.size ≤ 92 := hvl
  have h8 : (st.data.regs.getXReg .X8).toBitVec = BitVec.ofNat 64 values.size := by
    rw [hm1.regs .X8 _ rfl]; exact hL
  have h9 : (st.data.regs.getXReg .X9).toNat = min (values.size - 40) 25 := by
    rw [← UInt64.toNat_toBitVec, hm1.regs .X9 _ rfl]
    sym_simp
    rw [hL]
    generalize values.size = v at h40 hv92 ⊢
    interval_cases v <;> decide +kernel
  have h2 : st.data.regs.getXReg .X2 = m0.regs.X2 := by
    apply UInt64.toBitVec_inj.mp
    rw [hm1.regs .X2 _ rfl]
    show m0.regs.X2.toBitVec + BitVec.ofInt 64 0 = _
    rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  simp only [PcOk] at hpc
  split at hpc
  case isFalse hc =>
    exfalso; apply hc
    sym_simp
    rw [hL]
    generalize values.size = v at h40 hv92 ⊢
    interval_cases v <;> decide +kernel
  rw [show Labels.label NativeRustcVmArm.Vm.KeccakPhase.label_2 = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakPhase.b2Offset) from hp.label (j := NativeRustcVmArm.Vm.KeccakPhase.b2Offset) NativeRustcVmArm.Vm.KeccakPhase.label_2_at]
    at hpc
  -- `b2`: `memcpy` of the present lanes.
  have hwf1 := wfF hn hS hfr1
  refine exec_at (b2_in_code.trans hp.1 (by simp [b2])) run_b2 hwf1 hpc (matchF hn hS hfr1)
    fun st2 hm2 hpc2 ↦ ?_
  have hfr2 : Fr m0 480 keccakPhaseStack slots keep (fun _ ↦ False) st2.data :=
    Fr.ofBlock hfr1 (matchF hn hS hfr1) hm2 hwf1 rfl rfl rfl (fun r hr ↦ by
      simp only [keep, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩)
  have hd2 : st2.data.dmem = st.data.dmem := hm2.dmem_eq hwf1 rfl
  generalize hpr : min (values.size - 40) 25 = pr at h9
  have hpr25 : pr ≤ 25 := by omega
  have e20 : st2.data.regs.X0.toBitVec = fb m0 := by
    show (st2.data.regs.getXReg .X0).toBitVec = _
    rw [hm2.regs .X0 _ rfl]; simp [Sym.eval]
  have e21 : st2.data.regs.X1.toBitVec =
      m0.regs.X2.toBitVec + BitVec.ofNat 64 10336 + BitVec.ofNat 64 640 := by
    show (st2.data.regs.getXReg .X1).toBitVec = _
    rw [hm2.regs .X1 _ rfl]
    sym_simp
    have hlt : (BitVec.ofNat 64 values.size).ult (BitVec.ofNat 64 93) = true := by
      rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show values.size < 2 ^ 64 by omega)]
      simp only [decide_eq_true_eq]; omega
    simp only [Env.ofMachine_regs, h8, h2, hlt, ↓reduceIte]
  have e22 : st2.data.regs.X2.toNat = 16 * pr := by
    show (st2.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [hm2.regs .X2 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs, NativeRustcVmArm.Arrays.lsl4, BitVec.toNat_ofNat,
      UInt64.toNat_toBitVec, h9]
    omega
  have hX2 := hn.eW
  have hsrc : (m0.regs.X2.toBitVec + BitVec.ofNat 64 10336 + BitVec.ofNat 64 640).toNat =
      m0.regs.X2.toNat + 10976 := by
    rw [ea]; exact NativeRustcVm.toNat_add_ofNat (by simp only [UInt64.toNat_toBitVec] at *; omega)
  have hpre2 : MemcpyPre st2.data := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [e20, e21, e22]
    · exact Mapped.kept' (fun i hi ↦ hfok.1 i (by omega)) hfr2.kept
    · refine Mapped.kept' (fun i hi ↦ ?_) hfr2.kept
      rw [ea, NativeRustcVm.addr_add_add]; exact hevok _ (by omega)
    · unfold NoWrap; rw [hfb]; omega
    · unfold NoWrap; rw [hsrc]; omega
    · unfold Apart; rw [hfb, hsrc]; have := hn.eS; omega
  have hpc2' : st2.pc = Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel ∧
      retOf st2.data = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakPhase.b3Offset) := hpc2
  refine Fr.leafIn hfr2 hS.2.1 (N' := 0) (lo := 0) (n := 16 * pr) (by rw [stack_eq]; decide)
    (by omega) (fun r hr ↦ keep_cs r hr)
    (fun q hq ↦ ⟨slots_le q hq, .inr (by have := slots_ge q hq; omega)⟩) (fun _ h ↦ h.elim)
    hmemcpy hpc2' hpre2
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ .inr (.inl (by
      rw [e20, e22] at hq'; rw [NativeRustcVm.addr_add_zero]; exact hq')), hq.2.2.2⟩)
    fun m3 hfr3 hq3 hcs3 ↦ ?_
  obtain ⟨-, hcp, hs3, -⟩ := hq3
  rw [e20, e21, e22, ← hpr] at hcp
  rw [e20, e22, ← hpr] at hs3
  -- The output lanes in the frame.
  have hv2 : NativeRustcVm.EWsAt st2.data.dmem (m0.regs.X2.toBitVec + BitVec.ofNat 64 10336)
      values.toList :=
    evals_keep hn hfr2 hvv' (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList]; omega)
      (by omega)
  have hz2 : ∀ i < 50, NativeRustcVm.WordAt st2.data.dmem (fb m0 + BitVec.ofNat 64 (8 * i)) 0 :=
    fun i hi ↦ by rw [hd2]; exact hz1 i hi
  have hlanes : NativeRustcVm.EWsAt m3.dmem (fb m0) (lanes values).toList :=
    lanes_at (by rw [hfb]; omega) hz2 hv2 h40 hcp hs3
  -- `b3`: `verify_keccak`.
  have hwf3 : (Env.ofMachine m3 [(fb m0, 480), (m0.regs.X2.toBitVec, 11808)]).WF :=
    Env.wf_of ⟨⟨Mapped.kept' hfok.1 hfr3.kept, hfok.2⟩, ⟨Mapped.kept' hevok hfr3.kept, hn.eW⟩,
      trivial⟩
      (List.Pairwise.cons (fun e he ↦ by simp at he; subst he; exact hap0)
        (List.pairwise_singleton _ _))
  have k25 : m3.regs.getXReg .X25 = m0.regs.X2 := by
    rw [hcs3 .X25 rfl]
    exact (reg_of hm2 (r := .X25) (v := .reg .X2) rfl rfl).trans h2
  have hm3 : Match (Env.ofMachine m3 [(fb m0, 480), (m0.regs.X2.toBitVec, 11808)]) evS m3 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS (by rw [stack_eq]; decide) (by decide),
      ⟨rfl, ⟨fun h ↦ absurd h (by decide), trivial⟩⟩⟩
      (by rw [hfr3.sp]; simp [Sym.eval])
      ⟨by
        show (m3.regs.getXReg .X25).toBitVec = m0.regs.X2.toBitVec + BitVec.ofInt 64 0
        rw [ofInt_0, BitVec.add_zero, k25], trivial⟩
      trivial trivial trivial
  have hpn3 : NativeRustcVm.WordAt m3.dmem (m0.regs.X2.toBitVec + BitVec.ofNat 64 9840)
      point.size.toUInt64 :=
    evals_keep hn hfr3 hpn' (by rw [NativeRustcVm.length_wordBytes]; decide) (by decide)
  have hL3 : (Env.ofMachine m3 [(fb m0, 480), (m0.regs.X2.toBitVec, 11808)]).load 1 9840 8 =
      BitVec.ofNat 64 point.size := load_word hpn3
  refine exec_then (b3_in_code.trans hp.1 (by simp [b3])) run_b3 hwf3 hm3 fun st4 hm4 hpc4 ↦ ?_
  have hfr4 : Fr m0 480 keccakPhaseStack slots keep (fun _ ↦ False) st4.data :=
    Fr.ofBlock hfr3 hm3 hm4 hwf3 rfl rfl rfl (fun r hr ↦ by
      simp only [keep, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩)
  have hd4 : st4.data.dmem = m3.dmem := hm4.dmem_eq hwf3 rfl
  have chain : ∀ r r' : XReg, calleeSaved r = true → st2.data.regs.getXReg r =
      st.data.regs.getXReg r' → st.data.regs.getXReg r' = m0.regs.getXReg r' →
      m3.regs.getXReg r = m0.regs.getXReg r' := fun r r' hr h1 h2 ↦ by
    rw [hcs3 r hr, h1, h2]
  have e40 : st4.data.regs.X0 = m0.regs.X0 :=
    (reg_of hm4 (r := .X0) (v := .reg .X22) rfl rfl).trans (chain .X22 .X0 rfl
      (reg_of hm2 (r := .X22) (v := .reg .X0) rfl rfl) (reg_of hm1 (v := .reg .X0) rfl rfl))
  have e41 : st4.data.regs.X1 = m0.regs.X1 :=
    (reg_of hm4 (r := .X1) (v := .reg .X23) rfl rfl).trans (chain .X23 .X1 rfl
      (reg_of hm2 (r := .X23) (v := .reg .X1) rfl rfl) (reg_of hm1 (v := .reg .X1) rfl rfl))
  have e45 : st4.data.regs.X5 = m0.regs.X3 :=
    (reg_of hm4 (r := .X5) (v := .reg .X21) rfl rfl).trans (chain .X21 .X3 rfl
      (reg_of hm2 (r := .X21) (v := .reg .X3) rfl rfl) (reg_of hm1 (v := .reg .X3) rfl rfl))
  have e46 : st4.data.regs.X6 = m0.regs.X4 :=
    (reg_of hm4 (r := .X6) (v := .reg .X20) rfl rfl).trans (chain .X20 .X4 rfl
      (reg_of hm2 (r := .X20) (v := .reg .X4) rfl rfl) (reg_of hm1 (v := .reg .X4) rfl rfl))
  have e47 : st4.data.regs.X7 = m0.regs.X5 :=
    (reg_of hm4 (r := .X7) (v := .reg .X19) rfl rfl).trans (chain .X19 .X5 rfl
      (reg_of hm2 (r := .X19) (v := .reg .X5) rfl rfl) (reg_of hm1 (v := .reg .X5) rfl rfl))
  have hplt : (BitVec.ofNat 64 point.size).ult (BitVec.ofNat 64 31) = true := by
    rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show point.size < 2 ^ 64 by omega)]
    simp only [decide_eq_true_eq]; omega
  have e42 : st4.data.regs.X2.toBitVec = m0.regs.X2.toBitVec + BitVec.ofNat 64 9848 := by
    show (st4.data.regs.getXReg .X2).toBitVec = _
    rw [hm4.regs .X2 _ rfl]
    sym_simp
    simp only [hL3, hplt, ↓reduceIte, Env.base_ofMachine_eq]
    rfl
  have e43 : st4.data.regs.X3.toNat = point.size := by
    show (st4.data.regs.getXReg .X3).toBitVec.toNat = _
    rw [hm4.regs .X3 _ rfl]
    sym_simp
    simp only [hL3, hplt, ↓reduceIte, BitVec.toNat_ofNat]
    omega
  have e44 : st4.data.regs.X4.toBitVec = fb m0 := by
    show (st4.data.regs.getXReg .X4).toBitVec = _
    rw [hm4.regs .X4 _ rfl]; simp [Sym.eval]
  have hip : (m0.regs.X2.toBitVec + BitVec.ofNat 64 9848).toNat = m0.regs.X2.toNat + 9848 :=
    NativeRustcVm.toNat_add_ofNat (by rw [UInt64.toNat_toBitVec]; omega)
  have hpre4 : VerifyKeccakPre a s cs point (lanes values) st4.data := by
    refine ⟨hfr4.stackOk hS (by decide) (by rw [stack_eq, vk_stack_eq]),
      rc_keep hn hfr4 hrc, project_keep hn hfr4 hpj, rho_keep hn hfr4 hrh, ?_, ?_, hncs, ?_,
      ?_, hpl, ?_, lanes_size values, ?_, ?_⟩
    · rw [e40]; exact ts_keep hn hfr4 hts
    · rw [e46]
      exact NativeRustcVm.Tables.ClaimsWAt.of_same hcl
        (same_m0 hn hfr4 (n := NativeRustcVm.Layout.claimsBytes) (by rw [e_cl]; exact hn.cW)
          (by rw [e_cl]; exact hn.cS))
    · rw [e43]
    · rw [e41]; exact hpsz
    · rw [e42]
      exact evals_keep hn hfr4 hpv'
        (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList]; omega) (by decide)
    · rw [e44, hd4]; exact hlanes
    · rw [e40, e42, e44, e45, e46, e47]
      exact areas_vk hn hA hfr4 hp30 hip
        (Mapped.kept' (fun i hi ↦ by rw [NativeRustcVm.addr_add_add]; exact hevok _ (by omega))
          hfr4.kept) hfb (Mapped.kept' (fun i hi ↦ hfok.1 i (by omega)) hfr4.kept)
  have hpc4' : st4.pc = Labels.label NativeRustcVmArm.Vm.VerifyKeccak.entryLabel ∧
      retOf st4.data = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakPhase.b4Offset) := hpc4
  refine Fr.leafAt (Fr.weaken (outs' := outs m0) hfr4) hS.2.1 (N' := verifyKeccakStack)
    (by rw [stack_eq, vk_stack_eq]) (fun r hr ↦ keep_cs r hr) slots_le (outs_frame hn)
    (hvk a s cs point (lanes values)) hpc4' hpre4
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q ⟨w, hw, hq'⟩ ↦ by
      rcases List.mem_cons.mp hw with rfl | hw
      · exact .inl hq'
      · refine .inr ⟨w, ?_, hq'⟩
        rw [e40, e45, e46, e47] at hw; exact hw, hq.2.2.2⟩)
    fun m5 hfr5 hq5 hcs5 ↦ ?_
  -- `b4`: the epilogue.
  have hwf5 := wfF hn hS hfr5
  refine exec_then (b4_in_code.trans hp.1 (by simp [b4])) run_b4 hwf5 (matchF hn hS hfr5)
    fun st6 hm6 hpc6 ↦ .done _ ?_
  obtain ⟨hret, hsv⟩ := hfr5.exit (rs := []) hm6 hwf5 (by decide)
  have hd6 : st6.data.dmem = m5.dmem := hm6.dmem_eq hwf5 rfl
  have hx6 : st6.data.regs.X0 = m5.regs.X0 :=
    Match.reg_eq (matchF hn hS hfr5) hm6 (r := .X0) rfl rfl
  simp only [PcOk] at hpc6
  obtain ⟨hq50, hq51, -, -⟩ := hq5
  rw [e41] at hq50 hq51
  refine ⟨by rw [hpc6, hret], ?_, fun outs' pt sl s' hr ↦ ?_, fun q hq ↦ ?_, hsv⟩
  · rw [hx6, hq50, hrun]
  · rw [hrun] at hr
    obtain ⟨a1, a2, a3⟩ := hq51 outs' pt sl s' hr
    rw [e40] at a1; rw [e46] at a2; rw [e47] at a3
    rw [hd6]; exact ⟨a1, a2, a3⟩
  · rw [hd6]
    refine hfr5.same q fun h ↦ hq ?_
    rcases h with h | ⟨w, hw, h⟩
    · exact ⟨stackRegion m0 keccakPhaseStack, List.mem_cons_self, h⟩
    · exact ⟨w, List.mem_cons_of_mem _ hw, h⟩

end

end NativeRustcVmArm.KeccakGkr.KeccakPhase
