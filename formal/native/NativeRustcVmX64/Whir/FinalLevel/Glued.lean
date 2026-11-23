module

public import NativeRustcVmX64.Whir.FinalLevel.GluedStep
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.GluedEval.Names

/-!
# `final_level`: the glued claims (x86-64)

From `b27` (the basis' value at `72`): the claim kept at `88`, `96`, the point's address at `56`,
the weight in R15, RBP, the glued claims' count (`b27`; none: to `b33`), their end at `104`
(`b28`), the loop (`gstep`): `glued`, to `b33` with `GB` and the weight `finalWeight`.
-/

namespace NativeRustcVmX64.Whir.Levels.FL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.FinalLevel

public section

theorem vGs_eval [Labels] (env : Env) {n : Nat} (h : env.load 1 504 8 = BitVec.ofNat 64 n)
    (hn : n < 11) : vGs.eval env = BitVec.ofNat 64 (6064 * n) := by
  simp only [vGs, Sym.eval, SBool.eval, CmpOp.apply, low_W64, h, ult_ofNat hn (by decide),
    ite_true]
  show BinOp.apply .mul .W64 (BitVec.ofNat 64 n) (BitVec.ofNat 64 6064) = _
  simp only [BinOp.apply, low_W64, ext_W64]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl]
  omega

theorem vG13_eval [Labels] (env : Env) {n : Nat} (h : env.load 1 504 8 = BitVec.ofNat 64 n)
    (hn : n < 11) {p : BitVec 64} (hp : env.load 0 2680 8 = p) :
    vG13.eval env = p + BitVec.ofNat 64 512 := by
  simp only [vG13, Sym.eval, SBool.eval, CmpOp.apply, low_W64, h, ult_ofNat hn (by decide),
    ite_true]
  show BinOp.apply .add .W64 (BitVec.ofNat 64 512) (env.load 0 2680 8) = _
  simp only [BinOp.apply, low_W64, ext_W64, hp]
  exact BitVec.add_comm _ _

theorem cNoG_eval [Labels] (env : Env) {n : Nat} (h : env.load 1 504 8 = BitVec.ofNat 64 n)
    (hn : n < 11) : cNoG.eval env = decide (n = 0) := by
  have hv := vGs_eval env h hn
  simp only [cNoG, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, hv,
    BitVec.and_self]
  by_cases h0 : n = 0
  · subst h0; rfl
  · rw [decide_eq_false h0, beq_eq_false_iff_ne]
    intro he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat] at this
    omega

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The glued claims**: `b27`, `b28`, the loop, to `b33`. -/
theorem glued (hp : Placed code k) (c : Ctx a s level ba b w rounds m0)
    (hge : ∀ g, Spec (Labels.label NativeRustcVmX64.Vm.GluedEval.entryLabel) (GluedEvalPre g) (GluedEvalPost g))
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {st : MachineState} {folded tail : Array EW} {claim : EW} {s5 : TState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b27Offset)) (hc : Core level m0 st.data folded)
    (hbx : reg st.data .rbx = loc m0 640) (h12 : reg st.data .r12 = claim.c0.toBitVec)
    (h15 : reg st.data .r15 = claim.c1.toBitVec)
    (h48 : NativeRustcVm.WordAt st.data.dmem (loc m0 48)
      (.ofBitVec (BitVec.ofNat 64 (w.alphas ++ tail).size)))
    (hpt : NativeRustcVm.BufEWAt st.data.dmem (loc m0 632) 30 (w.alphas ++ tail).toList)
    (hb72 : NativeRustcVm.EWAt st.data.dmem (loc m0 72)
      (weightAt (reg m0 .r8).toNat b w tail 0))
    (htail : NativeRustcVm.EWsAt st.data.dmem (loc m0 1120) tail.toList) (htn : tail.size = mu m0)
    (hts : TStateAt st.data.dmem (tA m0) a s5) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b33Offset) →
      GB a level m0 folded tail claim (finalWeight (reg m0 .r8).toNat b w tail) s5 st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have g := c.geo
  have hfo : 2 ^ mu m0 + level.fold ≤ 64 := c.fold
  have hal : w.alphas.size + mu m0 ≤ 30 := c.alphas
  have hf := hc.fr
  have hws := (c.whir_at hf.same).1
  have hn10 : w.glued.size ≤ 10 := hws.glued_le
  have hPl2 : (w.alphas ++ tail).toList.length ≤ 30 := by
    rw [Array.length_toList, Array.size_append, htn]; omega
  obtain ⟨hb0, hb1⟩ := ewAt_iff'.mp hb72
  rw [show off (loc m0 72) 8 = loc m0 80 from off_off _ _ _] at hb1
  -- `b27`: the claim, the point's address, the weight; the claims' count.
  let env1 := argEnv m0 st.data 2672 8 [(pA m0, 63200)] (fun _ ↦ 0) 0
  have hwf1 : env1.WF :=
    c.wf1 hf.frame.kept (show NativeRustcVm.Mapped st.data.dmem (pA m0) 63200 from
      Mapped.keeps c.pout.1.1 hf.frame.kept) g.pW
      (g.pS.imp_left fun h ↦ Nat.le_trans h (Nat.sub_le_sub_left (by decide) _))
  have h2680 : env1.load 0 2680 8 = pA m0 :=
    load_ofMachine (r := 0) (o := 2680) rfl (c.arg_keep hf.same)
  have hm1 : Match env1 rowsS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨Frame.rsp_evalA hf.frame, trivial⟩ trivial trivial
      ⟨h2680.trans (eval_ptr rfl).symm, trivial⟩
  refine exec_at (infix_of b27_in_code (by simp [b27]) hp) exit_b27 hwf1 nofun hpc hm1
    fun st1 hm1' hpc1 ↦ ?_
  obtain ⟨hmid1, hW1, h56, h88, h96, hr151, hrbp1, hr131, hrsi1, hkr1⟩ := ok_b27
  have e1 : ∀ {r : Reg64} {v : Sym}, (after b27 rowsS).reg r = some v →
      reg st1.data r = v.eval env1 := fun h ↦ hm1'.regs _ _ h
  obtain ⟨hf1, hs1⟩ := c.blk hf hwf1 hm1' hmid1 (hi := 104) (by omega) (hW1.le (by decide))
  have hk1 : KeepF m0 st.data.dmem st1.data.dmem 56 48 :=
    keepF_blk hwf1 hm1' (writesIn_of_mid hmid1) hW1 (by decide)
  have l504 : env1.load 1 504 8 = BitVec.ofNat 64 w.glued.size :=
    load_ofMachine (r := 1) (o := 504) rfl hws.glued_len
  have hgb0 : GB a level m0 folded tail claim (weightAt (reg m0 .r8).toNat b w tail 0) s5
      st1.data :=
    ⟨hc.keepF hf1 (e1 (hkr1 .r14 (by simp))) hk1 (by omega) hfo,
      wordAt_written hm1' (r := 0) (o := 88) rfl (by omega) h88 h12,
      wordAt_written hm1' (r := 0) (o := 96) rfl (by omega) h96 h15,
      hk1.ews (xs := tail.toList) (by omega) (by rw [Array.length_toList]; omega)
        (by rw [Array.length_toList]; omega) htail,
      c.ts_frame (hi := 104) (by omega) (hm1'.kept hwf1) hs1 hts,
      (e1 hr151).trans (load_ofMachine (r := 0) (o := 72) rfl hb0),
      (e1 hrbp1).trans (load_ofMachine (r := 0) (o := 80) rfl hb1)⟩
  simp only [PcOk, cNoG_eval env1 l504 (by omega)] at hpc1
  by_cases h0 : w.glued.size = 0
  · rw [decide_eq_true h0] at hpc1
    simp only [ite_true] at hpc1
    refine cont st1 (hpc1.trans (label_of_infix hp b33_in_code rfl)) ?_
    rw [← weightAt_size, h0]
    exact hgb0
  rw [decide_eq_false h0] at hpc1
  simp only [Bool.false_eq_true, ite_false] at hpc1
  have hpc1' : st1.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b28Offset) := hpc1
  -- `b28`: the claims' end.
  have hsi1 : reg st1.data .rsi = BitVec.ofNat 64 (6064 * w.glued.size) :=
    (e1 hrsi1).trans (vGs_eval env1 l504 (by omega))
  have h131 : reg st1.data .r13 = pA m0 + BitVec.ofNat 64 512 :=
    (e1 hr131).trans (vG13_eval env1 l504 (by omega) h2680)
  let env2 := argEnv m0 st1.data 2672 8 [] (fun _ ↦ 0) 0
  have hwf2 : env2.WF := c.wf0 hf1.frame.kept
  refine exec_at (infix_of b28_in_code (by simp [b28]) hp) exit_b28 hwf2 nofun hpc1'
    (match_retS hf1) fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hW2, h104, hkr2⟩ := ok_b28
  obtain ⟨hf2, hs2⟩ := c.blk hf1 hwf2 hm2 hmid2 (hi := 112) (by omega) (hW2.le (by decide))
  have hk2 : KeepF m0 st1.data.dmem st2.data.dmem 104 8 :=
    keepF_blk hwf2 hm2 (writesIn_of_mid hmid2) hW2 (by decide)
  have hk2r : ∀ r ∈ six, reg st2.data r = reg st1.data r := fun r hr ↦ hm2.regs r _ (hkr2 r hr)
  have hw104 : NativeRustcVm.WordAt st2.data.dmem (loc m0 104)
      (.ofBitVec (pA m0 + BitVec.ofNat 64 (512 + 6064 * w.glued.size))) := by
    refine wordAt_written hm2 (r := 0) (o := 104) rfl (by omega) h104 ?_
    show BinOp.apply .add .W64 (reg st1.data .r13) (reg st1.data .rsi) = _
    simp only [BinOp.apply, low_W64, ext_W64]
    rw [h131, hsi1, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hpts : NativeRustcVm.EWsAt st.data.dmem (loc m0 640) (w.alphas ++ tail).toList := by
    have := hpt.2.2
    rwa [show loc m0 632 + 8#64 = loc m0 640 from off_add _ _ _] at this
  have hI0 : GInv a level b w m0 folded tail claim s5 0 st2.data := by
    refine ⟨?_, by omega, (hk2r .r13 (by simp [six])).trans h131, hw104, ?_, ?_, ?_⟩
    · refine ⟨hgb0.core.keepF hf2 (hk2r .r14 (by simp [six])) hk2 (by omega) hfo,
        hk2.word (by omega) (by omega) (by omega) hgb0.w88,
        hk2.word (by omega) (by omega) (by omega) hgb0.w96,
        hk2.ews (xs := tail.toList) (by omega) (by rw [Array.length_toList]; omega)
          (by rw [Array.length_toList]; omega) hgb0.tail,
        c.ts_frame (hi := 112) (by omega) (hm2.kept hwf2) hs2 hgb0.ts,
        (hk2r .r15 (by simp [six])).trans hgb0.r15, (hk2r .rbp (by simp [six])).trans hgb0.rbp⟩
    · exact hk2.word (by omega) (by omega) (by omega)
        (wordAt_written hm1' (r := 0) (o := 56) rfl (by omega) h56
          (w := .ofBitVec (loc m0 640)) hbx)
    · exact hk2.word (by omega) (by omega) (by omega)
        (hk1.word (by omega) (by omega) (by omega) h48)
    · exact hk2.ews (xs := (w.alphas ++ tail).toList) (by omega) (by omega) (by omega)
        (hk1.ews (xs := (w.alphas ++ tail).toList) (by omega) (by omega) (by omega) hpts)
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b29Offset) := hpc2
  -- the loop
  refine Eventually.bind (loop (Q := fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b33Offset) ∧
      GB a level m0 folded tail claim (finalWeight (reg m0 .r8).toNat b w tail) s5 st'.data)
    (fun n st' ↦ ∃ i, n = w.glued.size - i ∧ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b29Offset) ∧
      GInv a level b w m0 folded tail claim s5 i st'.data)
    (fun _ st' ⟨i, hn, hpc', hI⟩ ↦ (gstep hp c hge hmul hpc' htn hI).mono fun st'' h ↦ by
      rcases h with ⟨hlt, hpc'', hI'⟩ | ⟨heq, hpc'', hgb⟩
      · exact Or.inr ⟨w.glued.size - (i + 1), by have := hI.lt; omega, i + 1, rfl, hpc'', hI'⟩
      · refine Or.inl ⟨hpc'', ?_⟩
        rw [← weightAt_size, ← heq]
        exact hgb)
    ⟨0, rfl, hpc2', hI0⟩) fun st' ⟨hpc', hgb⟩ ↦ cont st' hpc' hgb

end

end NativeRustcVmX64.Whir.Levels.FL
