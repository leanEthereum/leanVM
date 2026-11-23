module

public import NativeRustcVmX64.Whir.FinalLevel.Point
public import NativeRustcVmX64.Code.Vm.BasisWEval.Names

/-!
# `final_level`: the basis at the rotated point (x86-64)

From `b25`: the point's length kept at `48`, `BasisW::eval(&out, basis, rotated)` into the
frame's `Option<EW>` at `64` (`b25`), its tag tested (`b26`, always `Some`): `rotate`, to `b27`
with the basis' value at `72`.
-/

namespace NativeRustcVmX64.Whir.Levels.FL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.FinalLevel

public section

theorem one_iff {x q : BitVec 64} {n : Nat} :
    NativeRustcVm.InAny [⟨x, n⟩] q ↔ NativeRustcVm.InRange x n q := by
  simp only [NativeRustcVm.inAny_cons_iff, NativeRustcVm.inAny_nil, or_false,
    NativeRustcVm.Region.Holds]

theorem vBn_eval [Labels] (env : Env) {n : Nat} (h : env.load 0 144 8 = BitVec.ofNat 64 n)
    (hn : n < 31) : vBn.eval env = BitVec.ofNat 64 n := by
  simp only [vBn, Sym.eval, SBool.eval, CmpOp.apply, low_W64, h, ult_ofNat hn (by decide),
    ite_true]

theorem vBp_eval [Labels] (env : Env) {n : Nat} (h : env.load 0 144 8 = BitVec.ofNat 64 n)
    (hn : n < 31) : vBp.eval env = env.base 0 + BitVec.ofInt 64 152 := by
  simp only [vBp, Sym.eval, SBool.eval, CmpOp.apply, low_W64, h, ult_ofNat hn (by decide),
    Bool.not_true, Bool.false_eq_true, ite_false]

theorem cTag64_eval [Labels] (env : Env) {u : UInt64} (hu : u = 0 ∨ u = 1)
    (h : env.load 0 64 4 = BitVec.ofNat 64 u.toNat) : cTag64.eval env = (u != 1) := by
  simp only [cTag64, SBool.eval, Sym.eval, CmpOp.apply, h]
  rcases hu with rfl | rfl <;> decide

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The basis at the rotated point**: `b25`, `BasisW::eval`, `b26`, to `b27`. -/
theorem rotate (hp : Placed code k) (c : Ctx a s level ba b w rounds m0)
    (hbw : ∀ ba b, Spec (Labels.label NativeRustcVmX64.Vm.BasisWEval.entryLabel) (BasisWEvalPre ba b) (BasisWEvalPost b))
    {st : MachineState} {folded tail rot : Array EW} {claim : EW} {s5 : TState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b25Offset)) (hc : Core level m0 st.data folded)
    (hbx : reg st.data .rbx = loc m0 640) (h12 : reg st.data .r12 = claim.c0.toBitVec)
    (h15 : reg st.data .r15 = claim.c1.toBitVec)
    (h13 : reg st.data .r13 = BitVec.ofNat 64 (w.alphas ++ tail).size)
    (h56 : NativeRustcVm.WordAt st.data.dmem (loc m0 56) (.ofBitVec (reg m0 .r9)))
    (hpt : NativeRustcVm.BufEWAt st.data.dmem (loc m0 632) 30 (w.alphas ++ tail).toList)
    (hrot : NativeRustcVm.BufEWAt st.data.dmem (loc m0 144) 30 rot.toList)
    (htail : NativeRustcVm.EWsAt st.data.dmem (loc m0 1120) tail.toList) (htn : tail.size = mu m0)
    (hts : TStateAt st.data.dmem (tA m0) a s5) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b27Offset) → Core level m0 st'.data folded →
      reg st'.data .rbx = loc m0 640 → reg st'.data .r12 = claim.c0.toBitVec →
      reg st'.data .r15 = claim.c1.toBitVec →
      NativeRustcVm.WordAt st'.data.dmem (loc m0 48)
        (.ofBitVec (BitVec.ofNat 64 (w.alphas ++ tail).size)) →
      NativeRustcVm.BufEWAt st'.data.dmem (loc m0 632) 30 (w.alphas ++ tail).toList →
      NativeRustcVm.EWAt st'.data.dmem (loc m0 72) (b.eval rot) →
      NativeRustcVm.EWsAt st'.data.dmem (loc m0 1120) tail.toList →
      TStateAt st'.data.dmem (tA m0) a s5 → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have g := c.geo
  have hfo : 2 ^ mu m0 + level.fold ≤ 64 := c.fold
  have hal : w.alphas.size + mu m0 ≤ 30 := c.alphas
  have hf := hc.fr
  have hrl : rot.toList.length ≤ 30 := hrot.1
  have htl : tail.toList.length = mu m0 := by rw [Array.length_toList, htn]
  -- `b25`: `BasisW::eval(&out, basis, rotated)`.
  let env1 := argEnv m0 st.data 2672 8 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b26Offset)).toBitVec
  have hwf1 : env1.WF := c.wf0 hf.frame.kept
  refine exec_at (infix_of b25_in_code (by simp [b25]) hp) exit_b25 hwf1 (fun _ _ ↦ rfl) hpc
    (match_retS hf) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hW1, h48, hrdi1, hrsi1, hrdx1, hrcx1, -, hkr1⟩ := ok_b25
  have e1 : ∀ {r : Reg64} {v : Sym}, (after b25 retS).reg r = some v →
      reg st1.data r = v.eval env1 := fun h ↦ hm1.regs _ _ h
  obtain ⟨hf1, hs1⟩ := c.blk hf hwf1 hm1 hmid1 (hi := 56) (by omega) (hW1.le (by decide))
  have hk1 : KeepF m0 st.data.dmem st1.data.dmem 48 8 :=
    keepF_blk hwf1 hm1 (writesIn_of_mid hmid1) hW1 (by decide)
  have l144 : env1.load 0 144 8 = BitVec.ofNat 64 rot.toList.length := by
    have := load_ofMachine (r := 0) (o := 144) (rs := [(stackBelow m0 2672, 2672 + 8 + 8)])
      (vs := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b26Offset)).toBitVec) (m := st.data) rfl hrot.2.1
    rw [this]
    rfl
  have hdi1 : reg st1.data .rdi = loc m0 64 := (e1 hrdi1).trans (eval_ptr0A 64)
  have hsi1 : reg st1.data .rsi = bA m0 := (e1 hrsi1).trans (load_ofMachine (r := 0) (o := 56) rfl h56)
  have hdx1 : reg st1.data .rdx = loc m0 152 :=
    (e1 hrdx1).trans ((vBp_eval env1 l144 (by omega)).trans (by
      show fa m0 + BitVec.ofInt 64 152 = fa m0 + BitVec.ofNat 64 152; rfl))
  have hcx1 : reg st1.data .rcx = BitVec.ofNat 64 rot.toList.length :=
    (e1 hrcx1).trans (vBn_eval env1 l144 (by omega))
  have hcxn : (reg st1.data .rcx).toNat = rot.toList.length := by
    rw [hcx1, BitVec.toNat_ofNat]; omega
  have hw48 : NativeRustcVm.WordAt st1.data.dmem (loc m0 48)
      (.ofBitVec (BitVec.ofNat 64 (w.alphas ++ tail).size)) :=
    wordAt_written hm1 (r := 0) (o := 48) rfl (by omega) h48 h13
  have hrot1 : NativeRustcVm.EWsAt st1.data.dmem (loc m0 152) rot.toList := by
    have := hk1.ews (j := 152) (xs := rot.toList) (by omega) (by omega) (by omega)
      (by have := hrot.2.2; rwa [show loc m0 144 + 8#64 = loc m0 152 from off_add _ _ _] at this)
    exact this
  have hat := c.at_call (o := 32) (by omega) hf1
  have hle : 2672 - 32 + basisWEvalStack ≤ finalLevelStack := by decide
  have hpre : BasisWEvalPre ba b st1.data := by
    refine ⟨(c.sctx (by decide)).stackOk hat hle, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show BasisWAt st1.data.dmem (reg st1.data .rsi) ba b
      rw [hsi1]; exact c.basis_at hf1.same
    · show BasisIn st1.data (reg st1.data .rsi) ba basisWEvalStack (reg st1.data .rdi) 24
      rw [hsi1, hdi1]
      refine ⟨c.whirIn hat hle c.bp.1, c.apart_in c.bp.1 (by omega), fun r hr ↦
        ⟨c.whirIn hat hle (c.bp.2.2 r hr).1, c.apart_in (c.bp.2.2 r hr).1 (by omega)⟩⟩
    · rw [hcxn]; omega
    · show SliceOk st1.data (reg st1.data .rdx) (reg st1.data .rcx) basisWEvalStack
      rw [hdx1]
      exact c.sliceLoc (o := 32) (by omega) hf1 hle (by omega) (by rw [hcxn]; omega)
    · show WhirIn st1.data (reg st1.data .rdi) 24 basisWEvalStack
      rw [hdi1]; exact c.inLoc (o := 32) (by omega) hf1 hle (by omega) (by omega)
    · show BasisApart (reg st1.data .rsi) ba
      rw [hsi1]; exact c.bap
  refine call_then hpc1 (hbw ba b) hpre fun st2 hpc2 hrsp2 hq ↦ ?_
  obtain ⟨hopt, hch, hsv⟩ := hq
  rw [hdi1, hdx1, slice_eq hcxn hrot1] at hopt
  have hch' : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem (fun q ↦
      NativeRustcVm.InRange (loc m0 64) 24 q ∨
        NativeRustcVm.InRange (stackBelow st1.data basisWEvalStack) basisWEvalStack q) :=
    NativeRustcVm.SameOutside.mono hch fun q hq ↦ by
      rcases hq with hq | hq
      · left; rw [hdi1] at hq; exact one_iff.mp hq
      · exact Or.inr hq
  obtain ⟨hf2, hkeep2⟩ := c.call (o := 32) (by omega) hf1 hle hsv hrsp2
    (R := NativeRustcVm.InRange (loc m0 64) 24) (lo := 64) (n := 24) (by omega) (by omega)
    (fun q hq ↦ Or.inr hq) hch'
  have hk2 : KeepF m0 st1.data.dmem st2.data.dmem 64 24 := hkeep2
  have hts2 := c.ts_call (o := 32) (by omega) hf1 hle hsv
    (fun q hq ↦ c.loc_not_t (by omega) hq) hch'
    (c.ts_frame (hi := 56) (by omega) (hm1.kept hwf1) hs1 hts)
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b26Offset) := hpc2
  -- `b26`: the tag.
  refine Eventually.bind (cond_spec hp c b26_in_code (by simp [b26]) exit_b26 ok_b26 hf2 hpc2')
    fun st3 ⟨hr3, hd3, hpc3⟩ ↦ ?_
  obtain ⟨hopt1, hopt2⟩ := hopt
  have h1 := load4_of_tag (Or.inr rfl) (show NativeRustcVm.WordAt
    ((argEnv m0 st2.data 2672 8 [] (fun _ ↦ 0) 0).mem0)
    ((argEnv m0 st2.data 2672 8 [] (fun _ ↦ 0) 0).base 0 + BitVec.ofNat 64 64) 1 from hopt1)
  rw [cTag64_eval _ (Or.inr rfl) h1] at hpc3
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false] at hpc3
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b27Offset) := hpc3
  have hcs : ∀ r ∈ [Reg64.rbx, .r12, .r14, .r15], reg st3.data r = reg st.data r := fun r hr ↦
    (hr3 r).trans ((hsv.1 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> rfl)).trans
      (e1 (hkr1 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> simp))))
  refine cont st3 hpc3' ?_ ((hcs .rbx (by simp)).trans hbx) ((hcs .r12 (by simp)).trans h12)
    ((hcs .r15 (by simp)).trans h15) ?_ ?_ ?_ ?_ (by rw [hd3]; exact hts2)
  · exact hc.keep (hf2.congr hr3 hd3) (hcs .r14 (by simp)) (fun j hj ↦ by
      rw [hd3, hk2 j (by omega) (by omega) (by omega), hk1 j (by omega) (by omega) (by omega)]) hfo
  · rw [hd3]; exact hk2.word (by omega) (by omega) (by omega) hw48
  · rw [hd3]
    exact hk2.buf (by omega) (by omega) (by omega) (hk1.buf (by omega) (by omega) (by omega) hpt)
  · rw [hd3]
    have := hopt2
    rwa [show off (loc m0 64) 8 = loc m0 72 from off_off _ _ _] at this
  · rw [hd3]
    exact hk2.ews (by omega) (by omega) (by omega) (hk1.ews (by omega) (by omega) (by omega) htail)

end

end NativeRustcVmX64.Whir.Levels.FL
