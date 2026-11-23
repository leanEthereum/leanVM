module

public import NativeRustcVmX64.Sumcheck.Layer.Frame
public import NativeRustcVmX64.Code.Vm.SumcheckOfVerifyLayer.Names
public import NativeRustcVmX64.Code.Vm.TStateSumcheckRoundPoly.Names

/-!
# `sumcheck` with `verify_layer`'s closure: a round's polynomial (x86-64)

From the loop's head (`Inv`), `b2` tests `i < |pt|`: `b3` copies the point's coordinate `i` into
the frame's `eq` (`some`), `b5` leaves it `None` (`eq_spec`); `b6` writes the tag and calls
`sumcheck_round_poly`; `b7` leaves for `.L6` on a rejection (`exit_fail`), else at `b8` the
polynomial read (`Mid`, `b6_spec`, `head_spec`).
-/

namespace NativeRustcVmX64.Sumcheck.Layer

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SumcheckOfVerifyLayer
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Sumcheck

@[expose] public section

/-- At `b8`, round `i`'s polynomial `msg` read, the state `s1`, the first `i` challenges `xs`. -/
structure Mid [Labels] (a : DecArea) (s : TState) (pt : Array EW) (n : Nat) (m0 : MachineData)
    (i : Nat) (xs msg : Array EW) (s1 : TState) (m : MachineData) : Prop where
  fr : FrG m0 n 8 m
  lt : i < n
  w : Words m0 m.dmem
  r12 : reg m .r12 = tG m0
  r13 : reg m .r13 = BitVec.ofNat 64 (16 * i)
  r14 : reg m .r14 = BitVec.ofNat 64 i
  rbx : reg m .rbx = off (slG m0) (16 * n)
  rbp : reg m .rbp = off (fG m0) 64
  run : (sumcheckFn (claimArg m0) (cntG m0) (fun j ↦ pt[j]?) (i + 1)).run s =
    some ((xs.push s1.sponge.squeeze.1, polyEval msg s1.sponge.squeeze.1),
      { s1 with sponge := s1.sponge.squeeze.2 })
  xsz : xs.size = i
  xs : NativeRustcVm.EWsAt m.dmem (slG m0) xs.toList
  msz : msg.size = cntG m0
  msg : NativeRustcVm.EWsAt m.dmem (off (fG m0) 64) msg.toList
  ts : TStateAt m.dmem (tG m0) a s1

/-- What the loop ends in: the exit (a rejection), or `.L8` after the last round. -/
abbrev Goal [Host] (a : DecArea) (s : TState) (pt : Array EW) (n : Nat) (m0 : MachineData)
    (k : Nat) (st : MachineState) : Prop :=
  (st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ LPost a s pt n m0 st.data) ∨
    (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b11Offset) ∧ Done a s pt n m0 st.data)

end

public section

/-- The frame's words kept where the frame's bytes from `16` to `40` are. -/
theorem Words.keep {m0 : MachineData} {d d' : Mem 64}
    (h : ∀ (o : Nat) (bs : List UInt8), 16 ≤ o → o + bs.length ≤ 40 →
      NativeRustcVm.BytesAt d (off (fG m0) o) bs → NativeRustcVm.BytesAt d' (off (fG m0) o) bs)
    (hw : Words m0 d) : Words m0 d' :=
  ⟨h 16 _ le_rfl (by rw [NativeRustcVm.length_wordBytes]; omega) hw.out,
    h 24 _ (by omega) (by rw [NativeRustcVm.length_wordBytes]; omega) hw.p,
    h 32 _ (by omega) (by rw [NativeRustcVm.length_wordBytes]) hw.sz⟩

section
variable [Labels] {m0 d d' : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64}
  {S : SState}

/-- The frame's words kept by a block whose frame writes miss them. -/
theorem Words.block (hwf : (frameEnv m0 d 192 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (frameEnv m0 d 192 rest (fun _ ↦ 0) ret) S d') (hin : writesIn S = true)
    (hS : ∀ w ∈ S.mem, w.r = 0 → w.off + w.n ≤ 16 ∨ 40 ≤ w.off) (hw : Words m0 d.dmem) :
    Words m0 d'.dmem :=
  Words.keep (fun o bs ho hob hb ↦ keep_frame hwf hm hin (by omega) (fun w hw hr ↦
    (hS w hw hr).imp (fun h ↦ by omega) (fun h ↦ by omega)) hb) hw

end

variable [Host] {a : DecArea} {s : TState} {pt : Array EW} {n : Nat} {m0 : MachineData} {k : Nat}

/-- **`b6`, `b7`**: the tag of `eq`, `sumcheck_round_poly`; a rejection's exit or `b8` with the
polynomial. -/
theorem b6_spec (hp : Placed code k)
    (hrp : ∀ a s e, Spec (Labels.label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.entryLabel) (RoundPolyPre a s e) (RoundPolyPost a s e))
    (hpre : LPre a s pt n m0) {i : Nat} {m : MachineData} (hi : Inv a s pt n m0 i m)
    (hrdx : reg m .rdx = if i < pt.size then 1 else 0)
    (hv : ∀ h : i < pt.size, NativeRustcVm.EWAt m.dmem (off (fG m0) 48) pt[i]) :
    Eventually (step1 Host.exe)
      (fun st ↦ Goal a s pt n m0 k st ∨
        (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b8Offset) ∧ ∃ xs msg s1, Mid a s pt n m0 i xs msg s1 st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b6Offset)⟩ := by
  have g := geo hpre
  obtain ⟨xs, si, hrun, hsz, hxs, hts⟩ := hi.run
  have hlt := hi.lt
  have hl6 : Labels.label NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.label_6 = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b12Offset) :=
    hp.label NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.label_6_at
  have hwf := wf_envB hpre hi.fr (Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b6Offset + b6.length)).toBitVec
  refine exec_then (infix_of b6_in_code (by simp [b6]) hp) exit_b6 hwf (fun _ _ ↦ rfl)
    (match_bodyS hi.fr _) fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hw2, hW40, hrdi2, hrsi2, hrdx2, hrcx2, hr8_2, hr9_2, hk2⟩ := ok_b6
  have hin2 := writesIn_of_mid hmid2
  have hs2 : NativeRustcVm.SameOutside m.dmem st2.data.dmem (NativeRustcVm.InRange (fG m0) 192) :=
    sameOutside_low hwf hm2 (r := 0) rfl (hi := 192) (by omega) fun w hw ↦
      ⟨(hw2 w hw).1, by rcases (hw2 w hw).2 with h | h <;> omega⟩
  have hf2 : FrG m0 n 0 st2.data :=
    g.block hi.fr hwf hm2 hmid2 hs2 fun q hq ↦ Or.inl (g.ctx.inRange_frame hq)
  have hmiss : ∀ w ∈ (after b6 bodyS).mem, w.r = 0 → w.off + w.n ≤ 16 ∨ 40 ≤ w.off :=
    fun w hw _ ↦ by rcases (hw2 w hw).2 with h | h <;> omega
  have w2 := Words.block hwf hm2 hin2 hmiss hi.w
  have ts2 : TStateAt st2.data.dmem (tG m0) a si :=
    g.t_keep hs2 (hm2.kept hwf) (fun q hq ↦ Or.inl (g.ctx.inRange_frame hq)) hts
  have xs2 : NativeRustcVm.EWsAt st2.data.dmem (slG m0) xs.toList :=
    g.sl_keep hs2 (fun q hq ↦ g.not_sl_stack (g.ctx.inRange_frame hq)) (by simp [hsz]; omega) hxs
  have he2 : OptEWAt st2.data.dmem (off (fG m0) 40) pt[i]? := by
    have wt := wordAt_written hm2 (r := 0) (o := 40) rfl (by omega) hW40
      (w := if i < pt.size then 1 else 0) (by
        show reg m .rdx = _
        rw [hrdx]; split <;> rfl)
    by_cases hp' : i < pt.size
    · rw [Array.getElem?_eq_getElem hp']
      simp only [hp', ite_true] at wt
      refine ⟨wt, ?_⟩
      rw [off_off]
      exact keep_frame hwf hm2 hin2 (o := 48) (bs := NativeRustcVm.ewBytes pt[i])
        (by rw [NativeRustcVm.length_ewBytes]; omega) (fun w hw _ ↦ by
          rw [NativeRustcVm.length_ewBytes]; rcases (hw2 w hw).2 with h | h <;> omega) (hv hp')
    · rw [Array.getElem?_eq_none (by omega)]
      simp only [hp', ite_false] at wt
      exact wt
  have hrdi : reg st2.data .rdi = tG m0 := (hm2.regs .rdi _ hrdi2).trans hi.r12
  have hrsi : (reg st2.data .rsi).toNat = cntG m0 := by
    rw [show reg st2.data .rsi = _ from hm2.regs .rsi _ hrsi2]; rfl
  have hr8 : reg st2.data .r8 = off (fG m0) 40 := (hm2.regs .r8 _ hr8_2).trans (eval_ptr0 40)
  have hr9 : reg st2.data .r9 = off (fG m0) 64 := (hm2.regs .r9 _ hr9_2).trans hi.rbp
  have hrbp : reg st2.data .rbp = off (fG m0) 64 :=
    (hm2.regs .rbp _ (Keeps.reg hk2 (by simp))).trans hi.rbp
  have hr12 : reg st2.data .r12 = tG m0 :=
    (hm2.regs .r12 _ (Keeps.reg hk2 (by simp))).trans hi.r12
  have hclaim : (⟨.ofBitVec (reg st2.data .rdx), .ofBitVec (reg st2.data .rcx)⟩ : EW) =
      claimR m := by
    rw [show reg st2.data .rdx = _ from hm2.regs .rdx _ hrdx2,
      show reg st2.data .rcx = _ from hm2.regs .rcx _ hrcx2]
    rfl
  have hreg2 : ∀ r ∈ [Reg64.rbx, .r13, .r14], reg st2.data r = reg m r :=
    fun r hr ↦ hm2.regs r _ (Keeps.reg hk2 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl <;> simp))
  refine call_then hpc2 (hrp a si pt[i]?)
    (g.roundPolyPre hf2 (Mo := 64) (Eo := 40) (by omega) (by omega) (by omega) (by omega) ts2 he2
      hrdi hrsi hr8 hr9) fun st3 hpc3 hrsp3 hpost3 ↦ ?_
  have hok3 := hpost3.1
  have hsv3 := hpost3.2.2.2.2
  obtain ⟨hf3, hmsg3, hsl3, hloc3⟩ := g.afterRoundPoly hf2 (Mo := 64) (by omega) hpost3 hrsp3 hrdi hr9
  rw [hrsi, hclaim] at hok3 hmsg3
  have w3 := Words.keep (fun o bs ho hob hb ↦ hloc3 o bs (by omega) (by omega) (Or.inl (by omega)) hb)
    w2
  have hreg3 : ∀ r ∈ [Reg64.rbx, .r13, .r14], reg st3.data r = reg m r :=
    fun r hr ↦ (hsv3.1 r (by simp at hr; rcases hr with rfl | rfl | rfl <;> rfl)).trans
      (hreg2 r hr)
  have hrbp3 : reg st3.data .rbp = off (fG m0) 64 := (hsv3.1 .rbp rfl).trans hrbp
  have hr12_3 : reg st3.data .r12 = tG m0 := (hsv3.1 .r12 rfl).trans hr12
  -- `b7`: the polynomial's test.
  have hwf3 := wf_envB hpre hf3 0
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) exit_b7 hwf3 nofun
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b6_next)) (match_bodyS hf3 _) fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid4, hmem4, hk4⟩ := ok_b7
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 hmem4
  have hf4 : FrG m0 n 8 st4.data := g.block hf3 hwf3 hm4 hmid4 (R := fun _ ↦ False)
    (fun q _ ↦ by rw [hd4]) fun _ h ↦ h.elim
  have hreg4 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14], reg st4.data r = reg st3.data r :=
    fun r hr ↦ hm4.regs r _ (Keeps.reg hk4 hr)
  have hc : cAl.eval (envB m0 st3.data 0) = decide ((reg st3.data .rax).toNat % 256 = 0) :=
    testAl_eq _
  simp only [PcOk, hc] at hpc4
  cases hr : (sumcheckRoundPoly (cntG m0) (claimR m) pt[i]?).run si with
  | none =>
    rw [hr] at hok3
    have hal : (reg st3.data .rax).toNat % 256 = 0 := hok3
    have hpc : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b12Offset) := by
      rw [hpc4, hal]; simp [hl6]
    have hnone := sumcheckFn_run_none_le (sumcheckFn_run_succ_none hrun hr)
      (show i + 1 ≤ n by omega)
    obtain ⟨d4, pc4⟩ := st4
    simp only at hpc
    subst hpc
    exact Eventually.mono (exit_fail hp hpre hf4 (by rw [hd4]; exact w3.out) hnone)
      fun st h ↦ .inl (.inl h)
  | some p =>
    obtain ⟨msg, s1⟩ := p
    rw [hr] at hok3
    have hal : (reg st3.data .rax).toNat % 256 = 1 := hok3
    have hpc : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b8Offset) := by
      rw [hpc4, hal]; rfl
    obtain ⟨hmsg, hts3⟩ := hmsg3 msg s1 hr
    refine Eventually.done _ (.inr ⟨hpc, xs, msg, s1, hf4, hlt, by rw [hd4]; exact w3,
      (hreg4 .r12 (by simp)).trans hr12_3, ?_, ?_, ?_, (hreg4 .rbp (by simp)).trans hrbp3,
      sumcheckFn_run_succ_some hrun hr, hsz, ?_, roundPoly_size g.cnt2 hr, ?_, ?_⟩)
    · rw [hreg4 .r13 (by simp), hreg3 .r13 (by simp)]; exact hi.r13
    · rw [hreg4 .r14 (by simp), hreg3 .r14 (by simp)]; exact hi.r14
    · rw [hreg4 .rbx (by simp), hreg3 .rbx (by simp)]; exact hi.rbx
    · rw [hd4]; exact hsl3 xs.toList (by simp [hsz]; omega) xs2
    · rw [hd4]; exact hmsg
    · rw [hd4]; exact hts3

/-- **`b2`, then `b3` or `b5`**: `eq`, the point's coordinate `i` if there is one, in the frame
at `40`'s payload, its tag in RDX; at `b6` with the invariant. -/
theorem eq_spec (hp : Placed code k) (hpre : LPre a s pt n m0) {i : Nat}
    {m : MachineData} (hi : Inv a s pt n m0 i m) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b6Offset) ∧ Inv a s pt n m0 i st.data ∧
        reg st.data .rdx = (if i < pt.size then 1 else 0) ∧
        ∀ h : i < pt.size, NativeRustcVm.EWAt st.data.dmem (off (fG m0) 48) pt[i])
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b2Offset)⟩ := by
  have g := geo hpre
  have hlt := hi.lt
  have hwf := wf_envB hpre hi.fr 0
  refine exec_then (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf nofun
    (match_bodyS hi.fr _) fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hmem2, hk2⟩ := ok_b2
  have hd2 : st2.data.dmem = m.dmem := hm2.dmem_eq hwf hmem2
  have hf2 : FrG m0 n 8 st2.data := g.block hi.fr hwf hm2 hmid2 (R := fun _ ↦ False)
    (fun q _ ↦ by rw [hd2]) fun _ h ↦ h.elim
  have hreg2 : ∀ r ∈ [Reg64.rax, .rcx, .rbx, .rbp, .r12, .r13, .r14], reg st2.data r = reg m r :=
    fun r hr ↦ hm2.regs r _ (Keeps.reg hk2 hr)
  have hi2 : Inv a s pt n m0 i st2.data := by
    refine ⟨hf2, hlt, by rw [hd2]; exact hi.w, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hreg2 .r12 (by simp)]; exact hi.r12
    · rw [hreg2 .rbp (by simp)]; exact hi.rbp
    · rw [hreg2 .r13 (by simp)]; exact hi.r13
    · rw [hreg2 .r14 (by simp)]; exact hi.r14
    · rw [hreg2 .rbx (by simp)]; exact hi.rbx
    · show RoundsG a s pt m0 st2.data.dmem i ⟨_, _⟩
      rw [hd2, hreg2 .rax (by simp), hreg2 .rcx (by simp)]; exact hi.run
  have hn64 : n < 2 ^ 64 := by rw [← hpre.2]; exact (stackArg m0 1).isLt
  have hsz : pt.size = (reg m0 .r9).toNat := hpre.1.2.2.1
  have hc : c2.eval (envB m0 m 0) = !decide (i < pt.size) := by
    have hl : (envB m0 m 0).load 0 32 8 = reg m0 .r9 :=
      load_ofMachine (r := 0) (o := 32) rfl hi.w.sz
    simp only [c2, SBool.eval, Sym.eval, CmpOp.apply, low_W64, hl, Env.ofMachine_regs]
    show (!(reg m .r14).ult (reg m0 .r9)) = _
    rw [hi.r14, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hsz]
  simp only [PcOk, hc] at hpc2
  by_cases hp' : i < pt.size
  · simp only [hp', decide_true, Bool.not_true, Bool.false_eq_true, ite_false] at hpc2
    -- `b3`: the coordinate into the frame.
    have hpt := pt_keep hpre hf2
    have hel := NativeRustcVm.EWsAt.getElem hpt (i := i) (by simpa using hp')
    have hnw : NativeRustcVm.NoWrap (ptG m0) (16 * pt.size) := hpre.1.2.2.2.2.1
    unfold NativeRustcVm.NoWrap at hnw
    have hx : (ptG m0 + BitVec.ofNat 64 (16 * i)) = off (ptG m0) (16 * i) := rfl
    rw [hx] at hel
    have hA : NativeRustcVm.Apart (off (ptG m0) (16 * i)) 16
        (stackBelow m0 sumcheckLayerStack) (sumcheckLayerStack + 8) := by
      have : (ptG m0).toNat + 16 * pt.size ≤ (stackBelow m0 sumcheckLayerStack).toNat ∨
          (stackBelow m0 sumcheckLayerStack).toNat + (sumcheckLayerStack + 8) ≤ (ptG m0).toNat :=
        hpre.1.2.2.2.2.2.1
      unfold NativeRustcVm.Apart
      rw [toNat_off (by omega)]
      omega
    have hwf3 := wf_envX hpre hf2 (x := off (ptG m0) (16 * i)) (l := 16) hel.mapped
      (by unfold NativeRustcVm.NoWrap; rw [toNat_off (by omega)]; omega) hA 0
    have hal : (Sym.bin .add .W64 (.load 0 24 8) (.reg .r13)).eval (envX m0 st2.data
        (off (ptG m0) (16 * i)) 16 0) =
        (envX m0 st2.data (off (ptG m0) (16 * i)) 16 0).base 1 + BitVec.ofInt 64 0 := by
      rw [ofInt_zero64, BitVec.add_zero]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [load_ofMachine (o := 24) rfl (by rw [hd2]; exact hi.w.p), toBitVec_ofBitVec]
      show ptG m0 + reg st2.data .r13 = _
      rw [hreg2 .r13 (by simp), hi.r13]
      rfl
    have hm3 : Match (envX m0 st2.data (off (ptG m0) (16 * i)) 16 0) ptS st2.data :=
      match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf2.frame.rsp_eval, trivial⟩ trivial trivial
        ⟨hal, trivial⟩
    refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf3 nofun
      (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b2_next)) hm3 fun st3 hm3' hpc3 ↦ ?_
    obtain ⟨hmid3, hw3, hW48, hW56, hrdx3, hk3⟩ := ok_b3
    have hin3 := writesIn_of_mid hmid3
    have hs3 : NativeRustcVm.SameOutside st2.data.dmem st3.data.dmem
        (NativeRustcVm.InRange (fG m0) 192) :=
      sameOutside_low hwf3 hm3' (r := 0) rfl (hi := 192) (by omega) fun w hw ↦
        ⟨(hw3 w hw).1, by have := (hw3 w hw).2.2; omega⟩
    have hf3 : FrG m0 n 8 st3.data :=
      g.block hf2 hwf3 hm3' hmid3 hs3 fun q hq ↦ Or.inl (g.ctx.inRange_frame hq)
    have hreg3 : ∀ r ∈ [Reg64.rax, .rcx, .rbx, .rbp, .r12, .r13, .r14],
        reg st3.data r = reg st2.data r :=
      fun r hr ↦ hm3'.regs r _ (Keeps.reg hk3 hr)
    have hel' := ewAt_iff.mp hel
    simp only [PcOk] at hpc3
    refine .done _ ⟨hpc3.trans (hp.label NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.label_5_at), ⟨hf3, hlt,
      Words.block hwf3 hm3' hin3 (fun w hw _ ↦ Or.inr (hw3 w hw).2.1 |>.imp id (by omega)) hi2.w,
      ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun _ ↦ ?_⟩
    · rw [hreg3 .r12 (by simp)]; exact hi2.r12
    · rw [hreg3 .rbp (by simp)]; exact hi2.rbp
    · rw [hreg3 .r13 (by simp)]; exact hi2.r13
    · rw [hreg3 .r14 (by simp)]; exact hi2.r14
    · rw [hreg3 .rbx (by simp)]; exact hi2.rbx
    · show RoundsG a s pt m0 st3.data.dmem i ⟨_, _⟩
      rw [hreg3 .rax (by simp), hreg3 .rcx (by simp)]
      exact g.rounds_keep hs3 (hm3'.kept hwf3) (fun q hq ↦ g.ctx.inRange_frame hq) hlt.le hi2.run
    · rw [show reg st3.data .rdx = _ from hm3'.regs .rdx _ hrdx3]; simp only [hp', ite_true]; rfl
    · refine ewAt_iff.mpr ⟨?_, ?_⟩
      · exact wordAt_written hm3' (r := 0) (o := 48) rfl (by omega) hW48
          (load_ofMachine (r := 1) (o := 0) rfl (by rw [off_zero]; exact hel'.1))
      · rw [off_off]
        exact wordAt_written hm3' (r := 0) (o := 56) rfl (by omega) hW56
          (load_ofMachine (r := 1) (o := 8) rfl hel'.2)
  · simp only [hp', decide_false, Bool.not_false, ite_true] at hpc2
    rw [hp.label NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.label_3_at] at hpc2
    -- `b5`: `None`.
    have hwf5 := wf_envB hpre hf2 0
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) exit_b5 hwf5 nofun hpc2
      (match_bodyS hf2 _) fun st3 hm3 hpc3 ↦ ?_
    obtain ⟨hmid3, hmem3, hrdx3, hk3⟩ := ok_b5
    have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf5 hmem3
    have hf3 : FrG m0 n 8 st3.data := g.block hf2 hwf5 hm3 hmid3 (R := fun _ ↦ False)
      (fun q _ ↦ by rw [hd3]) fun _ h ↦ h.elim
    have hreg3 : ∀ r ∈ [Reg64.rax, .rcx, .rbx, .rbp, .r12, .r13, .r14],
        reg st3.data r = reg st2.data r :=
      fun r hr ↦ hm3.regs r _ (Keeps.reg hk3 hr)
    simp only [PcOk] at hpc3
    refine .done _ ⟨hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b5_next),
      ⟨hf3, hlt, by rw [hd3]; exact hi2.w, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun h ↦ absurd h hp'⟩
    · rw [hreg3 .r12 (by simp)]; exact hi2.r12
    · rw [hreg3 .rbp (by simp)]; exact hi2.rbp
    · rw [hreg3 .r13 (by simp)]; exact hi2.r13
    · rw [hreg3 .r14 (by simp)]; exact hi2.r14
    · rw [hreg3 .rbx (by simp)]; exact hi2.rbx
    · show RoundsG a s pt m0 st3.data.dmem i ⟨_, _⟩
      rw [hd3, hreg3 .rax (by simp), hreg3 .rcx (by simp)]; exact hi2.run
    · rw [show reg st3.data .rdx = _ from hm3.regs .rdx _ hrdx3]; simp only [hp', ite_false]; rfl

/-- **A round's polynomial**: from the head, a rejection's exit or `b8` with the polynomial. -/
theorem head_spec (hp : Placed code k)
    (hrp : ∀ a s e, Spec (Labels.label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.entryLabel) (RoundPolyPre a s e) (RoundPolyPost a s e))
    (hpre : LPre a s pt n m0) {i : Nat} {m : MachineData} (hi : Inv a s pt n m0 i m) :
    Eventually (step1 Host.exe)
      (fun st ↦ Goal a s pt n m0 k st ∨
        (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b8Offset) ∧ ∃ xs msg s1, Mid a s pt n m0 i xs msg s1 st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b2Offset)⟩ := by
  refine Eventually.bind (eq_spec hp hpre hi) fun st ⟨hpc, hi', hrdx, hv⟩ ↦ ?_
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc
  exact b6_spec hp hrp hpre hi' hrdx hv

end

end NativeRustcVmX64.Sumcheck.Layer
