module

public import NativeRustcVmX64.Whir.FinalLevel.Ext
public import NativeRustcVmX64.Code.Vm.BufEW30Extend.Names

/-!
# `final_level`: the point and the rotated point (x86-64)

From `b17` (`Core`, RBX the state `w`, the tail at `1120`, the claim at `152`): the claim kept in
R12, R15; the point (`Buf<EW, 30>` at `632`) set to the `α`s (`b17`, `extend`, `b18`) and extended
by the tail (`b19`, `extend`, `b20`); the rotated point (`Buf<EW, 30>` at `144`) set to the point
from `laneFolds` (`b21`, `extend`, `b22`) and extended by the point before it (`b23`, `extend`,
`b24`): `point`, to `b25`.
-/

namespace NativeRustcVmX64.Whir.Levels.FL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.FinalLevel

public section

theorem Core.keepF {level : Whir.Level} {m0 d d' : MachineData} {folded : Array EW}
    (h : Core level m0 d folded) (hf : Fr m0 40 d') (hr : reg d' .r14 = reg d .r14) {lo n : Nat}
    (hk : KeepF m0 d.dmem d'.dmem lo n) (hdis : (48 ≤ lo ∧ lo + n ≤ 1600) ∨ 2624 ≤ lo)
    (h64 : 2 ^ mu m0 + level.fold ≤ 64) : Core level m0 d' folded :=
  h.keep hf hr (fun j hj ↦ hk j (by omega) (by omega) (by omega)) h64

/-- A block's writes as a `KeepF`. -/
theorem keepF_blk [Labels] {m0 d d' : MachineData} {rest : List (BitVec 64 × Nat)} {S : SState}
    {ret : BitVec 64} (hwf : (argEnv m0 d 2672 8 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (argEnv m0 d 2672 8 rest (fun _ ↦ 0) ret) S d')
    (hin : writesIn S = true) {rs : List (Nat × Nat)} (hW : Wr rs S) {lo n : Nat}
    (hrs : ∀ p ∈ rs, p.2 ≤ 40 ∨ (lo ≤ p.1 ∧ p.2 ≤ lo + n)) : KeepF m0 d.dmem d'.dmem lo n :=
  fun j h1 h2 h3 ↦ get_blk hwf hm hin hW h2 fun p hp ↦ by rcases hrs p hp with h | h <;> omega

theorem KeepF.trans {m0 : MachineData} {d d' d'' : Mem 64} {lo n lo' n' : Nat}
    (h : KeepF m0 d d' lo n) (h' : KeepF m0 d' d'' lo' n') {j : Nat} (hj : 40 ≤ j)
    (hjn : j < 2688) (h1 : j < lo ∨ lo + n ≤ j) (h2 : j < lo' ∨ lo' + n' ≤ j) :
    d''.get? (loc m0 j) = d.get? (loc m0 j) :=
  (h' j hj hjn h2).trans (h j hj hjn h1)

theorem extract_drop (xs : Array EW) (v : Nat) :
    xs.extract v xs.size = (xs.toList.drop v).toArray :=
  Array.ext' (by simp)

theorem extract_take (xs : Array EW) (v : Nat) : xs.extract 0 v = (xs.toList.take v).toArray :=
  Array.ext' (by simp)

section
variable [Labels] (env : Env)

theorem vAn_eval {n : Nat} (h : env.load 1 16 8 = BitVec.ofNat 64 n) (hn : n < 31) :
    vAn.eval env = BitVec.ofNat 64 n := by
  simp only [vAn, Sym.eval, SBool.eval, CmpOp.apply, low_W64, h, ult_ofNat hn (by decide),
    ite_true]

theorem vAp_eval {n : Nat} (h : env.load 1 16 8 = BitVec.ofNat 64 n) (hn : n < 31) :
    vAp.eval env = env.base 1 + BitVec.ofInt 64 24 := by
  simp only [vAp, Sym.eval, SBool.eval, CmpOp.apply, low_W64, h, ult_ofNat hn (by decide),
    ite_true]

theorem vLen_eval {n : Nat} (h : env.load 0 632 8 = BitVec.ofNat 64 n) (hn : n < 31) :
    vLen.eval env = BitVec.ofNat 64 n := by
  simp only [vLen, Sym.eval, SBool.eval, CmpOp.apply, low_W64, h, ult_ofNat hn (by decide),
    Bool.not_true, Bool.false_eq_true, ite_false]

theorem vPt_eval {n : Nat} (h : env.load 0 632 8 = BitVec.ofNat 64 n) (hn : n < 31) :
    vPt.eval env = env.base 0 + BitVec.ofInt 64 640 := by
  simp only [vPt, Sym.eval, SBool.eval, CmpOp.apply, low_W64, h, ult_ofNat hn (by decide),
    Bool.not_true, Bool.false_eq_true, ite_false]

theorem vRd_toNat {n : Nat} (h : env.load 0 632 8 = BitVec.ofNat 64 n) (hn : n < 31)
    {x : BitVec 64} (h48 : env.load 0 48 8 = x) : (vRd.eval env).toNat = n - x.toNat := by
  have hl := vLen_eval env h hn
  have hn' : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  simp only [vRd, Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, hl, h48]
  split <;> rename_i hc <;> simp only [BitVec.ult, decide_eq_true_eq, hn'] at hc
  · simp; omega
  · rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hn']; omega), hn']

omit [Labels] in
theorem shl4 (x : BitVec 64) :
    BinOp.apply .shl .W64 x (BitVec.ofNat 64 4) = BitVec.ofNat 64 (16 * x.toNat) := by
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [show shiftCount .W64 (BitVec.ofNat 64 4) = 4 from rfl]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    show (2 : Nat) ^ 4 = 16 from rfl, Nat.mul_comm]

theorem vRs_eval {n : Nat} (h : env.load 0 632 8 = BitVec.ofNat 64 n) (hn : n < 31)
    {x : BitVec 64} (h48 : env.load 0 48 8 = x) :
    vRs.eval env = if n < x.toNat then BitVec.ofNat 64 8
      else env.base 0 + BitVec.ofInt 64 640 + BitVec.ofNat 64 (16 * x.toNat) := by
  have hl := vLen_eval env h hn
  have hp := vPt_eval env h hn
  have hn' : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  simp only [vRs, Sym.eval, SBool.eval, CmpOp.apply, low_W64, hl, hp, h48]
  by_cases hc : n < x.toNat
  · have : (BitVec.ofNat 64 n).ult x = true := by simp only [BitVec.ult, hn']; exact decide_eq_true hc
    simp only [this, ite_true, hc]
  · have : (BitVec.ofNat 64 n).ult x = false := by
      simp only [BitVec.ult, hn']; exact decide_eq_false hc
    simp only [this, Bool.false_eq_true, ite_false, hc]
    show BinOp.apply .add .W64 _ (BinOp.apply .shl .W64 x (BitVec.ofNat 64 4)) = _
    rw [shl4 x]
    simp only [BinOp.apply, low_W64, ext_W64]

theorem vMin_toNat {n : Nat} (h13 : env.regs .r13 = BitVec.ofNat 64 n) (hn : n < 31)
    {x : BitVec 64} (h48 : env.load 0 48 8 = x) : (vMin.eval env).toNat = min n x.toNat := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  simp only [vMin, Sym.eval, SBool.eval, CmpOp.apply, low_W64, h13, h48]
  split <;> rename_i hc <;> simp only [BitVec.ult, decide_eq_true_eq, hn'] at hc <;> omega

end

theorem Ctx.apart_ll [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {ba : BasisAddrs}
    {b : BasisW} {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData}
    (c : Ctx a s level ba b w rounds m0) {o n o' n' : Nat} (ho : o < 2688) (ho' : o' < 2688)
    (hd : o + n ≤ o' ∨ o' + n' ≤ o) : NativeRustcVm.Apart (loc m0 o) n (loc m0 o') n' := by
  unfold NativeRustcVm.Apart
  rw [c.loc_toNat ho, c.loc_toNat ho']
  omega

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The point and the rotated point**: `b17` to `b24`, to `b25`. -/
theorem point (hp : Placed code k) (c : Ctx a s level ba b w rounds m0)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    {st : MachineState} {folded tail : Array EW} {claim : EW} {s5 : TState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b17Offset)) (hc : Core level m0 st.data folded)
    (hbx : reg st.data .rbx = pA m0)
    (h48 : NativeRustcVm.WordAt st.data.dmem (loc m0 48) (.ofBitVec (reg m0 .r8)))
    (h56 : NativeRustcVm.WordAt st.data.dmem (loc m0 56) (.ofBitVec (reg m0 .r9)))
    (htn : tail.size = mu m0) (htail : NativeRustcVm.EWsAt st.data.dmem (loc m0 1120) tail.toList)
    (hcl : NativeRustcVm.EWAt st.data.dmem (loc m0 152) claim)
    (hts : TStateAt st.data.dmem (tA m0) a s5)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b25Offset) → Core level m0 st'.data folded →
      reg st'.data .rbx = loc m0 640 → reg st'.data .r12 = claim.c0.toBitVec →
      reg st'.data .r15 = claim.c1.toBitVec →
      reg st'.data .r13 = BitVec.ofNat 64 (w.alphas ++ tail).size →
      NativeRustcVm.WordAt st'.data.dmem (loc m0 56) (.ofBitVec (reg m0 .r9)) →
      NativeRustcVm.BufEWAt st'.data.dmem (loc m0 632) 30 (w.alphas ++ tail).toList →
      NativeRustcVm.BufEWAt st'.data.dmem (loc m0 144) 30
        ((w.alphas ++ tail).extract (reg m0 .r8).toNat (w.alphas ++ tail).size ++
          (w.alphas ++ tail).extract 0 (reg m0 .r8).toNat).toList →
      NativeRustcVm.EWsAt st'.data.dmem (loc m0 1120) tail.toList →
      TStateAt st'.data.dmem (tA m0) a s5 → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have g := c.geo
  have hfo : 2 ^ mu m0 + level.fold ≤ 64 := c.fold
  have hal : w.alphas.size + mu m0 ≤ 30 := c.alphas
  have hf := hc.fr
  set P := w.alphas ++ tail with hP
  have hPs : P.size = w.alphas.size + mu m0 := by rw [hP, Array.size_append, htn]
  have hPl : P.toList.length = P.size := Array.length_toList
  have htl : tail.toList.length = mu m0 := by rw [Array.length_toList, htn]
  have hal' : w.alphas.toList.length = w.alphas.size := Array.length_toList
  -- `b17`: the claim kept, the point zeroed, `extend(&point, alphas)`.
  let ret1 := (Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b18Offset)).toBitVec
  let env1 := argEnv m0 st.data 2672 8 [(pA m0, 63200)] (fun _ ↦ 0) ret1
  have hwf1 : env1.WF :=
    c.wf1 hf.frame.kept (show NativeRustcVm.Mapped st.data.dmem (pA m0) 63200 from
      Mapped.keeps c.pout.1.1 hf.frame.kept) g.pW
      (g.pS.imp_left fun h ↦ Nat.le_trans h (Nat.sub_le_sub_left (by decide) _))
  have hm1 : Match env1 bxS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨Frame.rsp_evalA hf.frame, known_ptr rfl hbx, trivial⟩
      trivial trivial trivial
  refine exec_at (infix_of b17_in_code (by simp [b17]) hp) exit_b17 hwf1 (fun _ _ ↦ rfl) hpc hm1
    fun st1 hm1' hpc1 ↦ ?_
  obtain ⟨hmid1, hW1, h632, hrdi1, hrsi1, hrdx1, hr121, hr151, -, hkr1⟩ := ok_b17
  have e1 : ∀ {r : Reg64} {v : Sym}, (after b17 bxS).reg r = some v →
      reg st1.data r = v.eval env1 := fun h ↦ hm1'.regs _ _ h
  obtain ⟨hf1, -⟩ := c.blk hf hwf1 hm1' hmid1 (hi := 1120) (by omega) (hW1.le (by decide))
  have hk1 : KeepF m0 st.data.dmem st1.data.dmem 632 488 :=
    keepF_blk hwf1 hm1' (writesIn_of_mid hmid1) hW1 (by decide)
  have hsa := (c.whir_at hf.same).1.alphas
  have hal30 : w.alphas.size ≤ 30 := by have := hsa.1; rwa [Array.length_toList] at this
  have l16 : env1.load 1 16 8 = BitVec.ofNat 64 w.alphas.size := by
    have := load_ofMachine (r := 1) (o := 16) (rs := [(stackBelow m0 2672, 2672 + 8 + 8),
      (pA m0, 63200)]) (vs := fun _ ↦ 0) (ret := ret1) (m := st.data) rfl hsa.2.1
    rw [this, Array.length_toList]
    rfl
  obtain ⟨hc0, hc1⟩ := ewAt_iff'.mp hcl
  rw [show off (loc m0 152) 8 = loc m0 160 from off_off _ _ _] at hc1
  have h12 : reg st1.data .r12 = claim.c0.toBitVec :=
    (e1 hr121).trans (load_ofMachine (r := 0) (o := 152) rfl hc0)
  have h15 : reg st1.data .r15 = claim.c1.toBitVec :=
    (e1 hr151).trans (load_ofMachine (r := 0) (o := 160) rfl hc1)
  have hdi1 : reg st1.data .rdi = loc m0 632 := (e1 hrdi1).trans (eval_ptr0A 632)
  have hsi1 : reg st1.data .rsi = pA m0 + BitVec.ofNat 64 24 :=
    (e1 hrsi1).trans (vAp_eval env1 l16 (by omega))
  have hdx1 : (reg st1.data .rdx).toNat = w.alphas.toList.length := by
    rw [e1 hrdx1, vAn_eval env1 l16 (by omega), BitVec.toNat_ofNat, Array.length_toList]; omega
  have hbuf1 : NativeRustcVm.BufEWAt st1.data.dmem (loc m0 632) 30 [] :=
    ⟨by simp, wordAt_written hm1' (r := 0) (o := 632) rfl (by omega) h632 (w := 0) rfl,
      NativeRustcVm.ewsAt_nil _ _⟩
  have e24 : off (pA m0) alphasOff + 8#64 = pA m0 + BitVec.ofNat 64 24 := by
    show pA m0 + BitVec.ofNat 64 16 + 8#64 = _
    rw [BitVec.add_assoc]
    rfl
  have hys1 : NativeRustcVm.EWsAt st1.data.dmem (pA m0 + BitVec.ofNat 64 24) w.alphas.toList := by
    rw [← e24]; exact (c.whir_at hf1.same).1.alphas.2.2
  have hat1 := c.at_call (o := 32) (by omega) hf1
  have hle1 : 2672 - 32 + bufEWExtendStack ≤ finalLevelStack := by decide
  have hts1 := c.ts_frame (hi := 1120) (by omega) (hm1'.kept hwf1)
    (c.blk hf hwf1 hm1' hmid1 (hi := 1120) (by omega) (hW1.le (by decide))).2 hts
  refine ext_call hp c hext (jt := 255) (xs := []) (ys := w.alphas.toList) hpc1.1 hpc1.2
    b18_in_code b_eq.2.2.1 hf1 (j := 632)
    (by omega) (by omega) hdi1 hbuf1 hsi1 hdx1 hys1
    (c.whirIn hat1 hle1 (WL.whirIn_sub c.pIn (by rw [Array.length_toList]; unfold whirBytes; omega)))
    (c.apart_lp (by omega) (by omega) (by omega) (by omega))
    (by simp only [List.length_nil]; omega) fun st2 hpc2 hf2 hbuf2 hcs2 hk2 hts2 ↦ ?_
  rw [List.nil_append] at hbuf2
  -- `b19`: `extend(&point, tail)`.
  have hc2 : Core level m0 st2.data folded :=
    hc.keep hf2 ((hcs2 .r14 rfl).trans (hm1'.regs .r14 _ (hkr1 .r14 (by simp))))
      (fun j hj ↦ hk1.trans hk2 (by omega) (by omega) (by omega) (by omega)) hfo
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b19Offset) := hpc2
  let env3 := argEnv m0 st2.data 2672 8 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b20Offset)).toBitVec
  have hwf3 : env3.WF := c.wf0 hf2.frame.kept
  refine exec_at (infix_of b19_in_code (by simp [b19]) hp) exit_b19 hwf3 (fun _ _ ↦ rfl) hpc2'
    (match_retS hf2) fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hW3, hrdi3, hrsi3, hrdx3, hkr3⟩ := ok_b19
  obtain ⟨hf3, hs3⟩ := c.blk hf2 hwf3 hm3 hmid3 (hi := 40) (by omega) (hW3.le (by decide))
  have hk3 : KeepF m0 st2.data.dmem st3.data.dmem 2624 0 :=
    keepF_blk hwf3 hm3 (writesIn_of_mid hmid3) hW3 (by decide)
  have e3 : ∀ {r : Reg64} {v : Sym}, (after b19 retS).reg r = some v →
      reg st3.data r = v.eval env3 := fun h ↦ hm3.regs _ _ h
  have htail3 : NativeRustcVm.EWsAt st3.data.dmem (loc m0 1120) tail.toList :=
    hk3.ews (by omega) (by omega) (by omega)
      (hk2.ews (by omega) (by omega) (by omega)
        (hk1.ews (by omega) (by omega) (by omega) htail))
  have hbuf3 := hk3.buf (by omega) (by omega) (by omega) hbuf2
  have hdi3 : reg st3.data .rdi = loc m0 632 := (e3 hrdi3).trans (eval_ptr0A 632)
  have hsi3 : reg st3.data .rsi = loc m0 1120 := (e3 hrsi3).trans (eval_ptr0A 1120)
  have hdx3 : (reg st3.data .rdx).toNat = tail.toList.length := by
    rw [e3 hrdx3, Sym.eval, load_ofMachine (r := 0) (o := 40) rfl hc2.w40, Array.length_toList,
      htn]
  have hat3 := c.at_call (o := 32) (by omega) hf3
  have hts3 := c.ts_frame (hi := 40) (by omega) (hm3.kept hwf3) hs3 (hts2 hts1)
  refine ext_call hp c hext (jt := 261) (xs := w.alphas.toList) (ys := tail.toList) hpc3.1 hpc3.2
    b20_in_code b_eq.2.2.2.1 hf3 (j := 632)
    (by omega) (by omega) hdi3 hbuf3 hsi3 hdx3 htail3
    (c.inLoc (o := 32) (by omega) hf3 hle1 (by omega) (by omega))
    (c.apart_ll (by omega) (by omega) (by left; omega))
    (by omega) fun st4 hpc4 hf4 hbuf4 hcs4 hk4 hts4 ↦ ?_
  rw [← Array.toList_append, ← hP] at hbuf4
  -- `b21`: the rotated point zeroed, `extend(&rotated, point[lf..])`.
  have hP31 : P.size < 31 := by rw [hPs]; omega
  set lf := (reg m0 .r8).toNat with hlf
  have hdl : (P.toList.drop lf).length = P.size - lf := by rw [List.length_drop, hPl]
  have htk : (P.toList.take lf).length = min lf P.size := by rw [List.length_take, hPl]
  have hw48 : NativeRustcVm.WordAt st4.data.dmem (loc m0 48) (.ofBitVec (reg m0 .r8)) :=
    hk4.word (by omega) (by omega) (by omega) (hk3.word (by omega) (by omega) (by omega)
      (hk2.word (by omega) (by omega) (by omega) (hk1.word (by omega) (by omega) (by omega) h48)))
  have hw56 : NativeRustcVm.WordAt st4.data.dmem (loc m0 56) (.ofBitVec (reg m0 .r9)) :=
    hk4.word (by omega) (by omega) (by omega) (hk3.word (by omega) (by omega) (by omega)
      (hk2.word (by omega) (by omega) (by omega) (hk1.word (by omega) (by omega) (by omega) h56)))
  have htail4 := hk4.ews (by omega) (by omega) (by omega) htail3
  have hpc4' : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b21Offset) := hpc4
  let env5 := argEnv m0 st4.data 2672 8 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b22Offset)).toBitVec
  have hwf5 : env5.WF := c.wf0 hf4.frame.kept
  refine exec_at (infix_of b21_in_code (by simp [b21]) hp) exit_b21 hwf5 (fun _ _ ↦ rfl) hpc4'
    (match_retS hf4) fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hmid5, hW5, h144, hrdi5, hrsi5, hrdx5, hrbx5, hr135, hkr5⟩ := ok_b21
  have e5 : ∀ {r : Reg64} {v : Sym}, (after b21 retS).reg r = some v →
      reg st5.data r = v.eval env5 := fun h ↦ hm5.regs _ _ h
  obtain ⟨hf5, hs5⟩ := c.blk hf4 hwf5 hm5 hmid5 (hi := 632) (by omega) (hW5.le (by decide))
  have hk5 : KeepF m0 st4.data.dmem st5.data.dmem 144 488 :=
    keepF_blk hwf5 hm5 (writesIn_of_mid hmid5) hW5 (by decide)
  have l632 : env5.load 0 632 8 = BitVec.ofNat 64 P.size := by
    have := load_ofMachine (r := 0) (o := 632) (rs := [(stackBelow m0 2672, 2672 + 8 + 8)])
      (vs := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b22Offset)).toBitVec) (m := st4.data) rfl hbuf4.2.1
    rw [this, hPl]
    rfl
  have l48 : env5.load 0 48 8 = reg m0 .r8 := load_ofMachine (r := 0) (o := 48) rfl hw48
  have hpts : NativeRustcVm.EWsAt st4.data.dmem (loc m0 640) P.toList := by
    have := hbuf4.2.2
    rwa [show loc m0 632 + 8#64 = loc m0 640 from off_add _ _ _] at this
  have hbx5 : reg st5.data .rbx = loc m0 640 :=
    (e5 hrbx5).trans ((vPt_eval env5 l632 hP31).trans (by
      show fa m0 + BitVec.ofInt 64 640 = fa m0 + BitVec.ofNat 64 640; rfl))
  have h135 : reg st5.data .r13 = BitVec.ofNat 64 P.size := (e5 hr135).trans (vLen_eval env5 l632 hP31)
  have hdi5 : reg st5.data .rdi = loc m0 144 := (e5 hrdi5).trans (eval_ptr0A 144)
  have hdx5 : (reg st5.data .rdx).toNat = (P.toList.drop lf).length := by
    rw [e5 hrdx5, vRd_toNat env5 l632 hP31 l48, hdl]
  have hbuf5 : NativeRustcVm.BufEWAt st5.data.dmem (loc m0 144) 30 [] :=
    ⟨by simp, wordAt_written hm5 (r := 0) (o := 144) rfl (by omega) h144 (w := 0) rfl,
      NativeRustcVm.ewsAt_nil _ _⟩
  have hpts5 := hk5.ews (by omega) (by omega) (by omega) hpts
  have hat5 := c.at_call (o := 32) (by omega) hf5
  have hts5 := c.ts_frame (hi := 632) (by omega) (hm5.kept hwf5) hs5 (hts4 hts3)
  have hdrop0 : ∀ h : P.size < lf, P.toList.drop lf = [] := fun h ↦
    List.drop_eq_nil_of_le (by omega)
  have hsi5 : reg st5.data .rsi =
      (if P.size < lf then BitVec.ofNat 64 8 else loc m0 (640 + 16 * lf)) := by
    rw [e5 hrsi5, vRs_eval env5 l632 hP31 l48]
    split
    · rfl
    · show off (fa m0) 640 + BitVec.ofNat 64 (16 * lf) = _
      exact off_add _ _ _
  have hys5 : NativeRustcVm.EWsAt st5.data.dmem
      (if P.size < lf then BitVec.ofNat 64 8 else loc m0 (640 + 16 * lf)) (P.toList.drop lf) := by
    split
    · rename_i h; rw [hdrop0 h]; exact NativeRustcVm.ewsAt_nil _ _
    · have := hpts5.drop lf
      rwa [show loc m0 640 + BitVec.ofNat 64 (16 * lf) = loc m0 (640 + 16 * lf) from
        off_add _ _ _] at this
  have hin5 : WhirIn st5.data
      (if P.size < lf then BitVec.ofNat 64 8 else loc m0 (640 + 16 * lf))
      (16 * (P.toList.drop lf).length) bufEWExtendStack := by
    split
    · rename_i h; rw [hdrop0 h]; exact c.in8 (o := 32) (by omega) hf5 (by decide)
    · exact c.inLoc (o := 32) (by omega) hf5 hle1 (by omega)
        (by omega)
  have hap5 : NativeRustcVm.Apart (loc m0 144) 488
      (if P.size < lf then BitVec.ofNat 64 8 else loc m0 (640 + 16 * lf))
      (16 * (P.toList.drop lf).length) := by
    split
    · rename_i h
      rw [hdrop0 h]
      unfold NativeRustcVm.Apart
      rw [c.loc_toNat (by omega)]
      have := g.hN
      right; simp only [BitVec.toNat_ofNat, List.length_nil]; omega
    · exact c.apart_ll (by omega) (by omega) (by left; omega)
  refine ext_call hp c hext (jt := 341) (xs := []) (ys := P.toList.drop lf) hpc5.1 hpc5.2
    b22_in_code b_eq.2.2.2.2.1 hf5 (j := 144)
    (by omega) (by omega) hdi5 hbuf5 hsi5 hdx5 hys5 hin5 hap5
    (by simp only [List.length_nil]; omega) fun st6 hpc6 hf6 hbuf6 hcs6 hk6 hts6 ↦ ?_
  rw [List.nil_append] at hbuf6
  -- `b23`: `extend(&rotated, point[..lf])`.
  have hpc6' : st6.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b23Offset) := hpc6
  let env7 := argEnv m0 st6.data 2672 8 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b24Offset)).toBitVec
  have hwf7 : env7.WF := c.wf0 hf6.frame.kept
  refine exec_at (infix_of b23_in_code (by simp [b23]) hp) exit_b23 hwf7 (fun _ _ ↦ rfl) hpc6'
    (match_retS hf6) fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨hmid7, hW7, hrdi7, hrsi7, hrdx7, hkr7⟩ := ok_b23
  have e7 : ∀ {r : Reg64} {v : Sym}, (after b23 retS).reg r = some v →
      reg st7.data r = v.eval env7 := fun h ↦ hm7.regs _ _ h
  obtain ⟨hf7, hs7⟩ := c.blk hf6 hwf7 hm7 hmid7 (hi := 40) (by omega) (hW7.le (by decide))
  have hk7 : KeepF m0 st6.data.dmem st7.data.dmem 2624 0 :=
    keepF_blk hwf7 hm7 (writesIn_of_mid hmid7) hW7 (by decide)
  have hk7r : ∀ r ∈ six, reg st7.data r = reg st6.data r := fun r hr ↦ e7 (hkr7 r hr)
  have hw48' : NativeRustcVm.WordAt st6.data.dmem (loc m0 48) (.ofBitVec (reg m0 .r8)) :=
    hk6.word (by omega) (by omega) (by omega) (hk5.word (by omega) (by omega) (by omega) hw48)
  have hdi7 : reg st7.data .rdi = loc m0 144 := (e7 hrdi7).trans (eval_ptr0A 144)
  have hsi7 : reg st7.data .rsi = loc m0 640 :=
    (e7 hrsi7).trans ((hcs6 .rbx rfl).trans hbx5)
  have hdx7 : (reg st7.data .rdx).toNat = (P.toList.take lf).length := by
    rw [e7 hrdx7, vMin_toNat env7 ((hcs6 .r13 rfl).trans h135) hP31
      (load_ofMachine (r := 0) (o := 48) rfl hw48'), htk, Nat.min_comm]
  have hpts7 : NativeRustcVm.EWsAt st7.data.dmem (loc m0 640) P.toList :=
    hk7.ews (by omega) (by omega) (by omega)
      (hk6.ews (by omega) (by omega) (by omega) hpts5)
  have hbuf7 := hk7.buf (by omega) (by omega) (by omega) hbuf6
  have hat7 := c.at_call (o := 32) (by omega) hf7
  have hts7 := c.ts_frame (hi := 40) (by omega) (hm7.kept hwf7) hs7 (hts6 hts5)
  refine ext_call hp c hext (jt := 349) (xs := P.toList.drop lf) (ys := P.toList.take lf)
    hpc7.1 hpc7.2 b24_in_code b_eq.2.2.2.2.2.1 hf7 (j := 144)
    (by omega) (by omega) hdi7 hbuf7 hsi7 hdx7 (hpts7.take lf)
    (c.inLoc (o := 32) (by omega) hf7 hle1 (by omega)
      (by omega))
    (c.apart_ll (by omega) (by omega) (by left; omega))
    (by omega)
    fun st8 hpc8 hf8 hbuf8 hcs8 hk8 hts8 ↦ ?_
  -- to `b25`.
  have hc8 : Core level m0 st8.data folded := by
    refine hc.keep hf8 ?_ (fun j hj ↦ ?_) hfo
    · exact (hcs8 .r14 rfl).trans ((hk7r .r14 (by simp [six])).trans ((hcs6 .r14 rfl).trans
        ((e5 (hkr5 .r14 (by simp))).trans ((hcs4 .r14 rfl).trans ((e3 (hkr3 .r14 (by simp [six]))).trans
          ((hcs2 .r14 rfl).trans (hm1'.regs .r14 _ (hkr1 .r14 (by simp)))))))))
    · rw [hk8 j (by omega) (by omega) (by omega), hk7 j (by omega) (by omega) (by omega),
        hk6 j (by omega) (by omega) (by omega), hk5 j (by omega) (by omega) (by omega),
        hk4 j (by omega) (by omega) (by omega), hk3 j (by omega) (by omega) (by omega),
        hk2 j (by omega) (by omega) (by omega), hk1 j (by omega) (by omega) (by omega)]
  refine cont st8 hpc8 hc8 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (hcs8 .rbx rfl).trans ((hk7r .rbx (by simp [six])).trans ((hcs6 .rbx rfl).trans hbx5))
  · exact (hcs8 .r12 rfl).trans ((hk7r .r12 (by simp [six])).trans ((hcs6 .r12 rfl).trans
      ((e5 (hkr5 .r12 (by simp))).trans ((hcs4 .r12 rfl).trans
        ((e3 (hkr3 .r12 (by simp [six]))).trans ((hcs2 .r12 rfl).trans h12))))))
  · exact (hcs8 .r15 rfl).trans ((hk7r .r15 (by simp [six])).trans ((hcs6 .r15 rfl).trans
      ((e5 (hkr5 .r15 (by simp))).trans ((hcs4 .r15 rfl).trans
        ((e3 (hkr3 .r15 (by simp [six]))).trans ((hcs2 .r15 rfl).trans h15))))))
  · exact (hcs8 .r13 rfl).trans ((hk7r .r13 (by simp [six])).trans ((hcs6 .r13 rfl).trans h135))
  · exact hk8.word (by omega) (by omega) (by omega) (hk7.word (by omega) (by omega) (by omega)
      (hk6.word (by omega) (by omega) (by omega) (hk5.word (by omega) (by omega) (by omega) hw56)))
  · exact hk8.buf (by omega) (by omega) (by omega) (hk7.buf (by omega) (by omega) (by omega)
      (hk6.buf (by omega) (by omega) (by omega) (hk5.buf (by omega) (by omega) (by omega) hbuf4)))
  · rw [Array.toList_append, extract_drop, extract_take]
    exact hbuf8
  · exact hk8.ews (by omega) (by omega) (by omega)
      (hk7.ews (by omega) (by omega) (by omega)
        (hk6.ews (by omega) (by omega) (by omega)
          (hk5.ews (by omega) (by omega) (by omega) htail4)))
  · exact hts8 hts7

end

end NativeRustcVmX64.Whir.Levels.FL
