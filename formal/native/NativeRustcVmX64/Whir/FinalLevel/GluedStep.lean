module

public import NativeRustcVmX64.Whir.FinalLevel.Rotate
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.GluedEval.Names

/-!
# `final_level`: one glued claim (x86-64)

`GB`: what the end check reads (`Core`, the claim at `88`, `96`, the tail, the `TState`, the
weight in R15, RBP). `GInv i`: at the glued loop's head (`b29`) before claim `i`: `GB` with the
weight `weightAt … i`, claim `i`'s address in R13, the claims' end at `104`, the point (its length
at `48`, its entries at `640`, their address at `56`). `gstep`: `glued_eval` (`b29`), its tag
(`b30`), `EW::mul` by the claim's scalar (`b31`), the sum and the next claim or the end (`b32`).
-/

namespace NativeRustcVmX64.Whir.Levels.FL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.FinalLevel

@[expose] public section

/-- **What the end check reads**, the weight `wt` in R15, RBP. -/
structure GB [Labels] (a : DecArea) (level : Whir.Level) (m0 : MachineData) (folded tail : Array EW)
    (claim wt : EW) (s5 : TState) (d : MachineData) : Prop where
  core : Core level m0 d folded
  w88 : NativeRustcVm.WordAt d.dmem (loc m0 88) claim.c0
  w96 : NativeRustcVm.WordAt d.dmem (loc m0 96) claim.c1
  tail : NativeRustcVm.EWsAt d.dmem (loc m0 1120) tail.toList
  ts : TStateAt d.dmem (tA m0) a s5
  r15 : reg d .r15 = wt.c0.toBitVec
  rbp : reg d .rbp = wt.c1.toBitVec

/-- **The glued loop's head** before claim `i`. -/
structure GInv [Labels] (a : DecArea) (level : Whir.Level) (b : BasisW) (w : WhirStateW)
    (m0 : MachineData) (folded tail : Array EW) (claim : EW) (s5 : TState) (i : Nat)
    (d : MachineData) : Prop where
  gb : GB a level m0 folded tail claim (weightAt (reg m0 .r8).toNat b w tail i) s5 d
  lt : i < w.glued.size
  r13 : reg d .r13 = pA m0 + BitVec.ofNat 64 (512 + 6064 * i)
  w104 : NativeRustcVm.WordAt d.dmem (loc m0 104)
    (.ofBitVec (pA m0 + BitVec.ofNat 64 (512 + 6064 * w.glued.size)))
  w56 : NativeRustcVm.WordAt d.dmem (loc m0 56) (.ofBitVec (loc m0 640))
  w48 : NativeRustcVm.WordAt d.dmem (loc m0 48) (.ofBitVec (BitVec.ofNat 64 (w.alphas ++ tail).size))
  pts : NativeRustcVm.EWsAt d.dmem (loc m0 640) (w.alphas ++ tail).toList

end

public section

/-- `GB` kept: the frame, R14, R15, RBP, and the frame's bytes `40` to `48`, `88` to `104`,
`1120` to `2624`. -/
theorem GB.keep [Labels] {a : DecArea} {level : Whir.Level} {m0 d d' : MachineData}
    {folded tail : Array EW} {claim wt : EW} {s5 : TState}
    (h : GB a level m0 folded tail claim wt s5 d) (hf : Fr m0 40 d')
    (hr : ∀ r ∈ [Reg64.r14, .r15, .rbp], reg d' r = reg d r) {lo n : Nat}
    (hk : KeepF m0 d.dmem d'.dmem lo n)
    (hdis : (48 ≤ lo ∧ lo + n ≤ 88) ∨ (104 ≤ lo ∧ lo + n ≤ 1120) ∨ 2624 ≤ lo)
    (h64 : 2 ^ mu m0 + level.fold ≤ 64) (htn : tail.size ≤ 30)
    (hts : TStateAt d'.dmem (tA m0) a s5) : GB a level m0 folded tail claim wt s5 d' where
  core := h.core.keep hf (hr .r14 (by simp)) (fun j hj ↦ hk j (by omega) (by omega) (by omega)) h64
  w88 := hk.word (by omega) (by omega) (by omega) h.w88
  w96 := hk.word (by omega) (by omega) (by omega) h.w96
  tail := hk.ews (by omega) (by rw [Array.length_toList]; omega)
    (by rw [Array.length_toList]; omega) h.tail
  ts := hts
  r15 := (hr .r15 (by simp)).trans h.r15
  rbp := (hr .rbp (by simp)).trans h.rbp

/-- One glued claim's term, limb by limb. -/
theorem gStep_c (pt : Array EW) (wt : EW) (g : GluedClaimW) :
    (gStep pt wt g).c0 = (EW.mul g.scalar (g.weight.eval (pt.extract g.foldStart pt.size))).c0 ^^^
      wt.c0 ∧
    (gStep pt wt g).c1 = (EW.mul g.scalar (g.weight.eval (pt.extract g.foldStart pt.size))).c1 ^^^
      wt.c1 :=
  ⟨UInt64.xor_comm wt.c0 _, UInt64.xor_comm wt.c1 _⟩

theorem ew_eta (x : EW) : (⟨UInt64.ofBitVec x.c0.toBitVec, UInt64.ofBitVec x.c1.toBitVec⟩ : EW) = x :=
  rfl

theorem vGc_toNat [Labels] (env : Env) {n f : Nat} (h48 : env.load 0 48 8 = BitVec.ofNat 64 n)
    (hn : n < 31) (h16 : env.load 1 16 8 = BitVec.ofNat 64 f) (hf : f < 2 ^ 64) :
    (vGc.eval env).toNat = n - f := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  have hf' : (BitVec.ofNat 64 f).toNat = f := by rw [BitVec.toNat_ofNat]; omega
  simp only [vGc, Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, h48, h16]
  split <;> rename_i hc <;> simp only [BitVec.ult, decide_eq_true_eq, hn', hf'] at hc
  · simp; omega
  · rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hn', hf']; omega), hn', hf']

theorem vGd_eval [Labels] (env : Env) {n f : Nat} (h48 : env.load 0 48 8 = BitVec.ofNat 64 n)
    (hn : n < 31) (h16 : env.load 1 16 8 = BitVec.ofNat 64 f) (hf : f < 2 ^ 64) {p : BitVec 64}
    (h56 : env.load 0 56 8 = p) :
    vGd.eval env = if n < f then BitVec.ofNat 64 8 else p + BitVec.ofNat 64 (16 * f) := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  have hf' : (BitVec.ofNat 64 f).toNat = f := by rw [BitVec.toNat_ofNat]; omega
  simp only [vGd, Sym.eval, SBool.eval, CmpOp.apply, low_W64, h48, h16, h56]
  by_cases hc : n < f
  · have : (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 f) = true := by
      simp only [BitVec.ult, hn', hf']; exact decide_eq_true hc
    simp only [this, ite_true, hc]
  · have : (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 f) = false := by
      simp only [BitVec.ult, hn', hf']; exact decide_eq_false hc
    simp only [this, Bool.false_eq_true, ite_false, hc]
    show BinOp.apply .add .W64 p (BinOp.apply .shl .W64 (BitVec.ofNat 64 f) (BitVec.ofNat 64 4)) = _
    rw [shl4, hf']
    simp only [BinOp.apply, low_W64, ext_W64]

theorem cMore_eval [Labels] (env : Env) {p : BitVec 64}
    {i n : Nat} (hi : i < n) (hn : n ≤ 10)
    (h13 : env.regs .r13 = p + BitVec.ofNat 64 (512 + 6064 * i))
    (h104 : env.load 0 104 8 = p + BitVec.ofNat 64 (512 + 6064 * n)) :
    cMore.eval env = decide (i + 1 < n) := by
  simp only [cMore, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, h13, h104]
  have e : BitVec.ofNat 64 6064 + (p + BitVec.ofNat 64 (512 + 6064 * i)) =
      p + BitVec.ofNat 64 (512 + 6064 * (i + 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e]
  by_cases h : i + 1 < n
  · rw [decide_eq_true h]
    have hne : (p + BitVec.ofNat 64 (512 + 6064 * (i + 1)) ==
        p + BitVec.ofNat 64 (512 + 6064 * n)) = false := by
      rw [beq_eq_false_iff_ne]
      intro he
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
      omega
    rw [hne]; rfl
  · rw [decide_eq_false h, show i + 1 = n by omega]
    simp

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **One glued claim**: `b29` to `b32`, to the next claim's head or to `b33`. -/
theorem gstep (hp : Placed code k) (c : Ctx a s level ba b w rounds m0)
    (hge : ∀ g, Spec (Labels.label NativeRustcVmX64.Vm.GluedEval.entryLabel) (GluedEvalPre g) (GluedEvalPost g))
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {st : MachineState} {folded tail : Array EW} {claim : EW} {s5 : TState} {i : Nat}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b29Offset)) (htn : tail.size = mu m0)
    (hI : GInv a level b w m0 folded tail claim s5 i st.data) :
    Eventually (step1 Host.exe) (fun st' ↦
      (i + 1 < w.glued.size ∧ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b29Offset) ∧
        GInv a level b w m0 folded tail claim s5 (i + 1) st'.data) ∨
      (i + 1 = w.glued.size ∧ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b33Offset) ∧
        GB a level m0 folded tail claim (weightAt (reg m0 .r8).toNat b w tail (i + 1)) s5
          st'.data)) st := by
  have g := c.geo
  have hfo : 2 ^ mu m0 + level.fold ≤ 64 := c.fold
  have hal : w.alphas.size + mu m0 ≤ 30 := c.alphas
  have hf := hI.gb.core.fr
  set P := w.alphas ++ tail with hP
  have hPs : P.size = w.alphas.size + mu m0 := by rw [hP, Array.size_append, htn]
  have hPl : P.toList.length = P.size := Array.length_toList
  have hP31 : P.size < 31 := by omega
  have hPl2 : (w.alphas ++ tail).toList.length ≤ 30 := by
    rw [Array.length_toList, Array.size_append, htn]; omega
  have hws := (c.whir_at hf.same).1
  have hn10 : w.glued.size ≤ 10 := hws.glued_le
  have hi := hI.lt
  set gp := pA m0 + BitVec.ofNat 64 (512 + 6064 * i) with hgp
  have hgpn : gp.toNat = (pA m0).toNat + (512 + 6064 * i) :=
    NativeRustcVm.toNat_add_ofNat (by have := g.pW; omega)
  have hga : GluedAt st.data.dmem gp w.glued[i] := hws.glued i hi
  obtain ⟨hsc, hfs, hfsw, -⟩ := hga
  obtain ⟨hsc0, hsc1⟩ := ewAt_iff'.mp hsc
  -- `b29`: `glued_eval(&out, &glued[i], point[fs..])`.
  let ret1 := (Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b30Offset)).toBitVec
  let env1 := argEnv m0 st.data 2672 8 [(gp, 24)] (fun _ ↦ 0) ret1
  have hwf1 : env1.WF :=
    c.wf1 hf.frame.kept (fun j hj ↦ by
      have := Mapped.keeps c.pout.1.1 hf.frame.kept (512 + 6064 * i + j) (by unfold whirBytes; omega)
      rwa [show pA m0 + BitVec.ofNat 64 (512 + 6064 * i + j) = gp + BitVec.ofNat 64 j by
        rw [hgp, BitVec.add_assoc, ← BitVec.ofNat_add]] at this) (by rw [hgpn]; have := g.pW; omega)
      (by rw [hgpn]; have := g.pS; omega)
  have hm1 : Match env1 gS st.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨Frame.rsp_evalA hf.frame, known_ptr rfl hI.r13, trivial⟩
      trivial trivial trivial
  refine exec_at (infix_of b29_in_code (by simp [b29]) hp) exit_b29 hwf1 (fun _ _ ↦ rfl) hpc hm1
    fun st1 hm1' hpc1 ↦ ?_
  obtain ⟨hmid1, hW1, hrdi1, hrsi1, hrdx1, hrcx1, hrbx1, hr121, hr131, hkr1⟩ := ok_b29
  have e1 : ∀ {r : Reg64} {v : Sym}, (after b29 gS).reg r = some v →
      reg st1.data r = v.eval env1 := fun h ↦ hm1'.regs _ _ h
  obtain ⟨hf1, hs1⟩ := c.blk hf hwf1 hm1' hmid1 (hi := 40) (by omega) (hW1.le (by decide))
  have hk1 : KeepF m0 st.data.dmem st1.data.dmem 2624 0 :=
    keepF_blk hwf1 hm1' (writesIn_of_mid hmid1) hW1 (by decide)
  have l48 : env1.load 0 48 8 = BitVec.ofNat 64 P.size := load_ofMachine (r := 0) (o := 48) rfl hI.w48
  have l56 : env1.load 0 56 8 = loc m0 640 := load_ofMachine (r := 0) (o := 56) rfl hI.w56
  have l16 : env1.load 1 16 8 = BitVec.ofNat 64 w.glued[i].foldStart :=
    load_ofMachine (r := 1) (o := 16) rfl hfsw
  set fs := w.glued[i].foldStart with hfsd
  have hdi1 : reg st1.data .rdi = loc m0 64 := (e1 hrdi1).trans (eval_ptr0A 64)
  have hsi1 : reg st1.data .rsi = gp := (e1 hrsi1).trans (eval_ptr rfl)
  have hbx1 : reg st1.data .rbx = w.glued[i].scalar.c0.toBitVec :=
    (e1 hrbx1).trans (load_ofMachine (r := 1) (o := 0) rfl (by rw [off_zero]; exact hsc0))
  have h121 : reg st1.data .r12 = w.glued[i].scalar.c1.toBitVec :=
    (e1 hr121).trans (load_ofMachine (r := 1) (o := 8) rfl hsc1)
  have hdl : (P.toList.drop fs).length = P.size - fs := by rw [List.length_drop, hPl]
  have hcxn : (reg st1.data .rcx).toNat = (P.toList.drop fs).length := by
    rw [e1 hrcx1, vGc_toNat env1 l48 hP31 l16 hfs, hdl]
  have hdx1 : reg st1.data .rdx = (if P.size < fs then BitVec.ofNat 64 8 else loc m0 (640 + 16 * fs)) := by
    rw [e1 hrdx1, vGd_eval env1 l48 hP31 l16 hfs l56]
    split
    · rfl
    · exact off_add _ _ _
  have hpts1 := hk1.ews (xs := P.toList) (by omega) (by omega) (by omega) hI.pts
  have hdrop0 : ∀ h : P.size < fs, P.toList.drop fs = [] := fun h ↦
    List.drop_eq_nil_of_le (by omega)
  have hys1 : NativeRustcVm.EWsAt st1.data.dmem
      (if P.size < fs then BitVec.ofNat 64 8 else loc m0 (640 + 16 * fs)) (P.toList.drop fs) := by
    split
    · rename_i h; rw [hdrop0 h]; exact NativeRustcVm.ewsAt_nil _ _
    · have := hpts1.drop fs
      rwa [show loc m0 640 + BitVec.ofNat 64 (16 * fs) = loc m0 (640 + 16 * fs) from
        off_add _ _ _] at this
  have hat1 := c.at_call (o := 32) (by omega) hf1
  have hle1 : 2672 - 32 + gluedEvalStack ≤ finalLevelStack := by decide
  have hslice : slice st1.data (reg st1.data .rdx) (reg st1.data .rcx) =
      P.extract fs P.size := by
    rw [hdx1, slice_eq hcxn hys1, extract_drop]
  have hpre1 : GluedEvalPre w.glued[i] st1.data := by
    refine ⟨(c.sctx (by decide)).stackOk hat1 hle1, ?_, ?_, ?_, ?_, ?_⟩
    · show GluedAt st1.data.dmem (reg st1.data .rsi) w.glued[i]
      rw [hsi1]; exact (c.whir_at hf1.same).1.glued i hi
    · show WhirIn st1.data (reg st1.data .rsi) gluedBytes gluedEvalStack
      rw [hsi1]
      exact c.whirIn hat1 hle1 (WL.whirIn_sub c.pIn (by unfold whirBytes gluedBytes; omega))
    · show SliceOk st1.data (reg st1.data .rdx) (reg st1.data .rcx) gluedEvalStack
      rw [hdx1]
      split
      · rename_i h
        show WhirIn st1.data _ (16 * (reg st1.data .rcx).toNat) gluedEvalStack
        rw [hcxn, hdrop0 h]
        exact c.in8 (o := 32) (by omega) hf1 (by decide)
      · exact c.sliceLoc (o := 32) (by omega) hf1 hle1 (by omega) (by rw [hcxn, hdl]; omega)
    · show WhirIn st1.data (reg st1.data .rdi) 24 gluedEvalStack
      rw [hdi1]; exact c.inLoc (o := 32) (by omega) hf1 hle1 (by omega) (by omega)
    · rw [hsi1, hdi1, hdx1, hcxn, hdl]
      apply c.got_call hf1 (by omega) hle1 (by decide)
      intro ar har
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with (rfl | rfl) | har
      · refine ⟨(pA m0, whirBytes), by simp, ?_, ?_⟩
        · change (pA m0).toNat ≤ gp.toNat
          rw [hgpn]
          omega
        · change gp.toNat + 6064 ≤ (pA m0).toNat + 63200
          rw [hgpn]
          omega
      · exact c.got_loc (by omega) (by omega)
      · by_cases hn : 0 < P.size - fs
        · simp only [ite_eq_left hn, List.mem_singleton,
            ite_eq_right (show ¬P.size < fs by omega)] at har
          subst ar
          exact c.got_loc (by omega) (by omega)
        · simp [hn] at har
  refine call_then hpc1 (hge w.glued[i]) hpre1 fun st2 hpc2 hrsp2 hq ↦ ?_
  obtain ⟨hopt, hch, hsv⟩ := hq
  rw [hdi1, hslice] at hopt
  have hch' : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem (fun q ↦
      NativeRustcVm.InRange (loc m0 64) 24 q ∨
        NativeRustcVm.InRange (stackBelow st1.data gluedEvalStack) gluedEvalStack q) :=
    NativeRustcVm.SameOutside.mono hch fun q hq ↦ by
      rcases hq with hq | hq
      · left; rw [hdi1] at hq; exact one_iff.mp hq
      · exact Or.inr hq
  obtain ⟨hf2, hkeep2⟩ := c.call (o := 32) (by omega) hf1 hle1 hsv hrsp2
    (R := NativeRustcVm.InRange (loc m0 64) 24) (lo := 64) (n := 24) (by omega) (by omega)
    (fun q hq ↦ Or.inr hq) hch'
  have hk2 : KeepF m0 st1.data.dmem st2.data.dmem 64 24 := hkeep2
  have hts2 := c.ts_call (o := 32) (by omega) hf1 hle1 hsv
    (fun q hq ↦ c.loc_not_t (by omega) hq) hch'
    (c.ts_frame (hi := 40) (by omega) (hm1'.kept hwf1) hs1 hI.gb.ts)
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b30Offset) := hpc2
  -- `b30`: the tag.
  refine Eventually.bind (cond_spec hp c b30_in_code (by simp [b30]) (b_eq.2.2.2.2.2.2 ▸ exit_b26)
    (b_eq.2.2.2.2.2.2 ▸ ok_b26) hf2 hpc2') fun st3 ⟨hr3, hd3, hpc3⟩ ↦ ?_
  obtain ⟨hopt1, hopt2⟩ := hopt
  have h1 := load4_of_tag (Or.inr rfl) (show NativeRustcVm.WordAt
    ((argEnv m0 st2.data 2672 8 [] (fun _ ↦ 0) 0).mem0)
    ((argEnv m0 st2.data 2672 8 [] (fun _ ↦ 0) 0).base 0 + BitVec.ofNat 64 64) 1 from hopt1)
  rw [cTag64_eval _ (Or.inr rfl) h1] at hpc3
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false] at hpc3
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b31Offset) := hpc3
  have hf3 := hf2.congr hr3 hd3
  set ev := w.glued[i].weight.eval (P.extract fs P.size) with hev
  have hev72 : NativeRustcVm.EWAt st3.data.dmem (loc m0 72) ev := by
    rw [hd3]; have := hopt2; rwa [show off (loc m0 64) 8 = loc m0 72 from off_off _ _ _] at this
  obtain ⟨hev0, hev1⟩ := ewAt_iff'.mp hev72
  rw [show off (loc m0 72) 8 = loc m0 80 from off_off _ _ _] at hev1
  -- `b31`: `EW::mul(scalar, ev)`.
  let env4 := argEnv m0 st3.data 2672 8 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b32Offset)).toBitVec
  have hwf4 : env4.WF := c.wf0 hf3.frame.kept
  refine exec_at (infix_of b31_in_code (by simp [b31]) hp) exit_b31 hwf4 (fun _ _ ↦ rfl) hpc3'
    (match_retS hf3) fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid4, hW4, hrdi4, hrsi4, hrdx4, hrcx4, hkr4⟩ := ok_b31
  have e4 : ∀ {r : Reg64} {v : Sym}, (after b31 retS).reg r = some v →
      reg st4.data r = v.eval env4 := fun h ↦ hm4.regs _ _ h
  obtain ⟨hf4, hs4⟩ := c.blk hf3 hwf4 hm4 hmid4 (hi := 40) (by omega) (hW4.le (by decide))
  have hk4 : KeepF m0 st3.data.dmem st4.data.dmem 2624 0 :=
    keepF_blk hwf4 hm4 (writesIn_of_mid hmid4) hW4 (by decide)
  have hcs3 : ∀ r, calleeSaved r = true → reg st3.data r = reg st1.data r := fun r hr ↦
    (hr3 r).trans (hsv.1 r hr)
  have hargs : (⟨.ofBitVec (reg st4.data .rdi), .ofBitVec (reg st4.data .rsi)⟩ : EW) =
      w.glued[i].scalar ∧
      (⟨.ofBitVec (reg st4.data .rdx), .ofBitVec (reg st4.data .rcx)⟩ : EW) = ev := by
    refine ⟨?_, ?_⟩
    · rw [e4 hrdi4, e4 hrsi4]
      show (⟨.ofBitVec (reg st3.data .rbx), .ofBitVec (reg st3.data .r12)⟩ : EW) = _
      rw [hcs3 .rbx rfl, hcs3 .r12 rfl, hbx1, h121]
    · rw [e4 hrdx4, e4 hrcx4, Sym.eval, Sym.eval, load_ofMachine (r := 0) (o := 72) rfl hev0,
        load_ofMachine (r := 0) (o := 80) rfl hev1]
  have hat4 := c.at_call (o := 32) (by omega) hf4
  have hle4 : 2672 - 32 + ewMulStack ≤ finalLevelStack := by decide
  refine call_then hpc4 hmul ((c.sctx (by decide)).stackOk hat4 hle4) fun st5 hpc5 hrsp5 hq5 ↦ ?_
  obtain ⟨hax5, hdx5, hch5, hsv5⟩ := hq5
  rw [hargs.1, hargs.2] at hax5 hdx5
  have hch5' : NativeRustcVm.SameOutside st4.data.dmem st5.data.dmem (fun q ↦
      NativeRustcVm.InRange (loc m0 2624) 0 q ∨
        NativeRustcVm.InRange (stackBelow st4.data ewMulStack) ewMulStack q) :=
    NativeRustcVm.SameOutside.mono hch5 fun q hq ↦ Or.inr hq
  obtain ⟨hf5, hkeep5⟩ := c.call (o := 32) (by omega) hf4 hle4 hsv5 hrsp5
    (R := NativeRustcVm.InRange (loc m0 2624) 0) (lo := 2624) (n := 0) (by omega) (by omega)
    (fun q hq ↦ Or.inr hq) hch5'
  have hk5 : KeepF m0 st4.data.dmem st5.data.dmem 2624 0 := hkeep5
  have hts5 := c.ts_call (o := 32) (by omega) hf4 hle4 hsv5
    (fun q hq ↦ c.loc_not_t (by omega) hq) hch5'
    (c.ts_frame (hi := 40) (by omega) (hm4.kept hwf4) hs4
      (show TStateAt st3.data.dmem (tA m0) a s5 by rw [hd3]; exact hts2))
  have hpc5' : st5.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b32Offset) := hpc5
  -- `b32`: the sum, the next claim.
  let env6 := argEnv m0 st5.data 2672 8 [] (fun _ ↦ 0) 0
  have hwf6 : env6.WF := c.wf0 hf5.frame.kept
  refine exec_at (infix_of b32_in_code (by simp [b32]) hp) exit_b32 hwf6 nofun hpc5'
    (match_retS hf5) fun st6 hm6 hpc6 ↦ ?_
  obtain ⟨hmid6, hmem6, hr156, hrbp6, hr136, hkr6⟩ := ok_b32
  have hd6 : st6.data.dmem = st5.data.dmem := hm6.dmem_eq hwf6 hmem6
  have hf6 : Fr m0 40 st6.data :=
    ⟨Frame.of_blockA hf5.frame hwf6 hm6 hmid6 slots_le, by rw [Sm, hd6]; exact hf5.same⟩
  have hreg5 : ∀ r ∈ [Reg64.r14, .r15, .rbp], reg st5.data r = reg st.data r := fun r hr ↦ by
    have h6 : r ∈ six := by simp at hr; rcases hr with rfl | rfl | rfl <;> simp [six]
    exact (hsv5.1 r (six_cs h6)).trans ((e4 (hkr4 r h6)).trans ((hcs3 r (six_cs h6)).trans
      (e1 (hkr1 r (by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)))))
  have h135 : reg st5.data .r13 = gp :=
    (hsv5.1 .r13 rfl).trans ((e4 (hkr4 .r13 (by simp [six]))).trans ((hcs3 .r13 rfl).trans
      ((e1 hr131).trans (eval_ptr rfl))))
  have hk : KeepF m0 st.data.dmem st6.data.dmem 64 24 := fun j h1 h2 h3 ↦ by
    rw [hd6, hk5 j (by omega) h2 (by omega), hk4 j (by omega) h2 (by omega), hd3,
      hk2 j (by omega) h2 h3, hk1 j (by omega) h2 (by omega)]
  have hts6 : TStateAt st6.data.dmem (tA m0) a s5 := by rw [hd6]; exact hts5
  have hw104 := hk.word (by omega) (by omega) (by omega) hI.w104
  have l104 : env6.load 0 104 8 = pA m0 + BitVec.ofNat 64 (512 + 6064 * w.glued.size) :=
    load_ofMachine (r := 0) (o := 104) rfl (by rw [← hd6]; exact hw104)
  simp only [PcOk, cMore_eval env6 hi hn10 h135 l104] at hpc6
  have hgs : weightAt (reg m0 .r8).toNat b w tail (i + 1) =
      gStep P (weightAt (reg m0 .r8).toNat b w tail i) w.glued[i] := weightAt_succ _ _ _ _ hi
  have hgc := gStep_c P (weightAt (reg m0 .r8).toNat b w tail i) w.glued[i]
  have hr15 : reg st6.data .r15 = (weightAt (reg m0 .r8).toNat b w tail (i + 1)).c0.toBitVec := by
    refine (hm6.regs .r15 _ hr156).trans ?_
    rw [hgs, hgc.1]
    show BinOp.apply .xor .W64 (reg st5.data .r15) (reg st5.data .rax) = _
    simp only [BinOp.apply, low_W64, ext_W64]
    rw [hreg5 .r15 (by simp), hI.gb.r15, hax5, UInt64.toBitVec_xor, BitVec.xor_comm]
  have hrbp : reg st6.data .rbp = (weightAt (reg m0 .r8).toNat b w tail (i + 1)).c1.toBitVec := by
    refine (hm6.regs .rbp _ hrbp6).trans ?_
    rw [hgs, hgc.2]
    show BinOp.apply .xor .W64 (reg st5.data .rbp) (reg st5.data .rdx) = _
    simp only [BinOp.apply, low_W64, ext_W64]
    rw [hreg5 .rbp (by simp), hI.gb.rbp, hdx5, UInt64.toBitVec_xor, BitVec.xor_comm]
  have hr14 : reg st6.data .r14 = reg st.data .r14 :=
    (hm6.regs .r14 _ (hkr6 .r14 (by simp))).trans (hreg5 .r14 (by simp))
  have hgb : GB a level m0 folded tail claim (weightAt (reg m0 .r8).toNat b w tail (i + 1)) s5
      st6.data :=
    ⟨hI.gb.core.keep hf6 hr14 (fun j hj ↦ hk j (by omega) (by omega) (by omega)) hfo,
      hk.word (by omega) (by omega) (by omega) hI.gb.w88,
      hk.word (by omega) (by omega) (by omega) hI.gb.w96,
      hk.ews (by omega) (by rw [Array.length_toList]; omega) (by rw [Array.length_toList]; omega)
        hI.gb.tail, hts6, hr15, hrbp⟩
  by_cases hl : i + 1 < w.glued.size
  · rw [decide_eq_true hl] at hpc6
    simp only [ite_true] at hpc6
    refine .done _ (Or.inl ⟨hl, hpc6.trans (label_of_infix hp b29_in_code rfl), hgb, hl, ?_,
      hk.word (by omega) (by omega) (by omega) hI.w104,
      hk.word (by omega) (by omega) (by omega) hI.w56,
      hk.word (by omega) (by omega) (by omega) hI.w48,
      hk.ews (xs := (w.alphas ++ tail).toList) (by omega) (by omega) (by omega) hI.pts⟩)
    refine (hm6.regs .r13 _ hr136).trans ?_
    show BinOp.apply .add .W64 (BitVec.ofNat 64 6064) (reg st5.data .r13) = _
    simp only [BinOp.apply, low_W64, ext_W64]
    rw [h135, hgp, BitVec.add_comm, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 512 + 6064 * i + 6064 = 512 + 6064 * (i + 1) by omega]
  · rw [decide_eq_false hl] at hpc6
    simp only [Bool.false_eq_true, ite_false] at hpc6
    exact .done _ (Or.inr ⟨by omega, hpc6, hgb⟩)

end

end NativeRustcVmX64.Whir.Levels.FL
