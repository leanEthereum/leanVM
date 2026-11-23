module

public import NativeRustcVmArm.Code.Vm.GkrLayers.Names
public import NativeRustcVmArm.Code.Vm.GkrStep.Names
public import NativeRustcVmArm.Bus.GkrLayers.Exec
public import NativeRustcVmArm.Bus.GkrCommon
public import NativeRustcVmArm.Bus.GkrModel

/-!
# `gkr_layers`

`b0` saves X30, X22 to X19 in the 48-byte frame, keeps the `TState` in X20, the `GkrStateW` in
X19, the levels left `n` in X21 (`n - 1` in X22). One level left (`.LGkrLayers_1`, `Mid 1`): the
last step (`gkr_step(t, 1, true, s)`), then none left. At `.LGkrLayers_3` (`Head n`, `n ≠ 1`): none
left, the exit with `1`; `n` odd, a step of one level (`b9`), `n - 1` left; `n` even, a step of two
(`b6`, `last` when none are left after it), `n - 2` left at `.LGkrLayers_2` (`Mid`). A failed step
leaves with `0` (`.LGkrLayers_8`). `gkrLayers_spec`.
-/

namespace NativeRustcVmArm.Bus.GkrLayers

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.GkrLayers
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVmArm.Bus.Gkr
open NativeRustcVmArm.Sumcheck (Ctx At)

public section

/-- The frame's saved registers. -/
abbrev slots : List (Nat × XReg) := [(0, .X30), (16, .X22), (24, .X21), (32, .X20), (40, .X19)]

/-- The callee-saved registers it does not save. -/
abbrev keep : List XReg := [.X23, .X24, .X25, .X26, .X27, .X28, .X29]

theorem keep_callee : ∀ r ∈ keep, calleeSaved r = true := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 48 := by decide

/-- The outputs: the `TState` (X0) and the `GkrStateW` (X2). -/
@[expose] def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange m0.regs.X0.toBitVec tstateBytes q ∨ InRange m0.regs.X2.toBitVec gkrStateBytes q

/-- **In the loop**, `n` levels left: the frame, the `TState` and the `GkrStateW` where the
walk is. -/
structure Mid [Labels] (a : DecArea) (s0 : TState) (g0 : GkrStateW) (m0 : MachineData) (n : Nat)
    (m : MachineData) : Prop where
  fr : Fr m0 48 gkrLayersStack slots keep (outs m0) m
  x19 : m.regs.getXReg .X19 = m0.regs.X2
  x20 : m.regs.getXReg .X20 = m0.regs.X0
  x21 : (m.regs.getXReg .X21).toNat = n
  st : ∃ g s, (gkrLayers m0.regs.X1.toNat g0).run s0 = (gkrLayers n g).run s ∧
    TStateAt m.dmem m0.regs.X0.toBitVec a s ∧ GkrStateWAt m.dmem m0.regs.X2.toBitVec g ∧
    g.point.size + n ≤ busPointCap

/-- **At `.LGkrLayers_3`**: not one level left, `n - 1` in X22. -/
structure Head [Labels] (a : DecArea) (s0 : TState) (g0 : GkrStateW) (m0 : MachineData) (n : Nat)
    (m : MachineData) : Prop extends Mid a s0 g0 m0 n m where
  ne1 : n ≠ 1
  x22 : 1 ≤ n → (m.regs.getXReg .X22).toNat = n - 1

/-- `cmp x, #v` equal: the word is `v`. -/
theorem cmp_eq_lit (x : UInt64) (v : Nat) (hv : v < 2 ^ 64) :
    CmpOp.eq.apply .W64 x.toBitVec (BitVec.ofNat 64 v) = decide (x.toNat = v) := by
  simp only [CmpOp.apply, low_W64]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hv]
  rfl

/-- `x - v` of a word at least `v`. -/
theorem sub_lit_toNat (x : UInt64) (v : Nat) (h : v ≤ x.toNat) :
    (BinOp.apply .sub .W64 x.toBitVec (BitVec.ofNat 64 v)).toNat = x.toNat - v := by
  have hx := x.toBitVec.isLt
  have hx' : x.toBitVec.toNat = x.toNat := rfl
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [hx', Nat.mod_eq_of_lt (show v < 2 ^ 64 by rw [← hx'] at h; omega)]
  omega

theorem N_eq [Labels] : gkrLayersStack = 48 + gkrStepStack := rfl

theorem N_ge [Labels] : 48 ≤ gkrLayersStack := by rw [N_eq]; omega

end

public section
variable [Host] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData} {k : Nat}

/-- What `gkr_layers` reaches. -/
abbrev Goal (a : DecArea) (s0 : TState) (g0 : GkrStateW) (m0 : MachineData) (st : MachineState) :
    Prop :=
  st.pc = retOf m0 ∧ GkrLayersPost a s0 g0 m0 st.data

/-- The entry's context. -/
theorem ctx (h : GkrLayersPre a s0 g0 m0) : Ctx m0 m0.regs.X0.toBitVec a gkrLayersStack 48 :=
  ctx_of h.1 h.2.1 h.2.2.1 h.2.2.2.1 N_ge rfl

theorem outs_not_rc (h : GkrLayersPre a s0 g0 m0) :
    ∀ q, outs m0 q → ¬InRange rcAddr 192 q := fun _ hq ↦
  hq.elim (fun hq ↦ (ctx h).not_rc_tstate hq) fun hq ↦ out_not_rc (ctx h) h.2.2.2.2.2.1 hq

theorem outs_not_frame (h : GkrLayersPre a s0 g0 m0) :
    ∀ q, outs m0 q → ¬InRange (base m0 48) 48 q := fun _ hq ↦
  hq.elim (fun hq ↦ tstate_not_frame (ctx h) hq) fun hq ↦ out_not_frame (ctx h) h.2.2.2.2.2.1 hq

/-- **An exit** (`b13`, `b14`): the registers restored, X0 the literal, `ret`. -/
theorem exit_gen (h : GkrLayersPre a s0 g0 m0) {m : MachineData}
    (hfr : Fr m0 48 gkrLayersStack slots keep (outs m0) m) {ds : List Directive} {j v : Nat}
    {S' : SState} (hk : ds.IsInfixAt Host.prog j) (hx : exec ds headS = some (S', .ret))
    (hmem : S'.mem = []) (hok : exitOk S' 48 slots keep = true) (h0 : S'.reg .X0 = some (.lit v))
    (hpost : ∀ m' : MachineData, m'.dmem = m.dmem → m'.regs.X0.toBitVec = BitVec.ofNat 64 v →
      m'.regs.X0 = okWord ((gkrLayers m0.regs.X1.toNat g0).run s0).isSome ∧
      ∀ g' s', (gkrLayers m0.regs.X1.toNat g0).run s0 = some (g', s') →
        TStateAt m'.dmem m0.regs.X0.toBitVec a s' ∧ GkrStateWAt m'.dmem m0.regs.X2.toBitVec g') :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf j⟩ := by
  have hS := h.1
  have hwf := Bus.wf_frame hS N_ge hfr.kept
  have hm := Bus.match_frame hS N_ge rfl hfr.sp
  refine exec_then hk hx hwf hm fun st hm' hpc ↦ ?_
  obtain ⟨hret, hsv⟩ := hfr.exit hm' hwf hok
  have hd : st.data.dmem = m.dmem := hm'.dmem_eq hwf hmem
  obtain ⟨hx0, hrest⟩ := hpost st.data hd (hm'.regs .X0 _ h0)
  refine .done _ ⟨by simp only [PcOk] at hpc; rw [hpc, hret], hx0, hrest, ?_, hsv⟩
  rw [hd]
  exact NativeRustcVm.SameOutside.mono hfr.same fun q hq ↦ by
    rcases hq with hq | hq | hq
    · exact .inr (.inr hq)
    · exact .inl hq
    · exact .inr (.inl hq)

/-- **A failed step** (`.LGkrLayers_8`): X0 = `0`. -/
theorem fail_spec (hp : Placed code k) (h : GkrLayersPre a s0 g0 m0) {m : MachineData}
    (hfr : Fr m0 48 gkrLayersStack slots keep (outs m0) m)
    (hr : (gkrLayers m0.regs.X1.toNat g0).run s0 = none) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrLayers.b13Offset)⟩ :=
  exit_gen h hfr (b13_in_code.trans hp.1 (by simp [b13])) run_b13 rfl (by decide) rfl
    fun m' _ hx0 ↦ ⟨by rw [hr]; exact UInt64.toBitVec_inj.mp hx0, fun g' s' he ↦ by
      rw [hr] at he; cases he⟩

/-- **None left** (`.LGkrLayers_9`): X0 = `1`. -/
theorem ok_spec (hp : Placed code k) (h : GkrLayersPre a s0 g0 m0) {m : MachineData}
    (hi : Mid a s0 g0 m0 0 m) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrLayers.b14Offset)⟩ := by
  obtain ⟨g, s, hrun, hts, hgs, -⟩ := hi.st
  rw [gkrLayers_zero] at hrun
  exact exit_gen h hi.fr (b14_in_code.trans hp.1 (by simp [b14])) run_b14 rfl (by decide) rfl
    fun m' hd hx0 ↦ ⟨by rw [hrun]; exact UInt64.toBitVec_inj.mp hx0, fun g' s' he ↦ by
      rw [hrun] at he
      cases he
      rw [hd]
      exact ⟨hts, hgs⟩⟩

/-- **A call to `gkr_step`** from the frame. -/
theorem step_call (h : GkrLayersPre a s0 g0 m0)
    (hstep : ∀ s g, Spec (Labels.label NativeRustcVmArm.Vm.GkrStep.entryLabel) (GkrStepPre a s g) (GkrStepPost a s g))
    {st : MachineState} {next : Int64} {R : MachineState → Prop} {g : GkrStateW} {s : TState}
    (hfr : Fr m0 48 gkrLayersStack slots keep (outs m0) st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.GkrStep.entryLabel ∧ retOf st.data = next)
    (h0 : st.data.regs.X0 = m0.regs.X0) (h3 : st.data.regs.X3 = m0.regs.X2)
    (h1 : st.data.regs.X1.toNat = 1 ∨ st.data.regs.X1.toNat = 2) (h2 : st.data.regs.X2.toNat ≤ 1)
    (hsz : g.point.size + st.data.regs.X1.toNat ≤ busPointCap)
    (hts : TStateAt st.data.dmem m0.regs.X0.toBitVec a s)
    (hgs : GkrStateWAt st.data.dmem m0.regs.X2.toBitVec g)
    (cont : ∀ m2, Fr m0 48 gkrLayersStack slots keep (outs m0) m2 →
      GkrStepPost a s g st.data m2 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have c := ctx h
  have hat := Fr.at_ c hfr (outs_not_rc h)
  have hle : 48 + gkrStepStack ≤ gkrLayersStack := le_of_eq N_eq.symm
  refine Fr.callSpec hfr c.spN hle keep_callee slots_le (outs_not_frame h) (hstep s g) hpc ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ ?_, hq.2.2.2⟩) cont
  · refine ⟨hfr.stackOk h.1 rfl hle, c.rcAt hat hle, ?_, ?_, h1, h2, hsz, ?_, ?_⟩
    · rw [h0]; exact hts
    · rw [h0]; exact c.tstateOk hat hle
    · rw [h0, h3]; exact c.outOk_sub hat hle h.2.2.2.2.2.1
    · rw [h3]; exact hgs
  · rw [h0, h3] at hq'
    rcases hq' with hq' | hq' | hq'
    · exact .inr (.inl hq')
    · exact .inr (.inr hq')
    · exact .inl hq'

/-- `Mid` after a block that kept X19 to X21 and the memory. -/
theorem Mid.keep {n : Nat} {m m' : MachineData} (hi : Mid a s0 g0 m0 n m)
    (hfr : Fr m0 48 gkrLayersStack slots keep (outs m0) m') (hd : m'.dmem = m.dmem)
    (e19 : m'.regs.getXReg .X19 = m.regs.getXReg .X19)
    (e20 : m'.regs.getXReg .X20 = m.regs.getXReg .X20)
    (e21 : (m'.regs.getXReg .X21).toNat = n) : Mid a s0 g0 m0 n m' := by
  obtain ⟨g, s, h1, h2, h3, h4⟩ := hi.st
  exact ⟨hfr, e19.trans hi.x19, e20.trans hi.x20, e21, g, s, h1, by rw [hd]; exact h2,
    by rw [hd]; exact h3, h4⟩

omit [Host] in
/-- Bit `0` of a word's low half: the word is odd. -/
theorem odd_bit (q : UInt64) :
    (low .W32 q.toBitVec).getLsbD 0 = decide (q.toNat % 2 = 1) := by
  rw [NativeRustcVmArm.Sumcheck.getLsbD_low_zero]
  have e : q % 2 = 0 ↔ q.toNat % 2 = 0 := by
    constructor
    · intro h; have := congrArg UInt64.toNat h; simpa [UInt64.toNat_mod] using this
    · intro h; apply UInt64.toNat_inj.mp; simpa [UInt64.toNat_mod] using h
  by_cases h1 : q.toNat % 2 = 1
  · have : q % 2 ≠ 0 := fun e' ↦ by have := e.mp e'; omega
    simp [this, h1]
  · have : q % 2 = 0 := e.mpr (by omega)
    simp [this, h1]

/-- **At `.LGkrLayers_2`** (`b3`): one level left, to `.LGkrLayers_1`; else to `.LGkrLayers_3`. -/
theorem mid_spec (hp : Placed code k) (h : GkrLayersPre a s0 g0 m0) {n : Nat} {m : MachineData}
    (hi : Mid a s0 g0 m0 n m) :
    Eventually (step1 Host.exe) (fun st ↦
      (n = 1 ∧ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.GkrLayers.b1Offset) ∧ Mid a s0 g0 m0 1 st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.GkrLayers.b4Offset) ∧ Head a s0 g0 m0 n st.data)) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrLayers.b3Offset)⟩ := by
  refine Fr.runBlock h.1 N_ge rfl hi.fr (b3_in_code.trans hp.1 (by simp [b3])) run_b3 rfl rfl
    (by decide) (by decide) fun st hfr hd hm hpc ↦ ?_
  have e19 : st.data.regs.getXReg .X19 = m.regs.getXReg .X19 := reg_of hm rfl
  have e20 : st.data.regs.getXReg .X20 = m.regs.getXReg .X20 := reg_of hm rfl
  have e21 : st.data.regs.getXReg .X21 = m.regs.getXReg .X21 := reg_of hm rfl
  have e22 := hm.regs .X22 _ rfl
  have mid := hi.keep hfr hd e19 e20 (e21 ▸ hi.x21)
  have hc : SBool.eval (Env.ofMachine m [(base m0 48, 48)]) (.cmp .eq .W64 (.reg .X21) (.lit 1)) =
      decide (n = 1) := by
    show CmpOp.eq.apply .W64 (m.regs.getXReg .X21).toBitVec (BitVec.ofNat 64 1) = _
    rw [cmp_eq_lit _ _ (by decide), hi.x21]
  simp only [PcOk, hc] at hpc
  by_cases hn : n = 1
  · subst hn
    refine .done _ (.inl ⟨rfl, ?_, mid⟩)
    rw [hpc]
    simp only [decide_true, ↓reduceIte]
    exact hp.label (j := NativeRustcVmArm.Vm.GkrLayers.b1Offset) NativeRustcVmArm.Vm.GkrLayers.label_1_at
  · refine .done _ (.inr ⟨?_, { toMid := mid, ne1 := hn, x22 := fun h1 ↦ ?_ }⟩)
    · rw [hpc]
      simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte]
      rfl
    · rw [UInt64.toNat, e22]
      have := sub_lit_toNat (m.regs.getXReg .X21) 1 (by rw [hi.x21]; exact h1)
      rw [hi.x21] at this
      exact this

/-- **None left at `.LGkrLayers_3`**: to `.LGkrLayers_9`, X0 = `1`. -/
theorem head0_spec (hp : Placed code k) (h : GkrLayersPre a s0 g0 m0) {m : MachineData}
    (hi : Mid a s0 g0 m0 0 m) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrLayers.b4Offset)⟩ := by
  refine Fr.runBlock h.1 N_ge rfl hi.fr (b4_in_code.trans hp.1 (by simp [b4])) run_b4 rfl rfl
    (by decide) (by decide) fun st hfr hd hm hpc ↦ ?_
  have mid := hi.keep hfr hd (reg_of hm rfl) (reg_of hm rfl)
    ((reg_of hm (r := .X21) rfl) ▸ hi.x21)
  have hc : SBool.eval (Env.ofMachine m [(base m0 48, 48)]) (.cmp .eq .W64 (.reg .X21) (.lit 0)) =
      true := by
    show CmpOp.eq.apply .W64 (m.regs.getXReg .X21).toBitVec (BitVec.ofNat 64 0) = _
    rw [cmp_eq_lit _ _ (by decide), hi.x21]
    rfl
  simp only [PcOk, hc, ↓reduceIte] at hpc
  exact at_pc (hpc.trans (hp.label (j := NativeRustcVmArm.Vm.GkrLayers.b14Offset) NativeRustcVmArm.Vm.GkrLayers.label_9_at)) (ok_spec hp h mid)

/-- **One level left** (`.LGkrLayers_1`): the last step, then none left. -/
theorem one_spec (hp : Placed code k) (h : GkrLayersPre a s0 g0 m0)
    (hstep : ∀ s g, Spec (Labels.label NativeRustcVmArm.Vm.GkrStep.entryLabel) (GkrStepPre a s g) (GkrStepPost a s g))
    {m : MachineData} (hi : Mid a s0 g0 m0 1 m) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrLayers.b1Offset)⟩ := by
  obtain ⟨g, s, hrun, hts, hgs, hsz⟩ := hi.st
  refine Fr.runBlock h.1 N_ge rfl hi.fr (b1_in_code.trans hp.1 (by simp [b1])) run_b1 rfl rfl
    (by decide) (by decide) fun st hfr hd hm hpc ↦ ?_
  have e1 : st.data.regs.X1.toNat = 1 := by
    show (st.data.regs.getXReg .X1).toBitVec.toNat = 1
    rw [reg_lit hm (r := .X1) (n := 1) rfl]; rfl
  have e2 : st.data.regs.X2.toNat = 1 := by
    show (st.data.regs.getXReg .X2).toBitVec.toNat = 1
    rw [reg_lit hm (r := .X2) (n := 1) rfl]; rfl
  have e19 : st.data.regs.getXReg .X19 = m.regs.getXReg .X19 := reg_of hm rfl
  have e20 : st.data.regs.getXReg .X20 = m.regs.getXReg .X20 := reg_of hm rfl
  have e0 : st.data.regs.X0 = m0.regs.X0 := (reg_of hm (r := .X0) (r' := .X20) rfl).trans hi.x20
  have e3 : st.data.regs.X3 = m0.regs.X2 := (reg_of hm (r := .X3) (r' := .X19) rfl).trans hi.x19
  refine step_call h hstep hfr hpc e0 e3 (.inl e1) (by omega)
    (by rw [e1]; omega) (by rw [hd]; exact hts) (by rw [hd]; exact hgs) fun m2 hfr2 hq hcs ↦ ?_
  have hlast : decide (st.data.regs.X2.toNat = 1) = true := by rw [e2]; rfl
  obtain ⟨hx0, hok, -, -⟩ := hq
  rw [e1, hlast] at hx0 hok
  have hr : (gkrLayers m0.regs.X1.toNat g0).run s0 = (gkrStep 1 true g).run s := by
    rw [hrun, gkrLayers_one]
  refine Fr.runBlock h.1 N_ge rfl hfr2 (b2_in_code.trans hp.1 (by simp [b2])) run_b2 rfl rfl
    (by decide) (by decide) fun st3 hfr3 hd3 hm3 hpc3 ↦ ?_
  have hc : SBool.eval (Env.ofMachine m2 [(base m0 48, 48)]) (.not (.bit .W32 (.reg .X0) 0)) =
      !((gkrStep 1 true g).run s).isSome := by
    show (!(low .W32 (m2.regs.getXReg .X0).toBitVec).getLsbD 0) = _
    rw [show m2.regs.getXReg .X0 = m2.regs.X0 from rfl, hx0, okWord_bit]
  simp only [PcOk, hc] at hpc3
  cases hrs : (gkrStep 1 true g).run s with
  | none =>
    simp only [hrs, Option.isSome_none, Bool.not_false, ↓reduceIte] at hpc3
    exact at_pc (hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.GkrLayers.b13Offset) NativeRustcVmArm.Vm.GkrLayers.label_8_at)) (fail_spec hp h hfr3 (by rw [hr, hrs]))
  | some p =>
    obtain ⟨g', s'⟩ := p
    simp only [hrs, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc3
    obtain ⟨hts', hgs'⟩ := hok g' s' hrs
    rw [e0] at hts'
    rw [e3] at hgs'
    have h21 : (st3.data.regs.getXReg .X21).toNat = 0 := by
      show (st3.data.regs.getXReg .X21).toBitVec.toNat = 0
      rw [reg_lit hm3 (r := .X21) (n := 0) rfl]; rfl
    have hmid : Mid a s0 g0 m0 0 st3.data := by
      refine ⟨hfr3, ?_, ?_, h21, g', s', by rw [hr, hrs]; rfl, by rw [hd3]; exact hts',
        by rw [hd3]; exact hgs', ?_⟩
      · rw [reg_of hm3 rfl, hcs .X19 rfl, e19]; exact hi.x19
      · rw [reg_of hm3 rfl, hcs .X20 rfl, e20]; exact hi.x20
      · have := (gkrStep_size (by omega) hrs).1
        omega
    refine at_pc hpc3 (Eventually.bind (mid_spec hp h hmid) fun st4 h4 ↦ ?_)
    rcases h4 with ⟨h01, -⟩ | ⟨hpc4, hh⟩
    · cases h01
    · exact at_pc hpc4 (head0_spec hp h hh.toMid)

/-- **The loop** from `.LGkrLayers_3`, `n` levels left. -/
theorem head_spec (hp : Placed code k) (h : GkrLayersPre a s0 g0 m0)
    (hstep : ∀ s g, Spec (Labels.label NativeRustcVmArm.Vm.GkrStep.entryLabel) (GkrStepPre a s g) (GkrStepPost a s g)) :
    ∀ (n : Nat) {m : MachineData}, Head a s0 g0 m0 n m →
      Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrLayers.b4Offset)⟩ := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro m hi
  by_cases hn0 : n = 0
  · subst hn0; exact head0_spec hp h hi.toMid
  obtain ⟨g, s, hrun, hts, hgs, hsz⟩ := hi.st
  -- `b4`: not none left.
  refine Fr.runBlock h.1 N_ge rfl hi.fr (b4_in_code.trans hp.1 (by simp [b4])) run_b4 rfl rfl
    (by decide) (by decide) fun st hfr hd hm hpc ↦ ?_
  have hc : SBool.eval (Env.ofMachine m [(base m0 48, 48)]) (.cmp .eq .W64 (.reg .X21) (.lit 0)) =
      false := by
    show CmpOp.eq.apply .W64 (m.regs.getXReg .X21).toBitVec (BitVec.ofNat 64 0) = _
    rw [cmp_eq_lit _ _ (by decide), hi.x21]
    simp [hn0]
  simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc
  have e19 : st.data.regs.getXReg .X19 = m.regs.getXReg .X19 := reg_of hm rfl
  have e20 : st.data.regs.getXReg .X20 = m.regs.getXReg .X20 := reg_of hm rfl
  have e21 : st.data.regs.getXReg .X21 = m.regs.getXReg .X21 := reg_of hm rfl
  have e22 : st.data.regs.getXReg .X22 = m.regs.getXReg .X22 := reg_of hm rfl
  -- `b5`: the parity.
  refine at_pc hpc (Fr.runBlock h.1 N_ge rfl hfr (b5_in_code.trans hp.1 (by simp [b5])) run_b5
    rfl rfl (by decide) (by decide) fun st5 hfr5 hd5 hm5 hpc5 ↦ ?_)
  have f19 : st5.data.regs.getXReg .X19 = m0.regs.X2 := by
    rw [reg_of hm5 rfl, e19]; exact hi.x19
  have f20 : st5.data.regs.getXReg .X20 = m0.regs.X0 := by
    rw [reg_of hm5 rfl, e20]; exact hi.x20
  have f21 : (st5.data.regs.getXReg .X21).toNat = n := by
    rw [reg_of hm5 rfl, e21]; exact hi.x21
  have f22 : st5.data.regs.getXReg .X22 = m.regs.getXReg .X22 := by
    rw [reg_of hm5 rfl, e22]
  have hd5' : st5.data.dmem = m.dmem := hd5.trans hd
  have hc5 : SBool.eval (Env.ofMachine st.data [(base m0 48, 48)]) (.bit .W32 (.reg .X21) 0) =
      decide (n % 2 = 1) := by
    show (low .W32 (st.data.regs.getXReg .X21).toBitVec).getLsbD 0 = _
    rw [odd_bit, e21, hi.x21]
  simp only [PcOk, hc5] at hpc5
  by_cases hodd : n % 2 = 1
  · -- `n` odd, at least `3`: a step of one level (`b9`).
    have h3 : 3 ≤ n := by have := hi.ne1; omega
    simp only [hodd, decide_true, ↓reduceIte] at hpc5
    refine at_pc (hpc5.trans (hp.label (j := NativeRustcVmArm.Vm.GkrLayers.b9Offset) NativeRustcVmArm.Vm.GkrLayers.label_6_at)) (Fr.runBlock h.1 N_ge rfl hfr5
      (b9_in_code.trans hp.1 (by simp [b9])) run_b9 rfl rfl (by decide) (by decide)
      fun st9 hfr9 hd9 hm9 hpc9 ↦ ?_)
    have e1 : st9.data.regs.X1.toNat = 1 := by
      show (st9.data.regs.getXReg .X1).toBitVec.toNat = 1
      rw [reg_lit hm9 (r := .X1) (n := 1) rfl]; rfl
    have e2 : st9.data.regs.X2.toNat = 0 := by
      show (st9.data.regs.getXReg .X2).toBitVec.toNat = 0
      rw [reg_lit hm9 (r := .X2) (n := 0) rfl]; rfl
    have e0 : st9.data.regs.X0 = m0.regs.X0 := (reg_of hm9 (r := .X0) (r' := .X20) rfl).trans f20
    have e3 : st9.data.regs.X3 = m0.regs.X2 := (reg_of hm9 (r := .X3) (r' := .X19) rfl).trans f19
    have g19 : st9.data.regs.getXReg .X19 = m0.regs.X2 := (reg_of hm9 rfl).trans f19
    have g20 : st9.data.regs.getXReg .X20 = m0.regs.X0 := (reg_of hm9 rfl).trans f20
    have g22 : st9.data.regs.getXReg .X22 = m.regs.getXReg .X22 := (reg_of hm9 rfl).trans f22
    refine step_call (g := g) (s := s) h hstep hfr9 hpc9 e0 e3 (.inl e1) (by omega) (by rw [e1]; omega)
      (by rw [hd9, hd5']; exact hts) (by rw [hd9, hd5']; exact hgs) fun m2 hfr2 hq hcs ↦ ?_
    have hlast : decide (st9.data.regs.X2.toNat = 1) = false := by rw [e2]; rfl
    obtain ⟨hx0, hok, -, -⟩ := hq
    rw [e1, hlast] at hx0 hok
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    have hr : (gkrLayers m0.regs.X1.toNat g0).run s0 =
        ((gkrStep 1 false g).run s).bind fun p ↦ (gkrLayers (n' + 1) p.1).run p.2 := by
      rw [hrun, gkrLayers_odd (by omega)]
    -- `b10`: the step's result.
    refine Fr.runBlock h.1 N_ge rfl hfr2 (b10_in_code.trans hp.1 (by simp [b10])) run_b10 rfl rfl
      (by decide) (by decide) fun st10 hfr10 hd10 hm10 hpc10 ↦ ?_
    have hc10 : SBool.eval (Env.ofMachine m2 [(base m0 48, 48)]) (.not (.bit .W32 (.reg .X0) 0)) =
        !((gkrStep 1 false g).run s).isSome := by
      show (!(low .W32 (m2.regs.getXReg .X0).toBitVec).getLsbD 0) = _
      rw [show m2.regs.getXReg .X0 = m2.regs.X0 from rfl, hx0, okWord_bit]
    simp only [PcOk, hc10] at hpc10
    cases hrs : (gkrStep 1 false g).run s with
    | none =>
      simp only [hrs, Option.isSome_none, Bool.not_false, ↓reduceIte] at hpc10
      exact at_pc (hpc10.trans (hp.label (j := NativeRustcVmArm.Vm.GkrLayers.b13Offset) NativeRustcVmArm.Vm.GkrLayers.label_8_at)) (fail_spec hp h hfr10 (by rw [hr, hrs]; rfl))
    | some p =>
      obtain ⟨g', s'⟩ := p
      simp only [hrs, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc10
      obtain ⟨hts', hgs'⟩ := hok g' s' hrs
      rw [e0] at hts'
      rw [e3] at hgs'
      have k19 : st10.data.regs.getXReg .X19 = m0.regs.X2 := by
        rw [reg_of hm10 rfl, hcs .X19 rfl]; exact g19
      have k20 : st10.data.regs.getXReg .X20 = m0.regs.X0 := by
        rw [reg_of hm10 rfl, hcs .X20 rfl]; exact g20
      have k22 : (st10.data.regs.getXReg .X22).toNat = n' + 1 := by
        rw [reg_of hm10 rfl, hcs .X22 rfl, g22]
        have := hi.x22 (by omega)
        omega
      -- `b11`: `n - 1` left, back to `.LGkrLayers_3`.
      refine at_pc hpc10 (Fr.runBlock h.1 N_ge rfl hfr10 (b11_in_code.trans hp.1 (by simp [b11]))
        run_b11 rfl rfl (by decide) (by decide) fun st11 hfr11 hd11 hm11 hpc11 ↦ ?_)
      have hc11 : SBool.eval (Env.ofMachine st10.data [(base m0 48, 48)])
          (.not (.cmp .eq .W64 (.reg .X22) (.lit 1))) = true := by
        show (!CmpOp.eq.apply .W64 (st10.data.regs.getXReg .X22).toBitVec (BitVec.ofNat 64 1)) = _
        rw [cmp_eq_lit _ _ (by decide), k22]
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
        omega
      simp only [PcOk, hc11, ↓reduceIte] at hpc11
      have l21 : (st11.data.regs.getXReg .X21).toNat = n' + 1 := by
        rw [reg_of hm11 (r := .X21) (r' := .X22) rfl]; exact k22
      have l22 := hm11.regs .X22 _ rfl
      have hsz' : g'.point.size + (n' + 1) ≤ busPointCap := by
        have := (gkrStep_size (by omega) hrs).1
        omega
      have hmid : Mid a s0 g0 m0 (n' + 1) st11.data :=
        ⟨hfr11, (reg_of hm11 (r := .X19) (r' := .X19) rfl).trans k19,
          (reg_of hm11 (r := .X20) (r' := .X20) rfl).trans k20, l21, g', s',
          by rw [hr, hrs]; rfl, by rw [hd11, hd10]; exact hts', by rw [hd11, hd10]; exact hgs', hsz'⟩
      have hhead : Head a s0 g0 m0 (n' + 1) st11.data := by
        refine { toMid := hmid, ne1 := by omega, x22 := fun _ ↦ ?_ }
        rw [UInt64.toNat, l22]
        have := sub_lit_toNat (st10.data.regs.getXReg .X22) 1 (by rw [k22]; omega)
        rw [k22] at this
        exact this
      exact at_pc (hpc11.trans (hp.label (j := NativeRustcVmArm.Vm.GkrLayers.b4Offset) NativeRustcVmArm.Vm.GkrLayers.label_3_at)) (ih (n' + 1) (by omega) hhead)
  · -- `n` even, at least `2`: a step of two levels (`b6`).
    have h2 : 2 ≤ n := by omega
    simp only [hodd, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc5
    refine at_pc hpc5 (Fr.runBlock h.1 N_ge rfl hfr5 (b6_in_code.trans hp.1 (by simp [b6])) run_b6
      rfl rfl (by decide) (by decide) fun st6 hfr6 hd6 hm6 hpc6 ↦ ?_)
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    have e1 : st6.data.regs.X1.toNat = 2 := by
      show (st6.data.regs.getXReg .X1).toBitVec.toNat = 2
      rw [reg_lit hm6 (r := .X1) (n := 2) rfl]; rfl
    have e2 : st6.data.regs.X2.toNat = if n' = 0 then 1 else 0 := by
      show (st6.data.regs.getXReg .X2).toBitVec.toNat = _
      rw [hm6.regs .X2 _ rfl]
      show (if (!CmpOp.eq.apply .W64 (st5.data.regs.getXReg .X21).toBitVec
          (BitVec.ofNat 64 2)) = true then BitVec.ofNat 64 0 else BitVec.ofNat 64 1).toNat = _
      rw [cmp_eq_lit _ _ (by decide), f21]
      by_cases h0 : n' = 0 <;> simp [h0]
    have e21 : (st6.data.regs.getXReg .X21).toNat = n' := by
      rw [UInt64.toNat, hm6.regs .X21 _ rfl]
      have := sub_lit_toNat (st5.data.regs.getXReg .X21) 2 (by rw [f21]; omega)
      rw [f21] at this
      exact this.trans (by omega)
    have e0 : st6.data.regs.X0 = m0.regs.X0 := (reg_of hm6 (r := .X0) (r' := .X20) rfl).trans f20
    have e3 : st6.data.regs.X3 = m0.regs.X2 := (reg_of hm6 (r := .X3) (r' := .X19) rfl).trans f19
    have g19 : st6.data.regs.getXReg .X19 = m0.regs.X2 := (reg_of hm6 rfl).trans f19
    have g20 : st6.data.regs.getXReg .X20 = m0.regs.X0 := (reg_of hm6 rfl).trans f20
    refine step_call (g := g) (s := s) h hstep hfr6 hpc6 e0 e3 (.inr e1) (by rw [e2]; split <;> omega)
      (by rw [e1]; omega) (by rw [hd6, hd5']; exact hts) (by rw [hd6, hd5']; exact hgs)
      fun m2 hfr2 hq hcs ↦ ?_
    have hlast : decide (st6.data.regs.X2.toNat = 1) = decide (n' = 0) := by
      rw [e2]; by_cases h0 : n' = 0 <;> simp [h0]
    obtain ⟨hx0, hok, -, -⟩ := hq
    rw [e1, hlast] at hx0 hok
    have hr : (gkrLayers m0.regs.X1.toNat g0).run s0 =
        ((gkrStep 2 (decide (n' = 0)) g).run s).bind fun p ↦ (gkrLayers n' p.1).run p.2 := by
      rw [hrun, gkrLayers_even (by omega)]
    -- `b7`: the step's result.
    refine Fr.runBlock h.1 N_ge rfl hfr2 (b7_in_code.trans hp.1 (by simp [b7])) run_b7 rfl rfl
      (by decide) (by decide) fun st7 hfr7 hd7 hm7 hpc7 ↦ ?_
    have hc7 : SBool.eval (Env.ofMachine m2 [(base m0 48, 48)]) (.bit .W32 (.reg .X0) 0) =
        ((gkrStep 2 (decide (n' = 0)) g).run s).isSome := by
      show (low .W32 (m2.regs.getXReg .X0).toBitVec).getLsbD 0 = _
      rw [show m2.regs.getXReg .X0 = m2.regs.X0 from rfl, hx0, okWord_bit]
    simp only [PcOk, hc7] at hpc7
    cases hrs : (gkrStep 2 (decide (n' = 0)) g).run s with
    | none =>
      simp only [hrs, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc7
      -- `b8`: to `.LGkrLayers_8`.
      refine at_pc hpc7 (Fr.runBlock h.1 N_ge rfl hfr7 (b8_in_code.trans hp.1 (by simp [b8]))
        run_b8 rfl rfl (by decide) (by decide) fun st8 hfr8 _ _ hpc8 ↦ ?_)
      simp only [PcOk] at hpc8
      exact at_pc (hpc8.trans (hp.label (j := NativeRustcVmArm.Vm.GkrLayers.b13Offset) NativeRustcVmArm.Vm.GkrLayers.label_8_at)) (fail_spec hp h hfr8 (by rw [hr, hrs]; rfl))
    | some p =>
      obtain ⟨g', s'⟩ := p
      simp only [hrs, Option.isSome_some, ↓reduceIte] at hpc7
      obtain ⟨hts', hgs'⟩ := hok g' s' hrs
      rw [e0] at hts'
      rw [e3] at hgs'
      have hmid : Mid a s0 g0 m0 n' st7.data := by
        refine ⟨hfr7, ?_, ?_, ?_, g', s', by rw [hr, hrs]; rfl, by rw [hd7]; exact hts',
          by rw [hd7]; exact hgs', ?_⟩
        · rw [reg_of hm7 rfl, hcs .X19 rfl]; exact g19
        · rw [reg_of hm7 rfl, hcs .X20 rfl]; exact g20
        · rw [reg_of hm7 rfl, hcs .X21 rfl]; exact e21
        · have := (gkrStep_size (by omega) hrs).1
          omega
      refine at_pc (hpc7.trans (hp.label (j := NativeRustcVmArm.Vm.GkrLayers.b3Offset) NativeRustcVmArm.Vm.GkrLayers.label_2_at))
        (Eventually.bind (mid_spec hp h hmid) fun st4 h4 ↦ ?_)
      rcases h4 with ⟨h01, -⟩ | ⟨hpc4, hh⟩
      · omega
      · exact at_pc hpc4 (ih n' (by omega) hh)

/-- **`gkr_layers`'s contract.** -/
theorem gkrLayers_spec (hp : Placed code k)
    (hstep : ∀ s g, Spec (Labels.label NativeRustcVmArm.Vm.GkrStep.entryLabel) (GkrStepPre a s g) (GkrStepPost a s g)) :
    Spec (Labels.label NativeRustcVmArm.Vm.GkrLayers.entryLabel) (GkrLayersPre a s0 g0) (GkrLayersPost a s0 g0) := by
  intro m0 h
  have hS := h.1
  have hN : gkrLayersStack ≤ m0.regs.SP.toNat := hS.2.1
  have hwf := Bus.wf_env0 hS (F := 48) N_ge
  have hm : Match (Bus.env0 m0 48) entryS m0 := Bus.match_entry hS N_ge rfl
  rw [show Labels.label NativeRustcVmArm.Vm.GkrLayers.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.GkrLayers.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.GkrLayers.entryOffset) NativeRustcVmArm.Vm.GkrLayers.entry_at]
  refine exec_then (b0_in_code.trans hp.1 (by simp [b0])) run_b0 hwf hm fun st hm1 hpc ↦ ?_
  have hfr : Fr m0 48 gkrLayersStack slots keep (outs m0) st.data :=
    Fr.ofPrologue hN N_ge hm1 hwf rfl (by decide) slots_le (by decide) (by decide)
  have c := ctx h
  have hsame : NativeRustcVm.SameOutside m0.dmem st.data.dmem (InRange (base m0 48) 48) :=
    NativeRustcVm.SameOutside.mono (hm1.sameOutside hwf) fun q hq ↦
      Written.inRange (r := 0) rfl (Bus.frame_mapped hS N_ge).2 (by decide) hq
  have hts : TStateAt st.data.dmem m0.regs.X0.toBitVec a s0 :=
    h.2.2.1.frame (fun q hq ↦ hm1.kept hwf q hq) (fun q hq ↦ frame_not_tstate c hq) hsame
  have hgs : GkrStateWAt st.data.dmem m0.regs.X2.toBitVec g0 :=
    gkrStateWAt_keep h.2.2.2.2.2.2 hsame fun q hq ↦ frame_not_out c h.2.2.2.2.2.1 hq
  have hmid : Mid a s0 g0 m0 m0.regs.X1.toNat st.data :=
    ⟨hfr, reg_of hm1 (r' := .X2) rfl, reg_of hm1 (r' := .X0) rfl, by rw [reg_of hm1 (r := .X21) (r' := .X1) rfl]; rfl,
      g0, s0, rfl, hts, hgs, h.2.2.2.2.1⟩
  have hc : SBool.eval (Bus.env0 m0 48) (.not (.cmp .eq .W64 (.reg .X1) (.lit 1))) =
      !decide (m0.regs.X1.toNat = 1) := by
    show (!CmpOp.eq.apply .W64 (m0.regs.getXReg .X1).toBitVec (BitVec.ofNat 64 1)) = _
    rw [cmp_eq_lit _ _ (by decide)]
    rfl
  simp only [PcOk, hc] at hpc
  by_cases hn : m0.regs.X1.toNat = 1
  · simp only [hn, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc
    exact at_pc hpc (one_spec hp h hstep (hn ▸ hmid))
  · simp only [hn, decide_false, Bool.not_false, ↓reduceIte] at hpc
    refine at_pc (hpc.trans (hp.label (j := NativeRustcVmArm.Vm.GkrLayers.b4Offset) NativeRustcVmArm.Vm.GkrLayers.label_3_at)) (head_spec hp h hstep m0.regs.X1.toNat ?_)
    refine { toMid := hmid, ne1 := hn, x22 := fun h1 ↦ ?_ }
    rw [UInt64.toNat, hm1.regs .X22 _ rfl]
    exact sub_lit_toNat (m0.regs.getXReg .X1) 1 h1

end

end NativeRustcVmArm.Bus.GkrLayers
