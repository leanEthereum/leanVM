module

public import NativeRustcVmArm.Code.Vm.GkrLayers.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Code.Vm.VerifyGkrGrandProducts.Names
public import NativeRustcVmArm.Bus.VerifyGkr.Exec
public import NativeRustcVmArm.Bus.GkrCommon
public import NativeRustcVmArm.Bus.GkrModel

/-!
# `verify_gkr_grand_products`

`b0` saves X30, X25 to X19 in the 96-byte frame, keeps the output in X19, the `GkrStateW` in X20,
`depth` in X21, the `TState` in X22, and reads the shared root into the `Option<EW>` at SP + 8
(`b1`: none, to `.L5` with tag `0`). `b2` keeps the root in X23, X25 and reads the count root
(`b3`: none, to `.L4`, tag `0`). `b4` writes the state (`[shared, shared, count]`, an empty point)
and calls `gkr_layers` (`b5`: none, to `.L5` with tag `0`); `b6` writes the count at `out + 8`,
tag `1`. `.L5` (`b8`) writes the tag and returns. `verifyGkr_spec`.
-/

namespace NativeRustcVmArm.Bus.VerifyGkr

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyGkrGrandProducts
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVmArm.Bus.Gkr
open NativeRustcVmArm.Sumcheck (Ctx At)

public section

/-- The frame's saved registers. -/
abbrev slots : List (Nat × XReg) :=
  [(32, .X30), (40, .X25), (48, .X24), (56, .X23), (64, .X22), (72, .X21), (80, .X20), (88, .X19)]

/-- The callee-saved registers it does not save. -/
abbrev keep : List XReg := [.X26, .X27, .X28, .X29]

theorem keep_callee : ∀ r ∈ keep, calleeSaved r = true := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 96 := by decide

/-- The outputs: the `Option<EW>` (X0), the `TState` (X1), the `GkrStateW` (X3). -/
@[expose] def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange m0.regs.X0.toBitVec 24 q ∨ InRange m0.regs.X1.toBitVec tstateBytes q ∨
    InRange m0.regs.X3.toBitVec gkrStateBytes q

theorem N_ge : 96 ≤ verifyGkrStack := by unfold verifyGkrStack; omega

theorem le_rs : 96 + readScalarStack ≤ verifyGkrStack := by unfold verifyGkrStack; omega

theorem le_gl : 96 + gkrLayersStack ≤ verifyGkrStack := by unfold verifyGkrStack; omega

/-- Where a block's writes are: between offsets `lo` and `hi` of region `r`. -/
theorem written_in [Labels] {env : Env} {S : SState} {r : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) {lo hi : Nat}
    (hS : ∀ w ∈ S.mem, w.r = r ∧ lo ≤ w.off ∧ w.off + w.n ≤ hi) {q : BitVec 64}
    (h : Written env S q) : b.toNat + lo ≤ q.toNat ∧ q.toNat < b.toNat + hi := by
  obtain ⟨w, hw, b', sz', hb', h1, h2⟩ := h
  obtain ⟨hr, hlo, hhi⟩ := hS w hw
  rw [hr, hb] at hb'
  cases hb'
  omega

/-- `n ≤ 24` bytes of the output: of its 24. -/
theorem o_mono {o q : BitVec 64} {n : Nat} (hn : n ≤ 24) (hq : InRange o n q) : InRange o 24 q := by
  unfold InRange at *; omega

end

public section
variable [Host] {a : DecArea} {s0 : TState} {m0 : MachineData} {k : Nat}

/-- What `verify_gkr_grand_products` reaches. -/
abbrev Goal (a : DecArea) (s0 : TState) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ VerifyGkrPost a s0 m0 st.data

/-- The entry's context. -/
theorem ctx (h : VerifyGkrPre a s0 m0) : Ctx m0 m0.regs.X1.toBitVec a verifyGkrStack 96 :=
  ctx_of h.1 h.2.1 h.2.2.1 h.2.2.2.1 N_ge rfl

theorem outs_not_rc (h : VerifyGkrPre a s0 m0) : ∀ q, outs m0 q → ¬InRange rcAddr 192 q :=
  fun _ hq ↦ by
    rcases hq with hq | hq | hq
    · exact out_not_rc (ctx h) h.2.2.2.2.2.1 hq
    · exact (ctx h).not_rc_tstate hq
    · exact out_not_rc (ctx h) h.2.2.2.2.2.2.1 hq

theorem outs_not_frame (h : VerifyGkrPre a s0 m0) :
    ∀ q, outs m0 q → ¬InRange (base m0 96) 96 q := fun _ hq ↦ by
  rcases hq with hq | hq | hq
  · exact out_not_frame (ctx h) h.2.2.2.2.2.1 hq
  · exact tstate_not_frame (ctx h) hq
  · exact out_not_frame (ctx h) h.2.2.2.2.2.2.1 hq

/-- A byte of the output is neither the `TState`'s, its decoded area's nor the `GkrStateW`'s. -/
theorem o_apart (h : VerifyGkrPre a s0 m0) {q : BitVec 64} (hq : InRange m0.regs.X0.toBitVec 24 q) :
    (¬InRange m0.regs.X1.toBitVec tstateBytes q ∧ ¬InRange a.words (8 * a.len) q) ∧
      ¬InRange m0.regs.X3.toBitVec gkrStateBytes q := by
  have hoo := h.2.2.2.2.2.1
  have fp := h.2.2.1.footprint
  exact ⟨⟨NativeRustcVm.Apart.not_inRange hoo.2.2.1 hoo.2.1 fp.1.2 hq,
    NativeRustcVm.Apart.not_inRange hoo.2.2.2.1 hoo.2.1 fp.2.1.2 hq⟩,
    NativeRustcVm.Apart.not_inRange h.2.2.2.2.2.2.2 hoo.2.1 h.2.2.2.2.2.2.1.2.1 hq⟩

/-- A byte of the `GkrStateW` is neither the `TState`'s nor its decoded area's. -/
theorem p_apart (h : VerifyGkrPre a s0 m0) {q : BitVec 64}
    (hq : InRange m0.regs.X3.toBitVec gkrStateBytes q) :
    ¬InRange m0.regs.X1.toBitVec tstateBytes q ∧ ¬InRange a.words (8 * a.len) q := by
  have hgo := h.2.2.2.2.2.2.1
  have fp := h.2.2.1.footprint
  exact ⟨NativeRustcVm.Apart.not_inRange hgo.2.2.1 hgo.2.1 fp.1.2 hq,
    NativeRustcVm.Apart.not_inRange hgo.2.2.2.1 hgo.2.1 fp.2.1.2 hq⟩

/-- **The exit** (`.L5`, `b8`): the tag X8 at the output, the epilogue. -/
theorem exit_spec (hp : Placed code k) (h : VerifyGkrPre a s0 m0) {m : MachineData}
    (hfr : Fr m0 96 verifyGkrStack slots keep (outs m0) m)
    (h19 : m.regs.getXReg .X19 = m0.regs.X0)
    (hpost : ∀ d : DataMem, Kept m.dmem d →
      NativeRustcVm.SameOutside m.dmem d (InRange m0.regs.X0.toBitVec 8) →
      NativeRustcVm.WordAt d m0.regs.X0.toBitVec (m.regs.getXReg .X8) →
      OptEWAt d m0.regs.X0.toBitVec
          (((verifyGkrGrandProducts m0.regs.X2.toNat).run s0).map (·.1.1)) ∧
        (∀ c pt vs s', (verifyGkrGrandProducts m0.regs.X2.toNat).run s0 = some ((c, pt, vs), s') →
          TStateAt d m0.regs.X1.toBitVec a s' ∧ GkrStateWAt d m0.regs.X3.toBitVec ⟨vs, pt⟩)) :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyGkrGrandProducts.b8Offset)⟩ := by
  have hS := h.1
  have hoo := h.2.2.2.2.2.1
  have hwf : (Env.ofMachine m [(base m0 96, 96), (m0.regs.X0.toBitVec, 24)]).WF :=
    Bus.wf_frame2 hS N_ge hfr.kept ⟨hoo.1, hoo.2.1⟩ hoo.2.2.2.2.1
  have hm := match_frameW (n := 24) hS N_ge rfl hfr.sp (r := .X19) (by rw [h19])
  refine exec_then (b8_in_code.trans hp.1 (by simp [b8])) run_b8 hwf hm fun st hm' hpc ↦ ?_
  obtain ⟨hret, hsv⟩ := hfr.exit hm' hwf (by decide)
  have hnw : m0.regs.X0.toBitVec.toNat + 24 ≤ 2 ^ 64 := hoo.2.1
  have hs8 : NativeRustcVm.SameOutside m.dmem st.data.dmem (InRange m0.regs.X0.toBitVec 8) :=
    NativeRustcVm.SameOutside.mono (hm'.sameOutside hwf) fun q hq ↦ by
      have := written_in (r := 1) (lo := 0) (hi := 8) rfl (by decide) hq
      rw [Sym.inRange_iff (by omega)]
      omega
  have hw8 : NativeRustcVm.WordAt st.data.dmem m0.regs.X0.toBitVec (m.regs.getXReg .X8) := by
    have := Transcript.wordAt_write hm' (r := 1) (o := 0) rfl (by omega) (v := .reg .X8)
      (by decide)
    simpa [off, Sym.eval, NativeRustcVm.addr_add_zero] using this
  obtain ⟨h1, h2⟩ := hpost _ (hm'.kept hwf) hs8 hw8
  refine .done _ ⟨by simp only [PcOk] at hpc; rw [hpc, hret], h1, h2, fun q hq ↦ ?_, hsv⟩
  rw [hs8 q fun h' ↦ hq (.inl (o_mono (by omega) h'))]
  refine hfr.same q fun h' ↦ hq ?_
  rcases h' with h' | h' | h' | h'
  · exact .inr (.inr (.inr h'))
  · exact .inl h'
  · exact .inr (.inl h')
  · exact .inr (.inr (.inl h'))

/-- The tag `0` exits: `verifyGkrGrandProducts` failed, the output `none`. -/
theorem exit_none (hp : Placed code k) (h : VerifyGkrPre a s0 m0) {m : MachineData}
    (hfr : Fr m0 96 verifyGkrStack slots keep (outs m0) m)
    (h19 : m.regs.getXReg .X19 = m0.regs.X0) (h8 : m.regs.getXReg .X8 = 0)
    (hr : (verifyGkrGrandProducts m0.regs.X2.toNat).run s0 = none) :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyGkrGrandProducts.b8Offset)⟩ :=
  exit_spec hp h hfr h19 fun d _ _ hw ↦ by
    rw [hr]
    refine ⟨by rw [h8] at hw; exact hw, fun _ _ _ _ he ↦ by cases he⟩

/-- A word a block loaded from region `r` of a machine state. -/
theorem load_eq {m : MachineData} {rs : List (BitVec 64 × Nat)} {r n o : Nat} {b : BitVec 64}
    (hb : rs[r]? = some (b, n)) {w : UInt64}
    (hw : NativeRustcVm.WordAt m.dmem (b + BitVec.ofNat 64 o) w) :
    (Sym.load r o 8).eval (Env.ofMachine m rs) = w.toBitVec :=
  Transcript.load_ofMachine hb hw

/-- The register a block set to a load. -/
theorem reg_load {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState} {x : XReg}
    {r n o : Nat} {b : BitVec 64} (hm : Match (Env.ofMachine m rs) S m')
    (h : S.reg x = some (.load r o 8)) (hb : rs[r]? = some (b, n)) {w : UInt64}
    (hw : NativeRustcVm.WordAt m.dmem (b + BitVec.ofNat 64 o) w) : m'.regs.getXReg x = w :=
  UInt64.toBitVec_inj.mp ((hm.regs x _ h).trans (load_eq hb hw))

/-- **After `gkr_layers`** (`.LVerifyGkrGrandProducts_5`'s predecessor `b5`): its result in X0. -/
theorem after_layers (hp : Placed code k) (h : VerifyGkrPre a s0 m0) {sh cnt : EW} {s2 : TState}
    {m : MachineData} (hfr : Fr m0 96 verifyGkrStack slots keep (outs m0) m)
    (h19 : m.regs.getXReg .X19 = m0.regs.X0)
    (h23 : m.regs.getXReg .X23 = cnt.c1) (h24 : m.regs.getXReg .X24 = cnt.c0)
    (hr : (verifyGkrGrandProducts m0.regs.X2.toNat).run s0 =
      ((gkrLayers m0.regs.X2.toNat ⟨#[sh, sh, cnt], #[]⟩).run s2).bind fun z ↦
        some ((cnt, z.1.point, z.1.values), z.2))
    (hx0 : m.regs.X0 = okWord ((gkrLayers m0.regs.X2.toNat ⟨#[sh, sh, cnt], #[]⟩).run s2).isSome)
    (hok : ∀ g' s', (gkrLayers m0.regs.X2.toNat ⟨#[sh, sh, cnt], #[]⟩).run s2 = some (g', s') →
      TStateAt m.dmem m0.regs.X1.toBitVec a s' ∧ GkrStateWAt m.dmem m0.regs.X3.toBitVec g') :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyGkrGrandProducts.b5Offset)⟩ := by
  have hS := h.1
  refine Fr.runBlock hS N_ge rfl hfr (b5_in_code.trans hp.1 (by simp [b5])) run_b5 rfl rfl
    (by decide) (by decide) fun st hfr5 hd5 hm5 hpc5 ↦ ?_
  have hc : SBool.eval (Env.ofMachine m [(base m0 96, 96)]) (.not (.bit .W32 (.reg .X0) 0)) =
      !((gkrLayers m0.regs.X2.toNat ⟨#[sh, sh, cnt], #[]⟩).run s2).isSome := by
    show (!(low .W32 (m.regs.getXReg .X0).toBitVec).getLsbD 0) = _
    rw [show m.regs.getXReg .X0 = m.regs.X0 from rfl, hx0, okWord_bit]
  simp only [PcOk, hc] at hpc5
  have e19 : st.data.regs.getXReg .X19 = m0.regs.X0 := (reg_of hm5 rfl).trans h19
  have e23 : st.data.regs.getXReg .X23 = cnt.c1 := (reg_of hm5 rfl).trans h23
  have e24 : st.data.regs.getXReg .X24 = cnt.c0 := (reg_of hm5 rfl).trans h24
  cases hgl : (gkrLayers m0.regs.X2.toNat ⟨#[sh, sh, cnt], #[]⟩).run s2 with
  | none =>
    simp only [hgl, Option.isSome_none, Bool.not_false, ↓reduceIte] at hpc5
    refine at_pc (hpc5.trans (hp.label (j := NativeRustcVmArm.Vm.VerifyGkrGrandProducts.b8Offset) NativeRustcVmArm.Vm.VerifyGkrGrandProducts.label_5_at)) (exit_none hp h hfr5 e19 ?_ ?_)
    · exact UInt64.toBitVec_inj.mp (reg_lit hm5 (r := .X8) (n := 0) rfl)
    · rw [hr, hgl]; rfl
  | some z =>
    obtain ⟨g', s'⟩ := z
    simp only [hgl, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc5
    obtain ⟨hts', hgs'⟩ := hok g' s' hgl
    rw [← hd5] at hts' hgs'
    -- `b6`: the count at `out + 8`, tag `1`.
    have hoo := h.2.2.2.2.2.1
    have hwf6 : (Env.ofMachine st.data [(base m0 96, 96), (m0.regs.X0.toBitVec, 24)]).WF :=
      Bus.wf_frame2 hS N_ge hfr5.kept ⟨hoo.1, hoo.2.1⟩ hoo.2.2.2.2.1
    have hm6 := match_frameW (n := 24) hS N_ge rfl hfr5.sp (r := .X19) (by rw [e19])
    refine exec_at (b6_in_code.trans hp.1 (by simp [b6])) run_b6 hwf6 hpc5 hm6
      fun st6 hm6' hpc6 ↦ ?_
    have hnw : m0.regs.X0.toBitVec.toNat + 24 ≤ 2 ^ 64 := hoo.2.1
    have hs6 : NativeRustcVm.SameOutside st.data.dmem st6.data.dmem
        (InRange m0.regs.X0.toBitVec 24) :=
      NativeRustcVm.SameOutside.mono (hm6'.sameOutside hwf6) fun q hq ↦ by
        have := written_in (r := 1) (lo := 8) (hi := 24) rfl (by decide) hq
        rw [Sym.inRange_iff (by omega)]
        omega
    have hfr6 : Fr m0 96 verifyGkrStack slots keep (outs m0) st6.data :=
      Fr.ofBlockW hfr5 hm6 hm6' hwf6 rfl rfl
        (fun r hr ↦ ⟨.reg r, by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> rfl,
          by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> rfl⟩)
        rfl N_ge hS.2.1 slots_le fun w hw ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl <;>
          · refine .inr ⟨by decide, fun b sz hb ↦ ?_⟩
            simp only [Env.ofMachine, List.getElem?_cons_succ, List.getElem?_cons_zero,
              Option.some.injEq, Prod.mk.injEq] at hb
            obtain ⟨rfl, rfl⟩ := hb
            exact ⟨by decide, fun i hi ↦ .inl (NativeRustcVm.inRange_add hi (by omega))⟩
    have w8 := Transcript.wordAt_write hm6' (r := 1) (o := 8) rfl (by omega) (v := .reg .X24)
      (by decide)
    have w16 := Transcript.wordAt_write hm6' (r := 1) (o := 16) rfl (by omega) (v := .reg .X23)
      (by decide)
    simp only [Sym.eval, Env.ofMachine, e24, e23] at w8 w16
    have e6x19 : st6.data.regs.getXReg .X19 = m0.regs.X0 :=
      UInt64.toBitVec_inj.mp ((hm6'.regs .X19 _ rfl).trans (Transcript.eval_ptr rfl))
    simp only [PcOk] at hpc6
    refine at_pc (hpc6.trans (hp.label (j := NativeRustcVmArm.Vm.VerifyGkrGrandProducts.b8Offset) NativeRustcVmArm.Vm.VerifyGkrGrandProducts.label_5_at))
      (exit_spec hp h hfr6 e6x19 fun d hkd hd hw ↦ ?_)
    have e8 : st6.data.regs.getXReg .X8 = 1 :=
      UInt64.toBitVec_inj.mp (reg_lit hm6' (r := .X8) (n := 1) rfl)
    rw [e8] at hw
    have hsd : NativeRustcVm.SameOutside st.data.dmem d (InRange m0.regs.X0.toBitVec 24) :=
      fun q hq ↦ (hd q fun h' ↦ hq (o_mono (by omega) h')).trans (hs6 q hq)
    have kt : TStateAt d m0.regs.X1.toBitVec a s' :=
      hts'.frame (fun q hq ↦ hkd q (hm6'.kept hwf6 q hq)) (fun q hq ↦ (o_apart h hq).1) hsd
    have kg : GkrStateWAt d m0.regs.X3.toBitVec g' :=
      gkrStateWAt_keep hgs' hsd fun q hq ↦ (o_apart h hq).2
    have k8 : NativeRustcVm.WordAt d (off m0.regs.X0.toBitVec 8) cnt.c0 :=
      NativeRustcVm.BytesAt.of_sameOutside w8 hd fun i hi hq ↦ by
        rw [NativeRustcVm.length_wordBytes] at hi
        rw [off, NativeRustcVm.addr_add_add, inRange_add_iff (by omega)] at hq
        omega
    have k16 : NativeRustcVm.WordAt d (off m0.regs.X0.toBitVec 16) cnt.c1 :=
      NativeRustcVm.BytesAt.of_sameOutside w16 hd fun i hi hq ↦ by
        rw [NativeRustcVm.length_wordBytes] at hi
        rw [off, NativeRustcVm.addr_add_add, inRange_add_iff (by omega)] at hq
        omega
    simp only [hr, hgl, Option.bind_some, Option.map_some]
    refine ⟨?_, fun c pt vs s'' he ↦ ?_⟩
    · simp only [OptEWAt]
      refine ⟨hw, NativeRustcVm.ewAt_iff.mpr ⟨k8, ?_⟩⟩
      rw [off, NativeRustcVm.addr_add_add]
      exact k16
    · simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨⟨-, rfl, rfl⟩, rfl⟩ := he
      exact ⟨kt, kg⟩

/-- **After the count root** (`b3`): none, the tag `0` (`b7`); else the state written (`b4`) and
`gkr_layers` called. -/
theorem after_count (hp : Placed code k) (h : VerifyGkrPre a s0 m0)
    (hgl : ∀ s g, Spec (Labels.label NativeRustcVmArm.Vm.GkrLayers.entryLabel) (GkrLayersPre a s g) (GkrLayersPost a s g))
    {sh : EW} {s1 : TState} {m : MachineData}
    (hfr : Fr m0 96 verifyGkrStack slots keep (outs m0) m)
    (h19 : m.regs.getXReg .X19 = m0.regs.X0) (h20 : m.regs.getXReg .X20 = m0.regs.X3)
    (h21 : m.regs.getXReg .X21 = m0.regs.X2) (h22 : m.regs.getXReg .X22 = m0.regs.X1)
    (h23 : m.regs.getXReg .X23 = sh.c0) (h25 : m.regs.getXReg .X25 = sh.c1)
    (hr : (verifyGkrGrandProducts m0.regs.X2.toNat).run s0 =
      (readScalar.run s1).bind fun y ↦
        ((gkrLayers m0.regs.X2.toNat ⟨#[sh, sh, y.1], #[]⟩).run y.2).bind fun z ↦
          some ((y.1, z.1.point, z.1.values), z.2))
    (hopt : OptEWAt m.dmem (base m0 96 + BitVec.ofNat 64 8) ((readScalar.run s1).map (·.1)))
    (hnext : NextAt m.dmem m0.regs.X1.toBitVec a (readScalar.run s1)) :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyGkrGrandProducts.b3Offset)⟩ := by
  have hS := h.1
  have c := ctx h
  refine Fr.runBlock hS N_ge rfl hfr (b3_in_code.trans hp.1 (by simp [b3])) run_b3 rfl rfl
    (by decide) (by decide) fun st hfr3 hd3 hm3 hpc3 ↦ ?_
  have e19 : st.data.regs.getXReg .X19 = m0.regs.X0 := (reg_of hm3 rfl).trans h19
  have e20 : st.data.regs.getXReg .X20 = m0.regs.X3 := (reg_of hm3 rfl).trans h20
  have e21 : st.data.regs.getXReg .X21 = m0.regs.X2 := (reg_of hm3 rfl).trans h21
  have e22 : st.data.regs.getXReg .X22 = m0.regs.X1 := (reg_of hm3 rfl).trans h22
  have e23 : st.data.regs.getXReg .X23 = sh.c0 := (reg_of hm3 rfl).trans h23
  have e25 : st.data.regs.getXReg .X25 = sh.c1 := (reg_of hm3 rfl).trans h25
  cases hrs : readScalar.run s1 with
  | none =>
    rw [hrs] at hopt
    simp only [Option.map_none, OptEWAt] at hopt
    have hl : (Env.ofMachine m [(base m0 96, 96)]).load 0 8 4 = BitVec.ofNat 64 0 :=
      Transcript.load4_of_tag (w := 0) (.inl rfl) hopt
    have hc : SBool.eval (Env.ofMachine m [(base m0 96, 96)])
        (.not (.bit .W32 (.load 0 8 4) 0)) = true := by
      show (!(low .W32 ((Env.ofMachine m [(base m0 96, 96)]).load 0 8 4)).getLsbD 0) = true
      rw [hl]
      rfl
    simp only [PcOk, hc, ↓reduceIte] at hpc3
    refine at_pc (hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.VerifyGkrGrandProducts.b7Offset) NativeRustcVmArm.Vm.VerifyGkrGrandProducts.label_4_at)) (Fr.runBlock hS N_ge rfl hfr3
      (b7_in_code.trans hp.1 (by simp [b7])) run_b7 rfl rfl (by decide) (by decide)
      fun st7 hfr7 _ hm7 hpc7 ↦ ?_)
    simp only [PcOk] at hpc7
    exact at_pc hpc7 (exit_none hp h hfr7 ((reg_of hm7 rfl).trans e19)
      (UInt64.toBitVec_inj.mp (reg_lit hm7 (r := .X8) (n := 0) rfl)) (by rw [hr, hrs]; rfl))
  | some y =>
    obtain ⟨cnt, s2⟩ := y
    rw [hrs] at hopt hnext
    simp only [Option.map_some, OptEWAt] at hopt
    have hts2 : TStateAt st.data.dmem m0.regs.X1.toBitVec a s2 := by
      rw [hd3]; exact hnext cnt s2 rfl
    have hl : (Env.ofMachine m [(base m0 96, 96)]).load 0 8 4 = BitVec.ofNat 64 1 :=
      Transcript.load4_of_tag (w := 1) (.inr rfl) hopt.1
    have hc : SBool.eval (Env.ofMachine m [(base m0 96, 96)])
        (.not (.bit .W32 (.load 0 8 4) 0)) = false := by
      show (!(low .W32 ((Env.ofMachine m [(base m0 96, 96)]).load 0 8 4)).getLsbD 0) = false
      rw [hl]
      rfl
    simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc3
    obtain ⟨hc0, hc1⟩ := NativeRustcVm.ewAt_iff.mp hopt.2
    rw [off, NativeRustcVm.addr_add_add, ← hd3] at hc0
    rw [off, NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add, ← hd3] at hc1
    -- `b4`: the state written, `gkr_layers` called.
    have hgo := h.2.2.2.2.2.2.1
    have hwf4 : (Env.ofMachine st.data [(base m0 96, 96), (m0.regs.X3.toBitVec, 1064)]).WF :=
      Bus.wf_frame2 hS N_ge hfr3.kept ⟨hgo.1, hgo.2.1⟩ hgo.2.2.2.2.1
    have hm4 := match_frameW (n := 1064) hS N_ge rfl hfr3.sp (r := .X20) (by rw [e20])
    refine exec_at (b4_in_code.trans hp.1 (by simp [b4])) run_b4 hwf4 hpc3 hm4
      fun st4 hm4' hpc4 ↦ ?_
    have hnwp : m0.regs.X3.toBitVec.toNat + 1064 ≤ 2 ^ 64 := hgo.2.1
    have hfr4 : Fr m0 96 verifyGkrStack slots keep (outs m0) st4.data :=
      Fr.ofBlockW hfr3 hm4 hm4' hwf4 rfl rfl
        (fun r hr ↦ ⟨.reg r, by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> rfl,
          by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> rfl⟩)
        rfl N_ge hS.2.1 slots_le fun w hw ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          · refine .inr ⟨by decide, fun b sz hb ↦ ?_⟩
            simp only [Env.ofMachine, List.getElem?_cons_succ, List.getElem?_cons_zero,
              Option.some.injEq, Prod.mk.injEq] at hb
            obtain ⟨rfl, rfl⟩ := hb
            exact ⟨by decide, fun i hi ↦ .inr (.inr (NativeRustcVm.inRange_add hi (by decide)))⟩
    have hs4 : NativeRustcVm.SameOutside st.data.dmem st4.data.dmem
        (InRange m0.regs.X3.toBitVec gkrStateBytes) :=
      NativeRustcVm.SameOutside.mono (hm4'.sameOutside hwf4) fun q hq ↦ by
        have := written_in (r := 1) (lo := 0) (hi := 56) rfl (by decide) hq
        rw [Sym.inRange_iff (by unfold gkrStateBytes pointBufBytes busPointCap; omega)]
        unfold gkrStateBytes pointBufBytes busPointCap
        omega
    have hts4 : TStateAt st4.data.dmem m0.regs.X1.toBitVec a s2 :=
      hts2.frame (fun q hq ↦ hm4'.kept hwf4 q hq) (fun q hq ↦ p_apart h hq) hs4
    have w0 : NativeRustcVm.WordAt st4.data.dmem (off m0.regs.X3.toBitVec 0) sh.c0 := by
      have := Transcript.wordAt_write hm4' (r := 1) (o := 0) rfl (by omega) (v := .reg .X23)
        (by decide)
      simp only [Sym.eval, Env.ofMachine, e23] at this
      exact this
    have w8 : NativeRustcVm.WordAt st4.data.dmem (off m0.regs.X3.toBitVec 8) sh.c1 := by
      have := Transcript.wordAt_write hm4' (r := 1) (o := 8) rfl (by omega) (v := .reg .X25)
        (by decide)
      simp only [Sym.eval, Env.ofMachine, e25] at this
      exact this
    have w16 : NativeRustcVm.WordAt st4.data.dmem (off m0.regs.X3.toBitVec 16) sh.c0 := by
      have := Transcript.wordAt_write hm4' (r := 1) (o := 16) rfl (by omega) (v := .reg .X23)
        (by decide)
      simp only [Sym.eval, Env.ofMachine, e23] at this
      exact this
    have w24 : NativeRustcVm.WordAt st4.data.dmem (off m0.regs.X3.toBitVec 24) sh.c1 := by
      have := Transcript.wordAt_write hm4' (r := 1) (o := 24) rfl (by omega) (v := .reg .X25)
        (by decide)
      simp only [Sym.eval, Env.ofMachine, e25] at this
      exact this
    have w32 : NativeRustcVm.WordAt st4.data.dmem (off m0.regs.X3.toBitVec 32) cnt.c0 := by
      have := Transcript.wordAt_write hm4' (r := 1) (o := 32) rfl (by omega)
        (v := .load 0 16 8) (by decide)
      simp only [Sym.eval] at this
      rw [Transcript.load_ofMachine (b := base m0 96) (n := 96) rfl hc0] at this
      exact this
    have w40 : NativeRustcVm.WordAt st4.data.dmem (off m0.regs.X3.toBitVec 40) cnt.c1 := by
      have := Transcript.wordAt_write hm4' (r := 1) (o := 40) rfl (by omega)
        (v := .load 0 24 8) (by decide)
      simp only [Sym.eval] at this
      rw [Transcript.load_ofMachine (b := base m0 96) (n := 96) rfl hc1] at this
      exact this
    have w48 : NativeRustcVm.WordAt st4.data.dmem (off m0.regs.X3.toBitVec 48) 0 := by
      have := Transcript.wordAt_write hm4' (r := 1) (o := 48) rfl (by omega) (v := .lit 0)
        (by decide)
      exact this
    have hgs : GkrStateWAt st4.data.dmem m0.regs.X3.toBitVec ⟨#[sh, sh, cnt], #[]⟩ := by
      refine ⟨rfl, Bus.ewsAt_of_words [sh, sh, cnt] fun i hi ↦ ?_, ⟨Nat.zero_le _, w48,
        NativeRustcVm.ewsAt_nil _ _⟩⟩
      simp only [List.length_cons, List.length_nil] at hi
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · exact ⟨w0, w8⟩
      · exact ⟨w16, w24⟩
      · exact ⟨w32, w40⟩
    have f0 : st4.data.regs.X0 = m0.regs.X1 := (reg_of hm4' (r := .X0) (r' := .X22) rfl).trans e22
    have f1 : st4.data.regs.X1 = m0.regs.X2 :=
      (reg_of hm4' (r := .X1) (r' := .X21) rfl).trans e21
    have f2 : st4.data.regs.X2 = m0.regs.X3 :=
      UInt64.toBitVec_inj.mp ((hm4'.regs .X2 _ rfl).trans (Transcript.eval_ptr rfl))
    have f19 : st4.data.regs.getXReg .X19 = m0.regs.X0 := (reg_of hm4' rfl).trans e19
    have f23 : st4.data.regs.getXReg .X23 = cnt.c1 := by
      have := hm4'.regs .X23 _ rfl
      simp only [Sym.eval] at this
      rw [Transcript.load_ofMachine (b := base m0 96) (n := 96) rfl hc1] at this
      exact UInt64.toBitVec_inj.mp this
    have f24 : st4.data.regs.getXReg .X24 = cnt.c0 := by
      have := hm4'.regs .X24 _ rfl
      simp only [Sym.eval] at this
      rw [Transcript.load_ofMachine (b := base m0 96) (n := 96) rfl hc0] at this
      exact UInt64.toBitVec_inj.mp this
    have hat := Fr.at_ c hfr4 (outs_not_rc h)
    simp only [PcOk] at hpc4
    refine Fr.callSpec hfr4 hS.2.1 le_gl keep_callee slots_le (outs_not_frame h)
      (hgl s2 ⟨#[sh, sh, cnt], #[]⟩) hpc4 ?_
      (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ ?_, hq.2.2.2⟩)
      fun m5 hfr5 hq5 hcs5 ↦ ?_
    · refine ⟨hfr4.stackOk hS rfl le_gl, c.rcAt hat le_gl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [f0]; exact hts4
      · rw [f0]; exact c.tstateOk hat le_gl
      · rw [f1]; exact (Nat.zero_add _).trans_le h.2.2.2.2.1
      · rw [f0, f2]; exact c.outOk_sub hat le_gl hgo
      · rw [f2]; exact hgs
    · rw [f0, f2] at hq'
      rcases hq' with hq' | hq' | hq'
      · exact .inr (.inr (.inl hq'))
      · exact .inr (.inr (.inr hq'))
      · exact .inl hq'
    · obtain ⟨hx0, hok, -, -⟩ := hq5
      rw [f1] at hx0 hok
      rw [f0, f2] at hok
      exact after_layers hp h hfr5 ((hcs5 .X19 rfl).trans f19) ((hcs5 .X23 rfl).trans f23)
        ((hcs5 .X24 rfl).trans f24) (by rw [hr, hrs]; rfl) hx0 hok

/-- **`verify_gkr_grand_products`'s contract.** -/
theorem verifyGkr_spec (hp : Placed code k)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hgl : ∀ s g, Spec (Labels.label NativeRustcVmArm.Vm.GkrLayers.entryLabel) (GkrLayersPre a s g) (GkrLayersPost a s g)) :
    Spec (Labels.label NativeRustcVmArm.Vm.VerifyGkrGrandProducts.entryLabel) (VerifyGkrPre a s0) (VerifyGkrPost a s0) := by
  intro m0 h
  have hS := h.1
  have hN : verifyGkrStack ≤ m0.regs.SP.toNat := hS.2.1
  have c := ctx h
  have hwf := Bus.wf_env0 hS (F := 96) N_ge
  have hm : Match (Bus.env0 m0 96) entryS m0 := Bus.match_entry hS N_ge rfl
  rw [show Labels.label NativeRustcVmArm.Vm.VerifyGkrGrandProducts.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyGkrGrandProducts.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.VerifyGkrGrandProducts.entryOffset) NativeRustcVmArm.Vm.VerifyGkrGrandProducts.entry_at]
  refine exec_then (b0_in_code.trans hp.1 (by simp [b0])) run_b0 hwf hm fun st hm1 hpc ↦ ?_
  have hfr : Fr m0 96 verifyGkrStack slots keep (outs m0) st.data :=
    Fr.ofPrologue hN N_ge hm1 hwf rfl (by decide) slots_le (by decide) (by decide)
  have hsame : NativeRustcVm.SameOutside m0.dmem st.data.dmem (InRange (base m0 96) 96) :=
    NativeRustcVm.SameOutside.mono (hm1.sameOutside hwf) fun q hq ↦
      Written.inRange (r := 0) rfl (Bus.frame_mapped hS N_ge).2 (by decide) hq
  have hts : TStateAt st.data.dmem m0.regs.X1.toBitVec a s0 :=
    h.2.2.1.frame (fun q hq ↦ hm1.kept hwf q hq) (fun q hq ↦ frame_not_tstate c hq) hsame
  have e0 : st.data.regs.X0.toBitVec = base m0 96 + BitVec.ofNat 64 8 := by
    rw [show st.data.regs.X0 = st.data.regs.getXReg .X0 from rfl, hm1.regs .X0 _ rfl]
    rfl
  have e1 : st.data.regs.X1 = m0.regs.X1 := reg_of hm1 (r := .X1) (r' := .X1) rfl
  have e19 : st.data.regs.getXReg .X19 = m0.regs.X0 := reg_of hm1 (r' := .X0) rfl
  have e20 : st.data.regs.getXReg .X20 = m0.regs.X3 := reg_of hm1 (r' := .X3) rfl
  have e21 : st.data.regs.getXReg .X21 = m0.regs.X2 := reg_of hm1 (r' := .X2) rfl
  have e22 : st.data.regs.getXReg .X22 = m0.regs.X1 := reg_of hm1 (r' := .X1) rfl
  have hat := Fr.at_ c hfr (outs_not_rc h)
  simp only [PcOk] at hpc
  refine Fr.callLocal (o := 8) (n := 24) (X := fun q ↦
      InRange (base m0 96 + BitVec.ofNat 64 8) 24 q ∨ InRange m0.regs.X1.toBitVec tstateBytes q)
    hfr hN le_rs keep_callee (by decide) (by omega) (outs_not_frame h)
    (fun q hq ↦ hq.elim .inr fun h' ↦ .inl (.inr (.inl h'))) (hrs s0) hpc ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ ?_, hq.2.2.2⟩)
    fun m2 hfr2 hq2 hcs2 _ ↦ ?_
  · refine ⟨hfr.stackOk hS rfl le_rs, c.rcAt hat le_rs, ?_, ?_, ?_⟩
    · rw [e1]; exact hts
    · rw [e1]; exact c.tstateOk hat le_rs
    · rw [e1, e0]; exact c.outOk hat le_rs (o := 8) (n := 24) (by omega)
  · rw [e0, e1] at hq'
    rcases hq' with hq' | hq' | hq'
    · exact .inr (.inl hq')
    · exact .inr (.inr hq')
    · exact .inl hq'
  -- `b1`: the shared root's tag.
  obtain ⟨hopt1, hnext1, -, -⟩ := hq2
  rw [e0] at hopt1
  rw [e1] at hnext1
  have f19 : m2.regs.getXReg .X19 = m0.regs.X0 := (hcs2 .X19 rfl).trans e19
  have f20 : m2.regs.getXReg .X20 = m0.regs.X3 := (hcs2 .X20 rfl).trans e20
  have f21 : m2.regs.getXReg .X21 = m0.regs.X2 := (hcs2 .X21 rfl).trans e21
  have f22 : m2.regs.getXReg .X22 = m0.regs.X1 := (hcs2 .X22 rfl).trans e22
  refine Fr.runBlock hS N_ge rfl hfr2 (b1_in_code.trans hp.1 (by simp [b1])) run_b1 rfl rfl
    (by decide) (by decide) fun st1 hfr1 hd1 hm1' hpc1 ↦ ?_
  have g19 : st1.data.regs.getXReg .X19 = m0.regs.X0 := (reg_of hm1' rfl).trans f19
  cases hr1 : readScalar.run s0 with
  | none =>
    rw [hr1] at hopt1
    simp only [Option.map_none, OptEWAt] at hopt1
    have hc : SBool.eval (Env.ofMachine m2 [(base m0 96, 96)])
        (.cmp .eq .W64 (.load 0 8 8) (.lit 0)) = true := by
      show CmpOp.eq.apply .W64 ((Sym.load 0 8 8).eval (Env.ofMachine m2 [(base m0 96, 96)]))
        (BitVec.ofNat 64 0) = true
      rw [load_eq rfl hopt1]
      rfl
    simp only [PcOk, hc, ↓reduceIte] at hpc1
    exact at_pc (hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.VerifyGkrGrandProducts.b8Offset) NativeRustcVmArm.Vm.VerifyGkrGrandProducts.label_5_at)) (exit_none hp h hfr1 g19
      (reg_load hm1' rfl rfl hopt1) (by rw [verifyGkr_run, hr1]; rfl))
  | some y =>
    obtain ⟨sh, s1⟩ := y
    rw [hr1] at hopt1 hnext1
    simp only [Option.map_some, OptEWAt] at hopt1
    have hc : SBool.eval (Env.ofMachine m2 [(base m0 96, 96)])
        (.cmp .eq .W64 (.load 0 8 8) (.lit 0)) = false := by
      show CmpOp.eq.apply .W64 ((Sym.load 0 8 8).eval (Env.ofMachine m2 [(base m0 96, 96)]))
        (BitVec.ofNat 64 0) = false
      rw [load_eq rfl hopt1.1]
      rfl
    simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨hs0, hs1⟩ := NativeRustcVm.ewAt_iff.mp hopt1.2
    rw [off, NativeRustcVm.addr_add_add, ← hd1] at hs0
    rw [off, NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add, ← hd1] at hs1
    have hts1 : TStateAt st1.data.dmem m0.regs.X1.toBitVec a s1 := by
      rw [hd1]; exact hnext1 sh s1 rfl
    -- `b2`: the shared root kept, the count root read.
    refine at_pc hpc1 (Fr.runBlock hS N_ge rfl hfr1 (b2_in_code.trans hp.1 (by simp [b2])) run_b2
      rfl rfl (by decide) (by decide) fun st2 hfr2' hd2 hm2 hpc2 ↦ ?_)
    have k0 : st2.data.regs.X0.toBitVec = base m0 96 + BitVec.ofNat 64 8 := by
      rw [show st2.data.regs.X0 = st2.data.regs.getXReg .X0 from rfl, hm2.regs .X0 _ rfl]
      rfl
    have k1 : st2.data.regs.X1 = m0.regs.X1 :=
      (reg_of hm2 (r := .X1) (r' := .X22) rfl).trans ((reg_of hm1' rfl).trans f22)
    have k23 : st2.data.regs.getXReg .X23 = sh.c0 := reg_load hm2 rfl rfl hs0
    have k25 : st2.data.regs.getXReg .X25 = sh.c1 := reg_load hm2 rfl rfl hs1
    have k19 : st2.data.regs.getXReg .X19 = m0.regs.X0 := (reg_of hm2 rfl).trans g19
    have k20 : st2.data.regs.getXReg .X20 = m0.regs.X3 :=
      (reg_of hm2 rfl).trans ((reg_of hm1' rfl).trans f20)
    have k21 : st2.data.regs.getXReg .X21 = m0.regs.X2 :=
      (reg_of hm2 rfl).trans ((reg_of hm1' rfl).trans f21)
    have k22 : st2.data.regs.getXReg .X22 = m0.regs.X1 :=
      (reg_of hm2 rfl).trans ((reg_of hm1' rfl).trans f22)
    have hts2 : TStateAt st2.data.dmem m0.regs.X1.toBitVec a s1 := by rw [hd2]; exact hts1
    have hat2 := Fr.at_ c hfr2' (outs_not_rc h)
    simp only [PcOk] at hpc2
    refine Fr.callLocal (o := 8) (n := 24) (X := fun q ↦
        InRange (base m0 96 + BitVec.ofNat 64 8) 24 q ∨ InRange m0.regs.X1.toBitVec tstateBytes q)
      hfr2' hN le_rs keep_callee (by decide) (by omega) (outs_not_frame h)
      (fun q hq ↦ hq.elim .inr fun h' ↦ .inl (.inr (.inl h'))) (hrs s1) hpc2 ?_
      (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ ?_, hq.2.2.2⟩)
      fun m3 hfr3 hq3 hcs3 _ ↦ ?_
    · refine ⟨hfr2'.stackOk hS rfl le_rs, c.rcAt hat2 le_rs, ?_, ?_, ?_⟩
      · rw [k1]; exact hts2
      · rw [k1]; exact c.tstateOk hat2 le_rs
      · rw [k1, k0]; exact c.outOk hat2 le_rs (o := 8) (n := 24) (by omega)
    · rw [k0, k1] at hq'
      rcases hq' with hq' | hq' | hq'
      · exact .inr (.inl hq')
      · exact .inr (.inr hq')
      · exact .inl hq'
    · obtain ⟨hopt3, hnext3, -, -⟩ := hq3
      rw [k0] at hopt3
      rw [k1] at hnext3
      exact after_count hp h hgl hfr3 ((hcs3 .X19 rfl).trans k19) ((hcs3 .X20 rfl).trans k20)
        ((hcs3 .X21 rfl).trans k21) ((hcs3 .X22 rfl).trans k22) ((hcs3 .X23 rfl).trans k23)
        ((hcs3 .X25 rfl).trans k25) (by rw [verifyGkr_run, hr1]; rfl) hopt3 hnext3

end

end NativeRustcVmArm.Bus.VerifyGkr
