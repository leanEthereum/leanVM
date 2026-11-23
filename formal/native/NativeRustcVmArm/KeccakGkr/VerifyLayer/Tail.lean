module

public import NativeRustcVmArm.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.LinearTranspose.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.Exit
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.Lemmas
public import NativeRustcArm.Spec.Mem
import Mathlib.Tactic.IntervalCases
public import NativeRustcVm.KeccakGkr.Transpose

/-!
# `verify_layer`: after the layer's weights

From `.LVerifyLayer_35` (`b62`): `linear_transpose` of the layer's weights into the claim's bit
weights, the new value (two `EW::mul`), the instance weights copied into the claim (`memcpy`), its
point emptied and extended by the sumcheck's (`Buf<EW, 30>::extend`), the exit (`tail`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVmArm.Vm.VerifyLayer
open NativeRustcVm (Region)
open NativeRustcVm.Layout (Same)
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt claimBytes)

@[expose] public section

/-- The frame's words the tail reads: the scratch, the layer's weights, `t2`, `t1`, `t0`, the
claim, its instance weights. -/
def tailWords (m0 : MachineData) (t0 t1 t2 : EW) : List (Nat × UInt64) :=
  [(120, m0.regs.X4), (88, UInt64.ofBitVec (sA m0 + BitVec.ofNat 64 51200)), (16, t2.c1),
    (24, t2.c0), (32, t1.c1), (40, t1.c0), (48, t0.c1), (56, t0.c0), (136, m0.regs.X3),
    (80, UInt64.ofBitVec (cA m0 + BitVec.ofNat 64 16))]

end

public section

variable {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- `linear_transpose`'s regions in the scratch. -/
theorem lt_areas [Labels] (hpre : VerifyLayerPre a s c m0) {m : MachineData} (hb : Body m0 m) :
    Areas m linearTransposeStack
      [⟨sA m0 + BitVec.ofNat 64 76800, 25600⟩, ⟨sA m0 + BitVec.ofNat 64 102400, 5120⟩,
        ⟨sA m0 + BitVec.ofNat 64 25600, 25600⟩]
      [⟨sA m0 + BitVec.ofNat 64 51200, 25600⟩, rhoRegion] := by
  have g := geo_of hpre
  obtain ⟨hS, -, -, -, -, -, -, -, -, hA⟩ := hpre
  have hm : rhoRegion ∈ [a.region, rcRegion, projectRegion, rhoRegion] := by simp
  have hrok := hA.1 _ (List.mem_append.mpr (.inr hm))
  have hsok := hA.1 ⟨sA m0, NativeRustcVm.KeccakGkr.scratchBytes⟩ (by simp)
  have h0 := hA.2.2 _ List.mem_cons_self _ hm
  have h3 := hA.2.2 ⟨sA m0, NativeRustcVm.KeccakGkr.scratchBytes⟩ (by simp) _ hm
  have := g.hN; have := g.hs; have := g.hss; have := Geo.sp_lt m0
  have hspn : m0.regs.SP.toNat = m0.regs.SP.toBitVec.toNat := rfl
  have hsb : (stackBelow m0 3648).toNat = m0.regs.SP.toNat - 3648 :=
    NativeRustcVm.toNat_sub_ofNat (by omega)
  have hst := g.stk hb.sp (n := 80) (by decide)
  have hrw := hrok.2
  unfold NativeRustcVm.NoWrap at hrw
  unfold Apart at h0 h3
  simp only [stackRegion, stack_eq, NativeRustcVm.KeccakGkr.scratchBytes, rhoRegion] at h0 h3 hrw
  rw [hsb] at h0
  have e1 := g.sa (o := 76800) (by decide)
  have e2 := g.sa (o := 102400) (by decide)
  have e3 := g.sa (o := 25600) (by decide)
  have e4 := g.sa (o := 51200) (by decide)
  have hsub : ∀ o n, 0 < n → o + n ≤ 205824 →
      Region.Ok m.dmem ⟨sA m0 + BitVec.ofNat 64 o, n⟩ := by
    intro o n hn h
    refine ⟨fun i hi ↦ ?_, ?_⟩
    · have hi' : i < n := hi
      rw [NativeRustcVm.addr_add_add]
      exact hb.kept _ (hsok.1 _ (show o + i < NativeRustcVm.KeccakGkr.scratchBytes by
        unfold NativeRustcVm.KeccakGkr.scratchBytes; omega))
    · show (sA m0 + BitVec.ofNat 64 o).toNat + n ≤ 2 ^ 64
      rw [NativeRustcVm.toNat_add_ofNat (by omega)]
      omega
  have hlt : linearTransposeStack = 80 := by decide
  rw [hlt]
  refine ⟨fun r hr ↦ ?_, ?_, fun w hw r hr ↦ ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hsub _ _ (by decide) (by decide)
    · exact hsub _ _ (by decide) (by decide)
    · exact hsub _ _ (by decide) (by decide)
    · exact hsub _ _ (by decide) (by decide)
    · exact ⟨fun i hi ↦ hb.kept _ (hrok.1 i hi), hrok.2⟩
  · simp only [stackRegion, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, NativeRustcVm.Disjoint, List.Pairwise.nil,
      List.pairwise_cons, and_true, false_implies, implies_true]
    unfold NativeRustcVm.Apart
    rw [hst, e1, e2, e3]
    omega
  · simp only [stackRegion, List.mem_cons, List.not_mem_nil, or_false] at hw hr
    unfold Apart
    rcases hr with rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl <;>
      simp only [rhoRegion] <;> (try rw [e4]) <;> (try rw [hst]) <;> (try rw [e1]) <;>
      (try rw [e2]) <;> (try rw [e3]) <;> omega

theorem tailWords_le (m0 : MachineData) (t0 t1 t2 : EW) :
    ∀ p ∈ tailWords m0 t0 t1 t2, p.1 + 8 ≤ 2032 := by
  intro p hp
  simp only [tailWords, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- A range of the scratch misses the `TState` and its decoded area. -/
theorem sc_miss [Labels] (hpre : VerifyLayerPre a s c m0) {o n : Nat} (ho : o < 205824)
    (hon : o + n ≤ 205824) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (sA m0 + BitVec.ofNat 64 o) n q) :
    ¬InRange (tA m0) tstateBytes q ∧ ¬InRange a.words (8 * a.len) q := by
  have g := geo_of hpre
  obtain ⟨hdw, -, -, hds⟩ := dec_geo hpre
  have := g.hs; have := g.ht; have := g.htsc
  have hq' : InRange (sA m0 + BitVec.ofNat 64 o) n q := hq
  rw [Sym.inRange_iff (by rw [g.sa ho]; omega), g.sa ho] at hq'
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' : InRange (tA m0) 760 q := h
    rw [Sym.inRange_iff (by omega)] at h'; omega
  · have h' : InRange a.words (8 * a.len) q := h
    rw [Sym.inRange_iff hdw] at h'; omega

/-- A register a block set to a register's value. -/
theorem reg_of [Labels] {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    {r r' : XReg} (hm : Match (Env.ofMachine m rs) S m') (h : S.reg r = some (.reg r')) :
    m'.regs.getXReg r = m.regs.getXReg r' :=
  UInt64.toBitVec_inj.mp (hm.regs r _ h)

/-- A register a block loaded from a word of the frame. -/
theorem fw_reg [Labels] {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    {r : XReg} {o : Nat} {v : UInt64}
    (hm : Match (Env.ofMachine m ((base m0 2032, 2032) :: rs)) S m')
    (h : S.reg r = some (.load 0 o 8))
    (hw : NativeRustcVm.WordAt m.dmem (base m0 2032 + BitVec.ofNat 64 o) v) :
    m'.regs.getXReg r = v :=
  UInt64.toBitVec_inj.mp ((hm.regs r _ h).trans (fw_load rfl hw))

/-- A register a block set to a register's `eor` with a word of the frame. -/
theorem eor_fw [Labels] {m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    {r r' : XReg} {o : Nat} {v : UInt64}
    (hm : Match (Env.ofMachine m ((base m0 2032, 2032) :: rs)) S m')
    (h : S.reg r = some (.bin .eor .W64 (.reg r') (.load 0 o 8)))
    (hw : NativeRustcVm.WordAt m.dmem (base m0 2032 + BitVec.ofNat 64 o) v) :
    m'.regs.getXReg r = m.regs.getXReg r' ^^^ v := by
  apply UInt64.toBitVec_inj.mp
  rw [hm.regs r _ h, UInt64.toBitVec_xor]
  sym_simp
  rw [fw_load rfl hw]
  rfl

/-- **A call to `EW::mul`** from the body. -/
theorem mul_call [Host] (hpre : VerifyLayerPre a s c m0)
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {st : MachineState} {next : Int64}
    {env : Env} (hpc : PcOk env (.call NativeRustcVmArm.Vm.EWMul.entryLabel) next st) (hb : Body m0 st.data)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = next → Body m0 st'.data →
      st'.data.regs.X0 =
        (EW.mul ⟨st.data.regs.X0, st.data.regs.X1⟩ ⟨st.data.regs.X2, st.data.regs.X3⟩).c0 →
      st'.data.regs.X1 =
        (EW.mul ⟨st.data.regs.X0, st.data.regs.X1⟩ ⟨st.data.regs.X2, st.data.regs.X3⟩).c1 →
      Saved st.data st'.data →
      SameOutside st.data.dmem st'.data.dmem (fun q ↦
        InRange (stackBelow st.data ewMulStack) ewMulStack q ∨ False) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st :=
  call_then hpc hmul (hb.stackOk hpre.1 (by decide) (by decide)) fun st' hpc' ⟨h0, h1, hs, hsv⟩ ↦
    have hs' : SameOutside st.data.dmem st'.data.dmem fun q ↦
        InRange (stackBelow st.data ewMulStack) ewMulStack q ∨ False :=
      NativeRustcVm.SameOutside.mono hs fun q h ↦ Or.inl h
    cont st' hpc' (Body.call (geo_of hpre) hb (by decide) (W := fun _ ↦ False) hsv hs'
      fun _ h ↦ False.elim h) h0 h1 hsv hs'

/-- **A range kept by a callee** that writes only its stack, as numbers. -/
theorem same_stack (g : Geo m0) {m : MachineData} {d d' : DataMem}
    (hsp : m.regs.SP.toBitVec = base m0 2032) {n : Nat} (hn : n ≤ 1616)
    (hs : SameOutside d d' fun q ↦ InRange (stackBelow m n) n q ∨ False) {x : BitVec 64}
    {len : Nat} (hx : x.toNat + len ≤ 2 ^ 64)
    (h : x.toNat + len ≤ m0.regs.SP.toNat - 2032 - n ∨ m0.regs.SP.toNat - 2032 ≤ x.toNat) :
    Same d d' x len := by
  have := g.hN; have := Geo.sp_lt m0; have hst := g.stk hsp hn
  refine NativeRustcVm.Layout.Same.of_sameOutside hs fun j hj hq ↦ hq.elim (fun hq ↦ ?_) id
  exact notIn (by rw [hst]; omega) (by omega) (by rw [hst]; omega) hq

/-- What the tail keeps between its calls. -/
structure TailLive (m0 : MachineData) (a : DecArea) (s' : TState) (t0 t1 t2 : EW)
    (mu point lw : Array EW) (d : DataMem) : Prop where
  fw : Bus.FrameWords d (base m0 2032) (tailWords m0 t0 t1 t2)
  mu : NativeRustcVm.BufEWAt d (base m0 2032 + BitVec.ofNat 64 968) 16 mu.toList
  pt : NativeRustcVm.EWsAt d (base m0 2032 + BitVec.ofNat 64 1232) point.toList
  ts : TStateAt d (tA m0) a s'
  w : NativeRustcVm.EWsAt d (sA m0 + BitVec.ofNat 64 25600) (keccakLinearTranspose lw).toList

/-- The tail's facts kept by `EW::mul`. -/
theorem TailLive.mul [Labels] (hpre : VerifyLayerPre a s c m0) {s' : TState} {t0 t1 t2 : EW}
    {mu point lw : Array EW} {m m' : MachineData} (hb : Body m0 m) (hps : point.size ≤ 30)
    (hlts : (keccakLinearTranspose lw).size = 1600)
    (h : TailLive m0 a s' t0 t1 t2 mu point lw m.dmem) (hk : Kept m.dmem m'.dmem)
    (hs : SameOutside m.dmem m'.dmem fun q ↦
      InRange (stackBelow m ewMulStack) ewMulStack q ∨ False) :
    TailLive m0 a s' t0 t1 t2 mu point lw m'.dmem := by
  have g := geo_of hpre
  have := g.hN; have := Geo.sp_lt m0; have hbN := g.bN; have := g.hs; have := g.hss
  have hn : ewMulStack ≤ 1616 := by decide
  have hm : ewMulStack = 592 := by decide
  have hfr := same_stack g hb.sp hn hs (x := base m0 2032) (len := 2032) (by rw [hbN]; omega)
    (by rw [hbN]; omega)
  refine ⟨FrameWords.of_same h.fw hfr (tailWords_le m0 t0 t1 t2),
    NativeRustcVm.Layout.BufEWAt.of_same h.mu (hfr.sub (o := 968) (k := 264) (by omega))
      (by omega),
    ewsAt_same h.pt (hfr.sub (o := 1232) (k := 480) (by omega))
      (by rw [Array.length_toList]; omega),
    tstate_keep hpre hb.sp hn hs hk (fun _ h ↦ h.elim) h.ts,
    ewsAt_same h.w (same_stack g hb.sp hn hs
      (x := sA m0 + BitVec.ofNat 64 25600) (len := 25600) (by rw [g.sa (by omega)]; omega)
      (by rw [g.sa (by omega), hm]; omega)) (by rw [Array.length_toList, hlts])⟩

/-- The new value, limb by limb. -/
theorem value_eq (beta t0 t1 t2 : EW) :
    (⟨(EW.mul beta ⟨(EW.mul beta t2).c0 ^^^ t1.c0, (EW.mul beta t2).c1 ^^^ t1.c1⟩).c0 ^^^ t0.c0,
      (EW.mul beta ⟨(EW.mul beta t2).c0 ^^^ t1.c0, (EW.mul beta t2).c1 ^^^ t1.c1⟩).c1 ^^^ t0.c1⟩ :
      EW) = t0 + beta * (t1 + beta * t2) := by
  rw [ew_add t1, ew_add t0, UInt64.xor_comm t1.c0, UInt64.xor_comm t1.c1, UInt64.xor_comm t0.c0,
    UInt64.xor_comm t0.c1]
  rfl

/-- A range of the claim misses the `TState` and its decoded area. -/
theorem cl_miss [Labels] (hpre : VerifyLayerPre a s c m0) {o n : Nat} (ho : o < 768)
    (hon : o + n ≤ 768) {q : BitVec 64}
    (hq : InRange (cA m0 + BitVec.ofNat 64 o) n q) :
    ¬InRange (tA m0) tstateBytes q ∧ ¬InRange a.words (8 * a.len) q := by
  have g := geo_of hpre
  obtain ⟨hdw, -, hdc, -⟩ := dec_geo hpre
  have := g.hc; have := g.ht; have := g.htc
  rw [Sym.inRange_iff (by rw [g.ca ho]; omega), g.ca ho] at hq
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' : InRange (tA m0) 760 q := h
    rw [Sym.inRange_iff (by omega)] at h'; omega
  · have h' : InRange a.words (8 * a.len) q := h
    rw [Sym.inRange_iff hdw] at h'; omega

/-- **The tail's facts kept by a write into the claim.** -/
theorem TailLive.claimW [Labels] (hpre : VerifyLayerPre a s c m0) {s' : TState} {t0 t1 t2 : EW}
    {mu point lw : Array EW} {d d' : DataMem} (hps : point.size ≤ 30)
    (h : TailLive m0 a s' t0 t1 t2 mu point lw d) (hk : Kept d d') {o n : Nat} (ho : o < 768)
    (hon : o + n ≤ 768) (hs : SameOutside d d' (InRange (cA m0 + BitVec.ofNat 64 o) n)) :
    TailLive m0 a s' t0 t1 t2 mu point lw d' := by
  have g := geo_of hpre
  have := g.hN; have := Geo.sp_lt m0; have hbN := g.bN; have := g.hs; have := g.hcsc
  have := g.hc
  have hfr : Same d d' (base m0 2032) 2032 :=
    NativeRustcVm.Layout.Same.of_sameOutside hs fun j hj ↦ c_not_frame g hj ho hon
  have hlts' := NativeRustcVm.KeccakGkr.linearTranspose_size' lw
  refine ⟨FrameWords.of_same h.fw hfr (tailWords_le m0 t0 t1 t2),
    NativeRustcVm.Layout.BufEWAt.of_same h.mu (hfr.sub (o := 968) (k := 264) (by omega))
      (by omega),
    ewsAt_same h.pt (hfr.sub (o := 1232) (k := 480) (by omega))
      (by rw [Array.length_toList]; omega),
    NativeRustcVm.Transcript.TStateAt.frame h.ts hk (fun q hq ↦ cl_miss hpre ho hon hq) hs,
    ewsAt_same h.w (NativeRustcVm.Layout.Same.of_sameOutside hs fun j hj ↦ ?_)
      (by rw [Array.length_toList, hlts'])⟩
  rw [NativeRustcVm.addr_add_add]
  have : j < 25600 := by simpa using hj
  exact notIn (by rw [g.ca ho]; omega) (by omega) (by rw [g.ca ho]; omega)

/-- **The claim's bytes before `o`** kept by a write from `o`. -/
theorem claim_keep {d d' : DataMem} (g : Geo m0) {o n : Nat} (ho : o < 768) (hon : o + n ≤ 768)
    (hs : SameOutside d d' (InRange (cA m0 + BitVec.ofNat 64 o) n)) {o' n' : Nat}
    (hle : o' + n' ≤ o) : Same d d' (cA m0 + BitVec.ofNat 64 o') n' := by
  have := g.hc
  refine NativeRustcVm.Layout.Same.of_sameOutside hs fun j hj ↦ ?_
  rw [NativeRustcVm.addr_add_add]
  exact notIn (by rw [g.ca ho]; omega) (by omega) (by rw [g.ca ho]; omega)

/-- **The tail**, from `.LVerifyLayer_35`. -/
theorem tail [Host] {k : Nat} (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    (hlt : ∀ ws, Spec (label NativeRustcVmArm.Vm.LinearTranspose.entryLabel) (LinearTransposePre ws) (LinearTransposePost ws))
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hext : Spec (label NativeRustcVmArm.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b62Offset)) (hb : Body m0 st.data)
    {t0 t1 t2 beta : EW} {mu point lw : Array EW} {s' : TState}
    (hrun : runL s c m0 =
      some (⟨t0 + beta * (t1 + beta * t2), mu, point, keccakLinearTranspose lw⟩, s'))
    (hfw : Bus.FrameWords st.data.dmem (base m0 2032) (tailWords m0 t0 t1 t2))
    (hx23 : st.data.regs.X23 = beta.c0) (hx25 : st.data.regs.X25 = beta.c1)
    (hx24 : st.data.regs.X24.toNat = point.size) (hps : point.size ≤ 30)
    (hlws : lw.size = 1600)
    (hlw : NativeRustcVm.EWsAt st.data.dmem (sA m0 + BitVec.ofNat 64 51200) lw.toList)
    (hmu : NativeRustcVm.BufEWAt st.data.dmem (base m0 2032 + BitVec.ofNat 64 968) 16 mu.toList)
    (hpt : NativeRustcVm.EWsAt st.data.dmem (base m0 2032 + BitVec.ofNat 64 1232) point.toList)
    (hts : TStateAt st.data.dmem (tA m0) a s') :
    Eventually (step1 Host.exe) (Goal a s c m0) st := by
  have g := geo_of hpre
  have hS := hpre.1
  have := g.hN; have := Geo.sp_lt m0; have hbN := g.bN
  -- `b62`: `linear_transpose`'s arguments.
  have hwf := wf_fr hpre hb
  refine exec_at (blk hp b62_in_code (by simp [b62])) e62 hwf hpc (match_fr hpre hb)
    fun st1 hm1 hpc1 ↦ ?_
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hb1 : Body m0 st1.data :=
    Fr.ofBlock hb (match_fr hpre hb) hm1 hwf rfl rfl rfl (fun r hr ↦ by cases hr)
  have hbase : (Env.ofMachine st.data [(base m0 2032, 2032)]).base 0 = base m0 2032 := rfl
  have hl120 := fw_load hbase
    (FrameWords.get hfw (o := 120) (v := m0.regs.X4) (by simp [tailWords]))
  have hl88 := fw_load hbase (FrameWords.get hfw (o := 88)
    (v := UInt64.ofBitVec (sA m0 + BitVec.ofNat 64 51200))
    (by simp [tailWords]))
  have hx0 : st1.data.regs.X0.toBitVec = sA m0 + BitVec.ofNat 64 51200 := by
    have h := hm1.regs .X0 _ rfl; sym_simp at h; rw [hl88] at h; exact h
  have hx1 : st1.data.regs.X1.toBitVec = sA m0 + BitVec.ofNat 64 76800 := by
    have h := hm1.regs .X1 _ rfl; sym_simp at h; rw [hl120] at h; exact h
  have hx2 : st1.data.regs.X2.toBitVec = sA m0 + BitVec.ofNat 64 102400 := by
    have h := hm1.regs .X2 _ rfl; sym_simp at h; rw [hl120] at h; exact h
  have hx3 : st1.data.regs.X3.toBitVec = sA m0 + BitVec.ofNat 64 25600 := by
    have h := hm1.regs .X3 _ rfl; sym_simp at h; rw [hl120] at h; exact h
  have hpre1 : LinearTransposePre lw st1.data := by
    refine ⟨hb1.stackOk hS (by decide) (by decide), ?_, hlws, ?_, ?_⟩
    · have h := same_rs hpre hb1 (r := rhoRegion) (by simp)
      exact NativeRustcVm.Layout.BytesAt.of_same hpre.2.2.2.1 h
        (le_of_eq (by rw [show rhoBytes.length = 100 by decide]; rfl))
    · rw [hx0, hd1]; exact hlw
    · rw [hx0, hx1, hx2, hx3]; exact lt_areas hpre hb1
  refine call_then hpc1 (hlt lw) hpre1 fun st2 hpc2 hpost2 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b62Offset + b62.length = k + NativeRustcVmArm.Vm.VerifyLayer.b63Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b62_next]] at hpc2
  obtain ⟨hout2, hwr2, hsv2⟩ := hpost2
  have hs2 := writes_split hwr2
  rw [hx1, hx2, hx3] at hs2
  rw [hx3] at hout2
  have hlts : linearTransposeStack ≤ 1616 := by decide
  have hW2 : ∀ q, NativeRustcVm.InAny [⟨sA m0 + BitVec.ofNat 64 76800, 25600⟩,
      ⟨sA m0 + BitVec.ofNat 64 102400, 5120⟩, ⟨sA m0 + BitVec.ofNat 64 25600, 25600⟩] q →
      outs m0 q := by
    rintro q ⟨r, hr, hq⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [NativeRustcVm.Region.Holds] at hq <;>
      exact in_layer g (by omega) (by omega) hq
  have hb2 : Body m0 st2.data := Body.call g hb1 hlts hsv2 hs2 hW2
  have hfr2 : Same st1.data.dmem st2.data.dmem (base m0 2032) 2032 :=
    same_frame g hb1.sp hlts hs2 fun j hj ⟨r, hr, hq⟩ ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        simp only [NativeRustcVm.Region.Holds, NativeRustcVm.KeccakGkr.weightsBytes] at hq <;>
        exact s_not_frame g hj (by omega) (by omega) hq
  rw [← hd1] at hfw hmu hpt hts
  have hfw2 := FrameWords.of_same hfw hfr2 (tailWords_le m0 t0 t1 t2)
  have hmu2 := NativeRustcVm.Layout.BufEWAt.of_same hmu (hfr2.sub (o := 968) (k := 264) (by omega))
    (by omega)
  have hpt2 := ewsAt_same hpt (hfr2.sub (o := 1232) (k := 480) (by omega))
    (by rw [Array.length_toList]; omega)
  obtain ⟨hdw, hdws, hdc, hds⟩ := dec_geo hpre
  have hts2 := tstate_keep hpre hb1.sp hlts hs2 hsv2.2.2 (fun q ⟨r, hr, hq⟩ ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        simp only [NativeRustcVm.Region.Holds, NativeRustcVm.KeccakGkr.weightsBytes] at hq <;>
        exact sc_miss hpre (by omega) (by omega) hq) hts
  have hr2 : ∀ r ∈ [XReg.X23, .X24, .X25], st2.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact (hsv2.1 _ rfl).trans (UInt64.toBitVec_inj.mp (hm1.regs _ (.reg _) rfl))
  have hlts' := NativeRustcVm.KeccakGkr.linearTranspose_size' lw
  have hL2 : TailLive m0 a s' t0 t1 t2 mu point lw st2.data.dmem := ⟨hfw2, hmu2, hpt2, hts2, hout2⟩
  -- `b63`: `β · t2`.
  have hwf2 := wf_fr hpre hb2
  refine exec_at (blk hp b63_in_code (by simp [b63])) e63 hwf2 hpc2 (match_fr hpre hb2)
    fun st3 hm3 hpc3 ↦ ?_
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 rfl
  have hb3 : Body m0 st3.data :=
    Fr.ofBlock hb2 (match_fr hpre hb2) hm3 hwf2 rfl rfl rfl (fun r hr ↦ by cases hr)
  have hb2e : (Env.ofMachine st2.data [(base m0 2032, 2032)]).base 0 = base m0 2032 := rfl
  have e30 : st3.data.regs.X0 = beta.c0 :=
    (reg_of (r := .X0) (r' := .X23) hm3 rfl).trans ((hr2 .X23 (by simp)).trans hx23)
  have e31 : st3.data.regs.X1 = beta.c1 :=
    (reg_of (r := .X1) (r' := .X25) hm3 rfl).trans ((hr2 .X25 (by simp)).trans hx25)
  have e32 : st3.data.regs.X2 = t2.c0 :=
    fw_reg (r := .X2) hm3 rfl (FrameWords.get hL2.fw (o := 24) (v := t2.c0) (by simp [tailWords]))
  have e33 : st3.data.regs.X3 = t2.c1 :=
    fw_reg (r := .X3) hm3 rfl (FrameWords.get hL2.fw (o := 16) (v := t2.c1) (by simp [tailWords]))
  have hL3 : TailLive m0 a s' t0 t1 t2 mu point lw st3.data.dmem := by rw [hd3]; exact hL2
  refine mul_call hpre hmul hpc3 hb3 fun st4 hpc4 hb4 h40 h41 hsv4 hs4 ↦ ?_
  rw [e30, e31, e32, e33] at h40 h41
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b63Offset + b63.length = k + NativeRustcVmArm.Vm.VerifyLayer.b64Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b63_next]] at hpc4
  have hL4 := TailLive.mul hpre hb3 hps hlts' hL3 hsv4.2.2 hs4
  have hr4 : ∀ r ∈ [XReg.X23, .X24, .X25], st4.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact (hsv4.1 _ rfl).trans ((Bus.keep_reg hm3 rfl).trans (hr2 _ (by simp)))
  -- `b64`: `β · (t1 + β · t2)`.
  have hwf4 := wf_fr hpre hb4
  refine exec_at (blk hp b64_in_code (by simp [b64])) e64 hwf4 hpc4 (match_fr hpre hb4)
    fun st5 hm5 hpc5 ↦ ?_
  have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq hwf4 rfl
  have hb5 : Body m0 st5.data :=
    Fr.ofBlock hb4 (match_fr hpre hb4) hm5 hwf4 rfl rfl rfl (fun r hr ↦ by cases hr)
  have e50 : st5.data.regs.X0 = beta.c0 :=
    (reg_of (r := .X0) (r' := .X23) hm5 rfl).trans ((hr4 .X23 (by simp)).trans hx23)
  have e51 : st5.data.regs.X1 = beta.c1 :=
    (reg_of (r := .X1) (r' := .X25) hm5 rfl).trans ((hr4 .X25 (by simp)).trans hx25)
  have e52 : st5.data.regs.X2 = (EW.mul beta t2).c0 ^^^ t1.c0 :=
    (eor_fw (r := .X2) (r' := .X0) hm5 rfl
      (FrameWords.get hL4.fw (o := 40) (v := t1.c0) (by simp [tailWords]))).trans
      (by rw [← h40]; rfl)
  have e53 : st5.data.regs.X3 = (EW.mul beta t2).c1 ^^^ t1.c1 :=
    (eor_fw (r := .X3) (r' := .X1) hm5 rfl
      (FrameWords.get hL4.fw (o := 32) (v := t1.c1) (by simp [tailWords]))).trans
      (by rw [← h41]; rfl)
  have hL5 : TailLive m0 a s' t0 t1 t2 mu point lw st5.data.dmem := by rw [hd5]; exact hL4
  refine mul_call hpre hmul hpc5 hb5 fun st6 hpc6 hb6 h60 h61 hsv6 hs6 ↦ ?_
  rw [e50, e51, e52, e53] at h60 h61
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b64Offset + b64.length = k + NativeRustcVmArm.Vm.VerifyLayer.b65Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b64_next]] at hpc6
  have hL6 := TailLive.mul hpre hb5 hps hlts' hL5 hsv6.2.2 hs6
  have hr6 : ∀ r ∈ [XReg.X23, .X24, .X25], st6.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact (hsv6.1 _ rfl).trans ((Bus.keep_reg hm5 rfl).trans (hr4 _ (by simp)))
  -- `b65`: the value stored, `memcpy`'s arguments.
  have g' := g
  have hwfc := wf_claim hpre hb6
  have h136 := FrameWords.get hL6.fw (o := 136) (v := m0.regs.X3) (by simp [tailWords])
  have hmc := match_claimF hpre hb6 h136
  refine exec_at (blk hp b65_in_code (by simp [b65])) e65 hwfc hpc6 hmc fun st7 hm7 hpc7 ↦ ?_
  have hb7 : Body m0 st7.data := Body.claimBlock hpre hb6 hmc hm7 rfl rfl
  have hk7 : SameOutside st6.data.dmem st7.data.dmem (fun q ↦ InRange (cA m0) 16 q) := by
    refine NativeRustcVm.SameOutside.mono (hm7.sameOutside hwfc)
      fun q ⟨w, hw, b, sz, hb', h1, h2⟩ ↦ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    have := g.hc
    rcases hw with rfl | rfl <;>
    · simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Prod.mk.injEq] at hb'
      obtain ⟨rfl, rfl⟩ := hb'
      simp only at h1 h2
      rw [Sym.inRange_iff (by omega)]
      omega
  have hval : NativeRustcVm.EWAt st7.data.dmem (cA m0) (t0 + beta * (t1 + beta * t2)) := by
    rw [← value_eq, NativeRustcVm.ewAt_iff]
    have hw0 := Bus.wordAt_write (r := 1) (o := 0) hm7 rfl (by omega)
      (v := .bin .eor .W64 (.reg .X0)
      (.load 0 56 8)) (fun i hi ↦ by
        simp only [findWrite_cons]; interval_cases i <;> rfl)
    have hw1 := Bus.wordAt_write (r := 1) (o := 8) hm7 rfl (by omega)
      (v := .bin .eor .W64 (.reg .X1)
      (.load 0 48 8)) (fun i hi ↦ by
        simp only [findWrite_cons]; interval_cases i <;> rfl)
    have l56 : (Sym.load 0 56 8).eval
        (Env.ofMachine st6.data [(base m0 2032, 2032), (cA m0, 768)]) =
        t0.c0.toBitVec :=
      fw_load rfl (FrameWords.get hL6.fw (o := 56) (v := t0.c0) (by simp [tailWords]))
    have l48 : (Sym.load 0 48 8).eval
        (Env.ofMachine st6.data [(base m0 2032, 2032), (cA m0, 768)]) =
        t0.c1.toBitVec :=
      fw_load rfl (FrameWords.get hL6.fw (o := 48) (v := t0.c1) (by simp [tailWords]))
    rw [Bus.eval_eor _ _ _ t0.c0 l56] at hw0
    rw [Bus.eval_eor _ _ _ t0.c1 l48] at hw1
    have q0 : UInt64.ofBitVec
        ((Env.ofMachine st6.data [(base m0 2032, 2032), (cA m0, 768)]).regs .X0) =
        st6.data.regs.X0 := rfl
    have q1 : UInt64.ofBitVec
        ((Env.ofMachine st6.data [(base m0 2032, 2032), (cA m0, 768)]).regs .X1) =
        st6.data.regs.X1 := rfl
    rw [q0, h60] at hw0
    rw [q1, h61] at hw1
    rw [NativeRustcVm.addr_add_zero] at hw0
    exact ⟨hw0, hw1⟩
  have hL7 : TailLive m0 a s' t0 t1 t2 mu point lw st7.data.dmem :=
    TailLive.claimW hpre hps hL6 (hm7.kept hwfc) (o := 0) (n := 16) (by omega) (by omega)
      (by rw [NativeRustcVm.addr_add_zero]; exact hk7)
  have hc := g.hc; have hcs := g.hcs
  -- `memcpy`: the instance weights into the claim.
  have h7x0 : st7.data.regs.X0.toBitVec = cA m0 + BitVec.ofNat 64 16 := by
    have h := hm7.regs .X0 _ rfl
    rw [show Sym.eval _ (Sym.load 0 80 8) = _ from fw_load rfl
      (FrameWords.get hL6.fw (o := 80) (v := UInt64.ofBitVec (cA m0 + BitVec.ofNat 64 16))
        (by simp [tailWords]))] at h
    exact h
  have h7x1 : st7.data.regs.X1.toBitVec = base m0 2032 + BitVec.ofNat 64 968 := by
    have h := hm7.regs .X1 _ rfl; sym_simp at h
    show (st7.data.regs.getXReg .X1).toBitVec = _; rw [h]; rfl
  have h7x2 : st7.data.regs.X2.toNat = 264 := by
    show (st7.data.regs.getXReg .X2).toBitVec.toNat = 264
    rw [hm7.regs .X2 _ rfl]; rfl
  have hcok := hpre.2.2.2.2.2.2.2.2.2.1 ⟨cA m0, claimBytes⟩ (by simp)
  have e16 := g.ca (o := 16) (by omega)
  have e968 := g.fa (o := 968) (by omega)
  have hmpre : MemcpyPre st7.data := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [h7x0, h7x1, h7x2]
    · intro i hi
      rw [NativeRustcVm.addr_add_add]
      exact hb7.kept _ (hcok.1 _ (show 16 + i < claimBytes by simp only [claimBytes]; omega))
    · intro i hi
      rw [NativeRustcVm.addr_add_add]
      exact hb7.kept _ ((frame_mapped hpre.1 (by decide)) _ (by omega))
    · show (cA m0 + BitVec.ofNat 64 16).toNat + 264 ≤ 2 ^ 64; rw [e16]; omega
    · show (base m0 2032 + BitVec.ofNat 64 968).toNat + 264 ≤ 2 ^ 64; rw [e968]; omega
    · show _ ∨ _; rw [e16, e968]; omega
  refine call_then hpc7 hmemcpy hmpre fun st8 hpc8 ⟨_, hcp8, hs8, hsv8⟩ ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b65Offset + b65.length = k + NativeRustcVmArm.Vm.VerifyLayer.b66Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b65_next]] at hpc8
  rw [h7x0, h7x2] at hcp8 hs8
  rw [h7x1] at hcp8
  have hb8 : Body m0 st8.data := Body.call g hb7 (n := 0) (by omega) hsv8
    (NativeRustcVm.SameOutside.mono hs8 fun q h ↦ .inr h)
    fun q h ↦ .inr (.inr (.inl (by
      rw [Sym.inRange_iff (by rw [e16]; omega), e16] at h
      rw [Sym.inRange_iff (by simp only [claimBytes]; omega)]; simp only [claimBytes]; omega)))
  have hL8 := TailLive.claimW hpre hps hL7 hsv8.2.2 (o := 16) (n := 264) (by omega) (by omega) hs8
  have hmuc : NativeRustcVm.BufEWAt st8.data.dmem (cA m0 + BitVec.ofNat 64 16) 16 mu.toList :=
    BufEWAt.copy hL7.mu hcp8
  have hval8 := NativeRustcVm.Layout.EWAt.of_same hval
    (by have := claim_keep g (o := 16) (n := 264) (by omega) (by omega) hs8 (o' := 0) (n' := 16)
          (by omega)
        rwa [NativeRustcVm.addr_add_zero] at this) (Nat.le_refl _)
  -- `b66`: the point emptied, `extend`'s arguments.
  have hx19 : st8.data.regs.X19 = m0.regs.X3 :=
    (hsv8.1 .X19 rfl).trans (fw_reg (r := .X19) hm7 rfl h136)
  have hx24' : st8.data.regs.X24.toNat = point.size := by
    have h := (hsv8.1 .X24 rfl).trans ((reg_of (r := .X24) (r' := .X24) hm7 rfl).trans
      (hr6 .X24 (by simp)))
    show (st8.data.regs.getXReg .X24).toNat = _
    rw [h]
    exact hx24
  have hwf8 := wf_claim hpre hb8
  have hm8 := match_claim19 hpre hb8 hx19
  refine exec_at (blk hp b66_in_code (by simp [b66])) e66 hwf8 hpc8 hm8 fun st9 hm9 hpc9 ↦ ?_
  have hb9 : Body m0 st9.data := Body.claimBlock hpre hb8 hm8 hm9 rfl rfl
  have hk9 : SameOutside st8.data.dmem st9.data.dmem
      (fun q ↦ InRange (cA m0 + BitVec.ofNat 64 280) 8 q) := by
    refine NativeRustcVm.SameOutside.mono (hm9.sameOutside hwf8)
      fun q ⟨w, hw, b, sz, hb', h1, h2⟩ ↦ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    subst hw
    simp only [Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq, Prod.mk.injEq] at hb'
    obtain ⟨rfl, rfl⟩ := hb'
    simp only at h1 h2
    have e280 := g.ca (o := 280) (by omega)
    rw [Sym.inRange_iff (by rw [e280]; omega), e280]
    omega
  have hL9 := TailLive.claimW hpre hps hL8 (hm9.kept hwf8) (o := 280) (n := 8) (by omega)
    (by omega) hk9
  have hz9 : NativeRustcVm.WordAt st9.data.dmem (cA m0 + BitVec.ofNat 64 280) 0 :=
    Bus.wordAt_write (r := 1) (o := 280) hm9 rfl (by omega) (v := .lit 0) fun i hi ↦ by
      simp only [findWrite_cons]; interval_cases i <;> rfl
  have hval9 := NativeRustcVm.Layout.EWAt.of_same hval8
    (by have := claim_keep g (o := 280) (n := 8) (by omega) (by omega) hk9 (o' := 0) (n' := 16)
          (by omega)
        rwa [NativeRustcVm.addr_add_zero] at this) (Nat.le_refl _)
  have hmu9 := NativeRustcVm.Layout.BufEWAt.of_same hmuc
    (claim_keep g (o := 280) (n := 8) (by omega) (by omega) hk9 (o' := 16) (n' := 264) (by omega))
    (by omega)
  have e280 := g.ca (o := 280) (by omega)
  have e1232 := g.fa (o := 1232) (by omega)
  have h9x0 : st9.data.regs.X0.toBitVec = cA m0 + BitVec.ofNat 64 280 := by
    have h := hm9.regs .X0 _ rfl; sym_simp at h
    show (st9.data.regs.getXReg .X0).toBitVec = _; rw [h]; rfl
  have h9x1 : st9.data.regs.X1.toBitVec = base m0 2032 + BitVec.ofNat 64 1232 := by
    have h := hm9.regs .X1 _ rfl; sym_simp at h
    show (st9.data.regs.getXReg .X1).toBitVec = _; rw [h]; rfl
  have h9x2 : st9.data.regs.X2.toNat = point.size := by
    rw [← hx24']; exact congrArg BitVec.toNat (hm9.regs .X2 _ rfl)
  have hxpre : BufEWExtendPre 30 st9.data := by
    refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> simp only [h9x0, h9x1, h9x2]
    · rw [NativeRustcVm.wordOf_of_wordAt hz9]; decide
    · intro i hi
      rw [NativeRustcVm.addr_add_add]
      exact hb9.kept _ (hcok.1 _ (show 280 + i < claimBytes by simp only [claimBytes]; omega))
    · show (cA m0 + BitVec.ofNat 64 280).toNat + _ ≤ 2 ^ 64; rw [e280]; omega
    · intro i hi
      rw [NativeRustcVm.addr_add_add]
      exact hb9.kept _ ((frame_mapped hpre.1 (by decide)) _ (by omega))
    · show (base m0 2032 + BitVec.ofNat 64 1232).toNat + _ ≤ 2 ^ 64; rw [e1232]; omega
    · show _ ∨ _; rw [e280, e1232]; omega
  refine call_then hpc9 hext hxpre fun st10 hpc10 ⟨hx10, hs10, hsv10⟩ ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b66Offset + b66.length = k + NativeRustcVmArm.Vm.VerifyLayer.b67Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b66_next]] at hpc10
  rw [h9x0, h9x2, NativeRustcVm.wordOf_of_wordAt hz9] at hx10
  simp only [UInt64.toNat_zero, Nat.zero_add, hps, ↓reduceIte] at hx10
  obtain ⟨hx10, hpt10⟩ := hx10
  have hs10' : SameOutside st9.data.dmem st10.data.dmem
      (InRange (cA m0 + BitVec.ofNat 64 280) 488) := by
    refine NativeRustcVm.SameOutside.mono hs10 fun q h ↦ ?_
    rw [h9x0] at h
    exact h.elim id fun h ↦ absurd h (Bus.not_inRange_zero _ _)
  have hb10 : Body m0 st10.data := Body.call g hb9 (n := 0) (by omega) hsv10
    (NativeRustcVm.SameOutside.mono hs10' fun q h ↦ .inr h)
    fun q h ↦ .inr (.inr (.inl (by
      rw [Sym.inRange_iff (by rw [e280]; omega), e280] at h
      rw [Sym.inRange_iff (by simp only [claimBytes]; omega)]; simp only [claimBytes]; omega)))
  have hL10 := TailLive.claimW hpre hps hL9 hsv10.2.2 (o := 280) (n := 488) (by omega) (by omega)
    hs10'
  have hval10 := NativeRustcVm.Layout.EWAt.of_same hval9
    (by have := claim_keep g (o := 280) (n := 488) (by omega) (by omega) hs10' (o' := 0) (n' := 16)
          (by omega)
        rwa [NativeRustcVm.addr_add_zero] at this) (Nat.le_refl _)
  have hmu10 := NativeRustcVm.Layout.BufEWAt.of_same hmu9
    (claim_keep g (o := 280) (n := 488) (by omega) (by omega) hs10' (o' := 16) (n' := 264)
      (by omega)) (by omega)
  have hpts : (slice st9.data st9.data.regs.X1 st9.data.regs.X2).toList = point.toList := by
    unfold slice
    rw [h9x2, h9x1, List.toList_toArray]
    have := NativeRustcVm.ewsOf_of_ewsAt hL9.pt
    rwa [Array.length_toList] at this
  have hbuf0 : NativeRustcVm.bufEWOf st9.data.dmem (cA m0 + BitVec.ofNat 64 280) = [] := by
    unfold NativeRustcVm.bufEWOf
    rw [NativeRustcVm.wordOf_of_wordAt hz9]
    rfl
  rw [hbuf0, hpts, List.nil_append] at hpt10
  -- `b67`, `b68`: `Some(())`.
  have hwf10 := wf_fr hpre hb10
  refine exec_at (blk hp b67_in_code (by simp [b67])) e67 hwf10 hpc10 (match_fr hpre hb10)
    fun st11 hm11 hpc11 ↦ ?_
  have hd11 : st11.data.dmem = st10.data.dmem := hm11.dmem_eq hwf10 rfl
  have hb11 : Body m0 st11.data :=
    Fr.ofBlock hb10 (match_fr hpre hb10) hm11 hwf10 rfl rfl rfl (fun r hr ↦ by cases hr)
  have hpc11' : st11.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b68Offset) := by
    rw [hpc11]
    sym_simp
    rw [show (Env.ofMachine st10.data [(base m0 2032, 2032)]).regs .X0 = st10.data.regs.X0.toBitVec
      from rfl, hx10]
    rfl
  have hwf11 := wf_fr hpre hb11
  refine exec_at (blk hp b68_in_code (by simp [b68])) e68 hwf11 hpc11' (match_fr hpre hb11)
    fun st12 hm12 hpc12 ↦ ?_
  have hd12 : st12.data.dmem = st11.data.dmem := hm12.dmem_eq hwf11 rfl
  have hb12 : Body m0 st12.data :=
    Fr.ofBlock hb11 (match_fr hpre hb11) hm12 hwf11 rfl rfl rfl (fun r hr ↦ by cases hr)
  have hpc12' : st12.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b70Offset) := hpc12.trans (label38 hp)
  have hd : st12.data.dmem = st10.data.dmem := hd12.trans hd11
  refine exit hp hpre hpc12' hb12 ?_ fun c' s'' hr ↦ ?_
  · rw [hrun]
    apply UInt64.toBitVec_inj.mp
    rw [show st12.data.regs.X0 = st12.data.regs.getXReg .X0 from rfl, hm12.regs .X0 _ rfl]
    rfl
  · rw [hrun, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    rw [hd]
    exact ⟨hL10.ts, ⟨hval10, hmu10, hpt10⟩, NativeRustcVm.KeccakGkr.linearTranspose_size' lw,
      hL10.w⟩

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
