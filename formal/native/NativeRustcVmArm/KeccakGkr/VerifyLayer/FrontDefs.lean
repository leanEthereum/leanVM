module

public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.Tail
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.FrontModel
public import NativeRustcVmArm.Tables.Frame

/-!
# `verify_layer`'s front: the frame and its calls

Up to the layer's weights the body writes its frame, the `TState` and the scratch's equality
kernel only (`fouts`, `FB`, a `Body` by `FB.body`). The entry's context (`ctx`), the calls from
the frame: a leaf (`leaf_call`, its stack only), `read_scalars` into the frame (`rs_call`), a
call writing a range of the frame and the outputs (`local_call`); a range of the frame kept by a
call or a block (`keep_call`, `keep_blk`), the `TState` kept (`ts_blk`, `ts_call`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt claimBytes)
open NativeRustcVmArm.Sumcheck (Ctx At)
open NativeRustcVmArm.Bus.Gkr

@[expose] public section

/-- The front's outputs: the `TState`, the scratch's equality kernel. -/
def fouts (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (tA m0) tstateBytes q ∨ InRange (sA m0 + BitVec.ofNat 64 107520) 32768 q

/-- **The front's frame.** -/
abbrev FB (m0 m : MachineData) : Prop := Fr m0 2032 verifyLayerStack slots [] (fouts m0) m

/-- The frame's byte `o`. -/
abbrev loc (m0 : MachineData) (o : Nat) : BitVec 64 := base m0 2032 + BitVec.ofNat 64 o

end

public section

/-- `cmp w0, #0` of `okWord b`: `b` false. -/
theorem okw_eq0 (b : Bool) :
    CmpOp.eq.apply .W32 (okWord b).toBitVec (BitVec.ofNat 64 0) = !b := by
  cases b <;> rfl

end

public section

theorem le_rs : 2032 + readScalarsStack ≤ verifyLayerStack := by decide
theorem le_grind : 2032 + grindStack ≤ verifyLayerStack := by decide
theorem le_sq : 2032 + squeezeStack ≤ verifyLayerStack := by decide
theorem le_iw : 2032 + instanceWeightsStack ≤ verifyLayerStack := by decide
theorem le_sp : 2032 + sumcheckPlainStack ≤ verifyLayerStack := by decide
theorem le_sl : 2032 + sumcheckLayerStack ≤ verifyLayerStack := by decide
theorem le_pe : 2032 + polyEvalStack ≤ verifyLayerStack := by decide
theorem le_ek : 2032 + eqKernelStack ≤ verifyLayerStack := by decide
theorem le_dot : 2032 + dotStack ≤ verifyLayerStack := by decide
theorem le_mul : 2032 + ewMulStack ≤ verifyLayerStack := by decide
theorem le_sum : 2032 + sumEStack ≤ verifyLayerStack := by decide
theorem le_bl : 2032 + bitLengthStack ≤ verifyLayerStack := by decide
theorem N_ge : 2032 ≤ verifyLayerStack := by decide
theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 2032 := by decide

/-- Bytes of the frame below the slots. -/
theorem slots_lo {o n : Nat} (h : o + n ≤ 1936) : ∀ p ∈ slots, o + n ≤ p.1 ∧ p.1 + 8 ≤ 2032 :=
  fun p hp ↦ ⟨by have := (slots_bound p hp).1; omega, (slots_bound p hp).2⟩

section
variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

theorem pre_stack (h : VerifyLayerPre a s c m0) : StackOk m0 verifyLayerStack := h.1
theorem pre_rc (h : VerifyLayerPre a s c m0) : RcAt m0 verifyLayerStack := h.2.1
theorem pre_proj (h : VerifyLayerPre a s c m0) : ProjectAt m0 := h.2.2.1
theorem pre_ts (h : VerifyLayerPre a s c m0) : TStateAt m0.dmem (tA m0) a s := h.2.2.2.2.1
theorem pre_claim (h : VerifyLayerPre a s c m0) : ClaimAt m0.dmem (cA m0) c := h.2.2.2.2.2.1
theorem pre_w (h : VerifyLayerPre a s c m0) :
    WeightsAt m0.dmem (sA m0 + BitVec.ofNat 64 25600) c := h.2.2.2.2.2.2.1
theorem pre_step (h : VerifyLayerPre a s c m0) : m0.regs.X2.toNat < 12 := h.2.2.2.2.2.2.2.1
theorem pre_seg (h : VerifyLayerPre a s c m0) : SegmentsFit m0.regs.X1.toNat c :=
  h.2.2.2.2.2.2.2.2.1
theorem pre_areas (h : VerifyLayerPre a s c m0) :
    Areas m0 verifyLayerStack [⟨tA m0, tstateBytes⟩, ⟨cA m0, claimBytes⟩,
      ⟨sA m0, NativeRustcVm.KeccakGkr.scratchBytes⟩]
      [a.region, rcRegion, projectRegion, rhoRegion] := h.2.2.2.2.2.2.2.2.2

/-- The `TState` apart from the stack and the round constants. -/
theorem tok (h : VerifyLayerPre a s c m0) : TStateOk m0 (tA m0) a verifyLayerStack := by
  have hA := pre_areas h
  exact ⟨areas_stack hA (w := ⟨tA m0, tstateBytes⟩) (by simp),
    NativeRustcVm.Apart.symm (hA.2.2 _ List.mem_cons_self a.region (by simp)),
    hA.2.2 ⟨tA m0, tstateBytes⟩ (by simp) rcRegion (by simp)⟩

/-- **The entry's context.** -/
theorem ctx (h : VerifyLayerPre a s c m0) : Ctx m0 (tA m0) a verifyLayerStack 2032 :=
  ctx_of h.1 h.2.1 (pre_ts h) (tok h) N_ge rfl

omit [Labels] in
/-- A range of the scratch is not the frame's. -/
theorem scr_not_frame (g : Geo m0) {o n : Nat} (ho : o < 205824) (hon : o + n ≤ 205824)
    {q : BitVec 64}
    (hq : InRange (sA m0 + BitVec.ofNat 64 o) n q) : ¬InRange (base m0 2032) 2032 q := by
  have := g.hN; have := Geo.sp_lt m0; have hb := g.bN; have := g.hs; have := g.hss
  rw [Sym.inRange_iff (by rw [g.sa (by omega)]; omega), g.sa (by omega)] at hq
  rw [Sym.inRange_iff (by rw [hb]; omega), hb]
  omega

/-- A range of the scratch is not the round constants'. -/
theorem scr_not_rc (h : VerifyLayerPre a s c m0) {o n : Nat} (ho : o < 205824)
    (hon : o + n ≤ 205824)
    {q : BitVec 64} (hq : InRange (sA m0 + BitVec.ofNat 64 o) n q) : ¬InRange rcAddr 192 q := by
  have g := geo_of h
  have hA := pre_areas h
  have hap := hA.2.2 ⟨sA m0, NativeRustcVm.KeccakGkr.scratchBytes⟩ (by simp) rcRegion (by simp)
  have hrc := (hA.1 rcRegion (by simp)).2
  unfold Apart at hap
  unfold NativeRustcVm.NoWrap at hrc
  simp only [rcRegion, NativeRustcVm.KeccakGkr.scratchBytes] at hap hrc
  have := g.hs
  rw [Sym.inRange_iff (by rw [g.sa (by omega)]; omega), g.sa (by omega)] at hq
  rw [Sym.inRange_iff hrc]
  omega

theorem fouts_not_frame (h : VerifyLayerPre a s c m0) :
    ∀ q, fouts m0 q → ¬InRange (base m0 2032) 2032 q := fun _ hq ↦
  hq.elim (fun hq ↦ tstate_not_frame (ctx h) hq)
    (scr_not_frame (geo_of h) (by omega) (by omega))

theorem fouts_not_rc (h : VerifyLayerPre a s c m0) : ∀ q, fouts m0 q → ¬InRange rcAddr 192 q :=
  fun _ hq ↦ hq.elim (fun hq ↦ (ctx h).not_rc_tstate hq) (scr_not_rc h (by omega) (by omega))

theorem fouts_outs (h : VerifyLayerPre a s c m0) : ∀ q, fouts m0 q → outs m0 q := fun q hq ↦
  hq.elim (fun hq ↦ .inr (.inl hq)) fun hq ↦
    in_layer (geo_of h) (o := 107520) (n := 32768) (by omega) (by omega) hq

/-- **The body** of a front's frame. -/
theorem FB.body (h : VerifyLayerPre a s c m0) {m : MachineData} (hb : FB m0 m) : Body m0 m :=
  Bus.Fr.mono hb (fouts_outs h)

/-- A state of the front's frame is at the frame. -/
theorem FB.at_ (h : VerifyLayerPre a s c m0) {m : MachineData} (hb : FB m0 m) : At m0 2032 m :=
  Fr.at_ (ctx h) hb (fouts_not_rc h)

omit [Labels] in
/-- The frame's byte `o < 2032` is in the frame. -/
theorem loc_in (o : Nat) (ho : o < 2032) : InRange (base m0 2032) 2032 (loc m0 o) :=
  NativeRustcVm.inRange_add ho (by decide)

/-- The frame's byte `o` is neither the `TState`'s nor its decoded area's. -/
theorem loc_not_ts (h : VerifyLayerPre a s c m0) {o : Nat} (ho : o < 2032) :
    ¬InRange (tA m0) tstateBytes (loc m0 o) ∧ ¬InRange a.words (8 * a.len) (loc m0 o) :=
  frame_not_tstate (ctx h) (loc_in o ho)

/-- The frame's byte `o` is not an output. -/
theorem loc_not_fouts (h : VerifyLayerPre a s c m0) {o : Nat} (ho : o < 2032) :
    ¬fouts m0 (loc m0 o) := fun hq ↦ fouts_not_frame h _ hq (loc_in o ho)

end

/-- `n` bytes of the frame at `o'` miss the frame's byte `j` outside them. -/
theorem loc_not_loc {m0 : MachineData} (g : Geo m0) {o' n j : Nat} (hon : o' + n ≤ 2032)
    (hj : j < 2032) (hd : j < o' ∨ o' + n ≤ j) : ¬InRange (loc m0 o') n (loc m0 j) :=
  not_loc (by have := g.hN; omega) hon hj hd

/-- `n'` bytes of the frame at `o'` within `n` bytes at `o`. -/
theorem loc_mono {m0 : MachineData} (g : Geo m0) {o o' n n' : Nat} (h1 : o ≤ o')
    (h2 : o' + n' ≤ o + n) (h3 : o + n ≤ 2032) {q : BitVec 64} (hq : InRange (loc m0 o') n' q) :
    InRange (loc m0 o) n q := by
  have := g.hN; have hb := g.bN; have hl := Geo.sp_lt m0
  rw [Sym.inRange_iff (by rw [g.fa (by omega)]; omega), g.fa (by omega)] at hq
  rw [Sym.inRange_iff (by rw [g.fa (by omega)]; omega), g.fa (by omega)]
  omega

/-- A callee's stack misses the frame. -/
theorem stk_not_loc {m0 m : MachineData} (g : Geo m0) (hsp : m.regs.SP.toBitVec = base m0 2032)
    {N' : Nat} (hle : N' ≤ 1616) {j : Nat} (hj : j < 2032) :
    ¬InRange (stackBelow m N') N' (loc m0 j) := by
  have := g.hN; have hb := g.bN; have hl := Geo.sp_lt m0; have hst := g.stk hsp hle
  rw [Sym.inRange_iff (by rw [hst]; omega), hst, g.fa (by omega)]
  omega

/-- **Bytes of the frame kept by a call** writing its stack and `X`, apart from them. -/
theorem keep_call {m0 m : MachineData} {d' : DataMem} (g : Geo m0)
    (hsp : m.regs.SP.toBitVec = base m0 2032) {N' : Nat} (hle : N' ≤ 1616) {X : BitVec 64 → Prop}
    (hs : SameOutside m.dmem d' (fun q ↦ InRange (stackBelow m N') N' q ∨ X q))
    {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 2032)
    (hX : ∀ i < bs.length, ¬X (loc m0 (o + i)))
    (h : NativeRustcVm.BytesAt m.dmem (loc m0 o) bs) : NativeRustcVm.BytesAt d' (loc m0 o) bs :=
  keep_frame hsp (by have := g.hN; omega) hs ho hX h

/-- **Bytes of the frame kept by a block** whose writes there are apart from them. -/
theorem keep_blk [Labels] {m0 m m' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m ((base m0 2032, 2032) :: rs)) S m')
    (hwf : (Env.ofMachine m ((base m0 2032, 2032) :: rs)).WF) {o L : Nat} (hL : o + L ≤ 2032)
    (hw : ∀ w ∈ S.mem, (w.r = 0 ∧ (w.off + w.n ≤ o ∨ o + L ≤ w.off)) ∨
      (w.r ≠ 0 ∧ w.off + w.n ≤ (((2032 :: rs.map Prod.snd))[w.r]?).getD 0))
    {bs : List UInt8} (hbs : bs.length ≤ L)
    (h : NativeRustcVm.BytesAt m.dmem (loc m0 o) bs) :
    NativeRustcVm.BytesAt m'.dmem (loc m0 o) bs :=
  keep_block hm hwf (sizes := 2032 :: rs.map Prod.snd) (by simp) (r := 0) rfl hL hw hbs h

end

/-- A `Changes` with no output: the stack only. -/
theorem changes_stk {m m' : MachineData} {N' : Nat} (hc : Changes m m' N' 0 0) :
    SameOutside m.dmem m'.dmem (InRange (stackBelow m N') N') :=
  NativeRustcVm.SameOutside.mono hc fun _ hq ↦ hq.elim
    (fun h ↦ absurd h (Bus.not_inRange_zero _ _)) id

public section
variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- **The `TState` kept by a block** writing the frame (region 0) only. -/
theorem ts_blk (h : VerifyLayerPre a s c m0) {m m' : MachineData} {S : SState}
    (hm : Match (Env.ofMachine m [(base m0 2032, 2032)]) S m')
    (hwf : (Env.ofMachine m [(base m0 2032, 2032)]).WF)
    (hS : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 2032) {s' : TState}
    (ht : TStateAt m.dmem (tA m0) a s') : TStateAt m'.dmem (tA m0) a s' :=
  ht.frame (hm.kept hwf) (fun _ hq ↦ frame_not_tstate (ctx h) hq)
    (NativeRustcVm.SameOutside.mono (hm.sameOutside hwf) fun _ hq ↦
      Bus.Written.inRange (r := 0) rfl (Bus.frame_mapped (pre_stack h) N_ge).2 hS hq)

/-- **The `TState` kept by a call** writing its stack and `X` apart from it. -/
theorem ts_call (h : VerifyLayerPre a s c m0) {m m' : MachineData}
    (hsp : m.regs.SP.toBitVec = base m0 2032) {N' : Nat} (hle : N' ≤ 1616) {X : BitVec 64 → Prop}
    (hs : SameOutside m.dmem m'.dmem fun q ↦ InRange (stackBelow m N') N' q ∨ X q)
    (hk : Kept m.dmem m'.dmem)
    (hX : ∀ q, X q → ¬InRange (tA m0) tstateBytes q ∧ ¬InRange a.words (8 * a.len) q)
    {s' : TState} (ht : TStateAt m.dmem (tA m0) a s') : TStateAt m'.dmem (tA m0) a s' :=
  tstate_keep h hsp hle hs hk hX ht

/-- A frame byte apart from the `TState`: as `ts_call` wants it. -/
theorem loc_ts (h : VerifyLayerPre a s c m0) {o n : Nat} (hon : o + n ≤ 2032) {q : BitVec 64}
    (hq : InRange (loc m0 o) n q) :
    ¬InRange (tA m0) tstateBytes q ∧ ¬InRange a.words (8 * a.len) q := by
  have h' := loc_mono (geo_of h) (o := 0) (n := 2032) (Nat.zero_le _) (by omega) (Nat.le_refl _) hq
  simp only [loc, NativeRustcVm.addr_add_zero] at h'
  exact frame_not_tstate (ctx h) h'

/-- **The frame kept by a call** writing its stack and the `TState`. -/
theorem fr_same (h : VerifyLayerPre a s c m0) {m m' : MachineData}
    (hsp : m.regs.SP.toBitVec = base m0 2032) {N' : Nat} (hle : N' ≤ 1616)
    (hs : SameOutside m.dmem m'.dmem fun q ↦
      InRange (stackBelow m N') N' q ∨ InRange (tA m0) tstateBytes q) :
    NativeRustcVm.Layout.Same m.dmem m'.dmem (base m0 2032) 2032 :=
  same_frame (geo_of h) hsp hle hs fun _ hj ↦ (loc_not_ts h hj).1

/-- **A range of the scratch kept by a call** writing its stack and `W` apart from it. -/
theorem scr_same (h : VerifyLayerPre a s c m0) {m : MachineData} {d' : DataMem}
    (hsp : m.regs.SP.toBitVec = base m0 2032) {N' : Nat} (hle : N' ≤ 1616) {W : BitVec 64 → Prop}
    (hs : SameOutside m.dmem d' fun q ↦ InRange (stackBelow m N') N' q ∨ W q) {o n : Nat}
    (ho : o < 205824) (hon : o + n ≤ 205824)
    (hW : ∀ j < n, ¬W (sA m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 j)) :
    NativeRustcVm.Layout.Same m.dmem d' (sA m0 + BitVec.ofNat 64 o) n := by
  have g := geo_of h
  have := g.hN; have := Geo.sp_lt m0; have hst := g.stk hsp hle; have := g.hs; have := g.hss
  refine NativeRustcVm.Layout.Same.of_sameOutside hs fun j hj hq ↦ hq.elim (fun hq ↦ ?_) (hW j hj)
  exact notIn (by rw [hst]; omega) (by rw [g.sa ho]; omega) (by rw [hst, g.sa ho]; omega) hq

/-- A range of the scratch misses the `TState`. -/
theorem scr_not_ts (h : VerifyLayerPre a s c m0) {o n : Nat} (ho : o < 205824)
    (hon : o + n ≤ 205824) {j : Nat} (hj : j < n) :
    ¬InRange (tA m0) tstateBytes (sA m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 j) :=
  (sc_miss h (o := o) (n := n) ho hon (NativeRustcVm.inRange_add hj (by omega))).1

end

public section
variable [Host] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- **A leaf call** from the frame: its contract changes its stack only. -/
theorem leaf_call (h : VerifyLayerPre a s c m0) {l : Label} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} {N' : Nat} (hle : 2032 + N' ≤ verifyLayerStack)
    (hspec : Spec (Labels.label l) P Q)
    (hQ : ∀ m m', Q m m' →
      SameOutside m.dmem m'.dmem (InRange (stackBelow m N') N') ∧ Saved m m')
    {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (hfr : FB m0 st.data) (hpc : st.pc = Labels.label l ∧ retOf st.data = next) (hP : P st.data)
    (cont : ∀ m2, FB m0 m2 → Q st.data m2 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (fun q ↦ InRange (stackBelow st.data N') N' q ∨ False) →
      Kept st.data.dmem m2.dmem → Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st :=
  Fr.callSpec hfr (pre_stack h).2.1 hle (by decide) slots_le (fouts_not_frame h) hspec hpc hP
    (fun _ hq ↦ ⟨NativeRustcVm.SameOutside.mono (hQ _ _ hq).1 fun _ h ↦ .inl h, (hQ _ _ hq).2⟩)
    fun m2 hfr2 hq2 hcs2 ↦ cont m2 hfr2 hq2 hcs2
      (NativeRustcVm.SameOutside.mono (hQ _ _ hq2).1 fun _ h ↦ .inl h) (hQ _ _ hq2).2.2.2

/-- **A call writing `n` bytes of the frame at `o`** (below the slots) and outputs. -/
theorem local_call (h : VerifyLayerPre a s c m0) {l : Label} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} {N' : Nat} (hle : 2032 + N' ≤ verifyLayerStack)
    {X : BitVec 64 → Prop} {o n : Nat} (hon : o + n ≤ 1936)
    (hX : ∀ q, X q → fouts m0 q ∨ InRange (loc m0 o) n q)
    (hspec : Spec (Labels.label l) P Q)
    {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (hfr : FB m0 st.data) (hpc : st.pc = Labels.label l ∧ retOf st.data = next) (hP : P st.data)
    (hQ : ∀ m', Q st.data m' → SameOutside st.data.dmem m'.dmem
      (fun q ↦ InRange (stackBelow st.data N') N' q ∨ X q) ∧ Saved st.data m')
    (cont : ∀ m2, FB m0 m2 → Q st.data m2 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (fun q ↦ InRange (stackBelow st.data N') N' q ∨ X q) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st :=
  Fr.callLocal (o := o) (n := n) hfr (pre_stack h).2.1 hle (by decide) (slots_lo hon)
    (by omega) (fouts_not_frame h) hX hspec hpc hP hQ cont

/-- **`read_scalars(t, frame + o, n)`**. -/
theorem rs_call (h : VerifyLayerPre a s c m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    {st : MachineState} {next : Int64} {R : MachineState → Prop} {o n : Nat}
    (ho : o + 16 * n ≤ 1936) (hfr : FB m0 st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel ∧ retOf st.data = next)
    (h0 : st.data.regs.X0 = m0.regs.X0) (h1 : st.data.regs.X1.toBitVec = loc m0 o)
    (h2 : st.data.regs.X2.toNat = n) {s1 : TState}
    (hts : TStateAt st.data.dmem (tA m0) a s1)
    (cont : ∀ m2, FB m0 m2 →
      m2.regs.X0 = okWord ((readScalars n).run s1).isSome →
      (∀ ys s', (readScalars n).run s1 = some (ys, s') →
        NativeRustcVm.EWsAt m2.dmem (loc m0 o) ys.toList ∧ TStateAt m2.dmem (tA m0) a s') →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (fun q ↦
        InRange (stackBelow st.data readScalarsStack) readScalarsStack q ∨
          (InRange (loc m0 o) (16 * n) q ∨ InRange (tA m0) tstateBytes q)) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hS := pre_stack h
  have cx := ctx h
  have hat := FB.at_ h hfr
  refine local_call h le_rs (o := o) (n := 16 * n)
    (X := fun q ↦ InRange (loc m0 o) (16 * n) q ∨ InRange (tA m0) tstateBytes q) ho
    (fun q hq ↦ hq.elim .inr fun h' ↦ .inl (.inl h')) (hrs s1) hfr hpc ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.2.1 fun q hq' ↦ ?_, hq.2.2.2.2⟩)
    fun m2 hfr2 hq2 hcs2 hs2 ↦ ?_
  · refine ⟨hfr.stackOk hS rfl le_rs, cx.rcAt hat le_rs, by rw [h0]; exact hts,
      by rw [h0]; exact cx.tstateOk hat le_rs, ?_⟩
    rw [h0, h1, h2]
    exact cx.outOk hat le_rs (o := o) (by omega)
  · rw [h0, h1, h2] at hq'
    rcases hq' with hq' | hq' | hq'
    · exact .inr (.inl hq')
    · exact .inr (.inr hq')
    · exact .inl hq'
  · obtain ⟨hx0, hok, hnext, -, -⟩ := hq2
    rw [h2] at hx0 hok hnext
    rw [h1] at hok
    rw [h0] at hnext
    exact cont m2 hfr2 hx0 (fun ys s' he ↦ ⟨hok ys s' he, hnext ys s' he⟩) hcs2 hs2

/-- **`grind(t, bits)`**. -/
theorem grind_call (h : VerifyLayerPre a s c m0)
    (hgr : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    {st : MachineState} {next : Int64} {R : MachineState → Prop} (hfr : FB m0 st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel ∧ retOf st.data = next)
    (h0 : st.data.regs.X0 = m0.regs.X0) {bits : Nat} (h1 : grindBits st.data = bits)
    (hb : bits < 64) {s1 : TState} (hts : TStateAt st.data.dmem (tA m0) a s1)
    (cont : ∀ m2, FB m0 m2 →
      m2.regs.X0 = okWord ((grind bits).run s1).isSome →
      NextAt m2.dmem (tA m0) a ((grind bits).run s1) →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (fun q ↦
        InRange (stackBelow st.data grindStack) grindStack q ∨ InRange (tA m0) tstateBytes q) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hS := pre_stack h
  have cx := ctx h
  have hat := FB.at_ h hfr
  refine Fr.callSpec hfr hS.2.1 le_grind (by decide) slots_le (fouts_not_frame h) (hgr s1) hpc
    ⟨hfr.stackOk hS rfl le_grind, cx.rcAt hat le_grind, by rw [h0]; exact hts,
      by rw [h0]; exact cx.tstateOk hat le_grind, by rw [h1]; exact hb⟩
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ ?_, hq.2.2.2⟩)
    fun m2 hfr2 hq2 hcs2 ↦ ?_
  · rw [h0] at hq'
    exact hq'.elim (fun h' ↦ .inr (.inl h')) .inl
  · obtain ⟨hx0, hnext, hs2, -⟩ := hq2
    rw [h1] at hx0 hnext
    rw [h0] at hnext hs2
    exact cont m2 hfr2 hx0 hnext hcs2
      (NativeRustcVm.SameOutside.mono hs2 fun q hq ↦ hq.elim .inr .inl)

/-- **`SpongeW::squeeze`** on the `TState`'s sponge. -/
theorem sq_call (h : VerifyLayerPre a s c m0)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {st : MachineState} {next : Int64} {R : MachineState → Prop} (hfr : FB m0 st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel ∧ retOf st.data = next)
    (h0 : st.data.regs.X0 = m0.regs.X0) {s1 : TState} (hts : TStateAt st.data.dmem (tA m0) a s1)
    (cont : ∀ m2 : MachineData, FB m0 m2 →
      TStateAt m2.dmem (tA m0) a (sqS s1).2 →
      m2.regs.X0 = (sqS s1).1.c0 → m2.regs.X1 = (sqS s1).1.c1 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (fun q ↦
        InRange (stackBelow st.data squeezeStack) squeezeStack q ∨ InRange (tA m0) tstateBytes q) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st :=
  Tables.squeeze_call (ctx h) hsq hfr (fouts_not_rc h) le_sq (by decide) slots_le
    (fouts_not_frame h) (fun _ hq ↦ .inl hq) hpc (by rw [h0]) hts
    fun m2 hf2 hts2 hx0 hx1 hcs hs ↦ cont m2 hf2 hts2 hx0 hx1 hcs
      (NativeRustcVm.SameOutside.mono hs fun q hq ↦ hq.elim (fun h' ↦ .inr
        (NativeRustcVm.InRange.mono h' (NativeRustcVm.NoWrap.mono (pre_ts h).footprint.1.2
          (by exact (by decide : NativeRustcVm.Transcript.spongeBytes ≤ tstateBytes)))
          (pre_ts h).footprint.1.2 (Nat.le_refl _)
          (Nat.add_le_add_left (by decide) _))) .inl)

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
