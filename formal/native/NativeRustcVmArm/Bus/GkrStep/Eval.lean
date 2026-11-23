module

public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmArm.Bus.GkrStep.Tail

/-!
# `gkr_step`'s new values

`b23` to `b25` evaluate each child at `y` (`multilinear_eval`), `b24` to `b26` write the values
into the `GkrStateW` (region 1 of `frP`); `b26` checks `|xs| + step ≤ 63`; `b27`, `b28` write
the point's length and `y`: `AtCopy`, at `.LGkrStep_11`.
-/

namespace NativeRustcVmArm.Bus.GkrStep

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.GkrStep
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVmArm.Bus.Gkr
open NativeRustcVmArm.Sumcheck (Ctx At)

public section

/-- The environment of the blocks writing the `GkrStateW`: the frame, the `GkrStateW`. -/
abbrev envP [Labels] (m0 m : MachineData) : Env :=
  Env.ofMachine m [(base m0 1392, 1392), (m0.regs.X3.toBitVec, 1064)]

theorem ult_lit64 (x : BitVec 64) (v : Nat) (hv : v < 2 ^ 64) :
    CmpOp.ult.apply .W64 x (BitVec.ofNat 64 v) = decide (x.toNat < v) := by
  simp only [CmpOp.apply, low_W64, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

theorem eq_lit64 (x : BitVec 64) (v : Nat) (hv : v < 2 ^ 64) :
    CmpOp.eq.apply .W64 x (BitVec.ofNat 64 v) = decide (x.toNat = v) := by
  simp only [CmpOp.apply, low_W64]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hv]

variable [Labels] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData}

theorem wf_p (h : GkrStepPre a s0 g0 m0) {m : MachineData}
    (hfr : Fr m0 1392 gkrStepStack slots keep (outs m0) m) : (envP m0 m).WF :=
  Bus.wf_frame2 (pre_stack h) N_ge hfr.kept ⟨(pre_gk h).1, (pre_gk h).2.1⟩ (pre_gk h).2.2.2.2.1

theorem match_p (h : GkrStepPre a s0 g0 m0) {m : MachineData}
    (hfr : Fr m0 1392 gkrStepStack slots keep (outs m0) m)
    (h19 : m.regs.getXReg .X19 = m0.regs.X3) : Match (envP m0 m) frP m :=
  match_frameW (n := 1064) (pre_stack h) N_ge rfl hfr.sp (by rw [h19])

/-- The frame after a block writing the `GkrStateW` only. -/
theorem fr_p (h : GkrStepPre a s0 g0 m0) {m m' : MachineData} {S' : SState}
    (hfr : Fr m0 1392 gkrStepStack slots keep (outs m0) m) (hm : Match (envP m0 m) frP m)
    (hm' : Match (envP m0 m) S' m') (hsp : S'.sp = .ptr 0 0)
    (hw : ∀ w ∈ S'.mem, w.r = 1 ∧ w.off + w.n ≤ 1064) :
    Fr m0 1392 gkrStepStack slots keep (outs m0) m' := by
  have hnwp : m0.regs.X3.toBitVec.toNat + 1064 ≤ 2 ^ 64 := (pre_gk h).2.1
  refine Fr.ofBlockW hfr hm hm' (wf_p h hfr) rfl hsp (fun _ hr ↦ absurd hr List.not_mem_nil) rfl
    N_ge (pre_stack h).2.1 slots_le fun w hw' ↦ .inr ⟨by rw [(hw w hw').1]; decide,
      fun b sz hb ↦ ?_⟩
  rw [(hw w hw').1] at hb
  simp only [Env.ofMachine, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  exact ⟨(hw w hw').2, fun i hi ↦ .inr (NativeRustcVm.inRange_add hi (by decide))⟩

/-- The frame's elements kept by a block writing the `GkrStateW` only. -/
theorem ews_p {m m' : MachineData} {S' : SState} (hm' : Match (envP m0 m) S' m')
    (hwf : (envP m0 m).WF) (hw : ∀ w ∈ S'.mem, w.r = 1 ∧ w.off + w.n ≤ 1064) {o : Nat}
    {zs : List EW} (ho : o + 16 * zs.length ≤ 1392)
    (hz : NativeRustcVm.EWsAt m.dmem (loc m0 o) zs) : NativeRustcVm.EWsAt m'.dmem (loc m0 o) zs :=
  keep_block hm' hwf (sizes := [1392, 1064]) rfl (r := 0) rfl (L := 16 * zs.length) ho
    (fun w hw' ↦ .inr ⟨by rw [(hw w hw').1]; decide, by rw [(hw w hw').1]; exact (hw w hw').2⟩)
    (by rw [NativeRustcVm.length_ewsBytes]) hz

/-- The `TState` kept by a block writing the `GkrStateW` only. -/
theorem ts_p (h : GkrStepPre a s0 g0 m0) {m m' : MachineData} {S' : SState}
    (hm' : Match (envP m0 m) S' m') (hwf : (envP m0 m).WF)
    (hw : ∀ w ∈ S'.mem, w.r = 1 ∧ w.off + w.n ≤ 1064) {s : TState}
    (ht : TStateAt m.dmem m0.regs.X0.toBitVec a s) : TStateAt m'.dmem m0.regs.X0.toBitVec a s :=
  ht.frame (fun q hq ↦ hm'.kept hwf q hq) (fun _ hq ↦ p_apart h hq)
    (NativeRustcVm.SameOutside.mono (hm'.sameOutside hwf) fun _ hq ↦
      Written.inRange (r := 1) rfl (pre_gk h).2.1 hw hq)

/-- Bytes of the `GkrStateW` kept by a block writing elsewhere in it. -/
theorem out_p {m m' : MachineData} {S' : SState} (hm' : Match (envP m0 m) S' m')
    (hwf : (envP m0 m).WF) {o L : Nat} (hob : o + L ≤ 1064)
    (hw : ∀ w ∈ S'.mem, w.r = 1 ∧ (w.off + w.n ≤ o ∨ o + L ≤ w.off)) {bs : List UInt8}
    (hbs : bs.length ≤ L)
    (hb : NativeRustcVm.BytesAt m.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt m'.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 o) bs :=
  keep_block hm' hwf (sizes := [1392, 1064]) rfl (r := 1) rfl hob
    (fun w hw' ↦ .inl (hw w hw')) hbs hb

/-- Bytes of the `GkrStateW` kept by a leaf call. -/
theorem out_leaf (h : GkrStepPre a s0 g0 m0) {m m' : MachineData}
    (hfr : Fr m0 1392 gkrStepStack slots keep (outs m0) m) {N' : Nat}
    (hle : 1392 + N' ≤ gkrStepStack) (hc : Changes m m' N' 0 0) {o : Nat} {bs : List UInt8}
    (hob : o + bs.length ≤ 1064)
    (hb : NativeRustcVm.BytesAt m.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt m'.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 o) bs :=
  NativeRustcVm.BytesAt.of_sameOutside hb (Bus.changes_zero (outs := fun _ ↦ False) hc)
    fun i hi hq ↦ hq.elim (fun h' ↦ (callee_apart h hfr hle h').2.1 (by
      rw [NativeRustcVm.addr_add_add]
      have e : gkrStateBytes = 1064 := rfl
      exact NativeRustcVm.inRange_add (show o + i < gkrStateBytes by omega) (by decide))) id

omit [Labels] in
/-- An element from its two words. -/
theorem ew_words {d : DataMem} {b : BitVec 64} {o : Nat} {x : EW}
    (h0 : NativeRustcVm.WordAt d (b + BitVec.ofNat 64 o) x.c0)
    (h1 : NativeRustcVm.WordAt d (b + BitVec.ofNat 64 (o + 8)) x.c1) :
    NativeRustcVm.EWsAt d (b + BitVec.ofNat 64 o) [x] := by
  refine NativeRustcVm.ewsAt_singleton.mpr (NativeRustcVm.ewAt_iff.mpr ⟨h0, ?_⟩)
  rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add_add]
  exact h1

omit [Labels] in
/-- Elements one after the other. -/
theorem ews_cons {d : DataMem} {b : BitVec 64} {o : Nat} {x : EW} {xs : List EW}
    (hx : NativeRustcVm.EWsAt d (b + BitVec.ofNat 64 o) [x])
    (hxs : NativeRustcVm.EWsAt d (b + BitVec.ofNat 64 (o + 16)) xs) :
    NativeRustcVm.EWsAt d (b + BitVec.ofNat 64 o) (x :: xs) := by
  rw [show x :: xs = [x] ++ xs from rfl, NativeRustcVm.ewsAt_append]
  refine ⟨hx, ?_⟩
  rw [NativeRustcVm.addr_add_add]
  exact hxs

omit [Labels] in
/-- Element `i` of elements at `b + o`: its two words. -/
theorem ews_words {d : DataMem} {b : BitVec 64} {o : Nat} {xs : List EW}
    (h : NativeRustcVm.EWsAt d (b + BitVec.ofNat 64 o) xs) {i : Nat} (hi : i < xs.length) :
    NativeRustcVm.WordAt d (b + BitVec.ofNat 64 (o + 16 * i)) xs[i].c0 ∧
      NativeRustcVm.WordAt d (b + BitVec.ofNat 64 (o + 16 * i + 8)) xs[i].c1 := by
  have := NativeRustcVm.ewAt_iff.mp (NativeRustcVm.ewsAt_getElem h hi)
  rw [NativeRustcVm.addr_add_add, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
    NativeRustcVm.addr_add_add] at this
  exact this

end

public section
variable [Host] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData} {k : Nat}

/-- `multilinear_eval(2^step child at frame + o, y)`. -/
theorem mle_call (h : GkrStepPre a s0 g0 m0)
    (hmle : Spec (Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost)
    {st : MachineState} {next : Int64} {R : MachineState → Prop} {o : Nat} (ho : o + 64 ≤ 1216)
    (hfr : Fr m0 1392 gkrStepStack slots keep (outs m0) st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.entryLabel ∧ retOf st.data = next)
    {ch y : Array EW} (hch : NativeRustcVm.EWsAt st.data.dmem (loc m0 o) ch.toList)
    (hys : NativeRustcVm.EWsAt st.data.dmem (loc m0 1264) y.toList)
    (hcs : ch.size = 2 ^ m0.regs.X1.toNat) (hyz : y.size = m0.regs.X1.toNat)
    (h0 : st.data.regs.X0 = st.data.regs.X2) (h1 : st.data.regs.X1.toBitVec = loc m0 o)
    (h2 : st.data.regs.X2.toNat = 2 ^ m0.regs.X1.toNat)
    (h3 : st.data.regs.X3.toBitVec = loc m0 1264) (h4 : st.data.regs.X4 = m0.regs.X1)
    (cont : ∀ m2, Fr m0 1392 gkrStepStack slots keep (outs m0) m2 →
      ewRet m2 = multilinearEval ch y →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      Changes st.data m2 mleStack 0 0 → Kept st.data.dmem m2.dmem →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hS := pre_stack h
  have hn := two_pow_le h
  have hstep := pre_step h
  refine leaf_call h le_mle hmle (fun _ _ hq ↦ hq.2) hfr hpc
    ⟨hfr.stackOk hS rfl le_mle, h0, by rw [h4]; omega,
      sliceOk_loc h hfr le_mle h1 (by omega), sliceOk_loc h hfr le_mle h3 (by rw [h4]; omega)⟩
    fun m2 hfr2 hq2 hcs2 hc2 hk2 ↦ cont m2 hfr2 ?_ hcs2 hc2 hk2
  rw [hq2.1, slice_loc hch h1 (by rw [h2, hcs]), slice_loc hys h3 (by rw [h4, hyz])]

end

end NativeRustcVmArm.Bus.GkrStep
