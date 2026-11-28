module

public import NativeRustcVmArm.Whir.VerifyStackedOpening.Sample

/-!
# `verify_stacked_opening`: the scales, the first term

`b11` stores the count at the scales and calls `powers` on the challenge into them; `b12`
reads the count back, `b13` the first scale, `b15` the ring switch's target and calls `EW::mul`:
the first term of the batched target. `b16` starts the target's loop over the claims at
`.LVerifyStackedOpening_17` (`b22`, `Tgt 0`), or with no claim goes to
`.LVerifyStackedOpening_21` (`b26`, `AtB26`) (`powers_step`). `Common`: what holds from there
to the ladder.
-/

namespace NativeRustcVmArm.Whir.VerifyStackedOpening

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.VerifyStackedOpening

@[expose] public section

/-- The count of the stack claims. -/
abbrev cntOf (layout : LayoutW) (cs : Array ColumnClaimW) : Nat := placedOf layout cs cs.size + 2

/-- The scales. -/
abbrev scalesOf (s : TState) (layout : LayoutW) (cs : Array ColumnClaimW) : Array EW :=
  powers (sq s).1 (cntOf layout cs)

/-- **From the scales to the ladder**: the frame, the `TState` after the squeeze, the frame's
words, the scales' count and the scales, the layout and the ring switch's output in X22, X24, the
scales in X23 (their count in X25). -/
structure Common [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (cs : Array ColumnClaimW)
    (m0 st : MachineData) : Prop where
  fr : VFr m0 st
  ts : TStateAt st.dmem (tA m0) a (sq s).2
  fw : FW st.dmem m0 [(16, m0.regs.X0), (24, m0.regs.X4), (32, m0.regs.X5), (40, m0.regs.X6),
    (48, m0.regs.X2)]
  scw : NativeRustcVm.WordAt st.dmem (scA m0) (cntOf layout cs).toUInt64
  scs : NativeRustcVm.EWsAt st.dmem (scA m0 + BitVec.ofNat 64 8) (scalesOf s layout cs).toList
  x22 : st.regs.getXReg .X22 = m0.regs.X1
  x23 : (st.regs.getXReg .X23).toBitVec = scA m0 + BitVec.ofNat 64 8
  x24 : st.regs.getXReg .X24 = m0.regs.X3
  x25 : st.regs.getXReg .X25 = (cntOf layout cs).toUInt64

/-- **The target's loop head**, before claim `i`: the claim in X28, the bytes left in X29, the
layout's placements in X20, the next scale in X19, the scales' end in X21, the target's terms so
far in X27, X26. -/
structure Tgt [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (target : EW)
    (cs : Array ColumnClaimW) (value : EW) (m0 : MachineData) (i : Nat) (st : MachineData) :
    Prop where
  com : Common a s layout cs m0 st
  hi : i < cs.size
  x28 : (st.regs.getXReg .X28).toBitVec = m0.regs.X5.toBitVec + BitVec.ofNat 64 (8 + 608 * i)
  x29 : st.regs.getXReg .X29 = (608 * (cs.size - i)).toUInt64
  x20 : (st.regs.getXReg .X20).toBitVec = m0.regs.X1.toBitVec + BitVec.ofNat 64 120
  x19 : (st.regs.getXReg .X19).toBitVec =
    scA m0 + BitVec.ofNat 64 (8 + 16 * (1 + placedOf layout cs i))
  x21 : (st.regs.getXReg .X21).toBitVec = scA m0 + BitVec.ofNat 64 (8 + 16 * cntOf layout cs)
  acc : (⟨st.regs.getXReg .X27, st.regs.getXReg .X26⟩ : EW) =
    dotL ((scalesOf s layout cs).toList.take (1 + placedOf layout cs i))
      ((valsOf layout target cs value).take (1 + placedOf layout cs i))

/-- **At `b26`**: every claim's term added. -/
structure AtB26 [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (target : EW)
    (cs : Array ColumnClaimW) (value : EW) (m0 st : MachineData) : Prop where
  com : Common a s layout cs m0 st
  x19 : (st.regs.getXReg .X19).toBitVec =
    scA m0 + BitVec.ofNat 64 (8 + 16 * (1 + placedOf layout cs cs.size))
  x21 : (st.regs.getXReg .X21).toBitVec = scA m0 + BitVec.ofNat 64 (8 + 16 * cntOf layout cs)
  acc : (⟨st.regs.getXReg .X27, st.regs.getXReg .X26⟩ : EW) =
    dotL ((scalesOf s layout cs).toList.take (1 + placedOf layout cs cs.size))
      ((valsOf layout target cs value).take (1 + placedOf layout cs cs.size))

end

public section

theorem size_scalesOf (s : TState) (layout : LayoutW) (cs : Array ColumnClaimW) :
    (scalesOf s layout cs).size = cntOf layout cs := by
  unfold scalesOf powers
  generalize (sq s).1 = b
  suffices ∀ n (acc : Array EW × EW), ((List.range n).foldl (fun (acc : Array EW × EW) _ ↦
      (acc.1.push acc.2, acc.2 * b)) acc).1.size = acc.1.size + n from by
    simpa using this _ (#[], 1)
  intro n
  induction n with
  | zero => intro acc; simp
  | succ n ih => intro acc; rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
                 simp [ih]; omega

section
variable [Labels] {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- `Common` across a block without writes keeping X22 to X25. -/
theorem Common.same {st st' : MachineData} (hc : Common a s layout cs m0 st) (hf : VFr m0 st')
    (hd : st'.dmem = st.dmem)
    (hk : ∀ r ∈ [XReg.X22, .X23, .X24, .X25], st'.regs.getXReg r = st.regs.getXReg r) :
    Common a s layout cs m0 st' :=
  ⟨hf, hd ▸ hc.ts, hd ▸ hc.fw, hd ▸ hc.scw, hd ▸ hc.scs, (hk .X22 (by simp)).trans hc.x22,
    (hk .X23 (by simp)) ▸ hc.x23, (hk .X24 (by simp)).trans hc.x24,
    (hk .X25 (by simp)).trans hc.x25⟩

/-- `Common` across a block without writes from an environment of the state. -/
theorem Common.blk {rs : List (BitVec 64 × Nat)} {S S' : SState} {st st' : MachineData}
    (hc : Common a s layout cs m0 st) (hm : Match (Env.ofMachine st rs) S st)
    (hm' : Match (Env.ofMachine st rs) S' st') (hwf : (Env.ofMachine st rs).WF)
    (hmem : S'.mem = []) (hsp : S'.sp = S.sp)
    (hk : ∀ r ∈ [XReg.X22, .X23, .X24, .X25], S'.reg r = some (.reg r)) :
    Common a s layout cs m0 st' :=
  hc.same (Fr.ofBlock hc.fr hm hm' hwf rfl hmem hsp (by simp)) (hm'.dmem_eq hwf hmem)
    fun r hr ↦ (rv hm' (hk r hr)).trans rfl

/-- `Common` across a call writing its stack only. -/
theorem Common.call (h : Parts a s layout target coefficients point slices cs z value m0)
    {st st' : MachineData} (hc : Common a s layout cs m0 st) (hf' : VFr m0 st') {N' : Nat}
    (hle : 512 + N' ≤ verifyStackedOpeningStack)
    (hs : SameOutside st.dmem st'.dmem (InRange (stackBelow st N') N'))
    (hk : NativeRustcVm.Transcript.Keeps st.dmem st'.dmem)
    (hcs : ∀ r, calleeSaved r = true → st'.regs.getXReg r = st.regs.getXReg r) :
    Common a s layout cs m0 st' := by
  have hP : placedOf layout cs cs.size ≤ 160 := (placedOf_le_self _).trans h.cl.len_le
  have hscb : scalesBytes = 2600 := rfl
  refine ⟨hf', h.ts_call hc.fr hle hc.ts hk (NativeRustcVm.SameOutside.mono hs fun q hq ↦ .inl hq),
    fw_call h hc.fr hle (NativeRustcVm.SameOutside.mono hs fun q hq ↦ .inl hq) (by simp) hc.fw,
    ?_, ?_, (hcs .X22 rfl).trans hc.x22, (hcs .X23 rfl) ▸ hc.x23, (hcs .X24 rfl).trans hc.x24,
    (hcs .X25 rfl).trans hc.x25⟩
  · have := h.sc_keep hc.fr hle (o := 0) (bs := NativeRustcVm.wordBytes (cntOf layout cs).toUInt64)
      (NativeRustcVm.SameOutside.mono hs fun q hq ↦ .inl hq)
      (by rw [NativeRustcVm.length_wordBytes, hscb]; omega)
      (by rw [NativeRustcVm.length_wordBytes]; omega)
      (by rw [NativeRustcVm.addr_add_zero]; exact hc.scw)
    rwa [NativeRustcVm.addr_add_zero] at this
  · exact h.sc_keep hc.fr hle (o := 8) (NativeRustcVm.SameOutside.mono hs fun q hq ↦ .inl hq)
      (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, size_scalesOf, hscb]; unfold cntOf
          omega)
      (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, size_scalesOf]; unfold cntOf
          omega)
      hc.scs

end

end

end NativeRustcVmArm.Whir.VerifyStackedOpening
