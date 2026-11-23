module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.GluedEval.Names
public import NativeRustcVmArm.Whir.FinalLevel.Rotate

/-!
# `final_level`: one glued claim

`GBase`: what the glued loop keeps (the frame, `2 ^ μ` in X19, `μ` in X20, the point at the
frame's byte `1584` with its size in X29, the folded scalars, the tail, the claim at `24`, the
`TState`). `GInv`: at the loop's head (`b29`) after `i` claims, the weight `weightAt … i` in
(X21, X23), claim `i` at X24, the claims' end at X27, `6064` in X28. `gstep`: one claim,
`glued_eval` (`b29`), its `Some` (`b30`), `EW::mul` by the claim's scalar (`b31`), the sum and the
next claim or the end (`b32`).
-/

namespace NativeRustcVmArm.Whir.FinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.FinalLevel
open NativeRustcVmArm.Transcript (load_ofMachine eval_ptr load_of_wordAt)

public section

/-- The frame's bytes `[o, o + len)` of a range `[p, p + n)` kept. -/
theorem same_sub {m0 : MachineData} {d d' : Mem 64} {p n : Nat}
    (h : NativeRustcVm.Layout.Same d d' (loc m0 p) n) {o len : Nat} (hpo : p ≤ o)
    (hol : o + len ≤ p + n) : NativeRustcVm.Layout.Same d d' (loc m0 o) len := fun j hj ↦ by
  have := h (o - p + j) (by omega)
  have e : loc m0 p + BitVec.ofNat 64 (o - p + j) = loc m0 o + BitVec.ofNat 64 j :=
    (loc_off m0 p _).trans ((congrArg (loc m0) (show p + (o - p + j) = o + j by omega)).trans
      (loc_off m0 o j).symm)
  rwa [e] at this

/-- One glued claim's term, limb by limb. -/
theorem gStep_c (pt : Array EW) (wt : EW) (g : GluedClaimW) :
    (gStep pt wt g).c0 = (EW.mul g.scalar (g.weight.eval (pt.extract g.foldStart pt.size))).c0 ^^^
      wt.c0 ∧
    (gStep pt wt g).c1 = (EW.mul g.scalar (g.weight.eval (pt.extract g.foldStart pt.size))).c1 ^^^
      wt.c1 :=
  ⟨UInt64.xor_comm wt.c0 _, UInt64.xor_comm wt.c1 _⟩

/-- The next claim's address. -/
theorem ofNat_step (p : BitVec 64) (i : Nat) :
    p + BitVec.ofNat 64 (512 + 6064 * i) + BitVec.ofNat 64 6064 =
      p + BitVec.ofNat 64 (512 + 6064 * (i + 1)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 512 + 6064 * i + 6064 = 512 + 6064 * (i + 1) by
    omega]

/-- Two addresses at different small offsets differ. -/
theorem ofNat_ne (p : BitVec 64) {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : x ≠ y) :
    p + BitVec.ofNat 64 x ≠ p + BitVec.ofNat 64 y := fun he ↦ h (by
  have := congrArg BitVec.toNat ((BitVec.add_right_inj p).mp he)
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this)

section
variable [Labels]

theorem ev_eor (m : MachineData) (rs : List (BitVec 64 × Nat)) (r r' : XReg) :
    (Sym.bin .eor .W64 (.reg r) (.reg r')).eval (Env.ofMachine m rs) =
      (m.regs.getXReg r).toBitVec ^^^ (m.regs.getXReg r').toBitVec := by
  show BinOp.apply .eor .W64 (m.regs.getXReg r).toBitVec (m.regs.getXReg r').toBitVec = _
  simp only [BinOp.apply, low_W64, ext_W64]

/-- `cmp x24 + x28, x27; b.ne`. -/
theorem ev_next (m : MachineData) (rs : List (BitVec 64 × Nat)) :
    SBool.eval (Env.ofMachine m rs)
      (.not (.cmp .eq .W64 (.bin .add .W64 (.reg .X24) (.reg .X28)) (.reg .X27))) =
      !((m.regs.getXReg .X24).toBitVec + (m.regs.getXReg .X28).toBitVec ==
        (m.regs.getXReg .X27).toBitVec) := by
  show (!CmpOp.apply .eq .W64 (BinOp.apply .add .W64 (m.regs.getXReg .X24).toBitVec
    (m.regs.getXReg .X28).toBitVec) (m.regs.getXReg .X27).toBitVec) = _
  simp only [CmpOp.apply, BinOp.apply, low_W64, ext_W64]

end

/-- **What the glued loop keeps.** -/
structure GBase (a : DecArea) (level : Whir.Level) (w : WhirStateW) (m0 st : MachineData)
    (folded tail : Array EW) (claim : EW) (s5 : TState) : Prop where
  fr : FFr m0 st
  x19 : st.regs.X19.toNat = 2 ^ mu m0
  x20 : st.regs.X20 = m0.regs.X3
  x22 : st.regs.X22.toBitVec = loc m0 1584
  x29 : st.regs.X29.toNat = (w.alphas ++ tail).size
  size : folded.size = 2 ^ mu m0 + level.fold
  le64 : 2 ^ mu m0 + level.fold ≤ 64
  le30 : (w.alphas ++ tail).size ≤ 30
  fold : NativeRustcVm.EWsAt st.dmem (loc m0 40) folded.toList
  tl : NativeRustcVm.EWsAt st.dmem (loc m0 1096) tail.toList
  pts : NativeRustcVm.EWsAt st.dmem (loc m0 1584) (w.alphas ++ tail).toList
  cl : NativeRustcVm.EWAt st.dmem (loc m0 24) claim
  ts : TStateAt st.dmem (tA m0) a s5

/-- The registers the glued loop keeps. -/
@[expose] def gRegs : List XReg := [.X19, .X20, .X22, .X29]

theorem gRegs_cs : ∀ r ∈ gRegs, calleeSaved r = true := by decide

/-- `GBase` kept. -/
theorem GBase.saved {a : DecArea} {level : Whir.Level} {w : WhirStateW} {m0 st st' : MachineData}
    {folded tail : Array EW} {claim : EW} {s5 : TState}
    (h : GBase a level w m0 st folded tail claim s5) (hf : FFr m0 st')
    (hk : ∀ r ∈ gRegs, st'.regs.getXReg r = st.regs.getXReg r)
    (hs : NativeRustcVm.Layout.Same st.dmem st'.dmem (loc m0 0) 2552)
    (hts : TStateAt st'.dmem (tA m0) a s5) : GBase a level w m0 st' folded tail claim s5 where
  fr := hf
  x19 := by rw [show st'.regs.X19 = st.regs.X19 from hk .X19 (by simp [gRegs])]; exact h.x19
  x20 := (hk .X20 (by simp [gRegs])).trans h.x20
  x22 := by rw [show st'.regs.X22 = st.regs.X22 from hk .X22 (by simp [gRegs])]; exact h.x22
  x29 := by rw [show st'.regs.X29 = st.regs.X29 from hk .X29 (by simp [gRegs])]; exact h.x29
  size := h.size
  le64 := h.le64
  le30 := h.le30
  fold := ewsAt_same h.fold (same_sub hs (o := 40) (len := 1024) (by decide) (by decide)) (by
    rw [Array.length_toList, h.size]; have := h.le64; omega)
  tl := ewsAt_same h.tl (same_sub hs (o := 1096) (len := 480) (by decide) (by decide)) (by
    have := h.le30
    have : tail.size ≤ (w.alphas ++ tail).size := by simp
    rw [Array.length_toList]; omega)
  pts := ewsAt_same h.pts (same_sub hs (o := 1584) (len := 480) (by decide) (by decide)) (by
    have := h.le30; rw [Array.length_toList]; omega)
  cl := ewAt_same h.cl (same_sub hs (o := 24) (len := 16) (by decide) (by decide))
    (Nat.le_refl _)
  ts := hts

/-- **At the glued loop's head** after `i` claims. -/
structure GInv (a : DecArea) (level : Whir.Level) (b : BasisW) (w : WhirStateW)
    (m0 st : MachineData) (folded tail : Array EW) (claim : EW) (s5 : TState) (i : Nat) :
    Prop where
  base : GBase a level w m0 st folded tail claim s5
  x21 : st.regs.X21 = (weightAt m0.regs.X4.toNat b w tail i).c0
  x23 : st.regs.X23 = (weightAt m0.regs.X4.toNat b w tail i).c1
  x24 : st.regs.X24.toBitVec = pA m0 + BitVec.ofNat 64 (512 + 6064 * i)
  x27 : st.regs.X27.toBitVec = pA m0 + BitVec.ofNat 64 (512 + 6064 * w.glued.size)
  x28 : st.regs.X28 = 6064

/-- The registers `b29` to `b31` keep, across the calls. -/
@[expose] def sRegs : List XReg := [.X19, .X20, .X21, .X22, .X23, .X27, .X28, .X29]

theorem sRegs_cs : ∀ r ∈ sRegs, calleeSaved r = true := by decide

theorem gRegs_sub : ∀ r ∈ gRegs, r ∈ sRegs := fun r hr ↦ by
  simp only [gRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp [sRegs]

variable [Host] {a : DecArea} {s0 : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **One glued claim.** -/
theorem gstep (hp : Placed code k) (c : Ctx a s0 level ba b w rounds m0)
    (hge : ∀ g, Spec (Labels.label NativeRustcVmArm.Vm.GluedEval.entryLabel) (GluedEvalPre g) (GluedEvalPost g))
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {st : MachineState} {folded tail : Array EW} {claim : EW} {s5 : TState} {i : Nat}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b29Offset)) (hi : i < w.glued.size)
    (h : GInv a level b w m0 st.data folded tail claim s5 i)
    (next : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b29Offset) → i + 1 < w.glued.size →
      GInv a level b w m0 st'.data folded tail claim s5 (i + 1) →
      Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st')
    (done : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b33Offset) →
      GBase a level w m0 st'.data folded tail claim s5 →
      st'.data.regs.X21 = (weightAt m0.regs.X4.toNat b w tail w.glued.size).c0 →
      st'.data.regs.X23 = (weightAt m0.regs.X4.toNat b w tail w.glued.size).c1 →
      Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st := by
  have hB := h.base
  have hf := hB.fr
  have hN := c.hN'
  have hgl : w.glued.size ≤ 10 := (c.state_at hf).glued_le
  have h30 := hB.le30
  set pt := w.alphas ++ tail
  set g := w.glued[i]
  -- `b29`: `glued_eval(&out, &glued[i], point.get(fold_start..))`.
  have hga : GluedAt st.data.dmem (pA m0 + BitVec.ofNat 64 (512 + 6064 * i)) g :=
    (c.state_at hf).glued i hi
  have hgin : WhirIn m0 (pA m0 + BitVec.ofNat 64 (512 + 6064 * i)) gluedBytes finalLevelStack :=
    c.pIn_sub (o := 512 + 6064 * i) (n := gluedBytes) (by unfold whirBytes gluedBytes; omega)
      (by decide)
  have hwf1 := c.wf1 hf (whirIn_pre (n := 24) hgin (by decide))
  have hm1 := c.match1 (n := 24) hf (r := .X24) h.x24
  refine exec_at (inf hp b29_in_code (by simp [b29])) run_b29 hwf1 hpc hm1
    fun st1 hm1' hpc1 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.FinalLevel.b29Offset + b29.length = k + NativeRustcVmArm.Vm.FinalLevel.b30Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b29_next]] at hpc1
  have hf1 : FFr m0 st1.data := Fr.ofBlock hf hm1 hm1' hwf1 rfl rfl rfl (fun _ h ↦ by cases h)
  have hd1 : st1.data.dmem = st.data.dmem := hm1'.dmem_eq hwf1 rfl
  obtain ⟨hsc, hfs_lt, hfs, -⟩ := id hga
  obtain ⟨hs0, hs1⟩ := ewAt_iff.mp hsc
  have l16 : (fenv m0 st.data [(pA m0 + BitVec.ofNat 64 (512 + 6064 * i), 24)]).load 1 16 8 =
      g.foldStart.toUInt64.toBitVec := load_ofMachine (r := 1) (o := 16) rfl hfs
  have vfs : ((Sym.load 1 16 8).eval (fenv m0 st.data
      [(pA m0 + BitVec.ofNat 64 (512 + 6064 * i), 24)])).toNat = g.foldStart := by
    show ((fenv m0 st.data [(pA m0 + BitVec.ofNat 64 (512 + 6064 * i), 24)]).load 1 16 8).toNat
      = _
    rw [l16]
    simp only [UInt64.toNat_toBitVec, Nat.toUInt64, UInt64.toNat_ofNat']
    omega
  have v29 : ((Sym.reg .X29).eval
      (fenv m0 st.data [(pA m0 + BitVec.ofNat 64 (512 + 6064 * i), 24)])).toNat = pt.size :=
    hB.x29
  have v22 : (Sym.reg .X22).eval
      (fenv m0 st.data [(pA m0 + BitVec.ofNat 64 (512 + 6064 * i), 24)]) = loc m0 1584 := hB.x22
  have x0 : st1.data.regs.X0.toBitVec = loc m0 2552 :=
    reg_val hm1' (r := .X0) (v := .ptr 0 2552) rfl
  have x1 : st1.data.regs.X1.toBitVec = pA m0 + BitVec.ofNat 64 (512 + 6064 * i) :=
    (reg_val hm1' (r := .X1) (v := .ptr 1 0) rfl).trans (eval_ptr rfl)
  have x24 : st1.data.regs.X24.toBitVec = pA m0 + BitVec.ofNat 64 (512 + 6064 * i) :=
    (reg_val hm1' (r := .X24) (v := .ptr 1 0) rfl).trans (eval_ptr rfl)
  have x25 : st1.data.regs.X25 = g.scalar.c0 := UInt64.toBitVec_inj.mp
    ((reg_val hm1' (r := .X25) (v := .load 1 0 8) rfl).trans
      (load_ofMachine (r := 1) (o := 0) rfl (by rw [off_zero]; exact hs0)))
  have x26 : st1.data.regs.X26 = g.scalar.c1 := UInt64.toBitVec_inj.mp
    ((reg_val hm1' (r := .X26) (v := .load 1 8 8) rfl).trans
      (load_ofMachine (r := 1) (o := 8) rfl hs1))
  have x2 : st1.data.regs.X2.toBitVec = if pt.size < g.foldStart then 8#64
      else loc m0 1584 + BitVec.ofNat 64 (16 * g.foldStart) := by
    show (st1.data.regs.getXReg .X2).toBitVec = _
    rw [reg_val hm1' (r := .X2) rfl, ev_above, v29, v22, vfs]
  have x3 : st1.data.regs.X3.toNat = pt.size - g.foldStart := by
    rw [← UInt64.toNat_toBitVec]
    show (st1.data.regs.getXReg .X3).toBitVec.toNat = _
    rw [reg_val hm1' (r := .X3) rfl, ev_satSub, v29, vfs]
  have hpt1 : NativeRustcVm.EWsAt st1.data.dmem (loc m0 1584) pt.toList := by
    rw [hd1]; exact hB.pts
  have hrest : slice st1.data st1.data.regs.X2 st1.data.regs.X3 =
      pt.extract g.foldStart pt.size := by
    rw [extract_drop]
    by_cases hlt' : pt.size < g.foldStart
    · rw [List.drop_eq_nil_of_le (by simp; omega)]
      exact slice_zero (by rw [x3]; omega)
    · exact slice_eq (by rw [x2]; simp only [hlt', ↓reduceIte]) (by rw [x3]; simp)
        (NativeRustcVm.EWsAt.drop hpt1 g.foldStart)
  have hleG : 2672 + gluedEvalStack ≤ finalLevelStack := by decide
  have hsl : SliceOk st1.data st1.data.regs.X2 st1.data.regs.X3 gluedEvalStack := by
    unfold SliceOk
    rw [x3]
    by_cases hlt' : pt.size < g.foldStart
    · rw [x2, show pt.size - g.foldStart = 0 by omega]
      simp only [hlt', ↓reduceIte]
      refine ⟨⟨fun i hi ↦ absurd hi (by omega), by unfold NoWrap; simp⟩, ?_⟩
      have h2224 : gluedEvalStack = 2224 := by decide
      have hb := base_toNat (m0 := m0) (F := 2672 + gluedEvalStack) (by omega)
      unfold OffStack Apart
      rw [stackBelow_eq hf1.sp (N' := gluedEvalStack) (by omega), hb]
      left
      rw [BitVec.toNat_ofNat]
      omega
    · rw [x2]
      simp only [hlt', ↓reduceIte]
      have := c.locIn hf1 hleG (o := 1584 + 16 * g.foldStart) (n := 16 * (pt.size - g.foldStart))
        (by omega)
      rw [← loc_off m0 1584 (16 * g.foldStart)] at this
      exact this
  have hso : ∀ m' : MachineData, GluedEvalPost g st1.data m' →
      SameOutside st1.data.dmem m'.dmem fun q ↦
        InRange (stackBelow st1.data gluedEvalStack) gluedEvalStack q ∨
          InRange (loc m0 2552) 24 q := fun m' hq ↦
    NativeRustcVm.SameOutside.mono hq.2.1 fun q h ↦ by
      rcases h with h | h
      · rw [x0] at h; exact .inr (one_iff.mp h)
      · exact .inl h
  refine c.call hf1 (lo := 2552) (n := 24) hleG (by decide) (hge g) hpc1 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono (hso m' hq) fun q h ↦ by
      rcases h with h | h
      · exact .inl h
      · exact .inr (.inl h), hq.2.2⟩) fun m2 hf2 hq2 hcs2 ↦ ?_
  · refine ⟨c.stackOk' hf1 hleG, ?_, ?_, hsl, ?_⟩
    · show GluedAt st1.data.dmem st1.data.regs.X1.toBitVec g
      rw [x1, hd1]; exact hga
    · show WhirIn st1.data st1.data.regs.X1.toBitVec gluedBytes gluedEvalStack
      rw [x1]; exact c.whirIn' hf1 hleG hgin
    · show WhirIn st1.data st1.data.regs.X0.toBitVec 24 gluedEvalStack
      rw [x0]; exact c.locIn hf1 hleG (by decide)
  -- `b30`: `Some`.
  have hs2 := hso m2 hq2
  obtain ⟨hopt, -, hsv2⟩ := hq2
  rw [x0, hrest] at hopt
  have hsame2 : NativeRustcVm.Layout.Same st1.data.dmem m2.dmem (loc m0 0) 2552 :=
    c.keep_call hf1 hleG (lo := 2552) (n := 24) (NativeRustcVm.SameOutside.mono hs2
      fun q h ↦ by
        rcases h with h | h
        · exact .inl h
        · exact .inr (.inl h)) (by omega) (by decide) (by decide)
  have hts2 : TStateAt m2.dmem (tA m0) a s5 :=
    c.ts_stk hsv2.2.2 (c.call_stk hf1 hleG (by decide) hs2) (by rw [hd1]; exact hB.ts)
  refine c.fblock hp b30_in_code (by simp [b30]) run_b30 rfl rfl rfl hf2
    fun st3 hm3 hpc3 hf3 hd3 hk3 ↦ ?_
  simp only [PcOk] at hpc3
  rw [cbz_load (load_of_wordAt hopt.1)] at hpc3
  simp only [show ((1 : UInt64) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
    show k + NativeRustcVmArm.Vm.FinalLevel.b30Offset + b30.length = k + NativeRustcVmArm.Vm.FinalLevel.b31Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b30_next]] at hpc3
  have hd3' : st3.data.dmem = m2.dmem := hd3
  -- `b31`: `EW::mul(g.scalar, value)`.
  set v := g.weight.eval (pt.extract g.foldStart pt.size)
  have hv := hopt.2
  rw [loc_off] at hv
  obtain ⟨hv0, hv1⟩ := ewAt_iff.mp hv
  rw [loc_off] at hv1
  refine c.fblock hp b31_in_code (by simp [b31]) run_b31 rfl rfl hpc3 hf3
    fun st4 hm4 hpc4 hf4 hd4 hk4 ↦ ?_
  have r0 : st4.data.regs.X0 = g.scalar.c0 :=
    ((reg_of hm4 (r := .X0) (v := .reg .X25) rfl rfl).trans
      ((hk3 .X25 rfl).trans (hcs2 .X25 rfl))).trans x25
  have r1 : st4.data.regs.X1 = g.scalar.c1 :=
    ((reg_of hm4 (r := .X1) (v := .reg .X26) rfl rfl).trans
      ((hk3 .X26 rfl).trans (hcs2 .X26 rfl))).trans x26
  have r2 : st4.data.regs.X2 = v.c0 := reg_of hm4 (r := .X2) (v := .load 0 2560 8) rfl
    (load_ofMachine (r := 0) (o := 2560) rfl (by rw [hd3']; exact hv0))
  have r3 : st4.data.regs.X3 = v.c1 := reg_of hm4 (r := .X3) (v := .load 0 2568 8) rfl
    (load_ofMachine (r := 0) (o := 2568) rfl (by rw [hd3']; exact hv1))
  have e01 : (⟨st4.data.regs.X0, st4.data.regs.X1⟩ : EW) = g.scalar := by rw [r0, r1]
  have e23 : (⟨st4.data.regs.X2, st4.data.regs.X3⟩ : EW) = v := by rw [r2, r3]
  have hleM : 2672 + ewMulStack ≤ finalLevelStack := by decide
  refine c.call hf4 (lo := 0) (n := 0) hleM (by decide) hmul hpc4 (c.stackOk' hf4 hleM)
    (fun m' h ↦ ⟨NativeRustcVm.SameOutside.mono h.2.2.1 fun q h ↦ .inl h, h.2.2.2⟩)
    fun m5 hf5 hq5 hcs5 ↦ ?_
  obtain ⟨hy0, hy1, hs5, hsv5⟩ := hq5
  rw [e01, e23] at hy0 hy1
  have hd4' : st4.data.dmem = m2.dmem := hd4.trans hd3'
  have hstk5 : SameOutside st4.data.dmem m5.dmem (Ctx.Stk m0) :=
    c.call_stk hf4 hleM (lo := 0) (n := 0) (by decide)
      (NativeRustcVm.SameOutside.mono hs5 fun q h ↦ .inl h)
  have hsame5 : NativeRustcVm.Layout.Same st4.data.dmem m5.dmem (loc m0 0) 2552 :=
    c.keep_call hf4 hleM (lo := 0) (n := 0)
      (NativeRustcVm.SameOutside.mono hs5 fun q h ↦ .inl h) (by omega) (by decide) (by decide)
  have hts5 : TStateAt m5.dmem (tA m0) a s5 :=
    c.ts_stk hsv5.2.2 hstk5 (by rw [hd4']; exact hts2)
  have k5 : ∀ r ∈ sRegs, m5.regs.getXReg r = st.data.regs.getXReg r := fun r hr ↦
    (hcs5 r (sRegs_cs r hr)).trans ((reg_of hm4 (kept_of (by decide) r hr) rfl).trans
      ((hk3 r (kept_of (by decide) r hr)).trans ((hcs2 r (sRegs_cs r hr)).trans
        (reg_of hm1' (kept_of (by decide) r hr) rfl))))
  -- `b32`: the sum, the next claim.
  refine c.fblock hp b32_in_code (by simp [b32]) run_b32 rfl rfl rfl hf5
    fun st6 hm6 hpc6 hf6 hd6 hk6 ↦ ?_
  have hd6' : st6.data.dmem = m5.dmem := hd6
  have k6 : ∀ r ∈ gRegs, st6.data.regs.getXReg r = st.data.regs.getXReg r := fun r hr ↦
    (hk6 r (kept_of (by decide) r hr)).trans (k5 r (gRegs_sub r hr))
  have hB6 : GBase a level w m0 st6.data folded tail claim s5 := by
    refine hB.saved hf6 k6 ?_ (by rw [hd6']; exact hts5)
    rw [hd6', ← hd1]
    refine hsame2.trans ?_
    rw [← hd4']
    exact hsame5
  have hgs := gStep_c pt (weightAt m0.regs.X4.toNat b w tail i) g
  have y21 : st6.data.regs.X21 = (weightAt m0.regs.X4.toNat b w tail (i + 1)).c0 := by
    rw [weightAt_succ _ _ _ _ hi, hgs.1, ← hy0, ← (k5 .X21 (by simp [sRegs])).trans h.x21]
    exact UInt64.toBitVec_inj.mp (((reg_val hm6 (r := .X21) rfl).trans (ev_eor _ _ _ _)).trans
      (UInt64.toBitVec_xor _ _).symm)
  have y23 : st6.data.regs.X23 = (weightAt m0.regs.X4.toNat b w tail (i + 1)).c1 := by
    rw [weightAt_succ _ _ _ _ hi, hgs.2, ← hy1, ← (k5 .X23 (by simp [sRegs])).trans h.x23]
    exact UInt64.toBitVec_inj.mp (((reg_val hm6 (r := .X23) rfl).trans (ev_eor _ _ _ _)).trans
      (UInt64.toBitVec_xor _ _).symm)
  have m24 : (m5.regs.getXReg .X24).toBitVec = pA m0 + BitVec.ofNat 64 (512 + 6064 * i) :=
    (congrArg UInt64.toBitVec ((hcs5 .X24 rfl).trans ((reg_of hm4 (r := .X24) (v := .reg .X24)
      rfl rfl).trans ((hk3 .X24 rfl).trans (hcs2 .X24 rfl))))).trans x24
  have m28 : (m5.regs.getXReg .X28).toBitVec = BitVec.ofNat 64 6064 :=
    congrArg UInt64.toBitVec ((k5 .X28 (by simp [sRegs])).trans h.x28)
  have m27 : (m5.regs.getXReg .X27).toBitVec =
      pA m0 + BitVec.ofNat 64 (512 + 6064 * w.glued.size) :=
    (congrArg UInt64.toBitVec (k5 .X27 (by simp [sRegs]))).trans h.x27
  have y24 : st6.data.regs.X24.toBitVec = pA m0 + BitVec.ofNat 64 (512 + 6064 * (i + 1)) := by
    show (st6.data.regs.getXReg .X24).toBitVec = _
    rw [reg_val hm6 (r := .X24) rfl, ev_add2, m24, m28, ofNat_step]
  simp only [PcOk] at hpc6
  rw [ev_next, m24, m28, m27, ofNat_step] at hpc6
  by_cases hn : i + 1 = w.glued.size
  · rw [← hn] at hpc6
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      show k + NativeRustcVmArm.Vm.FinalLevel.b32Offset + b32.length = k + NativeRustcVmArm.Vm.FinalLevel.b33Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b32_next]] at hpc6
    exact done st6 hpc6 hB6 (by rw [← hn]; exact y21) (by rw [← hn]; exact y23)
  · rw [beq_eq_false_iff_ne.mpr (ofNat_ne (pA m0) (x := 512 + 6064 * (i + 1))
      (y := 512 + 6064 * w.glued.size) (by omega) (by omega) (by omega))] at hpc6
    simp only [Bool.not_false, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.FinalLevel.b29Offset) NativeRustcVmArm.Vm.FinalLevel.label_18_at] at hpc6
    refine next st6 hpc6 (by omega) ⟨hB6, y21, y23, y24, ?_, ?_⟩
    · exact (congrArg UInt64.toBitVec ((hk6 .X27 rfl).trans (k5 .X27 (by simp [sRegs])))).trans
        h.x27
    · exact ((hk6 .X28 rfl).trans (k5 .X28 (by simp [sRegs]))).trans h.x28

end

end NativeRustcVmArm.Whir.FinalLevel
