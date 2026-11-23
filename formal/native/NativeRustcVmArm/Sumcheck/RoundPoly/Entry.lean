module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.SumE.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.Code.Vm.TStateSumcheckRoundPoly.Names
public import NativeRustcVmArm.Sumcheck.RoundPoly.SomeRead
public import NativeRustcVmArm.Sumcheck.RoundPoly.NoneRead
public import NativeRustcVmArm.Transcript.Glue

/-!
# `sumcheck_round_poly`'s entry

`b0` saves the registers in the frame (`frame_of_b0`) and tests `eq`'s tag. In equality mode `b1`
loads the factor and calls `read_scalars` for `msg[1..count]` (`some_entry`, then `some_b2`); in
plain mode `b9` calls `read_scalar` into the frame (`none_entry`, then `none_b10`).
-/

namespace NativeRustcVmArm.Sumcheck.RoundPoly

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateSumcheckRoundPoly
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Sumcheck

@[expose] public section

/-- The saved registers, in their slots' order from offset 32 (`slotWords`). -/
def slotRegs : List XReg := [.X30, .X27, .X26, .X25, .X24, .X23, .X22, .X21, .X20, .X19]

/-- The entry's environment: the frame and `n` bytes of `eq`. -/
def env0 (m0 : MachineData) (n : Nat) : Env :=
  Env.ofMachine m0 [(fr m0, 112), (m0.regs.X4.toBitVec, n)]

end

public section

variable [Host] {a : DecArea} {s : TState} {e : Option EW} {m0 : MachineData} {k : Nat}

theorem wf_env0 (hpre : RoundPolyPre a s e m0) {n : Nat} (hn : n ≤ 24)
    (hmap : Mapped m0.dmem m0.regs.X4.toBitVec n) : (env0 m0 n).WF := by
  have c := ctx_of hpre
  have hfr := c.mapped_frame0 (o := 0) (n := 112) (by omega)
  rw [NativeRustcVm.addr_add_zero] at hfr
  refine Env.wf_of ⟨⟨hfr, c.noWrap_fr⟩,
      ⟨hmap, NativeRustcVm.NoWrap.mono hpre.2.2.2.2.2.2.2.1 hn⟩, trivial⟩
    (List.Pairwise.cons ?_ (List.pairwise_singleton _ _))
  simp only [List.mem_singleton, forall_eq]
  have := c.apart_of_stack (o := 0) (k := 112) (by omega) hpre.2.2.2.2.2.2.2.2.1
  rw [NativeRustcVm.addr_add_zero] at this
  exact NativeRustcVm.Apart.mono this (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by omega)

theorem match_env0 (hpre : RoundPolyPre a s e m0) {n : Nat} :
    Match (env0 m0 n) (init [(112, true), (n, false)] (.ptr 0 112) [(.X4, .ptr 1 0)]) m0 := by
  have c := ctx_of hpre
  have hal : (fr m0).toNat % 16 = 0 := by
    rw [c.fr]; have := c.stack.1; have := c.spN; have := c.le; omega
  refine match_ofMachine ⟨rfl, fun _ ↦ hal, rfl, by simp, trivial⟩ ?_ ⟨?_, trivial⟩ trivial trivial
    trivial
  · simp [Sym.eval, Env.base, Env.ofMachine, frAt]
  · simp [Sym.eval, Env.base, Env.ofMachine]; rfl

/-- **The frame after `b0`'s writes** (`S`'s writes, all in the frame): the saved registers in
their slots. -/
theorem frame_of_b0 (hpre : RoundPolyPre a s e m0) {n : Nat} (hwf : (env0 m0 n).WF)
    {S : SState} {m : MachineData} (hm : Match (env0 m0 n) S m) (hsp : S.sp = .ptr 0 0)
    (hS : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 112)
    (hws : ∀ i < 10, ∀ j < 8,
      findWrite 0 (32 + 8 * i + j) S.mem = some (.reg (slotRegs.getD i .X0), j))
    (h28 : S.reg .X28 = some (.reg .X28)) (h29 : S.reg .X29 = some (.reg .X29)) :
    RFrame m0 m := by
  have c := ctx_of hpre
  have hW : ∀ p, Written (env0 m0 n) S p → InRange (fr m0) 112 p := fun p hw ↦
    Written.inRange rfl c.noWrap_fr hS hw
  refine ⟨⟨?_, hm.kept hwf, fun p hp ↦ hm.get?_mem0 hwf fun hw ↦
      not_rc hpre (chg_frame hpre (hW p hw)) hp⟩, ?_,
    UInt64.toBitVec_inj.mp (hm.regs _ _ h28), UInt64.toBitVec_inj.mp (hm.regs _ _ h29),
    fun p hp ↦ hm.get?_mem0 hwf fun hw ↦ hp (chg_frame hpre (hW p hw))⟩
  · rw [hm.sp, hsp]; simp [Sym.eval, env0, Env.base, Env.ofMachine]
  · have key : ∀ i < 10, NativeRustcVm.WordAt m.dmem (fr m0 + BitVec.ofNat 64 (32 + 8 * i))
        (m0.regs.getXReg (slotRegs.getD i .X0)) := fun i hi ↦ by
      have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm (r := 0) (o := 32 + 8 * i) rfl
        (by omega) (hws i hi)
      rw [show (Sym.reg (slotRegs.getD i .X0)).eval (env0 m0 n) =
        (m0.regs.getXReg (slotRegs.getD i .X0)).toBitVec by simp [Sym.eval, env0]] at this
      exact this
    rw [NativeRustcVm.wordsAt_iff]
    intro i hi
    simp only [slotWords, List.length_cons, List.length_nil] at hi
    rw [NativeRustcVm.addr_add_add]
    match i, hi with
    | 0, _ => exact key 0 (by decide)
    | 1, _ => exact key 1 (by decide)
    | 2, _ => exact key 2 (by decide)
    | 3, _ => exact key 3 (by decide)
    | 4, _ => exact key 4 (by decide)
    | 5, _ => exact key 5 (by decide)
    | 6, _ => exact key 6 (by decide)
    | 7, _ => exact key 7 (by decide)
    | 8, _ => exact key 8 (by decide)
    | 9, _ => exact key 9 (by decide)

omit [Host] in
/-- `count - 1`, computed from X1. -/
theorem toNat_sub_one (h : 2 ≤ m0.regs.X1.toNat) :
    (m0.regs.X1.toBitVec - 1#64).toNat = cnt m0 - 1 := by
  have : 1 ≤ m0.regs.X1.toBitVec.toNat := by simp only [UInt64.toNat] at h; omega
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 (by simpa using this))]
  rfl

/-- **Equality mode**: `b0`, `b1` loads the factor and calls `read_scalars` for
`msg[1..count]`, then `some_b2`. -/
theorem some_entry (hp : Placed code k)
    (hrss : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hsum : Spec (Labels.label NativeRustcVmArm.Vm.SumE.entryLabel) SumEPre SumEPost)
    (hbl : Spec (Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {ev : EW} (hpre : RoundPolyPre a s (some ev) m0) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ RoundPolyPost a s (some ev) m0 st.data)
      ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b0Offset)⟩ := by
  have c := ctx_of hpre
  have hc2 : 2 ≤ cnt m0 := hpre.2.2.2.2.1
  have hc5 : cnt m0 ≤ maxCount := hpre.2.2.2.2.2.1
  obtain ⟨htag, hev⟩ : OptEWAt m0.dmem m0.regs.X4.toBitVec (some ev) := hpre.2.2.2.2.2.2.1
  have hev' := NativeRustcVm.ewAt_iff.1 hev
  have hmap : Mapped m0.dmem m0.regs.X4.toBitVec 24 :=
    NativeRustcVm.mapped_append_iff (n := 8) (m := 16) |>.2 ⟨htag.mapped, hev.mapped⟩
  have hwf := wf_env0 hpre (Nat.le_refl _) hmap
  have hm : Match (env0 m0 24) entryS m0 := match_env0 hpre
  have hk0 : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b0Offset) := b0_in_code.trans hp.1 (by simp [b0])
  have hk1 : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b1Offset) := b1_in_code.trans hp.1 (by simp [b1])
  have hb1 : (env0 m0 24).base 1 = m0.regs.X4.toBitVec := rfl
  refine exec_then hk0 run_b0 hwf hm fun st hm' hpc ↦ ?_
  have htag4 : (env0 m0 24).load 1 0 4 = BitVec.ofNat 64 1 :=
    NativeRustcVmArm.Transcript.load4_of_tag (Or.inr rfl)
      (by rw [hb1, NativeRustcVm.addr_add_zero]; exact htag)
  simp only [PcOk] at hpc
  sym_simp at hpc
  rw [htag4] at hpc
  simp (config := { decide := true }) only [↓reduceIte] at hpc
  have hm0 : Match (env0 m0 24) (after b0 entryS) st.data := by rw [after_eq run_b0]; exact hm'
  refine exec_at hk1 run_b1 hwf hpc hm0 fun st1 hm1 hpc1 ↦ ?_
  have hm1' : Match (env0 m0 24) (after b1 (after b0 entryS)) st1.data := by
    rw [after_eq run_b1]; exact hm1
  have hS1 : ∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 112 := by
    rw [after_eq run_b1]; decide +kernel
  have hf1 : RFrame m0 st1.data :=
    frame_of_b0 hpre hwf hm1' (by rw [after_eq run_b1]) hS1
      (by rw [after_eq run_b1]; decide +kernel) (by rw [after_eq run_b1]; rfl)
      (by rw [after_eq run_b1]; rfl)
  have hx27 : (st1.data.regs.getXReg .X27).toNat = cnt m0 - 1 := by
    rw [UInt64.toNat, hm1.regs .X27 _ rfl]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    exact toNat_sub_one hc2
  have hg1 : SomeRegs m0 ev st1.data := by
    refine ⟨UInt64.toBitVec_inj.mp ((hm1.regs .X19 _ rfl).trans rfl),
      UInt64.toBitVec_inj.mp ((hm1.regs .X20 _ rfl).trans rfl),
      UInt64.toBitVec_inj.mp ((hm1.regs .X21 _ rfl).trans rfl),
      UInt64.toBitVec_inj.mp ((hm1.regs .X22 _ rfl).trans rfl),
      UInt64.toBitVec_inj.mp ((hm1.regs .X23 _ rfl).trans (load_word (r := 1) (off := 8) ?_)),
      UInt64.toBitVec_inj.mp ((hm1.regs .X24 _ rfl).trans (load_word (r := 1) (off := 16) ?_)),
      hx27⟩
    · rw [hb1]; exact hev'.1
    · rw [hb1]
      have := hev'.2
      rwa [NativeRustcVm.addr_add_add] at this
  have h30 : st1.data.regs.X0 = m0.regs.X0 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X0 _ rfl).trans rfl)
  have h31 : st1.data.regs.X1.toBitVec = msgAt m0 + BitVec.ofNat 64 16 := by
    rw [show st1.data.regs.X1 = st1.data.regs.getXReg .X1 from rfl, hm1.regs .X1 _ rfl]
    simp [Sym.eval, BinOp.apply, env0, Env.ofMachine]; rfl
  have h32 : st1.data.regs.X2.toNat = cnt m0 - 1 := by
    rw [show st1.data.regs.X2 = st1.data.regs.getXReg .X2 from rfl, UInt64.toNat,
      hm1.regs .X2 _ rfl]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    exact toNat_sub_one hc2
  have hts1 : TStateAt st1.data.dmem (tAt m0) a s :=
    tstate_keep hpre (hm1'.sameOutside hwf) (hm1'.kept hwf)
      (fun p hp ↦ Or.inr (c.inRange_frame (Written.inRange rfl c.noWrap_fr hS1 hp))) hpre.2.2.1
  refine call_then hpc1 (hrss a s) ?pre fun st2 hpc2 hpost2 ↦ ?_
  case pre =>
    simp only [ReadScalarsPre, h30, h31, h32]
    exact ⟨c.stackOk hf1.at_ (by decide), c.rcAt hf1.at_ (by decide), hts1,
      c.tstateOk hf1.at_ (by decide), msgOut hpre hf1 (by decide) (by decide) (by omega)⟩
  simp only [ReadScalarsPost, h30, h31, h32] at hpost2
  obtain ⟨hok2, hxs2, hnext2, hs2, hsv2⟩ := hpost2
  have hR2 : ∀ p, (InRange (msgAt m0 + BitVec.ofNat 64 16) (16 * (cnt m0 - 1)) p ∨
      InRange (tAt m0) tstateBytes p) → Chg m0 p ∧ ¬ InRange (fr m0) 112 p := by
    intro p hp
    rcases hp with hp | hp
    · have := (msg_bounds hpre (o := 16) (by decide) (by omega) hp).1
      exact ⟨Or.inl this, msg_not_fr hpre this⟩
    · exact ⟨Or.inr (Or.inl hp), t_not_fr hpre hp⟩
  have hf2 : RFrame m0 st2.data :=
    hf1.after_call hpre (Nc := readScalarsStack) (by decide) hR2
      (fun p hp ↦ hs2 p fun h ↦ hp (or_assoc.2 h)) hsv2
  have hg2 := hg1.of_saved hsv2
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2
  subst hpc2
  exact some_b2 hp hsum hbl hgr hmul hpre hf2 hg2 hok2 fun tail s1 h ↦
    ⟨hxs2 tail s1 h, hnext2 tail s1 h⟩

/-- **Plain mode**: `b0`, `b9` calls `read_scalar` into the frame's `Option<EW>` at `8`, then
`none_b10`. -/
theorem none_entry (hp : Placed code k)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hrss : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hsum : Spec (Labels.label NativeRustcVmArm.Vm.SumE.entryLabel) SumEPre SumEPost)
    (hbl : Spec (Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hpre : RoundPolyPre a s none m0) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ RoundPolyPost a s none m0 st.data)
      ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b0Offset)⟩ := by
  have c := ctx_of hpre
  have htag : NativeRustcVm.WordAt m0.dmem m0.regs.X4.toBitVec 0 := hpre.2.2.2.2.2.2.1
  have hwf := wf_env0 hpre (n := 8) (by omega) htag.mapped
  have hm : Match (env0 m0 8) entryN m0 := match_env0 hpre
  have hk0 : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b0Offset) := b0_in_code.trans hp.1 (by simp [b0])
  have hk9 : b9.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b9Offset) := b9_in_code.trans hp.1 (by simp [b9])
  have hl4 : Labels.label NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.label_4 = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b9Offset) :=
    hp.label (j := NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b9Offset) NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.label_4_at
  have hb1 : (env0 m0 8).base 1 = m0.regs.X4.toBitVec := rfl
  refine exec_then hk0 run_b0n hwf hm fun st hm' hpc ↦ ?_
  have htag4 : (env0 m0 8).load 1 0 4 = BitVec.ofNat 64 0 :=
    NativeRustcVmArm.Transcript.load4_of_tag (Or.inl rfl)
      (by rw [hb1, NativeRustcVm.addr_add_zero]; exact htag)
  simp only [PcOk] at hpc
  sym_simp at hpc
  rw [htag4] at hpc
  simp (config := { decide := true }) only [↓reduceIte] at hpc
  rw [hl4] at hpc
  have hm0 : Match (env0 m0 8) (after b0 entryN) st.data := by rw [after_eq run_b0n]; exact hm'
  refine exec_at hk9 run_b9 hwf hpc hm0 fun st1 hm1 hpc1 ↦ ?_
  have hm1' : Match (env0 m0 8) (after b9 (after b0 entryN)) st1.data := by
    rw [after_eq run_b9]; exact hm1
  have hS1 : ∀ w ∈ (after b9 (after b0 entryN)).mem, w.r = 0 ∧ w.off + w.n ≤ 112 := by
    rw [after_eq run_b9]; decide +kernel
  have hf1 : RFrame m0 st1.data :=
    frame_of_b0 hpre hwf hm1' (by rw [after_eq run_b9]) hS1
      (by rw [after_eq run_b9]; decide +kernel) (by rw [after_eq run_b9]; rfl)
      (by rw [after_eq run_b9]; rfl)
  have hg1 : ConstRegs m0 st1.data :=
    ⟨UInt64.toBitVec_inj.mp ((hm1.regs .X19 _ rfl).trans rfl),
      UInt64.toBitVec_inj.mp ((hm1.regs .X20 _ rfl).trans rfl),
      UInt64.toBitVec_inj.mp ((hm1.regs .X21 _ rfl).trans rfl),
      UInt64.toBitVec_inj.mp ((hm1.regs .X22 _ rfl).trans rfl),
      UInt64.toBitVec_inj.mp ((hm1.regs .X25 _ rfl).trans rfl)⟩
  have h30 : st1.data.regs.X0.toBitVec = fr m0 + BitVec.ofNat 64 8 := by
    rw [show st1.data.regs.X0 = st1.data.regs.getXReg .X0 from rfl, hm1.regs .X0 _ rfl]
    simp [Sym.eval, env0, Env.base, Env.ofMachine]
  have h31 : st1.data.regs.X1 = m0.regs.X0 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X1 _ rfl).trans rfl)
  have hts1 : TStateAt st1.data.dmem (tAt m0) a s :=
    tstate_keep hpre (hm1'.sameOutside hwf) (hm1'.kept hwf)
      (fun p hp ↦ Or.inr (c.inRange_frame (Written.inRange rfl c.noWrap_fr hS1 hp))) hpre.2.2.1
  refine call_then hpc1 (hrs a s) ?pre fun st2 hpc2 hpost2 ↦ ?_
  case pre =>
    simp only [ReadScalarPre, h30, h31]
    exact ⟨c.stackOk hf1.at_ (by decide), c.rcAt hf1.at_ (by decide), hts1,
      c.tstateOk hf1.at_ (by decide), c.outOk hf1.at_ (by decide) (o := 8) (n := 24) (by omega)⟩
  simp only [ReadScalarPost, h30, h31] at hpost2
  obtain ⟨hopt2, hnext2, hs2, hsv2⟩ := hpost2
  have hfr8 : ∀ p, InRange (fr m0 + BitVec.ofNat 64 8) 24 p →
      InRange (fr m0) 112 p ∧ ¬ InRange (fr m0 + BitVec.ofNat 64 32) 80 p := by
    intro p hp
    have hl := Ctx.sp_lt m0; have := c.spN; have := c.le
    rw [Sym.inRange_iff (c.noWrap_frame (o := 8) (n := 24) (by omega)),
      c.frame_toNat (by omega)] at hp
    rw [Sym.inRange_iff c.noWrap_fr, c.fr,
      Sym.inRange_iff (c.noWrap_frame (o := 32) (n := 80) (by omega)), c.frame_toNat (by omega)]
    omega
  have hR2 : ∀ p, (InRange (fr m0 + BitVec.ofNat 64 8) 24 p ∨ InRange (tAt m0) tstateBytes p) →
      Chg m0 p ∧ ¬ InRange (fr m0 + BitVec.ofNat 64 32) 80 p := by
    intro p hp
    rcases hp with hp | hp
    · exact ⟨chg_frame hpre (hfr8 p hp).1, (hfr8 p hp).2⟩
    · exact ⟨Or.inr (Or.inl hp), fun h ↦ t_not_fr hpre hp (slots_in_fr hpre h)⟩
  have hf2 : RFrame m0 st2.data :=
    hf1.after_slots hpre (Nc := readScalarStack) (by decide) hR2
      (fun p hp ↦ hs2 p fun h ↦ hp (or_assoc.2 h)) hsv2.2.1 hsv2.2.2 (hsv2.1 .X28 rfl)
      (hsv2.1 .X29 rfl)
  have hg2 : ConstRegs m0 st2.data :=
    ⟨(hsv2.1 .X19 rfl).trans hg1.x19, (hsv2.1 .X20 rfl).trans hg1.x20,
      (hsv2.1 .X21 rfl).trans hg1.x21, (hsv2.1 .X22 rfl).trans hg1.x22,
      (hsv2.1 .X25 rfl).trans hg1.x25⟩
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2
  subst hpc2
  exact none_b10 hp hrss hsum hbl hgr hpre hf2 hg2 hopt2 hnext2

end

end NativeRustcVmArm.Sumcheck.RoundPoly
