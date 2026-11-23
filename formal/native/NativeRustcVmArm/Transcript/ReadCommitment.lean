module

public import NativeRustcVmArm.Code.Vm.TStateReadCommitment.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Transcript.Callee
public import NativeRustcVmArm.Transcript.ReadCommitment.Exec
public import NativeVm.Equiv.Transcript

/-!
# `TState::read_commitment` on AArch64

**`readCommitment_spec`**: X0 becomes `readCommitment height width`'s `Some`/`None` and the
`TState` at X0 its state, given `read_scalar`'s contract. `b0` saves X30, X23 to X19 and reads a
scalar into the frame (`call_read`); `b1` tests its tag (`0`: `b6` returns `0`); `b2` keeps it in
X23, X22 and reads a second (`b3`: its tag); `b4` compares the roots' count with `8` (below, by the
precondition); `b5` stores the root (the two elements, the height, the width) and advances the
count.
-/

namespace NativeRustcVmArm.Transcript.ReadCommitment

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateReadCommitment
open NativeRustcVm.Transcript NativeVm.Model NativeRustcArm

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 80 := by decide

theorem readScalar_roots {s s' : TState} {x : EW} (h : readScalar.run s = some (x, s')) :
    s'.roots = s.roots := by
  rw [NativeVm.Equiv.readScalar_run, NativeVm.Equiv.nextScalar_run] at h
  split at h
  · cases h
  · cases hx : s.stream[s.cursor]? with
    | none => rw [hx] at h; cases h
    | some y => rw [hx] at h; cases h; rfl

theorem run_eq (h w : Nat) (s : TState) :
    (readCommitment h w).run s = (readScalar.run s).bind fun p ↦
      (readScalar.run p.2).bind fun q ↦
        some ((), { q.2 with roots := q.2.roots.push ⟨#v[p.1.c0, p.1.c1, q.1.c0, q.1.c1], h, w⟩ }) :=
  NativeVm.Equiv.readCommitment_run h w s

theorem ofInt_neg368 : (BitVec.ofInt 64 (-368)).toNat = 2 ^ 64 - 368 := by
  rw [BitVec.toNat_ofInt]; rfl

theorem ofInt_neg752 : (BitVec.ofInt 64 (-752)).toNat = 2 ^ 64 - 752 := by
  rw [BitVec.toNat_ofInt]; rfl

theorem toUInt64_succ {n : Nat} (h : n + 1 < 2 ^ 64) :
    UInt64.ofBitVec (n.toUInt64.toBitVec + BitVec.ofNat 64 1) = (n + 1).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have e : ∀ m, m < 2 ^ 64 → m.toUInt64.toNat = m := fun m hm ↦ by
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hm
  rw [e _ h]
  show (n.toUInt64.toBitVec + BitVec.ofNat 64 1).toNat = _
  rw [BitVec.toNat_add, UInt64.toNat_toBitVec, e _ (by omega), BitVec.toNat_ofNat]
  omega

theorem toUInt64_toNat (x : UInt64) : x.toNat.toUInt64 = x :=
  UInt64.toNat_inj.mp (by
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt x.toNat_lt)

/-- An interval of the `TState` is at its offsets. -/
theorem touch_sub {t q : BitVec 64} {o n : Nat} (hT : NativeRustcVm.NoWrap t 760) (hle : o + n ≤ 760)
    (h : NativeRustcVm.InRange (off t o) n q) {W : Nat → Prop} (hW : ∀ j, o ≤ j → j < o + n → W j) :
    Touch t 760 W q := by
  obtain ⟨j, hj, ⟨h1, h2⟩, rfl⟩ := touch_of_inRange hT hle h
  exact ⟨j, hj, hW j h1 h2, rfl⟩

variable [Host] {k : Nat}

/-- What the transcript function may change: the `TState` and its stack. -/
abbrev Out (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange m0.regs.X0.toBitVec tstateBytes q ∨
    NativeRustcVm.InRange (stackBelow m0 readCommitmentStack) readCommitmentStack q

/-- **A call of `read_scalar`** from the frame, its output at `fb + 8`. -/
theorem call_read
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    {a : DecArea} {m0 : MachineData} (hst : StackOk m0 readCommitmentStack)
    (hrc : RcAt m0 readCommitmentStack) (htok : TStateOk m0 m0.regs.X0.toBitVec a readCommitmentStack)
    {s' : TState} {st : MachineState} {env : Env} {next : Int64}
    (hpc : PcOk env (.call NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) next st) (hf : Frame m0 80 slots st.data)
    (hX0 : st.data.regs.X0.toBitVec = off (frameBase m0 80) 8)
    (hX1 : st.data.regs.X1.toBitVec = m0.regs.X0.toBitVec)
    (hts : TStateAt st.data.dmem m0.regs.X0.toBitVec a s')
    (hso : SameOutside m0.dmem st.data.dmem (Out m0)) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = next → Frame m0 80 slots st'.data →
      OptEWAt st'.data.dmem (off (frameBase m0 80) 8) ((readScalar.run s').map (·.1)) →
      NextAt st'.data.dmem m0.regs.X0.toBitVec a (readScalar.run s') →
      SameOutside m0.dmem st'.data.dmem (Out m0) → Saved st.data st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  set t := m0.regs.X0.toBitVec
  set fb := frameBase m0 80
  have hn : readCommitmentStack ≤ m0.regs.SP.toNat := hst.2.1
  have hfnw : fb.toNat + 80 ≤ 2 ^ 64 :=
    frame_noWrap (m := m0) (F := 80) (by have : readCommitmentStack = 624 := rfl; omega)
  have hTn := hts.footprint.1.2
  have hTF : NativeRustcVm.Apart t 760 fb 80 := apart_frame htok.1 hn (by decide)
  have hslot : ∀ p ∈ slots, ∀ i < 8, NativeRustcVm.InRange fb 80 (off fb (p.1 + i)) :=
    fun p hp i hi ↦ inRange_off_self (by have := slots_le p hp; omega) (by omega)
  have hsnw : NativeRustcVm.NoWrap (stackBelow m0 readCommitmentStack) readCommitmentStack := by
    show _ + readCommitmentStack ≤ _
    rw [toNat_stackBelow hn]; have := m0.regs.SP.toNat_lt; omega
  have hrcOut : ∀ q, Out m0 q → ¬ NativeRustcVm.InRange rcAddr 192 q := by
    rintro q (hq | hq) h
    · exact not_inRange_of_apart (Apart.symm' htok.2.2) hrc.2.1 hTn h hq
    · exact not_inRange_of_apart hrc.2.2 hrc.2.1 hsnw h hq
  have hsp : st.data.regs.SP.toNat = m0.regs.SP.toNat - 80 := by
    rw [← UInt64.toNat_toBitVec, hf.sp, frameBase_toNat hn (by decide)]
  have hpre : ReadScalarPre a s' st.data := by
    unfold ReadScalarPre
    rw [hX1, hX0]
    exact ⟨stackOk_callee hst hf.kept hf.sp (by decide) (by decide) (by decide),
      RcAt.callee hrc (rc_keep hso hrcOut) hn (by decide) hsp (by decide), hts,
      TStateOk.callee htok hf.sp hn (by decide) (by decide),
      OutOk.frame hst (by decide) (by decide) hf.sp hf.kept (by decide) htok hrc⟩
  refine call_then hpc (hrs a s') hpre fun st' hpc' ⟨hout, hnext, hs, hsv⟩ => ?_
  rw [hX0] at hout
  rw [hX1] at hnext
  rw [hX0, hX1] at hs
  have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st.data readScalarStack) readScalarStack q →
      NativeRustcVm.InRange (stackBelow m0 readCommitmentStack) readCommitmentStack q ∧
        ¬ NativeRustcVm.InRange fb 80 q :=
    fun q hq ↦ inRange_callee hf.sp hn (by decide) (by decide) hq
  have hf' : Frame m0 80 slots st'.data := by
    refine Frame.call_slots hf hsv hs fun p hp i hi h ↦ ?_
    rcases h with h | h | h
    · exact not_slot_out hfnw (by decide) slots_le (by decide) p hp i hi h
    · exact not_inRange_of_apart hTF hTn hfnw h (hslot p hp i hi)
    · exact (hcal _ h).2 (hslot p hp i hi)
  refine cont st' hpc' hf' hout hnext (fun q hq ↦ ?_) hsv
  simp only [Out, not_or] at hq
  have hqf : ¬ NativeRustcVm.InRange fb 80 q :=
    fun h ↦ hq.2 (inRange_frame_stack hn (by decide) h)
  rw [hs q (by
    rintro (h | h | h)
    · exact hqf (inRange_of_off hfnw (by decide) h)
    · exact hq.1 h
    · exact hq.2 (hcal q h).1)]
  exact hso q (by simp only [Out, not_or]; exact hq)

/-- `b6`: `0`, the epilogue. -/
theorem finish_fail (hp : Placed code k) {m0 : MachineData} (hst : StackOk m0 readCommitmentStack)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateReadCommitment.b6Offset)) (hf : Frame m0 80 slots st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ st'.data.regs.X0 = 0 ∧
      st'.data.dmem = st.data.dmem ∧ Saved m0 st'.data) st := by
  have hfnw := frame_noWrap (m := m0) (F := 80) (by
    have := hst.2.1; have : readCommitmentStack = 624 := rfl; omega)
  have hwf : (frameEnv m0 st.data 80 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 80) hst (by decide)) hf.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 80 []) failS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 hwf hpc hm fun st1 hm1 hpc1 => ?_
  obtain ⟨hepi, hmem, hx0⟩ := after_eq run_b6 ▸ ok_b6
  obtain ⟨hsv, hsl⟩ := Frame.epilogue hf hwf hm1 hepi
  have hx30 : st1.data.regs.X30 = m0.regs.X30 := hsl (32, .X30) (List.mem_cons_self ..)
  exact .done _ ⟨by simp only [PcOk] at hpc1; rw [hpc1]; simp only [retOf, hx30],
    UInt64.toBitVec_inj.mp (hm1.regs .X0 _ hx0), hm1.dmem_eq hwf hmem, hsv⟩


/-- **`TState::read_commitment` meets its contract.** -/
theorem readCommitment_spec (hp : Placed code k)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (a : DecArea) (s : TState) :
    Spec (Labels.label NativeRustcVmArm.Vm.TStateReadCommitment.entryLabel) (ReadCommitmentPre a s) (ReadCommitmentPost a s) := by
  rintro m0 ⟨hst, hrc, hts, htok, hroots⟩
  set t := m0.regs.X0.toBitVec with htdef
  set fb := frameBase m0 80 with hfb
  have hC : readCommitmentStack = 624 := rfl
  have hn : readCommitmentStack ≤ m0.regs.SP.toNat := hst.2.1
  have hfnw : fb.toNat + 80 ≤ 2 ^ 64 := frame_noWrap (m := m0) (F := 80) (by omega)
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, -⟩ := hts.footprint
  have hTn' : t.toNat + 760 ≤ 2 ^ 64 := hTn
  have hTF : NativeRustcVm.Apart t 760 fb 80 := apart_frame htok.1 hn (by decide)
  have hAF : NativeRustcVm.Apart a.words (8 * a.len) fb 80 := apart_frame htok.2.1 hn (by decide)
  have hRF : ∀ q, NativeRustcVm.InRange fb 80 q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q :=
    fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hTF hTn hfnw h hq,
      fun h ↦ not_inRange_of_apart hAF hAn hfnw h hq⟩
  have hfr : ∀ {d : MachineData}, Frame m0 80 slots d → (frameEnv m0 d 80 []).WF := fun hf ↦
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 80) hst (by decide)) hf.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  -- `b0`: the prologue, `bl read_scalar`.
  have hm0 : Match (frameEnv m0 m0 80 []) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      frameBase_add.symm trivial trivial trivial trivial
  have hwf0 : (frameEnv m0 m0 80 []).WF :=
    Env.wf_of ⟨⟨frame_mapped (F := 80) hst (by decide), hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  unfold NativeRustcVmArm.Vm.TStateReadCommitment.entryLabel
  rw [hp.label (j := NativeRustcVmArm.Vm.TStateReadCommitment.entryOffset) NativeRustcVmArm.Vm.TStateReadCommitment.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 hm0 fun st1 hm1 hpc1 => ?_
  obtain ⟨hpro, hws1, hx0, hx1, hx19, hx20, hx21⟩ := after_eq run_b0 ▸ ok_b0
  have hf1 : Frame m0 80 slots st1.data := Frame.of_prologue hwf0 hm1 hpro slots_le
  have hs1 : SameOutside m0.dmem st1.data.dmem (NativeRustcVm.InRange fb 80) :=
    sameOutside_region hwf0 hm1 rfl hws1
  have hso1 : SameOutside m0.dmem st1.data.dmem (Out m0) :=
    SameOutside.mono hs1 fun q hq ↦ Or.inr (inRange_frame_stack hn (by decide) hq)
  have hX19 : st1.data.regs.X19 = m0.regs.X0 := UInt64.toBitVec_inj.mp (hm1.regs .X19 _ hx19)
  have hX20 : st1.data.regs.X20 = m0.regs.X2 := UInt64.toBitVec_inj.mp (hm1.regs .X20 _ hx20)
  have hX21 : st1.data.regs.X21 = m0.regs.X1 := UInt64.toBitVec_inj.mp (hm1.regs .X21 _ hx21)
  refine call_read hrs hst hrc htok hpc1 hf1 (by
      show (st1.data.regs.getXReg .X0).toBitVec = _; rw [hm1.regs .X0 _ hx0]; rfl)
    (by show (st1.data.regs.getXReg .X1).toBitVec = _; rw [hm1.regs .X1 _ hx1]; rfl)
    (hts.frame hf1.kept hRF hs1) hso1 fun st2 hpc2 hf2 hout2 hnext2 hso2 hsv2 => ?_
  have h19₂ : st2.data.regs.X19 = m0.regs.X0 := (hsv2.1 .X19 rfl).trans hX19
  have h20₂ : st2.data.regs.X20 = m0.regs.X2 := (hsv2.1 .X20 rfl).trans hX20
  have h21₂ : st2.data.regs.X21 = m0.regs.X1 := (hsv2.1 .X21 rfl).trans hX21
  -- `b1`: the first tag.
  have hm2 : Match (frameEnv m0 st2.data 80 []) tagS st2.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf2.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 (hfr hf2)
    (hpc2.trans (by change Host.addrOf (k + NativeRustcVmArm.Vm.TStateReadCommitment.b0Offset + NativeRustcVmArm.Vm.TStateReadCommitment.b0.length) = Host.addrOf (k + NativeRustcVmArm.Vm.TStateReadCommitment.b1Offset); rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateReadCommitment.b0_next])) hm2 fun st3 hm3 hpc3 => ?_
  obtain ⟨hmid3, hmem3, hcs3⟩ := after_eq run_b1 ▸ ok_b1
  have hf3 : Frame m0 80 slots st3.data := Frame.of_block hf2 (hfr hf2) hm3 hmid3 slots_le
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq (hfr hf2) hmem3
  have hk3 : ∀ r, calleeSaved r = true → st3.data.regs.getXReg r = st2.data.regs.getXReg r :=
    fun r hr ↦ Match.reg_eq hm2 hm3 (by cases r <;> rfl) (hcs3 r hr)
  have hso3 : SameOutside m0.dmem st3.data.dmem (Out m0) := by rw [hd3]; exact hso2
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  cases hr1 : readScalar.run s with
  | none =>
    rw [hr1] at hout2
    have h0 : NativeRustcVm.WordAt st2.data.dmem (off fb 8) 0 := hout2
    rw [load_ofMachine (o := 8) rfl h0] at hpc3
    simp (config := { decide := true }) only [↓reduceIte] at hpc3
    have hnone : (readCommitment m0.regs.X1.toNat m0.regs.X2.toNat).run s = none := by
      rw [run_eq, hr1]; rfl
    refine Eventually.mono (finish_fail hp hst (hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.TStateReadCommitment.b6Offset) NativeRustcVmArm.Vm.TStateReadCommitment.label_4_at)) hf3)
      fun st' ⟨hpc', hx0', hd', hsv'⟩ ↦ ⟨hpc', ?_, ?_, ?_, hsv'⟩
    · rw [hnone, hx0']; rfl
    · intro u s' h; rw [hnone] at h; cases h
    · intro q hq; rw [hd']; exact hso3 q hq
  | some p =>
  obtain ⟨x0, s1⟩ := p
  rw [hr1] at hout2
  obtain ⟨ht1, hel1⟩ := (hout2 : OptEWAt st2.data.dmem (off fb 8) (some x0))
  rw [ewAt_iff, off_off, off_off] at hel1
  have hts1 : TStateAt st2.data.dmem t a s1 := hnext2 x0 s1 hr1
  rw [load_ofMachine (o := 8) rfl ht1] at hpc3
  simp (config := { decide := true }) only [↓reduceIte] at hpc3
  -- `b2`: the first element kept, `bl read_scalar`.
  have hm3' : Match (frameEnv m0 st3.data 80 []) callS st3.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf3.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 (hfr hf3)
    (hpc3.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateReadCommitment.b1_next])) hm3' fun st4 hm4 hpc4 => ?_
  obtain ⟨hmid4, hmem4, hx0₄, hx1₄, hx23₄, hx22₄, hcs4⟩ := after_eq run_b2 ▸ ok_b2
  have hf4 : Frame m0 80 slots st4.data := Frame.of_block hf3 (hfr hf3) hm4 hmid4 slots_le
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq (hfr hf3) hmem4
  have hk4 : ∀ r, calleeSaved r = true → r ≠ .X23 → r ≠ .X22 →
      st4.data.regs.getXReg r = st3.data.regs.getXReg r :=
    fun r hr h1 h2 ↦ Match.reg_eq hm3' hm4 (by cases r <;> rfl) (hcs4 r hr h1 h2)
  have hX23₄ : st4.data.regs.X23 = x0.c0 := UInt64.toBitVec_inj.mp ((hm4.regs .X23 _ hx23₄).trans
    (load_ofMachine (o := 16) rfl (by rw [hd3]; exact hel1.1)))
  have hX22₄ : st4.data.regs.X22 = x0.c1 := UInt64.toBitVec_inj.mp ((hm4.regs .X22 _ hx22₄).trans
    (load_ofMachine (o := 24) rfl (by rw [hd3]; exact hel1.2)))
  have h19₄ : st4.data.regs.X19 = m0.regs.X0 :=
    ((hk4 .X19 rfl (by decide) (by decide)).trans (hk3 .X19 rfl)).trans h19₂
  have h20₄ : st4.data.regs.X20 = m0.regs.X2 :=
    ((hk4 .X20 rfl (by decide) (by decide)).trans (hk3 .X20 rfl)).trans h20₂
  have h21₄ : st4.data.regs.X21 = m0.regs.X1 :=
    ((hk4 .X21 rfl (by decide) (by decide)).trans (hk3 .X21 rfl)).trans h21₂
  have hts4 : TStateAt st4.data.dmem t a s1 := by rw [hd4, hd3]; exact hts1
  have hso4 : SameOutside m0.dmem st4.data.dmem (Out m0) := by rw [hd4]; exact hso3
  refine call_read hrs hst hrc htok hpc4 hf4 (by
      show (st4.data.regs.getXReg .X0).toBitVec = _; rw [hm4.regs .X0 _ hx0₄]; rfl)
    (by
      show (st4.data.regs.getXReg .X1).toBitVec = _; rw [hm4.regs .X1 _ hx1₄]
      show st3.data.regs.X19.toBitVec = _
      rw [show st3.data.regs.X19 = st2.data.regs.X19 from hk3 .X19 rfl, h19₂])
    hts4 hso4 fun st5 hpc5 hf5 hout5 hnext5 hso5 hsv5 => ?_
  have h19₅ : st5.data.regs.X19 = m0.regs.X0 := (hsv5.1 .X19 rfl).trans h19₄
  have h20₅ : st5.data.regs.X20 = m0.regs.X2 := (hsv5.1 .X20 rfl).trans h20₄
  have h21₅ : st5.data.regs.X21 = m0.regs.X1 := (hsv5.1 .X21 rfl).trans h21₄
  have h22₅ : st5.data.regs.X22 = x0.c1 := (hsv5.1 .X22 rfl).trans hX22₄
  have h23₅ : st5.data.regs.X23 = x0.c0 := (hsv5.1 .X23 rfl).trans hX23₄
  -- `b3`: the second tag.
  have hm5 : Match (frameEnv m0 st5.data 80 []) tagS st5.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
      (by rw [hf5.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 (hfr hf5)
    (hpc5.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateReadCommitment.b2_next])) hm5 fun st6 hm6 hpc6 => ?_
  obtain ⟨hmid6, hmem6, hcs6⟩ := after_eq run_b3 ▸ ok_b3
  have hf6 : Frame m0 80 slots st6.data := Frame.of_block hf5 (hfr hf5) hm6 hmid6 slots_le
  have hd6 : st6.data.dmem = st5.data.dmem := hm6.dmem_eq (hfr hf5) hmem6
  have hk6 : ∀ r, calleeSaved r = true → st6.data.regs.getXReg r = st5.data.regs.getXReg r :=
    fun r hr ↦ Match.reg_eq hm5 hm6 (by cases r <;> rfl) (hcs6 r hr)
  have hso6 : SameOutside m0.dmem st6.data.dmem (Out m0) := by rw [hd6]; exact hso5
  simp only [PcOk] at hpc6
  sym_simp at hpc6
  cases hr2 : readScalar.run s1 with
  | none =>
    rw [hr2] at hout5
    have h0 : NativeRustcVm.WordAt st5.data.dmem (off fb 8) 0 := hout5
    rw [load4_of_tag (Or.inl rfl) h0] at hpc6
    simp (config := { decide := true }) only [↓reduceIte] at hpc6
    have hnone : (readCommitment m0.regs.X1.toNat m0.regs.X2.toNat).run s = none := by
      rw [run_eq, hr1]; show (readScalar.run s1).bind _ = none; rw [hr2]; rfl
    refine Eventually.mono (finish_fail hp hst (hpc6.trans (hp.label (j := NativeRustcVmArm.Vm.TStateReadCommitment.b6Offset) NativeRustcVmArm.Vm.TStateReadCommitment.label_4_at)) hf6)
      fun st' ⟨hpc', hx0', hd', hsv'⟩ ↦ ⟨hpc', ?_, ?_, ?_, hsv'⟩
    · rw [hnone, hx0']; rfl
    · intro u s' h; rw [hnone] at h; cases h
    · intro q hq; rw [hd']; exact hso6 q hq
  | some p =>
  obtain ⟨x1, s2⟩ := p
  rw [hr2] at hout5
  obtain ⟨ht2, hel2⟩ := (hout5 : OptEWAt st5.data.dmem (off fb 8) (some x1))
  rw [ewAt_iff, off_off, off_off] at hel2
  have hts2 : TStateAt st5.data.dmem t a s2 := hnext5 x1 s2 hr2
  rw [load4_of_tag (Or.inr rfl) ht2] at hpc6
  simp (config := { decide := true }) only [↓reduceIte] at hpc6
  have hroots2 : s2.roots = s.roots := (readScalar_roots hr2).trans (readScalar_roots hr1)
  set nr := s2.roots.size with hnr
  have hnr8 : nr < 8 := by rw [hnr, hroots2]; exact hroots
  -- `b4`: the count against `8`.
  have h19₆ : st6.data.regs.X19 = m0.regs.X0 := (hk6 .X19 rfl).trans h19₅
  have hts6 : TStateAt st6.data.dmem t a s2 := by rw [hd6]; exact hts2
  have hwf6 : (frameEnv m0 st6.data 80 [(t, 760)]).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 80) hst (by decide)) hf6.kept, hfnw⟩,
      ⟨Mapped.keeps hTm hf6.kept, hTn⟩, trivial⟩ (List.pairwise_pair.mpr (Apart.symm' hTF))
  have hm6' : Match (frameEnv m0 st6.data 80 [(t, 760)]) countS st6.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, trivial⟩
      (by rw [hf6.sp]; exact (eval_ptr rfl).symm)
      ⟨known_ptr rfl (by show st6.data.regs.X19.toBitVec = _; rw [h19₆]), trivial⟩ trivial trivial
      trivial
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf6
    (hpc6.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateReadCommitment.b3_next])) hm6' fun st7 hm7 hpc7 => ?_
  obtain ⟨hmid7, hmem7, hx8₇, hx19₇, hcs7⟩ := after_eq run_b4 ▸ ok_b4
  have hf7 : Frame m0 80 slots st7.data := Frame.of_block hf6 hwf6 hm7 hmid7 slots_le
  have hd7 : st7.data.dmem = st6.data.dmem := hm7.dmem_eq hwf6 hmem7
  have hk7 : ∀ r, calleeSaved r = true → r ≠ .X19 →
      st7.data.regs.getXReg r = st6.data.regs.getXReg r := fun r hr h19 ↦ by
    rcases hcs7 r hr with h | h
    · exact Match.reg_eq hm6' hm7 (by cases r <;> first | rfl | exact absurd rfl h19) h
    · exact absurd h h19
  have hcnt : (frameEnv m0 st6.data 80 [(t, 760)]).load 1 752 8 = nr.toUInt64.toBitVec :=
    load_ofMachine (o := 752) rfl hts6.n_roots
  have hnr64 : nr.toUInt64.toBitVec.toNat = nr := by
    simp only [Nat.toUInt64_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  simp only [PcOk] at hpc7
  sym_simp at hpc7
  rw [hcnt] at hpc7
  have hc7 : (!nr.toUInt64.toBitVec.ult (BitVec.ofNat 64 8)) = false := by
    simp only [BitVec.ult, hnr64, BitVec.toNat_ofNat]
    simp [show nr < 8 from hnr8]
  rw [hc7] at hpc7
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc7
  -- `b5`: the root stored, the count advanced.
  have hX8₇ : (st7.data.regs.getXReg .X8).toBitVec.toNat = nr := by
    rw [hm7.regs .X8 _ hx8₇, Sym.eval, hcnt, hnr64]
  have hX19₇ : (st7.data.regs.getXReg .X19).toBitVec = t := by
    rw [hm7.regs .X19 _ hx19₇]; exact eval_ptr rfl
  set rb := off t (368 + 48 * nr) with hrbdef
  set cw := off t 752 with hcwdef
  have hrb : rb.toNat = t.toNat + (368 + 48 * nr) := toNat_off (by omega)
  have hcw : cw.toNat = t.toNat + 752 := toNat_off (by omega)
  have hTF' : t.toNat + 760 ≤ fb.toNat ∨ fb.toNat + 80 ≤ t.toNat := hTF
  have hwf7 : (frameEnv m0 st7.data 80 [(rb, 48), (cw, 8)]).WF := by
    refine Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 80) hst (by decide)) hf7.kept, hfnw⟩,
      ⟨Mapped.keeps (mapped_off hTm (by show 368 + 48 * nr + 48 ≤ 760; omega)) hf7.kept,
        by show rb.toNat + 48 ≤ 2 ^ 64; omega⟩,
      ⟨Mapped.keeps (mapped_off hTm (by show 752 + 8 ≤ 760; omega)) hf7.kept,
        by show cw.toNat + 8 ≤ 2 ^ 64; omega⟩, trivial⟩ (pairwise3 ?_ ?_ ?_)
    · show fb.toNat + 80 ≤ rb.toNat ∨ rb.toNat + 48 ≤ fb.toNat; omega
    · show fb.toNat + 80 ≤ cw.toNat ∨ cw.toNat + 8 ≤ fb.toNat; omega
    · show rb.toNat + 48 ≤ cw.toNat ∨ cw.toNat + 8 ≤ rb.toNat; omega
  have hm7' : Match (frameEnv m0 st7.data 80 [(rb, 48), (cw, 8)]) pushS st7.data := by
    refine match_ofMachine
      ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, rfl, nofun, trivial⟩
      (by rw [hf7.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial ⟨?_, ?_, trivial⟩
    · show Sym.eval _ rootSym = rb + BitVec.ofInt 64 (-368)
      simp only [rootSym]
      sym_simp
      rw [Env.ofMachine_regs, Env.ofMachine_regs, hX19₇]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_mul, hX8₇, BitVec.toNat_add, hrb, ofInt_neg368,
        BitVec.toNat_ofNat]
      simp only [MemWidth.bits]
      omega
    · show (st7.data.regs.getXReg .X19).toBitVec = cw + BitVec.ofInt 64 (-752)
      rw [hX19₇]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, hcw, ofInt_neg752]
      omega
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf7
    (hpc7.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateReadCommitment.b4_next])) hm7' fun st8 hm8 hpc8 => ?_
  obtain ⟨hepi, hx0₈, hw0, hw1, hw2, hw3, hw4, hw5, hwc, hws8⟩ := after_eq run_b5 ▸ ok_b5
  obtain ⟨hsv8, hsl8⟩ := Frame.epilogue hf7 hwf7 hm8 hepi
  have hx30 : st8.data.regs.X30 = m0.regs.X30 := hsl8 (32, .X30) (List.mem_cons_self ..)
  set env7 := frameEnv m0 st7.data 80 [(rb, 48), (cw, 8)] with henv7
  have hreg : ∀ r, calleeSaved r = true → r ≠ .X19 →
      (Sym.reg r).eval env7 = (st5.data.regs.getXReg r).toBitVec := fun r hr h19 ↦ by
    show (st7.data.regs.getXReg r).toBitVec = _
    rw [hk7 r hr h19, hk6 r hr]
  have hd76 : st7.data.dmem = st5.data.dmem := hd7.trans hd6
  have hv0 := wordAt_write hm8 (r := 1) (o := 0) (b := rb) (sz := 48) rfl (by decide) hw0
  rw [hreg .X23 rfl (by decide), off_zero] at hv0
  have hv1 := wordAt_write hm8 (r := 1) (o := 8) (b := rb) (sz := 48) rfl (by decide) hw1
  rw [hreg .X22 rfl (by decide)] at hv1
  have hv2 := wordAt_write hm8 (r := 1) (o := 16) (b := rb) (sz := 48) rfl (by decide) hw2
  rw [show (Sym.load 0 16 8).eval env7 = _ from
    load_ofMachine (o := 16) rfl (hd76 ▸ hel2.1)] at hv2
  have hv3 := wordAt_write hm8 (r := 1) (o := 24) (b := rb) (sz := 48) rfl (by decide) hw3
  rw [show (Sym.load 0 24 8).eval env7 = _ from
    load_ofMachine (o := 24) rfl (hd76 ▸ hel2.2)] at hv3
  have hv4 := wordAt_write hm8 (r := 1) (o := 32) (b := rb) (sz := 48) rfl (by decide) hw4
  rw [hreg .X21 rfl (by decide)] at hv4
  have hv5 := wordAt_write hm8 (r := 1) (o := 40) (b := rb) (sz := 48) rfl (by decide) hw5
  rw [hreg .X20 rfl (by decide)] at hv5
  have hvc := wordAt_write hm8 (r := 2) (o := 0) (b := cw) (sz := 8) rfl (by decide) hwc
  rw [off_zero] at hvc
  rw [show (Sym.bin .add .W64 (.load 2 0 8) (.lit 1)).eval env7 =
      nr.toUInt64.toBitVec + BitVec.ofNat 64 1 from by
    sym_simp
    rw [load_ofMachine (o := 0) rfl (by rw [off_zero, hd7]; exact hts6.n_roots)],
    toUInt64_succ (by omega)] at hvc
  rw [show st5.data.regs.getXReg .X23 = x0.c0 from h23₅] at hv0
  rw [show st5.data.regs.getXReg .X22 = x0.c1 from h22₅] at hv1
  rw [show st5.data.regs.getXReg .X21 = m0.regs.X1 from h21₅] at hv4
  rw [show st5.data.regs.getXReg .X20 = m0.regs.X2 from h20₅] at hv5
  have hroot : RootAt st8.data.dmem rb
      ⟨#v[x0.c0, x0.c1, x1.c0, x1.c1], m0.regs.X1.toNat, m0.regs.X2.toNat⟩ := by
    refine ⟨m0.regs.X1.toNat_lt, m0.regs.X2.toNat_lt, ?_, ?_, ?_⟩
    · show NativeRustcVm.WordsAt _ rb [x0.c0, x0.c1, x1.c0, x1.c1]
      refine wordsAt_cons.mpr ⟨hv0, wordsAt_cons.mpr ⟨hv1, ?_⟩⟩
      rw [off_off]
      refine wordsAt_cons.mpr ⟨hv2, wordsAt_cons.mpr ⟨?_, wordsAt_nil _ _⟩⟩
      rw [off_off]; exact hv3
    · show NativeRustcVm.WordAt _ (off rb 32) m0.regs.X1.toNat.toUInt64
      rw [toUInt64_toNat]; exact hv4
    · show NativeRustcVm.WordAt _ (off rb 40) m0.regs.X2.toNat.toUInt64
      rw [toUInt64_toNat]; exact hv5
  have hs8 : SameOutside st7.data.dmem st8.data.dmem (fun q ↦ Touch t tstateBytes (fun j ↦
      (368 + 48 * s2.roots.size ≤ j ∧ j < 416 + 48 * s2.roots.size) ∨ 752 ≤ j) q ∨ False) := by
    intro q hq
    refine hm8.get?_mem0 hwf7 fun hW ↦ hq (Or.inl ?_)
    rcases touch_of_written2 hwf7 (r := 1) (r' := 2) rfl rfl (by decide) hws8 hW with h | h
    · exact touch_sub hTn (by omega) (inRange_of_touch (by show rb.toNat + 48 ≤ 2 ^ 64; omega) h)
        fun j h1 h2 ↦ Or.inl ⟨by omega, by omega⟩
    · exact touch_sub hTn (by omega) h fun j h1 _ ↦ Or.inr h1
  have hts8 := (hd7 ▸ hts6 : TStateAt st7.data.dmem t a s2).with_root (hm8.kept hwf7)
    (fun _ h ↦ h.elim) hs8 (by rw [hroots2]; exact hroots) hroot hvc
  have hrun : (readCommitment m0.regs.X1.toNat m0.regs.X2.toNat).run s = some ((),
      { s2 with roots := (s2.roots.push
        ⟨#v[x0.c0, x0.c1, x1.c0, x1.c1], m0.regs.X1.toNat, m0.regs.X2.toNat⟩) }) := by
    rw [run_eq, hr1]; show (readScalar.run s1).bind _ = _; rw [hr2]; rfl
  refine .done _ ⟨by simp only [PcOk] at hpc8; rw [hpc8]; simp only [retOf, hx30], ?_, ?_, ?_,
    hsv8⟩
  · rw [hrun]
    exact UInt64.toBitVec_inj.mp (hm8.regs .X0 _ hx0₈)
  · intro u s' h
    rw [hrun] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact hts8
  · intro q hq
    rw [hs8 q (by
      rintro (⟨j, hj, -, rfl⟩ | h)
      · exact hq (Or.inl (inRange_off_self hj (by simp only [tstateBytes]; omega)))
      · exact h), hd7]
    exact hso6 q hq

end

end NativeRustcVmArm.Transcript.ReadCommitment
