module

public import NativeRustcVmArm.Code.Vm.DecodedStreamElement.Names
public import NativeRustcVmArm.Code.Vm.TStateNextScalar.Names
public import NativeRustcVmArm.Spec.Transcript
public import NativeRustcVmArm.Transcript.NextScalar.Exec
public import NativeVm.Equiv.Transcript

/-!
# `TState::next_scalar` on AArch64

**`nextScalar_spec`**: the `Option<EW>` at X0 becomes `nextScalar`'s element and the `TState` at X1
its state, given `stream_element`'s contract. `b0` saves X30, X21, X20, X19 and tests the ground
challenge's tag: one waiting, `b1`, `b2` store the tag `0`. Otherwise `b3` calls `stream_element`
on the area, its length and the cursor, its output in the frame; `b4` tests its tag: `0`, `b2`
stores it; `1`, `b5` advances the cursor and copies the element to the output.
-/

namespace NativeRustcVmArm.Transcript.NextScalar

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateNextScalar
open NativeRustcVm.Transcript NativeVm.Model NativeRustcArm

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 64 := by decide

theorem run_ground {s : TState} {c : EW} (h : s.sponge.ground = some c) :
    nextScalar.run s = none := by
  rw [NativeVm.Equiv.nextScalar_run, h]; rfl

theorem run_some {s : TState} (h : s.sponge.ground = none) {x : EW}
    (hx : s.stream[s.cursor]? = some x) :
    nextScalar.run s = some (x, { s with cursor := s.cursor + 1 }) := by
  rw [NativeVm.Equiv.nextScalar_run, h, hx]; rfl

theorem run_none {s : TState} (h : s.sponge.ground = none) (hx : s.stream[s.cursor]? = none) :
    nextScalar.run s = none := by
  rw [NativeVm.Equiv.nextScalar_run, h, hx]; rfl

theorem toNat_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

theorem toUInt64_succ {n : Nat} (h : n + 1 < 2 ^ 64) :
    UInt64.ofBitVec (n.toUInt64.toBitVec + BitVec.ofNat 64 1) = (n + 1).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [toNat_toUInt64 h]
  show (n.toUInt64.toBitVec + BitVec.ofNat 64 1).toNat = _
  rw [BitVec.toNat_add, UInt64.toNat_toBitVec, toNat_toUInt64 (by omega), BitVec.toNat_ofNat]
  omega

variable [Host] {k : Nat}

/-- `b2`: the tag X8 (`0`) stored at the output, the epilogue. -/
theorem finish_none (hp : Placed code k) {m0 : MachineData} (hst : StackOk m0 nextScalarStack)
    (hom : Mapped m0.dmem m0.regs.X0.toBitVec 24)
    (hon : NativeRustcVm.NoWrap m0.regs.X0.toBitVec 24)
    (hoF : NativeRustcVm.Apart m0.regs.X0.toBitVec 24 (frameBase m0 64) 64)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateNextScalar.b2Offset)) (hf : Frame m0 64 slots st.data)
    (hx8 : st.data.regs.X8 = 0) (hx19 : st.data.regs.X19 = m0.regs.X0) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      OptEWAt st'.data.dmem m0.regs.X0.toBitVec none ∧
      SameOutside st.data.dmem st'.data.dmem (NativeRustcVm.InRange m0.regs.X0.toBitVec 24) ∧
      Saved m0 st'.data) st := by
  set o := m0.regs.X0.toBitVec
  have hfnw := frame_noWrap (m := m0) (F := 64) hst.2.1
  have hwf : (frameEnv m0 st.data 64 [(o, 24)]).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 64) hst le_rfl) hf.kept, hfnw⟩,
      ⟨Mapped.keeps hom hf.kept, hon⟩, trivial⟩ (List.pairwise_pair.mpr (Apart.symm' hoF))
  have hm : Match (frameEnv m0 st.data 64 [(o, 24)]) storeS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst le_rfl (by decide), rfl, nofun, trivial⟩
      (by rw [hf.sp]; exact (eval_ptr rfl).symm)
      ⟨known_ptr rfl (by show st.data.regs.X19.toBitVec = _; rw [hx19]), trivial⟩ trivial trivial
      trivial
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf hpc hm fun st' hm' hpc' => ?_
  obtain ⟨hepi, hw, hws⟩ := after_eq run_b2 ▸ ok_b2
  obtain ⟨hsv, hsl⟩ := Frame.epilogue hf hwf hm' hepi
  have hx30 : st'.data.regs.X30 = m0.regs.X30 := hsl (32, .X30) (List.mem_cons_self ..)
  have ht := wordAt_write hm' (r := 1) (o := 0) (b := o) (sz := 24) rfl (by decide) hw
  rw [off_zero, show UInt64.ofBitVec ((Sym.reg .X8).eval (frameEnv m0 st.data 64 [(o, 24)])) = 0
    from by show UInt64.ofBitVec st.data.regs.X8.toBitVec = 0; rw [hx8]] at ht
  exact .done _ ⟨by simp only [PcOk] at hpc'; rw [hpc']; simp only [retOf, hx30], ht,
    sameOutside_region hwf hm' (r := 1) rfl hws, hsv⟩

/-- **`TState::next_scalar` meets its contract.** -/
theorem nextScalar_spec (hp : Placed code k)
    (hse : ∀ a stream openings, Spec (Labels.label NativeRustcVmArm.Vm.DecodedStreamElement.entryLabel)
      (StreamElementPre a stream openings) (StreamElementPost stream))
    (a : DecArea) (s : TState) :
    Spec (Labels.label NativeRustcVmArm.Vm.TStateNextScalar.entryLabel) (NextScalarPre a s) (NextScalarPost a s) := by
  rintro m0 ⟨hst, hts, ⟨hapT, hapA, -⟩, ⟨hom, hon, hoT, hoA, hoS, -⟩⟩
  set t := m0.regs.X1.toBitVec with htdef
  set o := m0.regs.X0.toBitVec with hodef
  set fb := frameBase m0 64 with hfb
  have hn : nextScalarStack ≤ m0.regs.SP.toNat := hst.2.1
  have hfnw : fb.toNat + 64 ≤ 2 ^ 64 := frame_noWrap (m := m0) (F := 64) hn
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, -⟩ := hts.footprint
  have hTn' : t.toNat + 760 ≤ 2 ^ 64 := hTn
  have hAn' : a.words.toNat + 8 * a.len ≤ 2 ^ 64 := hAn
  have hon' : o.toNat + 24 ≤ 2 ^ 64 := hon
  have hTF : NativeRustcVm.Apart t 760 fb 64 := apart_frame hapT hn le_rfl
  have hAF : NativeRustcVm.Apart a.words (8 * a.len) fb 64 := apart_frame hapA hn le_rfl
  have hoF : NativeRustcVm.Apart o 24 fb 64 := apart_frame hoS hn le_rfl
  have hRF : ∀ q, NativeRustcVm.InRange fb 64 q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q :=
    fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart hTF hTn hfnw h hq,
      fun h ↦ not_inRange_of_apart hAF hAn hfnw h hq⟩
  -- `b0`: the prologue, the ground tag.
  have hwf0 : (frameEnv m0 m0 64 [(t, 760)]).WF :=
    Env.wf_of ⟨⟨frame_mapped (F := 64) hst le_rfl, hfnw⟩, ⟨hTm, hTn⟩, trivial⟩
      (List.pairwise_pair.mpr (Apart.symm' hTF))
  have hm0 : Match (frameEnv m0 m0 64 [(t, 760)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst le_rfl (by decide), rfl, nofun, trivial⟩
      frameBase_add.symm ⟨known_ptr rfl rfl, trivial⟩ trivial trivial trivial
  unfold NativeRustcVmArm.Vm.TStateNextScalar.entryLabel
  rw [hp.label (j := NativeRustcVmArm.Vm.TStateNextScalar.entryOffset) NativeRustcVmArm.Vm.TStateNextScalar.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf0 hm0 fun st1 hm1 hpc1 => ?_
  obtain ⟨hpro, hws1, hx19, hx1⟩ := after_eq run_b0 ▸ ok_b0
  have hf1 : Frame m0 64 slots st1.data := Frame.of_prologue hwf0 hm1 hpro slots_le
  have hs1 : SameOutside m0.dmem st1.data.dmem (NativeRustcVm.InRange fb 64) :=
    sameOutside_region hwf0 hm1 rfl hws1
  have hX19 : st1.data.regs.X19 = m0.regs.X0 := UInt64.toBitVec_inj.mp (hm1.regs .X19 _ hx19)
  have hX1 : st1.data.regs.X1.toBitVec = t := by
    show (st1.data.regs.getXReg .X1).toBitVec = _
    rw [hm1.regs .X1 _ hx1]; exact eval_ptr rfl
  have hwf1 : (frameEnv m0 st1.data 64 [(t, 760)]).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 64) hst le_rfl) hf1.kept, hfnw⟩,
      ⟨Mapped.keeps hTm hf1.kept, hTn⟩, trivial⟩ (List.pairwise_pair.mpr (Apart.symm' hTF))
  have hgr := hts.sponge.ground
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  cases hg : s.sponge.ground with
  | some c =>
    -- A ground challenge waits: `None`.
    rw [hg] at hgr
    have htag : (frameEnv m0 m0 64 [(t, 760)]).load 1 304 8 = (1 : UInt64).toBitVec :=
      load_ofMachine (o := 304) rfl hgr.1
    rw [htag] at hpc1
    simp (config := { decide := true }) only [↓reduceIte] at hpc1
    have hwf1' : (frameEnv m0 st1.data 64 []).WF :=
      Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 64) hst le_rfl) hf1.kept, hfnw⟩, trivial⟩
        (List.pairwise_singleton _ _)
    have hm1' : Match (frameEnv m0 st1.data 64 []) zeroS st1.data :=
      match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst le_rfl (by decide), trivial⟩
        (by rw [hf1.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf1'
      (hpc1.trans (by change Host.addrOf (k + NativeRustcVmArm.Vm.TStateNextScalar.b0Offset + NativeRustcVmArm.Vm.TStateNextScalar.b0.length) = Host.addrOf (k + NativeRustcVmArm.Vm.TStateNextScalar.b1Offset); rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateNextScalar.b0_next])) hm1' fun st2 hm2 hpc2 => ?_
    obtain ⟨hmid2, hmem2, hx8, hx19'⟩ := after_eq run_b1 ▸ ok_b1
    have hf2 : Frame m0 64 slots st2.data := Frame.of_block hf1 hwf1' hm2 hmid2 slots_le
    have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq hwf1' hmem2
    have hX8 : st2.data.regs.X8 = 0 := UInt64.toBitVec_inj.mp (hm2.regs .X8 _ hx8)
    have hX19' : st2.data.regs.X19 = m0.regs.X0 :=
      (Match.reg_eq (r := .X19) hm1' hm2 rfl hx19').trans hX19
    have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateNextScalar.b2Offset) := by
      simp only [PcOk] at hpc2; rw [hpc2, Nat.add_assoc, NativeRustcVmArm.Vm.TStateNextScalar.b1_next]
    refine Eventually.mono (finish_none hp hst hom hon hoF hpc2' hf2 hX8 hX19')
      fun st' ⟨hpc', hout, hso, hsv⟩ ↦ ⟨hpc', ?_, ?_, ?_, hsv⟩
    · rw [run_ground hg]; exact hout
    · rw [run_ground hg]; intro x s' h; cases h
    · intro q hq
      rw [hso q fun h ↦ hq (Or.inl h), hd2]
      exact hs1 q fun h ↦ hq (Or.inr (Or.inr (inRange_frame_stack hn le_rfl h)))
  | none =>
  rw [hg] at hgr
  have htag : (frameEnv m0 m0 64 [(t, 760)]).load 1 304 8 = (0 : UInt64).toBitVec :=
    load_ofMachine (o := 304) rfl hgr
  rw [htag] at hpc1
  simp (config := { decide := true }) only [↓reduceIte] at hpc1
  -- `b3`: `bl stream_element`.
  have hts1 : TStateAt st1.data.dmem t a s := hts.frame hf1.kept hRF hs1
  have hm1' : Match (frameEnv m0 st1.data 64 [(t, 760)]) callS st1.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst le_rfl (by decide), rfl, nofun, trivial⟩
      (by rw [hf1.sp]; exact (eval_ptr rfl).symm) ⟨known_ptr rfl hX1, trivial⟩ trivial trivial
      trivial
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 hwf1
    (hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.TStateNextScalar.b3Offset) NativeRustcVmArm.Vm.TStateNextScalar.label_3_at)) hm1' fun st2 hm2 hpc2 => ?_
  obtain ⟨hmid2, hmem2, hx0, hx1', hx2, hx3, hx19', hx20, hx21⟩ := after_eq run_b3 ▸ ok_b3
  have hf2 : Frame m0 64 slots st2.data := Frame.of_block hf1 hwf1 hm2 hmid2 slots_le
  have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq hwf1 hmem2
  have hlen64 : a.len < 2 ^ 64 := by
    have := hts.decoded.len
    have := streamEnd_lt a.l
    omega
  have hcur64 : s.cursor < 2 ^ 64 := by
    have := hts.cursor_le
    have := hts.decoded.stream_le
    simp only [NativeVm.maxStream] at this
    have := hts.decoded.l_lt
    omega
  have hX0 : st2.data.regs.X0.toBitVec = off fb 8 := by
    show (st2.data.regs.getXReg .X0).toBitVec = _
    rw [hm2.regs .X0 _ hx0]; rfl
  have hX1' : st2.data.regs.X1.toBitVec = a.words := by
    show (st2.data.regs.getXReg .X1).toBitVec = _
    rw [hm2.regs .X1 _ hx1']
    exact load_ofMachine (o := 328) rfl hts1.dec.1
  have hX2 : st2.data.regs.X2.toNat = a.len := by
    show (st2.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [hm2.regs .X2 _ hx2, Sym.eval, load_ofMachine (o := 336) rfl (by
      have := hts1.dec.2.1; rwa [off_off] at this), UInt64.toNat_toBitVec, toNat_toUInt64 hlen64]
  have hX3 : st2.data.regs.X3.toNat = s.cursor := by
    show (st2.data.regs.getXReg .X3).toBitVec.toNat = _
    rw [hm2.regs .X3 _ hx3, Sym.eval, load_ofMachine (o := 352) rfl hts1.cursor,
      UInt64.toNat_toBitVec, toNat_toUInt64 hcur64]
  have hX20 : st2.data.regs.X20 = s.cursor.toUInt64 :=
    UInt64.toBitVec_inj.mp ((hm2.regs .X20 _ hx20).trans (load_ofMachine (o := 352) rfl hts1.cursor))
  have hX21 : st2.data.regs.X21.toBitVec = t := by
    show (st2.data.regs.getXReg .X21).toBitVec = _
    rw [hm2.regs .X21 _ hx21]; exact eval_ptr rfl
  have hX19' : st2.data.regs.X19 = m0.regs.X0 :=
    (Match.reg_eq (r := .X19) hm1' hm2 rfl hx19').trans hX19
  -- `stream_element`, its output at `fb + 8`.
  have h8n : (off fb 8).toNat = fb.toNat + 8 := toNat_off (by omega)
  have hpre2 : StreamElementPre a s.stream s.openings st2.data := by
    unfold StreamElementPre
    rw [hX0]
    refine ⟨stackOk_callee hst hf2.kept hf2.sp le_rfl (by decide) (by decide), hX1', hX2,
      Region.Ok.keeps ⟨hAm, hAn⟩ hf2.kept, hd2 ▸ hts1.decoded,
      Mapped.keeps (mapped_off (frame_mapped (F := 64) hst le_rfl) (by decide)) hf2.kept, ?_, ?_⟩
    · show (off fb 8).toNat + 24 ≤ 2 ^ 64
      omega
    · have h : a.words.toNat + 8 * a.len ≤ fb.toNat ∨ fb.toNat + 64 ≤ a.words.toNat := hAF
      show (off fb 8).toNat + 24 ≤ a.words.toNat ∨ a.words.toNat + 8 * a.len ≤ (off fb 8).toNat
      omega
  refine call_then hpc2 (hse a s.stream s.openings) hpre2 fun st3 hpc3 ⟨hout3, hs3, hsv3⟩ => ?_
  rw [hX0, hX3] at hout3
  rw [hX0] at hs3
  have hf3 : Frame m0 64 slots st3.data :=
    Frame.call_slots hf2 hsv3 hs3 (not_slot_out hfnw (by decide) slots_le (by decide))
  have hX19'' : st3.data.regs.X19 = m0.regs.X0 := (hsv3.1 .X19 rfl).trans hX19'
  have hX20'' : st3.data.regs.X20 = s.cursor.toUInt64 := (hsv3.1 .X20 rfl).trans hX20
  have hX21'' : st3.data.regs.X21.toBitVec = t := by
    show (st3.data.regs.getXReg .X21).toBitVec = _; rw [hsv3.1 .X21 rfl]; exact hX21
  -- `b4`: the tag.
  have hwf3 : (frameEnv m0 st3.data 64 []).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 64) hst le_rfl) hf3.kept, hfnw⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm3 : Match (frameEnv m0 st3.data 64 []) tagS st3.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst le_rfl (by decide), trivial⟩
      (by rw [hf3.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf3
    (hpc3.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateNextScalar.b3_next])) hm3 fun st4 hm4 hpc4 => ?_
  obtain ⟨hmid4, hmem4, hx8, hx19''', hx20''', hx21'''⟩ := after_eq run_b4 ▸ ok_b4
  have hf4 : Frame m0 64 slots st4.data := Frame.of_block hf3 hwf3 hm4 hmid4 slots_le
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 hmem4
  have hX19₄ : st4.data.regs.X19 = m0.regs.X0 :=
    (Match.reg_eq (r := .X19) hm3 hm4 rfl hx19''').trans hX19''
  -- What changed so far: the frame.
  have hs13 : SameOutside m0.dmem st4.data.dmem (NativeRustcVm.InRange fb 64) := fun q hq ↦ by
    rw [hd4, hs3 q fun h ↦ hq (inRange_of_off hfnw (by decide) h), hd2]
    exact hs1 q hq
  simp only [PcOk] at hpc4
  sym_simp at hpc4
  cases hx : s.stream[s.cursor]? with
  | none =>
    -- `stream_element` returned `None`: its tag `0` stored.
    rw [hx] at hout3
    have ht0 : (frameEnv m0 st3.data 64 []).load 0 8 8 = (0 : UInt64).toBitVec :=
      load_ofMachine (o := 8) rfl hout3
    rw [ht0] at hpc4
    simp (config := { decide := true }) only [↓reduceIte] at hpc4
    have hX8 : st4.data.regs.X8 = 0 := UInt64.toBitVec_inj.mp ((hm4.regs .X8 _ hx8).trans ht0)
    refine Eventually.mono (finish_none hp hst hom hon hoF (hpc4.trans (hp.label (j := NativeRustcVmArm.Vm.TStateNextScalar.b2Offset) NativeRustcVmArm.Vm.TStateNextScalar.label_2_at))
      hf4 hX8 hX19₄) fun st' ⟨hpc', hout, hso, hsv⟩ ↦ ⟨hpc', ?_, ?_, ?_, hsv⟩
    · rw [run_none hg hx]; exact hout
    · rw [run_none hg hx]; intro x s' h; cases h
    · intro q hq
      rw [hso q fun h ↦ hq (Or.inl h)]
      exact hs13 q fun h ↦ hq (Or.inr (Or.inr (inRange_frame_stack hn le_rfl h)))
  | some x =>
  -- `b5`: the cursor advanced, the element copied.
  rw [hx] at hout3
  obtain ⟨ht1, hel⟩ := hout3
  have ht1' : (frameEnv m0 st3.data 64 []).load 0 8 8 = (1 : UInt64).toBitVec :=
    load_ofMachine (o := 8) rfl ht1
  rw [ht1'] at hpc4
  simp (config := { decide := true }) only [↓reduceIte] at hpc4
  obtain ⟨hlt, hxv⟩ := Array.getElem?_eq_some_iff.mp hx
  rw [ewAt_iff, off_off, off_off] at hel
  have hX21₄ : st4.data.regs.X21.toBitVec = t := by
    show (st4.data.regs.getXReg .X21).toBitVec = _
    rw [hm4.regs .X21 _ hx21''']; exact hX21''
  have hX20₄ : st4.data.regs.X20 = s.cursor.toUInt64 :=
    (Match.reg_eq (r := .X20) hm3 hm4 rfl hx20''').trans hX20''
  have hwf4 : (frameEnv m0 st4.data 64 [(t, 760), (o, 24)]).WF :=
    Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 64) hst le_rfl) hf4.kept, hfnw⟩,
      ⟨Mapped.keeps hTm hf4.kept, hTn⟩, ⟨Mapped.keeps hom hf4.kept, hon⟩, trivial⟩
      (pairwise3 (Apart.symm' hTF) (Apart.symm' hoF) (Apart.symm' hoT))
  have hm4' : Match (frameEnv m0 st4.data 64 [(t, 760), (o, 24)]) someS st4.data :=
    match_ofMachine
      ⟨rfl, fun _ ↦ frame_aligned hst le_rfl (by decide), rfl, nofun, rfl, nofun, trivial⟩
      (by rw [hf4.sp]; exact (eval_ptr rfl).symm)
      ⟨known_ptr rfl hX21₄, known_ptr rfl (by show st4.data.regs.X19.toBitVec = _; rw [hX19₄]),
        trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf4
    (hpc4.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.TStateNextScalar.b4_next])) hm4' fun st5 hm5 hpc5 => ?_
  obtain ⟨hepi, hwc, hwt, hw0, hw1, hws5⟩ := after_eq run_b5 ▸ ok_b5
  obtain ⟨hsv5, hsl5⟩ := Frame.epilogue hf4 hwf4 hm5 hepi
  have hx30 : st5.data.regs.X30 = m0.regs.X30 := hsl5 (32, .X30) (List.mem_cons_self ..)
  have hs5 : SameOutside st4.data.dmem st5.data.dmem (fun q ↦
      Touch t 760 (fun j ↦ 352 ≤ j ∧ j < 360) q ∨ NativeRustcVm.InRange o 24 q) :=
    fun q hq ↦ hm5.get?_mem0 hwf4 fun hW ↦ hq (touch_of_written2 hwf4 (r := 1) (r' := 2) rfl rfl
      (by decide) hws5 hW)
  have hsz64 : s.stream.size < 2 ^ 64 := by
    have := hts.decoded.stream_le
    simp only [NativeVm.maxStream] at this
    have := hts.decoded.l_lt
    omega
  have hv : (Sym.bin .add .W64 (.reg .X20) (.lit 1)).eval
      (frameEnv m0 st4.data 64 [(t, 760), (o, 24)]) = (s.cursor + 1).toUInt64.toBitVec := by
    sym_simp
    show st4.data.regs.X20.toBitVec + BitVec.ofNat 64 1 = _
    rw [hX20₄]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, UInt64.toNat_toBitVec s.cursor.toUInt64,
      toNat_toUInt64 hcur64, UInt64.toNat_toBitVec (s.cursor + 1).toUInt64,
      toNat_toUInt64 (by omega)]
    omega
  have hc := wordAt_write hm5 (r := 1) (o := 352) (b := t) (sz := 760) rfl (by decide) hwc
  rw [hv] at hc
  have ht := wordAt_write hm5 (r := 2) (o := 0) (b := o) (sz := 24) rfl (by decide) hwt
  rw [off_zero, show UInt64.ofBitVec ((Sym.lit 1).eval
    (frameEnv m0 st4.data 64 [(t, 760), (o, 24)])) = 1 from rfl] at ht
  have hc0 := wordAt_write hm5 (r := 2) (o := 8) (b := o) (sz := 24) rfl (by decide) hw0
  rw [show (Sym.load 0 16 8).eval (frameEnv m0 st4.data 64 [(t, 760), (o, 24)]) = _ from
    load_ofMachine (o := 16) rfl (hd4 ▸ hel.1)] at hc0
  have hc1 := wordAt_write hm5 (r := 2) (o := 16) (b := o) (sz := 24) rfl (by decide) hw1
  rw [show (Sym.load 0 24 8).eval (frameEnv m0 st4.data 64 [(t, 760), (o, 24)]) = _ from
    load_ofMachine (o := 24) rfl (hd4 ▸ hel.2)] at hc1
  have hR : ∀ q, (NativeRustcVm.InRange o 24 q ∨ NativeRustcVm.InRange fb 64 q) →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q := by
    rintro q (hq | hq)
    · exact ⟨fun h ↦ not_inRange_of_apart hoT hon hTn hq h,
        fun h ↦ not_inRange_of_apart hoA hon hAn hq h⟩
    · exact hRF q hq
  have hsAll : SameOutside m0.dmem st5.data.dmem (fun q ↦
      Touch t tstateBytes (fun j ↦ 352 ≤ j ∧ j < 360) q ∨
        (NativeRustcVm.InRange o 24 q ∨ NativeRustcVm.InRange fb 64 q)) := fun q hq ↦ by
    simp only [not_or] at hq
    rw [hs5 q (by simp only [not_or]; exact ⟨hq.1, hq.2.1⟩)]
    exact hs13 q hq.2.2
  refine .done _ ⟨by simp only [PcOk] at hpc5; rw [hpc5]; simp only [retOf, hx30], ?_, ?_, ?_,
    hsv5⟩
  · rw [run_some hg hx]
    exact ⟨ht, ewAt_iff.mpr ⟨hc0, by rw [off_off]; exact hc1⟩⟩
  · rw [run_some hg hx]
    intro x' s' h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact hts.with_cursor hsv5.2.2 hR hsAll (by omega) hc
  · intro q hq
    simp only [not_or] at hq
    rw [hs5 q (by
      simp only [not_or]
      exact ⟨fun h ↦ hq.2.1 (inRange_of_touch hTn h), hq.1⟩)]
    exact hs13 q fun h ↦ hq.2.2 (inRange_frame_stack hn le_rfl h)

end

end NativeRustcVmArm.Transcript.NextScalar
