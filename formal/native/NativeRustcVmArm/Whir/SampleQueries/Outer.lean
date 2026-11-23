module

public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Whir.SampleQueries.Tail
public import NativeRustcVm.Whir.Per

/-!
# `sample_queries`: the outer loop's turn

From the outer loop's head (`b9`, `Outer`): no position left, the epilogue (`b5`); else the
squeeze (`b10`), `PER_CHALLENGE`'s entry for the depth (`b11`, `per_load`), then `b8` for the depth
`0` (`AtB8`, no position) or the inner loop's head with none pushed (`b12`, `Inner … 0`)
(`outer_step`).
-/

namespace NativeRustcVmArm.Whir.SampleQueries

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.SampleQueries
open NativeRustcVm (BufWordsAt WordsAt WordAt)

public section

/-! ## `PER_CHALLENGE` -/

theorem memExtend0 (x : BitVec 64) :
    (BitVec.ofInt 64 (x.apply_mem_extend ⟨.UXTX, .E0⟩)).toNat = x.toNat := by
  simp [BitVec.apply_mem_extend, BitVec.unsigned]

theorem ofInt_byte (v : Nat) (hv : v < 256) :
    BitVec.ofInt 64 (Int.ofBytes [UInt8.ofNat v]) = BitVec.ofNat 64 v := by
  rw [ofBytes_natCast, BitVec.ofInt_natCast, ofBytes_eq_leNat]
  simp only [NativeRustcVm.leNat, List.foldr_cons, List.foldr_nil, Nat.mul_zero, Nat.add_zero]
  rw [show (UInt8.ofNat v).toNat = v from UInt8.toNat_ofNat_of_lt hv]

/-- **The table's entry for `x`**, loaded as the code does: `128 / x`. -/
theorem per_load [Labels] {m : MachineData} {vs : Nat → BitVec 64}
    (hb : NativeRustcVm.BytesAt m.dmem (rodataAddr .perChallenge)
      NativeRustcVm.Data.Item.perChallenge.bytes) {x : BitVec 64} (hx : x.toNat < 129) :
    (Env.ofMachine m [(rodataAddr .perChallenge, 129)] vs).load 0
      (0 + (BitVec.ofInt 64 (x.apply_mem_extend ⟨.UXTX, .E0⟩)).toNat) 1 =
      BitVec.ofNat 64 (128 / x.toNat) := by
  rw [memExtend0, Nat.zero_add, Env.load_of_bytesAt (env := Env.ofMachine m _ vs) (r := 0)
    (n := 1) (bs := [UInt8.ofNat (128 / x.toNat)]) rfl (by exact perChallenge_byte hb hx),
    ofInt_byte _ (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by decide))]

section
variable [Labels] {a : DecArea} {s0 : TState} {m1 : MachineData}

/-- `PER_CHALLENGE` in a state of the frame. -/
theorem per_at (h : SampleQueriesPre a s0 m1) {st : MachineData} (hf : SFr m1 st) :
    NativeRustcVm.BytesAt st.dmem (rodataAddr .perChallenge)
      NativeRustcVm.Data.Item.perChallenge.bytes := by
  have hr := h.1.2.2.1
  obtain ⟨⟨hmo, hno, hot, hod, hos, hor⟩, hro⟩ := h.2.2.2
  have hfp := h.2.1.footprint
  exact keep_bytes hf (hr.bytesAt _) (hr.noWrap _) (hr.apart _)
    (NativeRustcVm.Apart.symm (hro _)) (NativeRustcVm.Apart.symm (h.1.2.2.2.2 _)) hno hfp.1.2
    (pre_N h)

/-- `PER_CHALLENGE`'s region. -/
abbrev perEnv (st : MachineData) : Env := Env.ofMachine st [(rodataAddr .perChallenge, 129)]

theorem per_wf (h : SampleQueriesPre a s0 m1) {st : MachineData} (hf : SFr m1 st) :
    (perEnv st).WF := by
  have hb := per_at h hf
  have hl := perChallenge_length
  refine Env.wf_of ⟨⟨fun i hi ↦ ?_, ?_⟩, trivial⟩ (List.pairwise_singleton _ _)
  · show (st.dmem.get? (rodataAddr .perChallenge + BitVec.ofNat 64 i)).isSome
    have hi' : i < 129 := hi
    rw [hb i (by omega)]; rfl
  · have := h.1.2.2.1.noWrap .perChallenge
    rwa [hl] at this

end

/-! ## The turn -/

section
variable [Host] {a : DecArea} {s0 : TState} {m1 : MachineData} {k : Nat}

/-- The frame is in the entry's stack. -/
theorem in_stack (h : SampleQueriesPre a s0 m1) {q : BitVec 64}
    (hq : InRange (base m1 112) 112 q) :
    InRange (stackBelow m1 sampleQueriesStack) sampleQueriesStack q := by
  have hN := pre_N h
  have hv := N_val
  have e1 := base_toNat (m0 := m1) (F := 112) (by omega)
  have e2 := base_toNat (m0 := m1) (F := sampleQueriesStack) hN
  exact NativeRustcVm.InRange.mono hq (base_noWrap (by omega)) (base_noWrap hN)
    (by show (base m1 sampleQueriesStack).toNat ≤ _; omega)
    (by show _ ≤ (base m1 sampleQueriesStack).toNat + _; omega)

/-- The frame is apart from the `TState` and its decoded area. -/
theorem frame_not_t (h : SampleQueriesPre a s0 m1) {q : BitVec 64}
    (hq : InRange (base m1 112) 112 q) :
    ¬InRange (tA m1) tstateBytes q ∧ ¬InRange a.words (8 * a.len) q := by
  have hN := pre_N h
  obtain ⟨hto, hda, -⟩ := h.1.2.2.2.1
  have hfp := h.2.1.footprint
  have hnt : NativeRustcVm.NoWrap (tA m1) tstateBytes := hfp.1.2
  have hnd : NativeRustcVm.NoWrap a.words (8 * a.len) := hfp.2.1.2
  exact ⟨fun ht ↦ NativeRustcVm.Apart.not_inRange hto hnt (base_noWrap hN) ht (in_stack h hq),
    fun hd ↦ NativeRustcVm.Apart.not_inRange hda hnd (base_noWrap hN) hd (in_stack h hq)⟩

/-- The frame is apart from the output. -/
theorem frame_not_o (h : SampleQueriesPre a s0 m1) {q : BitVec 64}
    (hq : InRange (base m1 112) 112 q) : ¬InRange (oA m1) queryBufBytes q := by
  have hN := pre_N h
  obtain ⟨⟨hmo, hno, hot, hod, hos, hor⟩, -⟩ := h.2.2.2
  exact fun ho ↦ NativeRustcVm.Apart.not_inRange hos hno (base_noWrap hN) ho (in_stack h hq)

/-- **The outer loop's turn.** -/
theorem outer_step (hp : Placed code k) (h : SampleQueriesPre a s0 m1)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {j r : Nat} {s : TState} {qs : List UInt64} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SampleQueries.b9Offset)) (ho : Outer a s0 m1 j r s qs st.data) :
    Eventually (step1 Host.exe)
      (fun st' ↦ Goal a s0 m1 st' ∨ (st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SampleQueries.b8Offset) ∧
        AtB8 a s0 m1 j r 0 (sq s).2 qs st'.data) ∨
        (st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SampleQueries.b13Offset) ∧ ∃ nn, Inner a s0 m1 j r s qs nn 0 st'.data)) st := by
  have hc := cnt_le h
  have hjc := ho.jlt
  have hN := pre_N h
  refine ho.fr.regsBlock (inf hp b9_in_code (by simp [b9])) run_b9 hpc rfl rfl (by rfl)
    fun st1 hf1 hd1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  have hk1 : ∀ r' : XReg, st1.data.regs.getXReg r' = st.data.regs.getXReg r' := fun r' ↦
    reg_of hm1 (v := .reg r') (by cases r' <;> rfl) rfl
  have hcond : (SBool.cmp CmpOp.eq RegWidth.W64 (Sym.reg XReg.X29) (Sym.lit 0)).eval
      (Env.ofMachine st.data []) = decide (r = 0) := by
    sym_simp
    simp only [Env.ofMachine_regs]
    rw [bv_beq _ (by decide)]
    simp only [← ho.x29]
    rfl
  rw [hcond] at hpc1
  by_cases hr : r = 0
  · -- nothing left: `b5`, the epilogue
    simp only [hr, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.SampleQueries.b5Offset) NativeRustcVmArm.Vm.SampleQueries.label_4_at] at hpc1
    refine hf1.regsBlock (inf hp b5_in_code (by simp [b5])) run_b5 hpc1 rfl rfl (by rfl)
      fun st2 hf2 hd2 hm2 hpc2 ↦ ?_
    simp only [PcOk, hp.label (j := NativeRustcVmArm.Vm.SampleQueries.b18Offset) NativeRustcVmArm.Vm.SampleQueries.label_14_at] at hpc2
    have h0 : st2.data.regs.X0 = 1 := reg_of hm2 (r := .X0) rfl rfl
    refine Eventually.mono (finish hp h hpc2 hf2 h0 (qs := qs) (s := s) ?_
      (by rw [hd2, hd1]; exact ho.buf) (by rw [hd2, hd1]; exact ho.ts)) fun _ hg ↦ Or.inl hg
    rw [ho.model, hr, auxP_zero_right]
    simp
  simp only [hr, decide_false, Bool.false_eq_true, ↓reduceIte,
    show k + NativeRustcVmArm.Vm.SampleQueries.b9Offset + b9.length = k + NativeRustcVmArm.Vm.SampleQueries.b10Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.SampleQueries.b9_next]] at hpc1
  -- the squeeze
  refine hf1.regsBlock (inf hp b10_in_code (by simp [b10])) run_b10 hpc1 rfl rfl (by rfl)
    fun st2 hf2 hd2 hm2 hpc2 ↦ ?_
  simp only [PcOk] at hpc2
  have hk2 : ∀ r' : XReg, r' ≠ .X0 → r' ≠ .X30 →
      st2.data.regs.getXReg r' = st.data.regs.getXReg r' := fun r' h0 h30 ↦
    (reg_of hm2 (v := .reg r') (by cases r' <;> first | rfl | contradiction) rfl).trans (hk1 r')
  have hx0 : st2.data.regs.X0 = m1.regs.X0 :=
    (reg_of hm2 (r := .X0) (v := .reg .X20) rfl rfl).trans ((hk1 .X20).trans ho.x20)
  refine squeeze_call h hsq hf2 hpc2 hx0 (by rw [hd2, hd1]; exact ho.ts)
    fun m3 hf3 hts3 h30 h31 hcs3 hs3 ↦ ?_
  have hk3 : ∀ r' : XReg, calleeSaved r' = true →
      m3.regs.getXReg r' = st.data.regs.getXReg r' := fun r' hr' ↦
    (hcs3 r' hr').trans (hk2 r' (by rintro rfl; simp [calleeSaved] at hr')
      (by rintro rfl; simp [calleeSaved] at hr'))
  have hbuf3 : BufWordsAt m3.dmem (oA m1) queryCap qs :=
    buf_sq h hf2 hs3 (by rw [hd2, hd1]; exact ho.buf)
  -- `PER_CHALLENGE`'s entry
  have hwf3 := per_wf h hf3
  have hm3 : Match (perEnv m3) perS m3 := by
    refine match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl ⟨?_, trivial⟩ trivial
      ⟨?_, trivial⟩ trivial
    · show (m3.regs.getXReg .X27).toBitVec = rodataAddr .perChallenge + BitVec.ofInt 64 0
      rw [hk3 .X27 rfl]
      have : (st.data.regs.getXReg .X27).toBitVec = rodataAddr .perChallenge := ho.x27
      simpa using this
    · show (m3.regs.getXReg .X22).toNat < 129
      rw [hk3 .X22 rfl]
      show st.data.regs.X22.toNat < 129
      rw [ho.x22]
      exact ho.dlt
  refine exec_then (inf hp b11_in_code (by simp [b11])) run_b11 hwf3 hm3 fun st4 hm4 hpc4 ↦ ?_
  simp only [PcOk] at hpc4
  have hf4 : SFr m1 st4.data := Fr.ofBlock hf3 hm3 hm4 hwf3 rfl rfl rfl (fun _ h ↦ absurd h (by simp))
  have hd4 : st4.data.dmem = m3.dmem := hm4.dmem_eq hwf3 rfl
  have hd : (m3.regs.getXReg .X22).toNat = dep m1 := by
    rw [hk3 .X22 rfl]; exact congrArg _ ho.x22
  have hk4 : ∀ r' : XReg, r' ≠ .X8 → r' ≠ .X27 →
      st4.data.regs.getXReg r' = m3.regs.getXReg r' := fun r' h8 h27 ↦
    reg_of hm4 (v := .reg r') (by cases r' <;> first | rfl | contradiction) rfl
  have hx27 : st4.data.regs.X27.toBitVec = rodataAddr .perChallenge := by
    have := reg_val hm4 (r := .X27) rfl
    show (st4.data.regs.getXReg .X27).toBitVec = _
    simpa [Sym.eval] using this
  have hnn : st4.data.regs.X8.toNat = min (128 / dep m1) r := by
    have := reg_val hm4 (r := .X8) rfl
    simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64, UnOp.apply] at this
    rw [per_load (per_at h hf3) (x := (perEnv m3).regs .X22)
      (by show (m3.regs.getXReg .X22).toNat < 129; rw [hd]; exact ho.dlt)] at this
    simp only [Env.ofMachine_regs, UInt64.toNat_toBitVec, hd, hk3 .X29 rfl] at this
    rw [bv_ult _ (by have := ho.dlt; have : 128 / dep m1 ≤ 128 := Nat.div_le_self _ _; omega)]
      at this
    show (st4.data.regs.getXReg .X8).toBitVec.toNat = _
    rw [this]
    have h29 : (st.data.regs.getXReg .X29).toNat = r := ho.x29
    have : 128 / dep m1 ≤ 128 := Nat.div_le_self _ _
    by_cases hlt : r < 128 / dep m1
    · simp only [h29, hlt, decide_true, ↓reduceIte, UInt64.toNat_toBitVec]; omega
    · simp only [h29, hlt, decide_false, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hcond4 : (SBool.cmp CmpOp.eq RegWidth.W64 (Sym.reg XReg.X22) (Sym.lit 0)).eval
      (perEnv m3) = decide (dep m1 = 0) := by
    sym_simp
    simp only [Env.ofMachine_regs]
    rw [bv_beq _ (by decide), hd]
  rw [hcond4] at hpc4
  have hmodel := auxP_next ho.model hjc hr
  by_cases hd0 : dep m1 = 0
  · -- depth `0`: no position
    simp only [hd0, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.SampleQueries.b8Offset) NativeRustcVmArm.Vm.SampleQueries.label_7_at] at hpc4
    refine .done _ (Or.inr (Or.inl ⟨hpc4, ?_⟩))
    have e0 : min (128 / dep m1) r = 0 := by rw [hd0]; simp
    rw [e0] at hmodel hnn
    exact {
      fr := hf4
      x8 := hnn
      x19 := ((hk4 .X19 (by decide) (by decide)).trans (hk3 .X19 rfl)).trans ho.x19
      x20 := ((hk4 .X20 (by decide) (by decide)).trans (hk3 .X20 rfl)).trans ho.x20
      x21 := ((hk4 .X21 (by decide) (by decide)).trans (hk3 .X21 rfl)).trans ho.x21
      x22 := ((hk4 .X22 (by decide) (by decide)).trans (hk3 .X22 rfl)).trans ho.x22
      x25 := by
        rw [show st4.data.regs.X25 = st.data.regs.X25 from
          (hk4 .X25 (by decide) (by decide)).trans (hk3 .X25 rfl)]
        exact ho.x25
      x26 := ((hk4 .X26 (by decide) (by decide)).trans (hk3 .X26 rfl)).trans ho.x26
      x27 := hx27
      x28 := by
        rw [show st4.data.regs.X28 = st.data.regs.X28 from
          (hk4 .X28 (by decide) (by decide)).trans (hk3 .X28 rfl)]
        exact ho.x28
      x29 := by
        rw [show st4.data.regs.X29 = st.data.regs.X29 from
          (hk4 .X29 (by decide) (by decide)).trans (hk3 .X29 rfl)]
        exact ho.x29
      hle := Nat.zero_le _
      jlt := hjc
      len := by simpa using ho.len
      dlt := ho.dlt
      ts := by rw [hd4]; exact hts3
      buf := by rw [hd4]; exact hbuf3
      model := by simpa [chunk] using hmodel }
  · -- the positions: `b12`
    simp only [hd0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc4
    rw [show k + NativeRustcVmArm.Vm.SampleQueries.b10Offset + b10.length + b11.length = k + NativeRustcVmArm.Vm.SampleQueries.b12Offset from by
      rw [← b11_next, ← b10_next]
      simp only [Nat.add_assoc]] at hpc4
    have hwf5 := frame_wf h hf4
    have hm5 := frame_match h hf4
    refine exec_at (inf hp b12_in_code (by simp [b12])) run_b12 hwf5 hpc4 hm5
      fun st5 hm5' hpc5 ↦ ?_
    simp only [PcOk, show k + NativeRustcVmArm.Vm.SampleQueries.b12Offset + b12.length = k + NativeRustcVmArm.Vm.SampleQueries.b13Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.SampleQueries.b12_next]] at hpc5
    refine .done _ (Or.inr (Or.inr ⟨hpc5, min (128 / dep m1) r, ?_⟩))
    have hN := pre_N h
    have hdpos : 1 ≤ 128 / dep m1 := (Nat.le_div_iff_mul_le (by omega)).mpr (by
      have := ho.dlt; omega)
    have hnn1 : 1 ≤ min (128 / dep m1) r := by omega
    have hmem5 : ∀ w ∈ (after b12 frameS).mem, w.r = 0 ∧ w.off + w.n ≤ 112 := by
      rw [after_eq run_b12]; decide
    rw [after_eq run_b12] at hmem5
    have hs5 : SameOutside st4.data.dmem st5.data.dmem (InRange (base m1 112) 112) :=
      NativeRustcVm.SameOutside.mono (hm5'.sameOutside hwf5) fun q hq ↦
        written_r0 hwf5 rfl hmem5 hq
    have hf5 : SFr m1 st5.data := Fr.ofBlockW hf4 hm5 hm5' hwf5 rfl rfl
      (fun _ h ↦ absurd h (by simp)) rfl (by decide) hN (by decide)
      (writeOk_of (F := 112) (slots := slots) (wr := []) hm5' (by decide)
        (fun _ h ↦ by cases h))
    have k5 : ∀ r' : XReg, (after b12 frameS).reg r' = some (.reg r') → r' ≠ .X8 → r' ≠ .X27 →
        calleeSaved r' = true → st5.data.regs.getXReg r' = st.data.regs.getXReg r' :=
      fun r' hr h8 h27 hc ↦ (reg_of hm5' (v := .reg r')
        (by rw [after_eq run_b12] at hr; exact hr) rfl).trans
        ((hk4 r' h8 h27).trans (hk3 r' hc))
    have hx0 : st4.data.regs.X0 = (sq s).1.c0 :=
      (hk4 .X0 (by decide) (by decide)).trans h30
    have hx1 : st4.data.regs.X1 = (sq s).1.c1 :=
      (hk4 .X1 (by decide) (by decide)).trans h31
    have h28 : st4.data.regs.X28.toNat = qs.length := by
      rw [show st4.data.regs.X28 = st.data.regs.X28 from
        (hk4 .X28 (by decide) (by decide)).trans (hk3 .X28 rfl)]
      exact ho.x28
    have h26 : st4.data.regs.X26 = 230 :=
      ((hk4 .X26 (by decide) (by decide)).trans (hk3 .X26 rfl)).trans ho.x26
    have hlen : qs.length < 230 := by have := ho.len; omega
    have hts5 : TStateAt st5.data.dmem (tA m1) a (sq s).2 := by
      rw [← hd4] at hts3
      exact hts3.frame (hm5'.kept hwf5) (fun q hq ↦ frame_not_t h hq) hs5
    have hbuf5 : BufWordsAt st5.data.dmem (oA m1) queryCap qs := by
      rw [← hd4] at hbuf3
      exact hbuf3.of_sameOutside hs5 (fun q hq ↦ frame_not_o h hq) (out_noWrap h)
    have hw0 := hm5'.bytesAt_write (r := 0) (o := 0) (n := 8) (b := base m1 112) (sz := 112) rfl
      (by decide) (v := .reg .X8) (by decide)
    have hw8 := hm5'.bytesAt_write (r := 0) (o := 8) (n := 8) (b := base m1 112) (sz := 112) rfl
      (by decide) (v := .reg .X25) (by decide)
    rw [wordBytes_reg] at hw0 hw8
    exact {
      fr := hf5
      x19 := (k5 .X19 rfl (by decide) (by decide) rfl).trans ho.x19
      x20 := (k5 .X20 rfl (by decide) (by decide) rfl).trans ho.x20
      x21 := (k5 .X21 rfl (by decide) (by decide) rfl).trans ho.x21
      x22 := (k5 .X22 rfl (by decide) (by decide) rfl).trans ho.x22
      x23 := (reg_of hm5' (r := .X23) (v := .reg .X0) rfl rfl).trans hx0
      x24 := (reg_of hm5' (r := .X24) (v := .reg .X1) rfl rfl).trans hx1
      x25 := by
        rw [show st5.data.regs.X25 = 0 from reg_of hm5' (r := .X25) (v := .lit 0) rfl rfl]
        simp
      x26 := by
        have := reg_val hm5' (r := .X26) rfl
        sym_simp at this
        simp only [Env.ofMachine_regs] at this
        rw [Nat.add_zero, ← h28]
        exact toNat_add_of this (by rw [h28]; omega)
      x27 := by
        have := reg_val hm5' (r := .X27) rfl
        have h28' : (st4.data.regs.getXReg .X28).toNat < 230 := by
          show st4.data.regs.X28.toNat < 230; omega
        sym_simp at this
        simp only [Env.ofMachine_regs, bv_ult _ (show 230 < 2 ^ 64 by decide), h28',
          decide_true, ↓reduceIte] at this
        show (st5.data.regs.getXReg .X27).toBitVec = _
        rw [this, Nat.add_zero]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [UInt64.toNat_toBitVec, BitVec.toNat_ofNat]
        show st4.data.regs.X28.toNat = _
        omega
      x28 := by
        have := reg_val hm5' (r := .X28) rfl
        have hx8 : (st4.data.regs.getXReg .X8).toNat = min (128 / dep m1) r := hnn
        sym_simp at this
        simp only [Env.ofMachine_regs, bv_ult _ (show 1 < 2 ^ 64 by decide),
          bv_beq _ (show 1 < 2 ^ 64 by decide), hx8] at this
        show (st5.data.regs.getXReg .X28).toBitVec.toNat = _
        rw [this]
        by_cases h1 : min (128 / dep m1) r = 1
        · simp [h1]
        · have : ¬ min (128 / dep m1) r < 1 := by omega
          simp only [this, h1, decide_false, Bool.not_false, Bool.and_self, ↓reduceIte,
            UInt64.toNat_toBitVec, hx8, Nat.sub_zero]
      x29 := by
        rw [show st5.data.regs.X29 = st.data.regs.X29 from k5 .X29 rfl (by decide) (by decide) rfl]
        exact ho.x29
      words := by
        rw [NativeRustcVm.wordsAt_cons_iff, NativeRustcVm.wordsAt_singleton_iff]
        have hx8 : (st4.data.regs.getXReg .X8).toNat = min (128 / dep m1) r := hnn
        have hx25 : (st4.data.regs.getXReg .X25).toNat = j := by
          rw [(hk4 .X25 (by decide) (by decide)).trans (hk3 .X25 rfl)]
          exact ho.x25
        rw [NativeRustcVm.addr_add_zero] at hw0
        have e1 : (min (128 / dep m1) r).toUInt64 = st4.data.regs.getXReg .X8 := by
          rw [← hx8]; simp
        have e2 : j.toUInt64 = st4.data.regs.getXReg .X25 := by rw [← hx25]; simp
        rw [e1, e2]
        exact ⟨hw0, hw8⟩
      jlt := hjc
      len := ho.len
      r0 := hr
      dpos := by omega
      dle := by have := ho.dlt; omega
      hn := rfl
      ilt := by omega
      ts := hts5
      buf := by simpa using hbuf5
      model := ho.model }

end

end

end NativeRustcVmArm.Whir.SampleQueries
