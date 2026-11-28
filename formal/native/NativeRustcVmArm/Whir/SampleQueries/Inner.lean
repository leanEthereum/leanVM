module

public import NativeRustcVmArm.Code.Vm.QueryBits.Names
public import NativeRustcVmArm.Whir.SampleQueries.Outer

/-!
# `sample_queries`: the inner loop

From the inner loop's head (`b13`, `Inner … i`): the buffer is not full (`b13`), `query_bits`
(`b14`), the position pushed (`b15`, `BufWordsAt.push`); then the head again (`Inner … (i + 1)`)
or, the chunk done, `b16`, `b7` (the chunk's count and the challenge's index reloaded from the
frame) and `b8` (`AtB8`) (`inner_step`, `inner_run`).
-/

namespace NativeRustcVmArm.Whir.SampleQueries

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.SampleQueries
open NativeRustcVm (BufWordsAt WordsAt WordAt bufSlot)

public section

theorem memExtend3 (x : BitVec 64) :
    BitVec.ofInt 64 (x.apply_mem_extend ⟨.UXTX, .E3⟩) = BitVec.ofNat 64 (8 * x.toNat) := by
  simp only [BitVec.apply_mem_extend, BitVec.unsigned, Int.shiftLeft_eq]
  rw [show ((x.toNat : Int) * 2 ^ 3) = ((8 * x.toNat : Nat) : Int) by push_cast; omega,
    BitVec.ofInt_natCast]

theorem sub230_succ (a : Nat) :
    BitVec.ofNat 64 a - 230#64 + 1#64 = BitVec.ofNat 64 (a + 1) - 230#64 := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (-230#64),
    ← BitVec.add_assoc, BitVec.ofNat_add]

section
variable [Labels] {a : DecArea} {s0 : TState} {m1 : MachineData}

/-- The push's regions: the frame, the count word, the slot of entry `c`. -/
abbrev pushEnv (m1 st : MachineData) (c : Nat) : Env :=
  Env.ofMachine st [(base m1 112, 112), (oA m1, 8), (bufSlot (oA m1) c, 8)]

theorem push_wf (h : SampleQueriesPre a s0 m1) {st : MachineData} (hf : SFr m1 st) {c : Nat}
    (hc : c < queryCap) : (pushEnv m1 st c).WF := by
  have hN := pre_N h
  have hv := N_val
  obtain ⟨⟨hmo, hno, hot, hod, hos, hor⟩, -⟩ := h.2.2.2
  have hq : queryBufBytes = 8 + 8 * queryCap := rfl
  have hqc : queryCap = 230 := rfl
  replace hno : (oA m1).toNat + queryBufBytes ≤ 2 ^ 64 := hno
  have e1 := base_toNat (m0 := m1) (F := 112) (by omega)
  have e2 := base_toNat (m0 := m1) (F := sampleQueriesStack) hN
  have es : (bufSlot (oA m1) c).toNat = (oA m1).toNat + (8 + 8 * c) :=
    NativeRustcVm.toNat_add_ofNat (a := oA m1) (i := 8 + 8 * c) (by omega)
  refine Env.wf_of ⟨(frame_wf h hf).mapped 0 _ _ rfl |> fun hm ↦ ⟨hm, base_noWrap (by omega)⟩,
    ⟨fun i hi ↦ hf.kept _ (hmo i (by omega)), by show (oA m1).toNat + 8 ≤ 2 ^ 64; omega⟩,
    ⟨fun i hi ↦ ?_, by show (bufSlot (oA m1) c).toNat + 8 ≤ 2 ^ 64; omega⟩, trivial⟩ ?_
  · have := hf.kept _ (hmo (8 + 8 * c + i) (by omega))
    rwa [← NativeRustcVm.addr_add_add] at this
  · have hs : (stackBelow m1 sampleQueriesStack).toNat = m1.regs.SP.toNat - sampleQueriesStack :=
      e2
    unfold Apart at hos
    rw [hs] at hos
    have es' : (bufSlot (oA m1) c).toNat = m1.regs.X3.toBitVec.toNat + (8 + 8 * c) := es
    have hno' : m1.regs.X3.toBitVec.toNat + queryBufBytes ≤ 2 ^ 64 := hno
    change m1.regs.X3.toBitVec.toNat + queryBufBytes ≤ _ ∨ _ at hos
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.pairwise_singleton _ _))
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · show (base m1 112).toNat + 112 ≤ (oA m1).toNat ∨ (oA m1).toNat + 8 ≤ (base m1 112).toNat
        omega
      · show (base m1 112).toNat + 112 ≤ (bufSlot (oA m1) c).toNat ∨
          (bufSlot (oA m1) c).toNat + 8 ≤ (base m1 112).toNat
        omega
    · intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      subst he
      show (oA m1).toNat + 8 ≤ (bufSlot (oA m1) c).toNat ∨ _
      omega

end

section
variable [Host] {a : DecArea} {s0 : TState} {m1 : MachineData} {k : Nat}

/-- **The inner loop's turn.** -/
theorem inner_step (hp : Placed code k) (h : SampleQueriesPre a s0 m1)
    (hqb : Spec (Labels.label NativeRustcVmArm.Vm.QueryBits.entryLabel) QueryBitsPre QueryBitsPost)
    {j r : Nat} {s : TState} {qs : List UInt64} {n i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SampleQueries.b13Offset)) (hi : Inner a s0 m1 j r s qs n i st.data) :
    Eventually (step1 Host.exe)
      (fun st' ↦ (st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SampleQueries.b13Offset) ∧ Inner a s0 m1 j r s qs n (i + 1) st'.data) ∨
        (st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SampleQueries.b8Offset) ∧
          AtB8 a s0 m1 j r n (sq s).2 (qs ++ (chunk (dep m1) (sq s).1 n).toList) st'.data)) st := by
  have hc := cnt_le h
  have hN := pre_N h
  have hnr : n ≤ r := by rw [hi.hn]; exact Nat.min_le_right _ _
  have hli : qs.length + i < 230 := by have := hi.len; have := hi.ilt; omega
  -- `b13`: the buffer is not full
  refine hi.fr.regsBlock (inf hp b13_in_code (by simp [b13])) run_b13 hpc rfl rfl (by rfl)
    fun st1 hf1 hd1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  have hk1 : ∀ r' : XReg, st1.data.regs.getXReg r' = st.data.regs.getXReg r' := fun r' ↦
    reg_of hm1 (v := .reg r') (by cases r' <;> rfl) rfl
  have hcond1 : (SBool.cmp CmpOp.eq RegWidth.W64 (Sym.reg XReg.X27) (Sym.lit 0)).eval
      (Env.ofMachine st.data []) = false := by
    sym_simp
    simp only [Env.ofMachine_regs, beq_eq_false_iff_ne, ne_eq]
    show ¬st.data.regs.X27.toBitVec = _
    rw [hi.x27]
    intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_sub] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  rw [hcond1] at hpc1
  simp only [Bool.false_eq_true, ↓reduceIte, show k + NativeRustcVmArm.Vm.SampleQueries.b13Offset + b13.length = k + NativeRustcVmArm.Vm.SampleQueries.b14Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.SampleQueries.b13_next]] at hpc1
  -- `b14`: `query_bits`
  refine hf1.regsBlock (inf hp b14_in_code (by simp [b14])) run_b14 hpc1 rfl rfl (by rfl)
    fun st2 hf2 hd2 hm2 hpc2 ↦ ?_
  simp only [PcOk] at hpc2
  have hk2 : ∀ r' : XReg, calleeSaved r' = true →
      st2.data.regs.getXReg r' = st.data.regs.getXReg r' := fun r' hr' ↦
    (reg_of hm2 (v := .reg r') (by cases r' <;> first | rfl | simp [calleeSaved] at hr') rfl).trans
      (hk1 r')
  have hfr : ∀ q, outs m1 q → ¬InRange (base m1 112) 112 q := by
    rintro q (hq | hq) hin
    · exact frame_not_o h hin hq
    · exact (frame_not_t h hin).1 hq
  refine Fr.leaf (N' := queryBitsStack) hf2 hN (by decide) (fun _ h ↦ by cases h) (by decide)
    hfr hqb
    (fun m m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ by
      rcases hq' with ⟨_, hr, _⟩ | hq'
      · cases hr
      · exact absurd hq' (by unfold InRange queryBitsStack; omega), hq.2.2⟩) hpc2 trivial
    fun m3 hf3 hq3 hcs3 ↦ ?_
  have hd3 : ∀ p, m3.dmem.get? p = st.data.dmem.get? p := fun p ↦ by
    rw [hq3.2.1 p (fun hq' ↦ by
      rcases hq' with ⟨_, hr, _⟩ | hq'
      · cases hr
      · exact absurd hq' (by unfold InRange queryBitsStack; omega)), hd2, hd1]
  have hd3' : m3.dmem = st.data.dmem := Std.ExtHashMap.ext_getElem? fun p ↦ by
    rw [← Std.ExtHashMap.get?_eq_getElem?, ← Std.ExtHashMap.get?_eq_getElem?]
    exact hd3 p
  have hk3 : ∀ r' : XReg, calleeSaved r' = true →
      m3.regs.getXReg r' = st.data.regs.getXReg r' := fun r' hr' ↦
    (hcs3 r' hr').trans (hk2 r' hr')
  have hqv : m3.regs.X0 = queryBits (sq s).1 (i * dep m1) (dep m1) := by
    rw [hq3.1]
    have e0 : st2.data.regs.X0 = (sq s).1.c0 :=
      (reg_of hm2 (r := .X0) (v := .reg .X23) rfl rfl).trans ((hk1 .X23).trans hi.x23)
    have e1 : st2.data.regs.X1 = (sq s).1.c1 :=
      (reg_of hm2 (r := .X1) (v := .reg .X24) rfl rfl).trans ((hk1 .X24).trans hi.x24)
    have e2 : st2.data.regs.X2.toNat = i * dep m1 := by
      rw [show st2.data.regs.X2 = st.data.regs.X25 from
        (reg_of hm2 (r := .X2) (v := .reg .X25) rfl rfl).trans (hk1 .X25)]
      exact hi.x25
    have e3 : st2.data.regs.X3.toNat = dep m1 := by
      rw [show st2.data.regs.X3 = st.data.regs.X22 from
        (reg_of hm2 (r := .X3) (v := .reg .X22) rfl rfl).trans (hk1 .X22), hi.x22]
    rw [e0, e1, e2, e3]
  -- `b15`: the push
  have hlc : qs.length + i < queryCap := hli
  have hwf6 := push_wf h hf3 hlc
  have hx26 : (m3.regs.getXReg .X26).toNat = qs.length + i + 1 := by
    rw [hk3 .X26 rfl]; exact hi.x26
  have hm6 : Match (pushEnv m1 m3 (qs.length + i)) pushS m3 := by
    refine match_ofMachine ⟨rfl, fun _ ↦ frame_aligned (pre_stack h) (by decide) rfl, rfl,
      fun h ↦ absurd h (by decide), rfl, fun h ↦ absurd h (by decide), trivial⟩ ?_ ⟨?_, trivial⟩
      trivial trivial ⟨?_, trivial⟩
    · rw [hf3.sp]; simp [Sym.eval]
    · show (m3.regs.getXReg .X21).toBitVec = oA m1 + BitVec.ofInt 64 0
      rw [hk3 .X21 rfl]
      simp only [BitVec.ofInt_ofNat, BitVec.add_zero]
      exact congrArg UInt64.toBitVec hi.x21
    · simp only [slotAddr, Sym.eval, BinOp.apply, UnOp.apply, low_W64, ext_W64,
        Env.base_ofMachine_eq, Env.ofMachine_regs]
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
        Option.getD_some]
      rw [memExtend3, UInt64.toNat_toBitVec, hx26]
      simp only [BitVec.ofInt_ofNat, BitVec.add_zero]
      show oA m1 + BitVec.ofNat 64 (8 * (qs.length + i + 1)) =
        oA m1 + BitVec.ofNat 64 (8 + 8 * (qs.length + i))
      congr 2
      omega
  have hN' := hN
  obtain ⟨⟨hmo, hno, hot, hod, hos, hor⟩, -⟩ := h.2.2.2
  have hfp := h.2.1.footprint
  have hnt : NativeRustcVm.NoWrap (tA m1) tstateBytes := hfp.1.2
  have hnd : NativeRustcVm.NoWrap a.words (8 * a.len) := hfp.2.1.2
  have hno' : NativeRustcVm.NoWrap (oA m1) queryBufBytes := hno
  have hqb' : queryBufBytes = 8 + 8 * queryCap := rfl
  have hqc : queryCap = 230 := rfl
  have out_not : ∀ q, InRange (oA m1) queryBufBytes q →
      ¬InRange (tA m1) tstateBytes q ∧ ¬InRange a.words (8 * a.len) q := fun q hq ↦
    ⟨fun ht ↦ NativeRustcVm.Apart.not_inRange hot hno' hnt hq ht,
      fun hd ↦ NativeRustcVm.Apart.not_inRange hod hno' hnd hq hd⟩
  have sub_out : ∀ q, (InRange (oA m1) 8 q ∨ InRange (bufSlot (oA m1) (qs.length + i)) 8 q) →
      InRange (oA m1) queryBufBytes q := by
    rintro q (hq | hq)
    · exact NativeRustcVm.InRange.mono hq (hno'.mono (by omega)) hno' (Nat.le_refl _)
        (by omega)
    · exact NativeRustcVm.InRange.of_sub hq hno' (by omega)
  refine exec_at (st := ⟨m3, _⟩) (k := k + NativeRustcVmArm.Vm.SampleQueries.b15Offset) (inf hp b15_in_code (by simp [b15])) run_b15 hwf6
    rfl hm6 fun st7 hm7 hpc7 ↦ ?_
  simp only [PcOk] at hpc7
  have hrs : ∀ w ∈ (after b15 pushS).mem, (w.r = 1 ∨ w.r = 2) ∧ w.off + w.n ≤ 8 := by
    rw [after_eq run_b15]; decide
  rw [after_eq run_b15] at hrs
  have hs7 : SameOutside m3.dmem st7.data.dmem
      (fun q ↦ InRange (oA m1) 8 q ∨ InRange (bufSlot (oA m1) (qs.length + i)) 8 q) :=
    NativeRustcVm.SameOutside.mono (hm7.sameOutside hwf6) fun q hq ↦ by
      obtain ⟨w, hw, b, sz, hb, hin⟩ := written_inRange hwf6 (fun w hw b sz hb ↦ by
        obtain ⟨hr, hle⟩ := hrs w hw
        rcases hr with hr | hr <;> rw [hr] at hb <;> simp at hb <;> omega) hq
      obtain ⟨hr, -⟩ := hrs w hw
      rcases hr with hr | hr <;> rw [hr] at hb <;> simp at hb <;> obtain ⟨rfl, rfl⟩ := hb
      · exact Or.inl hin
      · exact Or.inr hin
  have hf7 : SFr m1 st7.data := Fr.ofBlockW hf3 hm6 hm7 hwf6 rfl rfl
    (fun _ h ↦ absurd h (by simp)) rfl (by decide) hN (by decide)
    (writeOk_of (F := 112) (slots := slots) (wr := [1, 2]) hm7 (by decide) fun r hr b sz hb j hj ↦ by
      left
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp at hb <;> obtain ⟨rfl, rfl⟩ := hb
      · exact sub_out _ (Or.inl (NativeRustcVm.inRange_add hj (by omega)))
      · exact sub_out _ (Or.inr (NativeRustcVm.inRange_add hj (by omega))))
  -- the buffer, the `TState`, the frame's words
  have hlt : ((chunk (dep m1) (sq s).1 n).toList.take i).length = i := by
    have := hi.ilt; simp [chunk_size]; omega
  have hb3 : BufWordsAt m3.dmem (oA m1) queryCap
      (qs ++ (chunk (dep m1) (sq s).1 n).toList.take i) := by rw [hd3']; exact hi.buf
  have hw1 := hm7.bytesAt_write (r := 1) (o := 0) (n := 8) (b := oA m1) (sz := 8) rfl
    (by decide) (v := .reg .X26) (by decide)
  have hw2 := hm7.bytesAt_write (r := 2) (o := 0) (n := 8) (b := bufSlot (oA m1) (qs.length + i))
    (sz := 8) rfl (by decide) (v := .reg .X0) (by decide)
  rw [wordBytes_reg, NativeRustcVm.addr_add_zero] at hw1 hw2
  have hbuf7 : BufWordsAt st7.data.dmem (oA m1) queryCap
      (qs ++ (chunk (dep m1) (sq s).1 n).toList.take (i + 1)) := by
    rw [chunk_take_succ _ _ hi.ilt, ← List.append_assoc]
    refine hb3.push (by simp [hlt]; omega) (by rw [hqc]; exact hno)
      ?_ ?_ (by rw [List.length_append, hlt]; exact hs7)
    · simp only [List.length_append, hlt]
      have e : (qs.length + i + 1).toUInt64 = m3.regs.getXReg .X26 := by
        rw [← hx26]; simp
      rw [e]; exact hw1
    · simp only [List.length_append, hlt]
      rw [← hqv]; exact hw2
  have hts7 : TStateAt st7.data.dmem (tA m1) a (sq s).2 := by
    have := hi.ts
    rw [← hd3'] at this
    exact this.frame (hm7.kept hwf6) (fun q hq ↦ out_not q (sub_out q hq)) hs7
  have hwords7 : WordsAt st7.data.dmem (base m1 112) [n.toUInt64, j.toUInt64] := by
    have := hi.words
    rw [← hd3'] at this
    exact this.of_sameOutside hs7 fun q hq hin ↦ frame_not_o h (by
      rw [NativeRustcVm.length_wordsBytes] at hq
      have : q < 16 := by simpa using hq
      exact NativeRustcVm.inRange_add (by omega) (by decide)) (sub_out _ hin)
  -- the registers
  have hk7 : ∀ r' : XReg, (after b15 pushS).reg r' = some (.reg r') → calleeSaved r' = true →
      st7.data.regs.getXReg r' = st.data.regs.getXReg r' := fun r' hr hc ↦
    (reg_of hm7 (v := .reg r') (by rw [after_eq run_b15] at hr; exact hr) rfl).trans (hk3 r' hc)
  have hx21 : st7.data.regs.X21 = m1.regs.X3 := by
    apply UInt64.toBitVec_inj.mp
    have := reg_val hm7 (r := .X21) rfl
    simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.map_some, Option.getD_some, BitVec.ofInt_ofNat, BitVec.add_zero] at this
    exact this
  have hd22 : (m3.regs.getXReg .X22).toNat = dep m1 := by
    rw [hk3 .X22 rfl]; exact congrArg _ hi.x22
  have hnd : n * dep m1 ≤ 128 := by
    rw [hi.hn]
    exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.min_le_left _ _)) (Nat.div_mul_le_self _ _)
  have hid : (i + 1) * dep m1 ≤ 128 :=
    Nat.le_trans (Nat.mul_le_mul_right _ hi.ilt) hnd
  have h25 : st7.data.regs.X25.toNat = (i + 1) * dep m1 := by
    have := reg_val hm7 (r := .X25) rfl
    sym_simp at this
    simp only [Env.ofMachine_regs] at this
    have e := congrArg BitVec.toNat this
    rw [BitVec.toNat_add] at e
    simp only [UInt64.toNat_toBitVec, hd22] at e
    have e25 : (m3.regs.getXReg .X25).toNat = i * dep m1 := by
      rw [hk3 .X25 rfl]; exact hi.x25
    rw [e25] at e
    have hid' : i * dep m1 + dep m1 ≤ 128 := by have := hid; rwa [Nat.succ_mul] at this
    show (st7.data.regs.getXReg .X25).toNat = _
    rw [e, Nat.succ_mul]
    exact Nat.mod_eq_of_lt (by omega)
  have h26 : st7.data.regs.X26.toNat = qs.length + (i + 1) + 1 := by
    have := reg_val hm7 (r := .X26) rfl
    sym_simp at this
    simp only [Env.ofMachine_regs] at this
    rw [show qs.length + (i + 1) + 1 = (m3.regs.getXReg .X26).toNat + 1 by rw [hx26]; omega]
    exact toNat_add_of this (by rw [hx26]; omega)
  have h27 : st7.data.regs.X27.toBitVec = BitVec.ofNat 64 (qs.length + (i + 1)) - 230#64 := by
    have := reg_val hm7 (r := .X27) rfl
    sym_simp at this
    simp only [Env.ofMachine_regs] at this
    show (st7.data.regs.getXReg .X27).toBitVec = _
    rw [this, hk3 .X27 rfl]
    have e : (st.data.regs.getXReg .X27).toBitVec = BitVec.ofNat 64 (qs.length + i) - 230#64 :=
      hi.x27
    rw [e, sub230_succ, Nat.add_assoc]
  have h28' : (m3.regs.getXReg .X28).toNat = n - i := by rw [hk3 .X28 rfl]; exact hi.x28
  have h28 : st7.data.regs.X28.toNat = n - (i + 1) := by
    have := reg_val hm7 (r := .X28) rfl
    sym_simp at this
    simp only [Env.ofMachine_regs] at this
    have e := toNat_sub_of (z := 1) this (by rw [h28']; have := hi.ilt; simp; omega)
    rw [h28'] at e
    simp at e
    show (st7.data.regs.getXReg .X28).toNat = _
    rw [e]; omega
  have hcond7 : (SBool.cmp CmpOp.eq RegWidth.W64 (Sym.reg XReg.X28) (Sym.lit 1)).not.eval
      (pushEnv m1 m3 (qs.length + i)) = decide (i + 1 < n) := by
    sym_simp
    simp only [Env.ofMachine_regs]
    rw [bv_beq _ (by decide), h28']
    have := hi.ilt
    by_cases hc : i + 1 < n
    · simp only [hc, decide_true]; simp; omega
    · simp only [hc, decide_false]; simp; omega
  rw [hcond7] at hpc7
  by_cases hc : i + 1 < n
  · simp only [hc, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.SampleQueries.b13Offset) NativeRustcVmArm.Vm.SampleQueries.label_11_at] at hpc7
    refine .done _ (Or.inl ⟨hpc7, ?_⟩)
    exact {
      fr := hf7
      x19 := (hk7 .X19 rfl rfl).trans hi.x19
      x20 := (hk7 .X20 rfl rfl).trans hi.x20
      x21 := hx21
      x22 := (hk7 .X22 rfl rfl).trans hi.x22
      x23 := (hk7 .X23 rfl rfl).trans hi.x23
      x24 := (hk7 .X24 rfl rfl).trans hi.x24
      x25 := h25
      x26 := h26
      x27 := h27
      x28 := h28
      x29 := by
        rw [show st7.data.regs.X29 = st.data.regs.X29 from hk7 .X29 rfl rfl]; exact hi.x29
      words := hwords7
      jlt := hi.jlt
      len := hi.len
      r0 := hi.r0
      dpos := hi.dpos
      dle := hi.dle
      hn := hi.hn
      ilt := hc
      ts := hts7
      buf := hbuf7
      model := hi.model }
  · have hn1 : i + 1 = n := by have := hi.ilt; omega
    simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc7
    rw [show k + NativeRustcVmArm.Vm.SampleQueries.b15Offset + b15.length = k + NativeRustcVmArm.Vm.SampleQueries.b16Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.SampleQueries.b15_next]] at hpc7
    refine hf7.regsBlock (inf hp b16_in_code (by simp [b16])) run_b16 hpc7 rfl rfl (by rfl)
      fun st8 hf8 hd8 hm8 hpc8 ↦ ?_
    simp only [PcOk, hp.label (j := NativeRustcVmArm.Vm.SampleQueries.b7Offset) NativeRustcVmArm.Vm.SampleQueries.label_6_at] at hpc8
    have hwf9 := frame_wf h hf8
    have hm9 := frame_match h hf8
    refine exec_at (inf hp b7_in_code (by simp [b7])) run_b7 hwf9 hpc8 hm9 fun st9 hm9' hpc9 ↦ ?_
    simp only [PcOk, show k + NativeRustcVmArm.Vm.SampleQueries.b7Offset + b7.length = k + NativeRustcVmArm.Vm.SampleQueries.b8Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.SampleQueries.b7_next]] at hpc9
    refine .done _ (Or.inr ⟨hpc9, ?_⟩)
    have hf9 : SFr m1 st9.data :=
      Fr.ofBlock hf8 hm9 hm9' hwf9 rfl rfl rfl (fun _ h ↦ absurd h (by simp))
    have hd9 : st9.data.dmem = st8.data.dmem := hm9'.dmem_eq hwf9 rfl
    have hw := hwords7
    rw [← hd8, NativeRustcVm.wordsAt_cons_iff, NativeRustcVm.wordsAt_singleton_iff] at hw
    obtain ⟨w0, w8⟩ := hw
    rw [← NativeRustcVm.addr_add_zero (base m1 112)] at w0
    have k8 : ∀ r' : XReg, st8.data.regs.getXReg r' = st7.data.regs.getXReg r' := fun r' ↦
      reg_of hm8 (v := .reg r') (by cases r' <;> rfl) rfl
    have k9 : ∀ r' : XReg, r' ≠ .X8 → r' ≠ .X25 → r' ≠ .X26 → r' ≠ .X27 → r' ≠ .X28 →
        st9.data.regs.getXReg r' = st7.data.regs.getXReg r' := fun r' h8 h25 h26 h27 h28 ↦
      (reg_of hm9' (v := .reg r') (by cases r' <;> first | rfl | contradiction) rfl).trans (k8 r')
    have hlt' : n < 2 ^ 64 := by have := hi.dle; have := hnd; omega
    have hjlt : j < 2 ^ 64 := by have := hi.jlt; have := cnt_le h; omega
    have hx8 : st9.data.regs.X8 = n.toUInt64 :=
      reg_of hm9' (r := .X8) rfl (by exact load_word w0)
    have hx25 : st9.data.regs.X25 = j.toUInt64 :=
      reg_of hm9' (r := .X25) rfl (by exact load_word w8)
    have hnr' : n ≤ r := hnr
    exact {
      fr := hf9
      x8 := by rw [hx8]; simp; omega
      x19 := ((k9 .X19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (hk7 .X19 rfl rfl)).trans hi.x19
      x20 := ((k9 .X20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (hk7 .X20 rfl rfl)).trans hi.x20
      x21 := (k9 .X21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx21
      x22 := ((k9 .X22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (hk7 .X22 rfl rfl)).trans hi.x22
      x25 := by rw [hx25]; simp; omega
      x26 := reg_of hm9' (r := .X26) (v := .lit 230) rfl rfl
      x27 := by
        have := reg_val hm9' (r := .X27) rfl
        exact this
      x28 := by
        have := reg_val hm9' (r := .X28) rfl
        sym_simp at this
        simp only [Env.ofMachine_regs] at this
        have h26' : (st7.data.regs.getXReg .X26).toNat = qs.length + (i + 1) + 1 := h26
        have e := toNat_sub_of (z := 1) this (by
          rw [k8 .X26, show (1 : UInt64).toNat = 1 from rfl]; omega)
        rw [k8 .X26] at e
        simp only [List.length_append, Array.length_toList, chunk_size]
        show (st9.data.regs.getXReg .X28).toNat = _
        rw [e]
        have : (st7.data.regs.getXReg .X26).toNat = qs.length + (i + 1) + 1 := h26
        simp
        omega
      x29 := by
        rw [show st9.data.regs.X29 = st.data.regs.X29 from
          (k9 .X29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            (hk7 .X29 rfl rfl)]
        exact hi.x29
      hle := hnr'
      jlt := hi.jlt
      len := by simp only [List.length_append, Array.length_toList, chunk_size]; have := hi.len; omega
      dlt := by have := hi.dle; omega
      ts := by rw [hd9, hd8]; exact hts7
      buf := by rw [hd9, hd8]; rw [hn1, chunk_take_all] at hbuf7; exact hbuf7
      model := by
        have := auxP_next hi.model hi.jlt hi.r0
        rw [← hi.hn] at this
        exact this }

end

end

end NativeRustcVmArm.Whir.SampleQueries
