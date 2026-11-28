module

public import NativeRustcVmArm.Whir.SampleQueries.Exit
public import NativeRustcVmArm.Whir.Block
public import NativeRustcVm.Whir.Buf

/-!
# `sample_queries`: the end of a challenge

`b8` (`.LSampleQueries_7`) after the `j`th challenge's `n` positions (`AtB8`): the count of
challenges bumped, the positions left lessened; the epilogue after the last challenge, else the
outer loop's head (`tail_b8`). The loop's states (`OuterAt`), the facts the blocks' conditions
read (`bv_beq`, `bv_ult`), the buffer kept across a squeeze (`buf_sq`).
-/

namespace NativeRustcVmArm.Whir.SampleQueries

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.SampleQueries
open NativeRustcVm (BufWordsAt WordsAt WordAt)

public section

/-! ## Words -/

theorem bv_beq (x : UInt64) {n : Nat} (hn : n < 2 ^ 64) :
    (x.toBitVec == BitVec.ofNat 64 n) = decide (x.toNat = n) := by
  by_cases h : x.toNat = n
  · simp only [h, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    simp only [UInt64.toNat_toBitVec, BitVec.toNat_ofNat, h]
    omega
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro he
    apply h
    have := congrArg BitVec.toNat he
    simp only [UInt64.toNat_toBitVec, BitVec.toNat_ofNat] at this
    omega

theorem bv_ult (x : UInt64) {n : Nat} (hn : n < 2 ^ 64) :
    x.toBitVec.ult (BitVec.ofNat 64 n) = decide (x.toNat < n) := by
  simp only [BitVec.ult, UInt64.toNat_toBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem toNat_add_of {x y : UInt64} {c : Nat} (h : x.toBitVec = y.toBitVec + BitVec.ofNat 64 c)
    (hlt : y.toNat + c < 2 ^ 64) : x.toNat = y.toNat + c := by
  have := congrArg BitVec.toNat h
  rw [NativeRustcVm.toNat_add_ofNat (by simpa using hlt)] at this
  simpa using this

theorem toNat_sub_of {x y z : UInt64} (h : x.toBitVec = y.toBitVec - z.toBitVec)
    (hle : z.toNat ≤ y.toNat) : x.toNat = y.toNat - z.toNat := by
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_sub] at this
  simp only [UInt64.toNat_toBitVec] at this
  have := y.toNat_lt
  omega

theorem inf [Host] {k : Nat} (hp : Placed code k) {b : List Directive} {j : Nat}
    (hb : b.IsInfixAt code j) (hne : b ≠ []) : b.IsInfixAt Host.prog (k + j) :=
  hb.trans hp.1 hne

section
variable [Labels] {a : DecArea} {s0 : TState} {m1 : MachineData}

/-- The output buffer does not wrap. -/
theorem out_noWrap (h : SampleQueriesPre a s0 m1) : NativeRustcVm.NoWrap (oA m1) (8 + 8 * queryCap) :=
  h.2.2.2.1.2.1

/-- **The buffer across a squeeze**: apart from the sponge and the callee's stack. -/
theorem buf_sq (h : SampleQueriesPre a s0 m1) {st : MachineData} (hf : SFr m1 st) {d' : Mem 64}
    (hs : SameOutside st.dmem d' fun q ↦ InRange (tA m1) spongeBytes q ∨
      InRange (stackBelow st squeezeStack) squeezeStack q)
    {qs : List UInt64} (hb : BufWordsAt st.dmem (oA m1) queryCap qs) :
    BufWordsAt d' (oA m1) queryCap qs := by
  have hN := pre_N h
  obtain ⟨⟨hmo, hno, hot, hod, hos, hor⟩, -⟩ := h.2.2.2
  have hfp := h.2.1.footprint
  have hnt : NativeRustcVm.NoWrap (tA m1) tstateBytes := hfp.1.2
  refine hb.of_sameOutside hs (fun q hq hin ↦ ?_) hno
  rcases hq with hq | hq
  · exact NativeRustcVm.Apart.not_inRange hot hno hnt hin
      (NativeRustcVm.InRange.mono hq (NativeRustcVm.NoWrap.mono hnt sponge_le) hnt
        (Nat.le_refl _) (Nat.add_le_add_left sponge_le _))
  · exact NativeRustcVm.Apart.not_inRange hos hno (base_noWrap hN) hin
      (stack_in hf (by rw [N_eq]) hN hq)

end

/-! ## The loop's states -/

section
variable [Host] {a : DecArea} {s0 : TState} {m1 : MachineData}

/-- The outer loop's head with measure `n`: `j` challenges done, `n = count - j`. -/
@[expose] def OuterAt (a : DecArea) (s0 : TState) (m1 : MachineData) (k n : Nat)
    (st : MachineState) : Prop :=
  ∃ j r s qs, n = cnt m1 - j ∧ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SampleQueries.b9Offset) ∧ Outer a s0 m1 j r s qs st.data

end

section
variable [Labels]

/-- **At `b8`**, after the `j`th challenge's `nn` positions: the positions `qs`, `r` left before
them, the transcript's state `s`. -/
structure AtB8 (a : DecArea) (s0 : TState) (m1 : MachineData) (j r nn : Nat) (s : TState)
    (qs : List UInt64) (st : MachineData) : Prop where
  fr : SFr m1 st
  x8 : st.regs.X8.toNat = nn
  x19 : st.regs.X19 = m1.regs.X2
  x20 : st.regs.X20 = m1.regs.X0
  x21 : st.regs.X21 = m1.regs.X3
  x22 : st.regs.X22 = m1.regs.X1
  x25 : st.regs.X25.toNat = j
  x26 : st.regs.X26 = 230
  x27 : st.regs.X27.toBitVec = rodataAddr .perChallenge
  x28 : st.regs.X28.toNat = qs.length
  x29 : st.regs.X29.toNat = r
  hle : nn ≤ r
  jlt : j < cnt m1
  len : qs.length + (r - nn) = cnt m1
  dlt : dep m1 < 129
  ts : TStateAt st.dmem (tA m1) a s
  buf : BufWordsAt st.dmem (oA m1) queryCap qs
  model : auxP (dep m1) (cnt m1) (cnt m1) s0 =
    (qs.toArray ++ (auxP (dep m1) (cnt m1 - (j + 1)) (r - nn) s).1,
      (auxP (dep m1) (cnt m1 - (j + 1)) (r - nn) s).2)

end

section
variable [Host] {a : DecArea} {s0 : TState} {m1 : MachineData} {k : Nat}

theorem cnt_le (h : SampleQueriesPre a s0 m1) : cnt m1 ≤ 230 := h.2.2.1

/-- **`b8`**: the epilogue after the last challenge, else the outer loop's head. -/
theorem tail_b8 (hp : Placed code k) (h : SampleQueriesPre a s0 m1) {j r nn : Nat} {s : TState}
    {qs : List UInt64} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SampleQueries.b8Offset))
    (hb : AtB8 a s0 m1 j r nn s qs st.data) :
    Eventually (step1 Host.exe)
      (fun st' ↦ Goal a s0 m1 st' ∨ ∃ n' < cnt m1 - j, OuterAt a s0 m1 k n' st') st := by
  have hc := cnt_le h
  have hjc := hb.jlt
  refine hb.fr.regsBlock (inf hp b8_in_code (by simp [b8])) run_b8 hpc rfl rfl (by rfl)
    fun st1 hf1 hd1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  have h0 : st1.data.regs.X0 = 1 := reg_of hm1 (r := .X0) rfl rfl
  have h25 : st1.data.regs.X25.toNat = j + 1 := by
    have := reg_val hm1 (r := .X25) rfl
    sym_simp at this
    rw [← hb.x25]
    exact toNat_add_of this (by rw [hb.x25]; omega)
  have h29 : st1.data.regs.X29.toNat = r - nn := by
    have := reg_val hm1 (r := .X29) rfl
    sym_simp at this
    rw [← hb.x29, ← hb.x8]
    exact toNat_sub_of this (by rw [hb.x29, hb.x8]; exact hb.hle)
  have hk : ∀ r' : XReg, r' ≠ .X0 → r' ≠ .X25 → r' ≠ .X29 →
      st1.data.regs.getXReg r' = st.data.regs.getXReg r' := by
    intro r' h1 h2 h3
    exact reg_of hm1 (v := .reg r') (by cases r' <;> first | rfl | contradiction) rfl
  have hcond : (SBool.cmp CmpOp.eq RegWidth.W64 (Sym.bin BinOp.add RegWidth.W64 (Sym.reg XReg.X25)
      (Sym.lit 1)) (Sym.reg XReg.X19)).eval (Env.ofMachine st.data []) = decide (j + 1 = cnt m1) := by
    have e : (st.data.regs.getXReg .X25).toBitVec + 1#64 = BitVec.ofNat 64 (j + 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add]
      simp only [UInt64.toNat_toBitVec, BitVec.toNat_ofNat]
      rw [show (st.data.regs.getXReg .X25).toNat = j from hb.x25]
    sym_simp
    simp only [Env.ofMachine_regs]
    rw [show st.data.regs.getXReg .X19 = m1.regs.X2 from hb.x19, e, Bool.eq_iff_iff, beq_iff_eq,
      decide_eq_true_eq]
    have : m1.regs.X2.toNat < 2 ^ 64 := m1.regs.X2.toNat_lt
    constructor
    · intro he
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat, UInt64.toNat_toBitVec] at this
      show j + 1 = m1.regs.X2.toNat
      omega
    · intro hq
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, UInt64.toNat_toBitVec]
      change j + 1 = m1.regs.X2.toNat at hq
      omega
  rw [hcond] at hpc1
  by_cases hq : j + 1 = cnt m1
  · -- the last challenge: the epilogue
    simp only [hq, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.SampleQueries.b18Offset) NativeRustcVmArm.Vm.SampleQueries.label_14_at] at hpc1
    refine Eventually.mono (finish hp h hpc1 hf1 h0 (qs := qs) (s := s) ?_
      (by rw [hd1]; exact hb.buf) (by rw [hd1]; exact hb.ts)) fun _ hg ↦ Or.inl hg
    rw [hb.model, show cnt m1 - (j + 1) = 0 by omega, auxP_zero_left]
    simp
  · simp only [hq, decide_false, Bool.false_eq_true, ↓reduceIte,
      show k + NativeRustcVmArm.Vm.SampleQueries.b8Offset + b8.length = k + NativeRustcVmArm.Vm.SampleQueries.b9Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.SampleQueries.b8_next]] at hpc1
    refine .done _ (Or.inr ⟨cnt m1 - (j + 1), by omega, j + 1, r - nn, s, qs, rfl, hpc1, ?_⟩)
    exact {
      fr := hf1
      x19 := (hk .X19 (by decide) (by decide) (by decide)).trans hb.x19
      x20 := (hk .X20 (by decide) (by decide) (by decide)).trans hb.x20
      x21 := (hk .X21 (by decide) (by decide) (by decide)).trans hb.x21
      x22 := (hk .X22 (by decide) (by decide) (by decide)).trans hb.x22
      x25 := h25
      x26 := (hk .X26 (by decide) (by decide) (by decide)).trans hb.x26
      x27 := by rw [show st1.data.regs.X27 = st.data.regs.X27 from
        hk .X27 (by decide) (by decide) (by decide)]; exact hb.x27
      x28 := by rw [show st1.data.regs.X28 = st.data.regs.X28 from
        hk .X28 (by decide) (by decide) (by decide)]; exact hb.x28
      x29 := h29
      jlt := by omega
      len := hb.len
      dlt := hb.dlt
      ts := by rw [hd1]; exact hb.ts
      buf := by rw [hd1]; exact hb.buf
      model := hb.model }

end

end

end NativeRustcVmArm.Whir.SampleQueries
