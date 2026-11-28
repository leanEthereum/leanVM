module

public import NativeRustcVmArm.Code.Vm.ColumnKappas.Names
public import NativeRustcVmArm.Layout.BuildLayout.Stores

/-!
# `build_layout`: the last height and row, then `column_kappas` (`b15`)

`b15` stores the sixth table's height (its `bit_length`, at least `9`) and row count, and calls
`column_kappas` on the frame's `kappas`, the log-sizes and the heights just stored (`kappas`): the
heights in memory are the model's (`heightsF`), and `kappas` the model's `columnKappas`.
-/

namespace NativeRustcVmArm.Layout.BuildLayout

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BuildLayout
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt addr_add_add addr_add_zero toNat_add_ofNat)
open NativeRustcVmArm.Arrays (Body calleeRegs inSlots keepsAll restores)

public section

/-- A table's height word, from its row count. -/
abbrev hgt (rows : Array Nat) (t : Nat) : UInt64 := (bitLength (rows.getD t 0 - 1)).toUInt64

/-- The words `b9` to `b14` stored. -/
abbrev wsL (lm lb : Nat) (rows : Array Nat) : List (Nat × UInt64) :=
  [(56, hgt rows 4), (104, (rows.getD 4 0).toUInt64), (48, hgt rows 3), (96, (rows.getD 3 0).toUInt64),
   (40, hgt rows 2), (88, (rows.getD 2 0).toUInt64), (32, hgt rows 1), (80, (rows.getD 1 0).toUInt64),
   (24, hgt rows 0), (72, (rows.getD 0 0).toUInt64), (0, lm.toUInt64), (8, lb.toUInt64)]

/-- The words `b9` to `b15` stored. -/
abbrev wsK (lm lb : Nat) (rows : Array Nat) : List (Nat × UInt64) :=
  (64, (max (bitLength (rows.getD 5 0 - 1)) 9).toUInt64) :: (112, (rows.getD 5 0).toUInt64) ::
    wsL lm lb rows

variable [Host] {k : Nat}

/-- The layout's bytes are off the stack. -/
theorem Facts.lay_off {bc : Array UInt64} {m0 : MachineData} (hF : Facts bc m0) {o : Nat}
    (ho : o < layoutBytes) : ¬InRange (stackBelow m0 SS) SS (ll m0 + BitVec.ofNat 64 o) :=
  Arrays.not_inRange_of_apart hF.lo hF.lr.2 (Arrays.stack_noWrap hF.stack) ho

theorem Facts.lay_toNat {bc : Array UInt64} {m0 : MachineData} (hF : Facts bc m0) {o : Nat}
    (ho : o < layoutBytes) : (ll m0 + BitVec.ofNat 64 o).toNat = (ll m0).toNat + o := by
  have := hF.lr.2
  unfold NoWrap at this
  have : layoutBytes = 3912 := rfl
  exact toNat_add_ofNat (by omega)

/-- A part of the layout is apart from the stack. -/
theorem Facts.lay_apart {bc : Array UInt64} {m0 : MachineData} (hF : Facts bc m0) {o n : Nat}
    (h : o + n ≤ layoutBytes) (hn : 0 < n) :
    Apart (ll m0 + BitVec.ofNat 64 o) n (stackBelow m0 SS) SS := by
  have e := hF.lay_toNat (o := o) (by omega)
  have := hF.lo
  unfold OffStack Apart at *
  rw [e]
  omega

omit [Host] in
/-- Height `t` of the stored words is the model's. -/
theorem hgt_eq {rows : Array Nat} (hrs : rows.size = 6) {t : Nat} (ht : t < 5) :
    hgt rows t = ((heightsF rows).getD t 0).toUInt64 := by
  rw [heightsF_getD hrs (by omega)]
  unfold floorF
  simp only [show ¬t = 5 by omega, ↓reduceIte, Nat.max_zero]
  rfl

omit [Host] in
theorem hgt5_eq {rows : Array Nat} (hrs : rows.size = 6) :
    (max (bitLength (rows.getD 5 0 - 1)) 9).toUInt64 = ((heightsF rows).getD 5 0).toUInt64 := by
  rw [heightsF_getD hrs (by omega)]
  rfl

omit [Host] in
/-- **The heights in memory**, from the stored words. -/
theorem heights_words {d : Mem 64} {a : BitVec 64} {lm lb : Nat} {rows : Array Nat}
    (hrs : rows.size = 6) (hW : Ws d a (wsK lm lb rows)) :
    WordsAt d (a + BitVec.ofNat 64 24) (natWords (heightsF rows)) := by
  refine wordsAt_natWords fun t ht ↦ ?_
  rw [heightsF_size hrs] at ht
  rw [addr_add_add, show (heightsF rows)[t] = (heightsF rows).getD t 0 by
    simp [Array.getD, ht, heightsF_size hrs]]
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [← hgt_eq hrs (by omega)]; exact hW.get (by simp)
  · rw [← hgt_eq hrs (by omega)]; exact hW.get (by simp)
  · rw [← hgt_eq hrs (by omega)]; exact hW.get (by simp)
  · rw [← hgt_eq hrs (by omega)]; exact hW.get (by simp)
  · rw [← hgt_eq hrs (by omega)]; exact hW.get (by simp)
  · rw [← hgt5_eq hrs]; exact hW.get (by simp)

omit [Host] in
theorem heights_lt {rows : Array Nat} (hrs : rows.size = 6) (hr : ∀ t < 6, rows.getD t 0 ≤ 2 ^ 30) :
    ∀ x ∈ heightsF rows, x < 2 ^ 64 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hx
  have := heights_le hrs hr (t := i) (by rw [heightsF_size hrs] at hi; exact hi)
  simp [Array.getD, hi] at this
  omega

omit [Host] in
theorem ite9 (x : BitVec 64) {inst : Decidable (((!x.ult (BitVec.ofNat 64 9)) &&
    !(x == BitVec.ofNat 64 9)) = true)} :
    UInt64.ofBitVec (@ite _ (((!x.ult (BitVec.ofNat 64 9)) && !(x == BitVec.ofNat 64 9)) = true)
      inst x (BitVec.ofNat 64 9)) = (max x.toNat 9).toUInt64 := by
  rw [Arrays.ite_bool]
  apply UInt64.toNat.inj
  by_cases h : 9 < x.toNat
  · have : ((!x.ult (BitVec.ofNat 64 9)) && !(x == BitVec.ofNat 64 9)) = true := by
      simp only [Bool.and_eq_true, Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not,
        beq_eq_false_iff_ne, ne_eq, ← BitVec.toNat_inj]
      simp; omega
    rw [this, Bool.cond_true, Nat.max_eq_left (by omega)]
    simp
  · have : ((!x.ult (BitVec.ofNat 64 9)) && !(x == BitVec.ofNat 64 9)) = false := by
      simp only [Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.ult, decide_eq_true_eq,
        beq_iff_eq, ← BitVec.toNat_inj]
      simp; omega
    rw [this, Bool.cond_false, Nat.max_eq_right (by omega)]
    rfl

/-- **`b15` and `column_kappas`.** -/
theorem kappas (hp : Placed code k)
    (hck : Spec (Labels.label NativeRustcVmArm.Vm.ColumnKappas.entryLabel) ColumnKappasPre ColumnKappasPost)
    {bc : Array UInt64} {m0 : MachineData} (hF : Facts bc m0) {lm lb : Nat} {rows : Array Nat}
    (hrs : rows.size = 6) (hr : ∀ t < 6, rows.getD t 0 ≤ 2 ^ 30)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BuildLayout.b15Offset)) (hbd : Bd m0 st.data)
    (h22 : st.data.regs.getXReg .X22 = m0.regs.X3)
    (h21 : (st.data.regs.getXReg .X21).toBitVec = ll m0 + BitVec.ofInt 64 24)
    (h19 : (st.data.regs.getXReg .X19).toNat = lm) (h20 : (st.data.regs.getXReg .X20).toNat = lb)
    (h23 : st.data.regs.getXReg .X23 = (rows.getD 5 0).toUInt64)
    (hx0 : st.data.regs.X0.toNat = bitLength (rows.getD 5 0 - 1))
    (hW : Ws st.data.dmem (ll m0) (wsL lm lb rows)) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BuildLayout.b16Offset) → Bd m0 st'.data →
      st'.data.regs.getXReg .X22 = m0.regs.X3 →
      (st'.data.regs.getXReg .X21).toBitVec = ll m0 + BitVec.ofInt 64 24 →
      Ws st'.data.dmem (ll m0) (wsK lm lb rows) →
      WordsAt st'.data.dmem (fb m0) (natWords (columnKappas lm lb (heightsF rows))) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hS := hF.stack
  have hsp := hF.sp
  obtain ⟨k15, i15, r15, w15a, w15b, m15⟩ := Arrays.after_eq run_b15 ▸ b15_facts
  have hwf := hF.wf_lay hbd
  have hm := lay_match h22 h21
  refine exec_at (infix_of b15_in_code (by simp [b15]) hp) run_b15 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  simp only [InR0, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at i15
  have hb1 : Bd m0 st1.data := Layout.Body.of_write' hbd hS hm hm1 hwf
    (fun p hp ↦ NativeRustcVm.InRange.mono hp (NativeRustcVm.NoWrap.mono hF.lr.2 (by decide)) hF.lr.2
      (Nat.le_refl _) (by unfold layoutBytes placementBytes columnCountW; omega))
    k15 i15 (by have := hF.lay_apart (o := 0) (n := 120) (by decide) (by decide); rwa [addr_add_zero] at this)
    slots_le (by decide)
  have hW1 : Ws st1.data.dmem (ll m0) (wsK lm lb rows) := by
    refine Ws.cons ?_ (Ws.cons ?_ (Ws.keep hm1 hwf (by simp) hW (by exact m15)))
    · have := Layout.Match.wordAt_write hm1 (r := 0) rfl (by omega) w15a
      convert this using 1
      simp only [Sym.eval, Env.ofMachine_regs, SBool.eval, CmpOp.apply, Sym.low_W64]
      rw [ite9]
      exact congrArg (fun x ↦ (max x 9).toUInt64) hx0.symm
    · have := Arrays.wordAt_of_write hm1 (by omega) w15b
      rwa [h23] at this
  have hr1 := Arrays.regs_eq_of hm hm1 _ r15
  -- `column_kappas`
  have hx0' : st1.data.regs.X0.toBitVec = fb m0 := by
    have := hm1.regs .X0 _ rfl
    exact this.trans hbd.sp
  have hx3 : st1.data.regs.X3.toBitVec = ll m0 + BitVec.ofNat 64 24 := by
    have := hm1.regs .X3 _ rfl
    exact this.trans rfl
  have hhw : WordsAt st1.data.dmem (ll m0 + BitVec.ofNat 64 24) (natWords (heightsF rows)) :=
    heights_words hrs hW1
  have hnat : natsOf st1.data st1.data.regs.X3 nTables = heightsF rows :=
    natsOf_of_words (by rw [hx3]; exact hhw) (heights_lt hrs hr) (heightsF_size hrs)
  have hfr := Arrays.frame_ok hS (F := 1360) (by decide)
  have hpre : ColumnKappasPre st1.data := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hx0']; exact Layout.readable_prefix ⟨hfr.1, hfr.2.1⟩ hb1.kept (by decide)
    · rw [hx3]; exact Layout.readable_sub hF.lr hb1.kept (by decide)
    · rw [hx0', hx3]
      have := apart_frame_sub hS (F := 1360) (by decide) (hF.lay_apart (o := 24) (n := 48) (by decide) (by decide))
        (o := 0) (k := kappasBytes) (by decide)
      rwa [addr_add_zero] at this
    · rw [hnat, heightsF_getD hrs (by decide)]
      have := log2Ceil_le (hr opKeccak (by decide))
      have hq : qkeccakSlotBits < 64 := by decide
      have h9 : floorF opKeccak ≤ 30 := by decide
      omega
  refine call_then hpc1 hck hpre fun st2 hpc2 hpost ↦ ?_
  obtain ⟨hwk, hch, hs2⟩ := hpost
  have hR : ∀ p, (InRange st1.data.regs.X0.toBitVec kappasBytes p ∨
      InRange (stackBelow st1.data columnKappasStack) columnKappasStack p) →
      InRange (stackBelow m0 SS) SS p ∧ ¬InRange (m0.regs.SP.toBitVec - BitVec.ofNat 64 96) 96 p := by
    intro p hp
    rcases hp with hp | hp
    · rw [hx0'] at hp; exact kap_in hS (F := 1360) (by decide) (by decide) hp
    · exact absurd hp (by unfold InRange columnKappasStack; omega)
  have hb2 : Bd m0 st2.data := Body.of_call_stack (G := 96) hb1 hch
    (fun p hp ↦ ⟨.inr (hR p hp).1, (hR p hp).2⟩) hs2 slots_top (by decide) hsp
  refine cont st2 (pc_of hpc2 rfl) hb2 ?_ ?_ ?_ ?_
  · rw [hs2.1 .X22 rfl, hr1 .X22 (by simp [cs])]; exact h22
  · rw [hs2.1 .X21 rfl, hr1 .X21 (by simp)]; exact h21
  · refine Ws.of_same hW1 fun p hp j hj ↦ hch _ fun h ↦ ?_
    have hle : p.1 + 8 ≤ 120 := (show ∀ q ∈ wsK lm lb rows, q.1 + 8 ≤ 120 by simp) p hp
    exact hF.lay_off (o := p.1 + j) (by unfold layoutBytes placementBytes columnCountW; omega)
      (hR _ h).1
  · have e : columnKappas st1.data.regs.X1.toNat st1.data.regs.X2.toNat
        (natsOf st1.data st1.data.regs.X3 nTables) = columnKappas lm lb (heightsF rows) := by
      rw [hnat, show st1.data.regs.X1 = st.data.regs.getXReg .X19 from
          UInt64.toBitVec_inj.mp (hm1.regs .X1 _ rfl),
        show st1.data.regs.X2 = st.data.regs.getXReg .X20 from
          UInt64.toBitVec_inj.mp (hm1.regs .X2 _ rfl), h19, h20]
    rw [← e, ← hx0']
    exact hwk

end

end NativeRustcVmArm.Layout.BuildLayout
