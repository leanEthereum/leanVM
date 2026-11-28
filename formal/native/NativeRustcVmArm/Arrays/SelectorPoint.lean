module

public import NativeRustcVmArm.Code.Vm.SelectorPoint.Names
public import NativeRustcVmArm.Arrays.SelectorPoint.Exec

/-!
# `selector_point` on AArch64

**`selectorPoint_spec`**: rustc's `selector_point(selector, out)`, placed anywhere in the
program, meets `SelectorPointPre`/`SelectorPointPost`: `out` holds `selectorPoint selector |out|`.
No stack, no callee-saved register touched (`Base`: the arguments, X30, the saved registers kept,
memory changed only in `out`). At `|out| = 0` it returns (`b8`); from `|out| ≥ 4` the unrolled loop
(`b3`, `b4`: `UInv`) writes four entries a turn for the `4·⌊|out|/4⌋` first, then (or below `4`
at once, `b2`) the tail loop (`b6`, `b7`: `TInv`) one entry a turn. Entry `k` is bit `k` of the
selector, zero from `k = 64` on (`selBit_eval`).
-/

namespace NativeRustcVmArm.Arrays.SelectorPoint

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SelectorPoint NativeVm.Model
open NativeRustcVm (EWsAt EWAt WordAt)

public section

/-- The selector. -/
abbrev sel (m : MachineData) : Nat := m.regs.X0.toNat
/-- `out`. -/
abbrev out (m : MachineData) : BitVec 64 := m.regs.X1.toBitVec
/-- `|out|`. -/
abbrev len (m : MachineData) : Nat := m.regs.X2.toNat
/-- The entries `out` gets. -/
abbrev pt (m : MachineData) : List EW := (selectorPoint (sel m) (len m)).toList

theorem length_pt (m : MachineData) : (pt m).length = len m := by simp [selectorPoint]

theorem getElem_pt (m : MachineData) {k : Nat} (h : k < (pt m).length) :
    (pt m)[k] = EW.ofNat ((sel m >>> k) % 2) := by
  simp [selectorPoint]

theorem take_pt_succ (m : MachineData) {j : Nat} (h : j < len m) :
    (pt m).take (j + 1) = (pt m).take j ++ [EW.ofNat ((sel m >>> j) % 2)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [length_pt]; exact h), Option.toList_some,
    getElem_pt]

/-- What every block keeps. -/
structure Base (m0 s : MachineData) : Prop where
  x0 : s.regs.X0 = m0.regs.X0
  x1 : s.regs.X1 = m0.regs.X1
  x2 : s.regs.X2 = m0.regs.X2
  x30 : s.regs.X30 = m0.regs.X30
  saved : Saved m0 s
  same : Changes m0 s selectorPointStack (out m0) (16 * len m0)

theorem Base.entry (m0 : MachineData) : Base m0 m0 :=
  ⟨rfl, rfl, rfl, rfl, Saved.refl _, fun _ _ ↦ rfl⟩

/-- A block that keeps the registers `rs ⊇ keptRegs` and writes nothing. -/
theorem Base.step [Labels] {m0 s s' : MachineData} {env : Env} {S₀ S₁ : SState} {rs : List XReg}
    (hb : Base m0 s) (hm₀ : Match env S₀ s) (hm : Match env S₁ s') (hwf : env.WF)
    (hd : s.dmem = env.mem0) (hk : keepsAll S₀ S₁ rs = true) (hrs : ∀ r ∈ keptRegs, r ∈ rs) :
    Base m0 s' ∧ (∀ r ∈ rs, s'.regs.getXReg r = s.regs.getXReg r) ∧ s'.dmem = s.dmem := by
  simp only [keepsAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.isEmpty_iff] at hk
  obtain ⟨⟨hr, hsp⟩, hmem⟩ := hk
  have e : ∀ r ∈ rs, s'.regs.getXReg r = s.regs.getXReg r := fun r hr' ↦ by
    obtain ⟨hs, he⟩ := hr r hr'
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    exact Match.reg_eq hm₀ hm hv (he.trans hv)
  have hdm : s'.dmem = s.dmem := (hm.dmem_eq hwf hmem).trans hd.symm
  refine ⟨⟨(e .X0 (hrs _ (by simp [keptRegs]))).trans hb.x0,
    (e .X1 (hrs _ (by simp [keptRegs]))).trans hb.x1, (e .X2 (hrs _ (by simp [keptRegs]))).trans hb.x2,
    (e .X30 (hrs _ (by simp [keptRegs]))).trans hb.x30,
    hb.saved.trans ⟨fun r hr ↦ e r (hrs _ (List.mem_append_left _ (mem_calleeRegs hr))),
      Match.sp_eq hm₀ hm hsp, by rw [hdm]; exact fun _ h ↦ h⟩,
    fun p hp ↦ by rw [hdm]; exact hb.same p hp⟩, e, hdm⟩

/-- A block of registers only. -/
theorem Base.regs [Labels] {m0 s s' : MachineData} {S₁ : SState} {rs : List XReg}
    (hb : Base m0 s) (hm : Match (Env.ofMachine s []) S₁ s') (hk : keepsAll regsS S₁ rs = true)
    (hrs : ∀ r ∈ keptRegs, r ∈ rs) :
    Base m0 s' ∧ (∀ r ∈ rs, s'.regs.getXReg r = s.regs.getXReg r) ∧ s'.dmem = s.dmem :=
  hb.step (match_nil _) hm (Env.wf_nil _) rfl hk hrs

/-- A block writing into region 0, inside `out`. -/
theorem Base.write [Labels] {m0 s s' : MachineData} {a : BitVec 64} {sz : Nat} {S₀ S₁ : SState}
    {rs : List XReg} (hb : Base m0 s) (hm₀ : Match (Env.ofMachine s [(a, sz)]) S₀ s)
    (hm : Match (Env.ofMachine s [(a, sz)]) S₁ s') (hwf : (Env.ofMachine s [(a, sz)]).WF)
    (hk : keepsAll S₀ { S₁ with mem := [] } rs = true) (hrs : ∀ r ∈ keptRegs, r ∈ rs)
    (hw : ∀ w ∈ S₁.mem, w.r = 0 ∧ w.off + w.n ≤ sz)
    (hin : ∀ p, InRange a sz p → InRange (out m0) (16 * len m0) p) :
    Base m0 s' ∧ (∀ r ∈ rs, s'.regs.getXReg r = s.regs.getXReg r) ∧
      (∀ p, ¬InRange a sz p → s'.dmem.get? p = s.dmem.get? p) := by
  simp only [keepsAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.isEmpty_iff] at hk
  obtain ⟨⟨hr, hsp⟩, -⟩ := hk
  have e : ∀ r ∈ rs, s'.regs.getXReg r = s.regs.getXReg r := fun r hr' ↦ by
    obtain ⟨hs, he⟩ := hr r hr'
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    exact Match.reg_eq hm₀ hm hv (he.trans hv)
  have hsame := same_of_region0 hm hwf hw
  refine ⟨⟨(e .X0 (hrs _ (by simp [keptRegs]))).trans hb.x0,
    (e .X1 (hrs _ (by simp [keptRegs]))).trans hb.x1, (e .X2 (hrs _ (by simp [keptRegs]))).trans hb.x2,
    (e .X30 (hrs _ (by simp [keptRegs]))).trans hb.x30,
    hb.saved.trans ⟨fun r hr ↦ e r (hrs _ (List.mem_append_left _ (mem_calleeRegs hr))),
      Match.sp_eq hm₀ hm hsp, hm.kept hwf⟩,
    fun p hp ↦ by rw [hsame p fun h ↦ hp (Or.inl (hin p h))]; exact hb.same p hp⟩, e, hsame⟩

/-- **An entry's low limb**: bit `k` of X0, zero when the compared index `i ≤ k` is above `63`. -/
theorem selBit_eval [Labels] {env : Env} {idx cmp : Sym} {i k : Nat} (hc : (cmp.eval env).toNat = i)
    (hk : (idx.eval env).toNat = k) (hik : i ≤ k) (h63 : i ≤ 63 → k ≤ 63) :
    (selBit idx cmp).eval env = BitVec.ofNat 64 (((env.regs .X0).toNat >>> k) % 2) := by
  simp only [selBit, Sym.eval, SBool.eval, CmpOp.apply, low_W64]
  rw [ite_bool]
  by_cases h : i ≤ 63
  · have hb : ((!(cmp.eval env).ult (BitVec.ofNat 64 63)) &&
        !((cmp.eval env) == BitVec.ofNat 64 63)) = false := by
      by_cases h' : i < 63
      · simp [BitVec.ult, hc, h']
      · have : cmp.eval env = BitVec.ofNat 64 63 := by
          apply BitVec.eq_of_toNat_eq; rw [hc]; simp; omega
        simp [this]
    rw [hb, Bool.cond_false]
    rw [bit_eval _ _ (by rw [hk]; omega), hk]
  · have hb : ((!(cmp.eval env).ult (BitVec.ofNat 64 63)) &&
        !((cmp.eval env) == BitVec.ofNat 64 63)) = true := by
      have h1 : ¬(cmp.eval env).toNat < 63 := by omega
      have h2 : cmp.eval env ≠ BitVec.ofNat 64 63 := fun e ↦ by
        have := congrArg BitVec.toNat e; rw [hc] at this; simp at this; omega
      simp [BitVec.ult, h1, h2]
    rw [hb, Bool.cond_true]
    have hx := (env.regs .X0).isLt
    have : (env.regs .X0).toNat >>> k = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [this]

/-- **An entry written**: `v`, then the zero limb, at offset `o` of region 0. -/
theorem entry_at [Labels] {st m : MachineData} {a : BitVec 64} {sz o : Nat} {S : SState} {v : Sym}
    (hm : Match (Env.ofMachine st [(a, sz)]) S m) (hle : o + 16 ≤ sz) (hw : EntryW S o v = true)
    {b : Nat} (hv : v.eval (Env.ofMachine st [(a, sz)]) = BitVec.ofNat 64 b) :
    EWAt m.dmem (a + BitVec.ofNat 64 o) (EW.ofNat b) := by
  simp only [EntryW, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hw
  rw [NativeRustcVm.ewAt_iff]
  have a0 := hm.bytesAt_write (r := 0) rfl (by omega) hw.1
  have a1 := hm.bytesAt_write (r := 0) (o := o + 8) rfl (by omega) hw.2
  simp only [hv] at a0 a1
  refine ⟨?_, ?_⟩
  · unfold WordAt
    rw [← byteOf_wordBytes]
    exact a0
  · rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add]
    unfold WordAt
    rw [← byteOf_wordBytes]
    exact a1

/-- The `n` low bits of `x` masked by `0x1ffffffffffffffc`: `4·⌊x/4⌋`. -/
theorem and_mask (n : Nat) (h : n < 2 ^ 61) : n &&& 2305843009213693948 = 4 * (n / 4) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have e1 : (2305843009213693948 : Nat) = (2 ^ 59 - 1) <<< 2 := by decide
  have e2 : 4 * (n / 4) = (n >>> 2) <<< 2 := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]; omega
  rw [e1, e2, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
    Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight]
  by_cases hi : 2 ≤ i
  · rw [show 2 + (i - 2) = i by omega]
    by_cases h61 : i < 61
    · simp [hi, show i - 2 < 59 by omega]
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))]
      simp
  · simp [hi]

theorem lsl4' (x : BitVec 64) : evalUBFM x 60 59 = BitVec.ofNat 64 (16 * x.toNat) := by
  have := lsl4 x
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64] at this
  exact this

/-- `lsr #4` as rustc writes it (`ubfm #4, #63`). -/
theorem lsr4 (x : BitVec 64) : UnOp.apply (.ubfm 4 63) .W64 x = BitVec.ofNat 64 (x.toNat / 16) := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  apply BitVec.eq_of_toNat_eq
  simp [evalUBFM, toNat_take', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

theorem lsr4' (x : BitVec 64) : evalUBFM x 4 63 = BitVec.ofNat 64 (x.toNat / 16) := by
  have := lsr4 x
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64] at this
  exact this


/-- One more entry of the point. -/
theorem w_succ {m0 : MachineData} {d : DataMem} {j : Nat} (hj : j < len m0)
    (hw : EWsAt d (out m0) ((pt m0).take j))
    (he : EWAt d (out m0 + BitVec.ofNat 64 (16 * j)) (EW.ofNat ((sel m0 >>> j) % 2))) :
    EWsAt d (out m0) ((pt m0).take (j + 1)) := by
  rw [take_pt_succ m0 hj, NativeRustcVm.ewsAt_append, NativeRustcVm.ewsAt_singleton]
  refine ⟨hw, ?_⟩
  rw [List.length_take, length_pt, Nat.min_eq_left (by omega)]
  exact he

/-- The prefix written before a block writing at `a` from `16 j` on is kept. -/
theorem w_keep {m0 : MachineData} {d d' : DataMem} {j : Nat} {a : BitVec 64} {sz : Nat}
    (hw : EWsAt d (out m0) ((pt m0).take j)) (hjl : j ≤ len m0)
    (hnw : (out m0).toNat + 16 * len m0 ≤ 2 ^ 64) (ha : a = out m0 + BitVec.ofNat 64 (16 * j))
    (hsz : 16 * j + sz ≤ 2 ^ 64 - (out m0).toNat) (hsz0 : 0 < sz)
    (hs : ∀ p, ¬InRange a sz p → d'.get? p = d.get? p) :
    EWsAt d' (out m0) ((pt m0).take j) := by
  refine bytesAt_congr hw fun i hi ↦ hs _ fun h ↦ ?_
  rw [length_flatMap_ewBytes, List.length_take, length_pt, Nat.min_eq_left hjl] at hi
  have hnA : NoWrap a sz := by
    unfold NoWrap; rw [ha, toNat_add_ofNat' (by omega)]; omega
  rw [inRange_iff hnA, ha, toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega)] at h
  omega

variable [Host] {k : Nat}

theorem hb (hp : Placed code k) {b : List Directive} {j : Nat} (hj : b.IsInfixAt code j)
    (hne : b ≠ []) : b.IsInfixAt Host.prog (k + j) :=
  hj.trans hp.1 hne

/-- The postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ SelectorPointPost m0 s.data

/-- **The return** `b8`. -/
theorem ret8 (hp : Placed code k) {m0 : MachineData} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SelectorPoint.b8Offset)) (hB : Base m0 s.data)
    (hw : EWsAt s.data.dmem (out m0) (pt m0)) :
    Eventually (step1 Host.exe) (Post m0) s := by
  refine exec_at (hb hp b8_in_code (by simp [b8])) run_b8 (Env.wf_nil _) hpc (match_nil _)
    fun s' hm' hpc' ↦ .done _ ?_
  obtain ⟨hB', -, hdm⟩ := hB.regs hm' (after_eq run_b8 ▸ b8_keeps) fun _ h ↦ h
  refine ⟨?_, by rw [hdm]; exact hw, hB'.same, hB'.saved⟩
  simp only [PcOk] at hpc'
  rw [hpc']
  simp only [retOf]
  rw [hB'.x30]

/-- **The tail loop's head** `.LSelectorPoint_7`, `j` entries written. -/
structure TInv (m0 : MachineData) (j : Nat) (s : MachineData) : Prop where
  base : Base m0 s
  lt : j < len m0
  x9 : s.regs.X9.toNat = j
  x8 : s.regs.X8.toBitVec = out m0 + BitVec.ofNat 64 (16 * j)
  x10 : s.regs.X10.toBitVec = out m0 + BitVec.ofNat 64 (16 * len m0)
  w : EWsAt s.dmem (out m0) ((pt m0).take j)

/-- **The tail loop** `b7`, then the return. -/
theorem tail (hp : Placed code k) {m0 : MachineData} (hpre : SelectorPointPre m0) {j : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SelectorPoint.b7Offset)) (hI : TInv m0 j s.data) :
    Eventually (step1 Host.exe) (Post m0) s := by
  refine Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SelectorPoint.b7Offset) ∧ ∃ j, len m0 - j = n ∧ TInv m0 j s.data)
    (fun n s ⟨hpc, j, hn, hI⟩ ↦ ?_) ⟨hpc, j, rfl, hI⟩
  obtain ⟨hmO, hnO⟩ := hpre
  have hnw : (out m0).toNat + 16 * len m0 ≤ 2 ^ 64 := hnO
  have aL : m0.regs.X2.toNat = len m0 := rfl
  have hlt := hI.lt
  have hB := hI.base
  let a := out m0 + BitVec.ofNat 64 (16 * j)
  have hmA : Mapped s.data.dmem a 16 := fun i hi ↦ by
    rw [NativeRustcVm.addr_add]; exact hB.saved.2.2 _ (hmO _ (by omega))
  have hnA : NoWrap a 16 := by unfold NoWrap; rw [toNat_add_ofNat' (by omega)]; omega
  have hwf := wf_one hmA hnA (m := s.data)
  have hm : Match (Env.ofMachine s.data [(a, 16)]) tailS s.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨by show s.data.regs.X8.toBitVec = a + BitVec.ofInt 64 0
          rw [hI.x8]; exact (BitVec.add_zero _).symm, trivial⟩ trivial trivial trivial
  refine exec_at (hb hp b7_in_code (by simp [b7])) run_b7 hwf hpc hm fun s' hm' hpc' ↦ ?_
  obtain ⟨fk, fw, fe, f8, f9⟩ := after_eq run_b7 ▸ b7_facts
  have hin : ∀ p, InRange a 16 p → InRange (out m0) (16 * len m0) p :=
    fun p h ↦ inRange_mono h (by omega)
  obtain ⟨hB', e, hs⟩ := hB.write hm hm' hwf fk (fun r h ↦ List.mem_cons_of_mem _ h) fw hin
  have hx9 : ((Env.ofMachine s.data [(a, 16)]).regs .X9).toNat = j := hI.x9
  have hx0 : ((Env.ofMachine s.data [(a, 16)]).regs .X0).toNat = sel m0 := by
    show (s.data.regs.X0).toBitVec.toNat = _; rw [hB.x0]; rfl
  have he := entry_at hm' (o := 0) (by decide) fe
    (selBit_eval (i := j) (k := j) hx9 hx9 (Nat.le_refl _) id)
  rw [hx0, add_ofNat_zero] at he
  have hw' : EWsAt s'.data.dmem (out m0) ((pt m0).take (j + 1)) :=
    w_succ hlt (w_keep hI.w (by omega) hnw rfl (by omega) (by decide) hs) he
  simp only [PcOk] at hpc'
  sym_simp at hpc'
  have hpc'' := pc_cond hpc'
  have hmore : (!((Env.ofMachine s.data [(a, 16)]).base 0 + BitVec.ofInt 64 16 ==
      (Env.ofMachine s.data [(a, 16)]).regs .X10)) = true ↔ j + 1 < len m0 := by
    rw [Bool.not_eq_true', beq_eq_false_iff_ne, base0, Env.ofMachine_regs]
    show a + BitVec.ofNat 64 16 ≠ s.data.regs.X10.toBitVec ↔ _
    rw [hI.x10]
    constructor
    · intro h
      by_contra h'
      exact h (by rw [NativeRustcVm.addr_add, show 16 * j + 16 = 16 * len m0 by omega])
    · intro h h'
      have := congrArg BitVec.toNat h'
      have h1 : (out m0 + BitVec.ofNat 64 (16 * j + 16)).toNat = (out m0).toNat + (16 * j + 16) :=
        toNat_add_ofNat' (by omega)
      rw [NativeRustcVm.addr_add, h1] at this
      by_cases hz : (out m0).toNat + 16 * len m0 = 2 ^ 64
      · have h2 : (out m0 + BitVec.ofNat 64 (16 * len m0)).toNat = 0 := by
          rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        omega
      · rw [toNat_add_ofNat' (by omega)] at this
        omega
  by_cases hM : j + 1 < len m0
  · refine .done _ (Or.inr ⟨len m0 - (j + 1), by omega,
      (hpc''.1 (hmore.mpr hM)).trans (hp.label (j := NativeRustcVmArm.Vm.SelectorPoint.b7Offset) NativeRustcVmArm.Vm.SelectorPoint.label_7_at), j + 1, rfl, hB', hM, ?_, ?_, ?_, hw'⟩)
    · show (s'.data.regs.getXReg .X9).toNat = _
      rw [← UInt64.toNat_toBitVec, hm'.regs .X9 _ f9]
      sym_simp
      rw [Env.ofMachine_regs, BitVec.toNat_add, BitVec.toNat_ofNat]
      show (s.data.regs.X9.toNat + _) % _ = _
      rw [hI.x9]
      omega
    · show (s'.data.regs.getXReg .X8).toBitVec = _
      rw [hm'.regs .X8 _ f8]
      show a + BitVec.ofInt 64 16 = _
      rw [show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, NativeRustcVm.addr_add]
      rfl
    · show (s'.data.regs.getXReg .X10).toBitVec = _
      rw [e .X10 (by simp)]
      exact hI.x10
  · have hpc2 := hpc''.2 (fun h ↦ hM (hmore.mp h))
    refine Eventually.mono (ret8 hp hpc2 hB' ?_) fun _ h ↦ Or.inl h
    rw [← List.take_of_length_le (l := pt m0) (i := j + 1) (by rw [length_pt]; omega)]
    exact hw'


/-- **`.LSelectorPoint_6`** (`b6`): the tail from entry `j`. -/
theorem fromL6 (hp : Placed code k) {m0 : MachineData} (hpre : SelectorPointPre m0) {j : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SelectorPoint.b6Offset)) (hB : Base m0 s.data)
    (hlt : j < len m0) (hx9 : s.data.regs.X9.toNat = j)
    (hx8 : s.data.regs.X8.toBitVec = out m0 + BitVec.ofNat 64 (16 * j))
    (hx10 : s.data.regs.X10.toBitVec = BitVec.ofNat 64 (16 * len m0))
    (hw : EWsAt s.data.dmem (out m0) ((pt m0).take j)) :
    Eventually (step1 Host.exe) (Post m0) s := by
  refine exec_at (hb hp b6_in_code (by simp [b6])) run_b6 (Env.wf_nil _) hpc (match_nil _)
    fun s' hm' hpc' ↦ ?_
  obtain ⟨fk, f10⟩ := after_eq run_b6 ▸ b6_facts
  obtain ⟨hB', e, hdm⟩ := hB.regs hm' fk fun r h ↦ List.mem_append_right _ h
  simp only [PcOk] at hpc'
  refine tail hp hpre hpc' ⟨hB', hlt, ?_, ?_, ?_, by rw [hdm]; exact hw⟩
  · show (s'.data.regs.getXReg .X9).toNat = _
    rw [e .X9 (by simp)]; exact hx9
  · show (s'.data.regs.getXReg .X8).toBitVec = _
    rw [e .X8 (by simp)]; exact hx8
  · show (s'.data.regs.getXReg .X10).toBitVec = _
    rw [hm'.regs .X10 _ f10]
    sym_simp
    show s.data.regs.X1.toBitVec + s.data.regs.X10.toBitVec = _
    rw [hB.x1, hx10]

/-- **The unrolled loop's head** `.LSelectorPoint_4`, `4·t` entries written. -/
structure UInv (m0 : MachineData) (t : Nat) (s : MachineData) : Prop where
  base : Base m0 s
  lt : 4 * t < 4 * (len m0 / 4)
  x9 : s.regs.X9.toNat = 4 * (len m0 / 4)
  x11 : s.regs.X11.toNat = 4 * t
  x12 : s.regs.X12.toNat = len m0
  x13 : s.regs.X13.toBitVec = out m0 + BitVec.ofNat 64 (64 * t + 32)
  x8 : s.regs.X8.toBitVec = out m0 + BitVec.ofNat 64 (16 * (4 * (len m0 / 4)))
  x10 : s.regs.X10.toBitVec = BitVec.ofNat 64 (16 * len m0)
  w : EWsAt s.dmem (out m0) ((pt m0).take (4 * t))

/-- **A turn of the unrolled loop** `b4`: four entries, back at the head or on to `b5`, then the
return or the tail. -/
theorem ustep (hp : Placed code k) {m0 : MachineData} (hpre : SelectorPointPre m0) {t : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SelectorPoint.b4Offset)) (hI : UInv m0 t s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ Post m0 s' ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SelectorPoint.b4Offset) ∧ UInv m0 (t + 1) s'.data)) s := by
  have hpre' := hpre
  obtain ⟨hmO, hnO⟩ := hpre
  have hnw : (out m0).toNat + 16 * len m0 ≤ 2 ^ 64 := hnO
  have aL : m0.regs.X2.toNat = len m0 := rfl
  have hlt := hI.lt
  have hB := hI.base
  let a := out m0 + BitVec.ofNat 64 (64 * t)
  have hmA : Mapped s.data.dmem a 64 := fun i hi ↦ by
    rw [NativeRustcVm.addr_add]; exact hB.saved.2.2 _ (hmO _ (by omega))
  have hnA : NoWrap a 64 := by unfold NoWrap; rw [toNat_add_ofNat' (by omega)]; omega
  have hwf := wf_one hmA hnA (m := s.data)
  have hm : Match (Env.ofMachine s.data [(a, 64)]) loopS s.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨by show s.data.regs.X13.toBitVec = a + BitVec.ofInt 64 32
          rw [hI.x13, show BitVec.ofInt 64 32 = BitVec.ofNat 64 32 from rfl, NativeRustcVm.addr_add],
       trivial⟩ trivial trivial trivial
  refine exec_at (hb hp b4_in_code (by simp [b4])) run_b4 hwf hpc hm fun s' hm' hpc' ↦ ?_
  obtain ⟨fk, fw, fe0, fe1, fe2, fe3, f11, f13⟩ := after_eq run_b4 ▸ b4_facts
  have hin : ∀ p, InRange a 64 p → InRange (out m0) (16 * len m0) p :=
    fun p h ↦ inRange_mono h (by omega)
  obtain ⟨hB', e, hs⟩ := hB.write hm hm' hwf fk (fun r h ↦ List.mem_append_right _ h) fw hin
  have hx11 : ((Env.ofMachine s.data [(a, 64)]).regs .X11).toNat = 4 * t := hI.x11
  have hx0 : ((Env.ofMachine s.data [(a, 64)]).regs .X0).toNat = sel m0 := by
    show (s.data.regs.X0).toBitVec.toNat = _; rw [hB.x0]; rfl
  have hadd : ∀ c, c ≤ 4 → ((Sym.bin .add .W64 (.reg .X11) (.lit c)).eval
      (Env.ofMachine s.data [(a, 64)])).toNat = 4 * t + c := fun c hc ↦ by
    sym_simp
    rw [BitVec.toNat_add, hx11, BitVec.toNat_ofNat]
    omega
  have h63 : ∀ c, c ≤ 3 → 4 * t ≤ 63 → 4 * t + c ≤ 63 := fun c hc h ↦ by omega
  have he0 := entry_at hm' (o := 0) (by decide) fe0
    (selBit_eval (i := 4 * t) (k := 4 * t) hx11 hx11 (Nat.le_refl _) id)
  have he1 := entry_at hm' (o := 16) (by decide) fe1
    (selBit_eval (i := 4 * t) hx11 (hadd 1 (by decide)) (by omega) (h63 1 (by decide)))
  have he2 := entry_at hm' (o := 32) (by decide) fe2
    (selBit_eval (i := 4 * t) hx11 (hadd 2 (by decide)) (by omega) (h63 2 (by decide)))
  have he3 := entry_at hm' (o := 48) (by decide) fe3
    (selBit_eval (i := 4 * t) hx11 (hadd 3 (by decide)) (by omega) (h63 3 (by decide)))
  rw [hx0, NativeRustcVm.addr_add] at he0 he1 he2 he3
  have hw' : EWsAt s'.data.dmem (out m0) ((pt m0).take (4 * (t + 1))) := by
    have w0 := w_keep (j := 4 * t) hI.w (by omega) hnw
      (by rw [show 16 * (4 * t) = 64 * t by omega]) (by omega) (by decide) hs
    rw [show 64 * t = 16 * (4 * t) by omega] at he0 he1 he2 he3
    have w1 := w_succ (by omega) w0 (by rw [show 16 * (4 * t) + 0 = 16 * (4 * t) by omega] at he0; exact he0)
    have w2 := w_succ (by omega) w1 (by rw [show 16 * (4 * t) + 16 = 16 * (4 * t + 1) by omega] at he1; exact he1)
    have w3 := w_succ (by omega) w2 (by rw [show 16 * (4 * t) + 32 = 16 * (4 * t + 1 + 1) by omega,
      show 4 * t + 2 = 4 * t + 1 + 1 by omega] at he2; exact he2)
    have w4 := w_succ (by omega) w3 (by rw [show 16 * (4 * t) + 48 = 16 * (4 * t + 1 + 1 + 1) by omega,
      show 4 * t + 3 = 4 * t + 1 + 1 + 1 by omega] at he3; exact he3)
    rw [show 4 * (t + 1) = 4 * t + 1 + 1 + 1 + 1 by omega]
    exact w4
  have eq : ∀ r ∈ [XReg.X8, .X9, .X10, .X12], s'.data.regs.getXReg r = s.data.regs.getXReg r :=
    fun r h ↦ e r (by simp at h; rcases h with rfl | rfl | rfl | rfl <;> simp)
  have hx9 : (s.data.regs.getXReg .X9).toBitVec.toNat = 4 * (len m0 / 4) := hI.x9
  simp only [PcOk] at hpc'
  sym_simp at hpc'
  have hpc'' := pc_cond hpc'
  have hmore : (!((Env.ofMachine s.data [(a, 64)]).regs .X11 + 4#64 ==
      (Env.ofMachine s.data [(a, 64)]).regs .X9)) = true ↔ 4 * (t + 1) < 4 * (len m0 / 4) := by
    rw [Bool.not_eq_true', beq_eq_false_iff_ne]
    constructor
    · intro h
      by_contra h'
      exact h (by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, hx11]
        simp only [Env.ofMachine_regs]
        rw [hx9]
        simp
        omega)
    · intro h h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_add, hx11] at this
      simp only [Env.ofMachine_regs] at this
      rw [hx9] at this
      simp at this
      omega
  by_cases hM : 4 * (t + 1) < 4 * (len m0 / 4)
  · refine .done _ (Or.inr ⟨(hpc''.1 (hmore.mpr hM)).trans (hp.label (j := NativeRustcVmArm.Vm.SelectorPoint.b4Offset) NativeRustcVmArm.Vm.SelectorPoint.label_4_at),
      hB', hM, ?_, ?_, ?_, ?_, ?_, ?_, hw'⟩)
    · show (s'.data.regs.getXReg .X9).toNat = _
      rw [eq .X9 (by simp)]; exact hI.x9
    · show (s'.data.regs.getXReg .X11).toNat = _
      rw [← UInt64.toNat_toBitVec, hm'.regs .X11 _ f11, hadd 4 (by decide)]
      omega
    · show (s'.data.regs.getXReg .X12).toNat = _
      rw [eq .X12 (by simp)]; exact hI.x12
    · show (s'.data.regs.getXReg .X13).toBitVec = _
      rw [hm'.regs .X13 _ f13]
      show a + BitVec.ofInt 64 96 = _
      rw [show BitVec.ofInt 64 96 = BitVec.ofNat 64 96 from rfl, NativeRustcVm.addr_add,
        show 64 * t + 96 = 64 * (t + 1) + 32 by omega]
    · show (s'.data.regs.getXReg .X8).toBitVec = _
      rw [eq .X8 (by simp)]; exact hI.x8
    · show (s'.data.regs.getXReg .X10).toBitVec = _
      rw [eq .X10 (by simp)]; exact hI.x10
  have hpc5 := hpc''.2 (fun h ↦ hM (hmore.mp h))
  have hq : 4 * (t + 1) = 4 * (len m0 / 4) := by omega
  refine exec_at (hb hp b5_in_code (by simp [b5])) run_b5 (Env.wf_nil _) hpc5 (match_nil _)
    fun s5 hm5 hpc6 ↦ ?_
  obtain ⟨hB5, e5, hdm5⟩ := hB'.regs hm5 (after_eq run_b5 ▸ b5_keeps) fun r h ↦ List.mem_append_right _ h
  have hx12 : (s'.data.regs.getXReg .X12).toBitVec.toNat = len m0 := by
    rw [eq .X12 (by simp)]; exact hI.x12
  have hx9' : (s'.data.regs.getXReg .X9).toBitVec.toNat = 4 * (len m0 / 4) := by
    rw [eq .X9 (by simp)]; exact hI.x9
  simp only [PcOk] at hpc6
  sym_simp at hpc6
  have hpc6' := pc_cond hpc6
  by_cases hE : len m0 = 4 * (len m0 / 4)
  · refine Eventually.mono (ret8 hp ((hpc6'.1 ?_).trans (hp.label (j := NativeRustcVmArm.Vm.SelectorPoint.b8Offset) NativeRustcVmArm.Vm.SelectorPoint.label_8_at)) hB5 ?_)
      fun _ h ↦ Or.inl h
    · show ((s'.data.regs.getXReg .X12).toBitVec == (s'.data.regs.getXReg .X9).toBitVec) = true
      rw [beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [hx12, hx9']
      exact hE
    · rw [hdm5, ← List.take_of_length_le (l := pt m0) (i := 4 * (t + 1)) (by rw [length_pt]; omega)]
      exact hw'
  · have hpc7 := hpc6'.2 (by
      show ¬((s'.data.regs.getXReg .X12).toBitVec == (s'.data.regs.getXReg .X9).toBitVec) = true
      rw [beq_iff_eq]
      intro h
      have := congrArg BitVec.toNat h
      rw [hx12, hx9'] at this
      exact hE this)
    refine Eventually.mono (fromL6 hp hpre' hpc7 hB5 (j := 4 * (len m0 / 4)) (by omega) ?_ ?_ ?_ ?_)
      fun _ h ↦ Or.inl h
    · show (s5.data.regs.getXReg .X9).toNat = _
      rw [e5 .X9 (by simp)]; exact hx9'
    · show (s5.data.regs.getXReg .X8).toBitVec = _
      rw [e5 .X8 (by simp), eq .X8 (by simp)]; exact hI.x8
    · show (s5.data.regs.getXReg .X10).toBitVec = _
      rw [e5 .X10 (by simp), eq .X10 (by simp)]; exact hI.x10
    · rw [hdm5, ← hq]; exact hw'


/-- **`selector_point` meets its contract.** -/
theorem selectorPoint_spec (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmArm.Vm.SelectorPoint.entryLabel) SelectorPointPre SelectorPointPost := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmArm.Vm.SelectorPoint.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.SelectorPoint.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.SelectorPoint.entryOffset) NativeRustcVmArm.Vm.SelectorPoint.entry_at]
  have hnw : (out m0).toNat + 16 * len m0 ≤ 2 ^ 64 := hpre.2
  have aL : m0.regs.X2.toNat = len m0 := rfl
  refine exec_then (hb hp b0_in_code (by simp [b0])) run_b0 (Env.wf_nil _) (match_nil _)
    fun s1 hm1 hpc1 ↦ ?_
  obtain ⟨hB1, e1, hdm1⟩ := (Base.entry m0).regs hm1 (after_eq run_b0 ▸ b0_keeps) fun _ h ↦ h
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  have hpc1' := pc_cond hpc1
  have hx2 : (m0.regs.getXReg .X2).toBitVec.toNat = len m0 := rfl
  by_cases hz : len m0 = 0
  · refine ret8 hp ((hpc1'.1 ?_).trans (hp.label (j := NativeRustcVmArm.Vm.SelectorPoint.b8Offset) NativeRustcVmArm.Vm.SelectorPoint.label_8_at)) hB1 ?_
    · show ((m0.regs.getXReg .X2).toBitVec == BitVec.ofNat 64 0) = true
      rw [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; rw [hx2, hz]; rfl
    · rw [List.eq_nil_of_length_eq_zero (l := pt m0) (by rw [length_pt]; exact hz)]
      exact NativeRustcVm.ewsAt_nil _ _
  have hpc2 := hpc1'.2 (by
    show ¬((m0.regs.getXReg .X2).toBitVec == BitVec.ofNat 64 0) = true
    rw [beq_iff_eq]; intro h; have := congrArg BitVec.toNat h; rw [hx2] at this; exact hz this)
  refine exec_at (hb hp b1_in_code (by simp [b1])) run_b1 (Env.wf_nil _) hpc2 (match_nil _)
    fun s2 hm2 hpc3 ↦ ?_
  obtain ⟨fk1, f8, f10⟩ := after_eq run_b1 ▸ b1_facts
  obtain ⟨hB2, e2, hdm2⟩ := hB1.regs hm2 fk1 fun _ h ↦ h
  have hs2 : (s1.data.regs.getXReg .X2).toBitVec.toNat = len m0 := by
    rw [e1 .X2 (by simp [keptRegs])]; rfl
  have hx10 : (s2.data.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 (16 * len m0) := by
    rw [hm2.regs .X10 _ f10]
    simp only [Sym.eval, lsl4, Env.ofMachine_regs]
    rw [hs2]
  have hx8 : (s2.data.regs.getXReg .X8).toBitVec.toNat = 16 * len m0 - 16 := by
    rw [hm2.regs .X8 _ f8]
    simp only [Sym.eval, lsl4, Env.ofMachine_regs, BinOp.apply, low_W64, ext_W64]
    rw [hs2, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  have hpc3' := pc_cond hpc3
  have hc8 : evalUBFM ((Env.ofMachine s1.data []).regs .X2) 60 59 - 16#64 =
      BitVec.ofNat 64 (16 * len m0 - 16) := by
    rw [lsl4', Env.ofMachine_regs, hs2]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp
    omega
  rw [hc8] at hpc3'
  by_cases h4 : 4 ≤ len m0
  · have hpc := (hpc3'.1 (by
      rw [Bool.not_eq_true']
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not, MemWidth.bits]
      omega)).trans (hp.label (j := NativeRustcVmArm.Vm.SelectorPoint.b3Offset) NativeRustcVmArm.Vm.SelectorPoint.label_3_at)
    refine exec_at (hb hp b3_in_code (by simp [b3])) run_b3 (Env.wf_nil _) hpc (match_nil _)
      fun s3 hm3 hpc4 ↦ ?_
    obtain ⟨hB3, e3, hdm3⟩ := hB2.regs hm3 (after_eq run_b3 ▸ b3_keeps) fun r h ↦ List.mem_cons_of_mem _ h
    simp only [PcOk] at hpc4
    have hq : evalUBFM ((Env.ofMachine s2.data []).regs .X8) 4 63 + 1#64 =
        BitVec.ofNat 64 (len m0) := by
      rw [lsr4', Env.ofMachine_regs, hx8]
      apply BitVec.eq_of_toNat_eq
      simp
      omega
    have hx1 : (s2.data.regs.getXReg .X1).toBitVec = out m0 := by
      rw [e2 .X1 (by simp [keptRegs])]
      show s1.data.regs.X1.toBitVec = _
      rw [hB1.x1]
    have hmask : BitVec.ofNat 64 (len m0) &&& 2305843009213693948#64 =
        BitVec.ofNat 64 (4 * (len m0 / 4)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), and_mask _ (by omega)]
      exact (Nat.mod_eq_of_lt (by omega)).symm
    have g9 := hm3.regs .X9 _ rfl
    have g11 := hm3.regs .X11 _ rfl
    have g12 := hm3.regs .X12 _ rfl
    have g13 := hm3.regs .X13 _ rfl
    have g8 := hm3.regs .X8 _ rfl
    sym_simp at g9 g11 g12 g13 g8
    rw [hq] at g9 g12 g8
    rw [hmask] at g9 g8
    rw [Env.ofMachine_regs, hx1] at g13 g8
    refine Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SelectorPoint.b4Offset) ∧ ∃ t, len m0 / 4 - t = n ∧
      UInv m0 t s.data) (fun n s ⟨hpc, t, hn, hI⟩ ↦ ?_) ⟨hpc4, 0, rfl, ?inv⟩
    case inv =>
      refine ⟨hB3, by omega, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hdm3, hdm2, hdm1]; exact NativeRustcVm.ewsAt_nil _ _⟩
      · show (s3.data.regs.getXReg .X9).toBitVec.toNat = _
        rw [g9]; simp; omega
      · show (s3.data.regs.getXReg .X11).toBitVec.toNat = _
        rw [g11]; rfl
      · show (s3.data.regs.getXReg .X12).toBitVec.toNat = _
        rw [g12]; simp
      · show (s3.data.regs.getXReg .X13).toBitVec = _
        rw [g13]
      · show (s3.data.regs.getXReg .X8).toBitVec = _
        rw [g8, shl4]
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega)]
      · show (s3.data.regs.getXReg .X10).toBitVec = _
        rw [e3 .X10 (by simp)]
        exact hx10
    refine Eventually.mono (ustep hp hpre hpc hI) fun s' h ↦ ?_
    rcases h with h | ⟨hpc', hI'⟩
    · exact Or.inl h
    · exact Or.inr ⟨len m0 / 4 - (t + 1), by have := hI'.lt; omega, hpc', t + 1, rfl, hI'⟩
  · have hpc := hpc3'.2 (by
      rw [Bool.not_eq_true', Bool.not_eq_false]
      simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq, MemWidth.bits]
      omega)
    refine exec_at (hb hp b2_in_code (by simp [b2])) run_b2 (Env.wf_nil _) hpc (match_nil _)
      fun s3 hm3 hpc4 ↦ ?_
    obtain ⟨fk2, g8, g9⟩ := after_eq run_b2 ▸ b2_facts
    obtain ⟨hB3, e3, hdm3⟩ := hB2.regs hm3 fk2 fun r h ↦ List.mem_cons_of_mem _ h
    simp only [PcOk] at hpc4
    refine fromL6 (j := 0) hp hpre (hpc4.trans (hp.label (j := NativeRustcVmArm.Vm.SelectorPoint.b6Offset) NativeRustcVmArm.Vm.SelectorPoint.label_6_at)) hB3 (by omega) ?_ ?_ ?_ ?_
    · show (s3.data.regs.getXReg .X9).toNat = 0
      rw [← UInt64.toNat_toBitVec, hm3.regs .X9 _ g9]; rfl
    · show (s3.data.regs.getXReg .X8).toBitVec = _
      rw [hm3.regs .X8 _ g8]
      show (s2.data.regs.getXReg .X1).toBitVec = _
      rw [e2 .X1 (by simp [keptRegs])]
      show s1.data.regs.X1.toBitVec = _
      rw [hB1.x1]; exact (BitVec.add_zero _).symm
    · show (s3.data.regs.getXReg .X10).toBitVec = _
      rw [e3 .X10 (by simp)]; exact hx10
    · rw [hdm3, hdm2, hdm1]; exact NativeRustcVm.ewsAt_nil _ _

end

end NativeRustcVmArm.Arrays.SelectorPoint
