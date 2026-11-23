module

public import NativeRustcVmArm.Code.Vm.FormBufAddTerm.Names
public import NativeRustcVmArm.Layout.FormBufAddTerm.Exec
public import NativeRustcVmArm.Layout.FormBufAddTerm.Lemmas
public import NativeRustcVmArm.Arrays.Common

/-!
# `FormBuf::add_term`

`b0`, `b1` read the count `n` (at most `148`) and the degree `d` of `t`. The search (`.L4`, `Head
i`) compares term `i`'s degree with `d` (`b4`), then its columns with `t`'s, one word a turn
(`.L6`, `Inner i j`: `b6`, `b7`); a mismatch goes on to the next term (`.L3`, `Next i`: `b3`). A
term with `t`'s columns gets `c` added to its coefficient (`.L8`, `b9`: `found`); past the last
term (`b10`), the term is appended (`.L11`, `b12`: `push`) if there is room, else `None`
(`b11`: `full`). The model's `addTerm` finds the same term (`addTerm_found`, `addTerm_none`).
-/

namespace NativeRustcVmArm.Layout.FormBufAddTerm

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.FormBufAddTerm
open NativeVm.Model NativeRustcVm.Layout NativeRustcVmArm.Layout.Forms
open NativeRustcVm.Transcript (off)
open NativeRustcVm (WordAt EWAt addr_add_add addr_add_zero toNat_add_ofNat)

public section

theorem ptr_zero_eval [Labels] (env : Env) (r : Nat) : (Sym.ptr r 0).eval env = env.base r := by
  simp [Sym.eval]

theorem toBitVec_toUInt64 (n : Nat) : n.toUInt64.toBitVec = BitVec.ofNat 64 n := rfl

/-- Two addresses of one range are equal iff their offsets are. -/
theorem addr_beq {b : BitVec 64} {x y : Nat} (hx' : x < 2 ^ 64) (hy' : y < 2 ^ 64) :
    (b + BitVec.ofNat 64 x == b + BitVec.ofNat 64 y) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne]
    intro he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
    have := b.isLt
    omega

/-- A register no block's run changed. -/
theorem reg_keep [Labels] {env : Env} {S₀ S₁ : SState} {m₀ m : MachineData} (hm₀ : Match env S₀ m₀)
    (hm : Match env S₁ m) (x : XReg) (h₀ : S₀.reg x = some (.reg x))
    (h : S₁.reg x = some (.reg x)) : m.regs.getXReg x = m₀.regs.getXReg x :=
  Match.reg_eq hm₀ hm h₀ h

/-- A register kept, then its value. -/
theorem tb {a b : UInt64} {c : BitVec 64} (h : a = b) (h' : b.toBitVec = c) : a.toBitVec = c :=
  h ▸ h'

theorem ofNat_beq {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x == BitVec.ofNat 64 y) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne]
    intro he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat] at this
    omega

theorem ofNat_ult {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x).ult (BitVec.ofNat 64 y) = decide (x < y) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

/-- The registers and memory `add_term` keeps until it returns. -/
structure Ctx (m0 st : MachineData) : Prop where
  saved : Saved m0 st
  dmem : st.dmem = m0.dmem
  regs : ∀ r ∈ args, st.regs.getXReg r = m0.regs.getXReg r

theorem Ctx.step [Labels] {m0 st st' : MachineData} {rs : List (BitVec 64 × Nat)} {S₀ S₁ : SState}
    (hc : Ctx m0 st) (hm₀ : Match (Env.ofMachine st rs) S₀ st)
    (hm : Match (Env.ofMachine st rs) S₁ st') (hwf : (Env.ofMachine st rs).WF)
    (hk : ok S₀ S₁ = true) : Ctx m0 st' := by
  simp only [ok, Bool.and_eq_true, List.isEmpty_iff] at hk
  obtain ⟨⟨hk, ha⟩, hmem⟩ := hk
  exact ⟨hc.saved.trans (Match.saved hm₀ hm hwf rfl hk), (hm.dmem_eq hwf hmem).trans hc.dmem,
    fun r hr ↦ (Arrays.regs_eq_of hm₀ hm args ha r hr).trans (hc.regs r hr)⟩

theorem Ctx.x0 {m0 st : MachineData} (hc : Ctx m0 st) : st.regs.X0 = m0.regs.X0 :=
  hc.regs .X0 (by simp [args])
theorem Ctx.x1 {m0 st : MachineData} (hc : Ctx m0 st) : st.regs.X1 = m0.regs.X1 :=
  hc.regs .X1 (by simp [args])
theorem Ctx.x2 {m0 st : MachineData} (hc : Ctx m0 st) : st.regs.X2 = m0.regs.X2 :=
  hc.regs .X2 (by simp [args])
theorem Ctx.x3 {m0 st : MachineData} (hc : Ctx m0 st) : st.regs.X3 = m0.regs.X3 :=
  hc.regs .X3 (by simp [args])
theorem Ctx.x30 {m0 st : MachineData} (hc : Ctx m0 st) : st.regs.X30 = m0.regs.X30 :=
  hc.regs .X30 (by simp [args])

/-- The value of a register a block's final state gives. -/
theorem reg_val [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m) {r : XReg}
    {v : Sym} (h : S.reg r = some v) : (m.regs.getXReg r).toBitVec = v.eval env :=
  hm.regs r v h

/-- The buffer. -/
abbrev bb (m0 : MachineData) : BitVec 64 := m0.regs.X0.toBitVec
/-- The term. -/
abbrev pp (m0 : MachineData) : BitVec 64 := m0.regs.X1.toBitVec
/-- The coefficient added. -/
abbrev cc (m0 : MachineData) : EW := ewArg m0.regs.X2 m0.regs.X3

/-- **The search's head** `.L4`: terms before `i` have other columns. -/
structure Head (f : FormW) (t : TermW) (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  ctx : Ctx m0 st
  lt : i < f.size
  ne : ∀ j (hj : j < i), (f[j]'(Nat.lt_trans hj lt)).cols ≠ t.cols
  x8 : st.regs.X8 = f.size.toUInt64
  x9 : st.regs.X9.toBitVec = bb m0 + BitVec.ofNat 64 (8 + 40 * f.size)
  x10 : st.regs.X10 = t.cols.size.toUInt64
  x13 : st.regs.X13.toBitVec = pp m0 + BitVec.ofNat 64 8
  x14 : st.regs.X14 = t.cols.size.toUInt64
  x11 : st.regs.X11.toBitVec = bb m0 + BitVec.ofNat 64 (8 + 40 * i)
  x15 : st.regs.X15.toBitVec = bb m0 + BitVec.ofNat 64 (8 + 40 * i)

/-- **At `.L3`**: terms up to `i` have other columns, X15 at the next. -/
structure Next (f : FormW) (t : TermW) (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  ctx : Ctx m0 st
  lt : i < f.size
  ne : ∀ j (hj : j < i + 1), (f[j]'(Nat.lt_of_lt_of_le hj lt)).cols ≠ t.cols
  x8 : st.regs.X8 = f.size.toUInt64
  x9 : st.regs.X9.toBitVec = bb m0 + BitVec.ofNat 64 (8 + 40 * f.size)
  x10 : st.regs.X10 = t.cols.size.toUInt64
  x13 : st.regs.X13.toBitVec = pp m0 + BitVec.ofNat 64 8
  x14 : st.regs.X14 = t.cols.size.toUInt64
  x15 : st.regs.X15.toBitVec = bb m0 + BitVec.ofNat 64 (8 + 40 * (i + 1))

/-- **The columns' comparison** `.L6`: term `i` has `t`'s degree, its first `j` columns are
`t`'s. -/
structure Inner (f : FormW) (t : TermW) (m0 : MachineData) (i j : Nat) (st : MachineData) :
    Prop where
  ctx : Ctx m0 st
  lt : i < f.size
  ne : ∀ j' (hj : j' < i), (f[j']'(Nat.lt_trans hj lt)).cols ≠ t.cols
  deg : (f[i]'lt).cols.size = t.cols.size
  le : j ≤ t.cols.size
  pre : ∀ j' (hj : j' < j), (f[i]'lt).cols[j']'(by rw [deg]; omega) = t.cols[j']'(by omega)
  x8 : st.regs.X8 = f.size.toUInt64
  x9 : st.regs.X9.toBitVec = bb m0 + BitVec.ofNat 64 (8 + 40 * f.size)
  x10 : st.regs.X10 = t.cols.size.toUInt64
  x13 : st.regs.X13.toBitVec = pp m0 + BitVec.ofNat 64 8
  x14 : st.regs.X14 = t.cols.size.toUInt64
  x11 : st.regs.X11.toBitVec = bb m0 + BitVec.ofNat 64 (8 + 40 * i)
  x15 : st.regs.X15.toBitVec = bb m0 + BitVec.ofNat 64 (8 + 40 * (i + 1))
  x16 : st.regs.X16.toBitVec = bb m0 + BitVec.ofNat 64 (8 + 40 * i + (8 + 8 * j))
  x18 : st.regs.X18.toBitVec = pp m0 + BitVec.ofNat 64 (8 + 8 * j)
  x17 : st.regs.X17.toNat = t.cols.size - j

/-- `add_term`'s postcondition, reached. -/
abbrev Post (f : FormW) (t : TermW) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ FormBufAddTermPost f t m0 st.data
/-- The facts of the precondition the blocks use. -/
structure Facts (f : FormW) (t : TermW) (m0 : MachineData) : Prop where
  form : FormBufAt m0.dmem (bb m0) f
  term : TermWAt m0.dmem (pp m0) t
  bm : NativeRustcVm.Mapped m0.dmem (bb m0) 5928
  bn : NativeRustcVm.NoWrap (bb m0) 5928
  pm : NativeRustcVm.Mapped m0.dmem (pp m0) 40
  pn : NativeRustcVm.NoWrap (pp m0) 40
  apart : NativeRustcVm.Apart (bb m0) 5928 (pp m0) 40

theorem Facts.of_pre {f : FormW} {t : TermW} {m0 : MachineData} (h : FormBufAddTermPre f t m0) :
    Facts f t m0 :=
  ⟨h.1, h.2.1, h.2.2.1.1, h.2.2.1.2, h.2.2.2.1.1, h.2.2.2.1.2, h.2.2.2.2⟩

theorem Facts.size_le {f : FormW} {t : TermW} {m0 : MachineData} (h : Facts f t m0) :
    f.size ≤ 148 := h.form.len_le

theorem Facts.deg_le {f : FormW} {t : TermW} {m0 : MachineData} (h : Facts f t m0) :
    t.cols.size ≤ 2 := h.term.degree_le

theorem Facts.bnat {f : FormW} {t : TermW} {m0 : MachineData} (h : Facts f t m0) :
    (bb m0).toNat + 5928 ≤ 2 ^ 64 := h.bn

theorem Facts.pnat {f : FormW} {t : TermW} {m0 : MachineData} (h : Facts f t m0) :
    (pp m0).toNat + 40 ≤ 2 ^ 64 := h.pn

/-- A sub-range of the buffer, readable in a state that kept memory. -/
theorem Facts.sub_b {f : FormW} {t : TermW} {m0 st : MachineData} (h : Facts f t m0)
    (hd : st.dmem = m0.dmem) {o n : Nat} (hon : o + n ≤ 5928) :
    NativeRustcVm.Mapped st.dmem (bb m0 + BitVec.ofNat 64 o) n ∧
      NativeRustcVm.NoWrap (bb m0 + BitVec.ofNat 64 o) n :=
  ⟨hd ▸ h.bm.sub hon, h.bn.sub hon⟩

theorem Facts.sub_p {f : FormW} {t : TermW} {m0 st : MachineData} (h : Facts f t m0)
    (hd : st.dmem = m0.dmem) {o n : Nat} (hon : o + n ≤ 40) :
    NativeRustcVm.Mapped st.dmem (pp m0 + BitVec.ofNat 64 o) n ∧
      NativeRustcVm.NoWrap (pp m0 + BitVec.ofNat 64 o) n :=
  ⟨hd ▸ h.pm.sub hon, h.pn.sub hon⟩

/-- A sub-range of the buffer and one of the term are apart. -/
theorem Facts.apart_bp {f : FormW} {t : TermW} {m0 : MachineData} (h : Facts f t m0) {o n o' n' : Nat}
    (hon : o + n ≤ 5928) (hon' : o' + n' ≤ 40) (hn : 0 < n) (hn' : 0 < n') :
    NativeRustcVm.Apart (bb m0 + BitVec.ofNat 64 o) n (pp m0 + BitVec.ofNat 64 o') n' := by
  have hb := h.bnat
  have hp := h.pnat
  have h1 := toNat_add_ofNat (a := bb m0) (i := o) (by omega)
  have h2 := toNat_add_ofNat (a := pp m0) (i := o') (by omega)
  have := h.apart
  unfold NativeRustcVm.Apart at *
  omega

/-- Term `i` of the buffer. -/
theorem Facts.termAt {f : FormW} {t : TermW} {m0 : MachineData} (h : Facts f t m0) {i : Nat}
    (hi : i < f.size) : TermWAt m0.dmem (bb m0 + BitVec.ofNat 64 (8 + 40 * i)) f[i] := by
  have := h.form.terms i hi
  rwa [term_addr] at this

variable [Host] {k : Nat}

/-! ## The ends -/
theorem pc_of {pc : Int64} {a b : Nat} (h : pc = Host.addrOf a) (e : a = b) : pc = Host.addrOf b :=
  e ▸ h

/-- **Room, a new monomial**: `b12` appends the term, the count plus one, returns `1`. -/
theorem push (hp : Placed code k) {f : FormW} {t : TermW} {m0 : MachineData} (hF : Facts f t m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FormBufAddTerm.b12Offset)) (hc : Ctx m0 st.data)
    (hlt : f.size < 148) (hne : ∀ j (hj : j < f.size), f[j].cols ≠ t.cols)
    (h8 : st.data.regs.X8 = f.size.toUInt64)
    (h9 : st.data.regs.X9.toBitVec = bb m0 + BitVec.ofNat 64 (8 + 40 * f.size))
    (h10 : st.data.regs.X10 = t.cols.size.toUInt64) :
    Eventually (step1 Host.exe) (Post f t m0) st := by
  have hb := hF.bnat
  set n := f.size with hn
  set u := bb m0 + BitVec.ofNat 64 (8 + 40 * n) with hu
  obtain ⟨hm0, hn0⟩ := hF.sub_b hc.dmem (o := 0) (n := 8) (by omega)
  obtain ⟨hm1, hn1⟩ := hF.sub_b hc.dmem (o := 8 + 40 * n) (n := 40) (by omega)
  obtain ⟨hm2, hn2⟩ := hF.sub_p hc.dmem (o := 0) (n := 40) (by omega)
  rw [addr_add_zero] at hm0 hn0 hm2 hn2
  have a01 : NativeRustcVm.Apart (bb m0) 8 u 40 := by
    have := NativeRustcVm.apart_of_le (a := bb m0) (N := 5928) (o := 0) (n := 8) (o' := 8 + 40 * n)
      (n' := 40) hF.bn (by omega) (by omega) (by omega)
    rwa [addr_add_zero] at this
  have a02 : NativeRustcVm.Apart (bb m0) 8 (pp m0) 40 := by
    have := hF.apart_bp (o := 0) (n := 8) (o' := 0) (n' := 40) (by omega) (by omega) (by omega)
      (by omega)
    rwa [addr_add_zero, addr_add_zero] at this
  have a12 : NativeRustcVm.Apart u 40 (pp m0) 40 := by
    have := hF.apart_bp (o := 8 + 40 * n) (n := 40) (o' := 0) (n' := 40) (by omega) (by omega)
      (by omega) (by omega)
    rwa [addr_add_zero] at this
  let env := Env.ofMachine st.data [(bb m0, 8), (u, 40), (pp m0, 40)]
  have hwf : env.WF := Env.wf_of ⟨⟨hm0, hn0⟩, ⟨hm1, hn1⟩, ⟨hm2, hn2⟩, trivial⟩
    (List.Pairwise.cons (by
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        exacts [a01, a02])
      (List.Pairwise.cons (by
          intro e he
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          subst he
          exact a12)
        (List.Pairwise.cons nofun .nil)))
  have hm : Match env pushS st.data :=
    match_ofMachine ⟨rfl, nofun, rfl, nofun, rfl, nofun, trivial⟩ rfl
      ⟨by show _ = (Sym.ptr 0 0).eval env; rw [ptr_zero_eval]; exact congrArg UInt64.toBitVec hc.x0,
       by show _ = (Sym.ptr 1 0).eval env; rw [ptr_zero_eval]; exact h9,
       by show _ = (Sym.ptr 2 0).eval env; rw [ptr_zero_eval]; exact congrArg UInt64.toBitVec hc.x1,
       trivial⟩
      trivial trivial trivial
  refine exec_at (infix_of b12_in_code (by simp [b12]) hp) run_b12 hwf hpc hm
    fun st' hm' hpc' ↦ .done _ ?_
  have hd : env.mem0 = m0.dmem := hc.dmem
  have hadd := addTerm_none (c := cc m0) hne
  have hsize : (FormW.addTerm f t.cols (cc m0)).size = n + 1 := by rw [hadd, Array.size_push]
  -- what `b12` wrote
  have hw : SameOutside env.mem0 st'.data.dmem fun p ↦
      InRange (bb m0 + BitVec.ofNat 64 0) 8 p ∨ InRange (bb m0 + BitVec.ofNat 64 (8 + 40 * n)) 40 p :=
    Match.sameOutside_of hm' hwf _ fun p ⟨w, hw, b', sz', hb', h1, h2⟩ ↦ by
      rcases (after_eq run_b12 ▸ b12_mem) w hw with ⟨hr, hle⟩ | ⟨hr, hle⟩
      · rw [hr] at hb'
        simp only [env, Env.ofMachine_regions] at hb'
        simp at hb'
        obtain ⟨rfl, rfl⟩ := hb'
        exact .inl (inRange_of_written (by omega) (o := 0) (k := 8) (by omega) h1 h2 (by omega)
          (by omega))
      · rw [hr] at hb'
        simp only [env, Env.ofMachine_regions] at hb'
        simp at hb'
        obtain ⟨rfl, rfl⟩ := hb'
        refine .inr ?_
        have := inRange_of_written (b := u) (sz := 40) (o := 0) (k := 40) hn1 (by omega) h1 h2
          (by omega) hle
        rwa [addr_add_zero] at this
  have hlen : WordAt st'.data.dmem (bb m0) (n + 1).toUInt64 := by
    have := Layout.Match.wordAt_write hm' (r := 0) (o := 0) rfl (by omega) (after_eq run_b12 ▸ b12_len)
    rw [addr_add_zero] at this
    convert this using 1
    apply UInt64.toBitVec_inj.mp
    sym_simp
    rw [show env.regs .X8 = n.toUInt64.toBitVec from congrArg UInt64.toBitVec h8,
      toBitVec_toUInt64, toBitVec_toUInt64, BitVec.ofNat_add]
  have hwd : ∀ {o : Nat} {v : Sym}, o + 8 ≤ 40 → (∀ i < 8, findWrite 1 (o + i) (after b12 pushS).mem = some (v, i)) →
      WordAt st'.data.dmem (u + BitVec.ofNat 64 o) (UInt64.ofBitVec (v.eval env)) := fun hle hw ↦
    Layout.Match.wordAt_write hm' (r := 1) rfl hle (after_eq run_b12 ▸ hw)
  have hT := hF.term
  have hld : ∀ {o : Nat} {w : UInt64}, WordAt m0.dmem (pp m0 + BitVec.ofNat 64 o) w →
      env.load 2 o 8 = w.toBitVec := fun h ↦ load_word (by rw [hd]; exact h)
  have hnew : TermWAt st'.data.dmem u ⟨t.cols, 0 + cc m0⟩ := by
    refine ⟨hT.degree_le, ?_, hT.cols_lt, fun i hi ↦ ?_, ?_⟩
    · have := hwd (o := 0) (by omega) b12_deg
      rw [addr_add_zero] at this
      convert this using 1
      apply UInt64.toBitVec_inj.mp
      exact (congrArg UInt64.toBitVec h10).symm
    · have hd2 := hT.degree_le
      have hi' : i < t.cols.size := hi
      simp only [off]
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · have := hwd (o := 8) (by omega) b12_c0
        convert this using 1
        apply UInt64.toBitVec_inj.mp
        exact (hld (hT.cols 0 hi)).symm
      · have := hwd (o := 16) (by omega) b12_c1
        convert this using 1
        apply UInt64.toBitVec_inj.mp
        exact (hld (hT.cols 1 hi)).symm
    · rw [Forms.zero_add]
      simp only [off]
      rw [NativeRustcVm.ewAt_iff]
      refine ⟨?_, ?_⟩
      · have := hwd (o := 24) (by omega) b12_lo
        have e : UInt64.ofBitVec ((Sym.reg .X2).eval env) = (cc m0).c0 := hc.x2
        rw [e] at this
        exact this
      · have := hwd (o := 32) (by omega) b12_hi
        have e : UInt64.ofBitVec ((Sym.reg .X3).eval env) = (cc m0).c1 := hc.x3
        rw [e] at this
        rw [addr_add_add]
        exact this
  refine ⟨?_, ⟨?_, ?_, ?_⟩⟩
  · simp only [PcOk] at hpc'
    exact hpc'.trans (retOf_of_x30 hm' rfl (congrArg UInt64.toBitVec hc.x30))
  · have hle : (FormW.addTerm f t.cols (cc m0)).size ≤ formCap := by
      rw [hsize]; unfold formCap; omega
    simp only [hle, ↓reduceIte]
    rw [hadd]
    refine ⟨UInt64.toBitVec_inj.mp ((reg_val hm' (r := .X0) rfl).trans rfl), ?_⟩
    exact FormBufAt.push (hd ▸ hF.form) hlt hF.bn hlen (hd ▸ hw) hnew
  · intro p hp'
    rw [← hd]
    refine hw p fun h ↦ hp' (.inl ?_)
    show InRange (bb m0) 5928 p
    rcases h with h | h
    · exact NativeRustcVm.InRange.of_sub h hF.bn (by omega)
    · exact NativeRustcVm.InRange.of_sub h hF.bn (by omega)
  · exact hc.saved.trans (Match.saved hm hm' hwf rfl (after_eq run_b12 ▸ b12_keeps))

/-- **No room**: `b11` returns `0`, and the model's form has `149` terms. -/
theorem full (hp : Placed code k) {f : FormW} {t : TermW} {m0 : MachineData} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FormBufAddTerm.b11Offset)) (hc : Ctx m0 st.data) (hn : f.size = 148)
    (hne : ∀ j (hj : j < f.size), f[j].cols ≠ t.cols) :
    Eventually (step1 Host.exe) (Post f t m0) st := by
  refine exec_at (infix_of b11_in_code (by simp [b11]) hp) run_b11 (Env.wf_nil _) hpc
    (match_nil _) fun st' hm' hpc' ↦ .done _ ?_
  have hsize : (FormW.addTerm f t.cols (cc m0)).size = 149 := by
    rw [addTerm_none hne, Array.size_push, hn]
  have hdm : st'.data.dmem = st.data.dmem := hm'.dmem_eq (Env.wf_nil _) rfl
  refine ⟨?_, ⟨?_, ?_, ?_⟩⟩
  · simp only [PcOk] at hpc'
    exact hpc'.trans (retOf_of_x30 hm' rfl (congrArg UInt64.toBitVec hc.x30))
  · have hle : ¬(FormW.addTerm f t.cols (cc m0)).size ≤ formCap := by
      rw [hsize]; unfold formCap; omega
    simp only [hle, ↓reduceIte]
    exact UInt64.toBitVec_inj.mp ((reg_val hm' (r := .X0) rfl).trans rfl)
  · intro p _
    rw [hdm, hc.dmem]
  · exact hc.saved.trans (Match.saved (match_nil _) hm' (Env.wf_nil _) rfl
      (after_eq run_b11 ▸ b11_keeps))

/-- **A term with `t`'s columns**: `b9` adds `c` to its coefficient, returns `1`. -/
theorem found (hp : Placed code k) {f : FormW} {t : TermW} {m0 : MachineData} (hF : Facts f t m0)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FormBufAddTerm.b9Offset)) (hc : Ctx m0 st.data) {i : Nat}
    (hi : i < f.size) (heq : f[i].cols = t.cols) (hne : ∀ j (hj : j < i), f[j].cols ≠ t.cols)
    (h11 : st.data.regs.X11.toBitVec = bb m0 + BitVec.ofNat 64 (8 + 40 * i)) :
    Eventually (step1 Host.exe) (Post f t m0) st := by
  have hb := hF.bnat
  have hn := hF.size_le
  set u := bb m0 + BitVec.ofNat 64 (8 + 40 * i) with hu
  obtain ⟨hmu, hnu⟩ := hF.sub_b hc.dmem (o := 8 + 40 * i) (n := 40) (by omega)
  let env := Env.ofMachine st.data [(u, 40)]
  have hwf : env.WF := Arrays.wf_one hmu hnu
  have hm : Match env foundS st.data := match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
    ⟨by show _ = (Sym.ptr 0 0).eval env; rw [ptr_zero_eval]; exact h11, trivial⟩
    trivial trivial trivial
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 hwf hpc hm
    fun st' hm' hpc' ↦ .done _ ?_
  have hd : env.mem0 = m0.dmem := hc.dmem
  have hadd := addTerm_found (c := cc m0) hi heq hne
  have hT := hF.termAt hi
  obtain ⟨hc0, hc1⟩ := NativeRustcVm.ewAt_iff.mp hT.coeff
  have l24 : env.load 0 24 8 = f[i].coeff.c0.toBitVec := load_word (by rw [hd]; exact hc0)
  have l32 : env.load 0 32 8 = f[i].coeff.c1.toBitVec := load_word (by
    rw [hd]; simp only [off] at hc1; rw [addr_add_add] at hc1; exact hc1)
  have hws : SameOutside env.mem0 st'.data.dmem (InRange (u + BitVec.ofNat 64 24) 16) :=
    Match.sameOutside_of hm' hwf _ fun p ⟨w, hw, b', sz', hb', h1, h2⟩ ↦ by
      obtain ⟨hr, h3, h4⟩ := (after_eq run_b9 ▸ b9_mem) w hw
      rw [hr] at hb'
      simp only [env, Env.ofMachine_regions] at hb'
      simp at hb'
      obtain ⟨rfl, rfl⟩ := hb'
      exact inRange_of_written hnu (by omega) h1 h2 h3 h4
  have w24 := Layout.Match.wordAt_write hm' (r := 0) (o := 24) rfl (by omega)
    (after_eq run_b9 ▸ b9_w24)
  have w32 := Layout.Match.wordAt_write hm' (r := 0) (o := 32) rfl (by omega)
    (after_eq run_b9 ▸ b9_w32)
  have e24 : UInt64.ofBitVec ((Sym.bin .eor .W64 (.load 0 24 8) (.reg .X2)).eval env) =
      (f[i].coeff + cc m0).c0 := by
    apply UInt64.toBitVec_inj.mp
    sym_simp
    rw [l24]
    show _ = (f[i].coeff.c0 ^^^ m0.regs.X2).toBitVec
    rw [UInt64.toBitVec_xor, ← hc.x2]
    rfl
  have e32 : UInt64.ofBitVec ((Sym.bin .eor .W64 (.load 0 32 8) (.reg .X3)).eval env) =
      (f[i].coeff + cc m0).c1 := by
    apply UInt64.toBitVec_inj.mp
    sym_simp
    rw [l32]
    show _ = (f[i].coeff.c1 ^^^ m0.regs.X3).toBitVec
    rw [UInt64.toBitVec_xor, ← hc.x3]
    rfl
  rw [e24] at w24
  rw [e32] at w32
  have ea : u + BitVec.ofNat 64 24 = bb m0 + BitVec.ofNat 64 (8 + 40 * i + 24) := by
    rw [hu, addr_add_add]
  have hcoef : EWAt st'.data.dmem (bb m0 + BitVec.ofNat 64 (8 + 40 * i + 24))
      (f[i].coeff + cc m0) := by
    rw [← ea, NativeRustcVm.ewAt_iff]
    refine ⟨w24, ?_⟩
    rw [addr_add_add u 24 8]
    exact w32
  refine ⟨?_, ⟨?_, ?_, ?_⟩⟩
  · simp only [PcOk] at hpc'
    exact hpc'.trans (retOf_of_x30 hm' rfl (congrArg UInt64.toBitVec hc.x30))
  · have hle : (FormW.addTerm f t.cols (cc m0)).size ≤ formCap := by
      rw [hadd, Array.size_modify]; exact hF.form.len_le
    simp only [hle, ↓reduceIte]
    rw [hadd]
    refine ⟨UInt64.toBitVec_inj.mp ((reg_val hm' (r := .X0) rfl).trans rfl), ?_⟩
    exact FormBufAt.modify hi (hd ▸ hF.form) hF.bn _ rfl (ea ▸ hd ▸ hws) hcoef
  · intro p hp'
    rw [← hd]
    refine hws p fun h ↦ hp' (.inl ?_)
    show InRange (bb m0) 5928 p
    rw [ea] at h
    exact NativeRustcVm.InRange.of_sub h hF.bn (by omega)
  · exact hc.saved.trans (Match.saved hm hm' hwf rfl (after_eq run_b9 ▸ b9_keeps))

/-- What a turn of the search reaches: the end, or the head at the next term. -/
abbrev Turn (f : FormW) (t : TermW) (m0 : MachineData) (i : Nat) (st : MachineState) : Prop :=
  Post f t m0 st ∨ (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FormBufAddTerm.b4Offset) ∧ Head f t m0 (i + 1) st.data)

omit [Host] in
theorem env_nil_regs (m : MachineData) (r : XReg) :
    (Env.ofMachine m []).regs r = (m.regs.getXReg r).toBitVec := rfl

/-- **`.L3`**: past the last term, `b10` appends or fails; else the head at the next term. -/
theorem next (hp : Placed code k) {f : FormW} {t : TermW} {m0 : MachineData} (hF : Facts f t m0)
    {i : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FormBufAddTerm.b3Offset))
    (hN : Next f t m0 i st.data) : Eventually (step1 Host.exe) (Turn (k := k) f t m0 i) st := by
  have hb := hF.bnat
  have hn := hF.size_le
  have hlt := hN.lt
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) run_b3 (Env.wf_nil _) hpc (match_nil _)
    fun st1 hm1 hpc1 ↦ ?_
  have hc1 := hN.ctx.step (match_nil _) hm1 (Env.wf_nil _) (after_eq run_b3 ▸ b3_ok)
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  have e15 : (Env.ofMachine st.data []).regs .X15 = bb m0 + BitVec.ofNat 64 (8 + 40 * (i + 1)) :=
    hN.x15
  have e9 : (Env.ofMachine st.data []).regs .X9 = bb m0 + BitVec.ofNat 64 (8 + 40 * f.size) :=
    hN.x9
  rw [e15, e9, addr_beq (by omega) (by omega)] at hpc1
  obtain ⟨hpa, hpb⟩ := Arrays.pc_cond hpc1
  have r8 := Match.reg_eq (match_nil _) hm1 (r := .X8) rfl rfl
  have r9 := Match.reg_eq (match_nil _) hm1 (r := .X9) rfl rfl
  have r10 := Match.reg_eq (match_nil _) hm1 (r := .X10) rfl rfl
  have r13 := Match.reg_eq (match_nil _) hm1 (r := .X13) rfl rfl
  have r14 := Match.reg_eq (match_nil _) hm1 (r := .X14) rfl rfl
  have r15 := Match.reg_eq (match_nil _) hm1 (r := .X15) rfl rfl
  by_cases hend : i + 1 = f.size
  · have hpc2 := (hpa (by simpa using hend)).trans (hp.label (j := NativeRustcVmArm.Vm.FormBufAddTerm.b10Offset) NativeRustcVmArm.Vm.FormBufAddTerm.label_9_at)
    refine exec_at (infix_of b10_in_code (by simp [b10]) hp) run_b10 (Env.wf_nil _) hpc2
      (match_nil _) fun st2 hm2 hpc3 ↦ ?_
    have hc2 := hc1.step (match_nil _) hm2 (Env.wf_nil _) (after_eq run_b10 ▸ b10_ok)
    simp only [PcOk] at hpc3
    sym_simp at hpc3
    have e8 : (Env.ofMachine st1.data []).regs .X8 = BitVec.ofNat 64 f.size := by
      rw [env_nil_regs, r8]; exact congrArg UInt64.toBitVec hN.x8
    rw [e8, ofNat_beq (by omega) (by omega)] at hpc3
    obtain ⟨hpa', hpb'⟩ := Arrays.pc_cond hpc3
    have hne : ∀ j (hj : j < f.size), f[j].cols ≠ t.cols := fun j hj ↦ hN.ne j (by omega)
    by_cases h148 : f.size = 148
    · refine Eventually.mono (full hp (pc_of (hpb' (by simpa using h148)) rfl) hc2 h148 hne)
        fun _ h ↦ Or.inl h
    · refine Eventually.mono (push hp hF ((hpa' (by simpa using h148)).trans
        (hp.label (j := NativeRustcVmArm.Vm.FormBufAddTerm.b12Offset) NativeRustcVmArm.Vm.FormBufAddTerm.label_11_at)) hc2 (by omega) hne ?_ ?_ ?_) fun _ h ↦ Or.inl h
      · rw [show st2.data.regs.X8 = st.data.regs.X8 from
          (Match.reg_eq (match_nil _) hm2 (r := .X8) rfl rfl).trans r8]
        exact hN.x8
      · rw [show st2.data.regs.X9 = st.data.regs.X9 from
          (Match.reg_eq (match_nil _) hm2 (r := .X9) rfl rfl).trans r9]
        exact hN.x9
      · rw [show st2.data.regs.X10 = st.data.regs.X10 from
          (Match.reg_eq (match_nil _) hm2 (r := .X10) rfl rfl).trans r10]
        exact hN.x10
  · have hpc2 := pc_of (hpb (by simpa using hend)) rfl
    have h11 := hm1.regs .X11 _ rfl
    sym_simp at h11
    refine .done _ (Or.inr ⟨hpc2, hc1, by omega, fun j hj ↦ hN.ne j hj, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · rw [show st1.data.regs.X8 = _ from r8]; exact hN.x8
    · rw [show st1.data.regs.X9 = _ from r9]; exact hN.x9
    · rw [show st1.data.regs.X10 = _ from r10]; exact hN.x10
    · rw [show st1.data.regs.X13 = _ from r13]; exact hN.x13
    · rw [show st1.data.regs.X14 = _ from r14]; exact hN.x14
    · exact h11.trans e15
    · rw [show st1.data.regs.X15 = _ from r15]; exact hN.x15

omit [Host] in
theorem ofNat_sub_one {x : BitVec 64} {n : Nat} (h : x.toNat = n) (hn : 0 < n) :
    (x - 1#64).toNat = n - 1 := by
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), h]
  rfl

/-- **`.L6`**: the columns compared one word a turn; all equal: `found`; one unequal: `next`. -/
theorem inner (hp : Placed code k) {f : FormW} {t : TermW} {m0 : MachineData} (hF : Facts f t m0)
    {i : Nat} : ∀ (fuel j : Nat) {st : MachineState}, t.cols.size - j = fuel →
    st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FormBufAddTerm.b6Offset) → Inner f t m0 i j st.data →
    Eventually (step1 Host.exe) (Turn (k := k) f t m0 i) st := by
  have hb := hF.bnat
  have hpn := hF.pnat
  have hn := hF.size_le
  have hd2 := hF.deg_le
  intro fuel
  induction fuel with
  | zero =>
    intro j st hfj hpc hI
    have hlt := hI.lt
    refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 (Env.wf_nil _) hpc (match_nil _)
      fun st1 hm1 hpc1 ↦ ?_
    have hc1 := hI.ctx.step (match_nil _) hm1 (Env.wf_nil _) (after_eq run_b6 ▸ b6_ok)
    simp only [PcOk] at hpc1
    sym_simp at hpc1
    have hj : j = t.cols.size := by have := hI.le; omega
    have e17 : (Env.ofMachine st.data []).regs .X17 = 0#64 :=
      BitVec.eq_of_toNat_eq (by rw [env_nil_regs]; show st.data.regs.X17.toNat = 0; rw [hI.x17]; omega)
    rw [e17] at hpc1
    have hpc2 := (Arrays.pc_cond hpc1).1 (by decide)
    have heq : f[i].cols = t.cols := Array.ext hI.deg fun j' h1 h2 ↦ hI.pre j' (by omega)
    refine Eventually.mono (found hp hF (hpc2.trans (hp.label (j := NativeRustcVmArm.Vm.FormBufAddTerm.b9Offset) NativeRustcVmArm.Vm.FormBufAddTerm.label_8_at)) hc1 hlt heq hI.ne ?_)
      fun _ h ↦ Or.inl h
    rw [show st1.data.regs.X11 = st.data.regs.X11 from
      Match.reg_eq (match_nil _) hm1 (r := .X11) rfl rfl]
    exact hI.x11
  | succ fuel ih =>
    intro j st hfj hpc hI
    have hlt := hI.lt
    have hjd : j < t.cols.size := by omega
    refine exec_at (infix_of b6_in_code (by simp [b6]) hp) run_b6 (Env.wf_nil _) hpc (match_nil _)
      fun st1 hm1 hpc1 ↦ ?_
    have hc1 := hI.ctx.step (match_nil _) hm1 (Env.wf_nil _) (after_eq run_b6 ▸ b6_ok)
    simp only [PcOk] at hpc1
    sym_simp at hpc1
    have e17 : (Env.ofMachine st.data []).regs .X17 = BitVec.ofNat 64 (t.cols.size - j) :=
      BitVec.eq_of_toNat_eq (by
        rw [env_nil_regs, BitVec.toNat_ofNat]; show st.data.regs.X17.toNat = _; rw [hI.x17]; omega)
    rw [e17, ofNat_beq (by omega) (by omega)] at hpc1
    have hpc2 := pc_of ((Arrays.pc_cond hpc1).2 (by simp; omega)) rfl
    have r := reg_keep (match_nil _) hm1
    -- `b7`: column `j` of term `i` and of `t`
    have hT := hF.termAt hlt
    have hjt : j < f[i].cols.size := by rw [hI.deg]; exact hjd
    obtain ⟨hm0, hn0⟩ := hF.sub_b hc1.dmem (o := 8 + 40 * i + (8 + 8 * j)) (n := 8) (by omega)
    obtain ⟨hm1', hn1⟩ := hF.sub_p hc1.dmem (o := 8 + 8 * j) (n := 8) (by omega)
    have a01 := hF.apart_bp (o := 8 + 40 * i + (8 + 8 * j)) (n := 8) (o' := 8 + 8 * j) (n' := 8)
      (by omega) (by omega) (by omega) (by omega)
    let env := Env.ofMachine st1.data [(bb m0 + BitVec.ofNat 64 (8 + 40 * i + (8 + 8 * j)), 8),
      (pp m0 + BitVec.ofNat 64 (8 + 8 * j), 8)]
    have hwf : env.WF := Env.wf_of ⟨⟨hm0, hn0⟩, ⟨hm1', hn1⟩, trivial⟩
      (List.Pairwise.cons (by
          intro e he
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          subst he
          exact a01)
        (List.Pairwise.cons nofun .nil))
    have hm : Match env cmpS st1.data := match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl
      ⟨by
        show _ = (Sym.ptr 0 0).eval env
        rw [ptr_zero_eval]
        exact (congrArg UInt64.toBitVec (r .X16 rfl rfl)).trans hI.x16,
       by
        show _ = (Sym.ptr 1 0).eval env
        rw [ptr_zero_eval]
        exact (congrArg UInt64.toBitVec (r .X18 rfl rfl)).trans hI.x18, trivial⟩
      trivial trivial trivial
    refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 hwf hpc2 hm
      fun st2 hm2 hpc3 ↦ ?_
    have hc2 := hc1.step hm hm2 hwf (after_eq run_b7 ▸ b7_ok)
    have l0 : env.load 0 0 8 = BitVec.ofNat 64 (f[i].cols[j]) := load_word (by
      show WordAt st1.data.dmem _ _
      rw [hc1.dmem]
      have := hT.cols j hjt
      simp only [off] at this
      rw [addr_add_add] at this
      show WordAt m0.dmem (bb m0 + BitVec.ofNat 64 (8 + 40 * i + (8 + 8 * j)) + BitVec.ofNat 64 0) _
      rw [addr_add_zero]
      exact this)
    have l1 : env.load 1 0 8 = BitVec.ofNat 64 (t.cols[j]) := load_word (by
      show WordAt st1.data.dmem _ _
      rw [hc1.dmem]
      show WordAt m0.dmem (pp m0 + BitVec.ofNat 64 (8 + 8 * j) + BitVec.ofNat 64 0) _
      rw [addr_add_zero]
      exact hF.term.cols j hjd)
    simp only [PcOk] at hpc3
    sym_simp at hpc3
    rw [l0, l1, ofNat_beq (hT.cols_lt j hjt) (hF.term.cols_lt j hjd)] at hpc3
    obtain ⟨hpa, hpb⟩ := Arrays.pc_cond hpc3
    have r' := reg_keep hm hm2
    have k8 : st2.data.regs.X8 = st.data.regs.X8 := (r' .X8 rfl rfl).trans (r .X8 rfl rfl)
    have k9 : st2.data.regs.X9 = st.data.regs.X9 := (r' .X9 rfl rfl).trans (r .X9 rfl rfl)
    have k10 : st2.data.regs.X10 = st.data.regs.X10 := (r' .X10 rfl rfl).trans (r .X10 rfl rfl)
    have k11 : st2.data.regs.X11 = st.data.regs.X11 := (r' .X11 rfl rfl).trans (r .X11 rfl rfl)
    have k13 : st2.data.regs.X13 = st.data.regs.X13 := (r' .X13 rfl rfl).trans (r .X13 rfl rfl)
    have k14 : st2.data.regs.X14 = st.data.regs.X14 := (r' .X14 rfl rfl).trans (r .X14 rfl rfl)
    have k15 : st2.data.regs.X15 = st.data.regs.X15 := (r' .X15 rfl rfl).trans (r .X15 rfl rfl)
    by_cases hce : f[i].cols[j] = t.cols[j]
    · -- equal: on to column `j + 1`
      have hpc4 := (hpa (by simpa using hce)).trans (hp.label (j := NativeRustcVmArm.Vm.FormBufAddTerm.b6Offset) NativeRustcVmArm.Vm.FormBufAddTerm.label_6_at)
      have h16 := hm2.regs .X16 _ rfl
      have h18 := hm2.regs .X18 _ rfl
      have h17 := hm2.regs .X17 _ rfl
      sym_simp at h16 h18 h17
      refine ih (j + 1) (by omega) hpc4 ⟨hc2, hlt, hI.ne, hI.deg, by omega, fun j' hj' ↦ ?_,
        k8 ▸ hI.x8, k9 ▸ hI.x9, k10 ▸ hI.x10, k13 ▸ hI.x13, k14 ▸ hI.x14, k11 ▸ hI.x11,
        k15 ▸ hI.x15, ?_, ?_, ?_⟩
      · rcases Nat.lt_or_ge j' j with h | h
        · exact hI.pre j' h
        · obtain rfl : j' = j := by omega
          exact hce
      · show (st2.data.regs.getXReg .X16).toBitVec = _
        rw [h16]
        show bb m0 + BitVec.ofNat 64 (8 + 40 * i + (8 + 8 * j)) + BitVec.ofNat 64 8 = _
        rw [addr_add_add]
        congr 2
      · show (st2.data.regs.getXReg .X18).toBitVec = _
        rw [h18]
        show pp m0 + BitVec.ofNat 64 (8 + 8 * j) + BitVec.ofNat 64 8 = _
        rw [addr_add_add]
        congr 2
      · show (st2.data.regs.getXReg .X17).toBitVec.toNat = _
        rw [h17]
        rw [ofNat_sub_one (n := t.cols.size - j) (by
          rw [Env.ofMachine_regs, r .X17 rfl rfl]; exact hI.x17) (by omega)]
        omega
    · -- unequal: `b8` back to `.L3`
      have hpc4 := pc_of (hpb (by simpa using hce)) rfl
      refine exec_at (infix_of b8_in_code (by simp [b8]) hp) run_b8 (Env.wf_nil _) hpc4
        (match_nil _) fun st3 hm3 hpc5 ↦ ?_
      have hc3 := hc2.step (match_nil _) hm3 (Env.wf_nil _) (after_eq run_b8 ▸ b8_ok)
      simp only [PcOk] at hpc5
      have r'' := reg_keep (match_nil _) hm3
      refine next hp hF (hpc5.trans (hp.label (j := NativeRustcVmArm.Vm.FormBufAddTerm.b3Offset) NativeRustcVmArm.Vm.FormBufAddTerm.label_3_at)) ⟨hc3, hlt, fun j' hj' ↦ ?_,
        ((r'' .X8 rfl rfl).trans k8).trans hI.x8, tb ((r'' .X9 rfl rfl).trans k9) hI.x9,
        ((r'' .X10 rfl rfl).trans k10).trans hI.x10, tb ((r'' .X13 rfl rfl).trans k13) hI.x13,
        ((r'' .X14 rfl rfl).trans k14).trans hI.x14, tb ((r'' .X15 rfl rfl).trans k15) hI.x15⟩
      rcases Nat.lt_or_ge j' i with h | h
      · exact hI.ne j' h
      · obtain rfl : j' = i := by omega
        intro he
        exact hce (by simp only [he])

/-- **`.L4`**: term `i`'s degree against `d` (`b4`): unequal, `next`; equal, `b5` sets up the
columns' comparison. -/
theorem head (hp : Placed code k) {f : FormW} {t : TermW} {m0 : MachineData} (hF : Facts f t m0)
    {i : Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FormBufAddTerm.b4Offset))
    (hH : Head f t m0 i st.data) : Eventually (step1 Host.exe) (Turn (k := k) f t m0 i) st := by
  have hb := hF.bnat
  have hn := hF.size_le
  have hlt := hH.lt
  have hd2 := hF.deg_le
  have hT := hF.termAt hlt
  obtain ⟨hmu, hnu⟩ := hF.sub_b hH.ctx.dmem (o := 8 + 40 * i) (n := 8) (by omega)
  let env := Env.ofMachine st.data [(bb m0 + BitVec.ofNat 64 (8 + 40 * i), 8)]
  have hwf : env.WF := Arrays.wf_one hmu hnu
  have hm : Match env headS st.data := match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
    ⟨by show _ = (Sym.ptr 0 0).eval env; rw [ptr_zero_eval]; exact hH.x15, trivial⟩
    trivial trivial trivial
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  have hc1 := hH.ctx.step hm hm1 hwf (after_eq run_b4 ▸ b4_ok)
  have hdeg : env.load 0 0 8 = BitVec.ofNat 64 (f[i].cols.size) := load_word (by
    show WordAt st.data.dmem _ _
    rw [hH.ctx.dmem]
    show WordAt m0.dmem (bb m0 + BitVec.ofNat 64 (8 + 40 * i) + BitVec.ofNat 64 0) _
    rw [addr_add_zero]
    exact hT.degree)
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  have e10 : env.regs .X10 = BitVec.ofNat 64 t.cols.size := congrArg UInt64.toBitVec hH.x10
  rw [hdeg, e10, ofNat_beq (by have := hT.degree_le; omega) (by omega)] at hpc1
  obtain ⟨hpa, hpb⟩ := Arrays.pc_cond hpc1
  have r := reg_keep hm hm1
  have h15 : st1.data.regs.X15.toBitVec = bb m0 + BitVec.ofNat 64 (8 + 40 * (i + 1)) := by
    have := hm1.regs .X15 _ rfl
    sym_simp at this
    show (st1.data.regs.getXReg .X15).toBitVec = _
    rw [this]
    show bb m0 + BitVec.ofNat 64 (8 + 40 * i) + BitVec.ofNat 64 40 = _
    rw [addr_add_add]
    congr 2
  by_cases hdeq : f[i].cols.size = t.cols.size
  · -- `b5`, then the comparison from column `0`
    have hpc2 := pc_of (hpb (by simpa using hdeq)) rfl
    refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 (Env.wf_nil _) hpc2
      (match_nil _) fun st2 hm2 hpc3 ↦ ?_
    have hc2 := hc1.step (match_nil _) hm2 (Env.wf_nil _) (after_eq run_b5 ▸ b5_ok)
    simp only [PcOk] at hpc3
    have r' := reg_keep (match_nil _) hm2
    have h16 := hm2.regs .X16 _ rfl
    have h17 := hm2.regs .X17 _ rfl
    have h18 := hm2.regs .X18 _ rfl
    sym_simp at h16 h17 h18
    have e10' : (Env.ofMachine st1.data []).regs .X10 = BitVec.ofNat 64 t.cols.size := by
      rw [env_nil_regs, r .X10 rfl rfl]; exact congrArg UInt64.toBitVec hH.x10
    rw [Arrays.ite_bool, e10', ofNat_ult (by omega) (by omega),
      decide_eq_true (by omega : t.cols.size < 3), Bool.cond_true] at h16
    refine inner hp hF (t.cols.size - 0) 0 rfl (pc_of hpc3 rfl) ⟨hc2, hlt, hH.ne, hdeq, by omega,
      fun _ h ↦ absurd h (Nat.not_lt_zero _), ((r' .X8 rfl rfl).trans (r .X8 rfl rfl)).trans hH.x8,
      tb ((r' .X9 rfl rfl).trans (r .X9 rfl rfl)) hH.x9,
      ((r' .X10 rfl rfl).trans (r .X10 rfl rfl)).trans hH.x10,
      tb ((r' .X13 rfl rfl).trans (r .X13 rfl rfl)) hH.x13,
      ((r' .X14 rfl rfl).trans (r .X14 rfl rfl)).trans hH.x14,
      tb ((r' .X11 rfl rfl).trans (r .X11 rfl rfl)) hH.x11, tb (r' .X15 rfl rfl) h15, ?_, ?_, ?_⟩
    · show (st2.data.regs.getXReg .X16).toBitVec = _
      rw [h16, env_nil_regs, r .X11 rfl rfl]
      show st.data.regs.X11.toBitVec + BitVec.ofNat 64 8 = _
      rw [hH.x11, addr_add_add]
    · show (st2.data.regs.getXReg .X18).toBitVec = _
      rw [h18, env_nil_regs, r .X13 rfl rfl]
      exact hH.x13
    · show (st2.data.regs.getXReg .X17).toBitVec.toNat = _
      rw [h17, env_nil_regs, r .X14 rfl rfl, show st.data.regs.getXReg .X14 = _ from hH.x14]
      show t.cols.size % 2 ^ 64 = _
      omega
  · -- unequal degrees: `.L3`
    have hpc2 := (hpa (by simpa using hdeq)).trans (hp.label (j := NativeRustcVmArm.Vm.FormBufAddTerm.b3Offset) NativeRustcVmArm.Vm.FormBufAddTerm.label_3_at)
    refine next hp hF hpc2 ⟨hc1, hlt, fun j hj ↦ ?_, (r .X8 rfl rfl).trans hH.x8,
      tb (r .X9 rfl rfl) hH.x9, (r .X10 rfl rfl).trans hH.x10, tb (r .X13 rfl rfl) hH.x13,
      (r .X14 rfl rfl).trans hH.x14, h15⟩
    rcases Nat.lt_or_ge j i with h | h
    · exact hH.ne j h
    · obtain rfl : j = i := by omega
      intro he
      exact hdeq (by rw [he])

omit [Host] in
/-- The end of the buffer's terms, as `b1` computes it. -/
theorem end_addr (b : BitVec 64) (n : Nat) :
    BitVec.ofNat 64 n * 40#64 + (b + BitVec.ofInt 64 8) = b + BitVec.ofNat 64 (8 + 40 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl]
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

/-- **`FormBuf::add_term`'s contract.** -/
theorem formBufAddTerm_spec (hp : Placed code k) {f : FormW} {t : TermW} :
    Spec (Labels.label NativeRustcVmArm.Vm.FormBufAddTerm.entryLabel) (FormBufAddTermPre f t) (FormBufAddTermPost f t) := by
  intro m0 hpre
  have hF := Facts.of_pre hpre
  have hb := hF.bnat
  have hn := hF.size_le
  have hd2 := hF.deg_le
  obtain ⟨hm0, hn0⟩ := hF.sub_b (st := m0) rfl (o := 0) (n := 8) (by omega)
  obtain ⟨hm2, hn2⟩ := hF.sub_p (st := m0) rfl (o := 0) (n := 40) (by omega)
  rw [addr_add_zero] at hm0 hn0 hm2 hn2
  have a02 : NativeRustcVm.Apart (bb m0) 8 (pp m0) 40 := by
    have := hF.apart_bp (o := 0) (n := 8) (o' := 0) (n' := 40) (by omega) (by omega) (by omega)
      (by omega)
    rwa [addr_add_zero, addr_add_zero] at this
  let env := Env.ofMachine m0 [(bb m0, 8), (pp m0, 40)]
  have hwf : env.WF := Env.wf_of ⟨⟨hm0, hn0⟩, ⟨hm2, hn2⟩, trivial⟩
    (List.Pairwise.cons (by
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        subst he
        exact a02)
      (List.Pairwise.cons nofun .nil))
  have hm : Match env entryS m0 := match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl
    ⟨by show _ = (Sym.ptr 0 0).eval env; rw [ptr_zero_eval]; rfl,
     by show _ = (Sym.ptr 1 0).eval env; rw [ptr_zero_eval]; rfl, trivial⟩
    trivial trivial trivial
  have hlen : env.load 0 0 8 = BitVec.ofNat 64 f.size := load_word (by
    show WordAt m0.dmem (bb m0 + BitVec.ofNat 64 0) _
    rw [addr_add_zero]
    exact hF.form.len)
  have hdeg : env.load 1 0 8 = BitVec.ofNat 64 t.cols.size := load_word (by
    show WordAt m0.dmem (pp m0 + BitVec.ofNat 64 0) _
    rw [addr_add_zero]
    exact hF.term.degree)
  have hc0 : Ctx m0 m0 := ⟨⟨fun _ _ ↦ rfl, rfl, fun _ h ↦ h⟩, rfl, fun _ _ ↦ rfl⟩
  rw [show Labels.label NativeRustcVmArm.Vm.FormBufAddTerm.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.FormBufAddTerm.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.FormBufAddTerm.entryOffset) NativeRustcVmArm.Vm.FormBufAddTerm.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf hm fun st0 hm0' hpc0 ↦ ?_
  simp only [PcOk] at hpc0
  sym_simp at hpc0
  rw [hlen, ofNat_ult (by omega) (by omega), ofNat_beq (by omega) (by omega)] at hpc0
  have hpc0' := pc_of ((Arrays.pc_cond hpc0).2 (by simp; omega)) rfl
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) (exec_after run_b0 run_b1) hwf hpc0' hm0'
    fun st1 hm1 hpc1 ↦ ?_
  have hc1 := hc0.step hm hm1 hwf (after_eq run_b1 ▸ b1_ok)
  have h8 : st1.data.regs.X8 = f.size.toUInt64 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X8 _ rfl).trans hlen)
  have h9 : st1.data.regs.X9.toBitVec = bb m0 + BitVec.ofNat 64 (8 + 40 * f.size) := by
    have := hm1.regs .X9 _ rfl
    sym_simp at this
    rw [hlen] at this
    exact this.trans (end_addr _ _)
  have h10 : st1.data.regs.X10 = t.cols.size.toUInt64 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X10 _ rfl).trans hdeg)
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  rw [hlen, ofNat_beq (by omega) (by omega)] at hpc1
  obtain ⟨hpa, hpb⟩ := Arrays.pc_cond hpc1
  by_cases hz : f.size = 0
  · exact push hp hF ((hpa (by simpa using hz)).trans (hp.label (j := NativeRustcVmArm.Vm.FormBufAddTerm.b12Offset) NativeRustcVmArm.Vm.FormBufAddTerm.label_11_at)) hc1 (by omega)
      (fun j hj ↦ absurd hj (by omega)) h8 h9 h10
  · refine exec_at (infix_of b2_in_code (by simp [b2]) hp) (exec_after run_b1 run_b2) hwf
      (pc_of (hpb (by simpa using hz)) rfl) hm1 fun st2 hm2 hpc2 ↦ ?_
    have hc2 := hc0.step hm hm2 hwf (after_eq run_b2 ▸ b2_ok)
    simp only [PcOk] at hpc2
    have hH : Head f t m0 0 st2.data := by
      have h13 := hm2.regs .X13 _ rfl
      have h14 := hm2.regs .X14 _ rfl
      have h11 := hm2.regs .X11 _ rfl
      have h15 := hm2.regs .X15 _ rfl
      have h9' := hm2.regs .X9 _ rfl
      sym_simp at h13 h14 h11 h15 h9'
      rw [Arrays.ite_bool, hdeg, ofNat_ult (by omega) (by omega),
        decide_eq_true (by omega : t.cols.size < 3), Bool.cond_true] at h13 h14
      rw [hlen] at h9'
      exact ⟨hc2, by omega, fun _ h ↦ absurd h (Nat.not_lt_zero _),
        UInt64.toBitVec_inj.mp ((hm2.regs .X8 _ rfl).trans hlen), h9'.trans (end_addr _ _),
        UInt64.toBitVec_inj.mp ((hm2.regs .X10 _ rfl).trans hdeg), h13, UInt64.toBitVec_inj.mp h14,
        h11, h15⟩
    refine Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FormBufAddTerm.b4Offset) ∧ ∃ i, f.size - i = n ∧
      Head f t m0 i st.data) (fun n st ⟨hpc, i, hn', hH⟩ ↦ ?_)
      ⟨hpc2.trans (hp.label (j := NativeRustcVmArm.Vm.FormBufAddTerm.b4Offset) NativeRustcVmArm.Vm.FormBufAddTerm.label_4_at), 0, rfl, hH⟩
    refine Eventually.mono (head hp hF hpc hH) fun st' h ↦ ?_
    rcases h with h | ⟨hpc', hH'⟩
    · exact Or.inl h
    · exact Or.inr ⟨f.size - (i + 1), by have := hH.lt; omega, hpc', i + 1, rfl, hH'⟩

end

end NativeRustcVmArm.Layout.FormBufAddTerm
