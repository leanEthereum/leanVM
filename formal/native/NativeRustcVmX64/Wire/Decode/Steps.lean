module

public import NativeRustcVmX64.Wire.Decode.Basic
public import NativeRustcVmX64.Transcript.Arith

/-!
# `decode`: the steps the run is made of (x86-64)

A call keeps the body's state where the callee writes what it may and none of the slots
(`Bod.call`); a block from `frS` ending in a call (`cblk`); the way out with `None` (`none_run`,
`b14` then the epilogue). The arithmetic: the comparisons the blocks branch on (`ult_eval`,
`eqv_eval`, `c6_eval`), `b8`'s count of the phases the decoded area has room for (`quot_ge`), the
model's phases split (`phasesM_add`).
-/

namespace NativeRustcVmX64.Wire.Decode

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeRustcVmX64.Vm.Decode
open NativeRustcVmX64.Transcript (Frame frameEnv frame_wf frame_mapped frame_noWrap Frame.of_block
  Frame.call_slots after after_eq low8_replaceLow MidOk)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off Mapped.keeps)
open NativeRustcVmX64.Wire.PhaseM (iv_of_inRange)

public section

/-! ## Arithmetic -/

theorem mulhi_toNat (a b : BitVec 64) :
    (BinOp.apply .mulhi .W64 a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  have ha := a.isLt
  have hb := b.isLt
  have hab : a.toNat * b.toNat < 2 ^ 128 := by
    have := Nat.mul_lt_mul'' ha hb
    simpa using this
  generalize hP : a.toNat * b.toNat = P at hab
  have hP' : ((a.toNat : Int) * (b.toNat : Int)) = (P : Int) := by rw [← hP]; push_cast; rfl
  show (ext .W64 (BitVec.ofInt 64 (((low .W64 a).unsigned * (low .W64 b).unsigned) >>> 64))).toNat = _
  rw [ext_W64, low_W64, low_W64]
  show (BitVec.ofInt 64 (((a.toNat : Int) * (b.toNat : Int)) >>> 64)).toNat = _
  rw [hP', Int.shiftRight_eq_div_pow,
    show (P : Int) / ((2 ^ 64 : Nat) : Int) = ((P / 2 ^ 64 : Nat) : Int) by omega,
    BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  omega

theorem shr1_toNat (v : BitVec 64) :
    (BinOp.apply .shr .W64 v (BitVec.ofNat 64 1)).toNat = v.toNat / 2 := by
  have hs : shiftCount .W64 (BitVec.ofNat 64 1) = 1 := by decide
  simp only [BinOp.apply, low_W64, ext_W64, hs, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, pow_one]

theorem shr15_toNat (v : BitVec 64) :
    (BinOp.apply .shr .W64 v (BitVec.ofNat 64 15)).toNat = v.toNat / 32768 := by
  have hs : shiftCount .W64 (BitVec.ofNat 64 15) = 15 := by decide
  simp only [BinOp.apply, low_W64, ext_W64, hs, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]

/-- The magic constant `b8` divides by. -/
def magic : Nat := 6019990451287497113

theorem magic_toNat : (BitVec.ofNat 64 magic).toNat = magic :=
  Nat.mod_eq_of_lt (by unfold magic; norm_num)

/-- `b8`'s quotient, by numbers. -/
theorem quot_nat {X H : Nat} (hX : 395288 ≤ X) (hm : H = X * magic / 2 ^ 64) :
    9 ≤ (H + (X - H) / 2) / 32768 + 1 := by
  have hH0 : 129000 ≤ H := by
    rw [hm, Nat.le_div_iff_mul_le (by norm_num)]
    unfold magic
    omega
  have hHX : H ≤ X := by
    rw [hm]
    exact Nat.div_le_of_le_mul (by unfold magic; omega)
  omega

theorem notAdd_toNat (a b : BitVec 64) (h : a.toNat < b.toNat) :
    (BinOp.apply .add .W64 (UnOp.apply .not .W64 a) b).toNat = b.toNat - a.toNat - 1 := by
  have hb := b.isLt
  simp only [BinOp.apply, UnOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_not]
  omega

theorem sub_toNat' (X H : BitVec 64) (h : H.toNat ≤ X.toNat) :
    (BinOp.apply .sub .W64 X H).toNat = X.toNat - H.toNat := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_sub]
  have := X.isLt
  omega

theorem add_toNat' (H E : BitVec 64) (h : H.toNat + E.toNat < 2 ^ 64) :
    (BinOp.apply .add .W64 H E).toNat = H.toNat + E.toNat := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add]
  omega

theorem add1_toNat (E : BitVec 64) (h : E.toNat < 2 ^ 63) :
    (BinOp.apply .add .W64 E (BitVec.ofNat 64 1)).toNat = E.toNat + 1 := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `b8`'s quotient, by values. -/
theorem quot_chain (X c : BitVec 64) (hc : c.toNat = magic) (hX : 395288 ≤ X.toNat) :
    9 ≤ (BinOp.apply .add .W64 (BinOp.apply .shr .W64 (BinOp.apply .add .W64
      (BinOp.apply .mulhi .W64 X c) (BinOp.apply .shr .W64 (BinOp.apply .sub .W64 X
        (BinOp.apply .mulhi .W64 X c)) (BitVec.ofNat 64 1))) (BitVec.ofNat 64 15))
      (BitVec.ofNat 64 1)).toNat := by
  have hm := mulhi_toNat X c
  rw [hc] at hm
  generalize BinOp.apply .mulhi .W64 X c = H at hm
  have hq := quot_nat (X := X.toNat) hX hm
  have hHX : H.toNat ≤ X.toNat := by
    rw [hm]
    exact Nat.div_le_of_le_mul (by unfold magic; omega)
  have hXl := X.isLt
  have e1 := sub_toNat' X H hHX
  generalize BinOp.apply .sub .W64 X H = D at e1
  have e2 := shr1_toNat D
  generalize BinOp.apply .shr .W64 D (BitVec.ofNat 64 1) = E2 at e2
  have e3 := add_toNat' H E2 (by omega)
  generalize BinOp.apply .add .W64 H E2 = E3 at e3
  have e4 := shr15_toNat E3
  generalize BinOp.apply .shr .W64 E3 (BitVec.ofNat 64 15) = E4 at e4
  have := E3.isLt
  rw [add1_toNat E4 (by omega), e4, e3, e2, e1]
  exact hq

theorem magic_lit : (BitVec.ofNat 64 6019990451287497113).toNat = magic := magic_toNat

/-- **The phases' room**, as `b8` computes it: past `8` where the area holds `8` phases. -/
theorem quot_ge [Labels] (env : Env)
    (h : (env.regs .rax).toNat + 1 + 395288 ≤ (env.regs .r14).toNat) :
    9 ≤ (quot.eval env).toNat :=
  quot_chain _ _ magic_lit (by
    show 395288 ≤ (BinOp.apply .add .W64 (UnOp.apply .not .W64 (env.regs .rax)) (env.regs .r14)).toNat
    rw [notAdd_toNat _ _ (by omega)]; omega)

theorem ult_eval (x y : BitVec 64) : CmpOp.apply .ult .W64 x y = decide (x.toNat < y.toNat) := by
  simp only [CmpOp.apply, low_W64, BitVec.ult]

theorem eqv_eval (x y : BitVec 64) : CmpOp.apply .eq .W64 x y = decide (x.toNat = y.toNat) := by
  simp only [CmpOp.apply, low_W64]
  by_cases h : x = y
  · subst h; simp
  · have h' : x.toNat ≠ y.toNat := fun e ↦ h (BitVec.eq_of_toNat_eq e)
    simp [h, h']

theorem se_eval (x : BitVec 64) :
    (BinOp.apply .or .W64 (BinOp.apply .shr .W64 x (BitVec.ofNat 64 3)) (BitVec.ofNat 64 1)).toNat =
      streamEnd x.toNat := by
  simp only [BinOp.apply, low_W64, ext_W64]
  exact NativeRustcVmX64.Transcript.streamEnd_eval x

/-- `b6`'s test, by values: the flag `b` and the tag `a`. -/
theorem c6_val (c a : BitVec 64) (b : Bool) (ha : a = 0 ∨ a = 1) :
    CmpOp.apply .eq .W8 (BinOp.apply .merge .W8
      (BinOp.apply .merge .W8 c (if b = true then BitVec.ofNat 64 1 else BitVec.ofNat 64 0))
      (BinOp.apply .and .W8
        (BinOp.apply .merge .W8 c (if b = true then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)) a))
      (BitVec.ofNat 64 1) = (b && decide (a = 1)) := by
  simp only [CmpOp.apply, BinOp.apply, low8_replaceLow, low_ext]
  cases b <;> rcases ha with rfl | rfl <;> decide

/-- `b6`'s test: the read failed or the phase count is past `8`. -/
theorem c6_eval [Labels] (env : Env) (ha : env.regs .rax = 0 ∨ env.regs .rax = 1) :
    c6.eval env = !(decide ((env.regs .rdx).toNat < 9) && decide (env.regs .rax = 1)) := by
  have hc : CmpOp.apply .ult .W64 (env.regs .rdx) (BitVec.ofNat 64 9) =
      decide ((env.regs .rdx).toNat < 9) := by
    rw [ult_eval, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num)]
  simp only [c6, SBool.eval, Sym.eval, hc]
  rw [c6_val _ _ _ ha]

theorem c6_zero [Labels] (env : Env) (h : env.regs .rax = 0) : c6.eval env = true := by
  rw [c6_eval _ (.inl h), h]
  simp only [show decide ((0 : BitVec 64) = 1) = false by decide, Bool.and_false, Bool.not_false]

theorem c6_one [Labels] (env : Env) {p : Nat} (h : env.regs .rax = 1)
    (hd : (env.regs .rdx).toNat = p) : c6.eval env = !decide (p < 9) := by
  rw [c6_eval _ (.inr h), h, hd]
  simp only [decide_true, Bool.and_true]

/-- Four regions pairwise apart, by numbers. -/
theorem disjoint4 {a1 a2 a3 a4 : BitVec 64} {n1 n2 n3 n4 : Nat}
    (h12 : a1.toNat + n1 ≤ a2.toNat ∨ a2.toNat + n2 ≤ a1.toNat)
    (h13 : a1.toNat + n1 ≤ a3.toNat ∨ a3.toNat + n3 ≤ a1.toNat)
    (h14 : a1.toNat + n1 ≤ a4.toNat ∨ a4.toNat + n4 ≤ a1.toNat)
    (h23 : a2.toNat + n2 ≤ a3.toNat ∨ a3.toNat + n3 ≤ a2.toNat)
    (h24 : a2.toNat + n2 ≤ a4.toNat ∨ a4.toNat + n4 ≤ a2.toNat)
    (h34 : a3.toNat + n3 ≤ a4.toNat ∨ a4.toNat + n4 ≤ a3.toNat) :
    NativeRustcVm.Disjoint [⟨a1, n1⟩, ⟨a2, n2⟩, ⟨a3, n3⟩, ⟨a4, n4⟩] := by
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons (fun _ h ↦ absurd h List.not_mem_nil) .nil)))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; assumption

/-- `b7`'s test: the stream's end against the area's words. -/
theorem b7_eval [Labels] (env : Env) :
    (SBool.cmp .ult .W64 (.bin .or .W64 (.bin .shr .W64 (.reg .r15) (.lit 3)) (.lit 1))
      (.reg .r14)).not.eval env =
      !decide (streamEnd (env.regs .r15).toNat < (env.regs .r14).toNat) := by
  simp only [SBool.eval, Sym.eval]
  rw [ult_eval, NativeRustcVmX64.Wire.Decode.se_eval]

/-- AL after `sete`: `1` exactly when the two words are equal. -/
theorem merge_eq_al [Labels] (env : Env) (a X Y : Sym) :
    ((Sym.bin .merge .W8 a (.ite (.cmp .eq .W64 X Y) (.lit 1) (.lit 0))).eval env).toNat % 256 =
      if (X.eval env).toNat = (Y.eval env).toNat then 1 else 0 := by
  have hm : ∀ x y : BitVec 64, (BinOp.apply .merge .W8 x y).toNat % 256 = y.toNat % 256 :=
    fun x y ↦ by
      have h := congrArg BitVec.toNat (NativeRustcVmX64.Transcript.low8_replaceLow x (low .W8 y))
      simp only [BinOp.apply]
      rw [toNat_low, toNat_low] at h
      exact h
  simp only [Sym.eval, SBool.eval]
  have he := eqv_eval (X.eval env) (Y.eval env)
  by_cases h : (X.eval env).toNat = (Y.eval env).toNat
  · rw [decide_eq_true h] at he
    simp only [he, ↓reduceIte, hm]
    simp [h]
  · rw [decide_eq_false h] at he
    simp only [he, Bool.false_eq_true, ↓reduceIte, hm]
    simp [h]

/-- `b8`'s R13, `395288` below phase `0`'s words, moved up by a phase. -/
theorem r13_eq (d r : BitVec 64) (s : Nat) (hr : r.toNat = s) :
    BinOp.apply .add .W64 (BinOp.apply .add .W64 d (BinOp.apply .mul .W64 r (BitVec.ofNat 64 8)))
      (BitVec.ofNat 64 18446744073709156336) + BitVec.ofNat 64 395288 =
      d + BitVec.ofNat 64 (8 * (s + 1)) := by
  simp only [BinOp.apply, low_W64, ext_W64]
  have hc : BitVec.ofNat 64 18446744073709156336 + BitVec.ofNat 64 395288 = BitVec.ofNat 64 8 :=
    by decide
  rw [BitVec.add_assoc, hc, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have := r.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, hr]
  omega

/-- The phases after `a + b` phases: after `a`, then `b` more. -/
theorem phasesM_add (B : List UInt8) : ∀ (a b c : Nat), phasesM B (a + b) c =
    (phasesM B a c).bind fun r ↦ (phasesM B b r.2).map fun s ↦ (r.1 ++ s.1, s.2)
  | 0, b, c => by
    rw [Nat.zero_add]
    simp only [phasesM, Option.bind_some, List.nil_append]
    cases phasesM B b c <;> rfl
  | a + 1, b, c => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [phasesM, Option.bind_eq_bind]
    cases phaseM B c with
    | none => rfl
    | some p =>
      simp only [Option.bind_some]
      rw [phasesM_add B a b p.2]
      cases phasesM B a p.2 with
      | none => rfl
      | some r =>
        simp only [Option.bind_some]
        cases phasesM B b r.2 <;> rfl

theorem phasesM_one (B : List UInt8) (c : Nat) :
    phasesM B 1 c = (phaseM B c).map fun r ↦ ([r.1], r.2) := by
  simp only [phasesM, Option.bind_eq_bind]
  cases phaseM B c <;> rfl

theorem phasesM_length (B : List UInt8) : ∀ (n c : Nat) {ps : List PhaseOut} {c' : Nat},
    phasesM B n c = some (ps, c') → ps.length = n
  | 0, c, ps, c', h => by simp only [phasesM, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; rfl
  | n + 1, c, ps, c', h => by
    simp only [phasesM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨p, c1⟩, -, ⟨qs, c2⟩, h2, he⟩ := h
    cases he
    simp [phasesM_length B n c1 h2]

/-! ## Steps -/

variable {m0 : MachineData}

section
variable [Labels]

/-- **A call** keeps the body's state where the callee changes only what the body may and none of
the slots and the return address. -/
theorem Bod.call (G : Geo m0) {d d' : MachineData} (hb : Bod m0 0 d) (hs : Saved d d')
    (hrsp : rspOf d' = rspOf d + 8#64) {R : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem R)
    (hR : ∀ q, R q → Chg m0 q ∧ (q.toNat < SP0 m0 - 48 ∨ SP0 m0 + 8 ≤ q.toNat)) :
    Bod m0 8 d' := by
  have hsp := G.sp
  have h8 := G.top
  have hnot : ∀ j, 32 ≤ j → j < 88 → ¬ R (off (stackBelow m0 80) j) := fun j hj hj' hq ↦ by
    have := (hR _ hq).2
    rw [G.fr hj'] at this
    omega
  refine ⟨Frame.call_slots hb.fr hs hrsp hso
      (fun p hp i hi ↦ hnot _ (by have := slots_lo p hp; omega) (by have := slots_lo p hp; omega))
      (fun j hj ↦ hnot _ (by omega) (by omega)),
    (hb.chg.trans hso).mono fun q hq ↦ hq.elim id fun h ↦ (hR q h).1,
    (hs.1 .rbx rfl).trans hb.rbx, (hs.1 .r15 rfl).trans hb.r15⟩

/-- The round constants, kept by the body. -/
theorem Geo.rc_keep (G : Geo m0) {d : Mem 64} (h : NativeRustcVm.SameOutside m0.dmem d (Chg m0)) :
    ∀ j < 192, d.get? (rcAddr + BitVec.ofNat 64 j) = m0.dmem.get? (rcAddr + BitVec.ofNat 64 j) :=
  fun j hj ↦ h _ fun hq ↦ by
    have hcn := G.cNw
    have hcS := G.cS
    have hcD := G.cD
    have hcW := G.cW
    unfold Chg at hq
    rw [NativeRustcVm.toNat_add_ofNat (by omega)] at hq
    omega

end

variable [Host] {k : Nat}

/-- **A block from `frS` ending in a call**, writing the call's slot only. -/
theorem cblk (hp : Placed code k) (G : Geo m0) {bj : List Directive} {j : Nat} {l : Label}
    (hb : bj.IsInfixAt code j) (hne : bj ≠ [])
    (hrun : exec bj frS = some (after bj frS, .call l))
    (hok : MidOk 80 0 slots (after bj frS) = true)
    (hw : ∀ w ∈ (after bj frS).mem, w.r = 0 ∧ w.off + w.n ≤ 8)
    (hbx : (after bj frS).reg .rbx = some (.reg .rbx))
    (h15 : (after bj frS).reg .r15 = some (.reg .r15))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + j)) (hbod : Bod m0 8 st.data)
    {R : MachineState → Prop}
    (cont : ∀ st', Bod m0 0 st'.data →
      NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
        (fun q ↦ SP0 m0 - 80 ≤ q.toNat ∧ q.toNat < SP0 m0 - 72) →
      Match (frameEnv m0 st.data 80 [] (fun _ ↦ 0) (Host.addrOf (k + j + bj.length)).toBitVec)
        (after bj frS) st'.data →
      PcOk (frameEnv m0 st.data 80 [] (fun _ ↦ 0) (Host.addrOf (k + j + bj.length)).toBitVec)
        (.call l) (Host.addrOf (k + j + bj.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hst : StackOk m0 1296 := G.st
  have hwf := frame_wf (m0 := m0) (d := st.data) (F := 80) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + j + bj.length)).toBitVec)
    ⟨Mapped.keeps (frame_mapped hst (by decide)) hbod.fr.kept, frame_noWrap hst (by decide)⟩
    (by simp) (List.pairwise_singleton _ _)
  have hm : Match (frameEnv m0 st.data 80 [] (fun _ ↦ 0) (Host.addrOf (k + j + bj.length)).toBitVec)
      frS st.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hbod.fr.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of hb hne hp) hrun hwf (fun _ _ ↦ rfl) hpc hm fun st' hm' hpc' ↦ ?_
  have hs := NativeRustcVmX64.Transcript.sameOutside_low hwf hm' (r := 0) rfl (hi := 8)
    (by omega) hw
  have hsp := G.sp
  have hS := stackBelow_toNat (m := m0) (n := 80) (by omega)
  have hs' : NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
      (fun q ↦ SP0 m0 - 80 ≤ q.toNat ∧ q.toNat < SP0 m0 - 72) := hs.mono fun q h ↦ by
    have := iv_of_inRange (by rw [hS]; have := G.top; omega) h
    rw [hS] at this
    omega
  refine cont st' ⟨Frame.of_block hbod.fr hwf hm' hok slots_le,
    (hbod.chg.trans hs').mono fun q hq ↦ hq.elim id fun h ↦ .inl (by omega),
    (hm'.regs .rbx _ hbx).trans hbod.rbx, (hm'.regs .r15 _ h15).trans hbod.r15⟩ hs' hm' hpc'

/-- **The way out with `None`**: `b14`, then the epilogue. -/
theorem none_run (hp : Placed code k) (G : Geo m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Decode.b14Offset)) (hbod : Bod m0 8 st.data) (hn : decodeM (Bs m0) = none) :
    Eventually (step1 Host.exe) (Post m0) st := by
  refine fblk hp G b14_in_code (by simp [b14]) exit_b14 nofun ok_b14.1
    (ok_b14.2.2 .rbx (by simp)) (ok_b14.2.2 .r15 (by simp)) hpc hbod fun st1 hb1 _ hm1 hpc1 ↦ ?_
  refine fin hp G (hpc1.trans rfl) hb1 (res_none hn ?_)
  unfold boolRet
  rw [show reg st1.data .rax = _ from hm1.regs .rax _ ok_b14.2.1]
  rfl

end

end NativeRustcVmX64.Wire.Decode
