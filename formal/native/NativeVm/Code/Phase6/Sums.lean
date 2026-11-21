module

public import NativeVm.Code.Phase6.Scr
public import NativeVm.Field.E
public import NativeVm.Equiv.KeccakRmfe

/-!
# Loads from the scratch, and sums

Loads of an element's words, at a constant index (`ld0`, `ld1`) or at an index `i` with `16 i` in
`rax` (`ldi0`, `ldi1`). `ssum bound term`: the sum of `term`'s values for `i` from `0` while
`i < bound`, the index in `r15`, the sum so far in `(rsi, r13)` (`ssum_spec`); `lterm o` loads the
element `o + i` (`lterm_spec`), `dterm o o'` multiplies the elements `o + i` and `o' + i`
(`dterm_spec`). `msum src n`: the sum of the elements `src + i`, `i < n`, whose bit `i` of the mask
in `rbx` is set (`msum_spec`).
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model
open NativeVm.Transcript (wd wd_add wd_zero wd_inj wdisp wdisp_toUInt64)
open NativeVm.Field (eOf eOf_inj emul emul_spec eRegs eOf_add eOf_zero)
open LeanVM.Parameters Finset

variable {s : QState} {p : UInt64} {f : Nat → EW} {P E : QState → Prop} {xs : List Stmt}

theorem eOf_toE (x : EW) : eOf x.c0 x.c1 = x.toE := rfl

theorem regs_of_eOf {a b : UInt64} {x : EW} (h : eOf a b = x.toE) : a = x.c0 ∧ b = x.c1 :=
  eOf_inj.mp h

/-! ## Loads -/

/-- The element at an index: `{rbp + rax + 8 j}`. -/
def ix (j : Nat) : Addr := { base := .rbp, idx := some (.rax, .W8), disp := wdisp j }

theorem ld0 {d : Reg64} {o : Nat} (hp : s.reg .rbp = p) (hs : Scr s.mem p f) (ho : o < scrN)
    (k : WP (blk xs) (s.setReg d (f o).c0) P E) :
    WP (blk (I (.load d (at_ .rbp (wdisp (2 * o)))) :: xs)) s P E :=
  NativeVm.Transcript.wp_load (eval_el hp _) (hs.word0 ho) k

theorem ld1 {d : Reg64} {o : Nat} (hp : s.reg .rbp = p) (hs : Scr s.mem p f) (ho : o < scrN)
    (k : WP (blk xs) (s.setReg d (f o).c1) P E) :
    WP (blk (I (.load d (at_ .rbp (wdisp (2 * o + 1)))) :: xs)) s P E :=
  NativeVm.Transcript.wp_load (eval_el hp _) (hs.word1 ho) k

theorem ldi0 {d : Reg64} {o i : Nat} (hp : s.reg .rbp = p) (hi : s.reg .rax = (8 * (2 * i)).toUInt64)
    (hs : Scr s.mem p f) (ho : o + i < scrN) (k : WP (blk xs) (s.setReg d (f (o + i)).c0) P E) :
    WP (blk (I (.load d (ix (2 * o))) :: xs)) s P E :=
  NativeVm.Transcript.wp_load (eval_idx hp hi _)
    (by rw [show 2 * i + 2 * o = 2 * (o + i) by omega]; exact hs.word0 ho) k

theorem ldi1 {d : Reg64} {o i : Nat} (hp : s.reg .rbp = p) (hi : s.reg .rax = (8 * (2 * i)).toUInt64)
    (hs : Scr s.mem p f) (ho : o + i < scrN) (k : WP (blk xs) (s.setReg d (f (o + i)).c1) P E) :
    WP (blk (I (.load d (ix (2 * o + 1))) :: xs)) s P E :=
  NativeVm.Transcript.wp_load (eval_idx hp hi _)
    (by rw [show 2 * i + (2 * o + 1) = 2 * (o + i) + 1 by omega]; exact hs.word1 ho) k

/-- `rax := 16 · r15`. -/
def idx16 : List Stmt := [I (.mov .rax .r15), I (.shli .rax 4)]

theorem idx16_spec {i : Nat} (h15 : s.reg .r15 = i.toUInt64)
    (k : WP (blk xs) ((s.setReg .rax (s.reg .r15)).setReg .rax (i.toUInt64 <<< (4 : Nat).toUInt64))
      P E) :
    WP (blk (idx16 ++ xs)) s P E := by
  refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl) ?_)
  simpa [QState.setReg_reg, h15] using k

theorem rax16 (i : Nat) : i.toUInt64 <<< (4 : Nat).toUInt64 = (8 * (2 * i)).toUInt64 :=
  shl4_toUInt64 i

/-! ## Arrays for the field kernels -/

/-- The elements `[o, o + n)` as the field kernels' array (`EArr`). -/
theorem Scr.earr {mem : UInt64 → Option UInt64} (hs : Scr mem p f) {o n : Nat} (h : o + n ≤ scrN) :
    NativeVm.Field.EArr mem (wd p (2 * o)) ((List.range n).map fun i ↦ (f (o + i)).toE) := by
  intro i hi
  rw [List.length_map, List.length_range] at hi
  rw [List.getElem_map, List.getElem_range]
  have e0 : wd p (2 * o) + (16 * i).toUInt64 = wd p (2 * (o + i)) := by
    rw [show 16 * i = 8 * (2 * i) by omega, wd_add]; congr 1; omega
  have e1 : wd p (2 * (o + i)) + 8 = wd p (2 * (o + i) + 1) := by
    rw [← wd_add]; rfl
  refine ⟨?_, ?_⟩
  · rw [e0, NativeVm.Code.EW.toE_limb0]; exact hs.word0 (by omega)
  · rw [e0, e1, NativeVm.Code.EW.toE_limb1]; exact hs.word1 (by omega)

/-! ## Sums -/

/-- The sum of `term`'s values for `r15 = 0, 1, …` while `r15 < bound`. -/
def ssum (bound : Rhs) (term : Stmt) : Stmt := blk [
  I (.movi .rsi 0), I (.movi .r13 0), I (.movi .r15 0),
  .loop (.cmp .ltu .r15 bound)
    (blk [term, I (.xor .rsi .r9), I (.xor .r13 .r10), I (.addi .r15 1)]),
  I (.mov .r9 .rsi), I (.mov .r10 .r13)]

/-- The registers `ssum` writes besides its term's. -/
abbrev sumRegs : List Reg64 := [.r9, .r10, .rsi, .r13, .r15]

theorem rf_cons {l : List Reg64} {r : Reg64} {s t : QState} (h : RegsFrame l s t) :
    RegsFrame (r :: l) s t := fun q hq ↦ h q fun h' ↦ hq (List.mem_cons_of_mem _ h')

theorem rf_app {l l' : List Reg64} {s t : QState} (h : RegsFrame l s t) :
    RegsFrame (l' ++ l) s t := fun q hq ↦ h q fun h' ↦ hq (List.mem_append_right _ h')

/-- **`ssum` sums its term.** -/
theorem ssum_spec {N : Nat} {bound : Rhs} {term : Stmt} {Lt : List Reg64} {T : Nat → LeanVM.Parameters.E}
    (hLt : Reg64.rsi ∉ Lt ∧ Reg64.r13 ∉ Lt ∧ Reg64.r15 ∉ Lt) (hN : N < 2 ^ 63)
    (hb : ∀ t, RegsFrame (sumRegs ++ Lt) s t → bound.eval t = N.toUInt64)
    (ht : ∀ i < N, ∀ t, RegsFrame (sumRegs ++ Lt) s t → t.reg .r15 = i.toUInt64 → t.mem = s.mem →
      WP term t (fun t' ↦ eOf (t'.reg .r9) (t'.reg .r10) = T i ∧ t'.mem = t.mem ∧
        RegsFrame Lt t t') E) :
    WP (ssum bound term) s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) = ∑ i ∈ range N, T i ∧
      s'.mem = s.mem ∧ RegsFrame (sumRegs ++ Lt) s s') E := by
  unfold ssum
  refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl)
    (NativeVm.Transcript.wp_reg (by rfl) ?_))
  apply WP.blk_cons
  apply WP.loop (fun t ↦ ∃ i ≤ N, t.reg .r15 = i.toUInt64 ∧
      eOf (t.reg .rsi) (t.reg .r13) = ∑ j ∈ range i, T j ∧ t.mem = s.mem ∧
      RegsFrame (sumRegs ++ Lt) s t)
    (fun t ↦ N - (t.reg .r15).toNat)
  · refine ⟨0, Nat.zero_le _, by simp [QState.setReg]; rfl, ?_, rfl, ?_⟩
    · simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, range_zero, sum_empty]
      exact eOf_zero
    · intro r hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, not_or] at hr
      simp [QState.setReg_reg, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1]
  · intro t ⟨i, _, t15, tA, tM, tR⟩ hc
    have hlt : i < N := by
      have := hb t tR
      simp only [Cond.eval, t15, this, decide_eq_true_eq] at hc
      exact (toUInt64_lt' (by omega) (by omega)).mp hc
    refine WP.blk_cons (WP.mono (ht i hlt t tR t15 tM) (fun t₁ ⟨e1, e2, e3⟩ ↦ ?_) (fun _ h ↦ h))
    have k : ∀ r ∉ Lt, t₁.reg r = t.reg r := e3
    fstep; fstep; fstep; fdone
    refine ⟨⟨i + 1, hlt, ?_, ?_, e2.trans tM, ?_⟩, ?_⟩
    · rw [k .r15 hLt.2.2, t15]; exact NativeVm.Transcript.toUInt64_succ i
    · rw [sum_range_succ, eOf_add, k .rsi hLt.1, k .r13 hLt.2.1, tA, e1]
    · intro r hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, not_or] at hr
      simp only [QState.setReg_reg, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, ↓reduceIte]
      rw [k r hr.2.2.2.2.2]
      exact tR r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])
    · rw [k .r15 hLt.2.2, t15, NativeVm.Transcript.toUInt64_succ, toNat_toUInt64' (by omega),
        toNat_toUInt64' (by omega)]
      omega
  · intro t ⟨i, hi, t15, tA, tM, tR⟩ hc
    have hge : ¬ i < N := by
      have := hb t tR
      simp only [Cond.eval, t15, this, decide_eq_false_iff_not] at hc
      exact fun h ↦ hc ((toUInt64_lt' (by omega) (by omega)).mpr h)
    obtain rfl : i = N := by omega
    fstep; fstep; fdone
    refine ⟨tA, tM, ?_⟩
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, not_or] at hr
    simp only [QState.setReg_reg, hr.1, hr.2.1, ↓reduceIte]
    exact tR r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])

/-- Load the element `o + i`, `i` in `r15`. -/
def lterm (o : Nat) : Stmt := blk (idx16 ++ [I (.load .r9 (ix (2 * o))), I (.load .r10 (ix (2 * o + 1)))])

theorem lterm_spec {o i : Nat} (hp : s.reg .rbp = p) (hs : Scr s.mem p f) (ho : o + i < scrN)
    (h15 : s.reg .r15 = i.toUInt64) :
    WP (lterm o) s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) = (f (o + i)).toE ∧ s'.mem = s.mem ∧
      RegsFrame [.rax, .r9, .r10] s s') E := by
  unfold lterm
  refine idx16_spec h15 ?_
  refine ldi0 (o := o) (i := i) (by simp [hp]) (by simp only [QState.setReg_reg, ↓reduceIte]; exact rax16 i) hs ho ?_
  refine ldi1 (o := o) (i := i) (by simp [hp]) (by simp only [QState.setReg_reg, ↓reduceIte]; exact rax16 i) (hs.congr fun _ _ ↦ rfl) ho ?_
  refine WP.blk_nil ⟨by simp; rfl, rfl, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.1, hr.2.1, hr.2.2]

/-- The product of the elements `o + i` and `o' + i`, `i` in `r15`. -/
def dterm (o o' : Nat) : Stmt := blk (idx16 ++ [I (.load .r9 (ix (2 * o))),
  I (.load .r10 (ix (2 * o + 1))), I (.load .r11 (ix (2 * o'))), I (.load .r12 (ix (2 * o' + 1))),
  emul])

/-- The registers `dterm` writes. -/
abbrev dRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12]

theorem dterm_spec {o o' i : Nat} (hp : s.reg .rbp = p) (hs : Scr s.mem p f) (ho : o + i < scrN)
    (ho' : o' + i < scrN) (h15 : s.reg .r15 = i.toUInt64) :
    WP (dterm o o') s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) = (f (o + i)).toE * (f (o' + i)).toE ∧
      s'.mem = s.mem ∧ RegsFrame dRegs s s') E := by
  unfold dterm
  refine idx16_spec h15 ?_
  refine ldi0 (o := o) (i := i) (by simp [hp]) (by simp only [QState.setReg_reg, ↓reduceIte]; exact rax16 i) hs ho ?_
  refine ldi1 (o := o) (i := i) (by simp [hp]) (by simp only [QState.setReg_reg, ↓reduceIte]; exact rax16 i) (hs.congr fun _ _ ↦ rfl) ho ?_
  refine ldi0 (o := o') (i := i) (by simp [hp]) (by simp only [QState.setReg_reg, ↓reduceIte]; exact rax16 i) (hs.congr fun _ _ ↦ rfl) ho' ?_
  refine ldi1 (o := o') (i := i) (by simp [hp]) (by simp only [QState.setReg_reg, ↓reduceIte]; exact rax16 i) (hs.congr fun _ _ ↦ rfl) ho' ?_
  refine WP.blk_cons (WP.mono (emul_spec _) (fun t ⟨e1, e2, e3⟩ ↦ WP.blk_nil ⟨?_, e2, ?_⟩)
    (fun _ h ↦ h))
  · rw [e1]; simp; rfl
  · intro r hr
    have hr' := hr
    simp only [dRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [e3 r (by simp [eRegs, hr'.1, hr'.2.1, hr'.2.2.1, hr'.2.2.2.1, hr'.2.2.2.2.1, hr'.2.2.2.2.2.1,
      hr'.2.2.2.2.2.2.1])]
    simp [hr'.1, hr'.2.2.2.2.2.1, hr'.2.2.2.2.2.2.1, hr'.2.2.2.2.2.2.2.1, hr'.2.2.2.2.2.2.2.2]

/-! ## Masked sums -/

/-- The sum of the elements `src + i`, `i < n`, whose bit `i` of `rbx` is set; the mask shifted
down a bit a pass, the index in `rcx`. -/
def msum (src n : Nat) : Stmt := blk [
  I (.movi .r9 0), I (.movi .r10 0), I (.movi .rcx 0),
  .loop (.cmp .ltu .rcx (.imm (Int64.ofNat n))) (blk [
    .ite (.test true .rbx (.imm 1)) .skip (blk [
      I (.mov .rax .rcx), I (.shli .rax 4),
      I (.load .rdx (ix (2 * src))), I (.xor .r9 .rdx), I (.load .rdx (ix (2 * src + 1))),
      I (.xor .r10 .rdx)]),
    I (.shri .rbx 1), I (.addi .rcx 1)])]

/-- The registers `msum` writes. -/
abbrev mRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .r9, .r10]

theorem testBitW_div {w : UInt64} {i : Nat} (hi : i < 64) :
    testBitW w i = decide (w.toNat / 2 ^ i % 2 = 1) := by
  rw [NativeVm.Equiv.testBitW_eq _ hi, Nat.testBit_eq_decide_div_mod_eq]

theorem toNat_shr1 (x : UInt64) : (x >>> 1).toNat = x.toNat / 2 := by
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

theorem and1_eq_zero (x : UInt64) : (x &&& 1 == 0) = decide (x.toNat % 2 = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt64.toNat_inj, UInt64.toNat_and]
  simp

/-- **`msum` sums the elements the mask selects.** -/
theorem msum_spec {src n : Nat} {mask : UInt64} (hp : s.reg .rbp = p) (hs : Scr s.mem p f)
    (hn : src + n ≤ scrN) (hn64 : n ≤ 64) (hm : s.reg .rbx = mask) :
    WP (msum src n) s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) =
        ∑ i ∈ range n, (if testBitW mask i then (f (src + i)).toE else 0) ∧ s'.mem = s.mem ∧
      RegsFrame mRegs s s') E := by
  have hN := scrN_lt
  unfold msum
  fstep; fstep; fstep
  apply WP.blk_cons
  apply WP.loop (fun t ↦ ∃ i ≤ n, t.reg .rcx = i.toUInt64 ∧ (t.reg .rbx).toNat = mask.toNat / 2 ^ i ∧
      eOf (t.reg .r9) (t.reg .r10) =
        ∑ j ∈ range i, (if testBitW mask j then (f (src + j)).toE else 0) ∧ t.mem = s.mem ∧
      t.reg .rbp = p ∧ RegsFrame mRegs s t)
    (fun t ↦ n - (t.reg .rcx).toNat)
  · refine ⟨0, Nat.zero_le _, rfl, by simp [hm], ?_, rfl, hp, ?_⟩
    · simp only [range_zero, sum_empty]; exact eOf_zero
    · intro r hr
      simp only [mRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [QState.setReg_reg, hr.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]
  · intro t ⟨i, _, tc, tb, tA, tM, tp, tR⟩ hc
    have hlt : i < n := by
      simp only [Cond.eval, tc, Rhs.eval, decide_eq_true_eq] at hc
      rw [show (Int64.ofNat n).toUInt64 = n.toUInt64 from rfl] at hc
      exact (toUInt64_lt' (by omega) (by omega)).mp hc
    have hbit := testBitW_div (w := mask) (i := i) (by omega)
    rw [← tb] at hbit
    have ts : Scr t.mem p f := hs.congr fun a _ ↦ by rw [tM]
    apply WP.blk_cons
    apply WP.ite
    by_cases hz : (t.reg .rbx).toNat % 2 = 0
    · have hc' : (Cond.test true .rbx (.imm 1)).eval t = true := by
        simp only [Cond.eval, Rhs.eval]; rw [show Int64.toUInt64 1 = 1 from rfl, and1_eq_zero]
        simp [hz]
      rw [hc']
      refine WP.skip ?_
      fstep; fstep; fdone
      refine ⟨⟨i + 1, hlt, ?_, ?_, ?_, tM, tp, ?_⟩, ?_⟩
      · rw [tc]; exact NativeVm.Transcript.toUInt64_succ i
      · rw [toNat_shr1, tb, Nat.div_div_eq_div_mul, pow_succ]
      · rw [sum_range_succ, tA, hbit]; simp [hz]
      · intro r hr
        simp only [mRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [QState.setReg_reg, hr.2.1, hr.2.2.1, ↓reduceIte]
        exact tR r (by simp [mRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])
      · rw [tc, NativeVm.Transcript.toUInt64_succ, toNat_toUInt64' (by omega),
          toNat_toUInt64' (by omega)]
        omega
    · have hc' : (Cond.test true .rbx (.imm 1)).eval t = false := by
        simp only [Cond.eval, Rhs.eval]; rw [show Int64.toUInt64 1 = 1 from rfl, and1_eq_zero]
        simp [hz]
      rw [hc']
      refine WP.mono (P := fun t₁ ↦ t₁.reg .rcx = t.reg .rcx ∧ t₁.reg .rbx = t.reg .rbx ∧
          eOf (t₁.reg .r9) (t₁.reg .r10) = eOf (t.reg .r9) (t.reg .r10) + (f (src + i)).toE ∧
          t₁.mem = t.mem ∧ t₁.reg .rbp = p ∧ RegsFrame mRegs t t₁) ?_ ?_ (fun _ h ↦ h)
      · fstep; fstep
        refine ldi0 (o := src) (i := i) (by simp [tp]) (by simp only [tc]; exact rax16 i) ts
          (by omega) ?_
        fstep
        refine ldi1 (o := src) (i := i) (by simp [tp]) (by simp only [tc]; exact rax16 i) ts
          (by omega) ?_
        fstep; fdone
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        rotate_left 2
        · exact eOf_add _ _ _ _
        all_goals try trivial
        · intro r hr
          simp only [mRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp [QState.setReg_reg, hr.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2]
      · intro t₁ ⟨u1, u2, u3, u4, u5, u6⟩
        fstep; fstep; fdone
        refine ⟨⟨i + 1, hlt, ?_, ?_, ?_, u4.trans tM, u5, ?_⟩, ?_⟩
        · rw [u1, tc]; exact NativeVm.Transcript.toUInt64_succ i
        · rw [toNat_shr1, u2, tb, Nat.div_div_eq_div_mul, pow_succ]
        · rw [sum_range_succ, u3, tA, hbit]; simp [hz]
        · intro r hr
          simp only [mRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [QState.setReg_reg, hr.2.1, hr.2.2.1, ↓reduceIte]
          rw [u6 r (by simp [mRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
            hr.2.2.2.2.2])]
          exact tR r (by simp [mRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])
        · rw [u1, tc, NativeVm.Transcript.toUInt64_succ, toNat_toUInt64' (by omega),
            toNat_toUInt64' (by omega)]
          omega
  · intro t ⟨i, hi, tc, _, tA, tM, _, tR⟩ hc
    have hge : ¬ i < n := by
      simp only [Cond.eval, tc, Rhs.eval, decide_eq_false_iff_not] at hc
      rw [show (Int64.ofNat n).toUInt64 = n.toUInt64 from rfl] at hc
      exact fun h ↦ hc ((toUInt64_lt' (by omega) (by omega)).mpr h)
    obtain rfl : i = n := by omega
    exact WP.blk_nil ⟨tA, tM, tR⟩

end NativeVm.Code.P6
