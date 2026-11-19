module

public import NativeVm.Code.Phase6.Sums
public import NativeVm.Code.Phase6.Lay
public import NativeVm.Field.Arrays

/-!
# An entry of `eqKernel`

`ekern o`: `A := ∏_{k < n} (p_k if bit k of i is set, else 1 + p_k)`, `p_k` the element
`o + d + k`, `i` in `r13`, `n` and `d` the words of the elements `eKn` and `eKd`
(`ekern_spec`); entry `i` of `eqKernel` of the `n` coordinates (`Facts.eqKernel_getD`).
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model
open NativeVm.Transcript (wd wd_add wd_zero wd_inj wdisp wdisp_toUInt64)
open NativeVm.Field (eOf eOf_inj emul emul_spec eRegs eOf_add eOf_zero eOf_one eOf_xor_one)
open Finset

variable {s : QState} {p : UInt64} {g : Nat → EW} {E : QState → Prop}

/-- An `eqKernel` entry. -/
def ekern (o : Nat) : Stmt := blk [I (.movi .r9 1), I (.movi .r10 0), I (.movi .rsi 0),
  I (.load .rdx (at_ .rbp (wdisp (2 * eKn)))),
  .loop (.cmp .ltu .rsi (.reg .rdx)) (blk [
    I (.load .rax (at_ .rbp (wdisp (2 * eKd)))), I (.add .rax .rsi), I (.shli .rax 4),
    I (.load .r11 (ix (2 * o))), I (.load .r12 (ix (2 * o + 1))),
    I (.mov .rcx .rsi), I (.movi .rdx 1), I (.shlcl .rdx),
    .ite (.test true .r13 (.reg .rdx)) (I (.xori .r11 1)) .skip,
    emul, I (.addi .rsi 1), I (.load .rdx (at_ .rbp (wdisp (2 * eKn))))])]

/-- The registers `ekern` writes. -/
abbrev kernRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12, .rsi]

/-- The entry's factor for coordinate `k`. -/
def kfac (g : Nat → EW) (o d i k : Nat) : LeanVM.Parameters.E :=
  if i.testBit k then (g (o + d + k)).toE else 1 + (g (o + d + k)).toE

theorem bit_test {i k : Nat} (hi : i < 2 ^ 64) (hk : k < 64) :
    ((i.toUInt64 &&& ((1 : UInt64) <<< (k.toUInt64 &&& 63))) == 0) = !i.testBit k := by
  have hk' : k.toUInt64 &&& 63 = k.toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, toNat_toUInt64' (by omega)]
    show k &&& 63 = k
    rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hk]
  rw [hk']
  have h2 : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hk
  have e : ((1 : UInt64) <<< k.toUInt64) = (2 ^ k).toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftLeft, toNat_toUInt64' (by omega), toNat_toUInt64' h2,
      Nat.mod_eq_of_lt (by omega : k < 64)]
    simp only [UInt64.toNat_one, Nat.shiftLeft_eq, one_mul]
    exact Nat.mod_eq_of_lt h2
  rw [e]
  rw [Bool.eq_iff_iff, beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_and, toNat_toUInt64' hi,
    toNat_toUInt64' h2]
  simp only [UInt64.toNat_zero, Bool.not_eq_true']
  rw [Nat.and_two_pow, Bool.eq_false_iff]
  constructor
  · intro h ht; rw [ht] at h; simp at h
  · intro h; simp [Bool.eq_false_iff.mpr h]

/-- **`ekern` computes an `eqKernel` entry.** -/
theorem ekern_spec {o i n d : Nat} (hp : s.reg .rbp = p) (hs : Scr s.mem p g)
    (hn : g eKn = EW.ofK n.toUInt64) (hd : g eKd = EW.ofK d.toUInt64) (h13 : s.reg .r13 = i.toUInt64)
    (hi : i < 2 ^ 64) (hn64 : n < 64) (hod : o + d + n ≤ scrN) :
    WP (ekern o) s (fun s' ↦ eOf (s'.reg .r9) (s'.reg .r10) = ∏ k ∈ range n, kfac g o d i k ∧
      s'.mem = s.mem ∧ RegsFrame kernRegs s s') E := by
  have hN := scrN_lt
  unfold ekern
  fstep; fstep; fstep
  refine ld0 (p := p) (by simpa using hp) hs (by p6_omega) ?_
  rw [hn]
  apply WP.blk_cons
  apply WP.loop (fun t ↦ ∃ k ≤ n, t.reg .rsi = k.toUInt64 ∧ t.reg .rdx = n.toUInt64 ∧
      eOf (t.reg .r9) (t.reg .r10) = ∏ j ∈ range k, kfac g o d i j ∧ t.mem = s.mem ∧
      RegsFrame kernRegs s t)
    (fun t ↦ n - (t.reg .rsi).toNat)
  · refine ⟨0, Nat.zero_le _, by simp, by simp [EW.ofK], ?_, rfl, ?_⟩
    · simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, range_zero, prod_empty]
      exact eOf_one
    · intro r hr
      simp only [kernRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [QState.setReg_reg, hr.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2]
  · intro t ⟨k, _, tk, tn, tA, tM, tR⟩ hc
    have hlt : k < n := by
      simp only [Cond.eval, tk, Rhs.eval, tn, decide_eq_true_eq] at hc
      exact (toUInt64_lt' (by omega) (by omega)).mp hc
    have tp : t.reg .rbp = p := by rw [tR .rbp (by decide)]; exact hp
    have ts : Scr t.mem p g := hs.congr fun a _ ↦ by rw [tM]
    have t13 : t.reg .r13 = i.toUInt64 := by rw [tR .r13 (by decide)]; exact h13
    refine ld0 (p := p) tp ts (by p6_omega) ?_
    rw [hd]
    fstep; fstep
    have hrax : (d.toUInt64 + k.toUInt64) <<< (4 : Nat).toUInt64 = (8 * (2 * (d + k))).toUInt64 := by
      rw [NativeVm.Transcript.toUInt64_add]; exact rax16 _
    refine ldi0 (o := o) (i := d + k) (by simp [tp]) (by simp only [QState.setReg_reg, ↓reduceIte, tk, EW.ofK]; exact hrax) ts (by omega) ?_
    refine ldi1 (o := o) (i := d + k) (by simp [tp]) (by simp only [QState.setReg_reg, ↓reduceIte, tk, EW.ofK]; exact hrax) ts (by omega) ?_
    fstep; fstep; fstep
    apply WP.blk_cons
    apply WP.ite
    have hb := bit_test (i := i) (k := k) hi (by omega)
    simp only [Cond.eval, Rhs.eval, QState.setReg_reg, reduceCtorEq, ↓reduceIte, t13, tk] at hb ⊢
    rw [hb]
    have key : ∀ (u : QState), u.mem = t.mem → u.reg .rbp = p → u.reg .rsi = k.toUInt64 →
        RegsFrame kernRegs s u → eOf (u.reg .r11) (u.reg .r12) = kfac g o d i k →
        u.reg .r9 = t.reg .r9 → u.reg .r10 = t.reg .r10 →
        WP (blk [emul, I (.addi .rsi 1), I (.load .rdx (at_ .rbp (wdisp (2 * eKn))))]) u
          (fun t' ↦ (∃ k' ≤ n, t'.reg .rsi = k'.toUInt64 ∧ t'.reg .rdx = n.toUInt64 ∧
            eOf (t'.reg .r9) (t'.reg .r10) = ∏ j ∈ range k', kfac g o d i j ∧ t'.mem = s.mem ∧
            RegsFrame kernRegs s t') ∧ n - (t'.reg .rsi).toNat < n - k) E := by
      intro u um up uk uR uB u9 u10
      refine WP.blk_cons (WP.mono (emul_spec _) (fun u1 ⟨e1, e2, e3⟩ ↦ ?_) (fun _ h ↦ h))
      fstep
      refine ld0 (p := p) (by simp [e3 .rbp (by decide), up]) (hs.congr fun a _ ↦ by
        simp only [QState.setReg_mem]; rw [e2, um, tM]) (by p6_omega) ?_
      rw [hn]
      fdone
      refine ⟨⟨k + 1, hlt, ?_, rfl, ?_, by rw [e2, um, tM], ?_⟩, ?_⟩
      · rw [e3 .rsi (by decide), uk]; exact NativeVm.Transcript.toUInt64_succ k
      · rw [prod_range_succ, e1, u9, u10, tA, uB]
      · intro r hr
        simp only [kernRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [QState.setReg_reg, hr.2.2.2.1, hr.2.2.2.2.2.2.2.2.2, ↓reduceIte]
        rw [e3 r (by simp [eRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
          hr.2.2.2.2.2.2.1])]
        exact uR r (by simp [kernRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
          hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1,
          hr.2.2.2.2.2.2.2.2.2])
      · rw [e3 .rsi (by decide), uk, NativeVm.Transcript.toUInt64_succ,
          toNat_toUInt64' (by omega)]
        omega
    have frame : ∀ (u : QState), RegsFrame kernRegs t u → RegsFrame kernRegs s u :=
      fun u h r hr ↦ (h r hr).trans (tR r hr)
    rw [toNat_toUInt64' (by omega)]
    by_cases hbit : i.testBit k
    · simp only [hbit, Bool.not_true, beq_true, Bool.false_eq_true, ↓reduceIte]
      refine WP.skip (key _ (by simp) (by simp [tp]) (by simp [tk]) (frame _ (by rf_tac)) ?_
        (by simp) (by simp))
      simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, kfac, hbit]
      rw [eOf_toE, Nat.add_assoc]
    · simp only [hbit, Bool.not_false, beq_true, ↓reduceIte]
      refine WP.ins (by rfl) (key _ (by simp) (by simp [tp]) (by simp [tk])
        (frame _ (by rf_tac)) ?_ (by simp) (by simp))
      simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, kfac, hbit]
      rw [show Int64.toUInt64 1 = 1 from rfl, eOf_xor_one, eOf_toE, add_comm, Nat.add_assoc]
  · intro t ⟨k, hk, tk, tn, tA, tM, tR⟩ hc
    have hge : ¬ k < n := by
      simp only [Cond.eval, tk, Rhs.eval, tn, decide_eq_false_iff_not] at hc
      exact fun h ↦ hc ((toUInt64_lt' (by omega) (by omega)).mpr h)
    obtain rfl : k = n := by omega
    exact WP.blk_nil ⟨tA, tM, tR⟩

end NativeVm.Code.P6
