module

public import NativeVm.Code.Phase3.GkrBase

/-!
# The field kernels on the model's elements

The kernels the GKR walk runs (`emul`, `edot`, `eeqEval`, `epolyEval`, `emle`), their results as
the model's `EW` (`r9 = x.c0`, `r10 = x.c1`): `edot` and `eeqEval` against the ones give `sumE` and
`prodE` (`dot_ones`, `eqEval_ones`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field LeanVM.Parameters

variable {s : QState} {F : QState → Prop}

theorem eOf_regs {s : QState} {x : EW} (h : eOf (s.reg .r9) (s.reg .r10) = x.toE) :
    s.reg .r9 = x.c0 ∧ s.reg .r10 = x.c1 := eOf_eq_toE.mp h

theorem eOf_of {a b : UInt64} {x : EW} (h0 : a = x.c0) (h1 : b = x.c1) : eOf a b = x.toE := by
  rw [h0, h1]; rfl

theorem emul_ew {a b : EW} (h9 : s.reg .r9 = a.c0) (h10 : s.reg .r10 = a.c1)
    (h11 : s.reg .r11 = b.c0) (h12 : s.reg .r12 = b.c1) :
    WP emul s (fun s' ↦ s'.reg .r9 = (a * b).c0 ∧ s'.reg .r10 = (a * b).c1 ∧ s'.mem = s.mem ∧
      RegsFrame eRegs s s') F := by
  refine WP.mono (emul_spec s) (fun s' ⟨e, hm, hf⟩ ↦ ?_) (fun _ h ↦ h)
  rw [eOf_of h9 h10, eOf_of h11 h12, ← NativeVm.Equiv.EW.toE_mul] at e
  exact ⟨(eOf_regs e).1, (eOf_regs e).2, hm, hf⟩

theorem epoly_ew {cs : Array EW} {b : EW} (hc : EWArr s.mem (s.reg .r13) cs)
    (hn : s.reg .r15 = cs.size.toUInt64) (h11 : s.reg .r11 = b.c0) (h12 : s.reg .r12 = b.c1)
    (hlen : cs.size < 2 ^ 64) :
    WP epolyEval s (fun s' ↦ s'.reg .r9 = (polyEval cs b).c0 ∧ s'.reg .r10 = (polyEval cs b).c1 ∧
      s'.mem = s.mem ∧ RegsFrame polyRegs s s') F := by
  refine WP.mono (epolyEval_spec (EWArr_iff_EArr.mp hc) (by simpa using hn) (by simpa using hlen))
    (fun s' ⟨e, hm, hf⟩ ↦ ?_) (fun _ h ↦ h)
  rw [eOf_of h11 h12, ← NativeVm.Equiv.toE_polyEval] at e
  exact ⟨(eOf_regs e).1, (eOf_regs e).2, hm, hf⟩

theorem ones_earr {mem : UInt64 → Option UInt64} {p : UInt64} (h : EWArr mem p gones4) {n : Nat}
    (hn : n ≤ 4) : EArr mem p (List.replicate n 1) := by
  rw [← gones4_toE n hn]
  exact EWArr_iff_EArr.mp (EWArr.gextract h n)

theorem edot_sum {xs : Array EW} (hx : EWArr s.mem (s.reg .r13) xs)
    (ho : EWArr s.mem (s.reg .r14) gones4) (hn4 : xs.size ≤ 4) (h15 : s.reg .r15 = xs.size.toUInt64) :
    WP edot s (fun s' ↦ s'.reg .r9 = (sumE xs).c0 ∧ s'.reg .r10 = (sumE xs).c1 ∧ s'.mem = s.mem ∧
      RegsFrame arrRegs s s') F := by
  refine WP.mono (edot_spec (EWArr_iff_EArr.mp hx) (ones_earr ho hn4) (by simp) (by simpa using h15)
    (by simp; omega)) (fun s' ⟨e, hm, hf⟩ ↦ ?_) (fun _ h ↦ h)
  rw [dot_ones _ _ (by simp), ← NativeVm.Equiv.toE_sumE] at e
  exact ⟨(eOf_regs e).1, (eOf_regs e).2, hm, hf⟩

theorem eeq_prod {xs : Array EW} (hx : EWArr s.mem (s.reg .r13) xs)
    (ho : EWArr s.mem (s.reg .r14) gones4) (hn4 : xs.size ≤ 4) (h15 : s.reg .r15 = xs.size.toUInt64) :
    WP eeqEval s (fun s' ↦ s'.reg .r9 = (prodE xs).c0 ∧ s'.reg .r10 = (prodE xs).c1 ∧ s'.mem = s.mem ∧
      RegsFrame eqRegs s s') F := by
  refine WP.mono (eeqEval_spec (EWArr_iff_EArr.mp hx) (ones_earr ho hn4) (by simp)
    (by simpa using h15) (by simp; omega)) (fun s' ⟨e, hm, hf⟩ ↦ ?_) (fun _ h ↦ h)
  rw [eqEval_ones _ _ (by simp), ← NativeVm.Equiv.toE_prodE] at e
  exact ⟨(eOf_regs e).1, (eOf_regs e).2, hm, hf⟩

theorem ew_eq_wd (p : UInt64) (k : Nat) : ew p k = wd p k := rfl

theorem emle_ew {env : Env} {mle y : Array EW} {a b c : Nat}
    (h13 : s.reg .r13 = wd env.work a) (h14 : s.reg .r14 = wd env.work b)
    (hsi : s.reg .rsi = wd env.work c) (hm : EWArr s.mem (wd env.work a) mle)
    (hp : EWArr s.mem (wd env.work c) y) (hn : s.reg .r15 = mle.size.toUInt64)
    (hpow : mle.size = 2 ^ y.size) (hlen : y.size < 60)
    (hdom : ∀ k < mle.size, (s.mem (wd env.work (b + k))).isSome)
    (hab : b + mle.size ≤ a ∨ a + 2 * mle.size ≤ b) (hbc : b + mle.size ≤ c ∨ c + 2 * y.size ≤ b)
    (ha : a + 2 * mle.size < 2 ^ 61) (hb : b + mle.size < 2 ^ 61) (hc : c + 2 * y.size < 2 ^ 61) :
    WP emle s (fun s' ↦ s'.reg .r9 = (multilinearEval mle y).c0 ∧
      s'.reg .r10 = (multilinearEval mle y).c1 ∧ Wrote env [⟨b, mle.size⟩] s s') F := by
  have hpw : 2 ^ y.size < 2 ^ 60 := Nat.pow_lt_pow_right (by norm_num) hlen
  refine WP.mono (WP.frame (emle_spec (mle := mle.toList.map EW.toE) (point := y.toList.map EW.toE)
    h13 h14 hsi (EWArr_iff_EArr.mp hm) (EWArr_iff_EArr.mp hp) (by simpa using hn)
    (by simpa using hpow) (by simpa using hlen) ?_ ?_ ?_)) (fun s' ⟨⟨e, hmem, hf⟩, hd, _⟩ ↦ ?_)
    (fun _ h ↦ h.1)
  · intro k hk
    simp only [List.length_map, Array.length_toList] at hk
    rw [ew_eq_wd, wd_wd]
    exact hdom k (by omega)
  · intro k j l l' hkj hj hl hl' e
    simp only [List.length_map, Array.length_toList] at hj
    rw [ew_eq_wd, ew_eq_wd, wd_wd, wd_wd, wd_inj (by omega) (by omega)] at e
    omega
  · intro k hk j hj e
    simp only [List.length_map, Array.length_toList] at hk hj
    rw [ew_eq_wd, ew_eq_wd, wd_wd, wd_wd, wd_inj (by omega) (by omega)] at e
    omega
  · rw [← NativeVm.Equiv.toE_multilinearEval] at e
    refine ⟨(eOf_regs e).1, (eOf_regs e).2, ⟨hf .rdi (by simp), fun a' ha' ↦ hmem a' ?_, hd⟩⟩
    intro k hk e'
    simp only [List.length_map, Array.length_toList] at hk
    rw [ew_eq_wd, wd_wd] at e'
    exact ha' _ (List.mem_singleton_self _) ⟨k, by simp; omega, e'⟩

end NativeVm.Code.P3
