module

public import NativeVm.Field.K

/-!
# Powers and the inverse in `K`

`ksqn`: `rax := rax^(2^rdx)`, `rdx` squarings; `sqMul k m`: `rax := rax^(2^k) · m`; `kinv`:
`rax := rax⁻¹` (`0 ↦ 0`, as `K`'s `Inv`), by the Itoh-Tsujii chain of `K::inv`
(`crates/verifier/src/field.rs`): with `t_k = a^(2^k - 1)`, `t_(k+j) = t_k^(2^j) · t_j`, along
`1, 2, 3, 6, 12, 24, 48, 60, 63`, and `a^(2^64 - 2) = t_63²`.
-/

@[expose] public section

namespace NativeVm.Field

open Native LeanVM.Parameters

/-- `rax := rax^(2^rdx)` in `K`: `rdx` squarings, counting `rdx` down to zero. -/
def ksqn : Stmt := .loop (.test false .rdx (.reg .rdx)) (blk [ksq, I (.subi .rdx 1)])

/-- The registers `ksqn` and `sqMul` write. -/
abbrev kRegsD : List Reg64 := [.rax, .rbx, .rcx, .rdx, .r8]

theorem toNat_sub_one {x : UInt64} (h : x ≠ 0) : (x - 1).toNat = x.toNat - 1 := by
  have : x.toNat ≠ 0 := fun h0 ↦ h (UInt64.toNat_inj.mp (by simpa using h0))
  rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]
  rfl

/-- **`ksqn` raises to `2^rdx`.** -/
theorem ksqn_spec (s : QState) {E : QState → Prop} :
    WP ksqn s (fun s' ↦
      K.ofLane (s'.reg .rax) = K.ofLane (s.reg .rax) ^ 2 ^ (s.reg .rdx).toNat ∧
      s'.reg .rdx = 0 ∧ s'.mem = s.mem ∧ RegsFrame kRegsD s s') E := by
  unfold ksqn
  apply WP.loop (fun t ↦ K.ofLane (t.reg .rax) ^ 2 ^ (t.reg .rdx).toNat =
      K.ofLane (s.reg .rax) ^ 2 ^ (s.reg .rdx).toNat ∧ t.mem = s.mem ∧ RegsFrame kRegsD s t)
    (fun t ↦ (t.reg .rdx).toNat)
  · exact ⟨rfl, rfl, RegsFrame.refl _ _⟩
  · intro t ⟨hI, hm, hf⟩ hc
    have hne : t.reg .rdx ≠ 0 := by simpa [Cond.eval, Rhs.eval] using hc
    have hpos : (t.reg .rdx).toNat ≠ 0 := fun h0 ↦ hne (UInt64.toNat_inj.mp (by simpa using h0))
    refine WP.then (ksq_spec _) fun t₁ ⟨h1, h2, h3⟩ ↦ ?_
    have hd : t₁.reg .rdx = t.reg .rdx := h3 .rdx (by simp)
    fstep
    fdone
    refine ⟨⟨?_, h2.trans hm, ?_⟩, ?_⟩
    · rw [hd, toNat_sub_one hne, h1, ← pow_mul, ← pow_succ', Nat.sub_add_cancel (by omega), hI]
    · exact RegsFrame.setReg (RegsFrame.trans hf (RegsFrame.mono h3 (by simp))) (by simp) _
    · rw [hd, toNat_sub_one hne]
      omega
  · intro t ⟨hI, hm, hf⟩ hc
    have h0 : t.reg .rdx = 0 := by simpa [Cond.eval, Rhs.eval] using hc
    refine ⟨?_, h0, hm, hf⟩
    rw [← hI, h0]
    simp

/-- `rax := rax^(2^k) · m` in `K`. -/
def sqMul (k : Int64) (m : Reg64) : Stmt := blk [I (.movi .rdx k), ksqn, I (.mov .rbx m), kmul]

theorem sqMul_spec (k : Int64) (m : Reg64) (hm : m ∉ kRegsD) (s : QState) {E : QState → Prop} :
    WP (sqMul k m) s (fun s' ↦
      K.ofLane (s'.reg .rax) = K.ofLane (s.reg .rax) ^ 2 ^ k.toUInt64.toNat * K.ofLane (s.reg m) ∧
      s'.mem = s.mem ∧ RegsFrame kRegsD s s') E := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
  obtain ⟨ha, hb, hc, hd, h8⟩ := hm
  unfold sqMul
  fstep
  refine WP.then (ksqn_spec _) fun t ⟨h1, _, h2, h3⟩ ↦ ?_
  fstep
  refine WP.then (kmul_spec _) fun t₁ ⟨e1, e2, e3⟩ ↦ ?_
  fdone
  have hmt : t.reg m = s.reg m := by
    rw [h3 m (by simp [ha, hb, hc, hd, h8])]
    simp [hd]
  refine ⟨?_, e2.trans h2, ?_⟩
  · rw [e1]
    simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false, hmt]
    rw [h1]
    simp
  · refine RegsFrame.trans (RegsFrame.trans (by rf_tac) h3)
      (RegsFrame.trans ?_ (RegsFrame.mono e3 ?_))
    · exact RegsFrame.setReg (RegsFrame.refl _ _) (by simp) _
    · simp

/-- The Itoh-Tsujii step: `a^(2^n - 1)` to the `2^m`, times `a^(2^m - 1)`, is `a^(2^(n+m) - 1)`. -/
theorem chain_step {a x y : K} {n m : Nat} (hx : x = a ^ (2 ^ n - 1)) (hy : y = a ^ (2 ^ m - 1)) :
    x ^ 2 ^ m * y = a ^ (2 ^ (n + m) - 1) := by
  rw [hx, hy, ← pow_mul, ← pow_add]
  congr 1
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rw [pow_add]
  generalize 2 ^ n = A at *
  generalize 2 ^ m = B at *
  obtain ⟨a, rfl⟩ : ∃ a, A = a + 1 := ⟨A - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, B = b + 1 := ⟨B - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

/-- `a^(2^64 - 2)` is `a⁻¹` in `K`, `0` at `0`. -/
theorem pow_card_sub_two (a : K) : a ^ (2 ^ 64 - 2) = a⁻¹ := by
  by_cases ha : a = 0
  · subst ha
    rw [inv_zero, zero_pow (by norm_num)]
  · let := Fintype.ofFinite K
    have hc : Fintype.card K = 2 ^ 64 := BF64.card_bf64
    have h1 := FiniteField.pow_card_sub_one_eq_one a ha
    rw [hc] at h1
    have h2 : a ^ (2 ^ 64 - 2) * a = 1 := by
      rw [← pow_succ]
      exact h1
    exact eq_inv_of_mul_eq_one_left h2

/-- `rax := rax⁻¹` in `K` (`0 ↦ 0`): `t_1` in `rsi`, `t_3` in `rbp`, `t_6` then `t_12` in `r9`,
`t_24` in `r10`. -/
def kinv : Stmt := blk [
  I (.mov .rsi .rax),
  sqMul 1 .rsi,
  sqMul 1 .rsi, I (.mov .rbp .rax),
  sqMul 3 .rbp, I (.mov .r9 .rax),
  sqMul 6 .r9, I (.mov .r9 .rax),
  sqMul 12 .r9, I (.mov .r10 .rax),
  sqMul 24 .r10,
  sqMul 12 .r9,
  sqMul 3 .rbp,
  I (.movi .rdx 1), ksqn]

/-- The registers `kinv` writes. -/
abbrev kinvRegs : List Reg64 := [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10]

/-- **`kinv` inverts in `K`**, `0 ↦ 0`. -/
theorem kinv_spec (s : QState) {E : QState → Prop} :
    WP kinv s (fun s' ↦ K.ofLane (s'.reg .rax) = (K.ofLane (s.reg .rax))⁻¹ ∧ s'.mem = s.mem ∧
      RegsFrame kinvRegs s s') E := by
  set a := K.ofLane (s.reg .rax) with ha
  have e1 : a = a ^ (2 ^ 1 - 1) := by norm_num
  unfold kinv
  fstep
  refine WP.then (sqMul_spec 1 .rsi (by decide) _) fun t1 ⟨h1, m1, f1⟩ ↦ ?_
  have r1 : t1.reg .rsi = s.reg .rax := by rw [f1 .rsi (by decide)]; simp
  have x2 : K.ofLane (t1.reg .rax) = a ^ (2 ^ 2 - 1) := by
    rw [h1]
    rsimp
    exact chain_step (n := 1) (m := 1) e1 e1
  refine WP.then (sqMul_spec 1 .rsi (by decide) _) fun t2 ⟨h2, m2, f2⟩ ↦ ?_
  have x3 : K.ofLane (t2.reg .rax) = a ^ (2 ^ 3 - 1) := by
    rw [h2, r1]
    exact chain_step (n := 2) (m := 1) x2 e1
  fstep
  refine WP.then (sqMul_spec 3 .rbp (by decide) _) fun t3 ⟨h3, m3, f3⟩ ↦ ?_
  have r3 : K.ofLane (t3.reg .rbp) = a ^ (2 ^ 3 - 1) := by rw [f3 .rbp (by decide)]; simpa using x3
  have x6 : K.ofLane (t3.reg .rax) = a ^ (2 ^ 6 - 1) := by
    rw [h3]
    rsimp
    exact chain_step (n := 3) (m := 3) x3 x3
  fstep
  refine WP.then (sqMul_spec 6 .r9 (by decide) _) fun t4 ⟨h4, m4, f4⟩ ↦ ?_
  have x12 : K.ofLane (t4.reg .rax) = a ^ (2 ^ 12 - 1) := by
    rw [h4]
    rsimp
    exact chain_step (n := 6) (m := 6) x6 x6
  fstep
  refine WP.then (sqMul_spec 12 .r9 (by decide) _) fun t5 ⟨h5, m5, f5⟩ ↦ ?_
  have r5 : K.ofLane (t5.reg .r9) = a ^ (2 ^ 12 - 1) := by rw [f5 .r9 (by decide)]; simpa using x12
  have x24 : K.ofLane (t5.reg .rax) = a ^ (2 ^ 24 - 1) := by
    rw [h5]
    rsimp
    exact chain_step (n := 12) (m := 12) x12 x12
  fstep
  refine WP.then (sqMul_spec 24 .r10 (by decide) _) fun t6 ⟨h6, m6, f6⟩ ↦ ?_
  have r6 : K.ofLane (t6.reg .r9) = a ^ (2 ^ 12 - 1) := by
    rw [f6 .r9 (by decide)]; simpa using r5
  have x48 : K.ofLane (t6.reg .rax) = a ^ (2 ^ 48 - 1) := by
    rw [h6]
    rsimp
    exact chain_step (n := 24) (m := 24) x24 x24
  refine WP.then (sqMul_spec 12 .r9 (by decide) _) fun t7 ⟨h7, m7, f7⟩ ↦ ?_
  have x60 : K.ofLane (t7.reg .rax) = a ^ (2 ^ 60 - 1) := by
    rw [h7]
    exact chain_step (n := 48) (m := 12) x48 r6
  refine WP.then (sqMul_spec 3 .rbp (by decide) _) fun t8 ⟨h8, m8, f8⟩ ↦ ?_
  have r8 : K.ofLane (t7.reg .rbp) = a ^ (2 ^ 3 - 1) := by
    rw [f7 .rbp (by decide), f6 .rbp (by decide)]
    rsimp
    rw [f5 .rbp (by decide)]
    rsimp
    rw [f4 .rbp (by decide)]
    rsimp
    exact r3
  have x63 : K.ofLane (t8.reg .rax) = a ^ (2 ^ 63 - 1) := by
    rw [h8]
    exact chain_step (n := 60) (m := 3) x60 r8
  fstep
  refine WP.then (ksqn_spec _) fun t9 ⟨h9, _, m9, f9⟩ ↦ ?_
  fdone
  refine ⟨?_, ?_, ?_⟩
  · rw [h9]
    rsimp
    rw [x63, ← pow_card_sub_two, ← pow_mul]
    rfl
  · simp only [m9, m8, m7, m6, m5, m4, m3, m2, m1, QState.setReg_mem]
  · intro r hr
    simp only [kinvRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨_, _, _, hrdx, hrsi, hrbp, _, hr9, hr10⟩ := hr
    have hk : r ∉ kRegsD := by simp [kRegsD, *]
    simp only [f9 r hk, f8 r hk, f7 r hk, f6 r hk, f5 r hk, f4 r hk, f3 r hk, f2 r hk, f1 r hk,
      QState.setReg_reg, hrdx, hrsi, hrbp, hr9, hr10, ↓reduceIte]

end NativeVm.Field
