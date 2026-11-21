module

public import NativeVm.Wire.Mem
public import NativeVm.Wire.Read
public import Native.Sphincs.Words

/-!
# Reading the wire

What the reading gadgets do: `rdByte` loads byte `p` of the wire (`rdByte_ok`), `rdLE n` the
little-endian number of the `n` bytes from `p` (`rdLE_ok`), `needI` and `needR` fail unless enough
bytes are left (`needI_ok`, `needR_ok`), and `rdU32` reads the model's `rdU32` (`rdU32_ok`). The
position `p` is in `r15` throughout.
-/

@[expose] public section

namespace NativeVm.Wire

open Native Native.Keccak Native.Keccak.Proof
open Native.SphincsVerifier (toNat_toUInt64' toUInt64_add toUInt64_shr imm_nat)

/-! ## A byte of a word -/

theorem byte_nat (w r : Nat) (hr : r < 8) :
    w * 2 ^ (56 - 8 * r) % 2 ^ 64 / 2 ^ 56 = w / 2 ^ (8 * r) % 2 ^ 8 := by
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases ht : t < 8
  · simp [show t + 56 < 64 by omega, ht, show 56 - 8 * r ≤ t + 56 by omega,
      show t + 56 - (56 - 8 * r) = t + 8 * r by omega]
  · simp [show ¬ t + 56 < 64 by omega, ht]

/-- What `rdByte` computes from the word `w` and the position `q`. -/
theorem byte_word (w q : UInt64) :
    (w <<< (((~~~q) &&& 7) <<< 3 &&& 63)) >>> 56 =
      ((w >>> (8 * (q.toNat % 8)).toUInt64).toUInt8).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have h7 : ((~~~q) &&& 7).toNat = 7 - q.toNat % 8 := by
    rw [UInt64.toNat_and, UInt64.toNat_not, show (7 : UInt64).toNat = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    have := q.toNat_lt
    simp only [UInt64.size] at *
    omega
  have hs : (((~~~q) &&& 7) <<< 3 &&& 63).toNat = 56 - 8 * (q.toNat % 8) := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftLeft, h7, show (63 : UInt64).toNat = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show (3 : UInt64).toNat % 64 = 3 from rfl, Nat.shiftLeft_eq]
    omega
  rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, hs, show (56 : UInt64).toNat % 64 = 56 from rfl,
    Nat.mod_eq_of_lt (show 56 - 8 * (q.toNat % 8) < 64 by omega), Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, byte_nat _ _ (Nat.mod_lt _ (by omega)), UInt8.toNat_toUInt64,
    UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, toNat_toUInt64 (by omega),
    Nat.mod_eq_of_lt (show 8 * (q.toNat % 8) < 64 by omega), Nat.shiftRight_eq_div_pow]

/-- Byte `p` of the wire is byte `p % 8` of word `p / 8`. -/
theorem getD_B {e : Env} (P : Pre e) (p : Nat) :
    e.B.getD p 0 = (e.ws.getD (p / 8) 0 >>> (8 * (p % 8)).toUInt64).toUInt8 := by
  rw [Env.B, getD_held P.hold, getD_wordsBytes]

theorem B_length {e : Env} (P : Pre e) : e.B.length = e.L := length_held P.hold

/-- One more byte shifted in from the top. -/
theorem leStep_val {a b j : Nat} (hj : j < 8) (ha : a < 2 ^ (8 * j)) (hb : b < 256) :
    (a * 2 ^ (64 - 8 * j)) / 256 + b * 2 ^ 56 = (a + b * 2 ^ (8 * j)) * 2 ^ (64 - 8 * (j + 1)) ∧
      (a + b * 2 ^ (8 * j)) * 2 ^ (64 - 8 * (j + 1)) < 2 ^ 64 := by
  have h1 : 2 ^ (64 - 8 * j) = 2 ^ (64 - 8 * (j + 1)) * 256 := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← pow_add]; congr 1; omega
  have h2 : 2 ^ 56 = 2 ^ (8 * j) * 2 ^ (64 - 8 * (j + 1)) := by rw [← pow_add]; congr 1; omega
  have h3 : 2 ^ 64 = 2 ^ (8 * j) * 256 * 2 ^ (64 - 8 * (j + 1)) := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← pow_add, ← pow_add]; congr 1; omega
  refine ⟨?_, ?_⟩
  · rw [h1, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by norm_num), h2]
    ring
  · rw [h3]
    apply Nat.mul_lt_mul_of_pos_right _ (Nat.two_pow_pos _)
    have : b * 2 ^ (8 * j) ≤ 255 * 2 ^ (8 * j) := Nat.mul_le_mul_right _ (by omega)
    omega

theorem leNat_succ (B : List UInt8) (p j : Nat) :
    leNat B p (j + 1) = leNat B p j + (B.getD (p + j) 0).toNat * 2 ^ (8 * j) := by
  rw [leNat, Finset.sum_range_succ, ← leNat, pow_mul]
  rfl

/-- `failIf c` fails where `c` holds, and does nothing elsewhere. -/
theorem wp_failIf {c : Cond} {s : QState} {Q F : QState → Prop} (ht : c.eval s = true → F s)
    (hf : c.eval s = false → Q s) : WP (failIf c) s Q F := by
  unfold failIf
  apply WP.ite
  cases h : c.eval s
  · exact WP.skip (hf h)
  · exact WP.fail (ht h)

/-! ## The gadgets -/

section Gadgets

variable {e : Env} (P : Pre e)
include P

variable {s : QState} {D W : Nat → UInt64} {F : QState → Prop}

theorem rdByte_ok (hI : Inv e s D W) {p : Nat} (hp : s.reg .r15 = p.toUInt64) (hpL : p < e.L) :
    WP rdByte s (fun s' ↦ Inv e s' D W ∧ s'.reg .rax = (e.B.getD p 0).toUInt64 ∧
      s'.reg .r15 = (p + 1).toUInt64 ∧ RegsFrame [.rax, .rcx, .rdx, .r15] s s') F := by
  have hL := P.L32
  have hw : e.ws.length = (e.L + 7) / 8 := P.hold.1
  unfold rdByte
  refine blk_load_ctx P hI (eval_cw s hI.rdi cWire) (by decide) P.c0 ?_
  step; step
  refine blk_load_wire P ((hI.setReg (by decide) _).setReg (by decide) _) (i := p / 8) ?_
    (by omega) ?_
  · simp only [Addr.eval, QState.setReg_reg, reduceCtorEq, ite_true, ite_false, hp, Width.bytes]
    rw [toUInt64_shr (by omega) (by omega), adr]
    simp [Nat.toUInt64_eq, UInt64.ofNat_mul, UInt64.mul_comm]
    rfl
  step; step; step; step; step; step; step
  apply WP.blk_nil
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (((hI.setReg (by decide) _).setReg (by decide) _).setReg (by decide) _ |>.setReg
      (by decide) _ |>.setReg (by decide) _)
  · simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false, hp]
    rw [getD_B P p, show (7 : Int64).toUInt64 = 7 from rfl, show (3 : Nat).toUInt64 = 3 from rfl,
      show (56 : Nat).toUInt64 = 56 from rfl, byte_word, toNat_toUInt64 (by omega)]
  · simp only [QState.setReg_reg, ite_true, hp, show (1 : Int64).toUInt64 = (1 : Nat).toUInt64
      from rfl, toUInt64_add]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]

theorem leStep_ok (hI : Inv e s D W) {p j : Nat} (hj : j < 8) (hp : s.reg .r15 = (p + j).toUInt64)
    (hpL : p + j < e.L) (hb : (s.reg .rbx).toNat = leNat e.B p j * 2 ^ (64 - 8 * j)) :
    WP leStep s (fun s' ↦ Inv e s' D W ∧ s'.reg .r15 = (p + j + 1).toUInt64 ∧
      (s'.reg .rbx).toNat = leNat e.B p (j + 1) * 2 ^ (64 - 8 * (j + 1)) ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .r15] s s') F := by
  unfold leStep
  apply WP.blk_cons
  refine WP.mono (rdByte_ok P hI hp hpL) (fun s1 ⟨h1, ha, hr, hf⟩ ↦ ?_) (fun _ h ↦ h)
  have hb1 : s1.reg .rbx = s.reg .rbx := hf .rbx (by simp)
  step; step; step
  apply WP.blk_nil
  refine ⟨((h1.setReg (by decide) _).setReg (by decide) _).setReg (by decide) _, ?_, ?_, ?_⟩
  · simp [hr]
  · simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false, hb1, ha]
    have hlt := leNat_lt e.B p j
    have hbyte := (e.B.getD (p + j) 0).toNat_lt
    obtain ⟨hv, hv'⟩ := leStep_val (a := leNat e.B p j) (b := (e.B.getD (p + j) 0).toNat) hj
      (by simpa [pow_mul] using hlt) hbyte
    rw [leNat_succ, ← hv, UInt64.toNat_add, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, hb,
      UInt8.toNat_toUInt64, show (8 : Nat).toUInt64.toNat % 64 = 8 from rfl,
      show (56 : Nat).toUInt64.toNat % 64 = 56 from rfl, Nat.shiftRight_eq_div_pow,
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show (e.B.getD (p + j) 0).toNat * 2 ^ 56 < 2 ^ 64 by
        have : (e.B.getD (p + j) 0).toNat * 2 ^ 56 ≤ 255 * 2 ^ 56 := Nat.mul_le_mul_right _ (by omega)
        omega)]
    exact Nat.mod_eq_of_lt (hv ▸ hv')
  · intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    simp only [QState.setReg_reg, hr'.1, hr'.2.1, ite_false]
    exact hf r (by simp [hr'.1, hr'.2.2.1, hr'.2.2.2.1, hr'.2.2.2.2])

theorem leSteps_ok {p : Nat} {Q : QState → Prop} {rest : List Stmt} (m : Nat) :
    ∀ (j : Nat) (s : QState), Inv e s D W → j + m ≤ 8 → s.reg .r15 = (p + j).toUInt64 →
      p + j + m ≤ e.L → (s.reg .rbx).toNat = leNat e.B p j * 2 ^ (64 - 8 * j) →
      (∀ s', Inv e s' D W → s'.reg .r15 = (p + j + m).toUInt64 →
        (s'.reg .rbx).toNat = leNat e.B p (j + m) * 2 ^ (64 - 8 * (j + m)) →
        RegsFrame [.rax, .rbx, .rcx, .rdx, .r15] s s' → WP (blk rest) s' Q F) →
      WP (blk (List.replicate m leStep ++ rest)) s Q F := by
  induction m with
  | zero =>
    intro j s hI _ hp _ hb k
    simpa using k s hI hp hb (fun _ _ ↦ rfl)
  | succ m ih =>
    intro j s hI hjm hp hpL hb k
    rw [List.replicate_succ, List.cons_append]
    apply WP.blk_cons
    refine WP.mono (leStep_ok P hI (by omega) hp (by omega) hb) (fun s1 ⟨h1, hp1, hb1, hf1⟩ ↦ ?_)
      (fun _ h ↦ h)
    refine ih (j + 1) s1 h1 (by omega) (by rw [hp1]; rfl) (by omega) hb1
      fun s' h' hp' hb' hf' ↦ k s' h' (by rw [hp']; congr 1; omega)
        (by rw [hb', show j + 1 + m = j + (m + 1) by omega]) (RegsFrame.trans hf1 hf')

theorem rdLE_ok (hI : Inv e s D W) {p n : Nat} (hn : 0 < n) (hn8 : n ≤ 8)
    (hp : s.reg .r15 = p.toUInt64) (hpL : p + n ≤ e.L) :
    WP (rdLE n) s (fun s' ↦ Inv e s' D W ∧ s'.reg .rbx = (leNat e.B p n).toUInt64 ∧
      s'.reg .r15 = (p + n).toUInt64 ∧ RegsFrame [.rax, .rbx, .rcx, .rdx, .r15] s s') F := by
  unfold rdLE
  rw [List.singleton_append]
  step
  refine leSteps_ok P n 0 _ (hI.setReg (by decide) _) (by omega) (by simpa using hp) (by omega)
    (by simp [leNat]; rfl) fun s' h' hp' hb' hf' ↦ ?_
  step
  apply WP.blk_nil
  refine ⟨h'.setReg (by decide) _, ?_, by simpa using hp', ?_⟩
  · simp only [QState.setReg_reg, ite_true]
    apply UInt64.toNat_inj.mp
    have hlt := leNat_lt e.B p n
    rw [UInt64.toNat_shiftRight, toNat_toUInt64' (show 64 - 8 * n < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 64 - 8 * n < 64 by omega), Nat.zero_add] at *
    rw [hb', Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ (Nat.two_pow_pos _),
      toNat_toUInt64' (lt_of_lt_of_le hlt (by
        calc 256 ^ n ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) hn8
          _ = 2 ^ 64 := by norm_num))]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [QState.setReg_reg, hr.2.1, ite_false]
    rw [hf' r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])]
    simp [hr.2.1]

/-- `L - p` in `rax`, read from the context. -/
theorem left_ok (hI : Inv e s D W) {p : Nat} (hp : s.reg .r15 = p.toUInt64) (hpL : p ≤ e.L)
    {Q : QState → Prop} {rest : List Stmt}
    (k : WP (blk rest) (s.setReg .rax (e.L - p).toUInt64) Q F) :
    WP (blk (I (.load .rax (cw cLen)) :: I (.sub .rax .r15) :: rest)) s Q F := by
  refine blk_load_ctx P hI (eval_cw s hI.rdi cLen) (by decide) P.c1 ?_
  step
  rw [hp, Native.SphincsVerifier.toUInt64_sub hpL]
  exact k

theorem needI_ok (hI : Inv e s D W) {p n : Nat} (hp : s.reg .r15 = p.toUInt64) (hpL : p ≤ e.L)
    (hn : n < 2 ^ 31) :
    WP (needI n) s (fun s' ↦ p + n ≤ e.L ∧ Inv e s' D W ∧ RegsFrame [.rax] s s')
      (fun s' ↦ e.L < p + n ∧ Kept e s') := by
  have hL := P.L32
  unfold needI
  refine left_ok P hI hp hpL ?_
  apply WP.blk_cons
  have hc : (Cond.cmp .ltu .rax (.imm n.toInt64)).eval (s.setReg .rax (e.L - p).toUInt64) =
      decide (e.L - p < n) := by
    rw [Native.SphincsVerifier.cond_ltu_imm (n := e.L - p) (K := n) (by simp)
      (by rw [Native.SphincsVerifier.toInt64_toUInt64]) (by omega) (by omega)]
  refine wp_failIf (fun h ↦ ⟨?_, (hI.setReg (by decide) _).kept⟩)
    (fun h ↦ WP.blk_nil ⟨?_, hI.setReg (by decide) _, RegsFrame.setReg (RegsFrame.refl s) (by simp) _⟩)
  · rw [hc, decide_eq_true_iff] at h; omega
  · rw [hc, decide_eq_false_iff_not] at h; omega

theorem needR_ok (hI : Inv e s D W) {p n : Nat} {r : Reg64} (hr : r ≠ .rax)
    (hp : s.reg .r15 = p.toUInt64) (hpL : p ≤ e.L) (hrn : s.reg r = n.toUInt64) (hn : n < 2 ^ 64) :
    WP (needR r) s (fun s' ↦ p + n ≤ e.L ∧ Inv e s' D W ∧ RegsFrame [.rax] s s')
      (fun s' ↦ e.L < p + n ∧ Kept e s') := by
  have hL := P.L32
  unfold needR
  refine left_ok P hI hp hpL ?_
  apply WP.blk_cons
  have hc : (Cond.cmp .ltu .rax (.reg r)).eval (s.setReg .rax (e.L - p).toUInt64) =
      decide (e.L - p < n) :=
    Native.SphincsVerifier.cond_ltu_reg (by simp) (by simp [hr, hrn]) (by omega) hn
  refine wp_failIf (fun h ↦ ⟨?_, (hI.setReg (by decide) _).kept⟩)
    (fun h ↦ WP.blk_nil ⟨?_, hI.setReg (by decide) _, RegsFrame.setReg (RegsFrame.refl s) (by simp) _⟩)
  · rw [hc, decide_eq_true_iff] at h; omega
  · rw [hc, decide_eq_false_iff_not] at h; omega

/-- **`getU32` reads the model's `rdU32`**, or fails where it gives `none`. -/
theorem getU32_ok (hI : Inv e s D W) {p : Nat} (hp : s.reg .r15 = p.toUInt64) (hpL : p ≤ e.L) :
    WP getU32 s (fun s' ↦ ∃ v, rdU32 e.B p = some (v, p + 4) ∧ v < 2 ^ 32 ∧ Inv e s' D W ∧
      s'.reg .rbx = v.toUInt64 ∧ s'.reg .r15 = (p + 4).toUInt64 ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .r15] s s')
      (fun s' ↦ rdU32 e.B p = none ∧ Kept e s') := by
  unfold getU32
  apply WP.blk_cons
  refine WP.mono (needI_ok P hI hp hpL (n := 4) (by norm_num)) (fun s1 ⟨hn, h1, hf1⟩ ↦ ?_)
    (fun s1 ⟨hn, hk⟩ ↦ ⟨by rw [rdU32, B_length P]; simp; omega, hk⟩)
  have hp1 : s1.reg .r15 = p.toUInt64 := by rw [hf1 .r15 (by simp), hp]
  refine WP.blk_cons (WP.mono (rdLE_ok P h1 (by norm_num) (by norm_num) hp1 hn)
    (fun s2 ⟨h2, hb, hr, hf2⟩ ↦ WP.blk_nil ⟨leNat e.B p 4, ?_, ?_, h2, hb, hr, ?_⟩) (fun _ h ↦ h))
  · rw [rdU32, B_length P]; simp [hn]
  · exact lt_of_lt_of_le (leNat_lt _ _ _) (by norm_num)
  · exact RegsFrame.trans (RegsFrame.mono hf1 (by simp)) hf2

end Gadgets

end NativeVm.Wire
