/-
  LeanVM.Guest.B1.Sig.SphincsBytes

  `sp_from_bytes` (`lean_ethereum.py`) is sound: on a memory image of
  at most `2^32` words holding the byte table, its value is a word below `256^n`.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsDigestT
public import LeanVM.Guest.B1.Sig.InterfaceP

/-!
# `sp_from_bytes`, sound

* `range_sound`: a range check against `g^(K-1)` passes only for `x = g^e`, `e < K`, on a memory of
  at most `2^32` words (`rangeCheck_iff`'s soundness half, for any `K ≤ 2^32`);
* `sByte_sound`: a byte mark range checked below `256` and read off the byte table is the word
  `e < 256`;
* `sFromBytesRest_sound`, `sFromBytes_sound`, `sFromMarks_sound`: the folded value is a word below
  `256^bytes`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {σ : Val}

/-- **A range check, sound**: against `g^(K-1)`, on a memory image of at most `2^32` words, the
value is `g^e` for some `e < K`. -/
theorem range_sound {κ : Nat} (hκ : κ ≤ 32) (L : MemoryImage κ) {x y t1 t2 : E} {K : Nat}
    (hK : 1 ≤ K) (hK' : K ≤ 2 ^ 32) (h1 : LoadHolds L.read x 0 t1) (hk : ofK (addressOfIndex (K -
        1)) = x * y)
    (h2 : LoadHolds L.read y 0 t2) : ∃ e < K, x = ofK (addressOfIndex e) := by
  have hκ64 : κ < 64 := by omega
  have h32 : 2 ^ κ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hκ
  obtain ⟨hx, h1⟩ := h1
  obtain ⟨hy, h2⟩ := h2
  rw [addressOfIndex, pow_zero, mul_one] at h1 h2
  obtain ⟨i, hi, -⟩ := (read_some_iff hκ64 L _ _).mp h1
  obtain ⟨j, hj, -⟩ := (read_some_iff hκ64 L _ _).mp h2
  have ex : x = ofK (addressOfIndex i) := by rw [eq_ofK_limb hx, hi]
  have ey : y = ofK (addressOfIndex j) := by rw [eq_ofK_limb hy, hj]
  rw [ex, ey, ← ofK_mul, addressOfIndex, addressOfIndex, ← pow_add] at hk
  have hij := gpow_injOn (by have := i.isLt; have := j.isLt; simp only [Set.mem_Iio]; omega)
    (by simp only [Set.mem_Iio]; omega) (ofK_injective hk).symm
  exact ⟨i, by omega, ex⟩

theorem g255W_eq : g255W = ofK (addressOfIndex 255) := by
  rw [g255W, word, Value.ofBits_zero, ← ofK_eq_ofLimbs]
  exact congrArg ofK (by decide +kernel)

/-- **A byte, sound**: a mark range checked below `256` and read off the byte table at
`σ (.n 1)` is the word of its exponent. -/
theorem sByte_sound {κ : Nat} (hκ : κ ≤ 32) {L : MemoryImage κ} {mark : V} {b : Nat}
    (hbb : ByteBits L.read (σ (.n 1))) (h : AtomsHold L.read σ (sByte mark b)) :
    ∃ e < 256, σ (.n (b + 5)) = eOfNat e ∧ σ mark = ofK (addressOfIndex e) := by
  have hK : 1 ≤ 256 := by norm_num
  have c : σ (.n b) = g255W := h.atom (a := .const (.n b) g255W) (by simp [sByte, rangeS, cst])
  have r := h.atom (a := .rangeCheck mark (.n (b + 1)) (.n (b + 2)) (.n (b + 3)) (.n b))
    (by simp [sByte, rangeS])
  have m : σ (.n (b + 4)) = σ (.n 1) * σ mark :=
    h.atom (a := .mul (.n (b + 4)) (.n 1) mark) (by simp [sByte, mulS])
  have l : LoadHolds L.read (σ (.n (b + 4))) 0 (σ (.n (b + 5))) :=
    h.atom (a := .load (.n (b + 5)) (.n (b + 4)) 0) (by simp [sByte, loadS])
  obtain ⟨r1, r2, r3⟩ := r
  rw [c, g255W_eq] at r2
  obtain ⟨e, he, hm⟩ := range_sound hκ L hK (by omega) r1 r2 r3
  obtain ⟨hbbK, hbbv⟩ := hbb e (by omega)
  obtain ⟨-, hl⟩ := l
  have hp : σ (.n (b + 4)) = ofK ((σ (.n 1)).limb 0 * addressOfIndex e) := by
    rw [m, hm, ofK_mul, ← eq_ofK_limb hbbK]
  have hl0 : (ofK ((σ (.n 1)).limb 0 * addressOfIndex e)).limb 0 = (σ (.n 1)).limb 0 *
      addressOfIndex e := by simp
  rw [hp, hl0] at hl
  simp only [addressOfIndex, pow_zero, mul_one] at hl hbbv
  refine ⟨e, he, ?_, hm⟩
  rw [hbbv] at hl
  rw [← word_eq_eOfNat]
  exact (Option.some.inj hl).symm

theorem word256_eq : word 256 0 = eOfNat (2 ^ 8) := word_eq_eOfNat 256

/-- **The bytes after the top one, folded**: from a word below `M`, a word below `M · 256^n`. -/
theorem sFromBytesRest_sound {κ : Nat} (hκ : κ ≤ 32) {L : MemoryImage κ}
    (hbb : ByteBits L.read (σ (.n 1))) :
    ∀ (ms : List V) (b : Nat) (val : V) (N M : Nat), σ val = eOfNat N → N < M →
      M * 256 ^ ms.length ≤ 2 ^ 64 → AtomsHold L.read σ (sFromBytesRest ms b val).1 →
      ∃ N', σ (sFromBytesRest ms b val).2.2 = eOfNat N' ∧ N' < M * 256 ^ ms.length
  | [], _, _, N, M, hv, hN, _, _ => ⟨N, hv, by simpa using hN⟩
  | m :: ms, b, val, N, M, hv, hN, hM, h => by
      have h' : AtomsHold L.read σ (sByte m b ++ [cst (b + 6) (word 256 0),
          mulS (.n (b + 7)) val (.n (b + 6)), addS (.n (b + 8)) (.n (b + 5)) (.n (b + 7))] ++
          (sFromBytesRest ms (b + 9) (.n (b + 8))).1) := h
      obtain ⟨e, he, hb, -⟩ := sByte_sound hκ hbb h'.left.left
      have c : σ (.n (b + 6)) = word 256 0 :=
        h'.left.right.atom (a := .const (.n (b + 6)) _) (by simp [cst])
      have mu : σ (.n (b + 7)) = σ val * σ (.n (b + 6)) :=
        h'.left.right.atom (a := .mul (.n (b + 7)) val (.n (b + 6))) (by simp [mulS])
      have ad : σ (.n (b + 8)) = σ (.n (b + 5)) + σ (.n (b + 7)) :=
        h'.left.right.atom (a := .add (.n (b + 8)) (.n (b + 5)) (.n (b + 7))) (by simp [addS])
      have hpow : 256 ^ (ms.length + 1) = 256 ^ ms.length * 256 := pow_succ _ _
      have hM1 : 1 ≤ 256 ^ ms.length := Nat.one_le_pow _ _ (by norm_num)
      have hM256 : M * 256 ≤ 2 ^ 64 := by
        simp only [List.length_cons, hpow] at hM
        nlinarith
      have hv8 : σ (.n (b + 8)) = eOfNat (2 ^ 8 * N + e) := by
        rw [ad, mu, c, hv, hb, word256_eq, mul_comm, eOfNat_two_pow_mul (by omega), add_comm,
          Value.eOfNat_add_of_lt (by omega)]
      obtain ⟨N', h1, h2⟩ := sFromBytesRest_sound hκ hbb ms (b + 9) (.n (b + 8)) (2 ^ 8 * N + e)
        (M * 256) hv8 (by omega) (by simp only [List.length_cons, hpow] at hM; linarith) h'.right
      refine ⟨N', h1, ?_⟩
      simp only [List.length_cons, hpow]
      linarith

/-- **`sp_from_bytes`, sound**: the value is a word below `256^n`, `n` the bytes. -/
theorem sFromBytes_sound {κ : Nat} (hκ : κ ≤ 32) {L : MemoryImage κ} (hbb : ByteBits L.read (σ (.n 1)))
    {top : V} {rest : List V} {b : Nat} (hM : 256 ^ (rest.length + 1) ≤ 2 ^ 64)
    (h : AtomsHold L.read σ (sFromBytes top rest b).1) :
    ∃ N, σ (sFromBytes top rest b).2.2 = eOfNat N ∧ N < 256 ^ (rest.length + 1) := by
  have h' : AtomsHold L.read σ (sByte top b ++ (sFromBytesRest rest (b + 6) (.n (b + 5))).1) := h
  obtain ⟨e, he, hb, -⟩ := sByte_sound hκ hbb h'.left
  obtain ⟨N, h1, h2⟩ := sFromBytesRest_sound hκ hbb rest (b + 6) (.n (b + 5)) e 256 hb he
    (by rwa [pow_succ, mul_comm] at hM) h'.right
  exact ⟨N, h1, by rwa [pow_succ, mul_comm]⟩

theorem sMarks_length (b n : Nat) : (sMarks b n).2.length = n - 1 := by simp [sMarks]

/-- **`sp_from_bytes` of `n ≤ 8` hinted bytes, sound**: a word below `2^(8 n)`. -/
theorem sFromMarks_sound {κ : Nat} (hκ : κ ≤ 32) {L : MemoryImage κ} (hbb : ByteBits L.read (σ (.n 1)))
    {b n x : Nat} (hn : 1 ≤ n) (hn8 : n ≤ 8) (h : AtomsHold L.read σ (sFromMarks b n x).1) :
    ∃ N, σ (sFromMarks b n x).2.2 = eOfNat N ∧ N < 2 ^ (8 * n) := by
  have hl : (sMarks b n).2.length + 1 = n := by rw [sMarks_length]; omega
  obtain ⟨N, h1, h2⟩ := sFromBytes_sound hκ hbb (top := (sMarks b n).1) (rest := (sMarks b n).2) (b := x)
    (by rw [hl, show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)) h
  refine ⟨N, h1, ?_⟩
  rwa [hl, show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul] at h2

end
end LeanVM.Guest.B1.Sig
