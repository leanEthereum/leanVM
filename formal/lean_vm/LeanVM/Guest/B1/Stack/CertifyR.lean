/-
  LeanVM.Guest.B1.Stack.CertifyR

  What `certify_stack`'s ranks compute: the hinted order, the keys' descent, the running totals.
-/

module

public import LeanVM.Guest.B1.Stack.CertifyG
public import LeanVM.Guest.B1.Bits.Log2
import LeanVM.Guest.Value.FieldBits

/-!
# `certify_stack`'s ranks

Rank `r` reads its group `ρ` from the hinted order (`g^ρ`, range checked below `g^8`), the group's
key at `group_key[ρ]`, stores the running total at `group_at[ρ]` and multiplies the total by the
group's size at `group_size[ρ]` (`csRank0_sound`, `csRank_sound`). Past rank `0` the previous key
is `g^(e + 1)` times this one, `e < 1802` (`csBound`, `g^1801`, the range check's bound).
-/

namespace LeanVM.Guest.B1.Stack

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {σ : Val}

set_option maxRecDepth 100000 in
theorem csBound_eq : csBound = ofK (addressOfIndex 1801) := by
  rw [← gen_pow_eq_ofK, ← gw_eq (by decide)]
  rfl

theorem csInvGen_mul_gen : csInvGen * gen = 1 := by
  rw [mul_comm]; exact gen_mul_invGenWord

/-- A range check below `g^K`, `K ≤ 2^κ`, its bound's word `ofK (g^(K-1))`. -/
theorem csRc_gen {κ : ℕ} (hκ : κ ≤ 32) (L : MemoryImage κ) {x h k : ℕ} {K : ℕ} (hK1 : 1 ≤ K)
    (hK : K ≤ 2 ^ κ) (hk : σ (.n k) = ofK (addressOfIndex (K - 1)))
    (hrc : StmtOk C L.read σ (csRc x h k)) : ∃ e < K, σ (.n x) = gen ^ e := by
  simp only [csRc, StmtOk, Atom.Holds] at hrc
  obtain ⟨r1, r2, r3⟩ := hrc
  obtain ⟨e, he, hx⟩ := (rangeCheck_iff hκ L _ hK1 hK).1 ⟨_, _, _, r1, by rw [← hk, r2], r3⟩
  exact ⟨e, he, by rw [hx, gen_pow_eq_ofK]⟩

/-- **Rank `0`**: its group `ρ < 8`, its key, `group_at[ρ] = 1`, the total its size. -/
theorem csRank0_sound {κ : ℕ} (hκ : κ ≤ 32) (hκ3 : 3 ≤ κ) (L : MemoryImage κ) (ord at_ s0 : ℕ)
    (h : AllOk C L.read σ ([.atom (.load (.n s0) (.n ord) 0), osCst (s0 + 1) (csW 7),
      csRc s0 (s0 + 2) (s0 + 1), osMul (s0 + 5) 10 s0, .atom (.load (.n (s0 + 6)) (.n (s0 + 5)) 0),
      osCst (s0 + 7) (word 1 0), osMul (s0 + 8) at_ s0, .atom (.load (.n (s0 + 7)) (.n (s0 + 8)) 0),
      osMul (s0 + 9) 11 s0, .atom (.load (.n (s0 + 10)) (.n (s0 + 9)) 0)] : List Stmt)) :
    ∃ ρ < 8, LoadHolds L.read (σ (.n ord)) 0 (gen ^ ρ) ∧
      LoadHolds L.read (σ (.n 10)) ρ (σ (.n (s0 + 6))) ∧ LoadHolds L.read (σ (.n at_)) ρ 1 ∧
      LoadHolds L.read (σ (.n 11)) ρ (σ (.n (s0 + 10))) := by
  simp only [allOk_cons, allOk_nil, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  simp only [StmtOk, Atom.Holds] at h0 h1 h3 h4 h5 h6 h7 h8 h9
  obtain ⟨ρ, hρ, hx⟩ := csRc_gen hκ L (x := s0) (h := s0 + 2) (k := s0 + 1) (K := 8) (by decide)
    (le_trans (show 8 ≤ 2 ^ 3 by decide) (Nat.pow_le_pow_right (by decide) hκ3))
    (by rw [h1, csW_eq (by decide), gen_pow_eq_ofK]) h2
  rw [hx] at h0 h3 h6 h8
  rw [h3, loadHolds_mul_gen_pow, Nat.add_zero] at h4
  rw [h6, loadHolds_mul_gen_pow, Nat.add_zero, h5, word_one] at h7
  rw [h8, loadHolds_mul_gen_pow, Nat.add_zero] at h9
  exact ⟨ρ, hρ, h0, h4, h7, h9⟩

/-- **Rank `r`**, past rank `0`: its group `ρ < 8`, its key, under which the previous key `pk`
falls by `g^(e + 1)`, `e < 1802`, `group_at[ρ]` the total `tot`, the total times its size. -/
theorem csRank_sound {κ : ℕ} (hκ : κ ≤ 32) (hκ11 : 11 ≤ κ) (L : MemoryImage κ)
    (ord at_ s pk tot r : ℕ) (h : AllOk C L.read σ (csRank ord at_ s pk tot r)) :
    ∃ ρ < 8, LoadHolds L.read (σ (.n ord)) r (gen ^ ρ) ∧
      LoadHolds L.read (σ (.n 10)) ρ (σ (.n (s + 6))) ∧
      (∃ e < 1802, σ (.n pk) = gen ^ (e + 1) * σ (.n (s + 6))) ∧
      LoadHolds L.read (σ (.n at_)) ρ (σ (.n tot)) ∧
      LoadHolds L.read (σ (.n 11)) ρ (σ (.n (s + 16))) ∧
      σ (.n (s + 17)) = σ (.n tot) * σ (.n (s + 16)) := by
  unfold csRank at h
  simp only [allOk_cons, allOk_nil, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  simp only [StmtOk, Atom.Holds] at h0 h1 h3 h4 h5 h6 h7 h8 h10 h11 h12 h13 h14
  obtain ⟨ρ, hρ, hx⟩ := csRc_gen hκ L (x := s) (h := s + 2) (k := s + 1) (K := 8) (by decide)
    (le_trans (show 8 ≤ 2 ^ 3 by decide) (Nat.pow_le_pow_right (by decide) (show 3 ≤ κ by omega)))
    (by rw [h1, csW_eq (by decide), gen_pow_eq_ofK]) h2
  obtain ⟨e, he, hy⟩ := csRc_gen hκ L (x := s + 10) (h := s + 11) (k := s + 7) (K := 1802) (by decide)
    (le_trans (show 1802 ≤ 2 ^ 11 by decide) (Nat.pow_le_pow_right (by decide) hκ11))
    (by rw [h5, csBound_eq]) h9
  rw [hx] at h0 h3 h10 h12
  rw [h3, loadHolds_mul_gen_pow, Nat.add_zero] at h4
  rw [h10, loadHolds_mul_gen_pow, Nat.add_zero] at h11
  rw [h12, loadHolds_mul_gen_pow, Nat.add_zero] at h13
  refine ⟨ρ, hρ, h0, h4, ⟨e, he, ?_⟩, h11, h13, h14⟩
  have hx8 : σ (.n (s + 8)) = gen ^ (e + 1) := by
    have : σ (.n (s + 8)) * csInvGen * gen = gen ^ e * gen := by rw [← h7, ← h8, hy]
    rw [mul_assoc, csInvGen_mul_gen, mul_one] at this
    rw [this, pow_succ]
  rw [h6, hx8]

end
end LeanVM.Guest.B1.Stack
