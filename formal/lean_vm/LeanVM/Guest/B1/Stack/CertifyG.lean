/-
  LeanVM.Guest.B1.Stack.CertifyG

  What `certify_stack`'s template computes, group by group: the kappas, the rank keys, the sizes.
-/

module

public import LeanVM.Guest.B1.Stack.CertifyT
public import LeanVM.Guest.ExpTables
public import LeanVM.Guest.B1.Bits.SmallGPower
import LeanVM.Guest.Value.FieldBits

/-!
# `certify_stack`'s groups

On the kappa sources `g^(kv i)` at `kappa_base` (`kvOf`: `0`, the memory's log, the heights), group
`gi`'s `κ` is `csKap kv gi = kv src + adj` (`csKappa_val`), and `csKey`'s statements give
(`csKey_sound`): `κ < 34`, the rank key at `group_key[gi]` times `g^b0` is `g^(53 κ)`, and the size
at `group_size[gi]` is `g^(len·2^κ)`.
-/

namespace LeanVM.Guest.B1.Stack

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- Group `gi`'s `κ`, from the kappa sources' exponents `kv`. -/
def csKap (kv : ℕ → ℕ) (gi : ℕ) : ℕ := kv (csG gi).src + (csG gi).adj

theorem csGroups_facts : ∀ gi < 8, (csG gi).src < 8 ∧ (csG gi).adj < 7 ∧ 1 ≤ (csG gi).len ∧
    (csG gi).len ≤ 14 ∧ digitsVal (osPowDigits (csG gi).len) 1 = (csG gi).len := by
  decide

theorem digits53 : digitsVal (osPowDigits 53) 1 = 53 := by decide

set_option maxRecDepth 100000 in
theorem csInv_eq : ∀ gi < 8, (csG gi).b0 ≠ 0 → word (csG gi).inv 0 * gen ^ (csG gi).b0 = 1 := by
  intro gi hgi hb
  interval_cases gi <;> simp only [csG, csGroups, List.getD_cons_zero, List.getD_cons_succ] at hb ⊢
  all_goals first
    | exact absurd rfl hb
    | (rw [show ∀ n : ℕ, word n 0 = ofK (K.ofBits n) from fun n ↦ word_eOfNat n, gen_pow_eq_ofK,
          ← ofK_mul, ← ofK_one]; congr 1)

theorem csW_eq {e : ℕ} (h : e < 64) : csW e = gen ^ e := word_two_pow h

/-- **Group `g`'s `κ`**: `kb[src]·g^adj`. -/
theorem csKappa_val (kv : ℕ → ℕ) (hkb : ∀ i < 8, σ (.n (2 + i)) = gen ^ kv i) {g : CsGroup}
    (hs : g.src < 8) (ha : g.adj < 64) (s : ℕ) (h : AllOk C rd σ (csKappa g s).1) :
    σ (.n (csKappa g s).2.1) = gen ^ (kv g.src + g.adj) := by
  by_cases h0 : g.adj = 0
  · simp only [csKappa, h0, ↓reduceIte, Nat.add_zero] at h ⊢
    exact hkb _ hs
  · simp only [csKappa, h0, ↓reduceIte, osCst, osMul, allOk_cons, allOk_nil, and_true, StmtOk,
      Atom.Holds] at h ⊢
    obtain ⟨e0, e1⟩ := h
    rw [e1, e0, hkb _ hs, csW_eq ha, ← pow_add]

/-- **Group `gi`'s key and size**: on a memory image of at least `2^6` words, `κ < 34`, the key
at `group_key[gi]` times `g^b0` is `g^(53 κ)`, and the size at `group_size[gi]` is
`g^(len·2^κ)`. -/
theorem csKey_sound {κ : ℕ} (hκ : κ ≤ 32) (hκ6 : 6 ≤ κ) (L : MemoryImage κ) (kv : ℕ → ℕ)
    (hkv : ∀ i < 8, kv i < 2 ^ 40) (hkb : ∀ i < 8, σ (.n (2 + i)) = gen ^ kv i)
    (ht : ExpTables L.read (σ (.n 1))) {gi : ℕ} (hgi : gi < 8) (s : ℕ)
    (h : AllOk C L.read σ (csKey gi s).1) :
    csKap kv gi < 34 ∧
      (∃ key, LoadHolds L.read (σ (.n 10)) gi key ∧ key * gen ^ (csG gi).b0 = gen ^ (53 * csKap kv gi)) ∧
      LoadHolds L.read (σ (.n 11)) gi (gen ^ ((csG gi).len * 2 ^ csKap kv gi)) := by
  obtain ⟨hsrc, hadj, hl1, hl14, hdig⟩ := csGroups_facts gi hgi
  unfold csKey at h
  simp only [allOk_append, allOk_cons, allOk_nil, and_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hkp, hc33, hrc⟩, hch⟩, hkey⟩, hstk, hm, hld⟩, hsz⟩, hssz⟩ := h
  set kp := csKappa (csG gi) s with hkp_def
  have hv := csKappa_val kv hkb hsrc (by omega) s hkp
  -- the range check
  simp only [StmtOk, Atom.Holds] at hc33
  simp only [csRc, StmtOk, Atom.Holds] at hrc
  obtain ⟨r1, r2, r3⟩ := hrc
  obtain ⟨e, he, hve⟩ := (rangeCheck_gen_iff hκ L _ (K := 34) (by decide)
    (le_trans (by decide) (Nat.pow_le_pow_right (by decide) hκ6)) (by decide)).1
    ⟨_, _, _, r1, by rw [← r2, hc33]; rfl, r3⟩
  rw [hv] at hve
  have hkapl : kv (csG gi).src + (csG gi).adj < 2 ^ 64 - 1 := by
    have := hkv _ hsrc; omega
  have hke : kv (csG gi).src + (csG gi).adj = e :=
    gen_pow_inj hkapl (by omega) hve
  have hk34 : csKap kv gi < 34 := by unfold csKap; omega
  refine ⟨hk34, ?_, ?_⟩
  · -- the key
    have hc := osPowSteps_val (C := C) (rd := L.read) (σ := σ) kp.2.1 (osPowDigits 53) kp.2.1
      (kp.2.2 + 4) 1 (by rw [pow_one]) hch
    rw [digits53, hv] at hc
    simp only [StmtOk, Atom.Holds] at hstk
    by_cases hb0 : (csG gi).b0 = 0
    · simp only [hb0, ↓reduceIte] at hstk hkey
      refine ⟨_, hstk, ?_⟩
      rw [hb0, pow_zero, mul_one, hc, ← pow_mul]
      congr 1; unfold csKap; ring
    · simp only [hb0, ↓reduceIte, osCst, osMul, allOk_cons, allOk_nil, and_true, StmtOk,
        Atom.Holds] at hstk hkey
      obtain ⟨k0, k1⟩ := hkey
      refine ⟨_, hstk, ?_⟩
      rw [k1, k0, hc, mul_assoc, csInv_eq gi hgi hb0, mul_one, ← pow_mul]
      congr 1; unfold csKap; ring
  · -- the size
    simp only [osMul, StmtOk, Atom.Holds] at hm hld hssz
    rw [hm, hv, loadHolds_mul_gen_pow, Nat.add_zero] at hld
    have hsq := loadHolds_unique hld (ht.1 _ (show csKap kv gi < sizeBits from hk34))
    have hz := osPowSteps_val (C := C) (rd := L.read) (σ := σ) _ (osPowDigits (csG gi).len) _ _ 1
      (by rw [pow_one]) hsz
    rw [hdig, hsq] at hz
    rw [hz, ← pow_mul, Nat.mul_comm] at hssz
    exact hssz

end
end LeanVM.Guest.B1.Stack
