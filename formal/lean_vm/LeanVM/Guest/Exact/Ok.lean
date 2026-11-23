/-
  LeanVM.Guest.Exact.Ok

  Functions whose every valid path is exact, their computed hints pinned inside their own bodies by more than the next
  atom (`PathExactFn`), closed under calls with the functions exact for free (`ExactOk`): every valid tree of one is
  exact (`every_exact_of_ok`).
-/

module

public import LeanVM.Guest.Exact.Free
public import LeanVM.Guest.Value.Bits

/-!
# Exact on every valid path

`PathExactFn fn`: every path of `fn`'s body holding on a memory is exact on it. It holds of a body whose computed hints
are pinned by the next atom but a list of sites, each exact on every path that holds (`pathExact_of_sites`), as a
`bits` hint whose words are its word's bits (`bits_exact_of_eq`).

`ExactOk`: the least set holding the functions exact for free (`exactFree`) and every function whose body is
`PathExactFn` and whose callees are itself or in the set. It is call-closed with exact paths
(`coreProgram_exactOkIn`), so every valid tree of one of its functions is exact (`every_exact_of_ok`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat kToNat gen)

@[expose] public section

/-- **Every path of the body that holds is exact**, on the memory it holds on. -/
def PathExactFn (fn : Fn) : Prop :=
  ∀ (rd : Reader) (σ : Val) (es : List Ev) (vs : List V), walk σ fn.body = .ret es vs →
    (∀ e ∈ es, e.Holds rd σ) → ∀ e ∈ es, e.Exact rd σ

/-- A body whose computed hints are pinned by the next atom but `sites`, each exact on every path that holds. -/
theorem pathExact_of_sites {fn : Fn} {sites : List Atom}
    (hpin : Stmt.blockNextOk (fun a => isComputed a && !decide (a ∈ sites)) pinsInverse fn.body = true)
    (h : ∀ (rd : Reader) (σ : Val) (es : List Ev) (vs : List V), walk σ fn.body = .ret es vs →
      (∀ e ∈ es, e.Holds rd σ) → ∀ a ∈ sites, Ev.atom a ∈ es → a.Exact rd σ) : PathExactFn fn :=
  fun rd σ es vs hw hes => exact_of_sites hpin hw hes (h rd σ es vs hw hes)

/-- **The functions exact on every valid tree**: those exact for free, and those whose paths are exact calling only
themselves or functions of the set. -/
inductive ExactOk : String → Prop
  | free {g : String} : ExactFreeG g → ExactOk g
  | node {g : String} {fn : Fn} : coreProgram.find? g = some fn → PathExactFn fn →
      (∀ g' ∈ Stmt.blockCallees fn.body, g' ≠ g → ExactOk g') → ExactOk g

/-- **`ExactOk` is call-closed and its paths that hold are exact.** -/
theorem coreProgram_exactOkIn (rd : Reader) :
    coreProgram.EveryIn rd (fun f σ => ExactAt coreProgram rd f σ) ExactOk := by
  intro f hf fn hfn
  cases hf with
  | free hg =>
    obtain ⟨hc, hq⟩ := coreProgram_exactIn rd f hg fn hfn
    exact ⟨fun g hg' => .free (hc g hg'), fun σ es vs hw hes => hq σ es vs hw hes rd⟩
  | node hfind hpe hcal =>
    rw [hfind] at hfn
    cases hfn
    refine ⟨fun g hg => ?_, fun σ es vs hw hes => exactAt_of_walk hfind hw (hpe rd σ es vs hw hes)⟩
    by_cases e : g = f
    · subst e; exact .node hfind hpe hcal
    · exact hcal g hg e

/-- **A valid tree of a function of `ExactOk` is exact** on its memory. -/
theorem every_exact_of_ok {rd : Reader} {g : String} (hg : ExactOk g) {t : Tree} {args rets : List E}
    (hv : t.Valid coreProgram rd args rets) (hn : t.name = g) : t.Every (ExactAt coreProgram rd) :=
  every_of_everyIn (coreProgram_exactOkIn rd) t hv (hn ▸ hg)

/-! ## Bits rebuilding their word -/

theorem wordNat_eOfNat {N : ℕ} (hN : N < 2 ^ 64) : LeanVM.Prover.Exec.wordNat (eOfNat N) = N := by
  have e : LeanVM.Prover.Exec.wordNat (eOfNat N) = kToNat ((eOfNat N).limb 0) + 2 ^ 64 * kToNat ((eOfNat N).limb 1) :=
    rfl
  rw [e, eOfNat_eq_ofLimbs, ofLimbs_limb0, ofLimbs_limb1, kToNat_ofBits, Nat.mod_eq_of_lt hN,
    show (0 : K) = K.ofBits 0 from rfl, kToNat_ofBits]
  simp

theorem bitE_eq_bitWord (b : Bool) : bitE b = LeanVM.Prover.Exec.bitWord b := by
  cases b <;> rfl

/-- **A `bits` hint from bit `0` is exact** when its word is `E(N)` and its words are `N`'s bits. -/
theorem bits_exact_of_eq {rd : Reader} {σ : Val} {v : V} {nbits : ℕ} {ds : List V} {N : ℕ} (hN : N < 2 ^ 64)
    (hv : σ v = eOfNat N) (hds : ds.map σ = (List.range nbits).map fun j => bitE (N.testBit j)) :
    (Hint.bits v 0 nbits (.stack ds)).Exact rd σ := by
  show ds.map σ = _
  rw [hds, hv, wordNat_eOfNat hN]
  exact List.map_congr_left fun j _ => by rw [Nat.zero_add, bitE_eq_bitWord]

/-- **A `bits` hint from bit `0` is exact** when its words are Boolean and rebuild its word, `n ≤ 64` of them. -/
theorem bits_exact_of_sum {rd : Reader} {σ : Val} {v : V} {nbits : ℕ} {ds : List V} (b : ℕ → E) (hn : nbits ≤ 64)
    (hds : ds.map σ = (List.range nbits).map b) (hb : ∀ j < nbits, b j * b j = b j)
    (hv : σ v = ∑ j ∈ Finset.range nbits, b j * gen ^ j) : (Hint.bits v 0 nbits (.stack ds)).Exact rd σ := by
  have hx : ∑ j ∈ Finset.range nbits, b j * coordBasis (0 + j) = σ v := by
    rw [hv]
    exact Finset.sum_congr rfl fun j hj => by
      have := Finset.mem_range.mp hj
      rw [Nat.zero_add, coordBasis_of_lt (by omega), gen_pow_eq_eOfNat (by omega)]
  obtain ⟨N, hN, hxv, hbits⟩ := bits_of_reconstruct hb hx
  have hN64 : N < 2 ^ 64 := lt_of_lt_of_le hN (Nat.pow_le_pow_right (by decide) hn)
  rw [Nat.pow_zero, Nat.one_mul, eOfNat128_of_lt hN64] at hxv
  exact bits_exact_of_eq hN64 hxv (by
    rw [hds]; exact List.map_congr_left fun j hj => hbits j (List.mem_range.mp hj))

/-- **A `bitsExp` hint is exact** when its words are Boolean and their product of factors `1 + b_j·(g^(2^j) + 1)` is
its word. -/
theorem bitsExp_exact_of_prod {rd : Reader} {σ : Val} {v : V} {nbits : ℕ} {ds : List V} (b : ℕ → E)
    (hds : ds.map σ = (List.range nbits).map b) (hb : ∀ j < nbits, b j * b j = b j)
    (hv : σ v = ∏ j ∈ Finset.range nbits, (1 + b j * (gen ^ 2 ^ j + 1))) :
    (Hint.bitsExp v nbits (.stack ds)).Exact rd σ := by
  refine ⟨bitsVal (fun j ↦ decide (b j = 1)) nbits, bitsVal_lt _ _, by
    rw [hv, prod_gen_pow_of_bool hb, gen_pow_eq_ofK], ?_⟩
  show ds.map σ = _
  rw [hds]
  refine List.map_congr_left fun j hj => ?_
  have hj : j < nbits := List.mem_range.mp hj
  rw [testBit_bitsVal, decide_eq_true hj, Bool.true_and, ← bitE_eq_bitWord]
  exact bitE_of_mul_self (hb j hj)

/-- A Boolean factor raised to the fourth power. -/
theorem bitFactor_pow4 {b : E} (hb : b * b = b) (j : ℕ) :
    (((1 + b * (gen ^ 2 ^ j + 1)) ^ 2) ^ 2) = 1 + b * (gen ^ 2 ^ (j + 2) + 1) := by
  rw [bitE_of_mul_self hb]
  cases decide (b = 1)
  · simp [bitE]
  · simp only [bitE, ↓reduceIte, one_mul]
    have e : ∀ x : E, 1 + (x + 1) = x := fun x => by rw [add_comm x 1, ← add_assoc, e_add_self, zero_add]
    rw [e, e, ← pow_mul, ← pow_mul, pow_succ 2 (j + 1), pow_succ 2 j]
    ring_nf

/-- A Boolean factor raised to the eighth power. -/
theorem bitFactor_pow8 {b : E} (hb : b * b = b) (j : ℕ) :
    ((((1 + b * (gen ^ 2 ^ j + 1)) ^ 2) ^ 2) ^ 2) = 1 + b * (gen ^ 2 ^ (j + 3) + 1) := by
  rw [bitE_of_mul_self hb]
  cases decide (b = 1)
  · simp [bitE]
  · simp only [bitE, ↓reduceIte, one_mul]
    have e : ∀ x : E, 1 + (x + 1) = x := fun x => by rw [add_comm x 1, ← add_assoc, e_add_self, zero_add]
    rw [e, e, ← pow_mul, ← pow_mul, ← pow_mul, pow_succ 2 (j + 2), pow_succ 2 (j + 1), pow_succ 2 j]
    ring_nf

end
end LeanVM.Guest.Memory
