/-
  LeanVM.Protocol.Whir.Sound.Queries

  The query positions of the deployed WHIR verifier are i.i.d. uniform: `sample_queries` cuts each
  uniform 192-bit sample into disjoint chunks of `depth` bits, so all `t` positions land in a set
  of `a` columns with probability at most `(a / 2^depth)^t`.
-/

module

public import LeanVM.Protocol.Whir.Sound.Prob
public import LeanVM.Protocol.ToArkLib.Whir.Counting

/-!
# Uniformity of the query positions

`sample_queries(transcript, 2^depth, t)` (`python-verifier/verifier.py:945-953` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`, `LeanVM.Protocol.Verifier.sampleQueries`) draws
samples `c ∈ E` and reads `int(c)` (`eToNat`, the three limbs as one 192-bit integer); the chunks
`(int(c) >> (k·depth)) mod 2^depth`, `k < min(192/depth, remaining)`, are the positions.

* `eNatEquiv`: `eToNat` is a bijection `E ≃ [0, 2^192)` (three independent 64-bit limbs).
* `card_chunks`: of the `2^192` samples, exactly `2^(192 − n·depth)·a^n` have their first `n`
  chunks in a set `S` with `a` elements in `[0, 2^depth)`, for `n·depth ≤ 192`.
* `retExp_sampleQueries_le`: the probability that all `t` positions land in `S` is at most
  `(a / 2^depth)^t`, for `1 ≤ depth ≤ 192`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier Prog Finset
  LeanVM.Protocol.Whir

@[expose] public section

/-! ## `int(e)` is uniform on `[0, 2^192)` -/

/-- The limbs of a word as `64`-bit digits. -/
def limbDigits (e : E) : Fin 3 → Fin (2 ^ 64) := fun i ↦ (e.limb i).toBitVec.toFin

theorem limbDigits_injective : Function.Injective limbDigits := by
  intro e e' h
  refine E.ext fun i ↦ ?_
  have := congrFun h i
  simp only [limbDigits] at this
  exact BF64.toBitVec_injective (BitVec.toFin_inj.mp this)

/-- `int(e)` as a digit expansion. -/
theorem eToNat_eq (e : E) : eToNat e = (finFunctionFinEquiv (limbDigits e) : ℕ) := by
  rw [finFunctionFinEquiv_apply, Fin.sum_univ_three]
  simp only [eToNat, kToNat, limbDigits, BitVec.val_toFin, Fin.val_zero, Fin.val_one, Fin.val_two]
  ring

/-- **`int` is a bijection `E ≃ [0, 2^192)`.** -/
noncomputable def eNatEquiv : E ≃ Fin ((2 ^ 64) ^ 3) :=
  Equiv.ofBijective (fun e ↦ finFunctionFinEquiv (limbDigits e))
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨finFunctionFinEquiv.injective.comp limbDigits_injective, by
        rw [card_E, Fintype.card_fin]; norm_num⟩)

theorem eNatEquiv_val (e : E) : (eNatEquiv e : ℕ) = eToNat e := by
  rw [eToNat_eq]; rfl

/-! ## Counting chunks -/

/-- Chunk `k` of `depth` bits of `x`. -/
def chunk (depth k x : ℕ) : ℕ := x / 2 ^ (k * depth) % 2 ^ depth

theorem chunk_eq_shiftRight (depth k x : ℕ) :
    (x >>> (k * depth)) % 2 ^ depth = chunk depth k x := by
  rw [Nat.shiftRight_eq_div_pow]; rfl

/-- The chunks of `x` below `n` digits are its base-`2^depth` digits. -/
theorem chunk_eq_digit (depth k x : ℕ) : chunk depth k x = x / (2 ^ depth) ^ k % 2 ^ depth := by
  rw [chunk, ← pow_mul, mul_comm]

/-- Adding a multiple of `(2^depth)^n` does not change the chunks below `n`. -/
theorem chunk_add_mul {depth n k : ℕ} (hk : k < n) (y u : ℕ) :
    chunk depth k (y + (2 ^ depth) ^ n * u) = chunk depth k y := by
  rw [chunk_eq_digit, chunk_eq_digit]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
  rw [show (2 ^ depth) ^ (k + j + 1) * u = (2 ^ depth) ^ k * ((2 ^ depth) ^ (j + 1) * u) by ring,
    Nat.add_mul_div_left _ _ (by positivity), pow_succ, show
      (2 ^ depth) ^ j * 2 ^ depth * u = 2 ^ depth * ((2 ^ depth) ^ j * u) by ring,
    Nat.add_mul_mod_self_left]

/-- **The chunk count**: exactly `2^(192 − n·depth)·a^n` samples have their first `n` chunks in
`S`, with `a` the number of elements of `S` below `2^depth`, for `n·depth ≤ 192`. -/
theorem card_chunks (depth n : ℕ) (hn : n * depth ≤ 192) (S : ℕ → Prop) [DecidablePred S] :
    (univ.filter fun e : E ↦ ∀ k < n, S (chunk depth k (eToNat e))).card =
      2 ^ (192 - n * depth) * (univ.filter fun j : Fin (2 ^ depth) ↦ S j).card ^ n := by
  set M := 2 ^ depth
  set U := 2 ^ (192 - n * depth)
  have hUL : (2 ^ 64) ^ 3 = U * M ^ n := by
    simp only [U, M, ← pow_mul, ← pow_add]
    rw [Nat.mul_comm depth n, Nat.sub_add_cancel hn]
  let P : ℕ → Prop := fun x ↦ ∀ k < n, S (chunk depth k x)
  -- Transport to `Fin (U * M^n)`.
  have h1 : (univ.filter fun e : E ↦ P (eToNat e)).card =
      (univ.filter fun x : Fin (U * M ^ n) ↦ P x).card := by
    let eqv : E ≃ Fin (U * M ^ n) := eNatEquiv.trans (finCongr hUL)
    have hv : ∀ e, (eqv e : ℕ) = eToNat e := fun e ↦ by
      rw [Equiv.trans_apply, finCongr_apply, Fin.val_cast, eNatEquiv_val]
    rw [← Finset.card_map eqv.toEmbedding]
    congr 1
    ext x
    simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hv, Equiv.apply_symm_apply]
  -- Split into the high part and the `n` digits.
  have h2 : (univ.filter fun x : Fin (U * M ^ n) ↦ P x).card =
      U * (univ.filter fun y : Fin (M ^ n) ↦ P y).card := by
    have : (univ.filter fun x : Fin (U * M ^ n) ↦ P x) =
        (univ ×ˢ (univ.filter fun y : Fin (M ^ n) ↦ P y)).map finProdFinEquiv.toEmbedding := by
      ext x
      rw [Finset.mem_map_equiv, Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      conv_lhs => rw [← finProdFinEquiv.apply_symm_apply x, finProdFinEquiv_apply_val]
      exact forall₂_congr fun k hk ↦ by rw [chunk_add_mul hk]
    rw [this, Finset.card_map, Finset.card_product, Finset.card_univ, Fintype.card_fin]
  -- The digits are a function `Fin n → Fin M`.
  have h3 : (univ.filter fun y : Fin (M ^ n) ↦ P y).card =
      (univ.filter fun j : Fin M ↦ S j).card ^ n := by
    have : (univ.filter fun y : Fin (M ^ n) ↦ P y) =
        (univ.filter fun f : Fin n → Fin M ↦ ∀ k, f k ∈ univ.filter fun j : Fin M ↦ S j).map
          finFunctionFinEquiv.toEmbedding := by
      ext y
      rw [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, Finset.mem_filter, finFunctionFinEquiv_symm_apply_val,
        P, chunk_eq_digit]
      exact ⟨fun h k ↦ h k k.isLt, fun h k hk ↦ h ⟨k, hk⟩⟩
    rw [this, Finset.card_map, card_forall_mem_fin]
  change (univ.filter fun e : E ↦ P (eToNat e)).card = _
  rw [h1, h2, h3]

/-! ## The positions -/

/-- The indicator that all positions land in `S`. -/
noncomputable def allIn (S : ℕ → Prop) [DecidablePred S] (qs : List ℕ) : ENNReal :=
  if ∀ q ∈ qs, S q then 1 else 0

theorem allIn_append (S : ℕ → Prop) [DecidablePred S] (a b : List ℕ) :
    allIn S (a ++ b) = allIn S a * allIn S b := by
  unfold allIn
  simp only [List.forall_mem_append]
  split_ifs <;> simp_all

/-- One sample: the probability that its `n` chunks land in `S`. -/
theorem avg_chunks (depth n : ℕ) (hn : n * depth ≤ 192) (S : ℕ → Prop) [DecidablePred S] :
    (Fintype.card E : ENNReal)⁻¹ * ∑ c : E,
        allIn S ((List.range n).map fun k ↦ (eToNat c >>> (k * depth)) % 2 ^ depth) =
      ((univ.filter fun j : Fin (2 ^ depth) ↦ S j).card / 2 ^ depth : ENNReal) ^ n := by
  have hall : ∀ c : E, allIn S ((List.range n).map fun k ↦ (eToNat c >>> (k * depth)) % 2 ^ depth)
      = if ∀ k < n, S (chunk depth k (eToNat c)) then 1 else 0 := by
    intro c
    simp only [allIn, List.mem_map, List.mem_range, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, chunk_eq_shiftRight]
  simp only [hall]
  rw [Finset.sum_boole, card_chunks depth n hn, card_E]
  set a := (univ.filter fun j : Fin (2 ^ depth) ↦ S j).card
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have h192 : (2 : ENNReal) ^ 192 = 2 ^ (192 - n * depth) * (2 ^ depth) ^ n := by
    rw [← pow_mul, ← pow_add, Nat.mul_comm depth n, Nat.sub_add_cancel hn]
  rw [h192, ENNReal.mul_inv (by simp) (by simp), ENNReal.div_eq_inv_mul, mul_pow]
  have hx : ((2 : ENNReal) ^ (192 - n * depth))⁻¹ * 2 ^ (192 - n * depth) = 1 :=
    ENNReal.inv_mul_cancel (by simp) (by simp)
  calc _ = (((2 : ENNReal) ^ (192 - n * depth))⁻¹ * 2 ^ (192 - n * depth)) *
        (((2 ^ depth) ^ n)⁻¹ * (a : ENNReal) ^ n) := by ring
    _ = _ := by rw [hx, one_mul, ENNReal.inv_pow]

/-- **The query positions are i.i.d. uniform.** With `1 ≤ depth ≤ 192` and `rem ≤ fuel`, the
probability that all positions of `sampleQueriesAux depth fuel rem` land in `S` is at most
`(a / 2^depth)^rem`. -/
theorem retExp_sampleQueriesAux_le (depth : ℕ) (h1 : 1 ≤ depth) (h192 : depth ≤ 192)
    (S : ℕ → Prop) [DecidablePred S] :
    ∀ (fuel rem : ℕ), rem ≤ fuel → ∀ h₀ l,
      retExp (fun qs _ ↦ allIn S qs) h₀ l (sampleQueriesAux depth fuel rem) ≤
        ((univ.filter fun j : Fin (2 ^ depth) ↦ S j).card / 2 ^ depth : ENNReal) ^ rem
  | 0, rem, hrem, h₀, l => by
    obtain rfl : rem = 0 := by omega
    simp [sampleQueriesAux, retExp, allIn]
  | fuel + 1, rem, hrem, h₀, l => by
    set ρ := ((univ.filter fun j : Fin (2 ^ depth) ↦ S j).card / 2 ^ depth : ENNReal)
    by_cases h0 : rem = 0
    · subst h0
      simp [sampleQueriesAux, retExp, allIn]
    set n := min (192 / depth) rem with hn
    have hn1 : 1 ≤ n := le_min ((Nat.one_le_div_iff (by omega)).mpr h192) (by omega)
    have hnd : n * depth ≤ 192 :=
      (Nat.mul_le_mul_right _ (min_le_left _ _)).trans (Nat.div_mul_le_self 192 depth)
    have hnr : n ≤ rem := min_le_right _ _
    simp only [sampleQueriesAux, h0, ite_false, bind_eq, pure_eq]
    rw [show sampleE = (sample ret : Prog E) from rfl, Prog.bind]
    simp only [retExp, ret_bind]
    have hin : ∀ c : E,
        retExp (fun qs _ ↦ allIn S qs) h₀ (l ++ [Ev.sample c])
          ((sampleQueriesAux depth fuel (rem - n)).bind fun rest ↦
            ret ((List.range n).map (fun k ↦ (eToNat c >>> (k * depth)) % 2 ^ depth) ++ rest)) ≤
        allIn S ((List.range n).map fun k ↦ (eToNat c >>> (k * depth)) % 2 ^ depth) *
          ρ ^ (rem - n) := by
      intro c
      rw [retExp_bind]
      have : (fun a (h : List Ev) ↦ retExp (fun qs _ ↦ allIn S qs) h []
          (ret ((List.range n).map (fun k ↦ (eToNat c >>> (k * depth)) % 2 ^ depth) ++ a))) =
          fun a _ ↦ allIn S ((List.range n).map fun k ↦ (eToNat c >>> (k * depth)) % 2 ^ depth) *
            allIn S a := by
        funext a h; simp [retExp, allIn_append]
      rw [this, retExp_const_mul]
      gcongr
      exact retExp_sampleQueriesAux_le depth h1 h192 S fuel (rem - n) (by omega) _ _
    calc (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, _
        ≤ (Fintype.card E : ENNReal)⁻¹ * ∑ c : E,
          allIn S ((List.range n).map fun k ↦ (eToNat c >>> (k * depth)) % 2 ^ depth) *
            ρ ^ (rem - n) := by gcongr with c; exact hin c
      _ = ρ ^ n * ρ ^ (rem - n) := by
        rw [← Finset.sum_mul, ← mul_assoc, avg_chunks depth n hnd S]
      _ = ρ ^ rem := by rw [← pow_add]; congr 1; omega

/-- **`sample_queries` positions are i.i.d. uniform**: all `t` positions land in `S` with
probability at most `(a / 2^depth)^t`. -/
theorem retExp_sampleQueries_le (depth t : ℕ) (h1 : 1 ≤ depth) (h192 : depth ≤ 192)
    (S : ℕ → Prop) [DecidablePred S] (h₀ l : List Ev) :
    retExp (fun qs _ ↦ allIn S qs) h₀ l (sampleQueries depth t) ≤
      ((univ.filter fun j : Fin (2 ^ depth) ↦ S j).card / 2 ^ depth : ENNReal) ^ t :=
  retExp_sampleQueriesAux_le depth h1 h192 S t t le_rfl h₀ l

end
end LeanVM.Protocol.Whir.Sound
