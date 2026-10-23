/-
  LeanVM.Protocol.Compile.Rom.Encoding

  The byte encodings of the compiled verifier are injective, and the two functions of a digest
  the verifier reads off the chain are uniform: the challenge squeezed into a state, and the
  proof-of-work predicate.
-/

module

public import LeanVM.Spec.Verifier
public import LeanVM.Protocol.Compile.Prog
public import LeanVM.Protocol.Blake2sHash
public import LeanVM.Parameters.Field

/-!
# Encodings and uniformity for the random-oracle theorem

The random-oracle theorem of the compiled verifier (`LeanVM.Protocol.Compile.Rom.Sound`) reads
the oracle's log back into the verifier's operations, and averages over one fresh answer at a
time. Both rest on facts about the encodings of `LeanVM.Protocol.Compile.Run`, collected here.

* **Injectivity.** A digest is its 32 bytes (`digestBytes_injective`), a `K` word its 8 bytes
  (`kBytes_injective`), a list of words of a given length its bytes (`flatMap_kBytes_inj`), and a
  chain block its scalar and the low byte of its tag (`blockOf_inj`). So a log input of the form
  `digestBytes cv ++ blockOf x tag` names its state, scalar and tag.
* **Uniform challenges.** `Digest ≃ E × UInt32 × UInt32` with the first component the challenge
  `challengeOf` (`challengeEquiv`): the challenge of a uniform digest is uniform on `E`
  (`sum_challengeOf_div`), every challenge having `2^64` preimages, and `|Digest| = 2^256`
  (`card_digest`).
* **Proof of work.** The proof-of-work predicate holds for at most a `2^-min(b, 64)` fraction of
  digests (`sum_powOk_div_le`): for `1 ≤ b ≤ 64` exactly `2^-b`; for `b > 64` the 64-bit word it
  tests must vanish; for `b = 0` it does not read the digest at all.
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Blake2sHash
open scoped ENNReal

@[expose] public section

/-! ## Lengths and injectivity of the byte encodings -/

theorem wordBytes_length (w : UInt32) : (wordBytes w).length = 4 := rfl

theorem wordBytes_injective : Function.Injective wordBytes := by
  intro w w' h
  simp only [wordBytes, List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  have e0 := congrArg UInt8.toNat h0
  have e1 := congrArg UInt8.toNat h1
  have e2 := congrArg UInt8.toNat h2
  have e3 := congrArg UInt8.toNat h3
  simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
    UInt32.reduceToNat] at e0 e1 e2 e3
  apply UInt32.toNat_inj.mp
  have := w.toNat_lt
  have := w'.toNat_lt
  norm_num at e0 e1 e2 e3 ⊢
  omega

/-- A `flatMap` of an injective function with outputs of one length is injective on lists of
one length. -/
theorem flatMap_inj_of_length {α β : Type} {f : α → List β} {n : ℕ}
    (hlen : ∀ a, (f a).length = n) (hf : Function.Injective f) :
    ∀ {l l' : List α}, l.length = l'.length → l.flatMap f = l'.flatMap f → l = l' := by
  intro l
  induction l with
  | nil => intro l' hl _; exact (List.length_eq_zero_iff.mp hl.symm).symm
  | cons a l ih =>
    intro l' hl h
    obtain _ | ⟨a', l'⟩ := l'
    · simp at hl
    simp only [List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [hlen, hlen])
    rw [hf h1, ih (by simpa using hl) h2]

theorem digestBytes_length (d : Digest) : (digestBytes d).length = 32 := by
  simp [digestBytes, List.length_flatMap, wordBytes_length]

theorem digestBytes_injective : Function.Injective digestBytes := by
  intro d d' h
  exact Vector.toList_inj.mp
    (flatMap_inj_of_length wordBytes_length wordBytes_injective (by simp) h)

/-- Splitting a `K` element into its two words and joining them again is the identity. -/
theorem ofWords_lowWord_highWord (a : K) : ofWords (lowWord a) (highWord a) = a := by
  apply BF64.toBitVec_injective
  have := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := a.toBitVec) (start₁ := 0)
    (len₁ := 32) (start₂ := 32) (len₂ := 32) rfl
  simpa [ofWords, lowWord, highWord] using this

theorem kBytes_length (a : K) : (kBytes a).length = 8 := rfl

theorem kBytes_injective : Function.Injective kBytes := by
  intro a a' h
  obtain ⟨h1, h2⟩ := List.append_inj h rfl
  rw [← ofWords_lowWord_highWord a, ← ofWords_lowWord_highWord a', wordBytes_injective h1,
    wordBytes_injective h2]

/-- Two lists of `K` words of one length with the same bytes are equal. -/
theorem flatMap_kBytes_inj {ws ws' : List K} (hl : ws.length = ws'.length)
    (h : ws.flatMap kBytes = ws'.flatMap kBytes) : ws = ws' :=
  flatMap_inj_of_length kBytes_length kBytes_injective hl h

theorem tagBytes_length (tag : ℕ) : (tagBytes tag).length = 8 := rfl

theorem blockOf_length (x : E) (tag : ℕ) : (blockOf x tag).length = 32 := rfl

/-- A chain block determines its scalar and the low byte of its tag. -/
theorem blockOf_inj {x y : E} {a b : ℕ} (h : blockOf x a = blockOf y b) :
    x = y ∧ a.toUInt8 = b.toUInt8 := by
  simp only [blockOf, List.append_assoc] at h
  obtain ⟨h0, h⟩ := List.append_inj h rfl
  obtain ⟨h1, h⟩ := List.append_inj h rfl
  obtain ⟨h2, h3⟩ := List.append_inj h rfl
  refine ⟨?_, by simpa [tagBytes] using h3⟩
  rw [← ofLimbs_limb x, ← ofLimbs_limb y, kBytes_injective h0, kBytes_injective h1,
    kBytes_injective h2]

/-- The input of a chain step: a state followed by a block. -/
theorem chainInput_inj {c c' : Digest} {x y : E} {a b : ℕ}
    (h : digestBytes c ++ blockOf x a = digestBytes c' ++ blockOf y b) :
    c = c' ∧ x = y ∧ a.toUInt8 = b.toUInt8 := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by rw [digestBytes_length, digestBytes_length])
  exact ⟨digestBytes_injective h1, blockOf_inj h2⟩

/-- The input of a Merkle node: two digests. -/
theorem pairInput_inj {a b a' b' : Digest}
    (h : digestBytes a ++ digestBytes b = digestBytes a' ++ digestBytes b') : a = a' ∧ b = b' := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by rw [digestBytes_length, digestBytes_length])
  exact ⟨digestBytes_injective h1, digestBytes_injective h2⟩

/-! ## Uniformity of the challenge -/

/-- `UInt32` as `Fin (2^32)`. -/
def uint32EquivFin : UInt32 ≃ Fin (2 ^ 32) where
  toFun w := w.toFin
  invFun i := UInt32.ofFin i
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_uint32 : Fintype.card UInt32 = 2 ^ 32 := by
  rw [Fintype.card_congr uint32EquivFin, Fintype.card_fin]

theorem card_K : Fintype.card K = 2 ^ 64 := by
  rw [← Fintype.card_congr LeanVM.Protocol.finEquivK, Fintype.card_fin]

/-- The digest whose challenge is `c` and whose two top words are `w`. -/
def digestOfChallenge (c : E) (w : UInt32 × UInt32) : Digest :=
  #v[lowWord (c.limb 0), highWord (c.limb 0), lowWord (c.limb 1), highWord (c.limb 1),
    lowWord (c.limb 2), highWord (c.limb 2), w.1, w.2]

/-- A digest is its challenge and its two top words. -/
def challengeEquiv : Digest ≃ E × (UInt32 × UInt32) where
  toFun d := (challengeOf d, (d[6], d[7]))
  invFun p := digestOfChallenge p.1 p.2
  left_inv d := by
    have h : ∀ i : Fin 3, (challengeOf d).limb i = ofWords d[2 * i.val] d[2 * i.val + 1] := by
      intro i; rw [challengeOf, limb_ofLimbs]; fin_cases i <;> rfl
    simp only [digestOfChallenge, h]
    simp only [lowWord_ofWords, highWord_ofWords]
    ext i hi
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;> first | rfl | omega
  right_inv p := by
    obtain ⟨c, w⟩ := p
    simp only [digestOfChallenge, challengeOf, Prod.mk.injEq]
    refine ⟨?_, rfl⟩
    exact (congrArg₃ E.ofLimbs (ofWords_lowWord_highWord _) (ofWords_lowWord_highWord _)
      (ofWords_lowWord_highWord _)).trans (ofLimbs_limb c)
where
  congrArg₃ {α β γ δ : Type} (f : α → β → γ → δ) {a a' : α} {b b' : β} {c c' : γ}
      (ha : a = a') (hb : b = b') (hc : c = c') : f a b c = f a' b' c' := by
    subst ha hb hc; rfl

theorem challengeEquiv_fst (d : Digest) : (challengeEquiv d).1 = challengeOf d := rfl

/-- `|Digest| = 2^256`. -/
theorem card_digest : Fintype.card Digest = 2 ^ 256 := by
  rw [Fintype.card_congr challengeEquiv, Fintype.card_prod, Fintype.card_prod, card_E,
    card_uint32]
  norm_num

/-- **The challenge of a uniform digest is uniform.** -/
theorem sum_challengeOf_div (f : E → ℝ≥0∞) :
    (∑ d : Digest, f (challengeOf d)) / Fintype.card Digest =
      (∑ c : E, f c) / Fintype.card E := by
  have hs : ∑ d : Digest, f (challengeOf d) =
      (Fintype.card (UInt32 × UInt32) : ℝ≥0∞) * ∑ c : E, f c := by
    rw [Fintype.sum_equiv challengeEquiv (fun d ↦ f (challengeOf d)) (fun p ↦ f p.1)
      (fun _ ↦ rfl), Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  have hc : (Fintype.card Digest : ℝ≥0∞) =
      (Fintype.card (UInt32 × UInt32) : ℝ≥0∞) * Fintype.card E := by
    rw [Fintype.card_congr challengeEquiv, Fintype.card_prod, Nat.cast_mul, mul_comm]
  rw [hs, hc, ENNReal.mul_div_mul_left]
  · exact_mod_cast Fintype.card_ne_zero
  · exact ENNReal.natCast_ne_top _

/-! ## The proof of work -/

/-- The two words a proof of work tests, as one 64-bit number, are the first limb of the
challenge. -/
theorem toNat_lowWord_add_highWord (a : K) :
    (lowWord a).toNat + 2 ^ 32 * (highWord a).toNat = a.toBitVec.toNat := by
  simp only [lowWord, highWord, UInt32.toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have := a.toBitVec.isLt
  norm_num at this ⊢
  omega

/-- At most `2^(64 - min b 64)` 64-bit numbers are divisible by `2^b`. -/
theorem card_filter_mod_pow_eq_zero_le (b : ℕ) :
    (Finset.univ.filter fun i : Fin (2 ^ 64) ↦ i.val % 2 ^ b = 0).card ≤ 2 ^ (64 - min b 64) := by
  set m := min b 64
  have hsub : (Finset.univ.filter fun i : Fin (2 ^ 64) ↦ i.val % 2 ^ b = 0).map
      Fin.valEmbedding ⊆ (Finset.range (2 ^ (64 - m))).image fun j ↦ j * 2 ^ m := by
    intro x hx
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have hdvd : 2 ^ m ∣ i.val :=
      (Nat.pow_dvd_pow 2 (min_le_left b 64)).trans (Nat.dvd_of_mod_eq_zero hi)
    obtain ⟨j, hj⟩ := hdvd
    simp only [Finset.mem_image, Finset.mem_range]
    refine ⟨j, ?_, by rw [hj, mul_comm]⟩
    have hlt := i.isLt
    rw [hj] at hlt
    have h64 : 2 ^ 64 = 2 ^ m * 2 ^ (64 - m) := by
      rw [← pow_add, Nat.add_sub_cancel' (min_le_right b 64)]
    rw [h64] at hlt
    exact Nat.lt_of_mul_lt_mul_left hlt
  calc _ = ((Finset.univ.filter fun i : Fin (2 ^ 64) ↦ i.val % 2 ^ b = 0).map
        Fin.valEmbedding).card := (Finset.card_map _).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le.trans (by rw [Finset.card_range])

/-- `E` as its three limbs. -/
def limbEquiv : E ≃ K × (K × K) where
  toFun c := (c.limb 0, (c.limb 1, c.limb 2))
  invFun p := E.ofLimbs p.1 p.2.1 p.2.2
  left_inv c := ofLimbs_limb c
  right_inv p := by simp

/-- **The proof of work of a uniform digest succeeds with probability at most
`2^-min(b, 64)`.** -/
theorem sum_powOk_div_le (b : ℕ) (n : E) :
    (∑ d : Digest, if powOk b n d then (1 : ℝ≥0∞) else 0) / Fintype.card Digest ≤
      2⁻¹ ^ min b 64 := by
  by_cases hb : b = 0
  · subst hb
    rw [min_eq_left (Nat.zero_le _), pow_zero]
    refine ENNReal.div_le_of_le_mul ?_
    rw [one_mul]
    calc (∑ d : Digest, if powOk 0 n d then (1 : ℝ≥0∞) else 0)
        ≤ ∑ _d : Digest, (1 : ℝ≥0∞) := Finset.sum_le_sum fun _ _ ↦ by split <;> simp
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  -- The predicate reads the first limb of the challenge.
  have hpow : ∀ d : Digest, powOk b n d =
      decide (((challengeOf d).limb 0).toBitVec.toNat % 2 ^ b = 0) := by
    intro d
    have h0 : (challengeOf d).limb 0 = ofWords d[0] d[1] := by
      rw [challengeOf, limb_ofLimbs]; rfl
    simp only [powOk, hb, ↓reduceIte]
    rw [h0, ← toNat_lowWord_add_highWord, lowWord_ofWords, highWord_ofWords]
  let g : K → ℝ≥0∞ := fun a ↦ if a.toBitVec.toNat % 2 ^ b = 0 then 1 else 0
  have hsum : (∑ d : Digest, if powOk b n d then (1 : ℝ≥0∞) else 0) =
      ∑ d : Digest, g ((challengeOf d).limb 0) := by
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    simp only [hpow, decide_eq_true_eq, g]
  rw [hsum, sum_challengeOf_div (fun c ↦ g (c.limb 0))]
  -- Average over the three limbs, then over `Fin (2^64)`.
  have hE : (∑ c : E, g (c.limb 0)) =
      (Fintype.card (K × K) : ℝ≥0∞) * ∑ a : K, g a := by
    rw [Fintype.sum_equiv limbEquiv (fun c ↦ g (c.limb 0)) (fun p ↦ g p.1) (fun _ ↦ rfl),
      Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  have hcE : (Fintype.card E : ℝ≥0∞) = (Fintype.card (K × K) : ℝ≥0∞) * Fintype.card K := by
    rw [Fintype.card_congr limbEquiv, Fintype.card_prod, Nat.cast_mul, mul_comm]
  rw [hE, hcE, ENNReal.mul_div_mul_left _ _ (by exact_mod_cast Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _), card_K]
  have hK : (∑ a : K, g a) =
      ((Finset.univ.filter fun i : Fin (2 ^ 64) ↦ i.val % 2 ^ b = 0).card : ℝ≥0∞) := by
    rw [Fintype.sum_equiv LeanVM.Protocol.finEquivK.symm g
      (fun i : Fin (2 ^ 64) ↦ if i.val % 2 ^ b = 0 then 1 else 0) (fun _ ↦ rfl)]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hK]
  set m := min b 64
  calc (((Finset.univ.filter fun i : Fin (2 ^ 64) ↦ i.val % 2 ^ b = 0).card : ℕ) : ℝ≥0∞)
        / ((2 ^ 64 : ℕ) : ℝ≥0∞)
      ≤ ((2 ^ (64 - m) : ℕ) : ℝ≥0∞) / ((2 ^ 64 : ℕ) : ℝ≥0∞) := by
        gcongr
        exact_mod_cast card_filter_mod_pow_eq_zero_le b
    _ = 2⁻¹ ^ m := by
        have h64 : (2 : ℝ≥0∞) ^ 64 = 2 ^ (64 - m) * 2 ^ m := by
          rw [← pow_add, Nat.sub_add_cancel (min_le_right b 64)]
        rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, h64, ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (by simp) (by simp), mul_comm (2 ^ (64 - m))⁻¹, mul_assoc,
          ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, ENNReal.inv_pow]

end

end LeanVM.Protocol.Compile.Rom
