/-
  LeanVM.Guest.B1.FsBlocks

  The guest's `@inline` Fiat-Shamir and tower gadgets as expanded statement blocks, and their
  meaning: each block, at any position of its caller, holds exactly when the chain moves as the
  specification's step does.
-/

module

public import LeanVM.Guest.B1.Basic

/-!
# The inline Fiat-Shamir blocks (TRIAGE #1, #3-#11)

An `@inline` function has no compiled function: its body is expanded into each caller, its
values numbered densely after the caller's (`Renumber`). Each template below is that expansion,
parametric in the caller's values it reads (`V`) and the number `b` of its first own value, and
proved equal to the caller's statements by `rfl`. Its lemma is an iff on `Stmt.HoldsList` for
any continuation, its own values pinned to an honest vector (`fsVals`, `sqVals`) except the hint
cells no constraint reads:

| guest | template | meaning |
|---|---|---|
| `pack64x2(a, b)` (G:446-449) | `pack64x2T` | `E.ofLimbs a b 0` |
| `canonical_limbs(w)` (G:463-468) | `canonicalLimbsT` | `w` canonical, its two limbs |
| `fs_compress(st, x, tag, out)` (G:488-497) | `fsCompressT` | `absorbBlock cv (blockOf x tag)` |
| `obs(st, x)` (G:501-506), `absorb_nonce` (G:538-542) | `fsCompressT` at tag 1, 4 | `Node.observe`, `.grind`'s state |
| `fs_next(st, cursor)` (G:510-518) | `fsNextT` | `.read` of the word at the cursor |
| `squeeze_state(st)` (G:522-525) | `squeezeStateT` | `absorbBlock cv (blockOf 0 tag)` |
| `challenge_from_state(st)` (G:472-484), `squeeze` (G:529-534) | `squeezeT` | `.sample`, `Node.squeeze` |

`squeeze_step` (G:546-555) is `squeeze` after copying its two arguments into a run, which its
only caller (`opening_ood_point`'s loop) states as two copies before `squeezeT`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Digests -/

theorem digestScalars_injective : Function.Injective digestScalars := fun a b h => by
  have ha := digestOfScalars_digestScalars a
  rw [h, digestOfScalars_digestScalars] at ha
  exact (Option.some.inj ha).symm

/-- Two canonical cells are a digest's. -/
theorem exists_digest {a b : E} (ha : IsCanonical128 a) (hb : IsCanonical128 b) :
    ∃ cv, (a, b) = digestScalars cv :=
  ⟨cellWords a ++ cellWords b, pair_eq_digestScalars_iff.mpr ⟨ha, hb, rfl⟩⟩

/-! ## `pack64x2` and `canonical_limbs` -/

/-- `pack64x2(a, b)` at its first value `b0`: `assert_in_k(a, b)`, then `a + Y·b`. -/
def pack64x2T (a c : V) (b : ℕ) : List Stmt :=
  [.atom (.assertInK a c), .atom (.const (.n b) (word 0 1 0)), .atom (.mul (.n (b + 1)) (.n b) c),
    .atom (.add (.n (b + 2)) a (.n (b + 1)))]

/-- **`pack64x2`** (TRIAGE #1): the block holds exactly when both limbs are in `K`, and then its
value `.n (b + 2)` is the canonical cell `E.ofLimbs a c 0`. -/
theorem holds_pack64x2T (a c : V) (b : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (pack64x2T a c b) next kret ↔
      (IsInK (σ a) ∧ IsInK (σ c) ∧ σ (.n b) = y ∧ σ (.n (b + 1)) = y * σ c ∧
        σ (.n (b + 2)) = E.ofLimbs ((σ a).limb 0) ((σ c).limb 0) 0) ∧ next := by
  simp only [pack64x2T, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_y]
  constructor
  · rintro ⟨⟨ha, hc⟩, h0, h1, h2, hn⟩
    refine ⟨⟨ha, hc, h0, by rw [h1, h0], ?_⟩, hn⟩
    rw [h2, h1, h0, pack64x2_eq ha hc]
  · rintro ⟨⟨ha, hc, h0, h1, h2⟩, hn⟩
    refine ⟨⟨ha, hc⟩, h0, by rw [h1, h0], ?_, hn⟩
    rw [h2, h1, pack64x2_eq ha hc]

/-- `canonical_limbs(w)` (and `assert_canonical`'s body) at its first value `b`: hint the low
limb, derive `(w + lo)·Y⁻¹`, assert both in `K`. -/
def canonicalLimbsT (w : V) (b : ℕ) : List Stmt :=
  [.atom (.hint (.limbs w [.n b])), .atom (.add (.n (b + 1)) w (.n b)),
    .atom (.const (.n (b + 2)) (word 1 0 1)), .atom (.mul (.n (b + 3)) (.n (b + 1)) (.n (b + 2))),
    .atom (.assertInK (.n b) (.n (b + 3)))]

/-- **`canonical_limbs`** (TRIAGE #2, #3): the block holds exactly when `w` is canonical and the
hinted limb is its low limb; the derived `.n (b + 3)` is then its high limb. -/
theorem holds_canonicalLimbsT (w : V) (b : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (canonicalLimbsT w b) next kret ↔
      (IsCanonical128 (σ w) ∧ σ (.n b) = ofK ((σ w).limb 0) ∧ σ (.n (b + 1)) = σ w + σ (.n b) ∧
        σ (.n (b + 2)) = word 1 0 1 ∧ σ (.n (b + 3)) = ofK ((σ w).limb 1)) ∧ next := by
  simp only [canonicalLimbsT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and]
  constructor
  · rintro ⟨h1, h2, h3, ⟨hlo, hhi⟩, hn⟩
    rw [h3, h2, h1, word_y_inv] at hhi
    obtain ⟨hc, hl⟩ := (split_iff _ _).mp ⟨hlo, hhi⟩
    refine ⟨⟨hc, hl, h1, h2, ?_⟩, hn⟩
    rw [h3, h2, h1, hl, word_y_inv, split_hi hc]
  · rintro ⟨⟨hc, hl, h1, h2, h3⟩, hn⟩
    refine ⟨h1, h2, ?_, ⟨?_, ?_⟩, hn⟩
    · rw [h3, h2, h1, hl, word_y_inv, split_hi hc]
    · rw [hl]; exact ofK_isInK _
    · rw [h3]; exact ofK_isInK _

/-! ## `fs_compress`, `obs`, `absorb_nonce`, `fs_next` -/

/-- `fs_compress(st, x, tag, out)` at its first value `b`: the three hinted limbs of `x` at
`b .. b + 2`, the block cells at `b + 6`, `b + 8`, the output at `b + 12`, `b + 13`. -/
def fsCompressT (s0 s1 x : V) (b tag : ℕ) : List Stmt :=
  [.atom (.hint (.limbs x [.n b, .n (b + 1), .n (b + 2)])),
    .atom (.const (.n (b + 3)) (word tag 0 0)),
    .atom (.assertInK (.n (b + 2)) (.n (b + 3))),
    .atom (.const (.n (b + 4)) (word 0 0 1)),
    .atom (.mul (.n (b + 5)) (.n (b + 4)) (.n (b + 2))),
    .atom (.add (.n (b + 6)) x (.n (b + 5))),
    .atom (.const (.n (b + 7)) (word 0 tag 0)),
    .atom (.add (.n (b + 8)) (.n (b + 2)) (.n (b + 7))),
    .atom (.const (.n (b + 9)) (word 13503953895743350343 11912009169889063794 0)),
    .atom (.const (.n (b + 10)) (word 11170449402626986623 6620516960021240235 0)),
    .atom (.const (.n (b + 11)) (word 64 4294967295 0)),
    .atom (.blake2s s0 s1 (.n (b + 6)) (.n (b + 8)) (.n (b + 9)) (.n (b + 10)) (.n (b + 12))
      (.n (b + 13)) (.n (b + 11)))]

/-- The state after absorbing `x` with the tag. -/
def absorbCv (cv : Digest) (x : E) (tag : ℕ) : Digest :=
  blake2sBytes (digestBytes cv ++ blockOf x tag)

/-- The honest values of `fsCompressT`, from its first: the limbs of `x`, the tag, `y²`, the
block, the IV, the metadata, the output. -/
def fsVals (x : E) (cv : Digest) (tag : ℕ) : ℕ → E
  | 0 => ofK (x.limb 0)
  | 1 => ofK (x.limb 1)
  | 2 => ofK (x.limb 2)
  | 3 => eOfNat tag
  | 4 => y * y
  | 5 => y * y * ofK (x.limb 2)
  | 6 => x + y * y * ofK (x.limb 2)
  | 7 => y * eOfNat tag
  | 8 => ofK (x.limb 2) + y * eOfNat tag
  | 9 => Value.ivCells.1
  | 10 => Value.ivCells.2
  | 11 => metadataCell 64 true
  | 12 => (digestScalars (absorbCv cv x tag)).1
  | 13 => (digestScalars (absorbCv cv x tag)).2
  | _ => 0

/-- **`fs_compress`** (TRIAGE #5; `obs` #6 at tag 1, `absorb_nonce` #10 at tag 4): the block
holds exactly when the state is the digest `cv`'s cells and every value from `b + 2` on is the
honest one: the hinted top limb of `x`, and the output the state after absorbing
`blockOf x tag` (`absorbBlock`, V:522). -/
theorem holds_fsCompressT (s0 s1 x : V) (b : ℕ) {tag : ℕ} (htag : tag < 256) (next : Prop)
    (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (fsCompressT s0 s1 x b tag) next kret ↔
      (∃ cv, (σ s0, σ s1) = digestScalars cv ∧
        ∀ k, 2 ≤ k → k < 14 → σ (.n (b + k)) = fsVals (σ x) cv tag k) ∧ next := by
  simp only [fsCompressT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, word_eOfNat, word_yy,
    word_y_mul, word_iv0, word_iv1, word_md64]
  constructor
  · rintro ⟨h3, ⟨hl, -⟩, h4, h5, h6, h7, h8, h9, h10, h11, hc, hn⟩
    refine ⟨?_, hn⟩
    rw [h5, h4] at h6
    rw [h7] at h8
    rw [h6, h8, h9, h10, h11] at hc
    obtain ⟨cv, hcv⟩ := exists_digest (hc.1 0) (hc.1 1)
    have hc' : CompressCells (fsBlock (digestScalars cv) (σ x) (σ (.n (b + 2))) (eOfNat tag))
        Value.ivCells.1 Value.ivCells.2 (σ (.n (b + 12))) (σ (.n (b + 13)))
        (metadataCell 64 true) := by
      rw [← hcv]; exact hc
    obtain ⟨hl2, hout⟩ := (fs_compress_iff cv (σ x) htag _ _ _).mp ⟨hl, hc'⟩
    refine ⟨cv, hcv, fun k hk1 hk2 => ?_⟩
    interval_cases k
    · exact hl2
    · exact h3
    · exact h4
    · rw [h5, h4, hl2]; rfl
    · rw [h6, hl2]; rfl
    · exact h7
    · rw [h8, hl2]; rfl
    · exact h9
    · exact h10
    · exact h11
    · exact congrArg Prod.fst hout
    · exact congrArg Prod.snd hout
  · rintro ⟨⟨cv, hcv, e⟩, hn⟩
    have e2 : σ (.n (b + 2)) = ofK ((σ x).limb 2) := e 2 le_rfl (by omega)
    have e3 : σ (.n (b + 3)) = eOfNat tag := e 3 (by omega) (by omega)
    have e4 : σ (.n (b + 4)) = y * y := e 4 (by omega) (by omega)
    have e5 : σ (.n (b + 5)) = y * y * ofK ((σ x).limb 2) := e 5 (by omega) (by omega)
    have e6 : σ (.n (b + 6)) = σ x + y * y * ofK ((σ x).limb 2) := e 6 (by omega) (by omega)
    have e7 : σ (.n (b + 7)) = y * eOfNat tag := e 7 (by omega) (by omega)
    have e8 : σ (.n (b + 8)) = ofK ((σ x).limb 2) + y * eOfNat tag := e 8 (by omega) (by omega)
    have e9 : σ (.n (b + 9)) = Value.ivCells.1 := e 9 (by omega) (by omega)
    have e10 : σ (.n (b + 10)) = Value.ivCells.2 := e 10 (by omega) (by omega)
    have e11 : σ (.n (b + 11)) = metadataCell 64 true := e 11 (by omega) (by omega)
    have e12 : σ (.n (b + 12)) =
        (digestScalars (blake2sBytes (digestBytes cv ++ blockOf (σ x) tag))).1 :=
      e 12 (by omega) (by omega)
    have e13 : σ (.n (b + 13)) =
        (digestScalars (blake2sBytes (digestBytes cv ++ blockOf (σ x) tag))).2 :=
      e 13 (by omega) (by omega)
    have hout := (fs_compress_iff cv (σ x) htag (σ (.n (b + 2))) (σ (.n (b + 12)))
      (σ (.n (b + 13)))).mpr ⟨e2, by rw [e12, e13]⟩
    refine ⟨e3, ⟨hout.1, by rw [e3]; exact eOfNat_isInK tag⟩, e4, by rw [e5, e4, e2],
      by rw [e6, e5], e7, by rw [e8, e7, e2], e9, e10, e11, ?_, hn⟩
    have h := hout.2
    rw [fsBlock] at h
    rw [e6, e8, e9, e10, e11, ← e2, show σ s0 = _ from congrArg Prod.fst hcv,
      show σ s1 = _ from congrArg Prod.snd hcv]
    exact h

/-- `fs_next(st, cursor)` at its first value `b`, reading the word at offset `j`: the word at
`b`, then `fs_compress` at tag 1 from `b + 1`, the new state at `b + 13`, `b + 14`. -/
def fsNextT (s0 s1 cur : V) (j b : ℕ) : List Stmt :=
  .atom (.load (.n b) cur j) :: fsCompressT s0 s1 (.n b) (b + 1) 1

/-- **`fs_next`** (TRIAGE #7): the block holds exactly when the word at the cursor's offset `j`
is `.n b` and the chain absorbs it (`.read`, V:558-562). -/
theorem holds_fsNextT (s0 s1 cur : V) (j b : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (fsNextT s0 s1 cur j b) next kret ↔
      (LoadHolds rd (σ cur) j (σ (.n b)) ∧ ∃ cv, (σ s0, σ s1) = digestScalars cv ∧
        ∀ k, 2 ≤ k → k < 14 → σ (.n (b + 1 + k)) = fsVals (σ (.n b)) cv 1 k) ∧ next := by
  show (LoadHolds rd (σ cur) j (σ (.n b)) ∧
    Stmt.HoldsList C rd σ (fsCompressT s0 s1 (.n b) (b + 1) 1) next kret) ↔ _
  rw [holds_fsCompressT _ _ _ _ (by decide)]
  tauto

theorem absorbCv_one (cv : Digest) (x : E) : absorbCv cv x 1 = obsCv cv x := rfl

/-! ## `squeeze_state`, `challenge_from_state`, `squeeze` -/

/-- `squeeze_state` (at tag 2; `grind_check`'s base at tag 3) at its first value `b`: the block
`[0, Y·tag]`, the IV, the metadata, the output at `b + 5`, `b + 6`. -/
def squeezeStateT (s0 s1 : V) (b tag : ℕ) : List Stmt :=
  [.atom (.const (.n b) (word 0 0 0)),
    .atom (.const (.n (b + 1)) (word 0 tag 0)),
    .atom (.const (.n (b + 2)) (word 13503953895743350343 11912009169889063794 0)),
    .atom (.const (.n (b + 3)) (word 11170449402626986623 6620516960021240235 0)),
    .atom (.const (.n (b + 4)) (word 64 4294967295 0)),
    .atom (.blake2s s0 s1 (.n b) (.n (b + 1)) (.n (b + 2)) (.n (b + 3)) (.n (b + 5)) (.n (b + 6))
      (.n (b + 4)))]

/-- The honest values of `squeezeStateT`. -/
def sqStateVals (cv : Digest) (tag : ℕ) : ℕ → E
  | 0 => 0
  | 1 => y * eOfNat tag
  | 2 => Value.ivCells.1
  | 3 => Value.ivCells.2
  | 4 => metadataCell 64 true
  | 5 => (digestScalars (absorbCv cv 0 tag)).1
  | 6 => (digestScalars (absorbCv cv 0 tag)).2
  | _ => 0

/-- **`squeeze_state`** (TRIAGE #8): the block holds exactly when the state is `cv`'s cells and
the output is the state after absorbing `blockOf 0 tag`. -/
theorem holds_squeezeStateT (s0 s1 : V) (b : ℕ) {tag : ℕ} (htag : tag < 256) (next : Prop)
    (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (squeezeStateT s0 s1 b tag) next kret ↔
      (∃ cv, (σ s0, σ s1) = digestScalars cv ∧
        ∀ k, k < 7 → σ (.n (b + k)) = sqStateVals cv tag k) ∧ next := by
  simp only [squeezeStateT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_y_mul, eOfNat_zero,
    mul_zero, word_iv0, word_iv1, word_md64]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, hc, hn⟩
    refine ⟨?_, hn⟩
    rw [h0, h1, h2, h3, h4] at hc
    obtain ⟨cv, hcv⟩ := exists_digest (hc.1 0) (hc.1 1)
    rw [show σ s0 = (digestScalars cv).1 from congrArg Prod.fst hcv,
      show σ s1 = (digestScalars cv).2 from congrArg Prod.snd hcv] at hc
    have hout := (squeeze_state_iff cv htag _ _).mp hc
    refine ⟨cv, hcv, fun k hk => ?_⟩
    interval_cases k
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact congrArg Prod.fst hout
    · exact congrArg Prod.snd hout
  · rintro ⟨⟨cv, hcv, e⟩, hn⟩
    have e0 : σ (.n b) = 0 := e 0 (by omega)
    have e1 : σ (.n (b + 1)) = y * eOfNat tag := e 1 (by omega)
    have e2 : σ (.n (b + 2)) = Value.ivCells.1 := e 2 (by omega)
    have e3 : σ (.n (b + 3)) = Value.ivCells.2 := e 3 (by omega)
    have e4 : σ (.n (b + 4)) = metadataCell 64 true := e 4 (by omega)
    have e5 : σ (.n (b + 5)) = (digestScalars (blake2sBytes (digestBytes cv ++ blockOf 0 tag))).1 :=
      e 5 (by omega)
    have e6 : σ (.n (b + 6)) = (digestScalars (blake2sBytes (digestBytes cv ++ blockOf 0 tag))).2 :=
      e 6 (by omega)
    refine ⟨e0, e1, e2, e3, e4, ?_, hn⟩
    rw [e0, e1, e2, e3, e4, show σ s0 = (digestScalars cv).1 from congrArg Prod.fst hcv,
      show σ s1 = (digestScalars cv).2 from congrArg Prod.snd hcv, squeeze_state_iff cv htag, e5, e6]

/-- `challenge_from_state` over the state `(o0, o1)` at its first value `b`: hint `d2`, derive
`(o1 + d2)·Y⁻¹`, assert both in `K`; the challenge `o0 + Y²·d2` at `b + 6`. -/
def challengeT (o0 o1 : V) (b : ℕ) : List Stmt :=
  [.atom (.hint (.limbs o1 [.n b])), .atom (.add (.n (b + 1)) o1 (.n b)),
    .atom (.const (.n (b + 2)) (word 1 0 1)), .atom (.mul (.n (b + 3)) (.n (b + 1)) (.n (b + 2))),
    .atom (.assertInK (.n b) (.n (b + 3))), .atom (.const (.n (b + 4)) (word 0 0 1)),
    .atom (.mul (.n (b + 5)) (.n (b + 4)) (.n b)), .atom (.add (.n (b + 6)) o0 (.n (b + 5)))]

/-- `squeeze(st)` at its first value `b`: the new state at `b + 5`, `b + 6`, the challenge at
`b + 13`. -/
def squeezeT (s0 s1 : V) (b : ℕ) : List Stmt :=
  squeezeStateT s0 s1 b 2 ++ challengeT (.n (b + 5)) (.n (b + 6)) (b + 7)

/-- The honest values of `squeezeT`. -/
def sqVals (cv : Digest) : ℕ → E
  | 7 => ofK ((digestScalars (sqCv cv)).2.limb 0)
  | 8 => (digestScalars (sqCv cv)).2 + ofK ((digestScalars (sqCv cv)).2.limb 0)
  | 9 => word 1 0 1
  | 10 => ((digestScalars (sqCv cv)).2 + ofK ((digestScalars (sqCv cv)).2.limb 0)) * word 1 0 1
  | 11 => y * y
  | 12 => y * y * ofK ((digestScalars (sqCv cv)).2.limb 0)
  | 13 => challengeOf (sqCv cv)
  | k => sqStateVals cv 2 k

theorem absorbCv_sq (cv : Digest) : absorbCv cv 0 2 = sqCv cv := rfl

/-- **`squeeze`** (TRIAGE #9, #4; `squeeze_step` #11): the block holds exactly when the state
is `cv`'s cells and its values are the honest ones: the new state `Node.squeeze`'s
(`.sample`, V:563-565), the challenge `challengeOf` of it (V:477). -/
theorem holds_squeezeT (s0 s1 : V) (b : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (squeezeT s0 s1 b) next kret ↔
      (∃ cv, (σ s0, σ s1) = digestScalars cv ∧ ∀ k, k < 14 → σ (.n (b + k)) = sqVals cv k) ∧
        next := by
  rw [squeezeT, holdsList_append, holds_squeezeStateT _ _ _ (by decide)]
  simp only [challengeT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, true_and, word_yy,
    Nat.add_assoc, Nat.reduceAdd]
  constructor
  · rintro ⟨⟨cv, hcv, e⟩, h1, h2, h3, ⟨hd2, hd3⟩, h4, h5, h6, hn⟩
    have e5 : σ (.n (b + 5)) = (digestScalars (sqCv cv)).1 := e 5 (by omega)
    have e6 : σ (.n (b + 6)) = (digestScalars (sqCv cv)).2 := e 6 (by omega)
    rw [h3, h2, h1, e6, word_y_inv] at hd3
    have hd : σ (.n (b + 7)) = ofK ((digestScalars (sqCv cv)).2.limb 0) :=
      (challenge_from_state_iff (sqCv cv) _).mp ⟨hd2, hd3⟩
    refine ⟨⟨cv, hcv, fun k hk => ?_⟩, hn⟩
    rcases (show k < 7 ∨ 7 ≤ k by omega) with hk7 | hk7
    · rw [e k hk7]
      interval_cases k <;> rfl
    · interval_cases k
      · exact hd
      · rw [h1, e6, hd]; rfl
      · exact h2
      · rw [h3, h2, h1, e6, hd]; rfl
      · exact h4
      · rw [h5, h4, hd]; rfl
      · rw [h6, h5, h4, hd, e5, challenge_from_state_eq]; rfl
  · rintro ⟨⟨cv, hcv, e⟩, hn⟩
    have e7 : σ (.n (b + 7)) = ofK ((digestScalars (sqCv cv)).2.limb 0) := e 7 (by omega)
    have e8 : σ (.n (b + 8)) =
        (digestScalars (sqCv cv)).2 + ofK ((digestScalars (sqCv cv)).2.limb 0) := e 8 (by omega)
    have e9 : σ (.n (b + 9)) = word 1 0 1 := e 9 (by omega)
    have e10 : σ (.n (b + 10)) =
        ((digestScalars (sqCv cv)).2 + ofK ((digestScalars (sqCv cv)).2.limb 0)) * word 1 0 1 :=
      e 10 (by omega)
    have e11 : σ (.n (b + 11)) = y * y := e 11 (by omega)
    have e12 : σ (.n (b + 12)) = y * y * ofK ((digestScalars (sqCv cv)).2.limb 0) :=
      e 12 (by omega)
    have e13 : σ (.n (b + 13)) = challengeOf (sqCv cv) := e 13 (by omega)
    have e5 : σ (.n (b + 5)) = (digestScalars (sqCv cv)).1 := e 5 (by omega)
    have e6 : σ (.n (b + 6)) = (digestScalars (sqCv cv)).2 := e 6 (by omega)
    refine ⟨⟨cv, hcv, fun k hk => by rw [e k (by omega)]; interval_cases k <;> rfl⟩,
      by rw [e8, e6, e7], e9, by rw [e10, e8, e9], ⟨by rw [e7]; exact ofK_isInK _, ?_⟩, e11,
      by rw [e12, e11, e7], ?_, hn⟩
    · rw [e10, word_y_inv]
      exact ((split_iff _ _).mpr ⟨(isCanonical128_digestScalars _).2, rfl⟩).2
    · rw [e13, e12, e5, challenge_from_state_eq]

end
end LeanVM.Guest.B1
