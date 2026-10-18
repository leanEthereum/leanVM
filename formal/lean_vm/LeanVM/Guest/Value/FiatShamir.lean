/-
  LeanVM.Guest.Value.FiatShamir

  The guest's Fiat-Shamir gadgets as values: absorbing a scalar, squeezing a state, reading a
  challenge out of it, absorbing a grinding nonce and checking the proof of work, each the
  specification's step on the state's two cells.
-/

module

public import LeanVM.Guest.Value.Hash
public import LeanVM.Guest.Value.Bits
public import LeanVM.Spec.Node

/-!
# Fiat-Shamir in cells

The guest carries a Fiat-Shamir state as the two cells of a digest (`digestScalars`), and every
step is one `BLAKE2S` under the default IV (`Hash.blake2s_default_iff`) of the state's 32 bytes
and a 32-byte block, as `Spec/Verifier.lean`'s chain is (`absorbBlock`, V:522; `Compile.run`,
V:555-589; `Node.observe`, `Node.squeeze`, N:203-211):

| guest (G) | block | here |
|---|---|---|
| `fs_compress(state, x, tail, out)` (488-497) | `blockOf x tail` | `fs_compress_iff` |
| `obs` (501-506), `fs_next` (510-518) | `blockOf x 1` (`.read`, `Node.observe`) | `obs_iff` |
| `absorb_nonce` (538-542) | `blockOf n 4` (`.grind`'s new state) | `absorb_nonce_iff` |
| `squeeze_state` (522-525) | `blockOf 0 2` (`.sample`, `Node.squeeze`) | `squeeze_state_iff` |
| `challenge_from_state` (472-484) | `challengeOf` (V:477) | `challenge_from_state_iff`, `_eq` |
| `squeeze` (529-534), `squeeze_step` (546-555) | both | `squeeze_spec` |
| `grind_check` (701-734) | `blockOf 0 3`, then `blockOf n 4`; `powOk` (V:482) | `grind_check_sound`, `_complete` |

A scalar's block is its three limbs, then the tag (`blockOf`, `lib.rs:36-43`): `fs_compress`
hints the top limb `l2` and lands the scalar in two canonical cells, `x + y²·l2` (whose top limb
`BLAKE2S` reads as zero, which pins `l2`: `Tower.top_pin_iff`) and `l2 + y·tail`. The tags are
the guest's `DS_*` (G:51-54), integers below 256 (`kBytes_ofBits_tag`).
-/

namespace LeanVM.Guest.Value

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Blocks -/

/-- A tag below 256 is the eight bytes of its word. -/
theorem kBytes_ofBits_tag : ∀ tag < 256, kBytes (K.ofBits tag) = tagBytes tag := by decide +kernel

/-- The 64 bytes of a state and a scalar's block, as four cells. -/
theorem blockBytes_fs (cv : Digest) (x : E) {tag : ℕ} (htag : tag < 256) :
    blockBytes ![(digestScalars cv).1, (digestScalars cv).2, E.ofLimbs (x.limb 0) (x.limb 1) 0,
      E.ofLimbs (x.limb 2) (K.ofBits tag) 0] = digestBytes cv ++ blockOf x tag := by
  rw [blockBytes, digestBytes_eq, blockOf, ← kBytes_ofBits_tag tag htag]
  simp [cellBytes, List.append_assoc]

/-- The four cells `fs_compress(state, x, tail, out)` hashes (G:488-497): the state's two cells,
then `x + y²·l2` and `l2 + y·tail`, with `l2` the hinted top limb. -/
def fsBlock (st : E × E) (x l2 tail : E) : Fin 4 → E := ![st.1, st.2, x + y * y * l2, l2 + y * tail]

/-- With its top limb pinned, the block is the scalar's limbs and the tag. -/
theorem fsBlock_eq (cv : Digest) (x : E) (tag : ℕ) :
    fsBlock (digestScalars cv) x (ofK (x.limb 2)) (eOfNat tag) =
      ![(digestScalars cv).1, (digestScalars cv).2, E.ofLimbs (x.limb 0) (x.limb 1) 0,
        E.ofLimbs (x.limb 2) (K.ofBits tag) 0] := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact top_pin_eq x
  · exact ofK_add_y_mul_ofK _ _

theorem fsBlock_canonical (cv : Digest) (x : E) (tag : ℕ) :
    ∀ i, IsCanonical128 (fsBlock (digestScalars cv) x (ofK (x.limb 2)) (eOfNat tag) i) := by
  rw [fsBlock_eq]
  intro i
  fin_cases i
  · exact (isCanonical128_digestScalars cv).1
  · exact (isCanonical128_digestScalars cv).2
  · rfl
  · rfl

/-! ## Absorbing a scalar (`fs_compress`, `obs`, `absorb_nonce`) -/

/-- **`fs_compress(state, x, tail, out)`** (G:488-497; TRIAGE #5): from the state of the digest
`cv`, the hinted top limb `l2` in `K` (`assert_in_k`) and the compression of the block (whose
`BLAKE2S` requires canonical cells) hold exactly when `l2` is `x`'s top limb and the output is the
state after absorbing `blockOf x tag`, `absorbBlock cv (blockOf x tag)` (V:522). -/
theorem fs_compress_iff (cv : Digest) (x : E) {tag : ℕ} (htag : tag < 256) (l2 out0 out1 : E) :
    (IsInK l2 ∧ CompressCells (fsBlock (digestScalars cv) x l2 (eOfNat tag)) ivCells.1 ivCells.2
      out0 out1 (metadataCell 64 true)) ↔
      l2 = ofK (x.limb 2) ∧
        (out0, out1) = digestScalars (blake2sBytes (digestBytes cv ++ blockOf x tag)) := by
  constructor
  · rintro ⟨hl2, hc⟩
    have hl : l2 = ofK (x.limb 2) := (top_pin_iff x l2).mp ⟨hl2, hc.1 2⟩
    subst hl
    refine ⟨rfl, ?_⟩
    rw [← blockBytes_fs cv x htag, ← fsBlock_eq]
    exact blake2s_default hc
  · rintro ⟨rfl, hout⟩
    refine ⟨ofK_isInK _, (blake2s_default_iff (fsBlock_canonical cv x tag)).mpr ?_⟩
    rw [fsBlock_eq, blockBytes_fs cv x htag]
    exact hout

/-- The deployed chain's absorb is BLAKE2s of the state's bytes and the block. -/
theorem absorbBlock_blake2sBytes (cv : Digest) (b : Bytes) :
    absorbBlock (m := Id) blake2sBytes cv b = blake2sBytes (digestBytes cv ++ b) := rfl

/-- `Node.observe x` (N:203-205) is that absorb at tag 1. -/
theorem observe_apply (x : E) (cv : Digest) :
    Node.observe x cv = ((), blake2sBytes (digestBytes cv ++ blockOf x 1)) := rfl

/-- **`obs(state, x)`** (G:501-506; `fs_next`, G:510-518; TRIAGE #6, #7): `fs_compress` at
`DS_OBSERVE = 1` is `Node.observe x`, the `.read` step of `Compile.run` (V:558-562). -/
theorem obs_iff (cv : Digest) (x l2 out0 out1 : E) :
    (IsInK l2 ∧ CompressCells (fsBlock (digestScalars cv) x l2 (eOfNat 1)) ivCells.1 ivCells.2
      out0 out1 (metadataCell 64 true)) ↔
      l2 = ofK (x.limb 2) ∧ (out0, out1) = digestScalars (Node.observe x cv).2 :=
  fs_compress_iff cv x (by decide) l2 out0 out1

/-- **`absorb_nonce(state, x)`** (G:538-542; TRIAGE #10): `fs_compress` at `DS_POW_NONCE = 4` is
the state `.grind` moves to, `absorbBlock cv (blockOf x 4)` (V:566-572). -/
theorem absorb_nonce_iff (cv : Digest) (x l2 out0 out1 : E) :
    (IsInK l2 ∧ CompressCells (fsBlock (digestScalars cv) x l2 (eOfNat 4)) ivCells.1 ivCells.2
      out0 out1 (metadataCell 64 true)) ↔
      l2 = ofK (x.limb 2) ∧
        (out0, out1) = digestScalars (absorbBlock (m := Id) blake2sBytes cv (blockOf x 4)) :=
  fs_compress_iff cv x (by decide) l2 out0 out1

/-! ## Squeezing (`squeeze_state`, `challenge_from_state`, `squeeze`) -/

/-- **`squeeze_state(state)`** (G:522-525; TRIAGE #8), and `grind_check`'s base at
`DS_POW_BASE = 3` (G:713-714): `blake2s(state, [0, Y_TOWER·tag], out)` is the state after
absorbing `blockOf 0 tag`. -/
theorem squeeze_state_iff (cv : Digest) {tag : ℕ} (htag : tag < 256) (out0 out1 : E) :
    CompressCells ![(digestScalars cv).1, (digestScalars cv).2, 0, y * eOfNat tag] ivCells.1
      ivCells.2 out0 out1 (metadataCell 64 true) ↔
      (out0, out1) = digestScalars (blake2sBytes (digestBytes cv ++ blockOf 0 tag)) := by
  have hb : (![(digestScalars cv).1, (digestScalars cv).2, 0, y * eOfNat tag] : Fin 4 → E) =
      ![(digestScalars cv).1, (digestScalars cv).2, E.ofLimbs ((0 : E).limb 0) ((0 : E).limb 1) 0,
        E.ofLimbs ((0 : E).limb 2) (K.ofBits tag) 0] := by
    have h0 : ((0 : E).limb 0) = 0 ∧ (0 : E).limb 1 = 0 ∧ (0 : E).limb 2 = 0 :=
      ⟨limb_zero 0, limb_zero 1, limb_zero 2⟩
    rw [h0.1, h0.2.1, h0.2.2, ← zero_eq_ofLimbs, ← ofK_add_y_mul_ofK, ofK_zero, zero_add]
    rfl
  rw [hb, blake2s_default_iff, blockBytes_fs cv 0 htag]
  intro i
  fin_cases i
  · exact (isCanonical128_digestScalars cv).1
  · exact (isCanonical128_digestScalars cv).2
  · rfl
  · rfl

/-- `Node.squeeze` (N:207-211) from `cv`: the state after absorbing `blockOf 0 2`, and its
challenge. -/
theorem squeeze_apply (cv : Digest) :
    Node.squeeze cv = (challengeOf (blake2sBytes (digestBytes cv ++ blockOf 0 2)),
      blake2sBytes (digestBytes cv ++ blockOf 0 2)) := rfl

/-- **`challenge_from_state(state)`** (G:472-484; TRIAGE #4): over a state of the digest `d`, the
hinted `d2` and the derived `(state[1] + d2)·y⁻¹` lie in `K` exactly when `d2` is the second
cell's low limb. -/
theorem challenge_from_state_iff (d : Digest) (d2 : E) :
    IsInK d2 ∧ IsInK (((digestScalars d).2 + d2) * y⁻¹) ↔
      d2 = ofK ((digestScalars d).2.limb 0) :=
  (split_iff _ d2).trans ⟨fun h ↦ h.2, fun h ↦ ⟨(isCanonical128_digestScalars d).2, h⟩⟩

/-- The challenge `state[0] + y²·d2` is `challengeOf d` (V:477): the digest's three low 64-bit
words. -/
theorem challenge_from_state_eq (d : Digest) :
    (digestScalars d).1 + y * y * ofK ((digestScalars d).2.limb 0) = challengeOf d := by
  rw [add_y_mul_y_mul_ofK]
  simp only [digestScalars, wordsCell, challengeOf, ofLimbs_limb0, ofLimbs_limb1, ofLimbs_limb2,
    zero_add]
  rfl

/-- **`squeeze(state)`** (G:529-534; `squeeze_step`, G:546-555; TRIAGE #9, #11): the new state
and the challenge are `Node.squeeze`'s, the `.sample` step of `Compile.run` (V:563-565). -/
theorem squeeze_spec (cv : Digest) {nb0 nb1 d2 : E}
    (hc : CompressCells ![(digestScalars cv).1, (digestScalars cv).2, 0, y * eOfNat 2] ivCells.1
      ivCells.2 nb0 nb1 (metadataCell 64 true))
    (hd2 : IsInK d2) (hd3 : IsInK ((nb1 + d2) * y⁻¹)) :
    (nb0, nb1) = digestScalars (Node.squeeze cv).2 ∧ nb0 + y * y * d2 = (Node.squeeze cv).1 := by
  have h := (squeeze_state_iff cv (by decide) nb0 nb1).mp hc
  have h0 : nb0 = (digestScalars (blake2sBytes (digestBytes cv ++ blockOf 0 2))).1 :=
    congrArg Prod.fst h
  have h1 : nb1 = (digestScalars (blake2sBytes (digestBytes cv ++ blockOf 0 2))).2 :=
    congrArg Prod.snd h
  subst h0 h1
  rw [squeeze_apply, (challenge_from_state_iff _ d2).mp ⟨hd2, hd3⟩, challenge_from_state_eq]
  exact ⟨rfl, rfl⟩

/-! ## Grinding (`grind_check`, G:701-737) -/

/-- The low 64-bit word of a digest's first cell. -/
theorem kToNat_digestScalars_limb0 (d : Digest) :
    kToNat ((digestScalars d).1.limb 0) = d[0].toNat + 2 ^ 32 * d[1].toNat := by
  simp only [digestScalars, wordsCell, ofLimbs_limb0, ofWords, kToNat, BF64.toBitVec_ofBitVec,
    BitVec.toNat_append, UInt32.toNat_toBitVec]
  change d[1].toNat <<< 32 ||| d[0].toNat = _
  rw [Nat.shiftLeft_eq, Nat.mul_comm, two_pow_mul_or d[0].toNat_lt, Nat.add_comm]

/-- **`grind_check(state, nonce, g^bits)` is sound** (G:701-734; TRIAGE #18): from the state of
`cv`, if the guest's constraints hold (at `g^bits = 1` the nonce is zero, G:710-711; the base
squeeze at `DS_POW_BASE`, G:713-714; the nonce absorbed at `DS_POW_NONCE`, G:715-716; the
output's low lane split off, G:717-720, decomposed into 64 Boolean bits, G:723-730, of which the
low `bits` are zero, G:732-733), then `powOk bits nonce` (V:482) holds of the digest `.grind`
checks (V:566-572). -/
theorem grind_check_sound (cv : Digest) {nonce : E} {bits : ℕ} (hbits : bits ≤ 64)
    {base0 base1 l2 out0 out1 lane : E} {lb : ℕ → E}
    (hzero : gen ^ bits = 1 → nonce = 0)
    (hbase : CompressCells ![(digestScalars cv).1, (digestScalars cv).2, 0, y * eOfNat 3]
      ivCells.1 ivCells.2 base0 base1 (metadataCell 64 true))
    (hl2 : IsInK l2)
    (hout : CompressCells (fsBlock (base0, base1) nonce l2 (eOfNat 4)) ivCells.1 ivCells.2 out0
      out1 (metadataCell 64 true))
    (hlane : IsInK lane ∧ IsInK ((out0 + lane) * y⁻¹))
    (hb : ∀ i < 64, lb i * lb i = lb i)
    (hsum : ∑ i ∈ Finset.range 64, lb i * coordBasis i = lane)
    (hz : ∀ i < bits, lb i = 0) :
    powOk bits nonce
      (blake2sBytes (digestBytes (blake2sBytes (digestBytes cv ++ blockOf 0 3)) ++
        blockOf nonce 4)) = true := by
  set B := blake2sBytes (digestBytes cv ++ blockOf 0 3)
  set D := blake2sBytes (digestBytes B ++ blockOf nonce 4)
  have hB := (squeeze_state_iff cv (by decide) base0 base1).mp hbase
  rw [hB] at hout
  have hD := ((fs_compress_iff B nonce (by decide) l2 out0 out1).mp ⟨hl2, hout⟩).2
  have hout0 : out0 = (digestScalars D).1 := congrArg Prod.fst hD
  have hlane' : lane = ofK (out0.limb 0) := ((split_iff out0 lane).mp ⟨hlane.1, hlane.2⟩).2
  obtain ⟨_, hbits'⟩ := bits_of_reconstruct_zero (by decide) hb hsum
  have hN : eToNat lane = kToNat (out0.limb 0) := by
    rw [hlane', eToNat]
    simp [limb_ofK, kToNat]
  unfold powOk
  split
  · rename_i h0
    subst h0
    have := hzero (pow_zero gen)
    subst this
    simp [limb_zero]
  · rename_i h0
    simp only [decide_eq_true_eq]
    rw [← kToNat_digestScalars_limb0, ← hout0, ← hN]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hi : i < bits
    · have h1 := hbits' i (by omega)
      rw [hz i hi] at h1
      have : (eToNat lane).testBit i = false := by
        cases h : (eToNat lane).testBit i
        · rfl
        · rw [h] at h1
          exact absurd h1 (by simp [bitE])
      simp [hi, this]
    · simp [hi]

/-- **`grind_check` is complete**: when `powOk bits nonce D` holds, the honest values meet the
guest's checks: the nonce is zero at `g^bits = 1`, and the low `bits` bits of the digest's first
lane, which the honest `lane_bits` hold, are zero. -/
theorem grind_check_complete {nonce : E} {bits : ℕ} {D : Digest} (hbits : bits ≤ 64)
    (h : powOk bits nonce D = true) :
    (gen ^ bits = 1 → nonce = 0) ∧
      ∀ i < bits, (kToNat ((digestScalars D).1.limb 0)).testBit i = false := by
  unfold powOk at h
  split at h
  · rename_i h0
    subst h0
    simp only [decide_eq_true_eq] at h
    refine ⟨fun _ ↦ ?_, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩
    rw [eq_ofLimbs nonce, h.1, h.2.1, h.2.2, ← zero_eq_ofLimbs]
  · rename_i h0
    simp only [decide_eq_true_eq] at h
    refine ⟨fun h1 ↦ absurd ((gen_pow_eq_one_iff (by omega)).mp h1) h0, fun i hi ↦ ?_⟩
    rw [kToNat_digestScalars_limb0]
    have := congrArg (fun n ↦ n.testBit i) h
    simp only [Nat.testBit_mod_two_pow, Nat.zero_testBit] at this
    simpa [hi] using this

end
end LeanVM.Guest.Value
