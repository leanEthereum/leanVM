import XmssSecurity.Scan.SignStep

/-!
# The potentials of the adversary phase

Summed over leaf indices, each read on the leaf index's frozen cache:
* `openΦ`: the partner mass `Φ` of the unsigned leaf indices;
* `hvSum`: `V · H`;
* `nCount`, `vCount`: the cached inputs and the cached hits;
* `PreBad`: a first entry selected a cached input partnered in its initial cache;
* `PostBad`: a first entry selected a cached input, and a later query repeated its digest.

This file proves how one fresh oracle answer moves each of them.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Ghost

open Partner

local notation "N" => ((2 ^ digestBits : ℕ) : ℝ≥0∞)

theorem N_ne_zero : N ≠ 0 := by simp

theorem N_ne_top : N ≠ ⊤ := ENNReal.natCast_ne_top _

theorem N_mul_inv : N * N⁻¹ = 1 := ENNReal.mul_inv_cancel N_ne_zero N_ne_top

variable (parameter : PublicParameter)

/-- No entry at the leaf index yet. -/
def Unsigned (trace : SigningCacheTrace) (leafIndex : LeafIndex) : Prop := first trace leafIndex = none

instance (trace : SigningCacheTrace) (leafIndex : LeafIndex) : Decidable (Unsigned trace leafIndex) :=
  decidable_of_iff ((first trace leafIndex).isNone = true) Option.isNone_iff_eq_none

noncomputable def nCount (cache : QueryCache HashSpec) (trace : SigningCacheTrace) : ℕ :=
  ∑ e, C (frozen cache trace e) parameter e

noncomputable def vCount (cache : QueryCache HashSpec) (trace : SigningCacheTrace) : ℕ :=
  ∑ e, V (frozen cache trace e) parameter e

noncomputable def hvSum (cache : QueryCache HashSpec) (trace : SigningCacheTrace) : ℝ≥0∞ :=
  ∑ e, (V (frozen cache trace e) parameter e : ℝ≥0∞) * H (frozen cache trace e) parameter e

noncomputable def openΦ (cache : QueryCache HashSpec) (trace : SigningCacheTrace) : ℝ≥0∞ :=
  ∑ e, if Unsigned trace e then Φ cache parameter e else 0

/-- The partner step's cost of a query. -/
noncomputable def aCost (x : HashInput) (cache : QueryCache HashSpec) (trace : SigningCacheTrace) :
    ℝ≥0∞ :=
  (dec parameter x).elim 0 fun p => if cache x = none ∧ Unsigned trace p.1 then
    (V cache parameter p.1 : ℝ≥0∞) * W cache parameter p.1 p.2 + H cache parameter p.1 else 0

/-- A fresh encoding query at an unsigned leaf index. -/
noncomputable def openInd (x : HashInput) (cache : QueryCache HashSpec) (trace : SigningCacheTrace) :
    ℝ≥0∞ :=
  (dec parameter x).elim 0 fun p => if cache x = none ∧ Unsigned trace p.1 then 1 else 0

/-- An encoding query at a signed leaf index. -/
noncomputable def signedInd (x : HashInput) (trace : SigningCacheTrace) : ℝ≥0∞ :=
  (dec parameter x).elim 0 fun p => if Unsigned trace p.1 then 0 else 1

/-- The digest a signature selected, `0` if none. -/
noncomputable def selDigest (leafIndex : LeafIndex) (entry : SigningCacheEntry) : Digest :=
  entry.signature.elim 0 fun signature =>
    dig entry.initialCache parameter leafIndex (entry.request.message, signature.randomness)

/-- The digest a query at `x` must hit to repeat a selected one. -/
noncomputable def target (x : HashInput) (trace : SigningCacheTrace) : Digest :=
  (dec parameter x).elim 0 fun p => (first trace p.1).elim 0 fun entry => selDigest parameter p.1 entry

def PreBad (secretKey : SecretKey) (trace : SigningCacheTrace) : Prop :=
  ∃ (e : LeafIndex) (entry : SigningCacheEntry), first trace e = some entry ∧
    entry.CachedSelectionCollision secretKey entry.initialCache

def PostBad (trace : SigningCacheTrace) (cache : QueryCache HashSpec) : Prop :=
  ∃ e entry, first trace e = some entry ∧
    ∃ (signature : Signature) (o : HashOutput) (z : Position) (o' : HashOutput),
    entry.signature = some signature ∧
    entry.initialCache (input parameter e (entry.request.message, signature.randomness)) = some o ∧
    entry.finalCache (input parameter e z) = none ∧ cache (input parameter e z) = some o' ∧
    truncateHash o = truncateHash o'

variable {parameter}

theorem openInd_add_signedInd_le (x : HashInput) (cache : QueryCache HashSpec)
    (trace : SigningCacheTrace) :
    openInd parameter x cache trace + signedInd parameter x trace ≤
      if (dec parameter x).isSome then 1 else 0 := by
  unfold openInd signedInd
  cases dec parameter x with
  | none => simp
  | some p =>
      rw [Option.elim_some, Option.elim_some, Option.isSome_some, ite_eq_left rfl]
      by_cases h : Unsigned trace p.1
      · rw [ite_eq_left h, add_zero]
        split_ifs
        · exact le_rfl
        · exact zero_le
      · rw [ite_eq_right h, ite_eq_right (fun hh => h hh.2), zero_add]

/-! ### Counts under one fresh answer -/

theorem C_cacheQuery {cache : QueryCache HashSpec} {leafIndex : LeafIndex} {y : Position}
    (hx : cache (input parameter leafIndex y) = none) (u : HashOutput) :
    C (cache.cacheQuery (input parameter leafIndex y) u) parameter leafIndex =
      C cache parameter leafIndex + 1 := by
  unfold C
  have hy : y ∉ Finset.univ.filter fun z : Position => (cache (input parameter leafIndex z)).isSome := by
    rw [Finset.mem_filter, hx]; simp
  rw [← Finset.card_insert_of_notMem hy]
  refine congrArg Finset.card (Finset.ext fun z => ?_)
  rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_filter]
  by_cases hz : z = y
  · subst hz
    simp only [QueryCache.cacheQuery_self, Option.isSome_some, and_true, true_or, iff_true]
    exact @Finset.mem_univ Position _ z
  · rw [cacheQuery_input_of_ne y z u hz]
    simp only [hz, false_or]

theorem V_cacheQuery_nat {cache : QueryCache HashSpec} {leafIndex : LeafIndex} {y : Position}
    (hx : cache (input parameter leafIndex y) = none) (u : HashOutput) :
    V (cache.cacheQuery (input parameter leafIndex y) u) parameter leafIndex =
      V cache parameter leafIndex + if outcome u = .hit then 1 else 0 := by
  have h := V_cacheQuery hx u
  split_ifs at h ⊢ <;> exact_mod_cast h

/-- Off the queried leaf index, or at a signed one, the frozen caches agree. -/
theorem frozen_agree_of_dec {cache : QueryCache HashSpec} {trace : SigningCacheTrace} {x : HashInput}
    (u : HashOutput) {leafIndex : LeafIndex}
    (h : ∀ p, dec parameter x = some p → p.1 = leafIndex → first trace leafIndex ≠ none) (y : Position) :
    frozen (cache.cacheQuery x u) trace leafIndex (input parameter leafIndex y) =
      frozen cache trace leafIndex (input parameter leafIndex y) := by
  refine frozen_cacheQuery_agree u ?_ y
  by_cases hf : first trace leafIndex = none
  · refine Or.inr fun z hz => ?_
    subst hz
    exact h _ (dec_input parameter leafIndex z) rfl hf
  · exact Or.inl hf

theorem frozen_agree_of_ne {cache : QueryCache HashSpec} {trace : SigningCacheTrace} (u : HashOutput)
    {leafIndex other : LeafIndex} (z : Position) (hne : other ≠ leafIndex) (y : Position) :
    frozen (cache.cacheQuery (input parameter leafIndex z) u) trace other (input parameter other y) =
      frozen cache trace other (input parameter other y) :=
  frozen_agree_of_dec u (fun p hp hp1 => by
    rw [dec_input, Option.some.injEq] at hp
    subst hp
    exact absurd hp1.symm hne) y

theorem frozen_agree_of_signed {cache : QueryCache HashSpec} {trace : SigningCacheTrace} (u : HashOutput)
    {leafIndex other : LeafIndex} (z : Position) (hs : ¬Unsigned trace leafIndex) (y : Position) :
    frozen (cache.cacheQuery (input parameter leafIndex z) u) trace other (input parameter other y) =
      frozen cache trace other (input parameter other y) :=
  frozen_agree_of_dec u (fun p hp hp1 => by
    rw [dec_input, Option.some.injEq] at hp
    subst hp hp1
    exact hs) y

theorem frozen_agree_of_none {cache : QueryCache HashSpec} {trace : SigningCacheTrace} {x : HashInput}
    (hd : dec parameter x = none) (u : HashOutput) (other : LeafIndex) (y : Position) :
    frozen (cache.cacheQuery x u) trace other (input parameter other y) =
      frozen cache trace other (input parameter other y) :=
  frozen_agree_of_dec u (fun p hp _ => by rw [hd] at hp; cases hp) y

/-! ### One fresh answer -/

section Fresh

variable {cache : QueryCache HashSpec} {trace : SigningCacheTrace}

theorem openΦ_fresh {x : HashInput} (hx : cache x = none) :
    ex (fun u => openΦ parameter (cache.cacheQuery x u) trace) ≤
      openΦ parameter cache trace + aCost parameter x cache trace * N⁻¹ := by
  cases hd : dec parameter x with
  | none =>
      have h : ∀ u, openΦ parameter (cache.cacheQuery x u) trace = openΦ parameter cache trace := fun u =>
        Finset.sum_congr rfl fun e _ => by
          rw [(potentials_cacheQuery_of_not_input (fun y => dec_eq_none parameter hd e y) u).1]
      simp_rw [h]
      rw [ex_const, aCost, hd, Option.elim_none, zero_mul, add_zero]
  | some p =>
      obtain ⟨e, z⟩ := p
      have hxe := dec_eq_some parameter hd
      simp only at hxe
      subst hxe
      unfold openΦ
      rw [ex_sum]
      have hterm : ∀ e' ∈ (Finset.univ : Finset LeafIndex),
          ex (fun u => if Unsigned trace e' then
            Φ (cache.cacheQuery (input parameter e z) u) parameter e' else 0) ≤
          (if Unsigned trace e' then Φ cache parameter e' else 0) +
            if e' = e then aCost parameter (input parameter e z) cache trace * N⁻¹ else 0 := by
        intro e' _
        rw [ex_ite]
        by_cases hu : Unsigned trace e'
        · rw [ite_eq_left hu, ite_eq_left hu]
          by_cases he : e' = e
          · subst he
            rw [ite_eq_left rfl, aCost, dec_input, Option.elim_some, ite_eq_left ⟨hx, hu⟩]
            exact ex_Φ_le hx
          · rw [ite_eq_right he, add_zero]
            have h := fun u => (potentials_cacheQuery_of_not_input (cache := cache)
              (fun y => input_ne_of_ne parameter (Ne.symm he) z y) u).1
            simp_rw [h]
            rw [ex_const]
        · rw [ite_eq_right hu, ite_eq_right hu, zero_add]
          exact zero_le
      refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ e)]

theorem hvSum_fresh {x : HashInput} (hx : cache x = none) :
    hvSum parameter cache trace + landing * aCost parameter x cache trace ≤
      ex (fun u => hvSum parameter (cache.cacheQuery x u) trace) := by
  cases hd : dec parameter x with
  | none =>
      have h : ∀ u, hvSum parameter (cache.cacheQuery x u) trace = hvSum parameter cache trace := fun u =>
        Finset.sum_congr rfl fun e _ => by
          rw [V_congr (frozen_agree_of_none hd u e), H_congr (frozen_agree_of_none hd u e)]
      simp_rw [h]
      rw [ex_const, aCost, hd, Option.elim_none, mul_zero, add_zero]
  | some p =>
      obtain ⟨e, z⟩ := p
      have hxe := dec_eq_some parameter hd
      simp only at hxe
      subst hxe
      unfold hvSum
      rw [ex_sum]
      have hterm : ∀ e' ∈ (Finset.univ : Finset LeafIndex),
          (V (frozen cache trace e') parameter e' : ℝ≥0∞) * H (frozen cache trace e') parameter e' +
            (if e' = e then landing * aCost parameter (input parameter e z) cache trace else 0) ≤
          ex (fun u => (V (frozen (cache.cacheQuery (input parameter e z) u) trace e') parameter e' : ℝ≥0∞) *
            H (frozen (cache.cacheQuery (input parameter e z) u) trace e') parameter e') := by
        intro e' _
        by_cases hopen : e' = e ∧ Unsigned trace e
        · obtain ⟨rfl, hu⟩ := hopen
          rw [ite_eq_left rfl, aCost, dec_input, Option.elim_some, ite_eq_left ⟨hx, hu⟩]
          simp only [frozen_of_none hu]
          refine le_of_eq_of_le ?_ (ex_V_mul_H hx)
          rw [add_comm (_ * W _ _ _ _)]
        · have hagree : ∀ u y, frozen (cache.cacheQuery (input parameter e z) u) trace e'
              (input parameter e' y) = frozen cache trace e' (input parameter e' y) := fun u y => by
            by_cases he : e' = e
            · subst he
              exact frozen_agree_of_signed u z (fun hu => hopen ⟨rfl, hu⟩) y
            · exact frozen_agree_of_ne u z he y
          have hzero : (if e' = e then landing * aCost parameter (input parameter e z) cache trace else 0) = 0 := by
            split_ifs with he
            · subst he
              rw [aCost, dec_input, Option.elim_some, ite_eq_right (fun h => hopen ⟨rfl, h.2⟩), mul_zero]
            · rfl
          rw [hzero, add_zero]
          simp_rw [V_congr (hagree _), H_congr (hagree _)]
          rw [ex_const]
      refine le_of_eq_of_le ?_ (Finset.sum_le_sum hterm)
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ e)]

theorem counts_fresh_closed {x : HashInput}
    (h : ∀ p, dec parameter x = some p → ¬Unsigned trace p.1) (u : HashOutput) :
    nCount parameter (cache.cacheQuery x u) trace = nCount parameter cache trace ∧
      vCount parameter (cache.cacheQuery x u) trace = vCount parameter cache trace := by
  have hagree : ∀ e y, frozen (cache.cacheQuery x u) trace e (input parameter e y) =
      frozen cache trace e (input parameter e y) := fun e y =>
    frozen_agree_of_dec u (fun p hp hp1 => by subst hp1; exact h p hp) y
  exact ⟨Finset.sum_congr rfl fun e _ => C_congr (hagree e),
    Finset.sum_congr rfl fun e _ => V_congr (hagree e)⟩

theorem counts_fresh_open {e : LeafIndex} {z : Position} (hx : cache (input parameter e z) = none)
    (hu : Unsigned trace e) (u : HashOutput) :
    nCount parameter (cache.cacheQuery (input parameter e z) u) trace = nCount parameter cache trace + 1 ∧
      vCount parameter (cache.cacheQuery (input parameter e z) u) trace =
        vCount parameter cache trace + if outcome u = .hit then 1 else 0 := by
  have hrest : ∀ e' ∈ (Finset.univ : Finset LeafIndex).erase e, ∀ y,
      frozen (cache.cacheQuery (input parameter e z) u) trace e' (input parameter e' y) =
        frozen cache trace e' (input parameter e' y) := fun e' he' y =>
    frozen_agree_of_ne u z (Finset.ne_of_mem_erase he') y
  unfold nCount vCount
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e), ← Finset.add_sum_erase _ _ (Finset.mem_univ e),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ e), ← Finset.add_sum_erase _ _ (Finset.mem_univ e)]
  simp only [frozen_of_none hu]
  rw [C_cacheQuery hx, V_cacheQuery_nat hx,
    Finset.sum_congr rfl fun e' he' => C_congr (hrest e' he'),
    Finset.sum_congr rfl fun e' he' => V_congr (hrest e' he')]
  constructor <;> ring

theorem postBad_fresh {x : HashInput} (hx : cache x = none) (u : HashOutput)
    (h : PostBad parameter trace (cache.cacheQuery x u)) :
    PostBad parameter trace cache ∨
      (signedInd parameter x trace = 1 ∧ truncateHash u = target parameter x trace) := by
  obtain ⟨e, entry, hf, signature, o, z, o', hs, ho, hfin, hc, ht⟩ := h
  by_cases hxz : input parameter e z = x
  · subst hxz
    rw [QueryCache.cacheQuery_self, Option.some.injEq] at hc
    subst hc
    have hsigned : ¬Unsigned trace e := by unfold Unsigned; rw [hf]; simp
    refine Or.inr ⟨by rw [signedInd, dec_input, Option.elim_some, ite_eq_right hsigned], ?_⟩
    rw [target, dec_input, Option.elim_some, hf, Option.elim_some, selDigest, hs, Option.elim_some, dig, ho]
    exact ht.symm
  · rw [QueryCache.cacheQuery_of_ne _ _ hxz] at hc
    exact Or.inl ⟨e, entry, hf, signature, o, z, o', hs, ho, hfin, hc, ht⟩

end Fresh

open Classical in
/-- The post-signing collision, as an indicator. -/
noncomputable def postPot (parameter : PublicParameter) (trace : SigningCacheTrace) (cache : QueryCache HashSpec) : ℝ≥0∞ :=
  if trace.leafIndices.Nodup ∧ PostBad parameter trace cache then 1 else 0

theorem postPot_fresh {cache : QueryCache HashSpec} {trace : SigningCacheTrace} {x : HashInput}
    (hx : cache x = none) :
    ex (fun u => postPot parameter trace (cache.cacheQuery x u)) ≤
      postPot parameter trace cache + signedInd parameter x trace * N⁻¹ := by
  have hpoint : ∀ u, postPot parameter trace (cache.cacheQuery x u) ≤ postPot parameter trace cache +
      signedInd parameter x trace * if truncateHash u = target parameter x trace then 1 else 0 := by
    intro u
    unfold postPot
    by_cases h1 : trace.leafIndices.Nodup ∧ PostBad parameter trace (cache.cacheQuery x u)
    · rw [ite_eq_left h1]
      rcases postBad_fresh hx u h1.2 with h | ⟨hs, ht⟩
      · rw [ite_eq_left ⟨h1.1, h⟩]; exact le_self_add
      · rw [hs, ite_eq_left ht, one_mul]; exact le_add_self
    · rw [ite_eq_right h1]; exact zero_le
  refine (ex_mono hpoint).trans (le_of_eq ?_)
  rw [ex_add, ex_const, ex_const_mul, ex_digest]

/-! ### One signing request -/

section Sign

variable (secretKey : SecretKey) {request : SignRequest} {cache : QueryCache HashSpec}
  {trace : SigningCacheTrace} {r : Option Signature × QueryCache HashSpec}

theorem first_append_new_of_unsigned (h : Unsigned trace request.leafIndex) :
    first (trace ++ [⟨request, r.1, cache, r.2⟩]) request.leafIndex = some ⟨request, r.1, cache, r.2⟩ := by
  unfold Unsigned first at h
  unfold first
  rw [List.find?_append, h]
  simp

theorem first_append_eq_of_some {e : LeafIndex} {entry : SigningCacheEntry} (new : SigningCacheEntry)
    (h' : first (trace ++ [new]) e = some entry) :
    first trace e = some entry ∨ (Unsigned trace e ∧ entry = new) := by
  cases h : first trace e with
  | some other =>
      rw [first_append_of_some h] at h'
      exact Or.inl h'
  | none =>
      refine Or.inr ⟨h, ?_⟩
      by_cases hl : new.request.leafIndex = e
      · subst hl
        unfold first at h h'
        rw [List.find?_append, h] at h'
        simpa [eq_comm] using h'
      · rw [first_append_of_ne _ hl, h] at h'
        cases h'

variable (hr : r ∈ support ((simulateQ romImpl (Concrete.scheme.sign secretKey request.leafIndex
  request.message)).run cache))
include hr

theorem counts_sign :
    nCount secretKey.parameter r.2 (trace ++ [⟨request, r.1, cache, r.2⟩]) =
        nCount secretKey.parameter cache trace ∧
      vCount secretKey.parameter r.2 (trace ++ [⟨request, r.1, cache, r.2⟩]) =
        vCount secretKey.parameter cache trace ∧
      hvSum secretKey.parameter r.2 (trace ++ [⟨request, r.1, cache, r.2⟩]) =
        hvSum secretKey.parameter cache trace := by
  have h := fun e => frozen_sign_agree secretKey (trace := trace) hr e
  exact ⟨Finset.sum_congr rfl fun e _ => C_congr (h e),
    Finset.sum_congr rfl fun e _ => V_congr (h e),
    Finset.sum_congr rfl fun e _ => by rw [V_congr (h e), H_congr (h e)]⟩

theorem openΦ_sign :
    openΦ secretKey.parameter r.2 (trace ++ [⟨request, r.1, cache, r.2⟩]) +
        (if Unsigned trace request.leafIndex then Φ cache secretKey.parameter request.leafIndex else 0) =
      openΦ secretKey.parameter cache trace := by
  unfold openΦ
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ request.leafIndex),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ request.leafIndex),
    ite_eq_right (show ¬Unsigned (trace ++ [⟨request, r.1, cache, r.2⟩]) request.leafIndex from
      first_append_self (trace := trace) ⟨request, r.1, cache, r.2⟩), zero_add, add_comm]
  refine congrArg _ (Finset.sum_congr rfl fun e he => ?_)
  have hne := Finset.ne_of_mem_erase he
  have hu : Unsigned (trace ++ [⟨request, r.1, cache, r.2⟩]) e ↔ Unsigned trace e := by
    unfold Unsigned; rw [first_append_of_ne _ (Ne.symm hne)]
  rw [if_congr hu (Φ_congr fun y => sign_other_leaf secretKey hr (Ne.symm hne) y) rfl]

omit hr in
theorem preBad_sign (h : PreBad secretKey (trace ++ [⟨request, r.1, cache, r.2⟩])) :
    PreBad secretKey trace ∨
      (Unsigned trace request.leafIndex ∧
        (⟨request, r.1, cache, r.2⟩ : SigningCacheEntry).CachedSelectionCollision secretKey cache) := by
  obtain ⟨e, entry, hf, hcsc⟩ := h
  rcases first_append_eq_of_some _ hf with hold | ⟨hu, rfl⟩
  · exact Or.inl ⟨e, entry, hold, hcsc⟩
  · by_cases hl : request.leafIndex = e
    · subst hl
      exact Or.inr ⟨hu, hcsc⟩
    · rw [first_append_of_ne _ hl] at hf
      unfold Unsigned at hu
      rw [hu] at hf
      cases hf

theorem postPot_sign :
    postPot secretKey.parameter (trace ++ [⟨request, r.1, cache, r.2⟩]) r.2 ≤
      postPot secretKey.parameter trace cache := by
  unfold postPot
  split_ifs with h1 h2
  · exact le_rfl
  · exfalso
    obtain ⟨hnodup, e, entry, hf, signature, o, z, o', hs, ho, hfin, hc, ht⟩ := h1
    rw [SigningCacheTrace.leafIndices_append, List.nodup_append] at hnodup
    have hfresh : Unsigned trace request.leafIndex :=
      first_eq_none_iff.mpr fun hmem => hnodup.2.2 _ hmem _ (by simp [SigningCacheTrace.leafIndices]) rfl
    rcases first_append_eq_of_some _ hf with hold | ⟨hu, rfl⟩
    · have hne : request.leafIndex ≠ e := fun hl => by
        subst hl; unfold Unsigned at hfresh; rw [hfresh] at hold; cases hold
      rw [sign_other_leaf secretKey hr hne] at hc
      exact h2 ⟨hnodup.1, e, entry, hold, signature, o, z, o', hs, ho, hfin, hc, ht⟩
    · by_cases hl : request.leafIndex = e
      · subst hl
        change r.2 _ = none at hfin
        rw [hfin] at hc
        cases hc
      · rw [first_append_of_ne _ hl] at hf
        unfold Unsigned at hu
        rw [hu] at hf
        cases hf
  · exact zero_le
  · exact le_rfl

end Sign

end XmssSecurity.Ghost
