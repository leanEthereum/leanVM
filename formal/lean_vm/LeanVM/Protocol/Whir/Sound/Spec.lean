/-
  LeanVM.Protocol.Whir.Sound.Spec

  The round-by-round soundness of the deployed WHIR opening as a specification of the verifier
  program: `whirSpec` for `verifyWhir` from "every candidate violates the claim", and
  `stackedSpec` for `verifyStackedOpening` from "every candidate violates one of the pooled
  claims", with the explicit escape bound `whirEps`.
-/

module

public import LeanVM.Protocol.Whir.Sound.Start

/-!
# The specification of the WHIR opening

For the ladder of levels `config = derive_config(μ, R)` (`LeanVM.Protocol.Verifier.deriveConfig`)
and a code `codes i` per level (message variables `κ_i`, rate `2^-R_i`, Johnson slack `η_i`):

* `LadderArith`: the arithmetic of the ladder (`κ_i` is the number of variables left after level
  `i`'s folds, `R_i` the level's rate) and the joint groups' escapes below `1` (the hypothesis of
  `Spec.ofNoMove`);
* `levelEps codes i levels`, `whirEps codes config`: the largest group escape, **the `εmax` of the
  opening**:

  `max_i max( (2·L_i + 2^(ℓ_i−1)·E_i)/|E|,  C(L_{i+1}, 2)·κ_i/|E|,
             2^-17·(((A_i − 1)/n_i)^{t_i} + (t_i + 1)·L_{i+1}/|E|) )`
  over the levels with a next level, and for the final level
  `max( (2·L + 2^(ℓ−1)·E)/|E|, 2^-17·(((A − 1)/n)^t + t/|E|), 2/|E| )`, where `L_i = listMax`,
  `E_i = mcaMax` (ArkLib's `johnsonExceptionCount`), `A_i = thr`, `n_i = 2^(κ_i+R_i)`.
* `levelsSpec`: the levels from `LevelPre` of the first, returning never in doom;
* `whirSpec`: **`verifyWhir μ R t w` from `WhirPre`**: the level-0 commitment (the first in the
  history) is shaped as the ladder's level 0, and every candidate of its word at the Johnson
  threshold violates `(w, t)`, for `w` multiaffine (`isMultiaffine_of_isMultilinearFn`).
  Post `False`:
  the program does not return in doom. Lead `0` (it starts with a round polynomial).
* `stackedSpec`: **`verifyStackedOpening μ R claims` from "every candidate violates one of the
  claims"**, with the batching challenge's escape `eBatch J P₀ = (J − 1)·L₀/|E|` as lead.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset

@[expose] public section

/-! ## The ladder -/

section Ladder

variable (μ : ℕ) (codes : ℕ → LevelCode)

/-- The arithmetic of the ladder and the joint groups' escapes below `1`. -/
def LadderArith : ℕ → ℕ → List Whir.Level → Prop
  | _, _, [] => True
  | i, pre, [level] => (codes i).κ + pre + level.fold = μ ∧ (codes i).R = level.logInvRate ∧
      eQueryFinal (codes i) level.queries < 1
  | i, pre, level :: next :: rest => (codes i).κ + pre + level.fold = μ ∧
      (codes i).R = level.logInvRate ∧ eOod (codes (i + 1)) (codes i).κ < 1 ∧
      eQuery (codes i) (codes (i + 1)) level.queries < 1 ∧
      LadderArith (i + 1) (pre + level.fold) (next :: rest)

/-- **The largest group escape** of the levels from level `i`. -/
noncomputable def levelEps : ℕ → List Whir.Level → ENNReal
  | _, [] => 0
  | i, [level] => max (eFold (codes i) level.fold)
      (max ((2 : ENNReal)⁻¹ ^ Whir.queryGrindingBits * eQueryFinal (codes i) level.queries) eTail)
  | i, level :: next :: rest => max (max (eFold (codes i) level.fold) (eOod (codes (i + 1))
      (codes i).κ)) (max ((2 : ENNReal)⁻¹ ^ Whir.queryGrindingBits *
        eQuery (codes i) (codes (i + 1)) level.queries) (levelEps (i + 1) (next :: rest)))

/-- **The `εmax` of the WHIR opening.** -/
noncomputable def whirEps (config : List Whir.Level) : ENNReal := levelEps codes 0 config

/-- The doom at the start of the levels from `i`. -/
def LevelPreL (ℓ₀ : ℕ) (w : List E → E) : ℕ → ℕ → List Whir.Level → WhirState →
    List (ℕ × ℕ × Word) → Prop
  | _, _, [], _, _ => True
  | i, pre, level :: _, s, cs => LevelPre μ ℓ₀ w i (codes i) level.fold pre s cs

end Ladder

/-! ## A return in doom is impossible -/

/-- A specification whose program never returns in doom admits any follower's allowance. -/
def anyT {α : Type} {p : Prog α} {Pre : List Ev → Prop} {εmax L T : ENNReal}
    (S : Spec p Pre (fun _ _ ↦ False) εmax L T) (T' : ENNReal) :
    Spec p Pre (fun _ _ ↦ False) εmax L T' :=
  { S with retDoom := fun hl ha hD ↦ (S.post hl ha hD).elim }

/-! ## The levels -/

variable {μ ℓ₀ : ℕ} {w : List E → E} {codes : ℕ → LevelCode} {εmax : ENNReal}

/-- **The levels' specification.** -/
noncomputable def levelsSpec (hw : IsMultiaffine μ w) (hℓ₀ : ℓ₀ ≤ μ) :
    (levels : List Whir.Level) → (i pre : ℕ) → LadderArith μ codes i pre levels →
      levelEps codes i levels ≤ εmax → (s : WhirState) →
      Spec (whirLevels μ ℓ₀ w i levels s)
        (fun h ↦ LevelPreL μ codes ℓ₀ w i pre levels s (commits h)) (fun _ _ ↦ False) εmax εmax 0
  | [], i, pre, _, _, s => (Spec.fail (Pre := fun h ↦ LevelPreL μ codes ℓ₀ w i pre [] s (commits h))
      (Post := fun _ _ ↦ False)).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl zero_le le_rfl
  | [level], i, pre, hA, hε, s =>
    finSpec ⟨hw, hℓ₀, hA.1, hA.2.1⟩ ((le_max_left _ _).trans hε) hA.2.2
      ((le_max_left _ _).trans ((le_max_right _ _).trans hε))
      ((le_max_right _ _).trans ((le_max_right _ _).trans hε)) s
  | level :: next :: rest, i, pre, hA, hε, s =>
    midSpec ⟨hw, hℓ₀, hA.1, by
        have := hA.2.2.2.2
        cases rest <;> exact this.1, hA.2.1, by
        have := hA.2.2.2.2
        cases rest <;> exact this.2.1⟩
      ((le_max_left _ _).trans ((le_max_left _ _).trans hε))
      ((le_max_right _ _).trans ((le_max_left _ _).trans hε)) hA.2.2.1 hA.2.2.2.1
      ((le_max_left _ _).trans ((le_max_right _ _).trans hε))
      (fun s' ↦ levelsSpec hw hℓ₀ (next :: rest) (i + 1) (pre + level.fold) hA.2.2.2.2
        ((le_max_right _ _).trans ((le_max_right _ _).trans hε)) s') s

/-! ## The opening -/

/-- `verifyWhir` on an admissible shape: the first round polynomial, then the levels. -/
theorem verifyWhir_eq {R : ℕ} {t : E} {level : Whir.Level} {rest : List Whir.Level}
    (hc : deriveConfig μ R = some (level :: rest)) :
    verifyWhir μ R t w = (sumcheckRoundPoly 3 t none).bind fun quad ↦
      whirLevels μ level.fold w 0 (level :: rest) ⟨t, quad, [], []⟩ := by
  rw [verifyWhir, hc]
  rfl

/-- **The specification of the WHIR opening.** From `WhirPre` (the level-0 commitment is the
history's first, of the shape of the ladder's level `0`, and every candidate of its word violates
`(w, t)`), the opening's groups escape with probability at most `εmax ≥ whirEps codes config`
each, and it never returns in doom. -/
noncomputable def whirSpec {R : ℕ} {t : E} {level : Whir.Level} {rest : List Whir.Level}
    (hc : deriveConfig μ R = some (level :: rest)) (hℓ : level.fold = laneBits)
    (hμ : laneBits ≤ μ) (hκ₀ : (codes 0).κ = μ - laneBits) (hR₀ : (codes 0).R = R)
    (hw : IsMultiaffine μ w) (hA : LadderArith μ codes 0 0 (level :: rest))
    (hε : whirEps codes (level :: rest) ≤ εmax) (T : ENNReal) :
    Spec (verifyWhir μ R t w) (fun h ↦ WhirPre μ R (codes 0) w t (commits h))
      (fun _ _ ↦ False) εmax 0 T :=
  anyT (Spec.congr (p' := verifyWhir μ R t w) (by rw [verifyWhir_eq hc, hℓ]; rfl)
    ((roundPolyInv (WhirPre μ R (codes 0) w t) t (T := εmax) le_rfl).bind' fun quad ↦
      (levelsSpec (ℓ₀ := laneBits) hw hμ (level :: rest) 0 0 hA hε ⟨t, quad, [], []⟩).mono
        (fun h hp ↦ by
          show LevelPre μ laneBits w 0 (codes 0) level.fold 0 _ _
          rw [hℓ]
          exact levelPre_zero (codes 0) hκ₀ hR₀ hμ w t quad (commits h) hp.2 hp.1)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)) T

/-! ## The stacked opening -/

/-- The batching challenge's escape: `(J − 1)·L₀ / |E|`. -/
noncomputable def eBatch (J : ℕ) (P₀ : LevelCode) : ENNReal :=
  (((J - 1) * P₀.listMax : ℕ) : ENNReal) / Fintype.card E

/-- The opening's pooled relation: the level-0 commitment has the right shape and every candidate
violates at least one of the claims. -/
def StackedPre (μ R : ℕ) (P₀ : LevelCode) (claims : List StackClaim)
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  ShapeOK 0 P₀ laneBits cs ∧
    ∀ q ∈ Candidates μ R P₀.thr (wordOf cs 0), ∃ c ∈ claims, ¬ StackClaim.Holds μ c q

/-- `dot (powersFrom acc ρ J) (l.map f)` is `Σ_t acc ρ^t f(l_t)`. -/
theorem dot_powersFrom_map {α : Type*} (ρ : E) (f : α → E) :
    ∀ (l : List α) (acc : E), dot (powersFrom acc ρ l.length) (l.map f) =
      ∑ k : Fin l.length, acc * ρ ^ (k : ℕ) * f l[k]
  | [], acc => by simp [dot, powersFrom]
  | x :: l, acc => by
    have ih := dot_powersFrom_map ρ f l (acc * ρ)
    rw [dot, foldl_add_eq, zero_add] at ih ⊢
    simp only [List.length_cons, powersFrom, List.map_cons, List.zipWith_cons_cons,
      List.sum_cons, ih, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
    exact congrArg₂ (· + ·) (by simp) (Finset.sum_congr rfl fun k _ ↦ by
      simp only [Fin.getElem_fin, Fin.val_succ, List.getElem_cons_succ]; ring)

/-- `dot (powers ρ J) (l.map f)` is `Σ_t ρ^t f(l_t)`. -/
theorem dot_powers_map {α : Type*} (ρ : E) (f : α → E) (l : List α) :
    dot (powers ρ l.length) (l.map f) = ∑ k : Fin l.length, ρ ^ (k : ℕ) * f l[k] := by
  rw [powers, dot_powersFrom_map]
  simp

/-- The batched weight of multiaffine claims is multiaffine. -/
theorem isMultiaffine_batched {μ : ℕ} (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine μ c.1) (ρ : E) :
    IsMultiaffine μ fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point) := by
  simp only [dot_powers_map]
  exact IsMultiaffine.sum _ _ fun k _ ↦ (hcl _ (List.getElem_mem _)).const_mul _

/-- The batched claim holds exactly when the discrepancies' power combination vanishes. -/
theorem batch_iff {J N : ℕ} (A : Fin J → Fin N → E) (g : Fin N → E) (c : Fin J → E) (ρ : E) :
    (∑ j : Fin N, (∑ k : Fin J, ρ ^ (k : ℕ) * A k j) * g j = ∑ k : Fin J, ρ ^ (k : ℕ) * c k) ↔
      ∑ k : Fin J, ((∑ j : Fin N, A k j * g j) - c k) * ρ ^ (k : ℕ) = 0 := by
  have h : ∑ k : Fin J, ((∑ j : Fin N, A k j * g j) - c k) * ρ ^ (k : ℕ) =
      (∑ j : Fin N, (∑ k : Fin J, ρ ^ (k : ℕ) * A k j) * g j) -
        ∑ k : Fin J, ρ ^ (k : ℕ) * c k := by
    calc ∑ k : Fin J, ((∑ j : Fin N, A k j * g j) - c k) * ρ ^ (k : ℕ)
        = ∑ k : Fin J, (∑ j : Fin N, A k j * g j) * ρ ^ (k : ℕ) -
            ∑ k : Fin J, c k * ρ ^ (k : ℕ) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun k _ ↦ by ring
      _ = _ := by
          refine congrArg₂ (· - ·) ?_ (Finset.sum_congr rfl fun k _ ↦ by ring)
          simp only [Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  rw [h, sub_eq_zero]

open Classical in
/-- **The batching step**: at most `(J − 1)·listMax₀` challenges `ρ` let a candidate satisfy the
batched claim when every candidate violates one of the claims. -/
theorem card_batch_bad_le {μ R : ℕ} (P₀ : LevelCode) (hκ : P₀.κ = μ - laneBits)
    (hR : P₀.R = R) (hμ : laneBits ≤ μ) (claims : List StackClaim) (cs : List (ℕ × ℕ × Word))
    (hpre : StackedPre μ R P₀ claims cs) :
    (univ.filter fun ρ : E ↦ ∃ q ∈ Candidates μ R P₀.thr (wordOf cs 0),
        StackClaim.Holds μ (fun point ↦ dot (powers ρ claims.length)
          (claims.map fun c ↦ c.1 point), dot (powers ρ claims.length) (claims.map (·.2))) q).card ≤
      P₀.listMax * (claims.length - 1) := by
  obtain ⟨-, hviol⟩ := hpre
  rcases P₀ with ⟨κ, R', η, h64, hκ1, hR1, hη, hagr⟩
  simp only at hκ hR
  subst hκ hR
  set P₀ : LevelCode := ⟨μ - laneBits, R', η, h64, hκ1, hR1, hη, hagr⟩
  set L := iList (ReedSolomon.code (domain (μ - laneBits) R' h64) (2 ^ (μ - laneBits))) P₀.thr
    (laneWord μ R' (wordOf cs 0))
  -- The discrepancy of a candidate.
  let d : Column μ → Fin claims.length → E := fun q k ↦
    (∑ j : Fin (2 ^ μ), claims[k].1 (boolPoint μ j) * ofK (q.values.getD j 0)) - claims[k].2
  have hhold : ∀ ρ q, StackClaim.Holds μ (fun point ↦ dot (powers ρ claims.length)
      (claims.map fun c ↦ c.1 point), dot (powers ρ claims.length) (claims.map (·.2))) q ↔
      ∑ k : Fin claims.length, d q k * ρ ^ (k : ℕ) = 0 := by
    intro ρ q
    simp only [StackClaim.Holds, dot_powers_map]
    exact batch_iff (fun k j ↦ claims[k].1 (boolPoint μ j)) (fun j ↦ ofK (q.values.getD j 0))
      (fun k ↦ claims[k].2) ρ
  refine (Finset.card_le_card fun ρ hρ ↦ ?_).trans ((card_filter_exists_le L (fun
      (V : Fin (2 ^ laneBits) → Fin (2 ^ (μ - laneBits + R')) → E) (ρ : E) ↦
      ∃ q ∈ Candidates μ R' P₀.thr (wordOf cs 0), encStack μ R' q = V ∧
        ∑ k : Fin claims.length, d q k * ρ ^ (k : ℕ) = 0) (N := claims.length - 1)
      fun V _ ↦ ?_).trans ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
    obtain ⟨q, hq, hh⟩ := hρ
    exact ⟨encStack μ R' q, mem_iList_of_candidate h64 hq, q, hq, rfl, (hhold ρ q).mp hh⟩
  · by_cases hex : ∃ q ∈ Candidates μ R' P₀.thr (wordOf cs 0), encStack μ R' q = V
    · obtain ⟨q₀, hq₀, rfl⟩ := hex
      obtain ⟨c, hc, hnot⟩ := hviol q₀ hq₀
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
      have hd : ∃ k, d q₀ k ≠ 0 := ⟨⟨k, hk⟩, by
        simp only [d, sub_ne_zero]
        exact hnot⟩
      refine (Finset.card_le_card fun ρ hρ ↦ ?_).trans (card_powerBatch_eq_zero_le (d q₀) hd)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
      obtain ⟨q, -, hqV, hz⟩ := hρ
      rwa [encStack_injective hμ h64 hqV] at hz
    · refine le_trans (Finset.card_le_card (t := ∅) fun ρ hρ ↦ ?_) (by simp)
      rw [Finset.mem_filter] at hρ
      obtain ⟨q, hq, hqV, -⟩ := hρ.2
      exact absurd ⟨q, hq, hqV⟩ hex
  · exact Nat.mul_le_mul_right _ (P₀.card_iList_le _)

/-- `verifyStackedOpening`: the batching challenge, then the opening. -/
theorem verifyStackedOpening_eq (stackLog R : ℕ) (claims : List StackClaim) :
    verifyStackedOpening stackLog R claims = Prog.sampleE.bind fun ρ ↦
      verifyWhir stackLog R (dot (powers ρ claims.length) (claims.map (·.2)))
        (fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point)) := rfl

open Classical in
/-- **The specification of the stacked opening.** From `StackedPre` (every candidate violates one
of the `J` claims), the batching challenge escapes with probability at most
`eBatch J P₀ = (J − 1)·L₀/|E|` and the opening (`whirSpec`) follows. -/
noncomputable def stackedSpec {R : ℕ} {level : Whir.Level} {rest : List Whir.Level}
    (claims : List StackClaim) (hcl : ∀ c ∈ claims, IsMultiaffine μ c.1)
    (hc : deriveConfig μ R = some (level :: rest)) (hℓ : level.fold = laneBits)
    (hμ : laneBits ≤ μ) (hκ₀ : (codes 0).κ = μ - laneBits) (hR₀ : (codes 0).R = R)
    (hA : LadderArith μ codes 0 0 (level :: rest))
    (hε : whirEps codes (level :: rest) ≤ εmax) (T : ENNReal) :
    Spec (verifyStackedOpening μ R claims)
      (fun h ↦ StackedPre μ R (codes 0) claims (commits h)) (fun _ _ ↦ False) εmax
      (eBatch claims.length (codes 0)) T :=
  by
  have S0 : Spec Prog.sampleE (fun h ↦ StackedPre μ R (codes 0) claims (commits h))
      (fun ρ h ↦ WhirPre μ R (codes 0)
        (fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point))
        (dot (powers ρ claims.length) (claims.map (·.2))) (commits h)) εmax
      (eBatch claims.length (codes 0) + 0) 0 :=
    Spec.sampleE (eBatch claims.length (codes 0)) fun h₀ hp ↦ by
      have hb := card_batch_bad_le (codes 0) hκ₀ hR₀ hμ claims _ hp
      rw [eBatch, ENNReal.div_eq_inv_mul]
      refine mul_le_mul' le_rfl (Nat.cast_le.mpr ((Finset.card_le_card fun ρ hρ ↦ ?_).trans
        (hb.trans (le_of_eq (mul_comm _ _)))))
      rw [Finset.mem_filter] at hρ ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have hρ2 := hρ.2
      simp only [commits_sample] at hρ2
      by_contra hno
      exact hρ2 ⟨hp.1, fun q hq hh ↦ hno ⟨q, hq, hh⟩⟩
  have F0 := fun ρ : E ↦
    whirSpec (w := fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point))
      (t := dot (powers ρ claims.length) (claims.map (·.2))) hc hℓ hμ hκ₀ hR₀
      (isMultiaffine_batched claims hcl ρ) hA hε 0
  have S1 := Spec.bind S0 F0
  exact anyT (Spec.congr (p' := verifyStackedOpening μ R claims)
    (verifyStackedOpening_eq μ R claims).symm
    (S1.mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl)) T

end
end LeanVM.Protocol.Whir.Sound
