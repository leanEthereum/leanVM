/-
  LeanVM.Protocol.Whir.Sound.Spec

  The round-by-round soundness of the deployed WHIR opening as a specification of the verifier
  program: `whirSpec` for `verifyWhir` from "every candidate violates the claim", and
  `stackedSpec` for `verifyStackedOpening` from "every candidate violates one of the pooled
  claims", each group of challenges escaping within `εmax` after its grind.
-/

module

public import LeanVM.Protocol.Whir.Sound.Start
public import LeanVM.Protocol.Verifier.WhirTarget

/-!
# The specification of the WHIR opening

For the ladder of levels `config = derive_config(μ, R)` (`LeanVM.Parameters.Whir.ladder`) and a
code per level (`codes i`: message variables `κ_i` after its folds, rate, folds, last threshold):

* `LadderOK μ codes εmax i levels`: the levels match the codes, and each level's groups escape
  within `εmax` after their grinds (`MidOK`, `FinalOK`); with `RoundBounds` for the fold rounds.
* `levelsSpec`: the levels from `LevelPre` of the first, never returning in doom.
* `whirSpec`: **`verifyWhir μ R t w` from `WhirPre`**: the level-0 commitment is the history's
  only one, of level 0's shape, and every candidate of its word at level 0's threshold violates
  `(w, t)`, for `w` multiaffine.
* `stackedSpec`: **`verifyStackedOpening μ R claims` from `StackedPre`** (every candidate
  violates one of the claims), with the batching challenge's escape
  `eBatch J L₀ = (J − 1)·L₀/|E|` as lead, `L₀` a bound on the candidates.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset

@[expose] public section

/-! ## The ladder -/

/-- **The ladder's hypotheses** from level `i`. -/
def LadderOK (codes : ℕ → LevelCode) (εmax : ENNReal) : ℕ → List Whir.Level → Prop
  | _, [] => True
  | i, [level] => level.fold = (codes i).ℓ ∧ level.logInvRate = (codes i).R ∧
      FinalOK (codes i) level.queries εmax
  | i, level :: next :: rest => level.fold = (codes i).ℓ ∧ level.logInvRate = (codes i).R ∧
      MidOK (codes i) (codes (i + 1)) level.queries εmax ∧ LadderOK codes εmax (i + 1) (next :: rest)

theorem LadderOK.head {codes : ℕ → LevelCode} {εmax : ENNReal} {i : ℕ} {level : Whir.Level}
    {rest : List Whir.Level} (h : LadderOK codes εmax i (level :: rest)) :
    level.fold = (codes i).ℓ ∧ level.logInvRate = (codes i).R := by
  cases rest with
  | nil => exact ⟨h.1, h.2.1⟩
  | cons next rest => exact ⟨h.1, h.2.1⟩

variable {μ ℓ₀ : ℕ} {w : List E → E} {codes : ℕ → LevelCode} {εmax : ENNReal}

/-- **The levels' specification.** -/
noncomputable def levelsSpec (hw : IsMultiaffine μ w) (hℓ₀ : ℓ₀ ≤ μ)
    (B : ∀ j, RoundBounds (codes j) εmax) :
    (levels : List Whir.Level) → (i pre : ℕ) → LadderOK codes εmax i levels → (s : WhirState) →
      Spec (whirLevels μ ℓ₀ w i levels s)
        (fun h ↦ LevelPre μ ℓ₀ w i (codes i) pre s (commits h)) (fun _ _ ↦ False) εmax 0 0
  | [], i, pre, _, s => (Spec.fail (Pre := fun h ↦ LevelPre μ ℓ₀ w i (codes i) pre s (commits h))
      (Post := fun _ _ ↦ False)).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | [level], i, pre, hA, s =>
    (Spec.congr (whirLevels_final μ ℓ₀ w i level s).symm
      ((foldRoundsSpec μ ℓ₀ w i (codes i) pre
          (fun cs ↦ ShapeOK i (codes i) cs ∧ cs.length = i + 1) hw hℓ₀ (B i) level.fold s []
          (by simp [hA.1])).bind' fun r ↦
        (finalTailSpec μ ℓ₀ w i (codes i) pre level hw hℓ₀ ⟨hA.1, hA.2.1⟩ hA.2.2 r.1 r.2).mono
          (fun _ hp ↦ ⟨⟨by simpa using hp.1.1, hp.1.2⟩, by rw [hp.2, hA.1]⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)).mono
      (fun _ hp ↦ ⟨hp.1, hp.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | level :: next :: rest, i, pre, hA, s =>
    (Spec.congr (whirLevels_mid μ ℓ₀ w i level next rest s).symm
      ((foldRoundsSpec μ ℓ₀ w i (codes i) pre
          (fun cs ↦ ShapeOK i (codes i) cs ∧ cs.length = i + 1) hw hℓ₀ (B i) level.fold s []
          (by simp [hA.1])).bind' fun r ↦
        (midTailSpec μ ℓ₀ w i (codes i) (codes (i + 1)) pre μ ℓ₀ w level next rest rfl
          ⟨hA.1, hA.2.1⟩ hA.2.2.2.head hA.2.2.1
          (fun s' ↦ levelsSpec hw hℓ₀ B (next :: rest) (i + 1) (pre + (codes i).ℓ) hA.2.2.2 s')
          r.1 r.2).mono
          (fun _ hp ↦ ⟨⟨by simpa using hp.1.1, hp.1.2⟩, by rw [hp.2, hA.1]⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)).mono
      (fun _ hp ↦ ⟨hp.1, hp.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-! ## The opening -/

/-- `verifyWhir` on an admissible shape: the levels from the initial state. -/
theorem verifyWhir_eq {R : ℕ} {t : E} {level : Whir.Level} {rest : List Whir.Level}
    (hc : Whir.ladder μ R = some (level :: rest)) :
    verifyWhir μ R t w = whirLevels μ level.fold w 0 (level :: rest) ⟨t, [], []⟩ := by
  rw [verifyWhir, hc]
  rfl

/-- WHIR's starting relation: the level-0 commitment is the history's only one, of level 0's
shape, and every candidate of its word violates `(w, t)`. -/
def WhirPre (μ R : ℕ) (P₀ : LevelCode) (w : List E → E) (t : E) (cs : List (ℕ × ℕ × Word)) :
    Prop :=
  ShapeOK 0 P₀ cs ∧ cs.length = 1 ∧
    ∀ q ∈ Candidates μ R (P₀.thr 0) (wordOf cs 0), ¬ StackClaim.Holds μ (w, t) q

/-- **The specification of the WHIR opening.** From `WhirPre`, every group of challenges escapes
within `εmax` after its grind, and the opening never returns in doom. -/
noncomputable def whirSpec {R : ℕ} {t : E} {level : Whir.Level} {rest : List Whir.Level}
    (hc : Whir.ladder μ R = some (level :: rest)) (hℓ : level.fold = laneBits)
    (hμ : laneBits ≤ μ) (hκ₀ : (codes 0).κ = μ - laneBits) (hR₀ : (codes 0).R = R)
    (hthr : 2 ^ (codes 0).κ ≤ (codes 0).thr 0) (hw : IsMultiaffine μ w)
    (B : ∀ j, RoundBounds (codes j) εmax) (hA : LadderOK codes εmax 0 (level :: rest))
    (T : ENNReal) :
    Spec (verifyWhir μ R t w) (fun h ↦ WhirPre μ R (codes 0) w t (commits h))
      (fun _ _ ↦ False) εmax 0 T :=
  anyT (Spec.congr (by rw [verifyWhir_eq hc, hℓ])
    ((levelsSpec (ℓ₀ := laneBits) hw hμ B (level :: rest) 0 0 hA ⟨t, [], []⟩).mono
      (fun h hp ↦ levelPre_zero (codes 0) hκ₀ hR₀ (by rw [← hA.head.1, hℓ]) hμ hthr w t
        (commits h) hp.1 hp.2.1 hp.2.2)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)) T

/-! ## The stacked opening -/

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



/-- The batching challenge's escape: `(J − 1)·L₀ / |E|`. -/
noncomputable def eBatch (J L₀ : ℕ) : ENNReal := (((J - 1) * L₀ : ℕ) : ENNReal) / Fintype.card E

/-- The level-0 commitment is the history's only one: `2^(μ−6+R)` leaves of `2^6` words. -/
def ShapeOK₀ (μ R : ℕ) (cs : List (ℕ × ℕ × Word)) : Prop :=
  cs.length = 1 ∧ ∃ W, cs[0]? = some (μ - laneBits + R, 2 ^ laneBits, W) ∧
    WellShaped (2 ^ laneBits) W

/-- The opening's pooled relation: the level-0 commitment has the right shape and every candidate
at the threshold `A₀` violates at least one of the claims. -/
def StackedPre (μ R A₀ : ℕ) (claims : List StackClaim) (cs : List (ℕ × ℕ × Word)) : Prop :=
  ShapeOK₀ μ R cs ∧
    ∀ q ∈ Candidates μ R A₀ (wordOf cs 0), ∃ c ∈ claims, ¬ StackClaim.Holds μ c q

/-- `ShapeOK₀` is level 0's shape. -/
theorem shapeOK_of_shapeOK₀ {μ R : ℕ} {P₀ : LevelCode} (hκ₀ : P₀.κ = μ - laneBits)
    (hR₀ : P₀.R = R) (hℓ : P₀.ℓ = laneBits) {cs : List (ℕ × ℕ × Word)} (h : ShapeOK₀ μ R cs) :
    ShapeOK 0 P₀ cs := by
  obtain ⟨-, W, hW, hWs⟩ := h
  refine ⟨W, by rw [hW, hκ₀, hR₀, wdOf, hℓ]; rfl, fun v ↦ ?_⟩
  rw [hWs v, wdOf, hℓ]
  rfl

/-- The batched weight of multiaffine claims is multiaffine. -/
theorem isMultiaffine_batched {μ : ℕ} (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine μ c.1) (ρ : E) :
    IsMultiaffine μ fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point) := by
  simp only [dot_powers_map]
  exact IsMultiaffine.sum _ _ fun k _ ↦ (hcl _ (List.getElem_mem _)).const_mul _

open Classical in
/-- **The batching step**: at most `(J − 1)·|C|` challenges `ρ` let a stack of a finite set `C`
satisfy the batched claim when every member of `C` violates one of the claims. -/
theorem card_batch_bad_le {μ : ℕ} (claims : List StackClaim) (C : Set (Column μ)) (hC : C.Finite)
    (hviol : ∀ q ∈ C, ∃ c ∈ claims, ¬ StackClaim.Holds μ c q) :
    (univ.filter fun ρ : E ↦ ∃ q ∈ C, StackClaim.Holds μ (fun point ↦ dot (powers ρ claims.length)
        (claims.map fun c ↦ c.1 point), dot (powers ρ claims.length) (claims.map (·.2))) q).card ≤
      C.ncard * (claims.length - 1) := by
  let d : Column μ → Fin claims.length → E := fun q k ↦
    (∑ j : Fin (2 ^ μ), claims[k].1 (boolPoint μ j) * ofK (q.values.getD j 0)) - claims[k].2
  have hhold : ∀ ρ q, StackClaim.Holds μ (fun point ↦ dot (powers ρ claims.length)
      (claims.map fun c ↦ c.1 point), dot (powers ρ claims.length) (claims.map (·.2))) q ↔
      ∑ k : Fin claims.length, d q k * ρ ^ (k : ℕ) = 0 := by
    intro ρ q
    simp only [StackClaim.Holds, dot_powers_map]
    exact batch_iff (fun k j ↦ claims[k].1 (boolPoint μ j)) (fun j ↦ ofK (q.values.getD j 0))
      (fun k ↦ claims[k].2) ρ
  refine (card_le_card fun ρ hρ ↦ ?_).trans ((card_filter_exists_le hC.toFinset
    (fun q ρ ↦ ∑ k : Fin claims.length, d q k * ρ ^ (k : ℕ) = 0) (N := claims.length - 1)
    fun q hq ↦ ?_).trans (by rw [Set.ncard_eq_toFinset_card C hC]))
  · simp only [mem_filter, mem_univ, true_and, Set.Finite.mem_toFinset] at hρ ⊢
    obtain ⟨q, hq, hh⟩ := hρ
    exact ⟨q, hq, (hhold ρ q).mp hh⟩
  · obtain ⟨c, hc, hnot⟩ := hviol q ((Set.Finite.mem_toFinset hC).mp hq)
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    exact card_powerBatch_eq_zero_le (d q) ⟨⟨k, hk⟩, by simp only [d, sub_ne_zero]; exact hnot⟩

open Classical in
/-- **The specification of the stacked opening.** From `StackedPre` (every candidate at level 0's
threshold violates one of the `J ≤ 512` claims), the batching challenge escapes with probability
at most `eBatch J L₀ = (J − 1)·L₀/|E|`, `L₀` a bound on the candidates, and the opening
(`whirSpec`) follows. -/
noncomputable def stackedSpec {R : ℕ} {level : Whir.Level} {rest : List Whir.Level}
    (claims : List StackClaim) (hcl : ∀ c ∈ claims, IsMultiaffine μ c.1)
    (hc : Whir.ladder μ R = some (level :: rest)) (hℓ : level.fold = laneBits)
    (hμ : laneBits ≤ μ) (hκ₀ : (codes 0).κ = μ - laneBits) (hR₀ : (codes 0).R = R)
    (hthr : 2 ^ (codes 0).κ ≤ (codes 0).thr 0) (B : ∀ j, RoundBounds (codes j) εmax)
    (hA : LadderOK codes εmax 0 (level :: rest)) (L₀ : ℕ)
    (hfin : ∀ W, (Candidates μ R ((codes 0).thr 0) W).Finite)
    (hL₀ : ∀ W, (Candidates μ R ((codes 0).thr 0) W).ncard ≤ L₀) (T : ENNReal) :
    Spec (verifyStackedOpening μ R claims)
      (fun h ↦ StackedPre μ R ((codes 0).thr 0) claims (commits h)) (fun _ _ ↦ False) εmax
      (eBatch claims.length L₀) T :=
  by
  have hℓ₀ : (codes 0).ℓ = laneBits := by rw [← hA.head.1, hℓ]
  let Pre := fun h ↦ StackedPre μ R ((codes 0).thr 0) claims (commits h)
  let wρ := fun ρ : E ↦ fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point)
  let tρ := fun ρ : E ↦ dot (powers ρ claims.length) (claims.map (·.2))
  have S0 : Spec VerifierProgram.sampleChallenge Pre (fun ρ h ↦ WhirPre μ R (codes 0) (wρ ρ) (tρ ρ) (commits h))
      εmax (eBatch claims.length L₀ + 0) 0 :=
    Spec.sampleE (eBatch claims.length L₀) fun h₀ hp ↦ by
      rw [eBatch, ENNReal.div_eq_inv_mul]
      refine mul_le_mul' le_rfl (Nat.cast_le.mpr ((card_le_card fun ρ hρ ↦ ?_).trans
        ((card_batch_bad_le claims _ (hfin _) hp.2).trans ?_)))
      · simp only [mem_filter, mem_univ, true_and, commits_sample] at hρ ⊢
        by_contra hno
        exact hρ ⟨shapeOK_of_shapeOK₀ hκ₀ hR₀ hℓ₀ hp.1, hp.1.1,
          fun q hq hh ↦ hno ⟨q, hq, hh⟩⟩
      · rw [mul_comm]
        exact Nat.mul_le_mul_left _ (hL₀ _)
  have F0 : ∀ ρ, Spec (verifyWhir μ R (tρ ρ) (wρ ρ))
      (fun h ↦ WhirPre μ R (codes 0) (wρ ρ) (tρ ρ) (commits h)) (fun _ _ ↦ False) εmax 0 0 :=
    fun ρ ↦ whirSpec (codes := codes) hc hℓ hμ hκ₀ hR₀ hthr (isMultiaffine_batched claims hcl ρ)
      B hA 0
  have S1 := Spec.bind S0 F0
  have S2 : Spec (VerifierProgram.require (claims.length ≤ maxStackedClaims)) Pre (fun _ ↦ Pre)
      εmax (eBatch claims.length L₀ + 0) (eBatch claims.length L₀ + 0) :=
    Spec.require fun _ hp _ ↦ hp
  have S3 := Spec.bind S2 fun _ ↦ S1
  exact anyT (Spec.congr (verifyStackedOpening_eq μ R claims).symm
    (S3.mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl)) T

end
end LeanVM.Protocol.Whir.Sound
