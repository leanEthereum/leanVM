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
public import LeanVM.Protocol.Verifier.Phases

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

/-! ## The ghost levels -/

/-- **A WHIR trace**: each level's fold rounds and high part, then the last level's rounds and the
final polynomial's coefficients. It is what the agreement-set extractor descends through. -/
inductive WhirTrace where
  | final (rounds : List FoldRound) (folded : List E)
  | mid (rounds : List FoldRound) (high : List E) (rest : WhirTrace)

/-- **The levels, returning their trace**: `whirLevels` with the same events. -/
def whirLevelsG (logN laneFolds : ℕ) (eb : List E → E) :
    ℕ → List Whir.Level → WhirState → VerifierProgram WhirTrace
  | _, [], _ => VerifierProgram.fail
  | index, [level], s => foldRounds level.fold s >>= fun r ↦
      finalTailG logN laneFolds eb index level r.1 r.2 >>= fun folded ↦
        VerifierProgram.ret (.final r.2 folded)
  | index, level :: next :: rest, s => foldRounds level.fold s >>= fun r ↦
      midTailC logN index level next (fun high s' ↦
        whirLevelsG logN laneFolds eb (index + 1) (next :: rest) s' >>= fun tr ↦
          VerifierProgram.ret (.mid r.2 high tr)) r.1 r.2

theorem bind_unit_ret (p : VerifierProgram Unit) : p >>= (fun _ ↦ VerifierProgram.ret ()) = p := by
  rw [VerifierProgram.bind_eq]
  conv_rhs => rw [← VerifierProgram.bind_ret p]

theorem midTailC_bind {α β : Type} (logN index : ℕ) (level next : Whir.Level)
    (k : List E → WhirState → VerifierProgram α) (g : α → VerifierProgram β) (s : WhirState)
    (rounds : List FoldRound) :
    (midTailC logN index level next k s rounds).bind g =
      midTailC logN index level next (fun high s' ↦ (k high s').bind g) s rounds := by
  simp only [midTailC, VerifierProgram.bind_eq, VerifierProgram.bind_assoc]

/-- The ghost levels, their trace dropped, are the levels. -/
theorem whirLevelsG_unit (logN laneFolds : ℕ) (eb : List E → E) :
    ∀ (index : ℕ) (levels : List Whir.Level) (s : WhirState),
      (whirLevelsG logN laneFolds eb index levels s).bind (fun _ ↦ VerifierProgram.ret ()) =
        whirLevels logN laneFolds eb index levels s
  | index, [], s => by simp [whirLevelsG, whirLevels, VerifierProgram.bind]
  | index, [level], s => by
    rw [whirLevels_final]
    simp only [whirLevelsG, VerifierProgram.bind_eq, VerifierProgram.bind_assoc,
      VerifierProgram.ret_bind]
    refine congrArg (VerifierProgram.bind (foldRounds level.fold s)) (funext fun r ↦ ?_)
    rw [← finalTailG_unit, VerifierProgram.bind_eq]
  | index, level :: next :: rest, s => by
    rw [whirLevels_mid]
    simp only [whirLevelsG, VerifierProgram.bind_eq, VerifierProgram.bind_assoc]
    refine congrArg (VerifierProgram.bind (foldRounds level.fold s)) (funext fun r ↦ ?_)
    rw [midTailC_bind, midTail]
    refine congrArg (fun k ↦ midTailC logN index level next k r.1 r.2) (funext fun high ↦
      funext fun s' ↦ ?_)
    simp only [VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
    exact whirLevelsG_unit logN laneFolds eb (index + 1) (next :: rest) s'

/-- **A trace is good** from level `i` with predicate `B`: through each level's rounds and high
part, the final polynomial's descent is good (`FinGood`). -/
def traceGood (codes : ℕ → LevelCode) :
    ℕ → (List (ℕ × ℕ × Word) → TPred) → WhirTrace → List (ℕ × ℕ × Word) → Prop
  | i, B, .final rounds folded, cs => FinGood i (codes i) B rounds folded cs
  | i, B, .mid rounds high rest, cs => ∃ h : (codes i).κ = (codes (i + 1)).ℓ + (codes (i + 1)).κ,
      rounds.length = (codes i).ℓ ∧
        traceGood codes (i + 1) (nextPred i (codes i) (codes (i + 1)) h B rounds high) rest cs

/-- **The levels' specification**: from level `i`'s doom with a stable predicate `B`, every
group escapes within `εmax` after its grind, and an accepting return has a good trace. -/
noncomputable def levelsSpec (hw : IsMultiaffine μ w) (hℓ₀ : ℓ₀ ≤ μ)
    (RB : ∀ j, RoundBounds (codes j) εmax) :
    (levels : List Whir.Level) → (i pre : ℕ) → LadderOK codes εmax i levels →
      (B : List (ℕ × ℕ × Word) → TPred) → PredStable i B → (s : WhirState) →
      Spec (whirLevelsG μ ℓ₀ w i levels s)
        (fun h ↦ LevelPre μ ℓ₀ w i (codes i) pre B s (commits h))
        (fun tr h ↦ traceGood codes i B tr (commits h)) εmax 0 0
  | [], i, pre, _, B, _, s =>
    (Spec.fail (Pre := fun h ↦ LevelPre μ ℓ₀ w i (codes i) pre B s (commits h))
      (Post := fun tr h ↦ traceGood codes i B tr (commits h))).mono (fun _ h ↦ h) (fun _ _ h ↦ h)
      le_rfl le_rfl le_rfl
  | [level], i, pre, hA, B, hB, s =>
    ((foldRoundsSpec μ ℓ₀ w i (codes i) pre B
        (fun cs ↦ ShapeOK i (codes i) cs ∧ cs.length = i + 1) hw hℓ₀ (RB i) level.fold s []
        (by simp [hA.1])).bind' fun r ↦
      ((finalTailSpec μ ℓ₀ w i (codes i) pre B level hw hℓ₀ ⟨hA.1, hA.2.1⟩ hA.2.2 hB r.1 r.2).mono
        (fun _ hp ↦ ⟨⟨by simpa using hp.1.1, hp.1.2⟩, by rw [hp.2, hA.1]⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun folded ↦
      Spec.ret (Post := fun tr h ↦ traceGood codes i B tr (commits h)) (.final r.2 folded)).mono
      (fun _ hp ↦ ⟨hp.1, hp.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | level :: next :: rest, i, pre, hA, B, hB, s =>
    ((foldRoundsSpec μ ℓ₀ w i (codes i) pre B
        (fun cs ↦ ShapeOK i (codes i) cs ∧ cs.length = i + 1) hw hℓ₀ (RB i) level.fold s []
        (by simp [hA.1])).bind' fun r ↦
      if hr : r.2.length = (codes i).ℓ then
      (midTailSpec μ ℓ₀ w i (codes i) (codes (i + 1)) pre B μ level next rfl
        ⟨hA.1, hA.2.1⟩ hA.2.2.2.head hA.2.2.1 hB r.1 r.2 _
        (fun high s' ↦
          (levelsSpec hw hℓ₀ RB (next :: rest) (i + 1) (pre + (codes i).ℓ) hA.2.2.2
            (nextPred i (codes i) (codes (i + 1)) hA.2.2.1.hκ B r.2 high)
            (predStable_nextPred hB r.2 high) s').bind' fun tr ↦
          (Spec.ret (Post := fun tr h ↦ traceGood codes i B tr (commits h))
            (.mid r.2 high tr)).mono (fun _ h ↦ ⟨hA.2.2.1.hκ, hr, h⟩) (fun _ _ h ↦ h) le_rfl
            le_rfl le_rfl)).mono
        (fun _ hp ↦ ⟨⟨by simpa using hp.1.1, hp.1.2⟩, hr⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ hp ↦ hr (by rw [hp.2, hA.1])) (fun _ _ h ↦ h) le_rfl zero_le
        le_rfl).mono
      (fun _ hp ↦ ⟨hp.1, hp.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-! ## The opening -/

/-- `verifyWhir` on an admissible shape: the levels from the initial state. -/
theorem verifyWhir_eq {R : ℕ} {t : E} {level : Whir.Level} {rest : List Whir.Level}
    (hc : Whir.ladder μ R = some (level :: rest)) :
    verifyWhir μ R t w = whirLevels μ level.fold w 0 (level :: rest) ⟨t, [], []⟩ := by
  rw [verifyWhir, hc]
  rfl

/-- `verifyWhir`, returning its trace. -/
def verifyWhirG (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E) :
    VerifierProgram WhirTrace :=
  liftOption (Whir.ladder logN logInvRate) >>= fun config ↦
    whirLevelsG logN ((config.head?.map (·.fold)).getD 0) evaluateBasis 0 config ⟨target, [], []⟩

theorem verifyWhirG_eq {R : ℕ} {t : E} {level : Whir.Level} {rest : List Whir.Level}
    (hc : Whir.ladder μ R = some (level :: rest)) :
    verifyWhirG μ R t w = whirLevelsG μ level.fold w 0 (level :: rest) ⟨t, [], []⟩ := by
  rw [verifyWhirG, hc]
  rfl

/-- The ghost opening, its trace dropped, is the opening. -/
theorem verifyWhirG_unit (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E) :
    (verifyWhirG logN logInvRate target evaluateBasis).bind (fun _ ↦ VerifierProgram.ret ()) =
      verifyWhir logN logInvRate target evaluateBasis := by
  unfold verifyWhirG verifyWhir
  rcases Whir.ladder logN logInvRate with _ | config
  · rfl
  · simp only [Verifier.liftOption, VerifierProgram.bind_eq, VerifierProgram.ret_bind]
    exact whirLevelsG_unit _ _ _ _ _ _

/-- WHIR's starting relation, relativised to the bad stacks `Bad`: the level-0 commitment is the
history's only one, of level 0's shape, and every bad candidate of its word violates `(w, t)`. -/
def WhirPre (μ R : ℕ) (P₀ : LevelCode) (w : List E → E) (t : E) (Bad : Column μ → Prop)
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  ShapeOK 0 P₀ cs ∧ cs.length = 1 ∧
    ∀ q ∈ Candidates μ R (P₀.thr 0) (wordOf cs 0), Bad q → ¬ StackClaim.Holds μ (w, t) q

/-- **The specification of the WHIR opening.** From `WhirPre`, every group of challenges escapes
within `εmax` after its grind, and an accepting return has a good trace from level 0's
predicate. -/
noncomputable def whirSpec {R : ℕ} {t : E} {level : Whir.Level} {rest : List Whir.Level}
    (hc : Whir.ladder μ R = some (level :: rest)) (hℓ : level.fold = laneBits)
    (hμ : laneBits ≤ μ) (hκ₀ : (codes 0).κ = μ - laneBits) (hR₀ : (codes 0).R = R)
    (hthr : (codes 0).deg < (codes 0).thr 0) (hw : IsMultiaffine μ w)
    (RB : ∀ j, RoundBounds (codes j) εmax) (hA : LadderOK codes εmax 0 (level :: rest))
    (Bad : Column μ → Prop) :
    Spec (verifyWhirG μ R t w) (fun h ↦ WhirPre μ R (codes 0) w t Bad (commits h))
      (fun tr h ↦ traceGood codes 0 (lvl0Pred μ Bad) tr (commits h)) εmax 0 0 :=
  Spec.congr (by rw [verifyWhirG_eq hc, hℓ])
    ((levelsSpec (ℓ₀ := laneBits) hw hμ RB (level :: rest) 0 0 hA (lvl0Pred μ Bad)
      (predStable_lvl0Pred μ Bad) ⟨t, [], []⟩).mono
      (fun h hp ↦ levelPre_zero (codes 0) hκ₀ hR₀ (by rw [← hA.head.1, hℓ]) hμ hthr w t Bad
        (commits h) hp.1 hp.2.1 hp.2.2)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)

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

/-- The opening's pooled relation, relativised to the bad stacks `Bad`: the level-0 commitment has
the right shape and every bad candidate at the threshold `A₀` violates at least one of the
claims. -/
def StackedPre (μ R A₀ : ℕ) (claims : List StackClaim) (Bad : Column μ → Prop)
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  ShapeOK₀ μ R cs ∧
    ∀ q ∈ Candidates μ R A₀ (wordOf cs 0), Bad q → ∃ c ∈ claims, ¬ StackClaim.Holds μ c q

/-- `verifyStackedOpening`, returning the opening's trace, in the normal form
`verifyStackedOpening_nf`. -/
def verifyStackedOpeningG (stackLog logInvRate : ℕ) (claims : List StackClaim) :
    VerifierProgram WhirTrace :=
  (VerifierProgram.require (StackedOk claims)).bind fun _ ↦ VerifierProgram.sampleChallenge.bind fun c ↦
    verifyWhirG stackLog logInvRate (dot (powers c claims.length) (claims.map (·.2)))
      fun point ↦ dot (powers c claims.length) (claims.map fun cl ↦ cl.1 point)

/-- The ghost stacked opening, its trace dropped, is the stacked opening. -/
theorem verifyStackedOpeningG_unit (stackLog logInvRate : ℕ) (claims : List StackClaim) :
    (verifyStackedOpeningG stackLog logInvRate claims).bind (fun _ ↦ VerifierProgram.ret ()) =
      verifyStackedOpening stackLog logInvRate claims := by
  rw [verifyStackedOpening_nf, verifyStackedOpeningG]
  simp only [VerifierProgram.bind_assoc]
  refine congrArg (VerifierProgram.bind _) (funext fun _ ↦
    congrArg (VerifierProgram.bind _) (funext fun c ↦ ?_))
  exact verifyWhirG_unit _ _ _ _

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
    (hthr : (codes 0).deg < (codes 0).thr 0) (RB : ∀ j, RoundBounds (codes j) εmax)
    (hA : LadderOK codes εmax 0 (level :: rest)) (L₀ : ℕ)
    (hfin : ∀ W, (Candidates μ R ((codes 0).thr 0) W).Finite)
    (hL₀ : ∀ W, (Candidates μ R ((codes 0).thr 0) W).ncard ≤ L₀) (Bad : Column μ → Prop) :
    Spec (verifyStackedOpeningG μ R claims)
      (fun h ↦ StackedPre μ R ((codes 0).thr 0) claims Bad (commits h))
      (fun tr h ↦ traceGood codes 0 (lvl0Pred μ Bad) tr (commits h)) εmax
      (eBatch claims.length L₀) 0 :=
  by
  have hℓ₀ : (codes 0).ℓ = laneBits := by rw [← hA.head.1, hℓ]
  let Pre := fun h ↦ StackedPre μ R ((codes 0).thr 0) claims Bad (commits h)
  let wρ := fun ρ : E ↦ fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point)
  let tρ := fun ρ : E ↦ dot (powers ρ claims.length) (claims.map (·.2))
  have S0 : Spec VerifierProgram.sampleChallenge Pre
      (fun ρ h ↦ WhirPre μ R (codes 0) (wρ ρ) (tρ ρ) Bad (commits h))
      εmax (eBatch claims.length L₀ + 0) 0 :=
    Spec.sampleE (eBatch claims.length L₀) fun h₀ hp ↦ by
      have hfinB : {q ∈ Candidates μ R ((codes 0).thr 0) (wordOf (commits h₀) 0) | Bad q}.Finite :=
        (hfin _).subset fun q hq ↦ hq.1
      rw [eBatch, ENNReal.div_eq_inv_mul]
      refine mul_le_mul' le_rfl (Nat.cast_le.mpr ((card_le_card fun ρ hρ ↦ ?_).trans
        ((card_batch_bad_le claims _ hfinB fun q hq ↦ hp.2 q hq.1 hq.2).trans ?_)))
      · simp only [mem_filter, mem_univ, true_and, commits_sample] at hρ ⊢
        by_contra hno
        exact hρ ⟨shapeOK_of_shapeOK₀ hκ₀ hR₀ hℓ₀ hp.1, hp.1.1,
          fun q hq hb hh ↦ hno ⟨q, ⟨hq, hb⟩, hh⟩⟩
      · rw [mul_comm]
        exact Nat.mul_le_mul_left _
          ((Set.ncard_le_ncard (fun q hq ↦ hq.1) (hfin _)).trans (hL₀ _))
  have F0 : ∀ ρ, Spec (verifyWhirG μ R (tρ ρ) (wρ ρ))
      (fun h ↦ WhirPre μ R (codes 0) (wρ ρ) (tρ ρ) Bad (commits h))
      (fun tr h ↦ traceGood codes 0 (lvl0Pred μ Bad) tr (commits h)) εmax 0 0 :=
    fun ρ ↦ whirSpec (codes := codes) hc hℓ hμ hκ₀ hR₀ hthr (isMultiaffine_batched claims hcl ρ)
      RB hA Bad
  have S1 := Spec.bind S0 F0
  have S2 : Spec (VerifierProgram.require (StackedOk claims)) Pre (fun _ ↦ Pre)
      εmax (eBatch claims.length L₀ + 0) (eBatch claims.length L₀ + 0) :=
    Spec.require fun _ hp _ ↦ hp
  have S3 := Spec.bind S2 fun _ ↦ S1
  exact S3.mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl

end
end LeanVM.Protocol.Whir.Sound
