/-
  LeanVM.Protocol.EndToEnd.Front.BusGkr

  The verifier program's grand-product walk (`verify_gkr_grand_products`) specified on the oracle
  protocol's relations: each layer step from doom on the layer relation to doom on the step's
  output relation, through the combiner, the rounds, the descendants and the combination
  challenges.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.BusSpec
public import LeanVM.Protocol.EndToEnd.Front.BusGkrArk
public import LeanVM.Protocol.EndToEnd.Front.LayoutArith
public import LeanVM.Protocol.Verifier

/-!
# The grand-product walk on doom

The verifier program's `gkrStep step s` (`verifier.py:441-452` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) is one layer step of the oracle protocol's
`layerStep` (`LeanVM.Protocol.ToArkLib.GrandProduct`) at radix `2 ^ step`: both draw the
combiner first. Its state `s` (`GkrState`: three values, the point) is the protocol's layer
statement (`layerStmtOf`), and its doom is stated on the protocol's relations:

* before: doom on the layer relation (`layerRel`);
* after the combiner: doom on stage `0` of the layer's tracked family (`familyT`), the combiner
  charged `L₀ · 2 / |E|` (`lambda_escape`);
* through the rounds (`wireSumcheckSpec`, equality mode against the point);
* after the descendants and their check: doom on `childRelT … 0` (the descendants' security);
* through the combination challenges: doom on `childRelT … i`, each challenge charged
  `L₀ / |E|` (`card_interpNext_le'`);
* after the step: doom on the step's output relation `stepOutT`
  (`interpDone_mem_stepOutT_iff'`), which is the next layer's relation inside the walk and the
  argument's output relation after the last step (`layersPre_of_stepPost`).

The wire's state and the protocol's statement agree because the program computes what the
protocol's verdicts compute: `polyEval` of the values at the combiner is `powerBatch`
(`polyEval_eq_powerBatch`), the products of the descendants are the check's
(`prodE_eq_prod`), and `multilinear_eval` of each tree's descendants at the combination challenges
is the interpolated value (`multilinearEval_eq_evalMle`).
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open CompPoly CMlPolynomialEval OracleComp OracleSpec
open scoped NNReal ENNReal

@[expose] public section

/-! ## The wire's arithmetic is the protocol's -/

/-- Three values as the protocol's family of three. -/
def valuesFn (vals : List E) : Fin 3 → E := fun t ↦ vals.getD t 0

/-- Horner on the three values at the combiner is the protocol's batch by powers. -/
theorem polyEval_eq_powerBatch (vals : List E) (hlen : vals.length = 3) (l : E) :
    polyEval vals l = powerBatch (valuesFn vals) l := by
  rw [polyEval_eq_sum_range, hlen, powerBatch, ← Fin.sum_univ_eq_sum_range]
  rfl

/-- The product `reduce(mul, values)` is the list's product. -/
theorem prodE_eq_prod (l : List E) : prodE l = l.prod := by
  unfold prodE
  rw [List.prod_eq_foldl]

/-- The product of a list of `n` values is the product over its vector. -/
theorem prod_eq_prod_vecOf {n : ℕ} (l : List E) (hlen : l.length = n) :
    l.prod = ∏ c : Fin n, (vecOf n l)[c] := by
  subst hlen
  simp only [vecOf, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [← List.prod_ofFn]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-- The vector of a list of the right length lists back to it. -/
theorem toList_vecOf {n : ℕ} (l : List E) (hlen : l.length = n) : (vecOf n l).toList = l := by
  subst hlen
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [vecOf]

/-! ## The wire's state as the protocol's statement -/

section State

variable {X : Type} (data : X)

/-- The protocol's layer statement of the wire's GKR state: the public data, the point, the three
values. -/
def layerStmtOf (m : ℕ) (s : GkrState) : Gkr.LayerStmt X E 3 m :=
  (data, (vecOf m s.point, valuesFn s.values))

/-- The descendants' message of the wire's three lists. -/
def childrenOf (ρ : ℕ) (children : List (List E)) : Fin 3 → CMlPolynomialEval E ρ :=
  fun t ↦ vecOf (2 ^ ρ) (children.getD t [])

/-- The point of `m + ρ` coordinates the wire's `y ++ x` gives is the protocol's `(u, χ)`. -/
theorem vecOf_append {ρ m : ℕ} (y x : List E) (hy : y.length = ρ) :
    vecOf (m + ρ) (y ++ x) = Vector.cast (Nat.add_comm ρ m) (vecOf ρ y ++ vecOf m x) := by
  apply Vector.ext
  intro k hk
  simp only [vecOf, Vector.getElem_ofFn, Vector.getElem_cast, Vector.getElem_append]
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show k < y.length by omega)]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show y.length ≤ k by omega), hy]

/-- **The wire's step output is the protocol's interpolated statement**: the point `y ++ x`, and
each tree's `multilinear_eval` of its descendants at `y`. -/
theorem interpDone_eq {ρ m : ℕ} (x y : List E) (children : List (List E))
    (hy : y.length = ρ) (hc : children.length = 3)
    (hch : ∀ t ∈ children, t.length = 2 ^ ρ) :
    Gkr.interpDone 3 ρ m (((data, (vecOf m x, childrenOf ρ children)), vecOf ρ y)) =
      layerStmtOf data (m + ρ) ⟨children.map (multilinearEval · y), y ++ x⟩ := by
  refine Prod.ext rfl (Prod.ext (vecOf_append y x hy).symm (funext fun t ↦ ?_))
  show evalMle (childrenOf ρ children t) (vecOf ρ y) =
    (children.map (multilinearEval · y)).getD t 0
  have ht : (t : ℕ) < children.length := by rw [hc]; exact t.isLt
  rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_map, childrenOf,
    List.getD_eq_getElem _ _ ht, ← multilinearEval_eq_evalMle,
    toList_vecOf _ (hch _ (List.getElem_mem ht)), toList_vecOf _ hy]

end State

/-! ## The combination challenges -/

section Interp

variable {I : M3Instance} {X : Type} {μ : ℕ}
  (leaves : X → (∀ i, TheOracle I i) → Fin 3 → CMlPolynomialEval E μ)
  (riders : X → (∀ i, TheOracle I i) → List (Σ τ : Fin (μ + 1), CMlPolynomialEval E τ))
  (cands : Word → Set (∀ i, TheOracle I i)) {ρ m : ℕ} (T : Gkr.RiderTrack μ riders ρ m)

/-- The error of a challenge restoring a relation at one value at most, over at most `L₀`
candidates: `L₀ / |E|`. -/
noncomputable def unitError (L₀ : ℕ) : ℝ≥0∞ := L₀ * (Fintype.card E : ℝ≥0∞)⁻¹

/-- The lead of `n` combination challenges before a follower of lead `T`. -/
noncomputable def interpLead (L₀ : ℕ) : ℕ → ℝ≥0∞ → ℝ≥0∞
  | 0, T => T
  | n + 1, T => unitError L₀ + interpLead L₀ n T

theorem interpLead_eq (L₀ n : ℕ) (T : ℝ≥0∞) : interpLead L₀ n T = n * unitError L₀ + T := by
  induction n with
  | zero => simp [interpLead]
  | succ n ih => rw [interpLead, ih]; push_cast; ring

open Classical in
/-- A combination challenge escapes doom on `childRelT` with probability at most `L₀ / |E|`. -/
theorem interp_escape_le {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) {i : ℕ} (s : Gkr.InterpStmt X E 3 m ρ i) (h₀ : List Ev)
    (hpre : HDoom cands (Gkr.childRelT 3 μ leaves riders ρ m T i) s h₀) :
    (Fintype.card E : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun c ↦ ¬ HDoom cands
        (Gkr.childRelT 3 μ leaves riders ρ m T (i + 1)) (s.1, s.2.push c)
        (h₀ ++ [Ev.sample c])).card : ℝ≥0∞) ≤ unitError L₀ := by
  obtain ⟨W, hW, hR⟩ := hpre
  have hsub : (Finset.univ.filter fun c ↦ ¬ HDoom cands
        (Gkr.childRelT 3 μ leaves riders ρ m T (i + 1)) (s.1, s.2.push c)
        (h₀ ++ [Ev.sample c])) ⊆ Finset.univ.filter fun c ↦ ∃ o ∈ cands W,
          ((Gkr.interpNext 3 ρ m s c, o), ()) ∈ Gkr.childRelT 3 μ leaves riders ρ m T (i + 1) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    by_contra hno
    exact hc ⟨W, firstWord_append hW _, fun o ho hin ↦ hno ⟨o, ho, hin⟩⟩
  refine le_trans (by gcongr) (card_exists_le (e := (Fintype.card E : ℝ≥0∞)⁻¹) (hfin W)
    (hcard W) _ fun o ho ↦ ?_)
  have h1 := Gkr.card_interpNext_le' 3 μ leaves riders ρ m T s o (hR o ho)
  rw [natCard_subtype_eq_card_filter] at h1
  calc (Fintype.card E : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun c ↦
        ((Gkr.interpNext 3 ρ m s c, o), ()) ∈ Gkr.childRelT 3 μ leaves riders ρ m T (i + 1)).card :
          ℝ≥0∞)
      ≤ (Fintype.card E : ℝ≥0∞)⁻¹ * 1 := by
        gcongr
        exact_mod_cast (le_of_eq (by congr)).trans h1
    _ = (Fintype.card E : ℝ≥0∞)⁻¹ := mul_one _

variable {εmax T' : ℝ≥0∞}

/-- **The combination challenges** (`sample_n(step)` after the descendants): from doom on
`childRelT … i` at the challenges `pre` so far, to doom on `childRelT … (i + n)`, each challenge
charged `L₀ / |E|`. -/
noncomputable def interpSpec {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀)
    (base : X × (Vector E m × (Fin 3 → CMlPolynomialEval E ρ))) :
    (n i : ℕ) → (pre : Vector E i) →
      Spec (Prog.sampleN n) (HDoom cands (Gkr.childRelT 3 μ leaves riders ρ m T i) (base, pre))
        (fun ys h ↦ ys.length = n ∧ HDoom cands (Gkr.childRelT 3 μ leaves riders ρ m T (i + n))
          (base, vecOf (i + n) (pre.toList ++ ys)) h) εmax (interpLead L₀ n T') T'
  | 0, i, pre => (Spec.ret (Post := fun ys h ↦ ys.length = 0 ∧ HDoom cands
      (Gkr.childRelT 3 μ leaves riders ρ m T (i + 0)) (base, vecOf (i + 0) (pre.toList ++ ys)) h)
      []).mono (fun h hp ↦ ⟨rfl, by simpa [vecOf_toList] using hp⟩) (fun _ _ h ↦ h) le_rfl le_rfl
      le_rfl
  | n + 1, i, pre =>
    (Spec.sampleE (unitError L₀) (Post := fun c h ↦ HDoom cands
      (Gkr.childRelT 3 μ leaves riders ρ m T (i + 1)) (base, pre.push c) h)
      fun h₀ hp ↦ interp_escape_le leaves riders cands T hfin hcard (base, pre) h₀ hp).bind'
      fun c ↦ (interpSpec hfin hcard base n (i + 1) (pre.push c)).bind' fun ys ↦
        (Spec.ret (Post := fun ys h ↦ ys.length = n + 1 ∧ HDoom cands
          (Gkr.childRelT 3 μ leaves riders ρ m T (i + (n + 1)))
          (base, vecOf (i + (n + 1)) (pre.toList ++ ys)) h) (c :: ys)).mono
          (fun h hp ↦ ⟨by simp [hp.1], by
            have h2 := hp.2
            rw [show i + 1 + n = i + (n + 1) by omega, Vector.toList_push,
              List.append_assoc] at h2
            exact h2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Interp

/-! ## A layer step -/

section Step

variable {I : M3Instance} {X : Type} {μ : ℕ}
  (leaves : X → (∀ i, TheOracle I i) → Fin 3 → CMlPolynomialEval E μ)
  (riders : X → (∀ i, TheOracle I i) → List (Σ τ : Fin (μ + 1), CMlPolynomialEval E τ))
  (cands : Word → Set (∀ i, TheOracle I i)) (data : X) {ρ m : ℕ}
  (T : Gkr.RiderTrack μ riders ρ m)

/-- The doom before a step: doom on the layer relation at the wire's state. -/
def StepPre (s : GkrState) (h : List Ev) : Prop :=
  s.point.length = m ∧ s.values.length = 3 ∧
    HDoom cands (Gkr.layerRel 3 μ leaves riders m) (layerStmtOf data m s) h

/-- The doom after a step: doom on the step's output relation at the wire's new state. -/
def StepPost (s : GkrState) (h : List Ev) : Prop :=
  s.point.length = m + ρ ∧ s.values.length = 3 ∧
    HDoom cands (Gkr.stepOutT 3 μ leaves riders ρ m T) (layerStmtOf data (m + ρ) s) h

/-- The layer's family has the wire's equality-mode domains. -/
theorem weights_eq_wireDomain (s : GkrState) (hs : s.point.length = m) (l : E) (k : ℕ)
    (hk : k < (s.point.map some).length) :
    Gkr.weights (F := E) (X := X) 3 m (layerStmtOf data m s, l) (0 + k) =
      wireDomain (s.point.map some)[k] := by
  have hk' : k < m := by simpa [hs] using hk
  simp only [Gkr.weights, SumcheckRound.normalizedWeights, zero_add, hk', ↓reduceDIte,
    wireDomain, List.getElem_map, layerStmtOf, vecOf, Vector.getElem_ofFn]
  simp [List.getD_eq_getElem?_getD, show k < s.point.length by omega]

/-- **The descendants keep doom**: values that pass the check carry doom on the sumcheck's last
stage to doom on `childRelT … 0`. -/
theorem children_keep {C : Set (∀ i, TheOracle I i)}
    {st : SumcheckRound.Stmt (Gkr.LayerX X E 3 m) E m}
    (hpre : RelDoom C (SumcheckRound.rel (Gkr.familyT 3 μ leaves riders ρ m T) m) st)
    (ch : Fin 3 → CMlPolynomialEval E ρ) (hc : Gkr.combineCheck 3 ρ m st ch = true) :
    RelDoom C (Gkr.childRelT 3 μ leaves riders ρ m T 0) (Gkr.childNext 3 ρ m st ch) :=
  say_keep (Gkr.childrenSecurity 3 μ leaves riders ρ m T) hpre ch hc

/-- The wire's check of the descendants is the protocol's. -/
theorem combineCheck_eq (st : SumcheckRound.Stmt (Gkr.LayerX X E 3 m) E m)
    (children : List (List E)) (hc : children.length = 3)
    (hch : ∀ t ∈ children, t.length = 2 ^ ρ)
    (heq : st.2.2 = polyEval (children.map prodE) st.1.2) :
    Gkr.combineCheck 3 ρ m st (childrenOf ρ children) = true := by
  rw [Gkr.combineCheck, decide_eq_true_eq, heq,
    polyEval_eq_powerBatch _ (by simp [hc])]
  congr 1
  funext t
  have ht : (t : ℕ) < children.length := by rw [hc]; exact t.isLt
  show (children.map prodE).getD t 0 = ∏ c : Fin (2 ^ ρ), (vecOf (2 ^ ρ) (children.getD t []))[c]
  rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_map, prodE_eq_prod,
    List.getD_eq_getElem _ _ ht, prod_eq_prod_vecOf _ (hch _ (List.getElem_mem ht))]

/-- The error of a combiner over at most `L₀` candidates: `L₀ · 2 / |E|` (three trees). -/
noncomputable def lambdaError (L₀ : ℕ) : ℝ≥0∞ :=
  L₀ * ((((3 - 1 : ℕ) : ℝ≥0) / (Nat.card E : ℝ≥0) : ℝ≥0) : ℝ≥0∞)

/-- The doom after the combiner that starts a step at radix `2 ^ ρ'` from layer `m'`. -/
def LambdaDoom {ρ' m' : ℕ} (T' : Gkr.RiderTrack μ riders ρ' m') (W : Word)
    (ls : Gkr.LayerStmt X E 3 m') (c : E) : Prop :=
  RelDoom (cands W) (SumcheckRound.rel (Gkr.familyT 3 μ leaves riders ρ' m' T') 0)
    (Gkr.lambdaNext 3 m' ls c)

open Classical in
/-- **A combiner escapes** doom on the layer relation with probability at most `L₀ · 2 / |E|`. -/
theorem lambda_escape {ρ' m' : ℕ} (T' : Gkr.RiderTrack μ riders ρ' m') (hm : m' + ρ' ≤ μ)
    {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀) (W : Word)
    (ls : Gkr.LayerStmt X E 3 m')
    (hR : RelDoom (cands W) (Gkr.layerRel 3 μ leaves riders m') ls) :
    (Fintype.card E : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun c ↦
      ¬ LambdaDoom leaves riders cands T' W ls c).card : ℝ≥0∞) ≤ lambdaError L₀ :=
  draw_escape_le (Gkr.lambdaSecurity 3 μ leaves riders ρ' m' id T' hm
      (relS := Gkr.layerRel 3 μ leaves riders m') fun _ _ ↦ Iff.rfl) (hfin W) (hcard W) hR rfl

variable {εmax T' : ℝ≥0∞}

/-- A specification from a precondition that cannot hold. -/
def specOfFalse {α : Type} {p : Prog α} {Pre : List Ev → Prop} {Post : α → List Ev → Prop}
    {L T : ℝ≥0∞} (h : ∀ h, Pre h → False) : Spec p Pre Post εmax L T :=
  (Spec.dead (p := p) (Post := Post) (εmax := εmax) (L := L) (T := T)).mono (fun h' hp ↦ h h' hp)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

open Classical in
/-- **A layer step** of the wire's GKR walk at radix `2 ^ ρ` from layer `m`: from doom on the
layer relation to doom on the step's output relation. The combiner, drawn first, is charged
`L₀ · 2 / |E|` (`lambda_escape`), each sumcheck round's challenge `L₀ · 2^ρ / |E|`, each
combination challenge `L₀ / |E|`. -/
noncomputable def stepSpec {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hm : m + ρ ≤ μ)
    (he : roundError L₀ (2 ^ ρ) + 0 ≤ εmax) (hT : interpLead L₀ ρ T' ≤ εmax)
    (s : GkrState) :
    Spec (gkrStep ρ s) (StepPre (m := m) leaves riders cands data s)
      (StepPost leaves riders cands data T) εmax (lambdaError L₀ + 0) T' :=
  if hs : s.point.length = m ∧ s.values.length = 3 then
    (Spec.sampleE (lambdaError L₀) (Post := fun c h ↦ HDoom cands
        (SumcheckRound.rel (Gkr.familyT 3 μ leaves riders ρ m T) 0)
        (Gkr.lambdaNext 3 m (layerStmtOf data m s) c) h)
      (fun h₀ hp ↦ by
        obtain ⟨-, -, W, hW, hR⟩ := hp
        refine le_trans ?_ (lambda_escape leaves riders cands T hm hfin hcard W _ hR)
        gcongr with c _
        intro hD
        exact ⟨W, firstWord_append hW _, hD⟩)).bind' fun combiner ↦
    ((wireSumcheckSpec (T := 0) (Gkr.familyT 3 μ leaves riders ρ m T) cands
      (Gkr.familyT_consistent' 3 μ leaves riders ρ m T) (Gkr.familyT_sound' 3 μ leaves riders ρ m T)
      hfin hcard Nat.one_le_two_pow he (layerStmtOf data m s, combiner) (s.point.map some) 0
      #v[] (polyEval s.values combiner) (by simp [hs.1])
      (weights_eq_wireDomain data s hs.1 _)).mono
      (fun h hp ↦ by rw [polyEval_eq_powerBatch _ hs.2]; exact hp) (fun _ _ h ↦ h) le_rfl
      (sumcheckLead_le _ _) le_rfl).bind' fun ⟨x, claim⟩ ↦
    let P0 := SumcheckPost (Gkr.familyT 3 μ leaves riders ρ m T) cands
      (layerStmtOf data m s, combiner) m #v[] (x, claim)
    have hP0 : ∀ h z, P0 h → P0 (h ++ [Ev.read z]) := fun _ _ hp ↦ ⟨hp.1, hp.2.append _⟩
    have hread : Prog.readN (2 ^ ρ - 1 + 1) = Prog.readN (2 ^ ρ) := by
      rw [Nat.sub_add_cancel Nat.one_le_two_pow]
    (Spec.congr hread (readNSuccSpec P0 hP0 zero_le (2 ^ ρ - 1))).bind' fun child0 ↦
    let P1 := fun h ↦ child0.length = 2 ^ ρ - 1 + 1 ∧ P0 h
    (Spec.congr hread (readNSuccSpec P1 (fun _ _ hp ↦ ⟨hp.1, hP0 _ _ hp.2⟩) zero_le
      (2 ^ ρ - 1))).bind' fun child1 ↦
    let P2 := fun h ↦ child1.length = 2 ^ ρ - 1 + 1 ∧ P1 h
    (Spec.congr hread (readNSuccSpec P2 (fun _ _ hp ↦ ⟨hp.1, hp.2.1, hP0 _ _ hp.2.2⟩) hT
      (2 ^ ρ - 1))).bind' fun child2 ↦
    if hq : x.length = m ∧ child0.length = 2 ^ ρ ∧ child1.length = 2 ^ ρ ∧
        child2.length = 2 ^ ρ then
      let base : X × (Vector E m × (Fin 3 → CMlPolynomialEval E ρ)) :=
        (data, (vecOf m x, childrenOf ρ [child0, child1, child2]))
      have hch : ∀ t ∈ [child0, child1, child2], t.length = 2 ^ ρ := by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl
        exacts [hq.2.1, hq.2.2.1, hq.2.2.2]
      (Spec.require (Post := fun _ h ↦
          HDoom cands (Gkr.childRelT 3 μ leaves riders ρ m T 0) (base, #v[]) h)
        (fun _ hp hc ↦ by
          obtain ⟨-, -, -, -, W, hW, hR⟩ := hp
          exact ⟨W, hW, children_keep leaves riders T hR _ (combineCheck_eq _ _ rfl hch hc)⟩)).bind'
        fun _ ↦
      (interpSpec leaves riders cands T (T' := T') hfin hcard base ρ 0 #v[]).bind' fun y ↦
      if hy : y.length = ρ then
        (Spec.ret (Post := StepPost leaves riders cands data T)
          ⟨[child0, child1, child2].map (multilinearEval · y), y ++ x⟩).mono
          (fun _ hp ↦ by
            obtain ⟨-, W, hW, hR⟩ := hp
            have hR' : RelDoom (cands W) (Gkr.childRelT 3 μ leaves riders ρ m T ρ)
                (base, vecOf ρ y) := by
              have key : ∀ k, k = ρ → RelDoom (cands W) (Gkr.childRelT 3 μ leaves riders ρ m T k)
                  (base, vecOf k y) →
                  RelDoom (cands W) (Gkr.childRelT 3 μ leaves riders ρ m T ρ)
                    (base, vecOf ρ y) := by
                rintro k rfl h
                exact h
              exact key (0 + ρ) (Nat.zero_add ρ) hR
            have hR'' : RelDoom (cands W) (Gkr.stepOutT 3 μ leaves riders ρ m T)
                (Gkr.interpDone 3 ρ m (base, vecOf ρ y)) := fun o ho hin ↦
              hR' o ho ((Gkr.interpDone_mem_stepOutT_iff' 3 μ leaves riders ρ m T _ o).mp hin)
            rw [interpDone_eq data x y [child0, child1, child2] hy rfl hch] at hR''
            exact ⟨by simp [hy, hq.1]; omega, by simp, W, hW, hR''⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else specOfFalse fun _ hp ↦ hy hp.1
    else specOfFalse fun _ hp ↦ hq ⟨by have := hp.2.2.2.1; simpa using this,
      by have := Nat.one_le_two_pow (n := ρ); have := hp.2.2.1; omega,
      by have := Nat.one_le_two_pow (n := ρ); have := hp.2.1; omega,
      by have := Nat.one_le_two_pow (n := ρ); have := hp.1; omega⟩
  else specOfFalse fun _ hp ↦ hs ⟨hp.1, hp.2.1⟩

end Step

/-! ## The walk -/

section Walk

variable {I : M3Instance} {X : Type} {μ : ℕ}
  (leaves : X → (∀ i, TheOracle I i) → Fin 3 → CMlPolynomialEval E μ)
  (riders : X → (∀ i, TheOracle I i) → List (Σ τ : Fin (μ + 1), CMlPolynomialEval E τ))
  (cands : Word → Set (∀ i, TheOracle I i)) (data : X)

/-- The radix exponent of the next step with `n` layers left: `1` when `n` is odd, `2`
otherwise (`verifier.py:440`, the protocol's odd first step and radix-four steps). -/
def ρOf (n : ℕ) : ℕ := if n % 2 = 1 then 1 else 2

theorem ρOf_le {n : ℕ} (hn : n ≠ 0) : ρOf n ≤ n := by
  unfold ρOf; split_ifs <;> omega

theorem one_le_ρOf (n : ℕ) : 1 ≤ ρOf n := by
  unfold ρOf; split_ifs <;> omega

theorem ρOf_le_two (n : ℕ) : ρOf n ≤ 2 := by
  unfold ρOf; split_ifs <;> omega

/-- The rider tracker of the next step: progressive at the last step, constant before. -/
def trackOf (n m : ℕ) (h : m + n = μ) : Gkr.RiderTrack μ riders (ρOf n) m :=
  if hl : n = ρOf n then Gkr.progTrack μ riders (ρOf n) m (by omega)
  else Gkr.constTrack μ riders (ρOf n) m

/-- **The walk's doom** with `n` layers left at layer `m`: on the argument's output relation
when none is left; on the layer relation otherwise, where the next step starts. -/
def LayersPre (n m : ℕ) (_h : m + n = μ) (s : GkrState) (hist : List Ev) : Prop :=
  if n = 0 then
    s.point.length = μ ∧ s.values.length = 3 ∧
      HDoom cands (Gkr.relOut 3 μ leaves riders) (layerStmtOf data μ s) hist
  else StepPre (m := m) leaves riders cands data s hist

/-- The lead of the walk with `n` layers left: the next step's combiner, if there is one. -/
noncomputable def nextError (L₀ n : ℕ) : ℝ≥0∞ := if n = 0 then 0 else lambdaError L₀

theorem nextError_le (L₀ n : ℕ) : nextError L₀ n ≤ lambdaError L₀ := by
  unfold nextError; split_ifs <;> simp

/-- The doom after a step is the walk's doom with the layers it leaves: the argument's output
relation after the last step, the next layer's relation before. -/
theorem layersPre_of_stepPost (n m : ℕ) (h : m + n = μ) (hn : n ≠ 0) (s : GkrState)
    (hist : List Ev)
    (hp : StepPost leaves riders cands data (trackOf riders n m h) s hist) :
    LayersPre leaves riders cands data (n - ρOf n) (m + ρOf n)
      (by have := ρOf_le hn; omega) s hist := by
  obtain ⟨hl, hv, W, hW, hR⟩ := hp
  unfold LayersPre
  split_ifs with h0
  · have hlast : n = ρOf n := by have := ρOf_le hn; omega
    have hm : m + ρOf n = μ := by omega
    unfold trackOf at hR
    rw [dite_eq_left hlast] at hR
    refine ⟨by omega, hv, W, hW, fun o ho hin ↦ hR o ho ?_⟩
    have hvec : Vector.cast hm (vecOf (m + ρOf n) s.point) = vecOf μ s.point := by
      apply Vector.ext
      intro k hk
      simp [vecOf]
    refine (Gkr.stepOutT_progTrack_iff 3 μ leaves riders (ρOf n) m hm _ o).mpr ?_
    simpa only [layerStmtOf, hvec] using hin
  · have hlast : ¬ n = ρOf n := by omega
    unfold trackOf at hR
    rw [dite_eq_right hlast] at hR
    exact ⟨hl, hv, W, hW, fun o ho hin ↦ hR o ho
      ((Gkr.stepOutT_constTrack_iff 3 μ leaves riders (ρOf n) m _ o).mpr hin)⟩

theorem interpLead_mono (L₀ : ℕ) {ρ : ℕ} (hρ : ρ ≤ 2) {x y : ℝ≥0∞} (hxy : x ≤ y) :
    interpLead L₀ ρ x ≤ interpLead L₀ 2 y := by
  rw [interpLead_eq, interpLead_eq]
  gcongr

theorem roundError_mono (L₀ : ℕ) {a b : ℕ} (hab : a ≤ b) : roundError L₀ a ≤ roundError L₀ b := by
  unfold roundError
  gcongr

variable {εmax : ℝ≥0∞}

open Classical in
/-- **The walk's next step** with `n ≠ 0` layers left: radix `2 ^ ρOf n`, from the walk's doom to
the walk's doom with `n - ρOf n` layers left. -/
noncomputable def walkStepSpec {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (he : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (n m : ℕ) (h : m + n = μ) (hn : n ≠ 0)
    (s : GkrState) :
    Spec (gkrStep (ρOf n) s) (LayersPre leaves riders cands data n m h s)
      (fun s' ↦ LayersPre leaves riders cands data (n - ρOf n) (m + ρOf n)
        (by have := ρOf_le hn; omega) s') εmax (lambdaError L₀ + 0)
      (nextError L₀ (n - ρOf n)) :=
  (stepSpec leaves riders cands data (trackOf riders n m h) (T' := nextError L₀ (n - ρOf n)) hfin
    hcard (by have := ρOf_le hn; omega)
    (le_trans (by simpa using roundError_mono L₀ (Nat.pow_le_pow_right (by norm_num)
      (ρOf_le_two n))) he)
    (le_trans (interpLead_mono L₀ (ρOf_le_two n) (nextError_le L₀ _)) hT)
    s).mono
    (fun hist hp ↦ by unfold LayersPre at hp; simpa [hn] using hp)
    (fun s' hist hp ↦ layersPre_of_stepPost leaves riders cands data n m h hn s' hist hp)
    le_rfl le_rfl le_rfl

/-- The walk's doom depends on the layer counts, not on how they are written. -/
theorem layersPre_congr {n n' m m' : ℕ} (hn : n = n') (hm : m = m') {h : m + n = μ}
    {h' : m' + n' = μ} {s : GkrState} {hist : List Ev}
    (hp : LayersPre leaves riders cands data n m h s hist) :
    LayersPre leaves riders cands data n' m' h' s hist := by
  subst hn hm
  exact hp

/-- **The wire's GKR walk** (`gkrLayers`, the `while layer > 0` loop of
`verify_gkr_grand_products`, `verifier.py:438-452`) with `n` layers left at layer `m`: from the
walk's doom to doom on the argument's output relation. Its lead is the first step's combiner. -/
noncomputable def gkrLayersSpec {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (he : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) :
    (n m : ℕ) → (h : m + n = μ) → (s : GkrState) →
      Spec (gkrLayers n s) (LayersPre leaves riders cands data n m h s)
        (fun s' ↦ LayersPre leaves riders cands data 0 μ (by simp) s') εmax (nextError L₀ n) 0
  | 0, m, h, s =>
    (Spec.ret (Post := fun s' ↦ LayersPre leaves riders cands data 0 μ (by simp) s') s).mono
      (fun _ hp ↦ by unfold LayersPre at hp ⊢; simpa using hp) (fun _ _ h ↦ h) le_rfl
      (by simp [nextError]) le_rfl
  | 1, m, h, s =>
    ((walkStepSpec leaves riders cands data hfin hcard he hT 1 m h one_ne_zero s).bind' fun s' ↦
      (gkrLayersSpec hfin hcard he hT 0 (m + 1) (by omega) s').mono
        (fun _ hp ↦ layersPre_congr leaves riders cands data (by simp [ρOf]) (by simp [ρOf]) hp)
        (fun _ _ h ↦ h) le_rfl (by simp [nextError, ρOf]) le_rfl).mono
      (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp [nextError]) le_rfl
  | n + 2, m, h, s =>
    Spec.ite
      (fun hodd ↦
        have hρ : ρOf (n + 2) = 1 := by simp [ρOf, hodd]
        Spec.congr (by rw [hρ])
          (((walkStepSpec leaves riders cands data hfin hcard he hT (n + 2) m h (by omega)
            s).bind' fun s' ↦ (gkrLayersSpec hfin hcard he hT (n + 1) (m + 1) (by omega) s').mono
              (fun _ hp ↦ layersPre_congr leaves riders cands data (by rw [hρ]; omega) (by rw [hρ])
                hp)
              (fun _ _ h ↦ h) le_rfl (le_of_eq (by rw [hρ]; rfl)) le_rfl).mono
            (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp [nextError]) le_rfl))
      (fun heven ↦
        have hρ : ρOf (n + 2) = 2 := by
          have : n % 2 = 0 := by omega
          simp [ρOf, this]
        Spec.congr (by rw [hρ])
          (((walkStepSpec leaves riders cands data hfin hcard he hT (n + 2) m h (by omega)
            s).bind' fun s' ↦ (gkrLayersSpec hfin hcard he hT n (m + 2) (by omega) s').mono
              (fun _ hp ↦ layersPre_congr leaves riders cands data (by rw [hρ]; omega) (by rw [hρ])
                hp)
              (fun _ _ h ↦ h) le_rfl (le_of_eq (by rw [hρ]; rfl)) le_rfl).mono
            (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp [nextError]) le_rfl))

end Walk

end
end LeanVM.Protocol.EndToEnd.Front
