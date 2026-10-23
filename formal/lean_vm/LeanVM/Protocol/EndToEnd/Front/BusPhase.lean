/-
  LeanVM.Protocol.EndToEnd.Front.BusPhase

  The verifier program's bus phase (`verify_bus_balance`) specified on the oracle protocol's
  relations: the fingerprint challenges, the roots, the grand-product walk and the boundary
  values, from the commitment's doom to doom on the bus seam.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.BusGkr
public import LeanVM.Protocol.BusSecurity

/-!
# The bus phase on doom

`verifyBusBalance layout` (`verifier.py:534-593`) is the oracle protocol's `busPhase`
(`LeanVM.Protocol.Bus`) on the wire. This module specifies its parts on the protocol's
relations, in the calculus of verifier programs:

* `alwaysSpec`: a sub-program from a fact that already decides its postcondition (the count root
  `0`, which the later `require` rejects);
* `gkrSpec`: `verify_gkr_grand_products` (`verifier.py:432-455`), from doom on the relation after
  the fingerprint challenges (`Bus.afterChallenge`) to "the count root is `0`, or doom on the
  argument's output relation": the roots' message is the protocol's (`Bus.rootsSecurity`), the
  roots are the layer-`0` statement (`Gkr.relIn_iff_layerRel_zero`), and the walk, each step
  drawing its own combiner, is `gkrLayersSpec`.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open CompPoly CMlPolynomialEval OracleComp OracleSpec
open scoped NNReal ENNReal

@[expose] public section

/-! ## A decided postcondition -/

variable {εmax : ℝ≥0∞}

/-- **A sub-program whose postcondition is already decided**: if every return satisfies `Post`
(whatever the history), doom holds throughout and no challenge escapes it. The lead is the
follower's, capped at `1`. -/
noncomputable def alwaysSpec {α : Type} {p : Prog α} {Pre : List Ev → Prop}
    {Post : α → List Ev → Prop} {T : ℝ≥0∞} (hpost : ∀ a h, Post a h) (hT : min 1 T ≤ εmax) :
    Spec p Pre Post εmax (min 1 T) T where
  D _ _ := True
  V _ _ := min 1 T
  le_one _ _ := min_le_left _ _
  start_D _ _ := trivial
  start_V _ _ := le_rfl
  read := by intros; trivial
  grind := by intros; trivial
  commit := by intros; trivial
  sample := by
    intros
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
  query := by intros; exact le_rfl
  moveEnd := by intro _ _ _ _ _ _ hD; exact absurd trivial hD
  retEnd := by intro _ _ _ _ _ hD; exact absurd trivial hD
  retDoom := by intros; exact le_rfl
  post := by intros; exact hpost _ _
  bound := by
    intros
    exact le_trans (mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le (by norm_num))) hT

/-- `alwaysSpec` before a follower of lead `0`. -/
noncomputable def alwaysSpec0 {α : Type} {p : Prog α} {Pre : List Ev → Prop}
    {Post : α → List Ev → Prop} (hpost : ∀ a h, Post a h) : Spec p Pre Post εmax 0 0 :=
  (alwaysSpec (T := 0) hpost (by simp)).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl

/-! ## Several challenges in a row -/

/-- A sum over the tuples of `n + 1` challenges is a sum over the first and the rest. -/
theorem sum_fin_succ_fun (n : ℕ) (F : (Fin (n + 1) → E) → ℝ≥0∞) :
    ∑ w, F w = ∑ x : E, ∑ v : Fin n → E, F (Fin.cons x v) := by
  rw [← (Fin.consEquiv fun _ ↦ E).sum_comp, Fintype.sum_prod_type]
  rfl

/-- **`n` challenges in a row**, then a sub-program: the expectation of a function of the return
is at most the average, over the tuples of challenges, of a bound on the sub-program's. -/
theorem retExp_sampleN_bind_le {β : Type} (g : β → List Ev → ℝ≥0∞) (h₀ : List Ev) :
    ∀ (n : ℕ) (k : List E → Prog β) (B : List E → ℝ≥0∞),
      (∀ xs l, Prog.retExp g h₀ l (k xs) ≤ B xs) → ∀ l,
      Prog.retExp g h₀ l ((Prog.sampleN n).bind k) ≤
        ((Fintype.card E : ℝ≥0∞) ^ n)⁻¹ * ∑ v : Fin n → E, B (List.ofFn v)
  | 0, k, B, hk, l => by
    simpa [Prog.sampleN] using hk [] l
  | n + 1, k, B, hk, l => by
    show (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ x : E, Prog.retExp g h₀ (l ++ [Ev.sample x])
        (((Prog.sampleN n).bind fun xs ↦ Prog.ret (x :: xs)).bind k) ≤ _
    have ih : ∀ x : E, Prog.retExp g h₀ (l ++ [Ev.sample x])
        (((Prog.sampleN n).bind fun xs ↦ Prog.ret (x :: xs)).bind k) ≤
        ((Fintype.card E : ℝ≥0∞) ^ n)⁻¹ * ∑ v : Fin n → E, B (x :: List.ofFn v) := fun x ↦ by
      rw [Prog.bind_assoc]
      exact retExp_sampleN_bind_le g h₀ n (fun xs ↦ k (x :: xs)) (fun xs ↦ B (x :: xs))
        (fun xs l ↦ hk _ l) _
    calc (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ x : E, Prog.retExp g h₀ (l ++ [Ev.sample x])
          (((Prog.sampleN n).bind fun xs ↦ Prog.ret (x :: xs)).bind k)
        ≤ (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ x : E,
          ((Fintype.card E : ℝ≥0∞) ^ n)⁻¹ * ∑ v : Fin n → E, B (x :: List.ofFn v) := by
          gcongr with x
          exact ih x
      _ = ((Fintype.card E : ℝ≥0∞) ^ (n + 1))⁻¹ * ∑ v : Fin (n + 1) → E, B (List.ofFn v) := by
          rw [sum_fin_succ_fun, ← Finset.mul_sum, ← mul_assoc, pow_succ, ENNReal.mul_inv
            (by simp) (by simp), mul_comm ((Fintype.card E : ℝ≥0∞)⁻¹)]
          congr 2
          funext x
          congr 1
          funext v
          rw [List.ofFn_succ]
          rfl

/-- A program of challenges and returns only: no prover move. -/
inductive SampleOnly {α : Type} : Prog α → Prop
  | ret (a : α) : SampleOnly (.ret a)
  | fail : SampleOnly .fail
  | sample {k : E → Prog α} : (∀ c, SampleOnly (k c)) → SampleOnly (.sample k)

/-- What a program of challenges reaches is a program of challenges. -/
theorem SampleOnly.after {α : Type} {p : Prog α} (hp : SampleOnly p) :
    ∀ {l : List Ev} {q : Prog α}, p.after l = some q → SampleOnly q := by
  induction hp with
  | ret a =>
    intro l q h
    cases l with
    | nil => simp [Prog.after] at h; subst h; exact .ret a
    | cons e l => cases e <;> simp [Prog.after] at h
  | fail =>
    intro l q h
    cases l with
    | nil => simp [Prog.after] at h; subst h; exact .fail
    | cons e l => cases e <;> simp [Prog.after] at h
  | sample _ ih =>
    intro l q h
    cases l with
    | nil => simp [Prog.after] at h; subst h; exact .sample ‹_›
    | cons e l =>
      cases e <;> simp [Prog.after] at h
      exact ih _ h

/-- A program of challenges makes no prover move. -/
theorem SampleOnly.not_isMove {α : Type} {q : Prog α} (hq : SampleOnly q) : ¬ q.IsMove := by
  cases hq <;> simp [Prog.IsMove]

/-- The fingerprint challenges `(α, β)` as the wire draws them: four, then one. -/
def abProg : Prog (List E × E) :=
  (Prog.sampleN 4).bind fun as ↦ Prog.sampleE.bind fun b ↦ Prog.ret (as, b)

/-- The wire's four `α` as the protocol's. -/
def toAlpha (as : List E) : Fin 4 → E := fun i ↦ as.getD i 0

theorem sampleOnly_abProg : SampleOnly abProg :=
  .sample fun _ ↦ .sample fun _ ↦ .sample fun _ ↦ .sample fun _ ↦ .sample fun _ ↦ .ret _

theorem toAlpha_ofFn (v : Fin 4 → E) : toAlpha (List.ofFn v) = v := by
  funext i
  fin_cases i <;> rfl

open Classical in
/-- **The union bound over candidates**, for any finite type of challenges. -/
theorem card_exists_le_of {α β : Type} [Fintype α] {C : Set β} (hfin : C.Finite) {L₀ : ℕ}
    (hcard : C.ncard ≤ L₀) (P : β → α → Prop) {e : ℝ≥0∞}
    (h : ∀ q ∈ C, (Fintype.card α : ℝ≥0∞)⁻¹ *
      ((Finset.univ.filter fun c ↦ P q c).card : ℝ≥0∞) ≤ e) :
    (Fintype.card α : ℝ≥0∞)⁻¹ *
        ((Finset.univ.filter fun c ↦ ∃ q ∈ C, P q c).card : ℝ≥0∞) ≤ L₀ * e := by
  let s := hfin.toFinset
  have hsub : (Finset.univ.filter fun c ↦ ∃ q ∈ C, P q c) ⊆
      s.biUnion fun q ↦ Finset.univ.filter fun c ↦ P q c := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨q, hq, hp⟩ := hc
    exact Finset.mem_biUnion.mpr ⟨q, hfin.mem_toFinset.mpr hq, by simpa using hp⟩
  calc (Fintype.card α : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun c ↦ ∃ q ∈ C, P q c).card : ℝ≥0∞)
      ≤ (Fintype.card α : ℝ≥0∞)⁻¹ *
          ∑ q ∈ s, ((Finset.univ.filter fun c ↦ P q c).card : ℝ≥0∞) := by
        gcongr
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ = ∑ q ∈ s, (Fintype.card α : ℝ≥0∞)⁻¹ *
          ((Finset.univ.filter fun c ↦ P q c).card : ℝ≥0∞) := Finset.mul_sum _ _ _
    _ ≤ ∑ _q ∈ s, e := Finset.sum_le_sum fun q hq ↦ h q (hfin.mem_toFinset.mp hq)
    _ = s.card * e := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ L₀ * e := by
        gcongr
        rw [← Set.ncard_eq_toFinset_card C hfin]
        exact_mod_cast hcard

/-! ## The fingerprint challenges -/

section Challenges

variable (I : M3Instance) (cands : Word → Set (∀ i, TheOracle I i)) (input : I.Stmt)

/-- The error of the fingerprint challenges over at most `L₀` candidates:
`L₀ · 4 · 2^{μ_bus} / |E|` (Theorem 5.1). -/
noncomputable def abError (L₀ : ℕ) : ℝ≥0∞ := L₀ * (overE (4 * 2 ^ I.μBus) : ℝ≥0∞)

open Classical in
/-- From a stack outside `M3Holds`, the fingerprint challenges that satisfy the relation after
them are at most a fraction `4 · 2^{μ_bus} / |E|` (`Bus.challengeSecurity`). -/
theorem ab_card_le (hI : Bus.Conditions I) (o : ∀ i, TheOracle I i)
    (ho : ((input, o), ()) ∉ Seam.commit I) :
    (Fintype.card ((Fin 4 → E) × E) : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun ab ↦
      (((input, ab), o), ()) ∈ Bus.afterChallenge I).card : ℝ≥0∞) ≤
        (overE (4 * 2 ^ I.μBus) : ℝ≥0∞) := by
  have h := Typed.sample_escape (Bus.challengeSecurity hI) input o
    (fun w hw ↦ by cases w; exact ho hw) rfl
  have h : Pr{let c ← $ᵗ ((Fin 4 → E) × E)}[(((input, c), o), ()) ∈ Bus.afterChallenge I] ≤
      (overE (4 * 2 ^ I.μBus) : ℝ≥0∞) :=
    le_trans (prEvent_mono _ _ _ fun c hc ↦ ⟨(), hc⟩) h
  rw [SampleableType.prEvent_uniformSample, div_eq_mul_inv, mul_comm] at h
  exact h

variable {εmax : ℝ≥0∞}

open Classical in
/-- **The fingerprint challenges** (`alphas = sample_n(BUS_BITS)`, `beta = sample()`,
`verifier.py:540-542`): one group of five challenges, the protocol's one challenge `(α, β)`,
escaping the commitment's doom with probability at most `L₀ · 4 · 2^{μ_bus} / |E|`. -/
noncomputable def abSpec (hI : Bus.Conditions I) {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hlt : abError I L₀ < 1) {T : ℝ≥0∞} :
    Spec abProg (HDoom cands (Seam.commit I) input)
      (fun ab h ↦ HDoom cands (Bus.afterChallenge I) (input, (toAlpha ab.1, ab.2)) h) εmax
      (abError I L₀ + T) T :=
  Spec.ofNoMove (fun _ ha ↦ (sampleOnly_abProg.after ha).not_isMove) hlt fun h₀ hp ↦ by
    obtain ⟨W, hW, hR⟩ := hp
    let bad : (Fin 4 → E) × E → Prop := fun ab ↦
      ∃ o ∈ cands W, (((input, ab), o), ()) ∈ Bus.afterChallenge I
    unfold Prog.escRet abProg
    refine le_trans (retExp_sampleN_bind_le _ h₀ 4 _
      (fun as ↦ (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ b : E, if bad (toAlpha as, b) then 1 else 0)
      (fun as l ↦ ?_) []) ?_
    · show (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ b : E, (if HDoom cands (Bus.afterChallenge I)
          (input, (toAlpha as, b)) (h₀ ++ (l ++ [Ev.sample b])) then 0 else 1) ≤ _
      gcongr with b
      by_cases h1 : HDoom cands (Bus.afterChallenge I) (input, (toAlpha as, b))
          (h₀ ++ (l ++ [Ev.sample b]))
      · simp [h1]
      · have h2 : bad (toAlpha as, b) := by
          by_contra h2
          exact h1 ⟨W, firstWord_append hW _, fun o ho hin ↦ h2 ⟨o, ho, hin⟩⟩
        simp [h1, h2]
    · simp only [toAlpha_ofFn]
      have hcardT : (Fintype.card ((Fin 4 → E) × E) : ℝ≥0∞) =
          (Fintype.card E : ℝ≥0∞) ^ 4 * Fintype.card E := by
        rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
        push_cast
        ring
      calc ((Fintype.card E : ℝ≥0∞) ^ 4)⁻¹ * ∑ v : Fin 4 → E, (Fintype.card E : ℝ≥0∞)⁻¹ *
            ∑ b : E, (if bad (v, b) then 1 else 0)
          = (Fintype.card ((Fin 4 → E) × E) : ℝ≥0∞)⁻¹ *
              ((Finset.univ.filter fun ab ↦ bad ab).card : ℝ≥0∞) := by
            rw [← Finset.mul_sum, ← mul_assoc, ← ENNReal.mul_inv (by simp) (by simp), ← hcardT,
              ← Fintype.sum_prod_type', Finset.sum_boole]
        _ ≤ L₀ * (overE (4 * 2 ^ I.μBus) : ℝ≥0∞) :=
            card_exists_le_of (hfin W) (hcard W)
              (fun o ab ↦ (((input, ab), o), ()) ∈ Bus.afterChallenge I)
              fun o ho ↦ ab_card_le I input hI o (hR o ho)

end Challenges

/-! ## The roots and the walk -/

section Gkr

variable (I : M3Instance) (cands : Word → Set (∀ i, TheOracle I i))
  (data : Bus.Data I)

/-- The roots' message keeps doom: from doom after the fingerprint challenges, a nonzero count
root makes doom on the grand product's input relation. -/
theorem roots_keep (hI : Bus.Conditions I) {C : Set (∀ i, TheOracle I i)}
    (hpre : RelDoom C (Bus.afterChallenge I) data) (shared count : E) (hc : count ≠ 0) :
    RelDoom C (Gkr.relIn 3 I.μBus (Bus.leaves I) (Bus.riders I)) (data, ![shared, shared, count]) :=
  say_keep (Bus.rootsSecurity hI) hpre (shared, count) (by simpa using hc)

/-- The protocol's roots statement is the wire's GKR state at layer `0`. -/
theorem rootStmt_eq (shared count : E) :
    Gkr.rootStmt 3 (data, ![shared, shared, count]) =
      layerStmtOf data 0 ⟨[shared, shared, count], []⟩ := by
  refine Prod.ext rfl (Prod.ext (Vector.ext fun i hi ↦ absurd hi (by omega)) ?_)
  funext t
  fin_cases t <;> rfl

/-- What the wire's GKR gives: the count root `0`, which the bus phase rejects, or doom on the
argument's output relation at the point and values it returns. -/
def GkrPost (r : E × List E × List E) (h : List Ev) : Prop :=
  r.1 = 0 ∨ (r.2.1.length = I.μBus ∧ r.2.2.length = 3 ∧
    HDoom cands (Gkr.relOut 3 I.μBus (Bus.leaves I) (Bus.riders I))
      (layerStmtOf data I.μBus ⟨r.2.2, r.2.1⟩) h)

variable {εmax : ℝ≥0∞}

open Classical in
/-- **`verify_gkr_grand_products`** at the depth `μ_bus`: from doom after the fingerprint
challenges to `GkrPost`. Each round's challenge is charged `L₀ · 4 / |E|` at most, each combiner
`L₀ · 2 / |E|`, each combination challenge `L₀ / |E|`. -/
noncomputable def gkrSpec (hI : Bus.Conditions I) {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hμ : I.μBus ≠ 0) (he : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax) :
    Spec (verifyGkrGrandProducts I.μBus) (HDoom cands (Bus.afterChallenge I) data)
      (GkrPost I cands data) εmax 0 0 :=
  (Spec.readE (Post := fun _ h ↦ HDoom cands (Bus.afterChallenge I) data h)
    (fun _ _ hp ↦ hp.append _) zero_le).bind' fun shared ↦
  (Spec.readE (Post := fun count h ↦ count = 0 ∨ HDoom cands
      (Gkr.relIn 3 I.μBus (Bus.leaves I) (Bus.riders I)) (data, ![shared, shared, count]) h)
    (fun _ count hp ↦ by
      by_cases hz : count = 0
      · exact .inl hz
      · obtain ⟨W, hW, hR⟩ := hp
        exact .inr ⟨W, firstWord_append hW _, roots_keep I data hI hR shared count hz⟩)
    hlam).bind' fun count ↦
  if hz : count = 0 then
    ((alwaysSpec0 (Post := fun _ _ ↦ True) (fun _ _ ↦ trivial)).bind' fun (s : GkrState) ↦
      (Spec.ret (Post := GkrPost I cands data) (count, s.point, s.values)).mono
        (fun _ _ ↦ .inl hz) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
      (fun _ _ ↦ trivial) (fun _ _ h ↦ h) le_rfl zero_le le_rfl
  else
    ((gkrLayersSpec (Bus.leaves I) (Bus.riders I) cands data hfin hcard he hT I.μBus 0 (by simp)
      ⟨[shared, shared, count], []⟩).bind' fun s ↦
    (Spec.ret (Post := GkrPost I cands data) (count, s.point, s.values)).mono
      (fun _ hp ↦ by
        unfold LayersPre at hp
        simp only [↓reduceIte] at hp
        exact .inr hp) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
      (fun h₀ hp ↦ by
        obtain ⟨W, hW, hR⟩ := hp.resolve_left hz
        unfold LayersPre
        simp only [hμ, ↓reduceIte]
        refine ⟨rfl, rfl, W, hW, fun o ho hin ↦ hR o ho
          ((Gkr.relIn_iff_layerRel_zero 3 I.μBus (Bus.leaves I) (Bus.riders I) _ o).mpr ?_)⟩
        rw [rootStmt_eq I data shared count]
        exact hin) (fun _ _ h ↦ h) le_rfl (by simp [nextError, hμ]) le_rfl

end Gkr

/-! ## The phase -/

section Phase

/-- The pure part of `verify_bus_balance` after the reads (`verifier.py:548-593`): the claims, the
fingerprints, and the leaf decomposition of the three sides. -/
def pyBusResult (layout : Verifier.Layout) (alphas : List E) (beta : E)
    (point treeValues memory : List E) (memoryFinal bytecodeFinal : E) : BusResult :=
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayout frameworkLogRows layout.push
  let pullLayout := busLayout frameworkLogRows layout.pull
  let countLayout := busLayout [] layout.count
  let weights := eqKernel alphas
  let memoryLow := point.take layout.logMemory
  let bytecodeLow := point.take layout.logBytecode
  let claims : List Verifier.ColumnClaim :=
    (List.zipWith (fun column value ↦ ⟨column, memoryLow, value⟩) [memory0, memory1, memory2]
      memory) ++
    [⟨memoryFinalCounters, memoryLow, memoryFinal⟩, ⟨bytecodeFinalCounters, bytecodeLow,
      bytecodeFinal⟩]
  let fp := fingerprints weights memory memoryLow bytecodeLow
    (multilinearEval (layout.bytecode.map ofK) (bytecodeLow ++ alphas))
  let finalPc := Verifier.gpow (2 ^ layout.logBytecode - 1)
  let forms0 : List (List Form) := tables.map fun _ ↦ [{}, {}, {}]
  let (forms1, total0) := accumulateSide forms0 0 layout.push pushLayout (fp (Verifier.gpow 0) 1 1)
    weights beta point (treeValues.getD 0 0)
  let (forms2, total1) := accumulateSide forms1 1 layout.pull pullLayout
    (fp finalPc memoryFinal bytecodeFinal) weights beta point (treeValues.getD 1 0)
  let (forms3, total2) := accumulateSide forms2 2 layout.count countLayout [] [1] 0 point
    (treeValues.getD 2 0)
  ⟨claims, point, forms3, [total0, total1, total2]⟩

/-- What the bus phase reads after the fingerprint challenges: the challenges, the grand
product's point and values, and the boundary values. -/
structure BusWit where
  /-- The four `α`. -/
  alphas : List E
  /-- `β`. -/
  beta : E
  /-- The grand product's point. -/
  point : List E
  /-- The three trees' values there. -/
  values : List E
  /-- The memory columns' values. -/
  memory : List E
  /-- `MEMORY_FINAL_COUNTERS`' value. -/
  mf : E
  /-- `BYTECODE_FINAL_COUNTERS`' value. -/
  bf : E

/-- The bus phase's result on what it read. -/
def BusWit.result (layout : Verifier.Layout) (w : BusWit) : BusResult :=
  pyBusResult layout w.alphas w.beta w.point w.values w.memory w.mf w.bf

/-- The bus phase after the grand product, followed by `k`: the count root's check, the boundary
values, and `k` of what was read. -/
def busTailK {β : Type} (k : BusWit → Prog β) (alphas : List E) (beta : E)
    (r : E × List E × List E) : Prog β :=
  match r with
  | (countRoot, point, values) => do
    Prog.require (countRoot ≠ 0)
    let memory ← Prog.readN 3
    let mf ← Prog.readE
    let bf ← Prog.readE
    k ⟨alphas, beta, point, values, memory, mf, bf⟩

/-- **The bus phase followed by `f`** is the fingerprint challenges, the grand product at the push
side's depth, and the tail followed by `f` of the result. -/
theorem verifyBusBalance_bind_eq {β : Type} (layout : Verifier.Layout) (f : BusResult → Prog β) :
    (verifyBusBalance .computed layout).bind f =
      abProg.bind fun ab ↦ (verifyGkrGrandProducts
        (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth).bind
        (busTailK (fun w ↦ f (w.result layout)) ab.1 ab.2) := by
  unfold verifyBusBalance Evaluations.computed abProg busTailK BusWit.result
  simp only [Prog.bind_eq, Prog.bind_assoc, Prog.ret_bind, Prog.pure_eq]
  rfl

variable (I : M3Instance) (hI : Bus.Conditions I) (cands : Word → Set (∀ i, TheOracle I i))
  (input : I.Stmt) (layout : Verifier.Layout)

/-- The boundary values keep doom: from doom on the grand product's output relation, the values
sent make doom on the bus seam at the protocol's output. -/
theorem values_keep {C : Set (∀ i, TheOracle I i)}
    {ℓ : Gkr.LayerStmt (Bus.Data I) E 3 I.μBus}
    (hpre : RelDoom C (Gkr.relOut 3 I.μBus (Bus.leaves I) (Bus.riders I)) ℓ)
    (vals : Vector E I.busClaims) : RelDoom C (Seam.bus I) (ℓ.1.1, Bus.busOut hI ℓ vals) :=
  say_keep (Bus.valuesSecurity hI) hpre vals rfl

/-- The grand product's last statement on what the bus phase read. -/
def BusWit.layer (w : BusWit) : Gkr.LayerStmt (Bus.Data I) E 3 I.μBus :=
  layerStmtOf (input, (toAlpha w.alphas, w.beta)) I.μBus ⟨w.values, w.point⟩

/-- The boundary values as the protocol's message. -/
def BusWit.vals (w : BusWit) : Vector E I.busClaims := vecOf I.busClaims (w.memory ++ [w.mf, w.bf])

/-- **The bus seam on the wire, at what was read**: no candidate puts the protocol's output on
those values in the bus seam. -/
def BusAt (w : BusWit) (h : List Ev) : Prop :=
  w.point.length = I.μBus ∧ w.values.length = 3 ∧ w.memory.length = 3 ∧
    HDoom cands (Seam.bus I) (input, Bus.busOut hI (w.layer I input) (w.vals I)) h

/-- **The bus seam on the wire**: the bus phase returns the Python's leaf decomposition of what it
read, and the bus seam holds of no candidate at the protocol's output on it. -/
def BusPost (bus : BusResult) (h : List Ev) : Prop :=
  ∃ w : BusWit, bus = w.result layout ∧ BusAt I hI cands input w h

variable {εmax : ℝ≥0∞}

/-- **The bus phase's tail, then a continuation** specified from the bus seam at what was read:
the count root's check (which rejects the root `0`), the boundary values (the protocol's last
message), then `k`. -/
noncomputable def busTailSpec {β : Type} {k : BusWit → Prog β} {Q : β → List Ev → Prop}
    {Lk T : ℝ≥0∞} (hLk : Lk ≤ εmax) (K : ∀ w, Spec (k w) (BusAt I hI cands input w) Q εmax Lk T)
    (alphas : List E) (beta : E) (r : E × List E × List E) :
    Spec (busTailK k alphas beta r) (GkrPost I cands (input, (toAlpha alphas, beta)) r) Q
      εmax 0 T :=
  match r with
  | (countRoot, point, values) =>
    let P : List Ev → Prop := fun h ↦ point.length = I.μBus ∧ values.length = 3 ∧
      HDoom cands (Gkr.relOut 3 I.μBus (Bus.leaves I) (Bus.riders I))
        (layerStmtOf (input, (toAlpha alphas, beta)) I.μBus ⟨values, point⟩) h
    have hP : ∀ h x, P h → P (h ++ [Ev.read x]) := fun _ _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2.append _⟩
    (Spec.require (Post := fun _ h ↦ P h) fun _ hp hc ↦ hp.resolve_left hc).bind' fun _ ↦
    (readNSuccSpec P hP zero_le 2).bind' fun memory ↦
    (Spec.readE (Post := fun _ h ↦ memory.length = 3 ∧ P h)
      (fun _ _ hp ↦ ⟨hp.1, hP _ _ hp.2⟩) zero_le).bind' fun mf ↦
    (Spec.readE (Post := fun bf h ↦ BusAt I hI cands input ⟨alphas, beta, point, values, memory,
        mf, bf⟩ h)
      (fun _ bf hp ↦ by
        obtain ⟨hm, hl, hv, W, hW, hR⟩ := hp
        exact ⟨hl, hv, hm, W, firstWord_append hW _, values_keep I hI hR _⟩) hLk).bind'
      fun bf ↦ K ⟨alphas, beta, point, values, memory, mf, bf⟩

/-- **The bus phase, then a continuation** (`verify_bus_balance`, `verifier.py:534-593`): from
the commitment's doom (no candidate satisfies `M3Holds`, `Seam.commit`) to the bus seam at what
was read, then `f` of the result, specified from there by `K`, at the depth `μ_bus` of the push
side. The fingerprint challenges are charged `L₀ · 4 · 2^{μ_bus} / |E|`; every later group of
challenges (a sumcheck round's, the descendants' combination challenges with the next combiner)
at most `L₀ · 4 / |E|`. -/
noncomputable def busThenSpec {β : Type} {f : BusResult → Prog β} {Q : β → List Ev → Prop}
    {Lk T : ℝ≥0∞} (hLk : Lk ≤ εmax)
    (K : ∀ w : BusWit, Spec (f (w.result layout)) (BusAt I hI cands input w) Q εmax Lk T)
    {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hμ : I.μBus ≠ 0)
    (hdepth : (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth = I.μBus)
    (hab : abError I L₀ < 1) (he : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax) :
    Spec ((verifyBusBalance .computed layout).bind f) (HDoom cands (Seam.commit I) input) Q εmax
      (abError I L₀ + 0) T :=
  Spec.congr (verifyBusBalance_bind_eq layout f).symm
    ((abSpec I cands input hI hfin hcard hab (T := 0)).bind' fun ab ↦
      (Spec.congr (by rw [hdepth])
        (gkrSpec I cands (input, (toAlpha ab.1, ab.2)) hI hfin hcard hμ he hT hlam)).bind'
        fun r ↦ busTailSpec I hI cands input hLk K ab.1 ab.2 r)

/-- **The bus phase** alone: from the commitment's doom to the bus seam on the wire. -/
noncomputable def busPhaseSpec {T : ℝ≥0∞} (hTf : T ≤ εmax) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hμ : I.μBus ≠ 0)
    (hdepth : (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth = I.μBus)
    (hab : abError I L₀ < 1) (he : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax) :
    Spec (verifyBusBalance .computed layout) (HDoom cands (Seam.commit I) input)
      (BusPost I hI cands input layout) εmax (abError I L₀ + 0) T :=
  Spec.congr (Prog.bind_ret _)
    (busThenSpec I hI cands input layout hTf
      (fun w ↦ (Spec.ret (Post := BusPost I hI cands input layout) (w.result layout)).mono
        (fun _ hp ↦ ⟨w, rfl, hp⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)
      hfin hcard hμ hdepth hab he hT hlam)

end Phase

end
end LeanVM.Protocol.EndToEnd.Front
