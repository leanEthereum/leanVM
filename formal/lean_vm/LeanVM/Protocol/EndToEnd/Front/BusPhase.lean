/-
  LeanVM.Protocol.EndToEnd.Front.BusPhase

  The verifier program's bus phase (`verify_bus_balance`) specified on the oracle protocol's
  relations: the fingerprint challenges, the roots, the grand-product walk and the boundary
  values, from the commitment's doom to doom on the bus seam.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.BusShare
public import LeanVM.Protocol.EndToEnd.Complete.BusLayout
public import LeanVM.Protocol.BusSecurity

/-!
# The bus phase on doom

`verifyBusBalance layout` (`crates/verifier/src/bus.rs:130-247`) is the oracle protocol's `busPhase`
(`LeanVM.Protocol.Bus`) on the wire, with two parts the protocol does not have: the grind before
the fingerprint challenges (`busGrindingBits`, the challenges' error `2^{μ_bus}/|E|` discounted by
it) and the bytecode share's sumcheck (`BusShare`), which returns only the true share, the
fingerprint's part the protocol computes from the public bytecode. This module specifies its parts
on the protocol's relations, in the calculus of verifier programs:

* `alwaysSpec`: a sub-program from a fact that already decides its postcondition (the count root
  `0`, which the later `require` rejects);
* `gkrSpec`: `verify_gkr_grand_products` (`bus.rs:14-51`), from doom on the relation after
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
noncomputable def alwaysSpec {α : Type} {p : VerifierProgram α} {Pre : List Ev → Prop}
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
noncomputable def alwaysSpec0 {α : Type} {p : VerifierProgram α} {Pre : List Ev → Prop}
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
    ∀ (n : ℕ) (k : List E → VerifierProgram β) (B : List E → ℝ≥0∞),
      (∀ xs l, VerifierProgram.retExp g h₀ l (k xs) ≤ B xs) → ∀ l,
      VerifierProgram.retExp g h₀ l ((VerifierProgram.sampleChallenges n).bind k) ≤
        ((Fintype.card E : ℝ≥0∞) ^ n)⁻¹ * ∑ v : Fin n → E, B (List.ofFn v)
  | 0, k, B, hk, l => by
    simpa [VerifierProgram.sampleChallenges] using hk [] l
  | n + 1, k, B, hk, l => by
    show (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ x : E, VerifierProgram.retExp g h₀ (l ++ [Ev.sample x])
        (((VerifierProgram.sampleChallenges n).bind fun xs ↦ VerifierProgram.ret (x ::
            xs)).bind k) ≤ _
    have ih : ∀ x : E, VerifierProgram.retExp g h₀ (l ++ [Ev.sample x])
        (((VerifierProgram.sampleChallenges n).bind fun xs ↦ VerifierProgram.ret (x ::
            xs)).bind k) ≤
        ((Fintype.card E : ℝ≥0∞) ^ n)⁻¹ * ∑ v : Fin n → E, B (x :: List.ofFn v) := fun x ↦ by
      rw [VerifierProgram.bind_assoc]
      exact retExp_sampleN_bind_le g h₀ n (fun xs ↦ k (x :: xs)) (fun xs ↦ B (x :: xs))
        (fun xs l ↦ hk _ l) _
    calc (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ x : E, VerifierProgram.retExp g h₀ (l ++ [Ev.sample x])
          (((VerifierProgram.sampleChallenges n).bind fun xs ↦ VerifierProgram.ret (x ::
              xs)).bind k)
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
inductive SampleOnly {α : Type} : VerifierProgram α → Prop
  | ret (a : α) : SampleOnly (.ret a)
  | fail : SampleOnly .fail
  | sample {k : E → VerifierProgram α} : (∀ c, SampleOnly (k c)) → SampleOnly (.sample k)

/-- What a program of challenges reaches is a program of challenges. -/
theorem SampleOnly.after {α : Type} {p : VerifierProgram α} (hp : SampleOnly p) :
    ∀ {l : List Ev} {q : VerifierProgram α}, p.after l = some q → SampleOnly q := by
  induction hp with
  | ret a =>
    intro l q h
    cases l with
    | nil => simp [VerifierProgram.after] at h; subst h; exact .ret a
    | cons e l => cases e <;> simp [VerifierProgram.after] at h
  | fail =>
    intro l q h
    cases l with
    | nil => simp [VerifierProgram.after] at h; subst h; exact .fail
    | cons e l => cases e <;> simp [VerifierProgram.after] at h
  | sample _ ih =>
    intro l q h
    cases l with
    | nil => simp [VerifierProgram.after] at h; subst h; exact .sample ‹_›
    | cons e l =>
      cases e <;> simp [VerifierProgram.after] at h
      exact ih _ h

/-- A program of challenges makes no prover move. -/
theorem SampleOnly.not_isMove {α : Type} {q : VerifierProgram α} (hq : SampleOnly q) : ¬
    q.IsMove := by
  cases hq <;> simp [VerifierProgram.IsMove]

/-- The fingerprint challenges `(α, β)` as the wire draws them: sixteen slot weights, then
`β`. -/
def abProg : VerifierProgram (List E × E) :=
  (VerifierProgram.sampleChallenges (2 ^ busBits)).bind fun as ↦
    VerifierProgram.sampleChallenge.bind fun b ↦ VerifierProgram.ret (as, b)

/-- The wire's sixteen weights as the protocol's. -/
def toAlpha (as : List E) : Fin 16 → E := fun i ↦ as.getD i 0

/-- Challenges, then a program of challenges, make a program of challenges. -/
theorem sampleOnly_sampleN_bind {β : Type} :
    ∀ (n : ℕ) (k : List E → VerifierProgram β), (∀ xs, SampleOnly (k xs)) →
      SampleOnly ((VerifierProgram.sampleChallenges n).bind k)
  | 0, k, hk => hk []
  | n + 1, k, hk => .sample fun x ↦ by
    have h := sampleOnly_sampleN_bind n (fun xs ↦ k (x :: xs)) fun xs ↦ hk (x :: xs)
    simpa only [VerifierProgram.ret_bind, VerifierProgram.bind_assoc, VerifierProgram.pure_eq,
      VerifierProgram.bind_eq] using h

theorem sampleOnly_abProg : SampleOnly abProg :=
  sampleOnly_sampleN_bind _ _ fun _ ↦ .sample fun _ ↦ .ret _

theorem toAlpha_ofFn (v : Fin 16 → E) : toAlpha (List.ofFn v) = v := by
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
`L₀ · 2^{μ_bus} / |E|` (Theorem 5.1). -/
noncomputable def abError (L₀ : ℕ) : ℝ≥0∞ := L₀ * (overE (2 ^ I.μBus) : ℝ≥0∞)

open Classical in
/-- From a stack outside `M3Holds`, the fingerprint challenges that satisfy the relation after
them are at most a fraction `2^{μ_bus} / |E|` (`Bus.challengeSecurity`). -/
theorem ab_card_le (hI : Bus.Conditions I) (o : ∀ i, TheOracle I i)
    (ho : ((input, o), ()) ∉ Seam.commit I) :
    (Fintype.card ((Fin 16 → E) × E) : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun ab ↦
      (((input, ab), o), ()) ∈ Bus.afterChallenge I).card : ℝ≥0∞) ≤
        (overE (2 ^ I.μBus) : ℝ≥0∞) := by
  have h := Typed.sample_escape (Bus.challengeSecurity hI) input o
    (fun w hw ↦ by cases w; exact ho hw) rfl
  have h : Pr{let c ← $ᵗ ((Fin 16 → E) × E)}[(((input, c), o), ()) ∈ Bus.afterChallenge I] ≤
      (overE (2 ^ I.μBus) : ℝ≥0∞) :=
    le_trans (prEvent_mono _ _ _ fun c hc ↦ ⟨(), hc⟩) h
  rw [SampleableType.prEvent_uniformSample, div_eq_mul_inv, mul_comm] at h
  exact h

variable {εmax : ℝ≥0∞}

open Classical in
/-- **The fingerprint challenges** (`weights = samples(2^BUS_BITS)`, `beta = sample()`,
`bus.rs:139-142`): one group of seventeen challenges, the protocol's one challenge `(α, β)`,
escaping the commitment's doom with probability at most `L₀ · 2^{μ_bus} / |E|`. -/
noncomputable def abSpec (hI : Bus.Conditions I) {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hlt : abError I L₀ < 1) {T : ℝ≥0∞} :
    Spec abProg (HDoom cands (Seam.commit I) input)
      (fun ab h ↦ HDoom cands (Bus.afterChallenge I) (input, (toAlpha ab.1, ab.2)) h) εmax
      (abError I L₀ + T) T :=
  Spec.ofNoMove (fun _ ha ↦ (sampleOnly_abProg.after ha).not_isMove) hlt fun h₀ hp ↦ by
    obtain ⟨W, hW, hR⟩ := hp
    let bad : (Fin 16 → E) × E → Prop := fun ab ↦
      ∃ o ∈ cands W, (((input, ab), o), ()) ∈ Bus.afterChallenge I
    unfold VerifierProgram.escRet abProg
    refine le_trans (retExp_sampleN_bind_le _ h₀ 16 _
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
      have hcardT : (Fintype.card ((Fin 16 → E) × E) : ℝ≥0∞) =
          (Fintype.card E : ℝ≥0∞) ^ 16 * Fintype.card E := by
        rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
        push_cast
        ring
      calc ((Fintype.card E : ℝ≥0∞) ^ 16)⁻¹ * ∑ v : Fin 16 → E, (Fintype.card E : ℝ≥0∞)⁻¹ *
            ∑ b : E, (if bad (v, b) then 1 else 0)
          = (Fintype.card ((Fin 16 → E) × E) : ℝ≥0∞)⁻¹ *
              ((Finset.univ.filter fun ab ↦ bad ab).card : ℝ≥0∞) := by
            rw [← Finset.mul_sum, ← mul_assoc, ← ENNReal.mul_inv (by simp) (by simp), ← hcardT,
              ← Fintype.sum_prod_type', Finset.sum_boole]
        _ ≤ L₀ * (overE (2 ^ I.μBus) : ℝ≥0∞) :=
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

/-- What the bus phase reads after the fingerprint challenges: the sixteen slot weights and `β`,
the grand product's point and values, the boundary values, and the bytecode's share and point. -/
structure BusWit where
  /-- The sixteen slot weights. -/
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
  /-- The bytecode's share of a bytecode leaf. -/
  share : E
  /-- The point the share's sumcheck leaves the bytecode at. -/
  bytecodePoint : List E

/-- The bus phase's result on what it read (`Complete.busOut`). -/
def BusWit.result (layout : Verifier.Layout) (w : BusWit) : BusResult :=
  Complete.busOut layout w.alphas w.beta w.point w.values w.memory w.mf w.bf w.share
    w.bytecodePoint

/-- The bus phase after the grand product, followed by `k`: the count root's check, the boundary
values, the bytecode's share and its evaluation (`shareProg`), and `k` of what was read. -/
def busTailK {β : Type} (layout : Verifier.Layout) (k : BusWit → VerifierProgram β)
    (alphas : List E) (beta : E) (r : E × List E × List E) : VerifierProgram β := do
  VerifierProgram.require (r.1 ≠ 0)
  let memory ← VerifierProgram.readScalars 2
  let mf ← VerifierProgram.readScalar
  let bf ← VerifierProgram.readScalar
  let (share, bytecodePoint, value) ← bytecodeShare alphas (r.2.1.take layout.logBytecode)
  computedBytecodeValue layout.bytecode bytecodePoint value
  k ⟨alphas, beta, r.2.1, r.2.2, memory, mf, bf, share, bytecodePoint⟩

/-- The share and its evaluation, the share's triple taken apart, are `shareProg`. -/
theorem shareProg_bind {β : Type} (weights low : List E) (words : List K)
    (k : E → List E → VerifierProgram β) :
    (bytecodeShare weights low >>= fun x ↦ match x with
      | (share, bytecodePoint, value) =>
        computedBytecodeValue words bytecodePoint value >>= fun _ ↦ k share bytecodePoint) =
      shareProg weights low words >>= fun r ↦ k r.1 r.2.1 := by
  unfold shareProg
  simp only [VerifierProgram.bind_eq, VerifierProgram.bind_assoc]
  congr 1

/-- **The bus phase followed by `f`** is the depth's check, the grind, the fingerprint
challenges, the grand product at the push side's depth, and the tail followed by `f` of the
result. -/
theorem verifyBusBalance_bind_eq {β : Type} (layout : Verifier.Layout) (f : BusResult →
    VerifierProgram β) :
    (verifyBusBalance computedBytecodeValue layout).bind f =
      (VerifierProgram.require
        ((busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth < 64)).bind
        fun _ ↦ (VerifierProgram.grindProofOfWork
          (busGrindingBits (busLayout [0, layout.logMemory, layout.logBytecode]
            layout.push).depth)).bind fun _ ↦
      abProg.bind fun ab ↦ (verifyGkrGrandProducts
        (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth).bind
        fun r ↦ busTailK layout (fun w ↦ f (w.result layout)) ab.1 ab.2 r := by
  rw [Complete.verifyBusBalance_eq]
  simp only [abProg, busTailK, BusWit.result, VerifierProgram.bind_eq,
    VerifierProgram.bind_assoc, VerifierProgram.ret_bind, VerifierProgram.pure_eq]

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

/-- **The bus seam on the wire, at what was read**: the share is the bytecode's true share, and
no candidate puts the protocol's output on the values read in the bus seam. -/
def BusAt (w : BusWit) (h : List Ev) : Prop :=
  w.point.length = I.μBus ∧ w.values.length = 3 ∧ w.memory.length = 2 ∧
    w.share = shareTotal (vecOf (2 ^ 4) w.alphas)
      (slotValues layout.bytecode (w.point.take layout.logBytecode)) ∧
    HDoom cands (Seam.bus I) (input, Bus.busOut hI (w.layer I input) (w.vals I)) h

/-- `BusAt` from its parts. -/
theorem busAt_of {alphas : List E} {beta : E} {point values memory : List E} {mf bf share : E}
    {bytecodePoint : List E} {h : List Ev} (h1 : point.length = I.μBus) (h2 : values.length = 3)
    (h3 : memory.length = 2)
    (h4 : share = shareTotal (vecOf (2 ^ 4) alphas)
      (slotValues layout.bytecode (point.take layout.logBytecode)))
    (h5 : HDoom cands (Seam.bus I) (input, Bus.busOut hI
      (layerStmtOf (input, (toAlpha alphas, beta)) I.μBus ⟨values, point⟩)
      (vecOf I.busClaims (memory ++ [mf, bf]))) h) :
    BusAt I hI cands input layout ⟨alphas, beta, point, values, memory, mf, bf, share,
      bytecodePoint⟩ h :=
  ⟨h1, h2, h3, h4, h5⟩

/-- **The bus seam on the wire**: the bus phase returns the verifier's leaf decomposition of what it
read, and the bus seam holds of no candidate at the protocol's output on it. -/
def BusPost (bus : BusResult) (h : List Ev) : Prop :=
  ∃ w : BusWit, bus = w.result layout ∧ BusAt I hI cands input layout w h

variable {εmax : ℝ≥0∞}

open Classical in
/-- **The bus phase's tail, then a continuation** specified from the bus seam at what was read:
the count root's check (which rejects the root `0`), the boundary values (the protocol's last
message), the bytecode's share (`shareCheckSpec`, through one candidate oracle `o₀`; each of its
rounds' challenges at `2/|E|`), then `k`. The bytecode has `2 ^ (logBytecode + busBits)` words and
its log-size is within the push side's depth, as `build_layout` makes them. -/
noncomputable def busTailSpec {β : Type} {k : BusWit → VerifierProgram β}
    {Q : β → List Ev → Prop} {Lk T : ℝ≥0∞} (hLk : Lk ≤ εmax) (o₀ : ∀ i, TheOracle I i)
    (he : roundError 1 2 + 0 ≤ εmax)
    (hbc : layout.bytecode.length = 2 ^ (layout.logBytecode + busBits))
    (hlb : layout.logBytecode ≤ I.μBus)
    (K : ∀ w, Spec (k w) (BusAt I hI cands input layout w) Q εmax Lk T)
    (alphas : List E) (beta : E) (r : E × List E × List E) :
    Spec (busTailK layout k alphas beta r) (GkrPost I cands (input, (toAlpha alphas, beta)) r) Q
      εmax 0 T :=
  let P : List Ev → Prop := fun h ↦ r.2.1.length = I.μBus ∧ r.2.2.length = 3 ∧
    HDoom cands (Gkr.relOut 3 I.μBus (Bus.leaves I) (Bus.riders I))
      (layerStmtOf (input, (toAlpha alphas, beta)) I.μBus ⟨r.2.2, r.2.1⟩) h
  have hP : ∀ h x, P h → P (h ++ [Ev.read x]) := fun _ _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2.append _⟩
  (Spec.require (Post := fun _ h ↦ P h) fun _ hp hc ↦ hp.resolve_left hc).bind' fun _ ↦
  (readNSuccSpec P hP zero_le 1).bind' fun memory ↦
  (Spec.readE (Post := fun _ h ↦ memory.length = 2 ∧ P h)
    (fun _ _ hp ↦ ⟨hp.1, hP _ _ hp.2⟩) zero_le).bind' fun mf ↦
  let P' : E → List Ev → Prop := fun bf h ↦ r.2.1.length = I.μBus ∧ r.2.2.length = 3 ∧
    memory.length = 2 ∧
    HDoom cands (Seam.bus I) (input, Bus.busOut hI
      (layerStmtOf (input, (toAlpha alphas, beta)) I.μBus ⟨r.2.2, r.2.1⟩)
      (vecOf I.busClaims (memory ++ [mf, bf]))) h
  (Spec.readE (Post := P')
    (fun _ bf hp ↦ by
      obtain ⟨hm, hl, hv, W, hW, hR⟩ := hp
      exact ⟨hl, hv, hm, W, firstWord_append hW _, values_keep I hI hR _⟩) zero_le).bind'
    fun bf ↦
  if hl : r.2.1.length = I.μBus then
    Spec.congr (shareProg_bind alphas (r.2.1.take layout.logBytecode) layout.bytecode
      fun share bytecodePoint ↦
        k ⟨alphas, beta, r.2.1, r.2.2, memory, mf, bf, share, bytecodePoint⟩).symm <|
    ((shareCheckSpec (T := Lk) I o₀
      (by rw [hbc, List.length_take, hl, Nat.min_eq_left hlb]; rfl) (P' bf)
      (fun _ l hp ↦ ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.append l⟩)
      (fun _ hp ↦ by obtain ⟨W, hW, -⟩ := hp.2.2.2; exact ⟨W, hW⟩) hLk he).bind' fun s ↦
      (K ⟨alphas, beta, r.2.1, r.2.2, memory, mf, bf, s.1, s.2.1⟩).mono
        (fun _ hp ↦ busAt_of I hI cands input layout hp.1.1 hp.1.2.1 hp.1.2.2.1 hp.2 hp.1.2.2.2)
        (fun _ _ h ↦ h) le_rfl
        le_rfl le_rfl).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl zero_le le_rfl
  else specOfFalse fun _ hp ↦ hl hp.1

/-- **The bus phase, then a continuation** (`verify_bus_balance`, `bus.rs:130-247`): from the
commitment's doom (no candidate satisfies `M3Holds`, `Seam.commit`) to the bus seam at what was
read, then `f` of the result, specified from there by `K`, at the depth `μ_bus` of the push side.
The fingerprint challenges are charged `L₀ · 2^{μ_bus} / |E|`, after the grind of
`busGrindingBits μ_bus` bits (`hab`, the discounted bound); every later group of challenges (a
sumcheck round's, the descendants' combination challenges with the next combiner, the bytecode
share's rounds) at most `L₀ · 4 / |E|`. -/
noncomputable def busThenSpec {β : Type} {f : BusResult → VerifierProgram β}
    {Q : β → List Ev → Prop} {Lk T : ℝ≥0∞} (hLk : Lk ≤ εmax)
    (K : ∀ w : BusWit, Spec (f (w.result layout)) (BusAt I hI cands input layout w) Q εmax Lk T)
    {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hμ : I.μBus ≠ 0)
    (hdepth : (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth = I.μBus)
    (hbc : layout.bytecode.length = 2 ^ (layout.logBytecode + busBits))
    (hlb : layout.logBytecode ≤ I.μBus) (o₀ : ∀ i, TheOracle I i)
    (hlt : abError I L₀ < 1)
    (hab : (2 : ℝ≥0∞)⁻¹ ^ busGrindingBits I.μBus * (abError I L₀ + 0) ≤ εmax)
    (he : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) (hs : roundError 1 2 + 0 ≤ εmax) :
    Spec ((verifyBusBalance computedBytecodeValue layout).bind f)
      (HDoom cands (Seam.commit I) input) Q εmax
      (if busGrindingBits I.μBus = 0 then abError I L₀ + 0 else 0) T :=
  Spec.congr (by rw [verifyBusBalance_bind_eq, hdepth]; rfl) <|
    (Spec.require (c := I.μBus < 64) (Post := fun _ h ↦ HDoom cands (Seam.commit I) input h)
      fun _ hp _ ↦ hp).bind' fun _ ↦
    (Spec.grindP (Post := fun _ h ↦ HDoom cands (Seam.commit I) input h)
      (busGrindingBits I.μBus) (fun _ hp ↦ hp.append _) hab).bind' fun _ ↦
    (abSpec I cands input hI hfin hcard hlt (T := 0)).bind' fun ab ↦
      (gkrSpec I cands (input, (toAlpha ab.1, ab.2)) hI hfin hcard hμ he hT hlam).bind'
        fun r ↦ busTailSpec I hI cands input layout hLk o₀ hs hbc hlb K ab.1 ab.2 r

/-- **The bus phase** alone: from the commitment's doom to the bus seam on the wire. -/
noncomputable def busPhaseSpec {T : ℝ≥0∞} (hTf : T ≤ εmax) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hμ : I.μBus ≠ 0)
    (hdepth : (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth = I.μBus)
    (hbc : layout.bytecode.length = 2 ^ (layout.logBytecode + busBits))
    (hlb : layout.logBytecode ≤ I.μBus) (o₀ : ∀ i, TheOracle I i)
    (hlt : abError I L₀ < 1)
    (hab : (2 : ℝ≥0∞)⁻¹ ^ busGrindingBits I.μBus * (abError I L₀ + 0) ≤ εmax)
    (he : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) (hs : roundError 1 2 + 0 ≤ εmax) :
    Spec (verifyBusBalance computedBytecodeValue layout) (HDoom cands (Seam.commit I) input)
      (BusPost I hI cands input layout) εmax
      (if busGrindingBits I.μBus = 0 then abError I L₀ + 0 else 0) T :=
  Spec.congr (VerifierProgram.bind_ret _)
    (busThenSpec I hI cands input layout hTf
      (fun w ↦ (Spec.ret (Post := BusPost I hI cands input layout) (w.result layout)).mono
        (fun _ hp ↦ ⟨w, rfl, hp⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)
      hfin hcard hμ hdepth hbc hlb o₀ hlt hab he hT hlam hs)

end Phase

end
end LeanVM.Protocol.EndToEnd.Front
