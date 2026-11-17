module

public import Quantum.StdModel.Qrom.CpreTmpl
public import Quantum.StdModel.Qrom.Prf
public import Quantum.Xmss.Assembly.RecordDrop

@[expose] public section

/-!
# The CPRE game of a straight-line reduction in the QROM is runtime 1 on the template

At `romWorld`, averaged over the table, the CPRE game of a straight-line reduction (`slRed`) wins
with the average over the parameter `P`, the chain starts `s` and the honest cells' outputs `v`
of the winning probability of runtime 1, started with the honest cells of `(P, s, v)` hardwired,
running the read program of the game whose challenger answers the chain values from
`θ = thetaOf s v` (`gameθ`).

* **Walks at a function** (`walkH`, `simulateQ_walk`): a walk is a pure function of the table; on
  a table holding `θ` at the honest cells it walks the honest chain (`walkH_honest`).
* **The lazy table** (`lazyT P s`): the honest cell of `(j, ν)` reads the start or the output of
  `(j, ν - 1)`; distinct positions have distinct cells (hypothesis `hinj`).
* **The answers from `θ`** (`ansθ`, `judgeθ`, `gameθ`): at a table holding `θ` at the honest
  cells the game and `gameθ` win alike (`probAt_point`).
* `probAvg_cpre_slRed_eq_reads`: the average, through `probAt_game_slRed_eq` (the mixed game),
  the setup's two uniform samples, the lazy table law (`uavg_tab_eq_fill`), `probAt_point` and
  `readLaw_eq_avg` (runtime 1 at the hardwired honest cells).
-/

open IPFunctor OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Quantum.StdModel.Qrom.CpreQ

open Quantum Quantum.Qrom Props HashSig
open Quantum.Sponge (spongeHardwiredReadRuntime keepMem)
open Quantum.Xmss.Hybrid (uavg)

variable {Par Tw J Val Fn Out : Type} {Msg : Fn → Type} {ch : Chains Par Tw J Val}

/-! ## Walks at a fixed function -/

section walk

variable (ch) in
/-- **The walk at the function `H`**: `n` steps of chain `j` from position `μ` and value `x`. -/
noncomputable def walkH (H : romWorld.Tab) (P : Par) (j : J) : ℕ → ℕ → Val → Val
  | _, 0, x => x
  | μ, n + 1, x => walkH H P j (μ + 1) n
      (ch.step.trunc (romWorld.hashOf H (ch.step.layout () P (ch.tweak j μ) x)))

/-- A walk runs at the table `H` as its pure value. -/
theorem simulateQ_walk (H : romWorld.Tab) (P : Par) (j : J) :
    ∀ n μ x, simulateQ (romWorld.eager H) (ch.walk romWorld P j μ n x) =
      pure (walkH ch H P j μ n x)
  | 0, μ, x => by simp [Chains.walk, walkH]
  | n + 1, μ, x => by
    simp only [Chains.walk, simulateQ_bind, TwColl.eval, simulateQ_map, romWorld.simulateQ_hash,
      map_pure, pure_bind, simulateQ_walk H P j n]
    rfl

variable (ch) in
/-- **The chain steps' inputs fit one encoding.** -/
def StepLen : Prop :=
  ∀ P j ν x, ν < ch.len j → (ch.step.layout () P (ch.tweak j ν) x).length ≤ maxLen

theorem hashOf_step (hlen : StepLen ch) (H : romWorld.Tab) (P : Par)
    (θ : (s : CSrc ch) → CD ch s) (j : J) (ν : ℕ) (h : ν < ch.len j) :
    romWorld.hashOf H (ch.step.layout () P (ch.tweak j ν) (cval θ j ν)) =
      H (cellOf P θ ⟨j, ⟨ν, h⟩⟩) := by
  have hc := Quantum.StdModel.Qrom.encodeInput_eq_cellOf (hlen P j ν (cval θ j ν) h)
  change (encodeInput _).elim 0 H = H ((encodeInput _).getD 0)
  rw [hc]
  rfl

/-- **The honest walk**: on a table holding `θ` at the honest cells, walking from the value at
`μ` reaches the value at `μ + n`. -/
theorem walkH_honest (hlen : StepLen ch) {H : romWorld.Tab} {P : Par}
    {θ : (s : CSrc ch) → CD ch s} (hH : ∀ p, H (cellOf P θ p) = θ (.inr p)) (j : J) :
    ∀ n μ, μ + n ≤ ch.len j → walkH ch H P j μ n (cval θ j μ) = cval θ j (μ + n)
  | 0, μ, _ => rfl
  | n + 1, μ, h => by
    have hμ : μ < ch.len j := by omega
    have e : ch.step.trunc (romWorld.hashOf H (ch.step.layout () P (ch.tweak j μ)
        (cval θ j μ))) = cval θ j (μ + 1) := by
      rw [hashOf_step hlen H P θ j μ hμ, hH]
      simp only [cval, hμ, ↓reduceDIte]
    simp only [walkH]
    rw [e, walkH_honest hlen hH j n (μ + 1) (by omega), show μ + 1 + n = μ + (n + 1) by omega]

end walk

/-! ## The lazy table of a parameter and starts -/

section table

/-- The hidden values of the starts `s` and the honest outputs `v`. -/
def thetaOf (s : J → Val) (v : CPos ch → HashOutput) : (x : CSrc ch) → CD ch x
  | .inl j => s j
  | .inr p => v p

/-- **The lazy table** of the parameter `P` and the starts `s`: the honest cell of `(j, ν)` reads
the start or the output of `(j, ν - 1)`. -/
noncomputable def lazyT (P : Par) (s : J → Val)
    (hinj : ∀ θ, Function.Injective (cellOf (ch := ch) P θ)) :
    LazyTable (CPos ch) HashDomain HashOutput where
  cell p v := cellOf P (thetaOf s v) p
  pre p' p := p'.1 = p.1 ∧ p'.2.val < p.2.val
  wf := Subrelation.wf (fun h ↦ h.2) (InvImage.wf (fun p : CPos ch ↦ p.2.val) wellFounded_lt)
  dep p v v' h := by
    refine cellOf_congr P p ?_
    rcases p with ⟨j, ⟨_ | ν, hν⟩⟩
    · rfl
    · exact h ⟨j, ⟨ν, by omega⟩⟩ ⟨rfl, by simp⟩
  inj v := hinj (thetaOf s v)

theorem lazyT_fill_cell (P : Par) (s : J → Val)
    (hinj : ∀ θ, Function.Injective (cellOf (ch := ch) P θ)) (v : CPos ch → HashOutput)
    (H : romWorld.Tab) (p : CPos ch) :
    (lazyT P s hinj).fill v v H (cellOf P (thetaOf s v) p) = thetaOf s v (.inr p) :=
  (lazyT P s hinj).fill_cell v v H p

end table

/-! ## The game with the chain values from `θ` -/

section gameθ

variable (C : TwColl Par Tw Fn Msg Out)

/-- **The challenger's answers with the chain values from `θ`.** -/
noncomputable def ansθ (P : Par) (θ : (s : CSrc ch) → CD ch s) :
    (q : CpreQuery J Tw Fn Msg) →
      OracleComp romWorld.Oracles ((CpreSpec Par Tw J Val Fn Msg Out).Range q)
  | .value j μ => pure (cval θ j (min μ (ch.len j)))
  | .eval l t m => C.eval romWorld l P t m
  | .reveal => pure P

/-- **The decision with the honest values from `θ`**: the forgery's walk by hash calls. -/
noncomputable def judgeθ (P : Par) (θ : (s : CSrc ch) → CD ch s)
    (log : QueryLog (CpreSpec Par Tw J Val Fn Msg Out)) (out : J × ℕ × Val) :
    OracleComp romWorld.Oracles Bool :=
  (fun e' ↦ holds (CpreValid ch log ∧ out.2.1 < ch.len out.1 ∧
    e' = cval θ out.1 (ch.len out.1) ∧
    (OpenedAtOrBelow log out.1 out.2.1 → out.2.2 ≠ cval θ out.1 out.2.1))) <$>
  ch.walk romWorld P out.1 out.2.1 (ch.len out.1 - out.2.1) out.2.2

/-- **The mixed CPRE game of a reduction with the chain values from `θ`.** -/
noncomputable def gameθ {Q St S0 F : Type} {R : OracleSpec.{0, 0} Q} (P : Par)
    (θ : (s : CSrc ch) → CD ch s)
    (pre : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : S0 → St) (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : S0 → F → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val)) :
    QComp (MixSpec Caller) (QReg.of Unit) (QReg.of Unit) Bool :=
  QuantumComp₂.bind (mixNormal (ansθ C P θ) pre adv st0 σ post) fun r ↦
    (judgeθ P θ r.2 r.1).toQuantumAt (mixImpl .judge _)

variable [Fintype J] [SampleableType Par] [SampleableType Val]

variable (ch) in
/-- The mixed CPRE game at the state `(P, s)`. -/
noncomputable def gameAt {Q St S0 F : Type} {R : OracleSpec.{0, 0} Q} (P : Par) (s : J → Val)
    (pre : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : S0 → St) (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : S0 → F → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val)) :
    QComp (MixSpec Caller) (QReg.of Unit) (QReg.of Unit) Bool :=
  QuantumComp₂.bind (mixNormal ((cpre romWorld ch C).answer (P, s)) pre adv st0 σ post)
    fun r ↦ ((cpre romWorld ch C).judge (P, s) r.2 r.1).toQuantumAt (mixImpl .judge _)

/-- The challenger's samplers at a table holding `θ` at the honest cells are those of `ansθ`. -/
theorem simulateQ_answer (hlen : StepLen ch) {H : romWorld.Tab} {P : Par}
    {θ : (s : CSrc ch) → CD ch s} (hH : ∀ p, H (cellOf P θ p) = θ (.inr p))
    (q : CpreQuery J Tw Fn Msg) :
    simulateQ (romWorld.eager H) ((cpre romWorld ch C).answer (P, fun j ↦ cval θ j 0) q) =
      simulateQ (romWorld.eager H) (ansθ C P θ q) := by
  cases q with
  | value j μ =>
    change simulateQ (romWorld.eager H) (ch.walk romWorld P j 0 (min μ (ch.len j)) (cval θ j 0))
      = simulateQ (romWorld.eager H) (pure (cval θ j (min μ (ch.len j))))
    rw [simulateQ_walk, simulateQ_pure]
    have h := walkH_honest hlen hH j (min μ (ch.len j)) 0 (by omega)
    rw [Nat.zero_add] at h
    exact congrArg pure h
  | eval l t m => rfl
  | reveal => rfl

/-- The decision's sampler at a table holding `θ` at the honest cells is that of `judgeθ`. -/
theorem simulateQ_judge (hlen : StepLen ch) {H : romWorld.Tab} {P : Par}
    {θ : (s : CSrc ch) → CD ch s} (hH : ∀ p, H (cellOf P θ p) = θ (.inr p))
    (log : QueryLog (CpreSpec Par Tw J Val Fn Msg Out)) (out : J × ℕ × Val) :
    simulateQ (romWorld.eager H) ((cpre romWorld ch C).judge (P, fun j ↦ cval θ j 0) log out) =
      simulateQ (romWorld.eager H) (judgeθ P θ log out) := by
  obtain ⟨j, μ, z⟩ := out
  have hc : ∀ ν, ν ≤ ch.len j → walkH ch H P j 0 ν (cval θ j 0) = cval θ j ν := fun ν h ↦ by
    have := walkH_honest hlen hH j ν 0 (by omega)
    rwa [Nat.zero_add] at this
  have hL : simulateQ (romWorld.eager H)
      ((cpre romWorld ch C).judge (P, fun j ↦ cval θ j 0) log (j, μ, z)) =
      pure (holds (CpreValid ch log ∧ μ < ch.len j ∧
        walkH ch H P j μ (ch.len j - μ) z = walkH ch H P j 0 (ch.len j) (cval θ j 0) ∧
        (z ≠ walkH ch H P j 0 μ (cval θ j 0) ∨ ¬ OpenedAtOrBelow log j μ))) := by
    simp only [cpre, simulateQ_bind, simulateQ_walk, pure_bind, simulateQ_pure]
  have hR : simulateQ (romWorld.eager H) (judgeθ P θ log (j, μ, z)) =
      pure (holds (CpreValid ch log ∧ μ < ch.len j ∧
        walkH ch H P j μ (ch.len j - μ) z = cval θ j (ch.len j) ∧
        (OpenedAtOrBelow log j μ → z ≠ cval θ j μ))) := by
    simp only [judgeθ, simulateQ_map, simulateQ_walk, map_pure]
  rw [hL, hR, hc _ le_rfl]
  refine congrArg pure (congrArg holds (propext (and_congr_right fun _ ↦ ⟨?_, ?_⟩)))
  · rintro ⟨hμ, h1, h2⟩
    rw [hc μ hμ.le] at h2
    exact ⟨hμ, h1, fun hO ↦ h2.resolve_right (not_not.2 hO)⟩
  · rintro ⟨hμ, h1, h2⟩
    rw [hc μ hμ.le]
    by_cases hO : OpenedAtOrBelow log j μ
    · exact ⟨hμ, h1, Or.inl (h2 hO)⟩
    · exact ⟨hμ, h1, Or.inr hO⟩

/-- **The game and `gameθ` win alike at a table holding `θ` at the honest cells.** -/
theorem probAt_point (hlen : StepLen ch) {H : romWorld.Tab} {P : Par}
    {θ : (s : CSrc ch) → CD ch s} (hH : ∀ p, H (cellOf P θ p) = θ (.inr p))
    {Q St S0 F : Type} {R : OracleSpec.{0, 0} Q}
    (pre : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : S0 → St) (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : S0 → F → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val)) :
    romWorld.probAt H (romRun (gameAt ch C P (fun j ↦ cval θ j 0) pre adv st0 σ post)) =
      romWorld.probAt H (romRun (gameθ C P θ pre adv st0 σ post)) := by
  refine probAt_eq_of_run₂ romWorld H ?_
  rw [gameAt, gameθ, romRun_bind, romRun_bind]
  have hlog : logImpl H ((cpre romWorld ch C).answer (P, fun j ↦ cval θ j 0)) =
      logImpl H (ansθ C P θ) := by
    funext t
    rcases t with t | q'
    · rfl
    · funext log
      simp only [logImpl, simulateQ_answer C hlen hH q']
  refine run₂_bind_congr ?_ fun r ↦ ?_
  · rw [← run₂_romRun_mixNormal, ← run₂_romRun_mixNormal]
    have hK : hKernel H ((cpre romWorld ch C).answer (P, fun j ↦ cval θ j 0)) σ =
        hKernel H (ansθ C P θ) σ := by
      funext p q
      simp only [hKernel, hlog]
    simp only [slNormal, hlog, hK]
  · have h₁ := classicalOn_romRun_toQuantumAt (H := H) .judge (QReg.of Unit)
      ((cpre romWorld ch C).judge (P, fun j ↦ cval θ j 0) r.2 r.1)
    have h₂ := classicalOn_romRun_toQuantumAt (H := H) .judge (QReg.of Unit)
      (judgeθ P θ r.2 r.1)
    rw [simulateQ_judge C hlen hH] at h₁
    exact run₂_eq_of_classicalOn h₁ h₂

end gameθ

/-! ## The average over the table -/

section avg

variable [Fintype Par] [SampleableType Par] [Fintype Val] [SampleableType Val] [Fintype J]
  [DecidableEq J] (C : TwColl Par Tw Fn Msg Out)

theorem toQuantumAt_bind' {spec : QuantumOracleSpec.{0, 0}} {B : QReg} {α β : Type}
    (impl : QueryImpl romWorld.Oracles (QComp spec B B)) (x : OracleComp romWorld.Oracles α)
    (f : α → OracleComp romWorld.Oracles β) :
    (x >>= f).toQuantumAt impl = (x.toQuantumAt impl).bind fun a ↦ (f a).toQuantumAt impl := by
  simp only [OracleComp.toQuantumAt, simulateQ_bind]
  rfl

/-- An average written as a normalized sum. -/
theorem sum_inv_mul_eq_uavg {α : Type} [Fintype α] (f : α → ℝ≥0∞) :
    ∑ a, (Fintype.card α : ℝ≥0∞)⁻¹ * f a = uavg f := by
  rw [uavg, Finset.mul_sum]

/-- **The game at a fixed table, averaged over the challenger's setup.** -/
theorem probAt_cpre_slRed_eq {Q St S0 F : Type} {R : OracleSpec.{0, 0} Q}
    (pre : Unit → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : Unit → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : Unit → S0 → St) (σ : Unit → HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : Unit → S0 → F → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val)) (H : romWorld.Tab) :
    romWorld.probAt H ((cpre romWorld ch C).game fun p ↦
        slRed romWorld (pre p) (adv p) (st0 p) (σ p) (post p)) =
      uavg fun P : Par ↦ uavg fun s : J → Val ↦
        romWorld.probAt H
          (romRun (gameAt ch C P s (pre ()) (adv ()) (st0 ()) (σ ()) (post ()))) := by
  rw [probAt_game_slRed_eq]
  have e : mixGame (cpre romWorld ch C) pre adv st0 σ post =
      ((sample romWorld Par).toQuantumAt (mixImpl .setup _)).bind fun P ↦
        ((sample romWorld (J → Val)).toQuantumAt (mixImpl .setup _)).bind fun s ↦
          gameAt ch C P s (pre ()) (adv ()) (st0 ()) (σ ()) (post ()) := by
    rw [mixGame]
    change ((sample romWorld Par >>= fun P ↦ sample romWorld (J → Val) >>= fun s ↦
      pure (P, s)).toQuantumAt (mixImpl .setup _)).bind (fun s : Par × (J → Val) ↦
        gameAt ch C s.1 s.2 (pre ()) (adv ()) (st0 ()) (σ ()) (post ())) = _
    rw [toQuantumAt_bind', QuantumComp₂.bind_assoc]
    refine congrArg _ (funext fun P ↦ ?_)
    rw [toQuantumAt_bind', QuantumComp₂.bind_assoc]
    refine congrArg _ (funext fun s ↦ ?_)
    rw [toQuantumAt_pure, QuantumComp₂.pure_bind]
  rw [e, romRun_bind,
    probAt_bind_classicalOn romWorld H (classicalOn_romRun_toQuantumAt .setup _ _),
    tsum_sample_eq_uavg romWorld_coinsFair H]
  refine congrArg uavg (funext fun P ↦ ?_)
  rw [romRun_bind, probAt_bind_classicalOn romWorld H (classicalOn_romRun_toQuantumAt .setup _ _),
    tsum_sample_eq_uavg romWorld_coinsFair H]

/-- **The QROM CPRE game of a straight-line reduction as runtime 1's reads**: the average over
the parameter, the starts and the honest outputs of runtime 1, the honest cells hardwired, running
the read program of `gameθ`. -/
theorem probAvg_cpre_slRed_eq_reads (hlen : StepLen ch)
    (hinj : ∀ P θ, Function.Injective (cellOf (ch := ch) P θ)) {Q St S0 F : Type}
    {R : OracleSpec.{0, 0} Q}
    (pre : Unit → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : Unit → S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) F)
    (st0 : Unit → S0 → St) (σ : Unit → HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : Unit → S0 → F → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val)) :
    romWorld.probAvg ((cpre romWorld ch C).game fun p ↦
        slRed romWorld (pre p) (adv p) (st0 p) (σ p) (post p)) =
      uavg fun P : Par ↦ uavg fun s : J → Val ↦ uavg fun v : CPos ch → HashOutput ↦
        (spongeHardwiredReadRuntime HashOutput HashDomain ((lazyT P s (hinj P)).hwOf v)
          ()).evalDistMap .instruments (toReads (keepAll Caller Unit)
            (gameθ C P (thetaOf s v) (pre ()) (adv ()) (st0 ()) (σ ()) (post ())))
          (SubState.basis ()) (fun p ↦ p.2.2) {true} := by
  rw [OracleWorld.probAvg_eq_sum]
  simp only [probAt_cpre_slRed_eq C pre adv st0 σ post]
  rw [sum_inv_mul_eq_uavg, uavg_comm]
  refine congrArg uavg (funext fun P ↦ ?_)
  rw [uavg_comm]
  refine congrArg uavg (funext fun s ↦ ?_)
  have h := uavg_tab_eq_fill (lazyT P s (hinj P)) fun _ H ↦
    romWorld.probAt H (romRun (gameAt ch C P s (pre ()) (adv ()) (st0 ()) (σ ()) (post ())))
  refine h.trans (congrArg uavg (funext fun v ↦ ?_))
  rw [readLaw_eq_avg]
  have hG := sum_inv_card_mul_fst (A := HashDomain → HashOutput)
    (B := (HashOutput → HashDomain) × (HashOutput → HashDomain)) fun H ↦
      romWorld.probAt ((lazyT P s (hinj P)).fill v v H)
        (romRun (gameθ C P (thetaOf s v) (pre ()) (adv ()) (st0 ()) (σ ()) (post ())))
  refine Eq.trans ?_ (hG.symm.trans rfl)
  rw [sum_inv_mul_eq_uavg]
  refine congrArg uavg (funext fun H ↦ ?_)
  exact probAt_point C hlen (P := P) (θ := thetaOf s v)
    (fun p ↦ lazyT_fill_cell P s (hinj P) v H p) _ _ _ _ _

end avg

end Quantum.StdModel.Qrom.CpreQ

end
