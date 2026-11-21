module

public import Quantum.StdModel.Qrom.CpreLaw
public import Quantum.StdModel.Qrom.Moded

@[expose] public section

/-!
# The CPRE game's runtime-2 event

Runtime 2 (`runtimeR`, with the record ports) on the realized template `realizeT θ (cpreT ..)`
(`CpreTmpl`), at the parameter `P` and the hidden values `θ`.

* **The event** (`BadC P θ`): a recorded or hardwired cell `z` whose value lies in its target
  (`CellTargetBad (tgtC P θ)`), or a memory record `(z, y)` of the decision's walk with `y` in the
  target of `z` (`WonM`). The target of `z` (`Fib`): the values `y` with `trunc y` the honest value
  at `ν + 1` when `z` is the step cell (`cellAt`) of chain `j` at `ν < len j` of an input `x` that
  is bad (`BadIn`): `x` is not the honest value at `ν`, or its source is not in the memory label.
* **The label** (`Covered`, `LabInv`): every coordinate of the memory label was revealed by an entry
  of the transcript; on a valid transcript a revealed source below the end is an opening at or
  below it (`opened_of_covered`).
* **The walk** (`walk_live`): a live run of the decision's walk (each read recorded in the memory)
  that ends at the honest end from a bad start has a record in the target of its cell.
* **The bound** (`p2_cpre_le`): a win puts the run in the event (`p2_le_eventWeight`); sponge
  calls and reads of step cells cost `√(gradeEta F)` each, programs of revealed honest cells,
  records and other reads nothing (`tsum_potential_step_cpre`), so `p₂ ≤ N² · gradeEta F` for a
  game of `N` charged calls.
-/

open IPFunctor OracleComp OracleSpec Matrix
open scoped ENNReal Kronecker ComplexOrder

universe u v

set_option synthInstance.maxSize 2000

namespace Quantum.StdModel.Qrom.CpreQ

open Quantum Quantum.Qrom Props HashSig
open Quantum.Sponge (keepMem Hw HwReg)

variable {Par Tw J Val Fn Out : Type} {Msg : Fn → Type} {ch : Chains Par Tw J Val}

/-! ## Step cells, bad inputs and targets -/

section events

variable (ch) in
/-- **The step cell** of the input `x` at position `ν` of chain `j`. -/
def cellAt (P : Par) (j : J) (ν : ℕ) (x : Val) : HashDomain :=
  (encodeInput (ch.step.layout () P (ch.tweak j ν) x)).getD 0

theorem cellOf_eq_cellAt (P : Par) (θ : (s : CSrc ch) → CD ch s) (p : CPos ch) :
    cellOf P θ p = cellAt ch P p.1 p.2 (cval θ p.1 p.2) :=
  rfl

variable (ch) in
/-- **Step cells are injective** at `P`: a step cell names its chain, position and input. -/
def CellInj (P : Par) : Prop :=
  ∀ j ν x j' ν' x', ν < ch.len j → ν' < ch.len j' → cellAt ch P j ν x = cellAt ch P j' ν' x' →
    j = j' ∧ ν = ν' ∧ x = x'

variable (ch) in
/-- A cell is a step cell at `P`. -/
def StepCell (P : Par) (z : HashDomain) : Prop :=
  ∃ j ν x, ν < ch.len j ∧ cellAt ch P j ν x = z

/-- **A bad input** at `ν` of chain `j`: not the honest value, or its source is not in the label
`L`. -/
def BadIn (θ : (s : CSrc ch) → CD ch s) (L : Finset (CSrc ch)) (j : J) (ν : ℕ) (x : Val) :
    Prop :=
  x ≠ cval θ j ν ∨ ∀ h : ν ≤ ch.len j, srcOf j ν h ∉ L

/-- **The target of a cell**: the values whose truncation is the honest value above a step whose
input is bad. -/
def Fib (P : Par) (θ : (s : CSrc ch) → CD ch s) (L : Finset (CSrc ch)) (z : HashDomain) :
    Set HashOutput :=
  {y | ∃ j ν x, ν < ch.len j ∧ cellAt ch P j ν x = z ∧ BadIn θ L j ν x ∧
    ch.step.trunc y = cval θ j (ν + 1)}

/-- The targets of the cell event, read from the memory label. -/
def tgtC (P : Par) (θ : (s : CSrc ch) → CD ch s) :
    Hw HashOutput HashDomain → Finset (CSrc ch) × JMem → HashDomain → Set HashOutput :=
  fun _ m z ↦ Fib P θ m.1 z

/-- **A won memory**: a record of the walk in the target of its cell. -/
def WonM (P : Par) (θ : (s : CSrc ch) → CD ch s) (m : Finset (CSrc ch) × JMem) : Prop :=
  ∃ zy ∈ m.2, zy.2 ∈ Fib P θ m.1 zy.1

/-- **The event of the CPRE game**: a cell in its target, or a won memory. -/
def BadC (P : Par) (θ : (s : CSrc ch) → CD ch s) :
    Set (HwReg HashOutput HashDomain (Finset (CSrc ch) × JMem)) :=
  Quantum.Qrom.CellTargetBad (tgtC P θ) ∪ {s | WonM P θ s.2.2}

noncomputable instance instDecidablePredBadC (P : Par) (θ : (s : CSrc ch) → CD ch s) :
    DecidablePred (· ∈ BadC P θ) :=
  fun _ ↦ Classical.propDecidable _

theorem fib_subset {P : Par} (hinj : CellInj ch P) {θ : (s : CSrc ch) → CD ch s}
    {L : Finset (CSrc ch)} {j : J} {ν : ℕ} {x : Val} (hν : ν < ch.len j) :
    Fib P θ L (cellAt ch P j ν x) ⊆ {y | ch.step.trunc y = cval θ j (ν + 1)} := by
  rintro y ⟨j', ν', x', hν', hz, -, hy⟩
  obtain ⟨rfl, rfl, rfl⟩ := hinj j' ν' x' j ν x hν' hν hz
  exact hy

/-- **A target has at most `F` values** when the truncation's fibers do: any predicate inside a
target has at most `F` values. -/
theorem card_fib_le [DecidableEq Val] {P : Par} (hinj : CellInj ch P)
    (θ : (s : CSrc ch) → CD ch s) (L : Finset (CSrc ch)) (z : HashDomain) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ ch.step.trunc y = o).card ≤ F)
    (p : HashOutput → Prop) [DecidablePred p] (hp : ∀ y, p y → y ∈ Fib P θ L z) :
    (Finset.univ.filter p).card ≤ F := by
  by_cases h : ∃ j ν x, ν < ch.len j ∧ cellAt ch P j ν x = z
  · obtain ⟨j, ν, x, hν, rfl⟩ := h
    refine (Finset.card_le_card fun y hy ↦ ?_).trans (hF (cval θ j (ν + 1)))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact fib_subset hinj hν (hp y hy)
  · rw [Finset.filter_false_of_mem fun y _ hy ↦ ?_]
    · exact Nat.zero_le _
    obtain ⟨j, ν, x, hν, hz, _⟩ := hp y hy
    exact h ⟨j, ν, x, hν, hz⟩

/-- **An honest cell whose source is in the label has no target.** -/
theorem fib_cellOf_eq_empty {P : Par} (hinj : CellInj ch P) (θ : (s : CSrc ch) → CD ch s)
    {L : Finset (CSrc ch)} (p : CPos ch) (hL : srcOf p.1 p.2 p.2.isLt.le ∈ L) :
    Fib P θ L (cellOf P θ p) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun y ⟨j, ν, x, hν, hz, hb, _⟩ ↦ ?_
  obtain ⟨rfl, rfl, rfl⟩ := hinj j ν x p.1 p.2 _ hν p.2.isLt hz
  rcases hb with hb | hb
  · exact hb rfl
  · exact hb p.2.isLt.le hL

/-- A cell that is no step cell has no target. -/
theorem fib_eq_empty_of_not_stepCell {P : Par} (θ : (s : CSrc ch) → CD ch s)
    (L : Finset (CSrc ch)) {z : HashDomain} (hz : ¬StepCell ch P z) : Fib P θ L z = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨j, ν, x, hν, h, _⟩ ↦ hz ⟨j, ν, x, hν, h⟩

end events

/-! ## The label and the transcript -/

section label

variable [Fintype J] [DecidableEq J]

omit [Fintype J] [DecidableEq J] in
theorem srcOf_inj {j j' : J} {ν ν' : ℕ} (h : ν ≤ ch.len j) (h' : ν' ≤ ch.len j')
    (e : srcOf (ch := ch) j ν h = srcOf j' ν' h') : j = j' ∧ ν = ν' := by
  cases ν with
  | zero =>
    cases ν' with
    | zero => exact ⟨Sum.inl.inj e, rfl⟩
    | succ ν' => exact absurd e (by simp [srcOf])
  | succ ν =>
    cases ν' with
    | zero => exact absurd e (by simp [srcOf])
    | succ ν' =>
      simp only [srcOf, Sum.inr.injEq, Sigma.mk.inj_iff] at e
      obtain ⟨rfl, e⟩ := e
      exact ⟨rfl, by rw [Fin.mk.inj_iff.mp (eq_of_heq e)]⟩

/-- A source in an opening's coordinates is at or above the opening. -/
theorem eq_le_of_srcOf_mem_openSet {j j' : J} {ν μ : ℕ} (h : ν ≤ ch.len j)
    (hs : srcOf (ch := ch) j ν h ∈ openSet ch j' μ) : j = j' ∧ μ ≤ ν := by
  simp only [openSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and] at hs
  rcases hs with hs | ⟨p, ⟨rfl, hp⟩, hpe⟩
  · split_ifs at hs with hμ
    · obtain ⟨rfl, rfl⟩ := srcOf_inj h hμ (Finset.mem_singleton.mp hs)
      exact ⟨rfl, le_rfl⟩
    · exact absurd hs (Finset.notMem_empty _)
  · cases ν with
    | zero => exact absurd hpe (by simp [srcOf])
    | succ ν =>
      simp only [srcOf, Sum.inr.injEq] at hpe
      subst hpe
      exact ⟨rfl, by simp at hp; omega⟩

/-- **The coordinates a transcript entry reveals**: a value query its opening's (or the end's), an
evaluation at a chain step tweak everything (such a transcript loses), `reveal` nothing. -/
def RevBy : CpreQuery J Tw Fn Msg → CSrc ch → Prop
  | .value j μ, s => s ∈ (if μ < ch.len j then openSet ch j μ else endSet ch j)
  | .eval _ t _, _ => ch.IsStepTweak t
  | .reveal, _ => False

/-- A coordinate revealed by an entry of the transcript. -/
def Covered (log : QueryLog (CpreSpec Par Tw J Val Fn Msg Out)) (s : CSrc ch) : Prop :=
  ∃ e ∈ log, RevBy e.1 s

/-- **The label invariant**: every coordinate of the label is revealed by the transcript. -/
def LabInv (log : QueryLog (CpreSpec Par Tw J Val Fn Msg Out)) (L : Finset (CSrc ch)) : Prop :=
  ∀ s ∈ L, Covered log s

theorem covered_append {log : QueryLog (CpreSpec Par Tw J Val Fn Msg Out)} {s : CSrc ch}
    (l : QueryLog (CpreSpec Par Tw J Val Fn Msg Out)) (h : Covered log s) :
    Covered (log ++ l) s := by
  obtain ⟨e, he, hs⟩ := h
  exact ⟨e, List.mem_append_left _ he, hs⟩

theorem labInv_append {log : QueryLog (CpreSpec Par Tw J Val Fn Msg Out)}
    {L : Finset (CSrc ch)} (l : QueryLog (CpreSpec Par Tw J Val Fn Msg Out))
    (h : LabInv log L) : LabInv (log ++ l) L :=
  fun s hs ↦ covered_append l (h s hs)

/-- A new entry covers what it reveals. -/
theorem labInv_append_entry {log : QueryLog (CpreSpec Par Tw J Val Fn Msg Out)}
    {L : Finset (CSrc ch)} (q : CpreQuery J Tw Fn Msg) (a : CpreQuery.Resp Par Val Out q)
    {T : Finset (CSrc ch)} (h : LabInv log L) (hT : ∀ s ∈ T, RevBy (ch := ch) q s) :
    LabInv (log ++ [⟨q, a⟩]) (L ∪ T) := by
  intro s hs
  rcases Finset.mem_union.mp hs with hs | hs
  · exact covered_append _ (h s hs)
  · exact ⟨⟨q, a⟩, List.mem_append_right _ (List.mem_singleton_self _), hT s hs⟩

/-- **On a valid transcript a revealed source below the end is an opening at or below it.** -/
theorem opened_of_covered {log : QueryLog (CpreSpec Par Tw J Val Fn Msg Out)}
    (hv : CpreValid ch log) {j : J} {ν : ℕ} (h : ν ≤ ch.len j) (hν : ν < ch.len j)
    (hc : Covered log (srcOf (ch := ch) j ν h)) : OpenedAtOrBelow log j ν := by
  obtain ⟨⟨q, a⟩, he, hs⟩ := hc
  cases q with
  | value j' μ =>
    change srcOf j ν h ∈ (if μ < ch.len j' then openSet ch j' μ else endSet ch j') at hs
    split_ifs at hs with hμ
    · obtain ⟨rfl, hle⟩ := eq_le_of_srcOf_mem_openSet h hs
      exact ⟨μ, hle, List.mem_filterMap.mpr ⟨⟨.value j μ, a⟩, he, rfl⟩⟩
    · obtain ⟨rfl, rfl⟩ := srcOf_inj h le_rfl (Finset.mem_singleton.mp hs)
      exact absurd hν (lt_irrefl _)
  | eval l t m =>
    exact absurd (hs : ch.IsStepTweak t)
      (hv.1 t (List.mem_filterMap.mpr ⟨⟨.eval l t m, a⟩, he, rfl⟩))
  | reveal => exact hs.elim

end label

/-! ## The memory modes -/

section modes

open Quantum.Xmss.Assembly (ModedP modeCmdOk modeCmdNx tmplSpec recHwSpec realizeT tmplLens
  readLift readLens liftRead)
open Quantum.Sponge (HwRead HwProg)
open Quantum.Xmss.Hybrid (restrictTo)

variable (ch) in
/-- The memory of runtime 2 on the template: the label and the walk's records. -/
abbrev CMem : Type := Finset (CSrc ch) × JMem

/-- The empty log: the modes record no outcome. -/
def rl0 : CMem ch → HashDomain → Option HashOutput := fun _ _ ↦ none

/-- The read policies on the whole memory: the label kept, the walk's records by `updC`. -/
def updM : Caller → HashDomain → CMem ch → Option HashOutput → CMem ch :=
  fun c z m o ↦ (m.1, updC c z m.2 o)

theorem stepRd_rl0 (u : CMem ch → Option HashOutput → CMem ch) (z : HashDomain) (m : CMem ch)
    (v : HashOutput) : stepRd (rl0 (ch := ch)) u z (some m) v = some (u m (some v)) := by
  simp [stepRd, rl0]

/-- **The walk's live run**: it keeps the label and only adds records; ending at the honest end
from a bad start, it records a value in the target of its cell (for any label `L₁` holding the
end's source). -/
theorem walk_live (hlen : StepLen ch) (P : Par)
    (θ : (s : CSrc ch) → CD ch s) (j : J) (L₁ : Finset (CSrc ch))
    (hend : srcOf (ch := ch) j (ch.len j) le_rfl ∈ L₁) :
    ∀ n ν (x : Val) (m : CMem ch) (e : Val) (μ' : Option (CMem ch)),
      LiveRun rl0 (updM .judge) (ch.walk romWorld P j ν n x) (some m) e μ' →
      ν + n ≤ ch.len j → ∃ J', μ' = some (m.1, J') ∧ m.2 ⊆ J' ∧
        (ν + n = ch.len j → e = cval θ j (ch.len j) → BadIn θ L₁ j ν x →
          ∃ zy ∈ J', zy.2 ∈ Fib P θ L₁ zy.1) := by
  intro n
  induction n with
  | zero =>
    intro ν x m e μ' h _
    simp only [LiveRun, Chains.walk, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨m.2, rfl, subset_rfl, fun hn he hb ↦ ?_⟩
    rw [Nat.add_zero] at hn
    subst hn
    rcases hb with hb | hb
    · exact absurd he hb
    · exact absurd hend (hb le_rfl)
  | succ n ih =>
    intro ν x m e μ' h hle
    have hν : ν < ch.len j := by omega
    have hz : encodeInput (ch.step.layout () P (ch.tweak j ν) x) = some (cellAt ch P j ν x) :=
      Quantum.StdModel.Qrom.encodeInput_eq_cellOf (hlen P j ν x hν)
    have hw : ch.walk romWorld P j ν (n + 1) x =
        liftM (romWorld.Oracles.query (.inr (cellAt ch P j ν x))) >>= fun v ↦
          ch.walk romWorld P j (ν + 1) n (ch.step.trunc v) := by
      simp only [Chains.walk, TwColl.eval]
      change (ch.step.trunc <$> hashQ (ch.step.layout () P (ch.tweak j ν) x)) >>= _ = _
      rw [hashQ_of_encodeInput_eq_some hz]
      simp only [map_eq_bind_pure_comp]
      rfl
    unfold LiveRun at h
    rw [hw, run_simulateQ_query_bind, mem_support_bind_iff] at h
    obtain ⟨p, hp, h⟩ := h
    change p ∈ support ((fun v ↦ (v, stepRd rl0 (updM .judge (cellAt ch P j ν x))
      (cellAt ch P j ν x) (some m) v)) <$>
        liftM (romWorld.Oracles.query (.inr (cellAt ch P j ν x)))) at hp
    rw [support_map] at hp
    obtain ⟨v, -, rfl⟩ := hp
    dsimp only at h
    rw [stepRd_rl0] at h
    obtain ⟨J', hJ', hsub, hwin⟩ := ih (ν + 1) _ _ e μ' h (by omega)
    have hzv : (cellAt ch P j ν x, v) ∈ J' := hsub (Finset.mem_insert_self _ _)
    refine ⟨J', hJ', fun a ha ↦ hsub (Finset.mem_insert_of_mem ha), fun hn he hb ↦ ?_⟩
    by_cases hb' : BadIn θ L₁ j (ν + 1) (ch.step.trunc v)
    · exact hwin (by omega) he hb'
    · simp only [BadIn, not_or, not_not, not_forall] at hb'
      exact ⟨_, hzv, j, ν, x, hν, rfl, hb, hb'.1⟩

/-- The mode after a read: dead on the empty outcome, else the memory moved by the policy. -/
def rdNx {M' : Type} : (c : HwRead HashOutput HashDomain M') → c.Result → M' → Option M'
  | .readH _ u, r, m => r.1.elim none fun v ↦ some (u m (some v))
  | .readK _ u, r, m => some (u m r.1)
  | .readK' _ u, r, m => some (u m r.1)

/-- The reads of the realized game: cell reads keeping the memory, or recording the read. -/
def ReadShape : HwRead HashOutput HashDomain (CMem ch) → Prop
  | .readH z u => u = (fun m o ↦ (m.1, keepMem m.2 o)) ∨ u = (fun m o ↦ (m.1, recU z m.2 o))
  | .readK _ _ => False
  | .readK' _ _ => False

theorem readShape_liftRead (c : Caller) (z : HashDomain) :
    ReadShape (ch := ch) (liftRead (.readH z (updC c z))) := by
  cases c
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

variable [DecidableEq J] [Inhabited Val]

variable (P : Par) (θ : (s : CSrc ch) → CD ch s)

variable (ch) in
/-- The ports of the realized game. -/
abbrev RSpec : QuantumOracleSpec.{0, 0} :=
  recHwSpec HashOutput HashDomain (CSrc ch) JMem

/-- **The calls a live mode allows on the realized game**: sponge and record calls, reads of the
game's shape, and programs of honest cells whose source is in the label. -/
def okZ : Option (CMem ch) → (RSpec ch).Port → Prop
  | none, _ => True
  | some _, .inl (.inl (.inl _)) => True
  | some _, .inl (.inl (.inr c)) => ReadShape c
  | some m, .inl (.inr c) => ∃ q : CPos ch, c = .programH (cellOf P θ q) (θ (.inr q)) ∧
      srcOf q.1 q.2 q.2.isLt.le ∈ m.1
  | some _, .inr _ => True

/-- **The modes of the realized game**: the memory, moved by the reads and records. -/
def nxZ : Option (CMem ch) → (i : (RSpec ch).Port) → (RSpec ch).Result i → Option (CMem ch)
  | none, _, _ => none
  | some m, .inl (.inl (.inl _)), _ => some m
  | some m, .inl (.inl (.inr c)), r => rdNx c r m
  | some m, .inl (.inr _), _ => some m
  | some m, .inr T, _ => some (m.1 ∪ T, m.2)

/-- The calls a live mode allows on the template. -/
def okT : Option (CMem ch) → (TSpec ch).Port → Prop
  | none, _ => True
  | some _, .inl (.inl (.inl _)) => True
  | some _, .inl (.inl (.inr c)) => ReadShape c.1
  | some m, .inl (.inr p) => ∃ q : CPos ch, p.1 = progP P q ∧ progNeed q ⊆ m.1
  | some _, .inr _ => True

/-- The modes of the template: a reveal of other values than `θ`'s kills the mode. -/
noncomputable def nxT : Option (CMem ch) → (i : (TSpec ch).Port) → (TSpec ch).Result i →
    Option (CMem ch)
  | none, _, _ => none
  | some m, .inl (.inl (.inl _)), _ => some m
  | some m, .inl (.inl (.inr c)), r => rdNx c.1 r m
  | some m, .inl (.inr _), _ => some m
  | some m, .inr T, r => @ite _ (r.1 = restrictTo T θ) (Classical.propDecidable _)
      (some (m.1 ∪ T, m.2)) none

/-- **Realizing keeps the modes.** -/
theorem modedP_realizeT_cpre {L : LocalSig.{u, v}} {Ω : QReg → Type*}
    {fin : (Σ u, Ω u) → Option (CMem ch) → Prop} {A : QReg}
    (y : QuantumComp L (TSpec ch) Ω A) {μ : Option (CMem ch)}
    (hy : ModedP (okT P) (nxT θ) fin μ y) :
    ModedP (okZ P θ) (nxZ (ch := ch)) fin μ (realizeT θ y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedP _ _ _ μ (IFreeM.mapLens (tmplLens θ) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨((i | c) | ⟨p, hp⟩) | T, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨by rcases μ with _ | m <;> trivial, fun b ↦ ?_⟩
      have h := ih _ (hy.2 b)
      rcases μ with _ | m <;> exact h
    · refine ⟨by rcases μ with _ | m <;> exact hy.1, fun b ↦ ?_⟩
      have h := ih _ (hy.2 b)
      rcases μ with _ | m <;> exact h
    · refine ⟨?_, fun b ↦ ?_⟩
      · rcases μ with _ | m
        · trivial
        · obtain ⟨q, hq, hn⟩ := hy.1
          refine ⟨q, ?_, hn (by simp [progNeed])⟩
          change p.realize θ = _
          rw [show p = progP P q from hq, realize_progP]
      · have h := ih _ (hy.2 (by cases p <;> exact b))
        rcases μ with _ | m <;> cases p <;> exact h
    · refine ⟨by rcases μ with _ | m <;> trivial, fun b ↦ ?_⟩
      have h := ih _ (hy.2 (ULift.up (restrictTo T θ, b.down)))
      rcases μ with _ | m
      · exact h
      · have e : nxT θ (some m) (.inr T) (restrictTo T θ, b.down) = some (m.1 ∪ T, m.2) := by
          simp [nxT]
        change ModedP _ _ _ (nxT θ (some m) (.inr T) (restrictTo T θ, b.down)) _ at h
        rw [e] at h
        exact h

end modes

/-! ## The template game is moded -/

section tmpl

open Quantum.Xmss.Assembly (ModedP modeCmdOk modeCmdNx modedP_bind modedP₂_bind modedP_map
  modedP_act readLift readLiftQ readLens revealThen progThen RevealVals)
open Quantum.Xmss.Hybrid (restrictTo)

variable [Fintype J] [DecidableEq J] [Inhabited Val] (P : Par) (θ : (s : CSrc ch) → CD ch s)

/-- The mode invariant before the decision: the label is revealed by the transcript. -/
def Inv0 (log : QueryLog (CQ Par Tw J Val Fn Msg Out)) (μ : Option (CMem ch)) : Prop :=
  ∀ m, μ = some m → LabInv log m.1

omit [Inhabited Val] in
theorem inv0_none (log : QueryLog (CQ Par Tw J Val Fn Msg Out)) : Inv0 (ch := ch) log none :=
  fun _ h ↦ by cases h

omit [Fintype J] in
/-- From the dead mode every template is moded. -/
theorem modedP_none {Ω : QReg → Type} {fin : (Σ u, Ω u) → Option (CMem ch) → Prop}
    (hfin : ∀ p, fin p none) {A : QReg} (y : QuantumComp LocalSig.instruments.{0} (TSpec ch) Ω A) :
    ModedP (okT P) (nxT θ) fin none y :=
  modedP_of_dead none (fun _ ↦ trivial) (fun _ _ ↦ rfl) hfin y

omit [Fintype J] [DecidableEq J] [Inhabited Val] in
/-- A tagged call of a caller other than the decision keeps the mode. -/
theorem nxM_keep (c : Caller) (hc : c ≠ .judge) (μ : Option (CMem ch))
    (t : romWorld.Oracles.Domain) (y : romWorld.Oracles.Range t) :
    nxM updM rl0 μ (.call (c, t)) y = μ := by
  rcases t with n | z
  · rfl
  · rcases μ with _ | m
    · rfl
    · refine (stepRd_rl0 (ch := ch) (updM c z) z m y).trans ?_
      cases c
      · rfl
      · rfl
      · exact absurd rfl hc
      · rfl

omit [Fintype J] [DecidableEq J] [Inhabited Val] in
theorem modedP_toQuantumAt_keep (c : Caller) (hc : c ≠ .judge) (B : QReg) {α : Type}
    (oa : OracleComp romWorld.Oracles α) (μ : Option (CMem ch)) :
    ModedP okM (nxM updM rl0) (fun _ μ' ↦ μ' = μ) μ (oa.toQuantumAt (mixImpl c B)) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact rfl
  | query_bind t k ih =>
    rw [toQuantumAt_query_bind]
    exact modedP₂_bind (F := fun _ μ' ↦ μ' = μ) (F' := fun _ μ' ↦ μ' = μ) _ _
      (modedP_mono (fun p μ' h ↦ h.trans (nxM_keep c hc μ t _)) _ _
        (modedP_mixImpl updM rl0 c B t μ)) fun y μ' h ↦ h ▸ ih y

/-- One step of a moded command tree: normalize the head, then split the command. -/
local macro "moded_step" : tactic => `(tactic| (
  (conv => arg 5; whnf);
  refine ⟨?_, fun _ ↦ ?_⟩))

omit [Fintype J] in
/-- **A mixed command by template reads** moves the mode as the mixed command, or kills it. -/
theorem modedP_readLens_cmd {A : QReg}
    (c : QuantumComp.Cmd LocalSig.instruments.{0} (MixSpec Caller) A) (μ : Option (CMem ch)) :
    ModedP (okT P) (nxT θ)
      (fun p μ' ↦ μ' = modeCmdNx (nxM updM rl0) c μ p.2.1 ∨ μ' = none) μ
      (IFreeM.mapLens (readLens (goodC (ch := ch))) (readSub (M := JMem) updC A c)) := by
  rcases c with o | ⟨p | ⟨tag, n | z⟩, E, ℓ⟩
  · moded_step
    · trivial
    · exact Or.inl rfl
  · moded_step
    · rcases μ with _ | m <;> trivial
    · rcases μ with _ | m <;> exact Or.inl rfl
  · moded_step
    · trivial
    moded_step
    · trivial
    exact Or.inl rfl
  · moded_step
    · trivial
    (conv => arg 5; whnf)
    refine ⟨?_, fun r ↦ ?_⟩
    · rcases μ with _ | m
      · trivial
      · exact readShape_liftRead tag z
    moded_step
    · trivial
    rcases μ with _ | m
    · exact Or.inr rfl
    obtain ⟨⟨_ | v, mb⟩⟩ := r
    · exact Or.inr rfl
    · exact Or.inl rfl

omit [Fintype J] in
/-- **Mixed programs by template reads are moded** as the mixed program. -/
theorem modedP_readLiftSub {Ω : QReg → Type} {fin : (Σ u, Ω u) → Option (CMem ch) → Prop}
    (hfin : ∀ p, fin p none) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (MixSpec Caller)) Ω A)
    (μ : Option (CMem ch)) (hx : ModedP okM (nxM updM rl0) fin μ x) :
    ModedP (okT P) (nxT θ) fin μ
      (IFreeM.mapLens (readLens (goodC (ch := ch))) (IFreeM.substitute (readSub updC) x)) := by
  rw [← IFreeM.substitute_toSubstitution, Quantum.Xmss.Assembly.substitute_substitute]
  refine modedP_substitute _ none (fun _ ↦ trivial) (fun _ _ ↦ rfl) (fun A c μ _ ↦ ?_) hfin x μ hx
  rw [IFreeM.substitute_toSubstitution]
  exact modedP_readLens_cmd P θ c μ

omit [Fintype J] in
theorem modedP_readLiftQ {B C' : QReg} {α : Type} (y : QComp (MixSpec Caller) B C' α)
    (F : α → Option (CMem ch) → Prop) (hF : ∀ a, F a none) (μ : Option (CMem ch))
    (hy : ModedP okM (nxM updM rl0) (fun p μ ↦ F p.2.2 μ) μ y) :
    ModedP (okT P) (nxT θ) (fun p μ ↦ F p.2.2 μ) μ (readLiftQ goodC (toReads updC y)) :=
  modedP_readLiftSub P θ (fun _ ↦ hF _) y μ hy

omit [Fintype J] in
/-- The challenger's computation by reads keeps the mode (or kills it). -/
theorem modedP_keepReads (B : QReg) {α : Type} (oa : OracleComp romWorld.Oracles α)
    {F : α → Option (CMem ch) → Prop} (μ : Option (CMem ch)) (hF : ∀ a, F a μ)
    (hFn : ∀ a, F a none) :
    ModedP (okT P) (nxT θ) (fun p μ ↦ F p.2.2 μ) μ (keepReads (ch := ch) B oa) := by
  refine modedP_mono (fun p μ' h ↦ ?_) _ _ (modedP_readLiftQ P θ _
    (fun _ μ' ↦ μ' = μ ∨ μ' = none) (fun _ ↦ Or.inr rfl) μ
    (modedP_mono (fun _ _ h ↦ Or.inl h) _ _ (modedP_toQuantumAt_keep .answer (by decide) B oa μ)))
  rcases h with rfl | rfl
  · exact hF _
  · exact hFn _

omit [Fintype J] in
theorem modedP_revealThen {B C' : QReg} {α : Type} (T : Finset (CSrc ch))
    (k : RevealVals (CD ch) T × CMem ch → QComp (TSpec ch) B C' α)
    {F : α → Option (CMem ch) → Prop} (μ : Option (CMem ch))
    (hk : ∀ r, ModedP (okT P) (nxT θ) (fun p μ ↦ F p.2.2 μ) (nxT θ μ (.inr T) r) (k r)) :
    ModedP (okT P) (nxT θ) (fun p μ ↦ F p.2.2 μ) μ (revealThen goodC T k) :=
  ⟨by rcases μ with _ | m <;> trivial, fun b ↦ modedP₂_bind
    (F := fun _ μ' ↦ μ' = nxT θ μ (.inr T) b.down) _ _
    (modedP_act (F := fun _ μ' ↦ μ' = nxT θ μ (.inr T) b.down) _ _ fun _ ↦ rfl)
    fun _ μ' h ↦ h ▸ hk b.down⟩

omit [Fintype J] in
theorem modedP_progThen {B C' : QReg} {α : Type} (q : CPos ch) (k : QComp (TSpec ch) B C' α)
    {F : α → Option (CMem ch) → Prop} (μ : Option (CMem ch))
    (hμ : ∀ m, μ = some m → progNeed q ⊆ m.1)
    (hk : ModedP (okT P) (nxT θ) (fun p μ ↦ F p.2.2 μ) μ k) :
    ModedP (okT P) (nxT θ) (fun p μ ↦ F p.2.2 μ) μ (progThen (progP P q) trivial k) := by
  have hok : okT P μ (.inl (.inr ⟨progP P q, trivial⟩)) := by
    rcases μ with _ | m
    · trivial
    · exact ⟨q, rfl, hμ m rfl⟩
  refine ⟨hok, fun b ↦ modedP₂_bind (F := fun _ μ' ↦ μ' = μ) _ _
    (modedP_act (F := fun _ μ' ↦ μ' = μ) _ _ fun _ ↦ by rcases μ with _ | m <;> rfl)
    fun _ μ' h ↦ h ▸ hk⟩

theorem modedP_progFrom (B : QReg) (j : J) (μ₀ : ℕ) (μ : Option (CMem ch))
    (hμ : ∀ m, μ = some m → openSet ch j μ₀ ⊆ m.1) :
    ∀ ν, μ₀ ≤ ν → ModedP (okT P) (nxT θ) (fun _ μ' ↦ μ' = μ) μ (progFrom P B j ν) := by
  intro ν
  induction h : ch.len j - ν generalizing ν with
  | zero =>
    intro _
    rw [progFrom, dite_eq_right (by omega)]
    exact rfl
  | succ n ih =>
    intro hle
    have hν : ν < ch.len j := by omega
    rw [progFrom, dite_eq_left hν]
    exact modedP_progThen P θ ⟨j, ⟨ν, hν⟩⟩ _ (F := fun _ μ' ↦ μ' = μ) μ
      (fun m hm ↦ (progNeed_subset_openSet hle hν).trans (hμ m hm))
      (ih (ν + 1) (by omega) (by omega))

theorem modedP_openT {α : Type} (B : QReg) (j : J) (μ₀ : ℕ)
    (k : RevealVals (CD ch) (openSet ch j μ₀) → QComp (TSpec ch) B B α)
    {F : α → Option (CMem ch) → Prop} (hF : ∀ a, F a none) (μ : Option (CMem ch))
    (hk : ∀ m, μ = some m → ModedP (okT P) (nxT θ) (fun p μ ↦ F p.2.2 μ)
      (some (m.1 ∪ openSet ch j μ₀, m.2)) (k (restrictTo _ θ))) :
    ModedP (okT P) (nxT θ) (fun p μ ↦ F p.2.2 μ) μ (openT P B j μ₀ k) := by
  refine modedP_revealThen P θ _ _ μ fun r ↦ ?_
  rcases μ with _ | m
  · exact modedP_none P θ (fun _ ↦ hF _) _
  by_cases hr : r.1 = restrictTo (openSet ch j μ₀) θ
  · have e : nxT θ (some m) (.inr (openSet ch j μ₀)) r = some (m.1 ∪ openSet ch j μ₀, m.2) := by
      simp [nxT, hr]
    rw [e]
    refine modedP₂_bind (F := fun _ μ' ↦ μ' = some (m.1 ∪ openSet ch j μ₀, m.2)) _ _
      (modedP_progFrom P θ B j μ₀ _ (fun m' hm' ↦ ?_) μ₀ le_rfl) fun _ μ' h ↦ ?_
    · cases hm'
      exact Finset.subset_union_right
    · rw [h, hr]
      exact hk m rfl
  · have e : nxT θ (some m) (.inr (openSet ch j μ₀)) r = none := by simp [nxT, hr]
    rw [e]
    exact modedP_none P θ (fun _ ↦ hF _) _

/-- **The challenger's answers keep the label invariant**, with the answer's entry. -/
theorem modedP_ansT (C : TwColl Par Tw Fn Msg Out) (B : QReg) (q' : CpreQuery J Tw Fn Msg)
    (log : QueryLog (CQ Par Tw J Val Fn Msg Out)) (μ : Option (CMem ch)) (hμ : Inv0 log μ) :
    ModedP (okT P) (nxT θ) (fun p μ' ↦ Inv0 (log ++ [⟨q', p.2.2⟩]) μ') μ (ansT C P B q') := by
  cases q' with
  | value j μ₀ =>
    show ModedP _ _ _ μ (valueT P B j μ₀)
    unfold valueT
    split_ifs with h
    · refine modedP_openT P θ B j μ₀ _ (F := fun a μ' ↦ Inv0 (log ++ [⟨.value j μ₀, a⟩]) μ')
        (fun _ ↦ inv0_none _) μ fun m hm ↦ ?_
      rintro _ ⟨⟩
      exact labInv_append_entry _ _ (hμ m hm) fun s hs ↦ by
        change s ∈ (if μ₀ < ch.len j then openSet ch j μ₀ else endSet ch j)
        simp only [h, ↓reduceIte]
        exact hs
    · refine modedP_revealThen P θ _ _
        (F := fun a μ' ↦ Inv0 (log ++ [⟨.value j μ₀, a⟩]) μ') μ fun r ↦ ?_
      rcases μ with _ | m
      · exact modedP_none P θ (fun _ ↦ inv0_none _) _
      intro m' hm'
      by_cases hr : r.1 = restrictTo (endSet ch j) θ
      · simp only [nxT, hr, ↓reduceIte, Option.some.injEq] at hm'
        subst hm'
        exact labInv_append_entry _ _ (hμ m rfl) fun s hs ↦ by
          change s ∈ (if μ₀ < ch.len j then openSet ch j μ₀ else endSet ch j)
          simp only [h, ↓reduceIte]
          exact hs
      · simp [nxT, hr] at hm'
  | eval l t m =>
    show ModedP _ _ _ μ (evalT C P B l t m)
    unfold evalT
    by_cases h : ch.IsStepTweak t
    · rw [dite_eq_left h]
      refine modedP_openT P θ B h.choose 0 (fun _ ↦ keepReads B (C.eval romWorld l P t m))
        (F := fun a μ' ↦ Inv0 (log ++ [⟨.eval l t m, a⟩]) μ') (fun _ ↦ inv0_none _) μ
        fun m' hm' ↦
        modedP_keepReads P θ B _ (F := fun a μ' ↦ Inv0 (log ++ [⟨.eval l t m, a⟩]) μ') _
          (fun _ ↦ ?_) (fun _ ↦ inv0_none _)
      rintro _ ⟨⟩
      exact labInv_append_entry _ _ (hμ m' hm') fun _ _ ↦ h
    · rw [dite_eq_right h]
      exact modedP_keepReads P θ B _ (F := fun a μ' ↦ Inv0 (log ++ [⟨.eval l t m, a⟩]) μ') μ
        (fun _ m' hm' ↦ labInv_append _ (hμ m' hm'))
        (fun _ ↦ inv0_none _)
  | reveal => exact fun m' hm' ↦ labInv_append _ (hμ m' hm')

/-- **The reduction's computation against the template challenger keeps the invariant.** -/
theorem modedP_tImplRun (C : TwColl Par Tw Fn Msg Out) (B : QReg) {α : Type}
    (x : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) α) :
    ∀ (log : QueryLog (CQ Par Tw J Val Fn Msg Out)) (μ : Option (CMem ch)), Inv0 log μ →
      ModedP (okT P) (nxT θ) (fun p μ' ↦ Inv0 p.2.2.2 μ') μ
        ((simulateQ (tImpl C P B) x).run log) := by
  induction x using OracleComp.inductionOn with
  | pure a => exact fun _ _ h ↦ h
  | query_bind t k ih =>
    intro log μ hμ
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with i | q'
    · change ModedP _ _ _ μ (QuantumComp₂.bind ((readLiftQ goodC (toReads updC
          (mixImpl .red B i))).map fun a ↦ (a, log)) fun p ↦
            (simulateQ (tImpl C P B) (k p.1)).run p.2)
      refine modedP₂_bind (F := fun (p : romWorld.Oracles.Range i ×
          QueryLog (CQ Par Tw J Val Fn Msg Out)) μ' ↦ p.2 = log ∧ (μ' = μ ∨ μ' = none))
        (F' := fun (p : α × QueryLog (CQ Par Tw J Val Fn Msg Out)) μ' ↦ Inv0 p.2 μ') _ _
        (modedP_map _ (F := fun (p : romWorld.Oracles.Range i ×
          QueryLog (CQ Par Tw J Val Fn Msg Out)) μ' ↦ p.2 = log ∧ (μ' = μ ∨ μ' = none))
          (modedP_readLiftQ P θ _
          (fun _ μ' ↦ log = log ∧ (μ' = μ ∨ μ' = none)) (fun _ ↦ ⟨rfl, Or.inr rfl⟩) μ
          (modedP_mono (fun _ _ h ↦ ⟨rfl, Or.inl h⟩) _ _
            (modedP_mono (fun p μ' h ↦ h.trans (nxM_keep .red (by decide) μ i _)) _ _
              (modedP_mixImpl updM rl0 .red B i μ))))) fun p μ' hp ↦ ?_
      obtain ⟨a, l⟩ := p
      obtain ⟨hl, hμ'⟩ := hp
      change l = log at hl
      subst hl
      refine ih a l μ' ?_
      rcases hμ' with rfl | rfl
      · exact hμ
      · exact inv0_none _
    · change ModedP _ _ _ μ (QuantumComp₂.bind ((ansT C P B q').map
          fun a ↦ (a, log ++ [⟨q', a⟩])) fun p ↦ (simulateQ (tImpl C P B) (k p.1)).run p.2)
      exact modedP₂_bind (F := fun (p : (CQ Par Tw J Val Fn Msg Out).Range q' ×
          QueryLog (CQ Par Tw J Val Fn Msg Out)) μ' ↦ Inv0 p.2 μ')
        (F' := fun (p : α × QueryLog (CQ Par Tw J Val Fn Msg Out)) μ' ↦ Inv0 p.2 μ') _ _
        (modedP_map _ (F := fun (p : (CQ Par Tw J Val Fn Msg Out).Range q' ×
          QueryLog (CQ Par Tw J Val Fn Msg Out)) μ' ↦ Inv0 p.2 μ')
          (modedP_ansT P θ C B q' log μ hμ)) fun p μ' hp ↦ ih p.1 p.2 μ' hp

/-- **The adversary run by the reduction keeps the invariant.** -/
theorem modedP_tRun {Q St : Type} {R : OracleSpec.{0, 0} Q} {X Y : QReg → Type}
    (C : TwColl Par Tw Fn Msg Out) (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (leaf : ∀ u, X u → St × QueryLog (CQ Par Tw J Val Fn Msg Out) → Y u) {A : QReg}
    (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} (advSpec romWorld.spec R)) X A) :
    ∀ s μ, Inv0 s.2 μ → ModedP (okT P) (nxT θ)
      (fun p μ' ↦ ∃ u y s', Inv0 s'.2 μ' ∧ p = ⟨u, leaf u y s'⟩) μ (tRun C P σ leaf x s) := by
  induction x using IFreeM.inductionOn with
  | pure u y =>
    intro s μ h
    rw [tRun]
    exact ⟨u, y, s, h, rfl⟩
  | liftBind A cmd next ih =>
    intro s μ hs
    rcases cmd with o | ⟨p | q, E, ℓ⟩
    · rw [tRun]
      refine modedP_bind _ _ (modedP_readLens_cmd P θ (.prim o) μ) fun u b μ' hb ↦ ?_
      obtain ⟨b, e⟩ := b
      subst e
      refine ih b s μ' ?_
      rcases hb with rfl | rfl
      · exact hs
      · exact inv0_none _
    · rw [tRun]
      refine modedP_bind _ _ (modedP_readLens_cmd P θ (.query (.hash p) E ℓ) μ)
        fun u b μ' hb ↦ ?_
      obtain ⟨b, e⟩ := b
      subst e
      refine ih b s μ' ?_
      rcases hb with rfl | rfl
      · exact hs
      · exact inv0_none _
    · rw [tRun]
      have ht : ModedP (okT P) (nxT θ) (fun p μ' ↦ Inv0 p.2.2.2.2 μ') μ
          (tTree C P σ s q E ℓ) :=
        modedP₂_bind (F := fun _ μ' ↦ μ' = μ) (F' := fun (r : R.Range q × (St ×
          QueryLog (CQ Par Tw J Val Fn Msg Out))) μ' ↦ Inv0 r.2.2 μ') _ _
          (modedP_act (F := fun _ μ' ↦ μ' = μ) _ μ fun _ ↦ rfl) fun _ μ' h ↦ h ▸ modedP_map
            (fun (r : (R.Range q × St) × QueryLog (CQ Par Tw J Val Fn Msg Out)) ↦
              (r.1.1, (r.1.2, r.2)))
            (F := fun (r : R.Range q × (St × QueryLog (CQ Par Tw J Val Fn Msg Out))) μ' ↦
              Inv0 r.2.2 μ')
            (modedP_tImplRun P θ C _ (σ s.1 q) s.2 μ hs)
      refine modedP_bind _ _ ht fun u l μ' hl ↦ ?_
      obtain ⟨e, l⟩ := l
      subst e
      exact ih _ _ μ' hl

/-- **The decision is moded**: a decision returning `true` ends in a won memory. -/
theorem modedP_judgeT (hlen : StepLen ch) (log : QueryLog (CQ Par Tw J Val Fn Msg Out))
    (out : J × ℕ × Val) (μ : Option (CMem ch)) (hμ : Inv0 log μ) :
    ModedP (okT P) (nxT θ) (fun p μ' ↦ p.2.2 = true → ∀ m, μ' = some m → WonM P θ m) μ
      (judgeT P log out) := by
  obtain ⟨j, μ₀, z⟩ := out
  rcases μ with _ | m₀
  · exact modedP_none P θ (fun _ _ _ h ↦ by cases h) _
  unfold judgeT
  dsimp only
  refine modedP₂_bind (F := fun e' μ' ↦ μ' = none ∨ LiveRun rl0 (updM .judge)
      (ch.walk romWorld P j μ₀ (ch.len j - μ₀) z) (some m₀) e' μ')
    (F' := fun b μ' ↦ b = true → ∀ m, μ' = some m → WonM P θ m) _ _
    (modedP_readLiftQ P θ _ (fun e' μ' ↦ μ' = none ∨ LiveRun rl0 (updM .judge)
      (ch.walk romWorld P j μ₀ (ch.len j - μ₀) z) (some m₀) e' μ') (fun _ ↦ Or.inl rfl) _
      (modedP_mono (fun _ _ h ↦ Or.inr h) _ _
        (modedP_toQuantumAt_mixImpl updM rl0 .judge _ _ _))) fun e' μ₁ h₁ ↦ ?_
  rcases h₁ with rfl | h₁
  · exact modedP_none P θ (fun _ _ _ h ↦ by cases h) _
  refine modedP_revealThen P θ _ _ (F := fun b μ' ↦ b = true → ∀ m, μ' = some m → WonM P θ m)
    μ₁ fun r ↦ ?_
  refine fun hw m hm ↦ ?_
  rw [holds_eq_true] at hw
  obtain ⟨hv, hlt, he, hop⟩ := hw
  have hend : srcOf j (ch.len j) le_rfl ∈ judgeSet ch log j μ₀ :=
    Finset.mem_union_left _ (Finset.mem_singleton_self _)
  obtain ⟨J', rfl, -, hwin⟩ := walk_live hlen P θ j (m₀.1 ∪ judgeSet ch log j μ₀)
    (Finset.mem_union_right _ hend) _ _ _ _ _ _ h₁ (by omega)
  by_cases hr : r.1 = restrictTo (judgeSet ch log j μ₀) θ
  · have e : nxT θ (some (m₀.1, J')) (.inr (judgeSet ch log j μ₀)) r =
        some (m₀.1 ∪ judgeSet ch log j μ₀, J') := by simp [nxT, hr]
    rw [e] at hm
    cases hm
    have hext : ∀ s ∈ judgeSet ch log j μ₀, extendR r.1 s = θ s := fun s hs ↦ by
      rw [hr]
      exact extendR_restrictTo θ hs
    have hcend : cval (extendR r.1) j (ch.len j) = cval θ j (ch.len j) :=
      cval_congr le_rfl (hext _ hend)
    refine hwin (by omega) (he.trans hcend) ?_
    by_cases ho : OpenedAtOrBelow log j μ₀
    · left
      have hsrc : srcOf j μ₀ hlt.le ∈ judgeSet ch log j μ₀ := by
        simp only [judgeSet, Finset.mem_union]
        right
        rw [dite_eq_left (⟨hlt.le, ho⟩ : μ₀ ≤ ch.len j ∧ OpenedAtOrBelow log j μ₀)]
        exact Finset.mem_singleton_self _
      rw [← cval_congr hlt.le (hext _ hsrc)]
      exact hop ho
    · right
      intro h hs
      rcases Finset.mem_union.mp hs with hs | hs
      · exact ho (opened_of_covered hv h hlt (hμ m₀ rfl _ hs))
      · simp only [judgeSet, Finset.mem_union] at hs
        rcases hs with hs | hs
        · obtain ⟨-, he'⟩ := srcOf_inj h le_rfl (Finset.mem_singleton.mp hs)
          omega
        · split_ifs at hs with hc
          · exact ho hc.2
          · exact absurd hs (Finset.notMem_empty _)
  · have e : nxT θ (some (m₀.1, J')) (.inr (judgeSet ch log j μ₀)) r = none := by
      simp [nxT, hr]
    rw [e] at hm
    cases hm

/-- **The template game is moded**: from the empty memory, a run returning `true` ends in a won
memory. -/
theorem modedP_cpreT (hlen : StepLen ch) (C : TwColl Par Tw Fn Msg Out) {Q St S0 Fo : Type}
    {R : OracleSpec.{0, 0} Q} (pre : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) Fo)
    (st0 : S0 → St) (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : S0 → Fo → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val)) :
    ModedP (okT P) (nxT θ) (fun p μ ↦ p.2.2 = true → ∀ m, μ = some m → WonM P θ m)
      (some (∅, ∅)) (cpreT C P pre adv st0 σ post) := by
  unfold cpreT
  refine modedP₂_bind (F := fun (p : S0 × QueryLog (CQ Par Tw J Val Fn Msg Out)) μ ↦ Inv0 p.2 μ)
    (F' := fun b μ ↦ b = true → ∀ m, μ = some m → WonM P θ m) _ _
    (modedP_tImplRun P θ C _ pre [] _ fun m hm ↦ ?_) fun p μ₁ h₁ ↦ ?_
  · cases hm
    exact fun s hs ↦ absurd hs (Finset.notMem_empty s)
  refine modedP₂_bind
    (F := fun (r : (Fo × St) × QueryLog (CQ Par Tw J Val Fn Msg Out)) μ ↦ Inv0 r.2 μ)
    (F' := fun b μ ↦ b = true → ∀ m, μ = some m → WonM P θ m) _ _
    (modedP_mono (fun q μ h ↦ ?_) _ _ (modedP_tRun P θ C σ _ (adv p.1) (st0 p.1, p.2) μ₁ h₁))
    fun r μ₂ h₂ ↦ ?_
  · obtain ⟨u, y, s', hs', rfl⟩ := h
    exact hs'
  exact modedP₂_bind
    (F := fun (o : (J × ℕ × Val) × QueryLog (CQ Par Tw J Val Fn Msg Out)) μ ↦ Inv0 o.2 μ)
    (F' := fun b μ ↦ b = true → ∀ m, μ = some m → WonM P θ m) _ _
    (modedP_tImplRun P θ C _ _ r.2 μ₂ h₂) fun o μ₃ h₃ ↦ modedP_judgeT P θ hlen o.2 o.1 μ₃ h₃

end tmpl

/-! ## A win is in the event -/

section win

open Quantum.Xmss.Assembly (ModedP NoBot decR runtimeRH runtimeR realizeT decR_branch_apply
  decR_step_noBot noBot_init recStep_branch kron_one_mul_clsKraus_mul_kron_one run_conjReg)
open Quantum.Xmss.Hybrid (runtime2 runtime2_branch)
open Quantum.Sponge (compressReg compressReg_mul_self conjTranspose_compressReg clsKraus
  clsKraus_apply hwProjector one_kronecker_ne_zero)

variable [Fintype J] [DecidableEq J] [Fintype Val] [DecidableEq Val] [Inhabited Val]
  (P : Par) (θ : (s : CSrc ch) → CD ch s)

/-- **The decompressed invariant of a mode**: no empty decompressed cell, and the memory. -/
def InvD : Option (CMem ch) → Set (HwReg HashOutput HashDomain (CMem ch))
  | none => ∅
  | some m => {s | NoBot s ∧ s.2.2 = m}

omit [Fintype J] [DecidableEq J] [Fintype Val] [DecidableEq Val] [Inhabited Val] in
/-- A classical Kraus operator in the decompressed basis moves the classical part by its map. -/
theorem mem_of_clsKraus_dec {M' : Type} [Fintype M'] [DecidableEq M']
    (p : Hw HashOutput HashDomain × M' → Prop) {_ : DecidablePred p}
    (φ : Hw HashOutput HashDomain × M' → Hw HashOutput HashDomain × M')
    (R : Hw HashOutput HashDomain × M' → Matrix (Quantum.Sponge.DbReg HashOutput HashDomain)
      (Quantum.Sponge.DbReg HashOutput HashDomain) ℂ)
    (m' m : Unit × HwReg HashOutput HashDomain M')
    (h : (((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg HashOutput HashDomain M') *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ clsKraus p φ R) *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg HashOutput HashDomain M')) m' m ≠ 0) :
    m'.2.2 = φ m.2.2 := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul, compressReg,
    kron_one_mul_clsKraus_mul_kron_one] at h
  have h' := (one_kronecker_ne_zero (a := m.1) (a' := m'.1) (b := m.2) (b' := m'.2) h).2
  rw [clsKraus_apply] at h'
  split_ifs at h' with hc
  · exact hc.2
  · exact absurd rfl h'

omit [Fintype Val] [DecidableEq Val] [Inhabited Val] in
/-- **Every allowed step keeps the decompressed invariant of its mode.** -/
theorem decR_step_invD [Fintype Val] [DecidableEq Val] (m₀ : CMem ch) (μ : Option (CMem ch))
    (i : (RSpec ch).Port) (r : (RSpec ch).Result i)
    (σ : Matrix ((RSpec ch).In i × HwReg HashOutput HashDomain (CMem ch))
      ((RSpec ch).In i × HwReg HashOutput HashDomain (CMem ch)) ℂ)
    (hi : okZ P θ μ i)
    (hσ : QuerySupportedOn (fun m : (RSpec ch).In i × HwReg HashOutput HashDomain (CMem ch) ↦
      m.2) (InvD μ) σ) :
    QuerySupportedOn (fun m : (RSpec ch).Out i × HwReg HashOutput HashDomain (CMem ch) ↦ m.2)
      (InvD (nxZ μ i r)) (((decR (X := HashOutput) (Z := HashDomain) m₀).step i).branch r σ) := by
  rcases μ with _ | mm
  · have h0 : σ = 0 := eq_zero_of_querySupportedOn_empty hσ
    rw [h0, map_zero]
    exact querySupportedOn_zero _ _
  have hnb := decR_step_noBot m₀ i r σ (hσ.imp fun s hs ↦ hs.1)
  have hmem : QuerySupportedOn (fun m : (RSpec ch).Out i × HwReg HashOutput HashDomain (CMem ch) ↦
      m.2) {s | NoBot s → s ∈ InvD (nxZ (some mm) i r)}
      (((decR (X := HashOutput) (Z := HashDomain) m₀).step i).branch r σ) := by
    rcases i with ((i | c) | c) | T
    · rw [decR_branch_apply m₀ _ r _ (runtime2_branch m₀ (.inl (.inl i)) r)]
      refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ fun hnb' ↦ ⟨hnb', ?_⟩
      have he : m'.2 = m.2 := by
        cases i <;> exact hwPort_dec_ne_zero _ m' m hK
      rw [he]
      exact hm.2
    · rw [decR_branch_apply m₀ _ r _ (runtime2_branch m₀ (.inl (.inr c)) r)]
      refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ fun hnb' ↦ ?_
      cases c with
      | readH z u =>
        obtain ⟨hr, -, -, hM, ho⟩ := readH_dec_ne_zero z u r m' m hK
        have hz : (m.2.1.1 z).isSome := hm.1.1 z
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hz
        have hr1 : r.1 = some ((m.2.2.1.1 z).getD v) := by
          rw [← ho, hv]
          cases m.2.2.1.1 z <;> rfl
        have hnx : nxZ (some mm) (.inl (.inl (.inr (.readH z u)))) r =
            some (u mm (some ((m.2.2.1.1 z).getD v))) := by
          change r.1.elim none (fun v ↦ some (u mm (some v))) = _
          rw [hr1]
          rfl
        rw [hnx]
        refine ⟨hnb', ?_⟩
        rw [hM, ← hr, hm.2, hr1]
      | readK x u => exact absurd hi id
      | readK' x u => exact absurd hi id
    · rw [decR_branch_apply m₀ _ r _ (runtime2_branch m₀ (.inr c) r)]
      refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ fun hnb' ↦ ⟨hnb', ?_⟩
      cases c with
      | programH z v => exact (congrArg Prod.snd (mem_of_clsKraus_dec _ _ _ m' m hK)).trans hm.2
      | programK x v => exact (congrArg Prod.snd (mem_of_clsKraus_dec _ _ _ m' m hK)).trans hm.2
      | programK' x v => exact (congrArg Prod.snd (mem_of_clsKraus_dec _ _ _ m' m hK)).trans hm.2
    · rw [decR_branch_apply m₀ _ r _ (recStep_branch T r)]
      refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ fun hnb' ↦ ⟨hnb', ?_⟩
      have he := mem_of_clsKraus_dec _ _ _ m' m hK
      change m'.2.2.2 = (mm.1 ∪ T, mm.2)
      rw [he, ← hm.2]
  exact (Quantum.Xmss.Assembly.querySupportedOn_inter hnb hmem).imp fun s hs ↦ hs.2 hs.1

omit [Fintype Val] [DecidableEq Val] [Inhabited Val] in
/-- The decompressed initial operator is on the invariant of the initial memory. -/
theorem invD_init [Fintype Val] [DecidableEq Val] (m₀ : CMem ch) {A : Type} [Fintype A]
    [DecidableEq A] (ρ : Matrix A A ℂ) :
    QuerySupportedOn (fun m : A × HwReg HashOutput HashDomain (CMem ch) ↦ m.2) (InvD (some m₀))
      (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ compressReg HashOutput HashDomain (CMem ch))
        (ρ ⊗ₖ (runtimeR (X := HashOutput) (Z := HashDomain) m₀).init.matrix)) := by
  have h0 := querySupportedOn_init (X := HashOutput) (Z := HashDomain) m₀ ρ
  have h1 := querySupportedOn_conj_compressReg (S := {s | s.2.2 = m₀})
    (fun s s' he hs ↦ by change s'.2.2 = m₀; rw [← he]; exact hs)
    (h0.imp fun s hs ↦ by rw [Set.mem_singleton_iff] at hs; rw [hs]; rfl)
  exact (Quantum.Xmss.Assembly.querySupportedOn_inter (noBot_init m₀ ρ) h1).imp
    fun s hs ↦ ⟨hs.1, hs.2⟩

omit [Fintype Val] [DecidableEq Val] [Inhabited Val] in
/-- **A win is in the event.** A realized program moded from the memory `m₀` whose leaves
returning `true` are reached in won memories wins at most with the event weight of `BadC`. -/
theorem evalDistMap_le_eventWeight_cpre [Fintype Val] [DecidableEq Val] (m₀ : CMem ch)
    (x : QuantumComp LocalSig.instruments.{0} (RSpec ch)
      (QuantumComp₂.Leaf (QReg.of Unit) Bool) (QReg.of Unit))
    (hx : ModedP (okZ P θ) nxZ (fun p μ ↦ p.2.2 = true → ∀ m, μ = some m → WonM P θ m)
      (some m₀) x) :
    (runtimeR (X := HashOutput) (Z := HashDomain) m₀).evalDistMap .instruments x
        (SubState.basis ()) (fun p ↦ p.2.2) {true} ≤
      (runtimeR (X := HashOutput) (Z := HashDomain) m₀).eventWeight .instruments
        (hwProjector (BadC P θ)) x
        ((SubState.basis ()).matrix ⊗ₖ
          (runtimeR (X := HashOutput) (Z := HashDomain) m₀).init.matrix) := by
  set ρ := (SubState.basis ()).matrix ⊗ₖ
    (runtimeR (X := HashOutput) (Z := HashDomain) m₀).init.matrix with hρ
  have hdec := querySupportedOn_run_moded (decR (X := HashOutput) (Z := HashDomain) m₀)
    .instruments InvD (fun μ i r σ hi hσ ↦ decR_step_invD P θ m₀ μ i r σ hi hσ) x (some m₀) hx
    (ρ := MatrixMap.conj ((1 : Matrix (QReg.of Unit) (QReg.of Unit) ℂ) ⊗ₖ
      compressReg HashOutput HashDomain (CMem ch)) ρ) (invD_init m₀ _)
  rw [QuantumRuntime.evalDistMap_apply _ _ _ _ _ (measurableSet_singleton true)]
  unfold QuantumRuntime.eventWeight
  refine ENNReal.tsum_le_tsum fun p ↦ ?_
  rw [QuantumRuntime.matrix_jointPost]
  by_cases hp : p.2.2 = true
  · rw [Set.indicator_of_mem (by exact hp), Pi.one_apply, mul_one]
    have h1 := hdec p
    have e := run_conjReg (runtimeRH (X := HashOutput) (Z := HashDomain) m₀)
      (compressReg HashOutput HashDomain (CMem ch)) compressReg_mul_self conjTranspose_compressReg
      .instruments x p ρ
    erw [e] at h1
    have h2 := querySupportedOn_conj_compressReg (S := {d | WonM P θ d.2.2})
      (fun s s' he hs ↦ by change WonM P θ s'.2.2; rw [← he]; exact hs)
      (h1.imp fun d ⟨μ, hμ, hd⟩ ↦ by
        rcases μ with _ | m
        · exact absurd hd id
        · change WonM P θ d.2.2.2
          rw [hd.2]
          exact hμ hp m rfl)
    rw [conj_compressReg_conj_compressReg] at h2
    have h3 := conj_one_kronecker_hwProjector_of_supp (BadC P θ) (h2.imp fun d hd ↦ Or.inr hd)
    exact le_of_eq (congrArg (fun τ ↦ ENNReal.ofReal (Matrix.trace τ).re) h3).symm
  · rw [Set.indicator_of_notMem (by simpa using hp), mul_zero]
    exact zero_le

/-- **Runtime 2's win on the realized template game is at most the event weight** of `BadC`. -/
theorem p2_le_eventWeight (hlen : StepLen ch) (C : TwColl Par Tw Fn Msg Out) {Q St S0 Fo : Type}
    {R : OracleSpec.{0, 0} Q} (pre : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) Fo)
    (st0 : S0 → St) (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : S0 → Fo → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val)) :
    (runtimeR (X := HashOutput) (Z := HashDomain) ((∅, ∅) : CMem ch)).evalDistMap .instruments
        (realizeT θ (cpreT C P pre adv st0 σ post)) (SubState.basis ()) (fun p ↦ p.2.2) {true} ≤
      (runtimeR (X := HashOutput) (Z := HashDomain) ((∅, ∅) : CMem ch)).eventWeight .instruments
        (hwProjector (BadC P θ)) (realizeT θ (cpreT C P pre adv st0 σ post))
        ((SubState.basis ()).matrix ⊗ₖ
          (runtimeR (X := HashOutput) (Z := HashDomain) ((∅, ∅) : CMem ch)).init.matrix) :=
  evalDistMap_le_eventWeight_cpre P θ _ _
    (modedP_realizeT_cpre P θ _ (modedP_cpreT P θ hlen C pre adv st0 σ post))

end win

/-! ## The event's properties -/

section evprops

open Quantum.Qrom (CellTargetBad unionH upClosed_slice_cellTargetBad
  exists_of_mem_cellTargetBad_updateH mem_cellTargetBad_fill)
open Quantum.Sponge (Dbs DbReg UpClosed FreshBound slice dbGrade UpCell hFlip hCls hMove)

variable (P : Par) (θ : (s : CSrc ch) → CD ch s)

theorem wonM_insert {L : Finset (CSrc ch)} {J : JMem} {z : HashDomain} {v : HashOutput}
    (h : WonM P θ (L, insert (z, v) J)) : WonM P θ (L, J) ∨ v ∈ Fib P θ L z := by
  obtain ⟨zy, hzy, hf⟩ := h
  rcases Finset.mem_insert.mp hzy with rfl | hzy
  · exact Or.inr hf
  · exact Or.inl ⟨zy, hzy, hf⟩

/-- **The memory moves of the game's reads**: the label is kept, a won memory stays won, and a
memory becomes won only by recording a value in the target of the read cell. -/
theorem readShape_wonM {z : HashDomain} {u : CMem ch → Option HashOutput → CMem ch}
    (hu : ReadShape (.readH z u)) (m : CMem ch) (o : Option HashOutput) :
    (u m o).1 = m.1 ∧ (WonM P θ m → WonM P θ (u m o)) ∧
      (WonM P θ (u m o) → WonM P θ m ∨ ∃ y, o = some y ∧ y ∈ Fib P θ m.1 z) := by
  rcases hu with rfl | rfl
  · exact ⟨rfl, id, Or.inl⟩
  · rcases o with _ | y
    · exact ⟨rfl, id, Or.inl⟩
    · refine ⟨rfl, fun ⟨zy, hzy, hf⟩ ↦ ⟨zy, Finset.mem_insert_of_mem hzy, hf⟩, fun h ↦ ?_⟩
      rcases wonM_insert P θ h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨y, rfl, h⟩

/-- A cell holding a value of its target puts the register in the event. -/
theorem mem_badC_of_cell {s : HwReg HashOutput HashDomain (CMem ch)} {z : HashDomain}
    {y : HashOutput} (h : unionH s z = some y) (hy : y ∈ Fib P θ s.2.2.1 z) : s ∈ BadC P θ :=
  Or.inl ⟨z, y, h, hy⟩

/-- **A memory move off the target keeps the event.** -/
theorem memMove_iff {z : HashDomain} {u : CMem ch → Option HashOutput → CMem ch}
    (hu : ReadShape (.readH z u)) (s : HwReg HashOutput HashDomain (CMem ch))
    (o : Option HashOutput) (ho : ∀ y, o = some y → y ∉ Fib P θ s.2.2.1 z) :
    ((s.1, s.2.1, u s.2.2 o) ∈ BadC P θ ↔ s ∈ BadC P θ) := by
  obtain ⟨hl, hmono, hwon⟩ := readShape_wonM P θ hu s.2.2 o
  constructor
  · rintro (⟨x, y, hxy, hy⟩ | hw)
    · refine Or.inl ⟨x, y, hxy, ?_⟩
      change y ∈ Fib P θ s.2.2.1 x
      rw [← hl]
      exact hy
    · rcases hwon hw with hw | ⟨y, rfl, hy⟩
      · exact Or.inr hw
      · exact absurd hy (ho y rfl)
  · rintro (⟨x, y, hxy, hy⟩ | hw)
    · refine Or.inl ⟨x, y, hxy, ?_⟩
      change y ∈ Fib P θ (u s.2.2 o).1 x
      rw [hl]
      exact hy
    · exact Or.inr (hmono hw)

theorem upCell_badC (z : HashDomain) (u : CMem ch → Option HashOutput → CMem ch) :
    UpCell (BadC P θ) (.readH z u) := by
  rintro s hz (hs | hs) y
  · exact Or.inl (mem_cellTargetBad_fill hs hz (some y) s.2.2 fun _ _ h ↦ h)
  · exact Or.inr hs

/-- Filling an empty, not hardwired cell off its target keeps the event. -/
theorem fill_iff {s : HwReg HashOutput HashDomain (CMem ch)} {z : HashDomain} {v : HashOutput}
    (hW : s.2.1.1 z = none) (hD : s.1.1 z = none) (hv : v ∉ Fib P θ s.2.2.1 z) :
    (((Function.update s.1.1 z (some v), s.1.2), s.2) ∈ BadC P θ ↔ s ∈ BadC P θ) := by
  refine ⟨fun h ↦ ?_, fun h ↦ upCell_badC P θ z (fun m _ ↦ m) s hD h v⟩
  by_contra hs
  rcases h with h | h
  · obtain ⟨y, hy, hyt⟩ := exists_of_mem_cellTargetBad_updateH (fun h' ↦ hs (Or.inl h'))
      (fun _ _ _ h ↦ h) h
    rw [hW, Option.none_or] at hy
    cases hy
    exact hv hyt
  · exact hs (Or.inr h)

end evprops

/-! ## The costs of the calls -/

section costs

open Quantum.Qrom (CellTargetBad unionH upClosed_slice_cellTargetBad freshBound_slice_cellTargetBad)
open Quantum.Sponge (Dbs DbReg UpClosed FreshBound slice dbGrade hwProjector hwReadKraus
  hwProgKraus progMap sum_hwProgKraus potential_kraus_le flipCost flipCost_le_of
  flipCost_prog_le gram_classical liftSet mem_liftSet ind indProj readNoBot_of_noBot ReadNoBot
  spongeHardwired spongeIn rpow_inv_two_potential_spongeHardwired_le hwEmpty clsKraus_apply
  one_kronecker_hwProjector_proj one_kronecker_hwProjector tsum_potential_conj)
open Quantum.Xmss.Assembly (NoBot recKraus sum_recKraus)
variable [Fintype J] [DecidableEq J] [Fintype Val] [DecidableEq Val]
  (P : Par) (θ : (s : CSrc ch) → CD ch s)

omit [Fintype J] [DecidableEq J] [Fintype Val] [DecidableEq Val] in
theorem upClosed_slice_badC (W : Hw HashOutput HashDomain) (m : CMem ch) :
    UpClosed (slice (BadC P θ) W m) where
  h Db hDb z u hz := by
    rcases hDb with h | h
    · exact Or.inl ((upClosed_slice_cellTargetBad (tgt := tgtC P θ) W m).h Db h z u hz)
    · exact Or.inr h
  k Db hDb _ _ _ := hDb
  k' Db hDb _ _ _ := hDb

omit [Fintype J] [DecidableEq J] [Fintype Val] in
open scoped Classical in
/-- **The fresh bound of every slice**: `F / |Y|`. -/
theorem freshBound_slice_badC (hinj : CellInj ch P) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ ch.step.trunc y = o).card ≤ F)
    (W : Hw HashOutput HashDomain) (m : CMem ch) (t : ℕ) :
    FreshBound (slice (BadC P θ) W m) t ((F : ℝ≥0∞) / Fintype.card HashOutput) where
  h Db hDb h₁ h₂ h₃ z hz := by
    have hc := (freshBound_slice_cellTargetBad (tgt := tgtC P θ) W m (ε := (F : ℝ≥0∞) /
      Fintype.card HashOutput) (fun x _ ↦ ENNReal.div_le_div_right (Nat.cast_le.2
        (card_fib_le hinj θ m.1 x hF _ fun _ h ↦ h)) _) t).h Db (fun h ↦ hDb (Or.inl h)) h₁ h₂
          h₃ z hz
    refine le_trans (ENNReal.div_le_div_right (Nat.cast_le.2 (Finset.card_le_card
      fun u hu ↦ ?_)) _) hc
    rcases (Finset.mem_filter.1 hu).2 with h | h
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
    · exact absurd (Or.inr h) hDb
  k Db hDb _ _ _ x _ := by
    rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun _ _ hu ↦ ?_)]
    · rw [Nat.cast_zero, ENNReal.zero_div]
      exact zero_le
    rcases hu with h | h
    · exact hDb (Or.inl h)
    · exact hDb (Or.inr h)
  k' Db hDb _ _ _ x _ := by
    rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun _ _ hu ↦ ?_)]
    · rw [Nat.cast_zero, ENNReal.zero_div]
      exact zero_le
    rcases hu with h | h
    · exact hDb (Or.inl h)
    · exact hDb (Or.inr h)

omit [Fintype J] [DecidableEq J] [Fintype Val] [DecidableEq Val] in
theorem dbGrade_le_cardC (D : DbReg HashOutput HashDomain) :
    dbGrade D ≤ Fintype.card HashDomain + Fintype.card HashOutput := by
  have h₁ : D.1.size ≤ Fintype.card HashDomain := Finset.card_le_univ _
  have h₂ : D.2.1.size ≤ Fintype.card HashOutput := Finset.card_le_univ _
  have h₃ : D.2.2.size ≤ Fintype.card HashOutput := Finset.card_le_univ _
  unfold dbGrade
  omega

/-- `6 F / N ≤ gradeEta F`. -/
theorem six_mul_le_gradeEtaC (F : ℕ) :
    6 * ((F : ℝ≥0∞) / Fintype.card HashOutput) ≤ ENNReal.ofReal (gradeEta HashOutput F) := by
  have hN : (0 : ℝ) < Fintype.card HashOutput := Nat.cast_pos.mpr Fintype.card_pos
  have ha : 0 ≤ (F : ℝ) / Fintype.card HashOutput := div_nonneg (Nat.cast_nonneg _) hN.le
  have hab : √((F : ℝ) / Fintype.card HashOutput) ≤
      √(((F : ℝ) + 2) / Fintype.card HashOutput) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) hN.le)
  have hreal : 6 * ((F : ℝ) / Fintype.card HashOutput) ≤ gradeEta HashOutput F := by
    unfold gradeEta
    have h0 := Real.sq_sqrt ha
    nlinarith [Real.sqrt_nonneg ((F : ℝ) / Fintype.card HashOutput)]
  rw [ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_natCast F, ← ENNReal.ofReal_natCast
    (Fintype.card HashOutput), ← ENNReal.ofReal_inv_of_pos hN, ← ENNReal.ofReal_mul
    (inv_nonneg.mpr hN.le), ← ENNReal.ofReal_ofNat 6, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [inv_mul_eq_div]
  exact hreal

omit [Fintype Val] in
open scoped Classical in
/-- **A sponge call costs `√(gradeEta F)`.** -/
theorem potential_sponge_badC_le (hinj : CellInj ch P) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ ch.step.trunc y = o).card ≤ F) (m₀ : CMem ch)
    (i : Quantum.Sponge.SpongePort)
    {σ : Matrix (spongeIn HashOutput HashDomain i × HwReg HashOutput HashDomain (CMem ch))
      (spongeIn HashOutput HashDomain i × HwReg HashOutput HashDomain (CMem ch)) ℂ}
    (hσ : σ.PosSemidef) :
    QuantumRuntime.potential (hwProjector (BadC P θ))
        (MatrixMap.conj ((spongeHardwired HashOutput HashDomain (hwEmpty HashOutput HashDomain)
          m₀).U i) σ) ^ (2⁻¹ : ℝ) ≤
      QuantumRuntime.potential (hwProjector (BadC P θ)) σ ^ (2⁻¹ : ℝ) +
        (ENNReal.ofReal (gradeEta HashOutput F) * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ) := by
  have hεtop : (F : ℝ≥0∞) / Fintype.card HashOutput ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top F)
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  refine (rpow_inv_two_potential_spongeHardwired_le (BadC P θ)
    (fun W m ↦ upClosed_slice_badC P θ W m) hεtop
    (fun W m ↦ freshBound_slice_badC P θ hinj hF W m _)
    (hwEmpty HashOutput HashDomain) m₀ i hσ
    (N := Fintype.card HashDomain + Fintype.card HashOutput)
    (fun _ _ _ ↦ ⟨dbGrade_le_cardC _, dbGrade_le_cardC _⟩)).trans
    (add_le_add le_rfl (ENNReal.rpow_le_rpow ?_ (by norm_num)))
  exact mul_le_mul_of_nonneg_right (six_mul_le_gradeEtaC F) zero_le

omit [Fintype Val] in
/-- **A read of a step cell costs `√(gradeEta F)`.** -/
theorem tsum_potential_read_badC (hinj : CellInj ch P) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ ch.step.trunc y = o).card ≤ F) {z : HashDomain}
    {u : CMem ch → Option HashOutput → CMem ch} (hu : ReadShape (.readH z u))
    {σ : Matrix (Unit × HwReg HashOutput HashDomain (CMem ch))
      (Unit × HwReg HashOutput HashDomain (CMem ch)) ℂ} (hσ : σ.PosSemidef)
    (hnb : ReadNoBot (.readH z u) σ) :
    ∑' r, QuantumRuntime.potential (hwProjector (BadC P θ))
        (MatrixMap.conj (hwReadKraus (.readH z u) r) σ) ≤
      (QuantumRuntime.potential (hwProjector (BadC P θ)) σ ^ (2⁻¹ : ℝ) +
        ENNReal.ofReal (gradeEta HashOutput F * σ.trace.re) ^ (2⁻¹ : ℝ)) ^ 2 := by
  refine tsum_potential_readH_le_sqrt (BadC P θ) z u F (upCell_badC P θ z u) hσ hnb
    (fun q _ hW hD ↦ ⟨card_fib_le hinj θ q.2.2.2.1 z hF _ fun v hv ↦ ?_,
      (card_fib_le hinj θ q.2.2.2.1 z hF _ fun v hv ↦ ?_ : rdCnt _ _ _ _ ≤ F)⟩)
    (fun q _ hW ↦ ?_) (fun q _ hW ↦ ?_) (fun q _ hW _ hm ↦ ?_)
  · by_contra hf
    rcases hv with h | ⟨u', h⟩
    · exact h (fill_iff P θ (s := q.2) hW hD hf)
    · exact h (memMove_iff P θ hu (((Function.update q.2.1.1 z u', q.2.1.2), q.2.2.1, q.2.2.2))
        (some v) fun y hy ↦ by cases hy; exact hf)
  · by_contra hf
    exact hv ((memMove_iff P θ hu (((Function.update q.2.1.1 z (some v), q.2.1.2), q.2.2.1,
      q.2.2.2)) (some v) fun y hy ↦ by cases hy; exact hf).trans
        (fill_iff P θ (s := q.2) hW hD hf))
  · rintro ⟨hq, hin⟩
    by_cases hy : ∃ y, q.2.1.1 z = some y ∧ y ∈ Fib P θ q.2.2.2.1 z
    · obtain ⟨y, h1, h2⟩ := hy
      exact hq (mem_badC_of_cell P θ (by simp [unionH, hW, h1]) h2)
    · exact hq ((memMove_iff P θ hu q.2 (q.2.1.1 z) fun y h1 h2 ↦ hy ⟨y, h1, h2⟩).mp hin)
  · rintro ⟨hq, hin⟩
    by_cases hy : ∃ y, q.2.2.1.1 z = some y ∧ y ∈ Fib P θ q.2.2.2.1 z
    · obtain ⟨y, h1, h2⟩ := hy
      exact hq (mem_badC_of_cell P θ (by simp [unionH, h1]) h2)
    · exact hq ((memMove_iff P θ hu q.2 (q.2.2.1.1 z) fun y h1 h2 ↦ hy ⟨y, h1, h2⟩).mp hin)
  · obtain ⟨u', h⟩ := hm
    by_contra hq
    refine h (memMove_iff P θ hu (((Function.update q.2.1.1 z u', q.2.1.2), q.2.2.1, q.2.2.2))
      (q.2.1.1 z) fun y h1 h2 ↦ hq (mem_badC_of_cell P θ (by simp [unionH, hW, h1]) h2))

omit [Fintype J] [DecidableEq J] [Fintype Val] [DecidableEq Val] in
/-- A read off the step cells is invisible to the event. -/
theorem readInvisible_badC {z : HashDomain} (hz : ¬StepCell ch P z)
    {u : CMem ch → Option HashOutput → CMem ch} (hu : ReadShape (.readH z u)) :
    ReadInvisible (BadC P θ) z u := by
  intro s s' o hD hk hW hm
  have he : Fib P θ s'.2.2.1 z = ∅ := fib_eq_empty_of_not_stepCell θ _ hz
  have he' : Fib P θ s.2.2.1 z = ∅ := fib_eq_empty_of_not_stepCell θ _ hz
  obtain ⟨hl, hmono, hwon⟩ := readShape_wonM P θ hu s.2.2 o
  have hl' : s'.2.2.1 = s.2.2.1 := by rw [hm]; exact hl
  have hU : ∀ x, x ≠ z → unionH s' x = unionH s x := fun x hx ↦ by
    simp only [unionH, hW, hD x hx]
  constructor
  · rintro (⟨x, y, hxy, hy⟩ | hw)
    · by_cases hx : x = z
      · subst hx
        rw [show tgtC P θ s'.2.1 s'.2.2 x = Fib P θ s'.2.2.1 x from rfl, he] at hy
        exact absurd hy (Set.notMem_empty y)
      · refine Or.inl ⟨x, y, (hU x hx).symm.trans hxy, ?_⟩
        change y ∈ Fib P θ s.2.2.1 x
        rw [← hl']
        exact hy
    · change WonM P θ s'.2.2 at hw
      rw [hm] at hw
      rcases hwon hw with hw | ⟨y, -, hy⟩
      · exact Or.inr hw
      · rw [he'] at hy
        exact absurd hy (Set.notMem_empty y)
  · rintro (⟨x, y, hxy, hy⟩ | hw)
    · by_cases hx : x = z
      · subst hx
        rw [show tgtC P θ s.2.1 s.2.2 x = Fib P θ s.2.2.1 x from rfl, he'] at hy
        exact absurd hy (Set.notMem_empty y)
      · refine Or.inl ⟨x, y, (hU x hx).trans hxy, ?_⟩
        change y ∈ Fib P θ s'.2.2.1 x
        rw [hl']
        exact hy
    · refine Or.inr ?_
      change WonM P θ s'.2.2
      rw [hm]
      exact hmono hw

omit [Fintype J] [DecidableEq J] [Fintype Val] [DecidableEq Val] in
/-- Fewer targets for a larger label. -/
theorem fib_anti {L L' : Finset (CSrc ch)} (hL : L ⊆ L') (z : HashDomain) :
    Fib P θ L' z ⊆ Fib P θ L z := by
  rintro y ⟨j, ν, x, hν, hz, hb, hy⟩
  refine ⟨j, ν, x, hν, hz, ?_, hy⟩
  rcases hb with hb | hb
  · exact Or.inl hb
  · exact Or.inr fun h hs ↦ hb h (hL hs)

omit [Fintype J] [Fintype Val] [DecidableEq Val] in
/-- **Recording coordinates never enters the event.** -/
theorem mem_badC_of_record (s : HwReg HashOutput HashDomain (CMem ch)) (T : Finset (CSrc ch))
    (h : ((s.1, s.2.1, (s.2.2.1 ∪ T, s.2.2.2)) : HwReg HashOutput HashDomain (CMem ch)) ∈
      BadC P θ) : s ∈ BadC P θ := by
  rcases h with ⟨x, y, hxy, hy⟩ | ⟨zy, hzy, hf⟩
  · exact Or.inl ⟨x, y, hxy, fib_anti P θ Finset.subset_union_left x hy⟩
  · exact Or.inr ⟨zy, hzy, fib_anti P θ Finset.subset_union_left _ hf⟩

omit [Fintype J] [DecidableEq J] [Fintype Val] [DecidableEq Val] in
/-- **Programming an honest cell whose source is in the label never enters the event.** -/
theorem not_mem_badC_progMap (hinj : CellInj ch P) (q : CPos ch) (v : HashOutput)
    {s : HwReg HashOutput HashDomain (CMem ch)} (hL : srcOf q.1 q.2 q.2.isLt.le ∈ s.2.2.1)
    (hs : s ∉ BadC P θ) : progMap (.programH (cellOf P θ q) v) s ∉ BadC P θ := by
  rintro (⟨x, y, hxy, hy⟩ | hw)
  · by_cases hx : x = cellOf P θ q
    · subst hx
      change y ∈ Fib P θ s.2.2.1 (cellOf P θ q) at hy
      rw [fib_cellOf_eq_empty hinj θ q hL] at hy
      exact hy
    · refine hs (Or.inl ⟨x, y, ?_, hy⟩)
      change (Function.update s.2.1.1 (cellOf P θ q) (some v) x).or
        (Function.update s.1.1 (cellOf P θ q) none x) = some y at hxy
      rw [Function.update_of_ne hx, Function.update_of_ne hx] at hxy
      exact hxy
  · exact hs (Or.inr hw)

omit [Fintype J] [DecidableEq J] [Fintype Val] [DecidableEq Val] in
/-- **A classical step that never enters the event costs nothing** (ReadGrade's
`tsum_potential_le_of_into` for any complete Kraus family). -/
theorem tsum_potential_kraus_le_of_into {X Z M' : Type} [Fintype X] [DecidableEq X] [Fintype Z]
    [DecidableEq Z] [Fintype M'] [DecidableEq M'] (S : Set (HwReg X Z M'))
    [DecidablePred (· ∈ S)] {ι : Type} [Fintype ι]
    (K : ι → Matrix (Unit × HwReg X Z M') (Unit × HwReg X Z M') ℂ) (hK : ∑ r, (K r)ᴴ * K r = 1)
    (hT : ∀ r (q' q : Unit × HwReg X Z M'), K r q' q ≠ 0 → q'.2 ∈ S → q.2 ∈ S)
    {σ : Matrix (Unit × HwReg X Z M') (Unit × HwReg X Z M') ℂ} (hσ : σ.PosSemidef) :
    ∑' r, QuantumRuntime.potential (hwProjector S) (MatrixMap.conj (K r) σ) ≤
      QuantumRuntime.potential (hwProjector S) σ := by
  obtain ⟨hQ, hQQ⟩ := one_kronecker_hwProjector_proj S
  rw [one_kronecker_hwProjector] at hQ hQQ
  set Pj := indProj (liftSet S) with hPj
  have hcomm : ∀ r, Pj * K r * σ = Pj * K r * Pj * σ := by
    intro r
    ext q' b
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [hPj, indProj, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hk : K r q' a = 0
    · simp [hk]
    by_cases hq : q'.2 ∈ S
    · have h1 : ind (liftSet S) a = 1 := by
        simp [ind, mem_liftSet, hT r q' a hk hq]
      rw [h1]
      simp
    · have h0 : ind (liftSet S) q' = 0 := by
        simp [ind, mem_liftSet, hq]
      rw [h0]
      simp
  have hσh : σᴴ = σ := hσ.1
  have hadj : ∀ r, σ * (K r)ᴴ * Pj = σ * Pj * (K r)ᴴ * Pj := by
    intro r
    have h := congrArg conjTranspose (hcomm r)
    simp only [conjTranspose_mul, hσh, hQ] at h
    simpa only [Matrix.mul_assoc] using h
  set τ := Pj * σ * Pj with hτ
  have hτp : τ.PosSemidef := by
    have h := hσ.mul_mul_conjTranspose_same Pj
    rwa [hQ] at h
  have key : ∀ K' : Matrix (Unit × HwReg X Z M') (Unit × HwReg X Z M') ℂ,
      Pj * K' * σ = Pj * K' * Pj * σ → σ * K'ᴴ * Pj = σ * Pj * K'ᴴ * Pj →
      (K'ᴴ * Pj * K' * σ).trace = (Pj * (K' * τ * K'ᴴ) * Pj).trace := by
    intro K' hc ha
    have e1 : (K'ᴴ * Pj * K' * σ).trace = (Pj * K' * σ * K'ᴴ).trace := by
      rw [show K'ᴴ * Pj * K' * σ = K'ᴴ * (Pj * K' * σ) by simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm]
    have e2 : Pj * K' * σ * K'ᴴ * Pj = Pj * (K' * τ * K'ᴴ) * Pj := by
      calc Pj * K' * σ * K'ᴴ * Pj = (Pj * K' * σ) * K'ᴴ * Pj := rfl
        _ = Pj * K' * Pj * (σ * K'ᴴ * Pj) := by rw [hc]; simp only [Matrix.mul_assoc]
        _ = Pj * K' * Pj * (σ * Pj * K'ᴴ * Pj) := by rw [ha]
        _ = Pj * (K' * τ * K'ᴴ) * Pj := by simp only [hτ, Matrix.mul_assoc]
    rw [e1, ← e2, Matrix.trace_mul_comm (Pj * K' * σ * K'ᴴ) Pj]
    simp only [← Matrix.mul_assoc]
    rw [hQQ]
  have hterm : ∀ r, ((K r)ᴴ * Pj * K r * σ).trace = (Pj * (K r * τ * (K r)ᴴ) * Pj).trace :=
    fun r ↦ key _ (hcomm r) (hadj r)
  have hproj : ∀ A : Matrix (Unit × HwReg X Z M') (Unit × HwReg X Z M') ℂ, A.PosSemidef →
      (Pj * A * Pj).trace.re ≤ A.trace.re := by
    intro A hA
    have hdec : A.trace = (Pj * A * Pj).trace + ((1 - Pj) * A * (1 - Pj)).trace := by
      have h1 : ((1 - Pj) * A * (1 - Pj)).trace = A.trace - (Pj * A).trace - (A * Pj).trace +
          (Pj * A * Pj).trace := by
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
          Matrix.trace_sub]
        ring
      have h2 : (A * Pj).trace = (Pj * A).trace := Matrix.trace_mul_comm A Pj
      have h3 : (Pj * A * Pj).trace = (Pj * A).trace := by
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQQ]
      rw [h1, h2, h3]
      ring
    have hnn : 0 ≤ ((1 - Pj) * A * (1 - Pj)).trace.re := by
      have h := hA.mul_mul_conjTranspose_same (1 - Pj)
      rw [conjTranspose_sub, conjTranspose_one, hQ] at h
      exact h.trace_re_nonneg
    rw [hdec, Complex.add_re]
    linarith
  rw [tsum_potential_conj S _ hσ, ← hPj]
  have hpot : QuantumRuntime.potential (hwProjector S) σ = ENNReal.ofReal τ.trace.re := by
    rw [QuantumRuntime.potential, MatrixMap.amplifyLeft_conj, one_kronecker_hwProjector,
      MatrixMap.conj_apply, hQ]
  rw [hpot]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  simp only [hterm]
  calc ∑ r, (Pj * (K r * τ * (K r)ᴴ) * Pj).trace.re
      ≤ ∑ r, (K r * τ * (K r)ᴴ).trace.re :=
        Finset.sum_le_sum fun r _ ↦ hproj _ (hτp.mul_mul_conjTranspose_same _)
    _ = τ.trace.re := by
        have hc : ∀ r, (K r * τ * (K r)ᴴ).trace = ((K r)ᴴ * K r * τ).trace := fun r ↦ by
          rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
        rw [← Complex.re_sum]
        congr 1
        simp only [hc]
        rw [← Matrix.trace_sum, ← Finset.sum_mul, hK, Matrix.one_mul]

omit [Fintype Val] [DecidableEq Val] in
/-- **A record call never raises the event weight.** -/
theorem tsum_potential_rec_badC (T : Finset (CSrc ch))
    {σ : Matrix (Unit × HwReg HashOutput HashDomain (CMem ch))
      (Unit × HwReg HashOutput HashDomain (CMem ch)) ℂ} (hσ : σ.PosSemidef) :
    ∑' r, QuantumRuntime.potential (hwProjector (BadC P θ))
        (MatrixMap.conj (recKraus (X := HashOutput) (Z := HashDomain) T r) σ) ≤
      QuantumRuntime.potential (hwProjector (BadC P θ)) σ :=
  tsum_potential_kraus_le_of_into (BadC P θ) _ (sum_recKraus T) (fun r q' q hK hq ↦ by
    have he := Quantum.Xmss.Assembly.eq_of_recKraus_ne_zero (u := q.1) (u' := q'.1) (s := q.2)
      (s' := q'.2) hK
    rw [he] at hq
    exact mem_badC_of_record P θ q.2 T hq) hσ

omit [Fintype Val] [DecidableEq Val] in
/-- **A program of an honest cell whose source is in the label never raises the event weight.** -/
theorem tsum_potential_prog_badC (hinj : CellInj ch P) (q : CPos ch) (v : HashOutput)
    {σ : Matrix (Unit × HwReg HashOutput HashDomain (CMem ch))
      (Unit × HwReg HashOutput HashDomain (CMem ch)) ℂ} (hσ : σ.PosSemidef)
    (hsupp : QuerySupportedOn (fun m : Unit × HwReg HashOutput HashDomain (CMem ch) ↦ m.2)
      {s | srcOf q.1 q.2 q.2.isLt.le ∈ s.2.2.1} σ) :
    ∑' r, QuantumRuntime.potential (hwProjector (BadC P θ))
        (MatrixMap.conj (hwProgKraus (.programH (cellOf P θ q) v) r) σ) ≤
      QuantumRuntime.potential (hwProjector (BadC P θ)) σ := by
  refine (potential_kraus_le (BadC P θ) (hwProgKraus _) (sum_hwProgKraus _) 0 (by simp)
    (by simp) σ hσ).trans ?_
  have hf := flipCost_prog_le (BadC P θ) (.programH (cellOf P θ q) v) hσ
  have h0 : (∑ q' : Unit × HwReg HashOutput HashDomain (CMem ch),
      if q'.2 ∉ BadC P θ ∧ progMap (.programH (cellOf P θ q) v) q'.2 ∈ BadC P θ then
        (σ q' q').re else 0) = 0 :=
    Finset.sum_eq_zero fun q' _ ↦ by
      by_cases hq : σ q' q' = 0
      · simp [hq]
      · exact ite_eq_right fun h ↦ absurd h.2
          (not_mem_badC_progMap P θ hinj q v (hsupp q' q' hq).1 h.1)
  rw [h0, ENNReal.ofReal_zero] at hf
  rw [nonpos_iff_eq_zero.mp hf, add_zero]

end costs

/-! ## The event bound -/

section bound

open Quantum.Xmss.Assembly (ModedP NoBot decR runtimeRH runtimeR realizeT recKraus conjReg_branch
  forallQueries_of_modedP_sguard)
open Quantum.Sponge (hwProjector hwReadKraus hwProgKraus compressReg spongeHardwired hwEmpty
  spongeHardwiredRuntime_step_sponge spongeHardwiredRuntime_step_read
  spongeHardwiredRuntime_step_prog readNoBot_of_noBot portCharge)

variable [Fintype J] [DecidableEq J] [Fintype Val] [DecidableEq Val] [Inhabited Val]
  (P : Par) (θ : (s : CSrc ch) → CD ch s)

omit [Fintype Val] [DecidableEq Val] [Inhabited Val] in
theorem le_sq_of_rpow_inv_two_le {a b : ℝ≥0∞} (h : a ^ (2⁻¹ : ℝ) ≤ b) : a ≤ b ^ 2 := by
  calc a = (a ^ (2⁻¹ : ℝ)) ^ 2 := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ b ^ 2 := by gcongr

omit [Fintype Val] [DecidableEq Val] [Inhabited Val] in
theorem le_sq_add_rpow (a b : ℝ≥0∞) : a ≤ (a ^ (2⁻¹ : ℝ) + b) ^ 2 :=
  le_sq_of_rpow_inv_two_le le_self_add

omit [Inhabited Val] in
/-- **The cost of one call**: sponge calls and reads of step cells `√(gradeEta F)` (times their
charge, at least `1`), every other call nothing. -/
theorem tsum_potential_step_cpre (hinj : CellInj ch P) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ ch.step.trunc y = o).card ≤ F)
    (κ : (RSpec ch).Port → ℕ) (hκs : ∀ p, 1 ≤ κ (.inl (.inl (.inl p))))
    (hκr : ∀ z u, StepCell ch P z → 1 ≤ κ (.inl (.inl (.inr (.readH z u)))))
    (m₀ : CMem ch) (i : (RSpec ch).Port)
    {σ : Matrix ((RSpec ch).In i × HwReg HashOutput HashDomain (CMem ch))
      ((RSpec ch).In i × HwReg HashOutput HashDomain (CMem ch)) ℂ} (hσ : σ.PosSemidef)
    (hP : ∃ μ, okZ P θ μ i ∧ QuerySupportedOn
      (fun m : (RSpec ch).In i × HwReg HashOutput HashDomain (CMem ch) ↦ m.2) (InvD μ)
      (MatrixMap.conj ((1 : Matrix ((RSpec ch).In i) ((RSpec ch).In i) ℂ) ⊗ₖ
        compressReg HashOutput HashDomain (Finset (CSrc ch) × JMem)) σ)) :
    ∑' r, QuantumRuntime.potential (hwProjector (BadC P θ))
        (((runtimeR (X := HashOutput) (Z := HashDomain) m₀).step i).branch r σ) ≤
      (QuantumRuntime.potential (hwProjector (BadC P θ)) σ ^ (2⁻¹ : ℝ) + κ i *
        (ENNReal.ofReal (gradeEta HashOutput F) * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ)) ^ 2 := by
  obtain ⟨μ, hok, hsupp⟩ := hP
  rcases μ with _ | m
  · have h0 := eq_zero_of_querySupportedOn_empty hsupp
    have hσ0 : σ = 0 := by rw [← conj_compressReg_conj_compressReg σ, h0, map_zero]
    refine (ENNReal.tsum_eq_zero.mpr fun r ↦ ?_).trans_le zero_le
    have hb : ((runtimeR (X := HashOutput) (Z := HashDomain) m₀).step i).branch r σ = 0 := by
      rw [hσ0]
      exact map_zero _
    rw [hb]
    exact (QuantumRuntime.potential_eq _ _).trans ((congrArg
      (fun M ↦ ENNReal.ofReal (Matrix.trace M : ℂ).re) (Matrix.mul_zero _)).trans (by simp))
  have hmem : QuerySupportedOn
      (fun m' : (RSpec ch).In i × HwReg HashOutput HashDomain (CMem ch) ↦ m'.2)
      {s | s.2.2 = m} σ := by
    have h := querySupportedOn_conj_compressReg (S := {s | s.2.2 = m})
      (fun s s' he hs ↦ by change s'.2.2 = m; rw [← he]; exact hs) (hsupp.imp fun s hs ↦ hs.2)
    rwa [conj_compressReg_conj_compressReg] at h
  rcases i with ((p | c) | c) | T
  · change ∑' r : Unit, _ ≤ _
    rw [tsum_eq_single () fun r hr ↦ absurd (Subsingleton.elim r ()) hr]
    have hb : ((runtimeR (X := HashOutput) (Z := HashDomain) m₀).step
        (.inl (.inl (.inl p)))).branch () σ = MatrixMap.conj ((spongeHardwired HashOutput
          HashDomain (hwEmpty HashOutput HashDomain) m₀).U p) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty HashOutput HashDomain)
        m₀ p ()) σ
    rw [hb]
    refine le_sq_of_rpow_inv_two_le ((potential_sponge_badC_le P θ hinj hF m₀ p hσ).trans ?_)
    exact add_le_add le_rfl (le_mul_of_one_le_left zero_le (by exact_mod_cast hκs p))
  · cases c with
    | readH z u =>
      have hb : ∀ r, ((runtimeR (X := HashOutput) (Z := HashDomain) m₀).step
          (.inl (.inl (.inr (.readH z u))))).branch r σ =
            MatrixMap.conj (hwReadKraus (.readH z u) r) σ := fun r ↦
        LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty HashOutput HashDomain)
          m₀ (.readH z u) r) σ
      simp only [hb]
      by_cases hz : StepCell ch P z
      · refine (tsum_potential_read_badC P θ hinj hF hok hσ
          (readNoBot_of_noBot _ (hsupp.imp fun s hs ↦ hs.1))).trans ?_
        refine pow_le_pow_left₀ zero_le (add_le_add le_rfl ?_) 2
        rw [ENNReal.ofReal_mul (gradeEta_nonneg _ _)]
        exact le_mul_of_one_le_left zero_le (by exact_mod_cast hκr z u hz)
      · have h0 := readFlip_eq_zero (BadC P θ) (readInvisible_badC P θ hz hok) σ hσ
        unfold readFlip at h0
        rw [tsub_eq_zero_iff_le] at h0
        exact h0.trans (le_sq_add_rpow _ _)
    | readK _ _ => exact hok.elim
    | readK' _ _ => exact hok.elim
  · obtain ⟨q, rfl, hL⟩ := hok
    have hb : ∀ r, ((runtimeR (X := HashOutput) (Z := HashDomain) m₀).step
        (.inl (.inr (.programH (cellOf P θ q) (θ (.inr q)))))).branch r σ =
          MatrixMap.conj (hwProgKraus (.programH (cellOf P θ q) (θ (.inr q))) r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty HashOutput HashDomain)
        m₀ (.programH (cellOf P θ q) (θ (.inr q))) r) σ
    simp only [hb]
    exact (tsum_potential_prog_badC P θ hinj q _ hσ (hmem.imp fun s hs ↦ by
      change srcOf q.1 q.2 q.2.isLt.le ∈ s.2.2.2.1
      change s.2.2.2 = m at hs
      rw [hs]
      exact hL)).trans (le_sq_add_rpow _ _)
  · change ∑' r, QuantumRuntime.potential (hwProjector (BadC P θ))
      (MatrixMap.conj (recKraus (X := HashOutput) (Z := HashDomain) T r) σ) ≤ _
    exact (tsum_potential_rec_badC P θ T hσ).trans (le_sq_add_rpow _ _)

omit [Inhabited Val] in
/-- **The calls of a moded realized program** are presented operators on the decompressed
invariant of a mode allowing them. -/
theorem forallQueries_cpre (m₀ : CMem ch) {Ω : QReg → Type*}
    {fin : (Σ u, Ω u) → Option (CMem ch) → Prop} {A : QReg}
    (x : QuantumComp LocalSig.instruments.{0} (RSpec ch) Ω A)
    (hx : ModedP (okZ P θ) nxZ fin (some m₀) x) (ρ : Matrix A A ℂ) :
    (runtimeR (X := HashOutput) (Z := HashDomain) m₀).ForallQueries .instruments
      (fun i E τ ↦ ∃ μ, okZ P θ μ i ∧ QuerySupportedOn
        (fun m : (RSpec ch).In i × HwReg HashOutput HashDomain (CMem ch) ↦ m.2) (InvD μ)
        (MatrixMap.conj ((1 : Matrix ((RSpec ch).In i) ((RSpec ch).In i) ℂ) ⊗ₖ
          compressReg HashOutput HashDomain (Finset (CSrc ch) × JMem))
          (MatrixMap.traceRight _ E τ))) x
      (ρ ⊗ₖ (runtimeR (X := HashOutput) (Z := HashDomain) m₀).init.matrix) := by
  have h1 := forallQueries_of_modedP_sguard (decR (X := HashOutput) (Z := HashDomain) m₀)
    .instruments InvD (fun _ ↦ Set.univ) (fun μ i r σ hi hσ ↦
      decR_step_invD P θ m₀ μ i r σ hi (hσ.mono Set.inter_subset_left)) x (some m₀) hx
    (ρ := MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ
      compressReg HashOutput HashDomain (Finset (CSrc ch) × JMem))
      (ρ ⊗ₖ (runtimeR (X := HashOutput) (Z := HashDomain) m₀).init.matrix))
    (Quantum.Xmss.Hybrid.forallQueries_of_forall _ _ (fun _ _ _ ↦ querySupportedOn_univ _ _) _ _)
    (invD_init m₀ ρ)
  have hsim : ∀ i r, ((runtimeR (X := HashOutput) (Z := HashDomain) m₀).step i).branch r ∘ₗ
      (MatrixMap.conj (compressReg HashOutput HashDomain (Finset (CSrc ch) × JMem))).amplifyLeft
        ((RSpec ch).In i) =
      (MatrixMap.conj (compressReg HashOutput HashDomain (Finset (CSrc ch) × JMem))).amplifyLeft
        ((RSpec ch).Out i) ∘ₗ
        ((decR (X := HashOutput) (Z := HashDomain) m₀).step i).branch r := by
    intro i r
    rw [conjReg_branch, MatrixMap.amplifyLeft_conj]
    exact LinearMap.ext fun τ ↦ (conj_compressReg_conj_compressReg _).symm
  have h2 := QuantumRuntime.ForallQueries.of_simulation .instruments
    (R₁ := decR (X := HashOutput) (Z := HashDomain) m₀)
    (R₂ := runtimeR (X := HashOutput) (Z := HashDomain) m₀)
    (V := MatrixMap.conj (compressReg HashOutput HashDomain (Finset (CSrc ch) × JMem))) hsim
    (P₂ := fun i E τ ↦ ∃ μ, okZ P θ μ i ∧ QuerySupportedOn
      (fun m : (RSpec ch).In i × HwReg HashOutput HashDomain (CMem ch) ↦ m.2) (InvD μ)
      (MatrixMap.conj ((1 : Matrix ((RSpec ch).In i) ((RSpec ch).In i) ℂ) ⊗ₖ
        compressReg HashOutput HashDomain (Finset (CSrc ch) × JMem)) (MatrixMap.traceRight _ E τ)))
    (fun i E τ hτ ↦ by
      obtain ⟨μ, hi, hτ⟩ := hτ
      refine ⟨μ, hi, ?_⟩
      have e := LinearMap.congr_fun (MatrixMap.traceRight_comp_amplify (R := E)
        ((MatrixMap.conj (compressReg HashOutput HashDomain (Finset (CSrc ch) × JMem))).amplifyLeft
          ((RSpec ch).In i))) τ
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at e
      erw [e]
      rw [MatrixMap.amplifyLeft_conj, conj_compressReg_conj_compressReg]
      exact Quantum.Xmss.Assembly.querySupportedOn_traceRight hτ) h1
  have e : (MatrixMap.conj (compressReg HashOutput HashDomain
      (Finset (CSrc ch) × JMem))).amplifyLeft A (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ
        compressReg HashOutput HashDomain (Finset (CSrc ch) × JMem))
        (ρ ⊗ₖ (runtimeR (X := HashOutput) (Z := HashDomain) m₀).init.matrix)) =
      ρ ⊗ₖ (runtimeR (X := HashOutput) (Z := HashDomain) m₀).init.matrix := by
    rw [MatrixMap.amplifyLeft_conj]
    exact conj_compressReg_conj_compressReg _
  rw [← e]
  exact h2

omit [Fintype Val] [DecidableEq Val] [Inhabited Val] in
/-- The event starts empty. -/
theorem potential_init_badC :
    QuantumRuntime.potential (hwProjector (BadC P θ)) ((SubState.basis ()).matrix ⊗ₖ
      (runtimeR (X := HashOutput) (Z := HashDomain) ((∅, ∅) : CMem ch)).init.matrix) = 0 := by
  have hnot : (((Database.empty, Database.empty, Database.empty), hwEmpty HashOutput HashDomain,
      ((∅, ∅) : CMem ch)) : HwReg HashOutput HashDomain (CMem ch)) ∉ BadC P θ := by
    rintro (⟨x, y, hxy, -⟩ | ⟨zy, hzy, -⟩)
    · exact absurd hxy (by simp [Quantum.Qrom.unionH, hwEmpty])
    · exact absurd hzy (Finset.notMem_empty _)
  have hz : hwProjector (BadC P θ) * (SubState.basis (((Database.empty, Database.empty,
      Database.empty), hwEmpty HashOutput HashDomain, ((∅, ∅) : CMem ch)) :
        HwReg HashOutput HashDomain (CMem ch))).matrix = 0 := by
    rw [hwProjector, labelProjector, SubState.matrix_basis]
    ext a b
    rw [diagonal_mul, Matrix.single_apply, Matrix.zero_apply]
    by_cases h : ((Database.empty, Database.empty, Database.empty), hwEmpty HashOutput HashDomain,
        ((∅, ∅) : CMem ch)) = a ∧ ((Database.empty, Database.empty, Database.empty),
          hwEmpty HashOutput HashDomain, ((∅, ∅) : CMem ch)) = b
    · rcases h with ⟨rfl, rfl⟩
      simp [hnot]
    · simp [h]
  change QuantumRuntime.potential (hwProjector (BadC P θ)) ((SubState.basis ()).matrix ⊗ₖ
    (SubState.basis (((Database.empty, Database.empty, Database.empty),
      hwEmpty HashOutput HashDomain, ((∅, ∅) : CMem ch)) :
        HwReg HashOutput HashDomain (CMem ch))).matrix) = 0
  rw [QuantumRuntime.potential, MatrixMap.amplifyLeft_conj, MatrixMap.conj_apply,
    ← mul_kronecker_mul, hz, kronecker_zero, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re,
    ENNReal.ofReal_zero]

/-- **Runtime 2's win on the CPRE template game** (Part C): with `N` the charge of the realized
game for weights `κ` at least `1` at the sponge calls and at the reads of step cells,
`p₂ ≤ N² · gradeEta F`. -/
theorem p2_cpre_le (hlen : StepLen ch) (hinj : CellInj ch P) {F : ℕ}
    (hF : ∀ o, (Finset.univ.filter fun y ↦ ch.step.trunc y = o).card ≤ F)
    (κ : (RSpec ch).Port → ℕ) (hκs : ∀ p, 1 ≤ κ (.inl (.inl (.inl p))))
    (hκr : ∀ z u, StepCell ch P z → 1 ≤ κ (.inl (.inl (.inr (.readH z u)))))
    (C : TwColl Par Tw Fn Msg Out) {Q St S0 Fo : Type} {R : OracleSpec.{0, 0} Q}
    (pre : OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out) S0)
    (adv : S0 → QComp (advSpec romWorld.spec R) (QReg.of Unit) (QReg.of Unit) Fo)
    (st0 : S0 → St) (σ : HHandler romWorld R (CQ Par Tw J Val Fn Msg Out) St)
    (post : S0 → Fo → St → OracleComp (romWorld.Oracles + CQ Par Tw J Val Fn Msg Out)
      (J × ℕ × Val)) {N : ℕ}
    (hN : IFreeM.IsChargeBound (realizeT θ (cpreT C P pre adv st0 σ post)) (portCharge κ) N) :
    (runtimeR (X := HashOutput) (Z := HashDomain) ((∅, ∅) : CMem ch)).evalDistMap .instruments
        (realizeT θ (cpreT C P pre adv st0 σ post)) (SubState.basis ()) (fun p ↦ p.2.2) {true} ≤
      (N : ℝ≥0∞) ^ 2 * ENNReal.ofReal (gradeEta HashOutput F) := by
  refine (p2_le_eventWeight P θ hlen C pre adv st0 σ post).trans ?_
  have hpi := potential_init_badC (ch := ch) P θ
  set m₀ : CMem ch := (∅, ∅)
  set x := realizeT θ (cpreT C P pre adv st0 σ post)
  have hρ : ((SubState.basis ()).matrix ⊗ₖ
      (runtimeR (X := HashOutput) (Z := HashDomain) m₀).init.matrix).PosSemidef :=
    ((SubState.basis ()).prod (runtimeR (X := HashOutput) (Z := HashDomain) m₀).init).posSemidef
  have htr : ENNReal.ofReal ((SubState.basis ()).matrix ⊗ₖ
      (runtimeR (X := HashOutput) (Z := HashDomain) m₀).init.matrix).trace.re ≤ 1 := by
    rw [← SubState.matrix_prod]
    exact ENNReal.ofReal_le_one.mpr ((SubState.basis ()).prod
      (runtimeR (X := HashOutput) (Z := HashDomain) m₀).init).trace_re_le_one
  have hP := forallQueries_cpre P θ m₀ x
    (modedP_realizeT_cpre P θ _ (modedP_cpreT P θ hlen C pre adv st0 σ post))
    (SubState.basis ()).matrix
  have h := rpow_inv_two_eventWeight_le_weighted
    (runtimeR (X := HashOutput) (Z := HashDomain) m₀) .instruments (hwProjector (BadC P θ)) κ
    (fun i E τ ↦ ∃ μ, okZ P θ μ i ∧ QuerySupportedOn
      (fun m : (RSpec ch).In i × HwReg HashOutput HashDomain (CMem ch) ↦ m.2) (InvD μ)
      (MatrixMap.conj ((1 : Matrix ((RSpec ch).In i) ((RSpec ch).In i) ℂ) ⊗ₖ
        compressReg HashOutput HashDomain (Finset (CSrc ch) × JMem)) (MatrixMap.traceRight _ E τ)))
    (ENNReal.ofReal (gradeEta HashOutput F)) (fun _ _ ↦ 0)
    (fun i E τ hτ hτp ↦ by
      rw [add_zero]
      exact tsum_potential_step_cpre P θ hinj hF κ hκs hκr m₀ i hτp.traceRight hτ)
    x N hN hρ hP
  have hw0 : (runtimeR (X := HashOutput) (Z := HashDomain) m₀).totalWeight .instruments
      (fun _ _ ↦ 0) x ((SubState.basis ()).matrix ⊗ₖ
        (runtimeR (X := HashOutput) (Z := HashDomain) m₀).init.matrix) = 0 := by
    simpa using Quantum.Xmss.Hybrid.totalWeight_const_mul_weight
      (runtimeR (X := HashOutput) (Z := HashDomain) m₀) .instruments 0 (fun _ _ ↦ 0) x
      ((SubState.basis ()).matrix ⊗ₖ
        (runtimeR (X := HashOutput) (Z := HashDomain) m₀).init.matrix)
  have hz : ∀ b c : ℝ≥0∞, c = 0 → b + c ^ (2⁻¹ : ℝ) = b := fun b c hc ↦ by
    rw [hc, ENNReal.zero_rpow_of_pos (by norm_num), add_zero]
  refine (le_sq_of_rpow_inv_two_le (h.trans_eq
    (hz _ _ ((congrArg₂ (· + ·) hpi hw0).trans (add_zero 0))))).trans ?_
  rw [mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  have e2 : ((2⁻¹ : ℝ) * ((2 : ℕ) : ℝ)) = 1 := by norm_num
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, e2, ENNReal.rpow_one]
  exact mul_le_of_le_one_right zero_le htr

end bound

end Quantum.StdModel.Qrom.CpreQ

end
