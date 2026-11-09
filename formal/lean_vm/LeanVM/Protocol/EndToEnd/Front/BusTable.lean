/-
  LeanVM.Protocol.EndToEnd.Front.BusTable

  The bus phase followed by the table sumcheck, specified from the commitment's doom to the table
  seam on the wire, and the commitment's doom as the bus phase's.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Protocol.EndToEnd.Front.TablePhase
public import LeanVM.Protocol.EndToEnd.Front.LayoutBridgeB
public import LeanVM.Protocol.EndToEnd.Front.CommitDoom
public import LeanVM.Protocol.EndToEnd.Complete.BusLayout

/-!
# The bus phase and the table sumcheck

`busTableSpec` composes `busThenSpec` with `tablePhaseSpec` for the program's
`do let bus ← verifyBusBalance computedBytecodeValue layout; tablePhase layout bus`, from the commitment's doom
(`Seam.commit` on the candidates) to the table seam on the wire (`TablePost`). It needs the table phase's
identities (`TableFid`) for every read of the right shape.

`commitDoom_hdoom`: at the verifier's layout, the commitment's doom (`CommitDoom`) is the bus
phase's: at the sizes the layout was built from (`verifierLayout_injective`), no candidate of the
committed word, as an oracle of the leanISA instance (`candsOf`), satisfies `M3Holds`.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

@[expose] public section

variable (I : M3Instance) (hI : Bus.Conditions I) (cands : Word → Set (∀ i, TheOracle I i))
  (input : I.Stmt) (layout : Verifier.Layout) {εmax : ℝ≥0∞}

/-- What a read of the bus phase of the right shape is. -/
def BusWit.Shaped (w : BusWit) : Prop :=
  w.point.length = I.μBus ∧ w.values.length = 3 ∧ w.memory.length = 2

instance (w : BusWit) : Decidable (w.Shaped I) := inferInstanceAs (Decidable (_ ∧ _))

/-- A lead whose discount by a grind of `b` bits is within `εmax` is within it at `b = 0`. -/
theorem grindLead_le_of_discount {b : ℕ} {X : ℝ≥0∞} (h : (2 : ℝ≥0∞)⁻¹ ^ b * X ≤ εmax) :
    (if b = 0 then X else 0) ≤ εmax := by
  split_ifs with hb
  · simpa [hb] using h
  · exact zero_le

/-- **The bus phase, then the table sumcheck**: from the commitment's doom to the table seam on
the wire. The side conditions are the bus phase's (`busThenSpec`: the fingerprint challenges'
discounted error `hab`, the GKR's, the bytecode share's `hs`) and the table phase's
(`tablePhaseSpec`: `ξ`'s discounted error `hxi`, the rounds' `he3`). -/
noncomputable def busTableSpec (colOf : I.ColumnId → ℕ)
    (fid : ∀ w : BusWit, w.Shaped I → TableFid I hI input layout colOf w) (hd : I.d ≤ 2)
    {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀)
    (hμ : I.μBus ≠ 0)
    (hdepth : (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth = I.μBus)
    (hbc : layout.bytecode.length = 2 ^ (layout.logBytecode + busBits))
    (hlb : layout.logBytecode ≤ I.μBus) (o₀ : ∀ i, TheOracle I i)
    (hlt : abError I L₀ < 1)
    (hab : (2 : ℝ≥0∞)⁻¹ ^ busGrindingBits I.μBus * (abError I L₀ + 0) ≤ εmax)
    (he4 : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax)
    (hs : roundError 1 2 + 0 ≤ εmax)
    {T : ℝ≥0∞} (he3 : roundError L₀ 3 + T ≤ εmax) (hTf : T ≤ εmax)
    (hxi : (2 : ℝ≥0∞)⁻¹ ^ xiGrindBits * (xiError I L₀ +
      sumcheckLead (List.replicate (layout.tableLogHeights.foldl max 0) none) T) ≤ εmax) :
    Spec ((verifyBusBalance computedBytecodeValue layout).bind (tablePhaseClaims layout))
      (HDoom cands (Seam.commit I) input) (TablePost I cands input colOf) εmax
      (if busGrindingBits I.μBus = 0 then abError I L₀ + 0 else 0) T :=
  busThenSpec I hI cands input layout (grindLead_le_of_discount hxi)
    (fun w ↦ if hw : w.Shaped I then
      tablePhaseSpec I hI cands input layout colOf w (fid w hw) hd hfin hcard he3 hTf hxi
    else specOfFalse fun _ hp ↦ hw ⟨hp.1, hp.2.1, hp.2.2.1⟩)
    hfin hcard hμ hdepth hbc hlb o₀ hlt hab he4 hT hlam hs

/-! ## The commitment's doom at the leanISA instance -/

section LeanIsa

open LeanVM.Protocol.LeanIsa

variable (prog : LeanIsaProgram) (s : Sizes) (input' : PublicInput)

/-- The candidates of a committed word as oracles of the instance. -/
def candsOf (ρ : ℕ) (A : ℕ → ℕ → ℕ) (W : Word) :
    Set (∀ i, TheOracle (leanIsaInstance prog s) i) :=
  (fun q ↦ fun _ ↦ q) '' EndToEnd.Candidates (leanIsaμ prog s) ρ (A (leanIsaμ prog s) ρ) W

/-- The candidates of the history's first commitment, read on the layout's stack. -/
def candsL (ρ : ℕ) (A : ℕ → ℕ → ℕ) (h : List Ev) : Set (Column (verifierLayout prog s).stackLog) :=
  {q | ∃ W, firstWord h = some W ∧
    toI prog s q ∈ EndToEnd.Candidates (leanIsaμ prog s) ρ (A (leanIsaμ prog s) ρ) W}

theorem candsL_mem (ρ : ℕ) (A : ℕ → ℕ → ℕ) :
    ∀ h q, q ∈ candsL prog s ρ A h → ∀ W, firstWord h = some W →
      (fun _ ↦ toI prog s q) ∈ candsOf prog s ρ A W := by
  rintro h q ⟨W', hW', hq⟩ W hW
  rw [hW] at hW'
  cases hW'
  exact ⟨_, hq, rfl⟩

/-- The candidates as oracles are as many as the candidates. -/
theorem candsOf_ncard (ρ : ℕ) (A : ℕ → ℕ → ℕ) (W : Word) :
    (candsOf prog s ρ A W).ncard =
      (EndToEnd.Candidates (leanIsaμ prog s) ρ (A (leanIsaμ prog s) ρ) W).ncard :=
  Set.ncard_image_of_injective _ fun _ _ h ↦ congrFun h 0

/-- Every opcode table has a push block, at its row count. -/
theorem exists_pushBlock (s : Sizes) (t : Fin 6) :
    ∃ b ∈ Complete.pushBlocks s, b.owner = t.val ∧ b.rows = s.rows t := by
  obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil (Complete.refSide_push_ne_nil t)
  refine ⟨⟨s.τ t, s.rows t, c, t⟩, ?_, rfl, rfl⟩
  rw [Complete.pushBlocks, List.mem_flatten]
  exact ⟨_, List.mem_ofFn.mpr ⟨t, rfl⟩, by rw [hc]; exact List.mem_map_of_mem List.mem_cons_self⟩

/-- A push block of an opcode table has the table's row count. -/
theorem rows_of_mem_pushBlocks (s : Sizes) {b : BusBlock} (hb : b ∈ Complete.pushBlocks s)
    (t : Fin 6) (ht : b.owner = t.val) : b.rows = s.rows t := by
  obtain ⟨t', he⟩ := Complete.pushBlocks_owned s b hb
  have : t' = t := Fin.ext (by rw [← ht, he])
  subst this
  rw [he]

/-- The verifier's layout determines the sizes: the memory's log-size, and each table's row count,
which its push blocks carry. -/
theorem verifierLayout_injective {s s' : Sizes}
    (h : verifierLayout prog s = verifierLayout prog s') : s = s' := by
  have hm : s.logMem = s'.logMem := congrArg Verifier.Layout.logMemory h
  have hp : Complete.pushBlocks s = Complete.pushBlocks s' := by
    rw [← Complete.layout_push prog s, ← Complete.layout_push prog s', h]
  have hr : ∀ t, s.rows t = s'.rows t := fun t ↦ by
    obtain ⟨b, hb, ho, hr⟩ := exists_pushBlock s t
    rw [← hr]
    exact rows_of_mem_pushBlocks s' (hp ▸ hb) t ho
  obtain ⟨m, hm0, r⟩ := s
  obtain ⟨m', hm0', r'⟩ := s'
  simp only at hm
  subst hm
  have : r = r' := funext hr
  subst this
  rfl

/-- **The commitment's doom is the bus phase's**: at the sizes the layout was built from, no
candidate oracle satisfies `M3Holds`. -/
theorem commitDoom_hdoom (A : ℕ → ℕ → ℕ) (ρ : ℕ) (h : List Ev)
    (hD : CommitDoom prog input' A (verifierLayout prog s, ρ) h) :
    HDoom (candsOf prog s ρ A) (Seam.commit (leanIsaInstance prog s)) input' h := by
  obtain ⟨s', W, hs, hW, hq⟩ := hD
  obtain rfl := verifierLayout_injective prog hs.symm
  exact ⟨W, hW, by rintro _ ⟨q, hq', rfl⟩ hin; exact hq q hq' hin⟩

end LeanIsa

end
end LeanVM.Protocol.EndToEnd.Front
