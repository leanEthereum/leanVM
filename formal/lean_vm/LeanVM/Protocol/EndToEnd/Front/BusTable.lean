/-
  LeanVM.Protocol.EndToEnd.Front.BusTable

  The bus phase followed by the table sumcheck, specified from the commitment's doom to the table
  seam on the wire, and the table seam read as the doom the public-input bridge starts from.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.TablePhase
public import LeanVM.Protocol.EndToEnd.Front.LayoutBridgeB
public import LeanVM.Protocol.EndToEnd.Front.CommitDoom
public import LeanVM.Protocol.EndToEnd.Complete.BusLayout

/-!
# The bus phase and the table sumcheck

`busTableSpec` composes `busThenSpec` with `tablePhaseSpec` for the program's
`do let bus ← verifyBusBalance .computed layout; tablePhase layout bus`, from the commitment's doom
(`Seam.commit` on the candidates) to the table seam on the wire (`TablePost`). It needs the table phase's
identities (`TableFid`) for every read of the right shape.

`tablePost_pubPre`: at the verifier's layout and the leanISA instance with the deployed Flock
slots, the table seam on the wire is the doom the public-input bridge starts from (`PubPre`): no
candidate satisfies the program's column claims, the public lines and the Flock predicate.
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
  w.point.length = I.μBus ∧ w.values.length = 3 ∧ w.memory.length = 3

instance (w : BusWit) : Decidable (w.Shaped I) := inferInstanceAs (Decidable (_ ∧ _))

/-- **The bus phase, then the table sumcheck**: from the commitment's doom to the table seam on
the wire. -/
noncomputable def busTableSpec (colOf : I.ColumnId → ℕ)
    (fid : ∀ w : BusWit, w.Shaped I → TableFid I hI input layout colOf w) (hd : I.d ≤ 2)
    {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀)
    (hμ : I.μBus ≠ 0)
    (hdepth : (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth = I.μBus)
    (hab : abError I L₀ < 1) (he4 : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax)
    {T : ℝ≥0∞} (he3 : roundError L₀ 3 + T ≤ εmax) (hTf : T ≤ εmax)
    (hxi : xiError I L₀ + sumcheckLead (List.replicate (layout.tableLogHeights.foldl max 0) none)
      T ≤ εmax) :
    Spec ((verifyBusBalance .computed layout).bind (tablePhase layout)) (HDoom cands (Seam.commit I) input)
      (TablePost I cands input colOf) εmax (abError I L₀ + 0) T :=
  busThenSpec I hI cands input layout hxi
    (fun w ↦ if hw : w.Shaped I then
      tablePhaseSpec I hI cands input layout colOf w (fid w hw) hd hfin hcard he3 hTf
    else specOfFalse fun _ hp ↦ hw ⟨hp.1, hp.2.1, hp.2.2.1⟩)
    hfin hcard hμ hdepth hab he4 hT hlam

/-! ## The table seam as the public-input bridge's doom -/

section LeanIsa

open LeanVM.Protocol.LeanIsa

variable (F : FlockSpec) (prog : Program) (s : Sizes)
  (cands' : Word → Set (∀ i, TheOracle (leanIsaInstance F prog s) i))
  (input' : PublicInput)

/-- **The table seam on the wire is the public-input bridge's doom**: at the verifier's layout,
with the deployed Flock slots, if the table seam holds of no candidate at the protocol's output,
then no candidate of `C` satisfies the program's column claims, the public lines and the Flock
predicate, `C` being read off the same commitment. -/
theorem tablePost_pubPre (hF : F.slot = Blake2sFlock.slots)
    (C : List Ev → Set (Column (verifierLayout prog s).stackLog))
    (hC : ∀ h q, q ∈ C h → ∀ W, firstWord h = some W → (fun _ ↦ toI prog s q) ∈ cands' W)
    (claims : List Verifier.ColumnClaim) (h : List Ev)
    (hpost : TablePost (leanIsaInstance F prog s) cands' input' pyCol claims h) :
    PubPre F prog s (verifierLayout prog s) C (toI prog s) claims input' h := by
  obtain ⟨W, tout, hW, hR, hin, hcl⟩ := hpost
  rintro q hq ⟨hcols, hpl, haux⟩
  refine hR _ (hC h q hq W hW) ⟨fun c hc ↦ ?_, by rw [hin]; exact hpl, haux⟩
  have hs := hcols _ (hcl c hc)
  rw [holds_castColumn (stackLog_verifierLayout prog s)] at hs
  exact (onStack_holds_iff prog s F hF c.col c.point c.value (toI prog s q)).mp hs

/-- The candidates of a committed word as oracles of the instance. -/
def candsOf (ρ : ℕ) (A : ℕ → ℕ → ℕ) (W : Word) :
    Set (∀ i, TheOracle (leanIsaInstance F prog s) i) :=
  (fun q ↦ fun _ ↦ q) '' EndToEnd.Candidates (leanIsaμ prog s) ρ (A (leanIsaμ prog s) ρ) W

/-- The candidates of the history's first commitment, read on the layout's stack. -/
def candsL (ρ : ℕ) (A : ℕ → ℕ → ℕ) (h : List Ev) : Set (Column (verifierLayout prog s).stackLog) :=
  {q | ∃ W, firstWord h = some W ∧
    toI prog s q ∈ EndToEnd.Candidates (leanIsaμ prog s) ρ (A (leanIsaμ prog s) ρ) W}

theorem candsL_mem (ρ : ℕ) (A : ℕ → ℕ → ℕ) :
    ∀ h q, q ∈ candsL prog s ρ A h → ∀ W, firstWord h = some W →
      (fun _ ↦ toI prog s q) ∈ candsOf F prog s ρ A W := by
  rintro h q ⟨W', hW', hq⟩ W hW
  rw [hW] at hW'
  cases hW'
  exact ⟨_, hq, rfl⟩

/-- The candidates as oracles are as many as the candidates. -/
theorem candsOf_ncard (ρ : ℕ) (A : ℕ → ℕ → ℕ) (W : Word) :
    (candsOf F prog s ρ A W).ncard =
      (EndToEnd.Candidates (leanIsaμ prog s) ρ (A (leanIsaμ prog s) ρ) W).ncard :=
  Set.ncard_image_of_injective _ fun _ _ h ↦ congrFun h 0

/-- Every opcode table has a push block, at its row count. -/
theorem exists_pushBlock (s : Sizes) (t : Fin 6) :
    ∃ b ∈ Complete.pushBlocks s, b.owner = t.val ∧ b.rows = s.rows t := by
  obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil (Complete.pySide_push_ne_nil t)
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
    (hD : CommitDoom F prog input' A (verifierLayout prog s, ρ) h) :
    HDoom (candsOf F prog s ρ A) (Seam.commit (leanIsaInstance F prog s)) input' h := by
  obtain ⟨s', W, hs, hW, hq⟩ := hD
  obtain rfl := verifierLayout_injective prog hs.symm
  exact ⟨W, hW, by rintro _ ⟨q, hq', rfl⟩ hin; exact hq q hq' hin⟩

end LeanIsa

end
end LeanVM.Protocol.EndToEnd.Front
