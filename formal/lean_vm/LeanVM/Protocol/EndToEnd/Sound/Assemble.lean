/-
  LeanVM.Protocol.EndToEnd.Sound.Assemble

  The specification of the whole deployed leanVM verifier program, composed from the phase
  specifications, at `εmax = 2^-128` per group of challenges, and the doom certificate it gives.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.Frame
public import LeanVM.Protocol.EndToEnd.Sound.Glue
public import LeanVM.Protocol.EndToEnd.Sound.Moves
public import LeanVM.Protocol.EndToEnd.Sound.Returns
public import LeanVM.Protocol.EndToEnd.Sound.BusDepth
public import LeanVM.Protocol.EndToEnd.Front.TableFidLeanIsa
public import LeanVM.Protocol.EndToEnd.Front.WalkFaithful
public import LeanVM.Protocol.EndToEnd.Front.LayoutSizes
public import LeanVM.Protocol.EndToEnd.Complete.Public
public import LeanVM.Protocol.Whir.Complete.Opening
public import LeanVM.Protocol.Compile.SpecRules.Cert

/-!
# The specification of the leanVM verifier

`leanVmSpec prog input` is a specification of `leanVmProgram (bytecodeWords prog)
(publicDigest input)` (`LeanVM.Protocol.Verifier`, leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) from no doom, with postcondition rejection, at
`εmax = 2^-128` and lead `0`; `leanVmCert` is its doom certificate (`Spec.toCert`). It composes,
with `Spec.bind'`:

1. the announced sizes (`readSizesSpec`, dead): no doom;
2. a case split on the announced value `a = (layout, ρ)`: unless `layout` is the verifier's layout
   at admissible sizes `s` with an admissible WHIR shape (`Good`), the rest is dead
   (`readSizes` never returns such a value, `good_of_readSizes`);
3. the stack's root (`commitSpec`), creating `CommitPost`: no candidate of the committed word at
   level 0's Johnson threshold satisfies `M3Holds` of the leanISA instance at `s`
   (`CommitDoom`), and the commitments so far are exactly the stack's, of level 0's shape;
4. the bus and the table sumcheck (`busTableSpec_leanIsa`), the public input (`pubPhaseSpec`), Flock
   (`flockBridgeSpec`) and ring switching (`ringBridgeSpec`), each framed (`Spec.frame`) with the
   shape of the commitments, which they keep since they commit nothing (`MovesOK.reach_commits`),
   and the first two with the bound on the number of claims they return (`Spec.retInv`);
5. the stacked opening (`stackedSpec`) with the deployed codes (`deployed_spec_hyps`), from ring
   switching's postcondition (`stackedPre_of_ringPost`).

The deployed table sumcheck's computations are the model's at leanISA (`tableFid_leanIsa`, for a
bus read with four fingerprint challenges, which `busTableSpec_leanIsa` carries); nothing is
assumed.

The errors are those of `phase_errors` (`L₀ = 2^18` candidates, the level-0 list bound of
`deployed_spec_hyps`): every group's escape is at most `2^-128`.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.EndToEnd.Complete (publicDigest)
open scoped ENNReal NNReal

@[expose] public section

/-! ## The parameters -/

/-- The deployed Flock specification, with the BLAKE2s circuit. -/
abbrev F₀ : FlockSpec := Blake2sFlock.blake2sFlockSpec

/-- **The per-group error**, `2^-128`. -/
noncomputable abbrev εLean : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ 128

/-- The deployed codes of level `0` of the ladder `(μ, R)`. -/
noncomputable abbrev code₀ (μ R : ℕ) : LevelCode := Whir.Params.deployedCodes μ R 0

/-- The commitments of a history are exactly the stack's, of level 0's shape. -/
abbrev StackShape (μ R : ℕ) (h : List Ev) : Prop := ShapeOK 0 (code₀ μ R) laneBits (commits h)

/-- **The doom the stack's root creates** for the announced value `a = (layout, ρ)`: no candidate
satisfies the leanISA relation (`CommitDoom`), and the stack's is the only commitment. -/
def CommitPost (prog : Program) (input : PublicInput) (a : Verifier.Layout × ℕ) (_ : Unit)
    (h : List Ev) : Prop :=
  CommitDoom F₀ prog input thrOf a h ∧ StackShape a.1.stackLog a.2 h

/-- What the announced value is on a run: the verifier's layout at admissible sizes, an
admissible WHIR shape, and a layout `buildLayout` returned. -/
def Good (prog : Program) (a : Verifier.Layout × ℕ) (s : Sizes) : Prop :=
  a.1 = verifierLayout prog s ∧ s.Admissible prog ∧ Whir.Admissible a.1.stackLog a.2 ∧
    LayoutBounds a.1

/-- **The announced value of a run is good.** -/
theorem good_of_readSizes (prog : Program) {l : List Ev} {a : Verifier.Layout × ℕ}
    (h : (readSizes (bytecodeWords prog)).after l = some (.ret a)) : ∃ s, Good prog a s := by
  obtain ⟨s, hs, hρ, hl, -⟩ := readSizes_ret_sizes prog h
  obtain ⟨xs, -, -, -, hρ1, hρ2, -, hb, hμ1, hμ2⟩ := readSizes_ret h
  exact ⟨s, hl, hs, ⟨hμ1, hμ2, hρ1, hρ2⟩, layoutBounds_of_buildLayout hb⟩

/-! ## The program after the announced sizes -/

/-- `verify_execution` after the announced sizes `(layout, ρ)`. -/
def veBody (publicInput : Digest) (layout : Verifier.Layout) (ρ : ℕ) : Prog Unit := do
  Verifier.commitStack layout.stackLog ρ
  let bus ← Verifier.verifyBusBalance .computed layout
  let claims ← Verifier.tablePhase layout bus
  let publicClaims ← Verifier.publicInputPhase layout publicInput
  let claims := claims ++ publicClaims
  let (flockPoint, flockS) ←
    Verifier.verifyFlock .computed (blake2sR1csLogSize + layout.tableLogHeights.getD opBlake2s 0)
  let (ringTarget, ringWeight) ← Verifier.ringSwitch flockPoint flockS
  Verifier.verifyStackedOpening layout.stackLog ρ
    (Verifier.ringSwitchClaim layout ringTarget ringWeight :: claims.map (·.onStack layout))

/-- `verify_execution` is the announced sizes, then `veBody`. -/
theorem verifyExecution_eq (bytecode : List K) (publicInput : Digest) :
    verifyExecution .computed bytecode publicInput =
      (readSizes bytecode).bind fun a ↦ veBody publicInput a.1 a.2 := rfl

/-! ## The phases at sizes `s` and rate `ρ` -/

section Phases

variable (prog : Program) (input : PublicInput) (s : Sizes) (ρ : ℕ)

/-- The candidates of the history's stack word, on the verifier's layout. -/
abbrev Cs : List Ev → Set (Column (verifierLayout prog s).stackLog) := candsL prog s ρ thrOf

/-- The candidates of the deployed level-0 code at an admissible shape: finite, at most
`2^18`. -/
theorem candidates_bound {μ R : ℕ} (hw : Whir.Admissible μ R) (W : Word) :
    (Candidates μ R (thrOf μ R) W).Finite ∧ (Candidates μ R (thrOf μ R) W).ncard ≤ L₀ := by
  obtain ⟨q₀, rest, hc, -⟩ := Whir.Complete.exists_ladder hw
  obtain ⟨-, hμ, hκ, hR, hL, -⟩ := Whir.Params.deployed_spec_hyps hw hc
  exact ⟨candidates_finite _ hκ hR hμ W, (candidates_ncard_le _ hκ hR hμ W).trans hL⟩

/-- The deployed level-0 list bound is at most `2^18`. -/
theorem listMax_le {μ R : ℕ} (hw : Whir.Admissible μ R) : (code₀ μ R).listMax ≤ L₀ := by
  obtain ⟨q₀, rest, hc, -⟩ := Whir.Complete.exists_ladder hw
  exact (Whir.Params.deployed_spec_hyps hw hc).2.2.2.2.1

/-- The bus of the leanISA instance at a built verifier layout has depth at most `38`. -/
theorem μBus_le (hlb : LayoutBounds (verifierLayout prog s)) :
    (leanIsaInstance F₀ prog s).μBus ≤ 38 := by
  rw [← busLayout_depth_leanIsa]
  exact pushDepth_le hlb

/-- The history's candidates are the candidates of its stack word. -/
theorem cs_eq {h : List Ev} {W : Word} (hW : firstWord h = some W) :
    Cs prog s ρ h = Candidates (verifierLayout prog s).stackLog ρ
      (thrOf (verifierLayout prog s).stackLog ρ) W := by
  ext q
  simp only [Cs, candsL, Set.mem_ofPred_eq, hW, Option.some.injEq, exists_eq_left']
  exact mem_candidates_castColumn (stackLog_verifierLayout prog s) ρ W q

/-- The history's candidates are stable along a run with no commitment. -/
theorem cs_stable : Stable (Cs prog s ρ) := by
  intro h₀ l hl
  ext q
  simp only [Cs, candsL, Set.mem_ofPred_eq, firstWord, commits_append_hist, hl, List.append_nil]

/-- The history's candidates are at most `2^18`. -/
theorem cs_ncard (hw : Whir.Admissible (verifierLayout prog s).stackLog ρ) (h : List Ev) :
    (Cs prog s ρ h).ncard ≤ L₀ := by
  rcases hW : firstWord h with _ | W
  · have : Cs prog s ρ h = ∅ := by
      ext q; simp [Cs, candsL, hW]
    rw [this, Set.ncard_empty]; exact Nat.zero_le _
  · rw [cs_eq prog s ρ hW]; exact (candidates_bound hw W).2

/-- A sub-program without commitments keeps the shape of the commitments. -/
theorem stackShape_keep {α : Type} {p : Prog α} (hp : MovesOK (fun _ ↦ False) False p) (μ R : ℕ) :
    ∀ h₀ l, p.Reach h₀ l → StackShape μ R h₀ → StackShape μ R (h₀ ++ l) := by
  intro h₀ l hl hJ
  simpa [StackShape, commits_append_hist, hp.reach_commits hl] using hJ

/-- The number of Flock rounds of a built layout is at most `46`. -/
theorem flockRounds_le {layout : Verifier.Layout} (hlb : LayoutBounds layout) :
    blake2sR1csLogSize + layout.tableLogHeights.getD opBlake2s 0 - flockKSkip -
      fixedChallenges.length ≤ 46 := by
  have : layout.tableLogHeights.getD opBlake2s 0 ≤ 32 := by
    rw [List.getD_eq_getElem?_getD]
    cases hi : layout.tableLogHeights[opBlake2s]? with
    | none => simp
    | some x => exact hlb.heights_le x (List.mem_of_getElem? hi)
  simp only [blake2sR1csLogSize]
  omega

variable {prog s ρ}

/-- **The stacked opening at an admissible shape**, with the deployed codes. -/
noncomputable def stackedGen {μ R : ℕ} (hw : Whir.Admissible μ R) (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine μ c.1) :
    Spec (verifyStackedOpening μ R claims)
      (fun h ↦ StackedPre μ R (code₀ μ R) claims (commits h)) (fun _ _ ↦ False) εLean
      (eBatch claims.length (code₀ μ R)) 0 :=
  have hex := Whir.Complete.exists_ladder hw
  have hc := hex.choose_spec.choose_spec.1
  have hd := Whir.Params.deployed_spec_hyps hw hc
  stackedSpec claims hcl hc hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.2.1 hd.2.2.2.2.2.2 0

/-- The opening's claims are multiaffine when the ring claim is multilinear. -/
theorem openingClaims_multiaffine (layout : Verifier.Layout) (r : E × (List E → E))
    (cl : List Verifier.ColumnClaim)
    (hq : IsMultilinearFn layout.stackLog (ringSwitchClaim layout r.1 r.2).1) :
    ∀ c ∈ ringSwitchClaim layout r.1 r.2 :: cl.map (·.onStack layout),
      IsMultiaffine layout.stackLog c.1 := by
  intro c hc'
  rcases List.mem_cons.1 hc' with rfl | hc'
  · exact isMultiaffine_of_isMultilinearFn hq
  · obtain ⟨c', -, rfl⟩ := List.mem_map.1 hc'
    exact isMultiaffine_onStack _ c'

open Classical in
/-- **The stacked opening**, from ring switching's postcondition with a multilinear ring claim
and the stack's shape. -/
noncomputable def stackedPart (hw : Whir.Admissible (verifierLayout prog s).stackLog ρ)
    (cl : List Verifier.ColumnClaim) (r : E × (List E → E)) :
    Spec (verifyStackedOpening (verifierLayout prog s).stackLog ρ
        (ringSwitchClaim (verifierLayout prog s) r.1 r.2 ::
          cl.map (·.onStack (verifierLayout prog s))))
      (fun h ↦ (RingPost (verifierLayout prog s) (Cs prog s ρ) cl r h ∧
          IsMultilinearFn (verifierLayout prog s).stackLog
            (ringSwitchClaim (verifierLayout prog s) r.1 r.2).1) ∧
        StackShape (verifierLayout prog s).stackLog ρ h)
      (fun _ _ ↦ False) εLean (eBatch (cl.length + 1) (code₀ (verifierLayout prog s).stackLog ρ))
      0 :=
  if hq : IsMultilinearFn (verifierLayout prog s).stackLog
      (ringSwitchClaim (verifierLayout prog s) r.1 r.2).1 then
    (stackedGen hw _ (openingClaims_multiaffine _ r cl hq)).mono
      (fun h hp ↦ stackedPre_of_ringPost prog s ρ cl r h hp.1.1 hp.2) (fun _ _ h ↦ h) le_rfl
      (by simp) le_rfl
  else Spec.dead.mono (fun _ hp ↦ hq hp.1.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- The ring claim of every value ring switching returns is multilinear. -/
theorem ringSwitch_ret_multilinear (layout : Verifier.Layout) (pt sv : List E) :
    ∀ l y, (ringSwitch pt sv).after l = some (.ret y) →
      IsMultilinearFn layout.stackLog (ringSwitchClaim layout y.1 y.2).1 :=
  RetOK.bind_true fun _ ↦ RetOK.ret (isMultilinearFn_ringSwitchClaim layout _ pt _)

/-- **Ring switching, then the stacked opening.** -/
noncomputable def ringPart (hw : Whir.Admissible (verifierLayout prog s).stackLog ρ)
    (cl : List Verifier.ColumnClaim) (pt sv : List E) :
    Spec ((ringSwitch pt sv).bind fun y ↦ verifyStackedOpening (verifierLayout prog s).stackLog ρ
        (ringSwitchClaim (verifierLayout prog s) y.1 y.2 ::
          cl.map (·.onStack (verifierLayout prog s))))
      (fun h ↦ LinPost F₀ prog s (verifierLayout prog s) (Cs prog s ρ) (toI prog s) cl input
          (pt, sv) h ∧ StackShape (verifierLayout prog s).stackLog ρ h)
      (fun _ _ ↦ False) εLean
      ((∑ _i ∈ Finset.range 6, (L₀ : ℝ≥0∞) * ((overE 1 : ℝ≥0) : ℝ≥0∞)) +
        eBatch (cl.length + 1) (code₀ (verifierLayout prog s).stackLog ρ)) 0 :=
  (Spec.frame (Spec.retInv (ringBridgeSpec F₀ prog s (verifierLayout prog s) (Cs prog s ρ)
      (toI prog s) cl input (ringLayoutHyp_verifierLayout prog s F₀) (cs_stable prog s ρ)
      (cs_ncard prog s ρ hw)
      (T := eBatch (cl.length + 1) (code₀ (verifierLayout prog s).stackLog ρ))
      pt sv) _ (ringSwitch_ret_multilinear _ pt sv))
    _ (stackShape_keep (movesOK_ringSwitch pt sv) _ _)).bind' fun y ↦ stackedPart hw cl y

/-- **Flock, ring switching and the stacked opening**, for at most `230` claims. -/
noncomputable def flockPart (hw : Whir.Admissible (verifierLayout prog s).stackLog ρ)
    (hlb : LayoutBounds (verifierLayout prog s)) (cl : List Verifier.ColumnClaim)
    (hcl : cl.length ≤ 230) :
    Spec ((verifyFlock .computed (blake2sR1csLogSize +
          (verifierLayout prog s).tableLogHeights.getD opBlake2s 0)).bind fun x ↦
        (ringSwitch x.1 x.2).bind fun y ↦ verifyStackedOpening (verifierLayout prog s).stackLog ρ
          (ringSwitchClaim (verifierLayout prog s) y.1 y.2 ::
            cl.map (·.onStack (verifierLayout prog s))))
      (fun h ↦ FlockPre F₀ prog s (verifierLayout prog s) (Cs prog s ρ) (toI prog s) cl h ∧
        StackShape (verifierLayout prog s).stackLog ρ h)
      (fun _ _ ↦ False) εLean
      ((∑ _i ∈ Finset.range (blake2sR1csLogSize +
          (verifierLayout prog s).tableLogHeights.getD opBlake2s 0 - flockKSkip -
          fixedChallenges.length), (L₀ : ℝ≥0∞) * ((overE 1 : ℝ≥0) : ℝ≥0∞)) + 0) 0 :=
  have he := phase_errors (leanIsaInstance F₀ prog s) (μBus_le prog s hlb)
    (B_leanIsa_le F₀ prog s)
  (Spec.frame (flockBridgeSpec F₀ prog s (verifierLayout prog s) (Cs prog s ρ) (toI prog s) cl
      input walkFaithful_blake2sFlockSpec (tableLogHeights_blake2s prog s) (cs_stable prog s ρ)
      (cs_ncard prog s ρ hw)
      (he.2.2.2.2.2.2.2.2.1 (cl.length + 1) _ (by omega)
        (listMax_le hw))
      he.2.2.2.2.2.2.2.2.2.1 he.2.2.2.2.2.2.2.2.2.2.1 he.2.2.2.2.2.2.2.2.2.2.2)
    _ (stackShape_keep (movesOK_verifyFlock _) _ _)).bind' fun x ↦ ringPart input hw cl x.1 x.2

open Classical in
/-- **The public input, then Flock, ring switching and the opening**, after at most `227` claims
of the table phase. The public input's challenge and Flock's point are one group of challenges,
whose lead is at most `L₀ · 47/|E|` (`pubLead_le`). -/
noncomputable def pubPart (hw : Whir.Admissible (verifierLayout prog s).stackLog ρ)
    (hlb : LayoutBounds (verifierLayout prog s)) (cl : List Verifier.ColumnClaim)
    (hcl : cl.length ≤ 227) :
    Spec ((Verifier.publicInputPhase (verifierLayout prog s) (publicDigest input)).bind fun pc ↦
        (verifyFlock .computed (blake2sR1csLogSize +
          (verifierLayout prog s).tableLogHeights.getD opBlake2s 0)).bind fun x ↦
        (ringSwitch x.1 x.2).bind fun y ↦ verifyStackedOpening (verifierLayout prog s).stackLog ρ
          (ringSwitchClaim (verifierLayout prog s) y.1 y.2 ::
            (cl ++ pc).map (·.onStack (verifierLayout prog s))))
      (fun h ↦ PubPre F₀ prog s (verifierLayout prog s) (Cs prog s ρ) (toI prog s) cl input h ∧
        StackShape (verifierLayout prog s).stackLog ρ h)
      (fun _ _ ↦ False) εLean ((L₀ : ℝ≥0∞) * ((overE 47 : ℝ≥0) : ℝ≥0∞)) 0 :=
  ((Spec.frame (Spec.retInv (pubPhaseSpec F₀ prog s (verifierLayout prog s) (Cs prog s ρ)
      (toI prog s) cl input (pubLayoutHyp_verifierLayout prog s F₀)
      (EndToEnd.Complete.digestScalars_publicDigest input) (cs_stable prog s ρ)
      (cs_ncard prog s ρ hw))
      (fun pc ↦ pc.length ≤ 3) (retOK_publicInputPhase _ _))
    _ (stackShape_keep (movesOK_publicInputPhase _ _) _ _)).bind' fun pc ↦
    if hpc : pc.length ≤ 3 then
      (flockPart input hw hlb (cl ++ pc) (by rw [List.length_append]; omega)).mono
        (fun _ hp ↦ ⟨hp.1.1, hp.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hp ↦ hpc hp.1.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
    (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (pubLead_le L₀ (flockRounds_le hlb)) le_rfl

/-- The candidates of the stack's word, as oracles of the instance, are finite and at most
`2^18`. -/
theorem candsOf_bound (hw : Whir.Admissible (verifierLayout prog s).stackLog ρ) (W : Word) :
    (candsOf F₀ prog s ρ thrOf W).Finite ∧ (candsOf F₀ prog s ρ thrOf W).ncard ≤ L₀ := by
  rw [stackLog_verifierLayout] at hw
  refine ⟨(candidates_bound hw W).1.image _, ?_⟩
  rw [candsOf_ncard]
  exact (candidates_bound hw W).2

variable (prog s ρ) in
/-- The bus phase and the table sumcheck commit nothing. -/
theorem movesOK_busTable (layout : Verifier.Layout) :
    MovesOK (fun _ ↦ False) False ((verifyBusBalance .computed layout).bind (tablePhase layout)) :=
  (movesOK_verifyBusBalance layout).bind (movesOK_tablePhase layout)

open Classical in
/-- **Everything after the stack's root**: the bus and the table sumcheck, from the root's doom,
then the public input, Flock, ring switching and the
opening. -/
noncomputable def restSpec
    (hw : Whir.Admissible (verifierLayout prog s).stackLog ρ)
    (hlb : LayoutBounds (verifierLayout prog s)) :
    Spec ((verifyBusBalance .computed (verifierLayout prog s)).bind fun bus ↦
        (tablePhase (verifierLayout prog s) bus).bind fun cl ↦
        (Verifier.publicInputPhase (verifierLayout prog s) (publicDigest input)).bind fun pc ↦
        (verifyFlock .computed (blake2sR1csLogSize +
          (verifierLayout prog s).tableLogHeights.getD opBlake2s 0)).bind fun x ↦
        (ringSwitch x.1 x.2).bind fun y ↦ verifyStackedOpening (verifierLayout prog s).stackLog ρ
          (ringSwitchClaim (verifierLayout prog s) y.1 y.2 ::
            (cl ++ pc).map (·.onStack (verifierLayout prog s))))
      (fun h ↦ CommitPost prog input (verifierLayout prog s, ρ) () h)
      (fun _ _ ↦ False) εLean (abError (leanIsaInstance F₀ prog s) L₀ + 0) 0 :=
  have he := phase_errors (leanIsaInstance F₀ prog s) (μBus_le prog s hlb)
    (B_leanIsa_le F₀ prog s)
  Spec.congr (Prog.bind_assoc _ _ _) <|
    ((Spec.frame (Spec.retInv (busTableSpec_leanIsa F₀ prog s input
        (candsOf F₀ prog s ρ thrOf) (fun W ↦ (candsOf_bound hw W).1)
        (fun W ↦ (candsOf_bound hw W).2) he.2.1 he.2.2.1 he.2.2.2.1 he.2.2.2.2.1
        he.2.2.2.2.2.1 he.2.2.2.2.2.2.1 (he.2.2.2.2.2.2.2.1 _))
        (fun cl ↦ cl.length ≤ 227) (retOK_busTable _))
      _ (stackShape_keep (movesOK_busTable _) _ _)).mono
      (fun h hp ↦ ⟨commitDoom_hdoom F₀ prog s input thrOf ρ h hp.1, hp.2⟩) (fun _ _ h ↦ h)
      le_rfl le_rfl le_rfl).bind' fun cl ↦
      if hcl : cl.length ≤ 227 then
        (pubPart input hw hlb cl hcl).mono
          (fun h hp ↦ ⟨tablePost_pubPre F₀ prog s (candsOf F₀ prog s ρ thrOf) input rfl
            (Cs prog s ρ) (candsL_mem F₀ prog s ρ thrOf) cl h hp.1.1, hp.2⟩) (fun _ _ h ↦ h)
          le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ hp ↦ hcl hp.1.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **`verify_execution` after the announced sizes**, at good sizes: the stack's root, then
`restSpec`. -/
noncomputable def realSpec
    (hw : Whir.Admissible (verifierLayout prog s).stackLog ρ)
    (hlb : LayoutBounds (verifierLayout prog s)) :
    Spec (veBody (publicDigest input) (verifierLayout prog s) ρ) (fun _ ↦ False)
      (fun _ _ ↦ False) εLean 0 0 :=
  (commitSpec (CommitPost prog input (verifierLayout prog s, ρ))
      (verifierLayout prog s).stackLog ρ
      (phase_errors (leanIsaInstance F₀ prog s) (μBus_le prog s hlb)
        (B_leanIsa_le F₀ prog s)).1).bind' fun _ ↦
    restSpec input hw hlb

end Phases

/-! ## The whole program -/

section Whole

variable (prog : Program) (input : PublicInput)

open Classical in
/-- `verify_execution` after the announced value `a`: `realSpec` at good sizes, dead
otherwise. -/
noncomputable def bodySpec (a : Verifier.Layout × ℕ) :
    Spec (veBody (publicDigest input) a.1 a.2) (fun _ ↦ False) (fun _ _ ↦ False) εLean 0 0 :=
  if h : ∃ s, Good prog a s then
    (realSpec (prog := prog) (s := h.choose) (ρ := a.2) input
      (by rw [← h.choose_spec.1]; exact h.choose_spec.2.2.1)
      (by rw [← h.choose_spec.1]; exact h.choose_spec.2.2.2)).congr
      (by rw [h.choose_spec.1])
  else Spec.dead

/-- **The specification of `verify_execution`.** -/
noncomputable def veSpec :
    Spec (verifyExecution .computed (bytecodeWords prog) (publicDigest input)) (fun _ ↦ False)
      (fun _ _ ↦ False) εLean 0 0 :=
  (readSizesSpec (bytecodeWords prog) (fun _ _ ↦ False)).bind' (bodySpec prog input)

/-- **The specification of the leanVM verifier program**: from no doom, rejecting where it
returns in doom, every group's escape at most `2^-128` (discounted by its proof of work), lead
`0`. -/
noncomputable def leanVmSpec :
    Spec (leanVmProgram (bytecodeWords prog) (publicDigest input)) (fun _ ↦ False)
      (fun b _ ↦ b = false) εLean 0 0 :=
  (veSpec prog input).bind' fun _ ↦
    (Spec.ret (Post := fun b _ ↦ b = false) true).mono (fun _ h ↦ h.elim) (fun _ _ h ↦ h)
      le_rfl le_rfl le_rfl

/-- **The doom certificate of the leanVM verifier.** -/
noncomputable def leanVmCert : Cert (leanVmProgram (bytecodeWords prog) (publicDigest input)) :=
  (leanVmSpec prog input).toCert

end Whole

end
end LeanVM.Protocol.EndToEnd.Sound
