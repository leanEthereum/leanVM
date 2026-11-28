/-
  LeanVM.Protocol.Relation.Body

  The walk's body after the announced sizes, round by round: the commitment, its out-of-domain
  sample, the front phases, ring switching and the stacked opening, every group within `2^-125`
  after its grind, an accepting return's trace good.
-/

module

public import LeanVM.Protocol.Relation.Walk
public import LeanVM.Protocol.Relation.Claims
public import LeanVM.Protocol.Relation.NoCommit
public import LeanVM.Protocol.Whir.Params.Iface
public import LeanVM.Protocol.EndToEnd.Front.CommitDoom

/-!
# The body, round by round

**`bodySpec`**: `veBodyG layout ρ input` (`Walk.lean`) from no doom, its accepting returns' traces
good from the bad stacks (`StackBad`: the relation fails): the descent of the trace ends on a
candidate of the stack's word that satisfies the relation (`OpeningIface.traceGood_cands`).

1. The commitment (`commitSpec`) creates the doom "level 0's shape" (`ShapeOK₀`).
2. Its out-of-domain sample (`commitOodSpec`) separates the candidates of the stack's word, so at
   most one answers it (`oodCands`, `OodSep`).
3. The front phases (`frontSpecShaped`), on the bad candidate left, carrying the commitments
   (`Spec.withCommits`, the phases committing nothing).
4. Ring switching and the stacked opening (`OpeningIface.stackedSpec`): every bad candidate of
   the stack's word fails a claim the opening reads (`openPre`): the one left fails a front claim
   (`not_frontHolds`), every other the out-of-domain claim (`not_holds_of_not_mem`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.Whir.Params
open LeanVM.Protocol.Whir.Sound (IsMultiaffine WhirTrace isMultiaffine_eqEval)
open scoped ENNReal

@[expose] public section

/-! ## The relation -/

/-- **The relation on a stack**: the link's part, the public input, `q_keccak`'s segments. -/
def StackRel (LI : LinkIface) (input : PublicInput) (layout : Layout)
    (q : Column layout.stackLog) : Prop :=
  LI.LinkRel layout q ∧ PubRel layout input q ∧ KeccakRel layout q

/-- **A bad stack** fails the relation. -/
def StackBad (LI : LinkIface) (input : PublicInput) (layout : Layout)
    (q : Column layout.stackLog) : Prop :=
  ¬ StackRel LI input layout q

/-! ## Facts of an announced layout -/

theorem announced_built {bytecode : List K} {layout : Layout} {ρ : ℕ}
    (h : Announced bytecode layout ρ) :
    (∃ lm rows, buildLayout bytecode lm rows = some layout) ∧ Whir.Admissible layout.stackLog ρ := by
  unfold Announced readAnnouncedSizes at h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, hr, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨layout', hl, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, hs, h⟩ := VerifierProgram.returns_bind h
  have he := VerifierProgram.returns_ret h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨⟨_, _, returns_liftOption hl⟩, ?_⟩
  have hs' := VerifierProgram.returns_require hs
  have hr' := VerifierProgram.returns_require hr
  exact ⟨hs'.1, hs'.2, hr'.1, hr'.2⟩

/-! ## Multiaffine weights -/

theorem length_stackPoint (p : Placement) (point : List E) (μ : ℕ) :
    (p.stackPoint point μ).length = point.length + (μ - p.variableCount) := by
  simp [Placement.stackPoint, selectorPoint]

theorem isMultiaffine_stackPoint {μ : ℕ} {p : Placement} {point : List E}
    (hlen : point.length = p.variableCount) (hvc : p.variableCount ≤ μ) :
    IsMultiaffine μ fun x ↦ eqEval (p.stackPoint point μ) x := by
  have h := isMultiaffine_eqEval (p.stackPoint point μ)
  rwa [length_stackPoint, hlen, Nat.add_sub_cancel' hvc] at h

theorem vc_le_of_placed {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hb : buildLayout bytecode lm rows = some layout) {c : ℕ} {p : Placement}
    (hp : layout.placements.getD c none = some p) : p.variableCount ≤ layout.stackLog := by
  obtain ⟨-, hfit⟩ := placement_aligned hb hp
  exact le_of_two_pow_le (by omega)

/-- The memory term's weight is multiaffine on the stack. -/
theorem isMultiaffine_memoryTerm {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hb : buildLayout bytecode lm rows = some layout) {p0 p1 : Placement}
    (h0 : layout.placements.getD memory0 none = some p0)
    (h1 : layout.placements.getD memory1 none = some p1) {e : LinkEnd}
    (hl0 : e.memoryPoint.length = p0.variableCount) (hl1 : e.memoryPoint.length = p1.variableCount) :
    IsMultiaffine layout.stackLog (memoryTermOf layout p0 p1 e).1 := by
  have h := ((isMultiaffine_stackPoint hl0 (vc_le_of_placed hb h0)).const_mul e.memoryScales.1).add
    ((isMultiaffine_stackPoint hl1 (vc_le_of_placed hb h1)).const_mul e.memoryScales.2)
  have he : (memoryTermOf layout p0 p1 e).1 = fun x ↦
      e.memoryScales.1 * eqEval (p0.stackPoint e.memoryPoint layout.stackLog) x +
        e.memoryScales.2 * eqEval (p1.stackPoint e.memoryPoint layout.stackLog) x := by
    funext x
    simp only [memoryTermOf, Tables.sumE_eq, List.sum_cons, List.sum_nil, add_zero]
  rw [he]
  exact h

/-- The placed column claims are multiaffine on the stack, each at a point over its placement's
variables. -/
theorem isMultiaffine_onStack {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hb : buildLayout bytecode lm rows = some layout) {cs : List ColumnClaim}
    (hlen : ∀ cl ∈ cs, ∀ p, layout.placements.getD cl.column none = some p →
      cl.point.length = p.variableCount) :
    ∀ c ∈ cs.filterMap (·.onStack layout), IsMultiaffine layout.stackLog c.1 := by
  intro c hc
  obtain ⟨cl, hcl, hon⟩ := List.mem_filterMap.mp hc
  rcases hp : layout.placements.getD cl.column none with _ | p
  · unfold ColumnClaim.onStack at hon
    rw [hp] at hon
    simp at hon
  · rw [onStack_eq hp, Option.some.injEq] at hon
    subst hon
    exact isMultiaffine_stackPoint (hlen cl hcl p hp) (vc_le_of_placed hb hp)

/-- A link claim at a placed column is at a point over its placement's variables. -/
theorem linkClaim_length {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hb : buildLayout bytecode lm rows = some layout) {e : LinkEnd} (he : LinkShape layout e)
    {c : ColumnClaim} (hc : c ∈ linkColumnClaims e) {p : Placement}
    (hp : layout.placements.getD c.column none = some p) : c.point.length = p.variableCount := by
  obtain ⟨-, -, hpts, hcols, -⟩ := he
  obtain ⟨t, ht, j, value, hjv, rfl⟩ := mem_linkColumnClaims hc
  have hj : j < tableWidths.getD t 0 := (hcols t ht).2 _ hjv
  rw [placement_variableCount hb hp, columnKappas_table _ _ ht hj, hpts t ht]

/-- The claims the opening reads past the ring claim are multiaffine, for results of the front
phases' shapes. -/
theorem isMultiaffine_others {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    (hb : buildLayout bytecode lm rows = some layout) (input : PublicInput)
    {p0 p1 : Placement} (h0 : layout.placements.getD memory0 none = some p0)
    (h1 : layout.placements.getD memory1 none = some p1)
    {r : LinkEnd × List ColumnClaim × (List ColumnClaim × List E × List E)}
    (hr : FrontShape layout input r) {z : List E} (hz : z.length = layout.stackLog) (y : E) :
    ∀ c ∈ openOthers layout (memoryTermOf layout p0 p1 r.1) r.1 r.2.1 r.2.2.1 (oodClaim z y),
      IsMultiaffine layout.stackLog c.1 := by
  unfold FrontShape at hr
  obtain ⟨hls, ⟨cc, m, hm, hpub⟩, hks⟩ := hr
  obtain ⟨⟨m0, hm0, hv0⟩, ⟨m1, hm1, hv1⟩, ⟨mk, hmk, hvk⟩⟩ := global_placed hb
  cases placement_unique h0 hm0
  cases placement_unique h1 hm1
  cases placement_unique hm h0
  obtain ⟨_, hlm⟩ := buildLayout_logMemory hb
  have hlm1 : 1 ≤ layout.logMemory := by
    obtain ⟨h1', _⟩ := buildLayout_logMemory hb; rw [h1']; simpa [minLogMemory] using hlm
  intro c hc
  simp only [openOthers, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hc
  rcases hc with (rfl | hc) | rfl
  · exact isMultiaffine_memoryTerm hb h0 h1 (by rw [hls.1, hv0]) (by rw [hls.1, hv1])
  · refine isMultiaffine_onStack hb (fun cl hcl p hp ↦ ?_) c hc
    simp only [List.mem_append] at hcl
    rcases hcl with (hcl | hcl) | hcl
    · exact linkClaim_length hb hls hcl hp
    · rw [hpub] at hcl
      simp only [publicClaims, List.map_cons, List.map_nil, List.zipWith_cons_cons,
        List.zipWith_nil_left, List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl
      · cases placement_unique hp h0; simp; omega
      · cases placement_unique hp h1; simp; omega
    · obtain ⟨hcol, hpl⟩ := hks.1 cl hcl
      rw [hcol] at hp
      cases placement_unique hp hmk
      rw [hpl, hvk]
  · have h := isMultiaffine_eqEval z
    rw [hz] at h
    exact h

theorem length_le_of_nodup_lt {l : List ℕ} {w : ℕ} (hn : l.Nodup) (hl : ∀ x ∈ l, x < w) :
    l.length ≤ w := by
  have := List.toFinset_card_of_nodup hn
  rw [← this]
  calc l.toFinset.card ≤ (Finset.range w).card :=
        Finset.card_le_card fun x hx ↦ Finset.mem_range.mpr (hl x (List.mem_toFinset.mp hx))
    _ = w := Finset.card_range w

/-- The link sends at most one claim per committed column of its tables. -/
theorem length_linkColumnClaims_le {layout : Layout} {e : LinkEnd} (he : LinkShape layout e) :
    (linkColumnClaims e).length ≤ 113 := by
  obtain ⟨-, hlen, -, hcols, -⟩ := he
  have hw : ∀ t < nTables, (e.columns.getD t ([], [])).2.length ≤ tableWidths.getD t 0 :=
    fun t ht ↦ by
      have := length_le_of_nodup_lt (hcols t ht).1 (fun x hx ↦ by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact (hcols t ht).2 y hy)
      simpa using this
  obtain ⟨c0, c1, c2, c3, c4, c5, hc⟩ : ∃ c0 c1 c2 c3 c4 c5, e.columns = [c0, c1, c2, c3, c4, c5] := by
    match e.columns, hlen with
    | [c0, c1, c2, c3, c4, c5], _ => exact ⟨c0, c1, c2, c3, c4, c5, rfl⟩
  have h0 := hw 0 (by decide); have h1 := hw 1 (by decide); have h2 := hw 2 (by decide)
  have h3 := hw 3 (by decide); have h4 := hw 4 (by decide); have h5 := hw 5 (by decide)
  rw [hc, tableWidths_eq] at h0 h1 h2 h3 h4 h5
  simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2 h3 h4 h5
  unfold linkColumnClaims
  rw [hc, globalColumnBases_eq]
  simp only [List.zip_cons_cons, List.zip_nil_right, List.flatMap_cons, List.flatMap_nil,
    List.length_append, List.length_map, List.length_nil]
  omega

theorem length_openOthers {layout : Layout} (mt : StackClaim) (link : LinkEnd)
    (pub outs : List ColumnClaim) (ood : StackClaim) (hls : LinkShape layout link)
    (hpub : pub.length ≤ 2) (houts : outs.length ≤ 1) :
    (openOthers layout mt link pub outs ood).length + 1 ≤ maxStackedClaims := by
  have h := length_linkColumnClaims_le hls
  have hf := (List.length_filterMap_le (·.onStack layout) (linkColumnClaims link ++ pub ++ outs))
  simp only [List.length_append] at hf
  simp only [openOthers, List.length_cons, List.length_append, List.length_nil, maxStackedClaims]
  omega

/-! ## The tail: ring switching and the stacked opening -/

/-- The front phases' two ring claims: the Keccak reduction's on `q_keccak`, the link's. -/
def ringsOf (qk : Placement)
    (r : LinkEnd × List ColumnClaim × (List ColumnClaim × List E × List E)) : List RingClaim :=
  [keccakRingClaim qk r.2.2.2.1 r.2.2.2.2, r.1.ring]

/-- The body after the front phases: `q_keccak`'s placement, ring switching, the memory term, the
stacked opening. -/
def tailProg (layout : Layout) (ρ : ℕ) (ood : StackClaim)
    (r : LinkEnd × List ColumnClaim × (List ColumnClaim × List E × List E)) :
    VerifierProgram WhirTrace :=
  match r with
  | (link, pub, outs, keccakPoint, keccakSlices) => do
    let qk ← liftOption (layout.placements.getD qkeccak none)
    let (ring, batching) ← ringSwitch [keccakRingClaim qk keccakPoint keccakSlices, link.ring]
    let memoryTerm ← memoryTermClaim layout link
    Whir.Sound.verifyStackedOpeningG layout.stackLog ρ
      (ring :: openOthers layout memoryTerm link pub outs ood) batching

theorem veBodyG_eq (layout : Layout) (ρ : ℕ) (input : PublicInput) :
    veBodyG layout ρ input = (commitStack layout.stackLog ρ).bind fun _ ↦
      (readOod layout.stackLog).bind fun ood ↦
        (frontProg layout input).bind (tailProg layout ρ ood) := rfl

theorem tailProg_eq {layout : Layout} (ρ : ℕ) (ood : StackClaim) {qk p0 p1 : Placement}
    (hqk : layout.placements.getD qkeccak none = some qk)
    (h0 : layout.placements.getD memory0 none = some p0)
    (h1 : layout.placements.getD memory1 none = some p1)
    (r : LinkEnd × List ColumnClaim × (List ColumnClaim × List E × List E)) :
    tailProg layout ρ ood r = (ringSwitch (ringsOf qk r)) >>= fun rb ↦
      Whir.Sound.verifyStackedOpeningG layout.stackLog ρ
        (rb.1 :: openOthers layout (memoryTermOf layout p0 p1 r.1) r.1 r.2.1 r.2.2.1 ood) rb.2 := by
  obtain ⟨link, pub, outs, kp, ks⟩ := r
  simp only [tailProg, hqk, memoryTermClaim_eq layout link h0 h1]
  rfl

open Classical in
/-- What the tail takes: the stack's shape, the out-of-domain claim at a point separating the
candidates, the bad candidate it leaves failing a front claim, the front's results shaped. -/
def TailPre (O : OpeningIface) (LI : LinkIface) (input : PublicInput) (layout : Layout) (ρ : ℕ)
    (qk : Placement) (ood : StackClaim)
    (r : LinkEnd × List ColumnClaim × (List ColumnClaim × List E × List E)) (h : List Ev) : Prop :=
  ∃ z y, ood = oodClaim z y ∧ z.length = layout.stackLog ∧
    O.ShapeOK₀ layout.stackLog ρ (commits h) ∧
    OodSep (firstCands layout.stackLog ρ (O.thr₀ layout.stackLog ρ) (commits h)) z ∧
    (∀ q ∈ oodCands (firstCands layout.stackLog ρ (O.thr₀ layout.stackLog ρ) (commits h)) z y ∩
        {q | StackBad LI input layout q}, ¬ FrontHolds layout qk q r) ∧
    FrontShape layout input r

/-- **Every bad candidate of the stack's word fails a claim the opening reads**: the one the
out-of-domain sample leaves a ring claim or a placed front claim, every other the out-of-domain
claim. -/
theorem openPre {O : OpeningIface} {LI : LinkIface} {input : PublicInput} {bytecode : List K}
    {lm : ℕ} {rows : List ℕ} {layout : Layout} (hb : buildLayout bytecode lm rows = some layout)
    {ρ : ℕ} {qk p0 p1 : Placement} (hqk : layout.placements.getD qkeccak none = some qk)
    (h0 : layout.placements.getD memory0 none = some p0)
    (h1 : layout.placements.getD memory1 none = some p1) {ood : StackClaim}
    {r : LinkEnd × List ColumnClaim × (List ColumnClaim × List E × List E)} {h : List Ev}
    (hp : TailPre O LI input layout ρ qk ood r h) :
    O.ShapeOK₀ layout.stackLog ρ (commits h) ∧
      ∀ q ∈ Candidates layout.stackLog ρ (O.thr₀ layout.stackLog ρ) (O.word₀ (commits h)),
        StackBad LI input layout q →
          (q ∈ Set.univ ∧ ∃ rc ∈ ringsOf qk r, ¬ RingClaimHolds q rc) ∨
            ∃ c ∈ openOthers layout (memoryTermOf layout p0 p1 r.1) r.1 r.2.1 r.2.2.1 ood,
              ¬ StackClaimHolds c q := by
  obtain ⟨z, y, rfl, -, hshape, hsep, hfront, hfs⟩ := hp
  refine ⟨hshape, fun q hq hbad ↦ ?_⟩
  have hq' : q ∈ firstCands layout.stackLog ρ (O.thr₀ layout.stackLog ρ) (commits h) :=
    ⟨_, O.shape_word hshape, hq⟩
  by_cases hin : q ∈ oodCands (firstCands layout.stackLog ρ (O.thr₀ layout.stackLog ρ)
    (commits h)) z y
  · obtain ⟨hls, hpub, hks⟩ := hfs
    rcases not_frontHolds hb q input hqk h0 h1 hls hpub hks (hfront q ⟨hin, hbad⟩) with
      ⟨rc, hrc, hn⟩ | ⟨c, hc, hn⟩
    · exact .inl ⟨trivial, rc, hrc, hn⟩
    · refine .inr ⟨c, ?_, hn⟩
      simp only [openOthers, List.mem_cons, List.mem_append] at hc ⊢
      rcases hc with rfl | hc
      · exact .inl (.inl rfl)
      · exact .inl (.inr hc)
  · refine .inr ⟨oodClaim z y, by simp [openOthers], ?_⟩
    exact not_holds_of_not_mem hsep hq' hin

/-! ## The body's specification -/

section Specs

variable (O : OpeningIface) (LI : LinkIface) (KI : KeccakIface) (input : PublicInput)

/-- The tail at the out-of-domain point `zy`. -/
noncomputable def openTailSpecAt {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    {ρ : ℕ} (hb : buildLayout bytecode lm rows = some layout) (hA : Announced bytecode layout ρ)
    {qk p0 p1 : Placement} (hqk : layout.placements.getD qkeccak none = some qk)
    (h0 : layout.placements.getD memory0 none = some p0)
    (h1 : layout.placements.getD memory1 none = some p1)
    (hRF : ∀ r, FrontShape layout input r → RingFacts layout.stackLog (ringsOf qk r))
    (ood : StackClaim) (r : LinkEnd × List ColumnClaim × (List ColumnClaim × List E × List E))
    (zy : List E × E) :
    Spec (tailProg layout ρ ood r)
      (fun h ↦ ood = oodClaim zy.1 zy.2 ∧ zy.1.length = layout.stackLog ∧
        TailPre O LI input layout ρ qk ood r h)
      (fun tr h ↦ O.TraceGood layout.stackLog ρ (StackBad LI input layout) tr (commits h))
      εmsg 0 0 := by
  by_cases hfs : FrontShape layout input r
  swap
  · exact Spec.dead.mono (fun _ hp ↦ hfs hp.2.2.choose_spec.choose_spec.2.2.2.2.2)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  by_cases hz : ood = oodClaim zy.1 zy.2 ∧ zy.1.length = layout.stackLog
  swap
  · exact Spec.dead.mono (fun _ hp ↦ hz ⟨hp.1, hp.2.1⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  obtain ⟨rfl, hzl⟩ := hz
  have hlen : (openOthers layout (memoryTermOf layout p0 p1 r.1) r.1 r.2.1 r.2.2.1
      (oodClaim zy.1 zy.2)).length + 1 ≤ maxStackedClaims := by
    obtain ⟨hls, ⟨c, m, -, hpub⟩, hks⟩ := hfs
    refine length_openOthers _ _ _ _ _ hls ?_ hks.2.2.2
    rw [hpub]; simp [publicClaims]
  rw [tailProg_eq ρ _ hqk h0 h1 r]
  exact (O.stackedSpec (announced_built hA).2 Set.univ (ringsOf qk r) (hRF r hfs) _ hlen
    (isMultiaffine_others hb input h0 h1 hfs hzl zy.2) (StackBad LI input layout)).mono
    (fun _ hp ↦ openPre hb hqk h0 h1 hp.2.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **The tail, round by round**: from `TailPre`, the trace good. -/
noncomputable def openTailSpec {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    {ρ : ℕ} (hb : buildLayout bytecode lm rows = some layout) (hA : Announced bytecode layout ρ)
    {qk p0 p1 : Placement} (hqk : layout.placements.getD qkeccak none = some qk)
    (h0 : layout.placements.getD memory0 none = some p0)
    (h1 : layout.placements.getD memory1 none = some p1)
    (hRF : ∀ r, FrontShape layout input r → RingFacts layout.stackLog (ringsOf qk r))
    (ood : StackClaim) (r : LinkEnd × List ColumnClaim × (List ColumnClaim × List E × List E)) :
    Spec (tailProg layout ρ ood r) (TailPre O LI input layout ρ qk ood r)
      (fun tr h ↦ O.TraceGood layout.stackLog ρ (StackBad LI input layout) tr (commits h))
      εmsg 0 0 :=
  (Spec.exPre (openTailSpecAt O LI input hb hA hqk h0 h1 hRF ood r)).mono
    (fun _ hp ↦ ⟨(hp.choose, hp.choose_spec.choose), hp.choose_spec.choose_spec.1,
      hp.choose_spec.choose_spec.2.1, hp⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- `7/|E|` is within `2^-125`. -/
theorem front_lead_le :
    (Fintype.card E : ℝ≥0∞)⁻¹ +
      (((keccakSegmentBits + keccakLaneBits : ℕ) : ℝ≥0∞) / Fintype.card E + 0) ≤ εmsg := by
  have h6 : keccakSegmentBits + keccakLaneBits = 6 := by decide
  have h := discount_le 0 7 (by norm_num)
  rw [pow_zero, one_mul] at h
  refine le_trans (le_of_eq ?_) h
  rw [h6, add_zero, ← one_div, ENNReal.div_add_div_same]
  norm_num

/-- The front phases' stage at the out-of-domain index `(z, y, cs)`. -/
noncomputable def frontStageAt {bytecode : List K} {layout : Layout} {ρ : ℕ}
    (hA : Announced bytecode layout ρ) {qk : Placement}
    (hqk : layout.placements.getD qkeccak none = some qk) (ood : StackClaim)
    (i : List E × E × List (ℕ × ℕ × Word)) :
    Spec (frontProg layout input)
      (fun h ↦ commits h = i.2.2 ∧ ood = oodClaim i.1 i.2.1 ∧ i.1.length = layout.stackLog ∧
        O.ShapeOK₀ layout.stackLog ρ i.2.2 ∧
        OodSep (firstCands layout.stackLog ρ (O.thr₀ layout.stackLog ρ) i.2.2) i.1)
      (TailPre O LI input layout ρ qk ood) εmsg εmsg 0 := by
  obtain ⟨z, y, cs⟩ := i
  let S := oodCands (firstCands layout.stackLog ρ (O.thr₀ layout.stackLog ρ) cs) z y ∩
    {q | StackBad LI input layout q}
  have hS : S.Subsingleton := fun _ ha _ hb' ↦ hb'.1.2.2 _ ha.1.1 ha.1.2.1
  refine ((frontSpecShaped LI KI hA input hqk S hS front_lead_le).withCommits
    (noCommit_frontProg layout input)
    (fun c ↦ c = cs ∧ ood = oodClaim z y ∧ z.length = layout.stackLog ∧
      O.ShapeOK₀ layout.stackLog ρ cs ∧
      OodSep (firstCands layout.stackLog ρ (O.thr₀ layout.stackLog ρ) cs) z)).mono
    (fun _ hp ↦ ⟨fun q hq hrel ↦ hq.2 hrel, hp⟩) (fun r h hp ↦ ?_) le_rfl le_rfl le_rfl
  obtain ⟨⟨hfront, hshape⟩, hcs, hood, hzl, hsh, hsep⟩ := hp
  refine ⟨z, y, hood, hzl, hcs ▸ hsh, hcs ▸ hsep, ?_, hshape⟩
  rw [hcs]
  exact hfront

/-- The front phases' stage and the tail, after the out-of-domain sample `ood`. -/
noncomputable def afterOodSpec {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    {ρ : ℕ} (hb : buildLayout bytecode lm rows = some layout) (hA : Announced bytecode layout ρ)
    {qk p0 p1 : Placement} (hqk : layout.placements.getD qkeccak none = some qk)
    (h0 : layout.placements.getD memory0 none = some p0)
    (h1 : layout.placements.getD memory1 none = some p1)
    (hRF : ∀ r, FrontShape layout input r → RingFacts layout.stackLog (ringsOf qk r))
    (ood : StackClaim) :
    Spec ((frontProg layout input).bind (tailProg layout ρ ood))
      (OodPost (firstCands layout.stackLog ρ (O.thr₀ layout.stackLog ρ))
        (O.ShapeOK₀ layout.stackLog ρ) ood)
      (fun tr h ↦ O.TraceGood layout.stackLog ρ (StackBad LI input layout) tr (commits h))
      εmsg εmsg 0 :=
  Spec.bind ((Spec.exPre (frontStageAt O LI KI input hA hqk ood)).mono
    (fun h hp ↦ by
      obtain ⟨z, y, hood, hzl, hsh, hsep⟩ := hp
      exact ⟨(z, y, commits h), rfl, hood, hzl, hsh, hsep⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)
    fun r ↦ openTailSpec O LI input hb hA hqk h0 h1 hRF ood r

theorem body_hμ {layout : Layout} {ρ : ℕ} (hadm : Whir.Admissible layout.stackLog ρ) :
    layout.stackLog ≠ 0 := by
  have := hadm.1; simp only [Whir.minLogStack] at this; omega

theorem body_he {layout : Layout} {ρ : ℕ} (hadm : Whir.Admissible layout.stackLog ρ) :
    oodError (O.listMax₀ layout.stackLog ρ) layout.stackLog < 1 := by
  have hrow := O.ood_row hadm
  unfold oodError
  rw [card_E, ENNReal.div_lt_iff (by simp) (by simp), one_mul]
  have : (O.listMax₀ layout.stackLog ρ).choose 2 * layout.stackLog < 2 ^ 128 :=
    lt_of_le_of_lt hrow (by simp only [Whir.oodGrindingBits]; norm_num)
  exact_mod_cast this

theorem body_hε {layout : Layout} {ρ : ℕ} (hadm : Whir.Admissible layout.stackLog ρ) :
    (2 : ℝ≥0∞)⁻¹ ^ Whir.oodGrindingBits *
      (oodError (O.listMax₀ layout.stackLog ρ) layout.stackLog + 0) ≤ εmsg := by
  rw [add_zero]; exact discount_le _ _ (O.ood_row hadm)

/-- The body on its unfolded program. -/
noncomputable def bodySpecRaw {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    {ρ : ℕ} (hb : buildLayout bytecode lm rows = some layout) (hA : Announced bytecode layout ρ)
    {qk p0 p1 : Placement} (hqk : layout.placements.getD qkeccak none = some qk)
    (h0 : layout.placements.getD memory0 none = some p0)
    (h1 : layout.placements.getD memory1 none = some p1)
    (hRF : ∀ r, FrontShape layout input r → RingFacts layout.stackLog (ringsOf qk r)) :
    Spec ((commitStack layout.stackLog ρ).bind fun _ ↦
        (readOod layout.stackLog).bind fun ood ↦ (frontProg layout input).bind (tailProg layout ρ ood))
      (fun _ ↦ False)
      (fun tr h ↦ O.TraceGood layout.stackLog ρ (StackBad LI input layout) tr (commits h))
      εmsg 0 0 :=
  (commitSpec (fun _ h ↦ O.ShapeOK₀ layout.stackLog ρ (commits h)) layout.stackLog ρ
    (εmax := εmsg) (by simp)).bind fun _ ↦
      (commitOodSpec (εmax := εmsg) (T := εmsg) O.thr₀ (body_hμ (announced_built hA).2)
        (fun W ↦ ⟨O.candidates_finite W (announced_built hA).2,
          O.card_candidates_le W (announced_built hA).2⟩)
        (O.ShapeOK₀ layout.stackLog ρ) (body_he O (announced_built hA).2)
        (body_hε O (announced_built hA).2) le_rfl).bind fun ood ↦
          afterOodSpec O LI KI input hb hA hqk h0 h1 hRF ood

/-- **The body, round by round**: `veBodyG` from no doom, an accepting return's trace good from
the bad stacks. -/
noncomputable def bodySpec {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    {ρ : ℕ} (hb : buildLayout bytecode lm rows = some layout) (hA : Announced bytecode layout ρ)
    {qk p0 p1 : Placement} (hqk : layout.placements.getD qkeccak none = some qk)
    (h0 : layout.placements.getD memory0 none = some p0)
    (h1 : layout.placements.getD memory1 none = some p1)
    (hRF : ∀ r, FrontShape layout input r → RingFacts layout.stackLog (ringsOf qk r)) :
    Spec (veBodyG layout ρ input) (fun _ ↦ False)
      (fun tr h ↦ O.TraceGood layout.stackLog ρ (StackBad LI input layout) tr (commits h))
      εmsg 0 0 :=
  (bodySpecRaw O LI KI input hb hA hqk h0 h1 hRF).congr (veBodyG_eq layout ρ input).symm

/-- **Right after the stack's root, the body's doom is level 0's shape.** -/
theorem bodySpecRaw_D_commit {bytecode : List K} {lm : ℕ} {rows : List ℕ} {layout : Layout}
    {ρ : ℕ} (hb : buildLayout bytecode lm rows = some layout) (hA : Announced bytecode layout ρ)
    {qk p0 p1 : Placement} (hqk : layout.placements.getD qkeccak none = some qk)
    (h0 : layout.placements.getD memory0 none = some p0)
    (h1 : layout.placements.getD memory1 none = some p1)
    (hRF : ∀ r, FrontShape layout input r → RingFacts layout.stackLog (ringsOf qk r))
    {h₀ : List Ev} {e : Ev} (hce : (commitStack layout.stackLog ρ).after [e] = some (.ret ()))
    (hpost : O.ShapeOK₀ layout.stackLog ρ (commits (h₀ ++ [e]))) :
    (bodySpecRaw O LI KI input hb hA hqk h0 h1 hRF).D h₀ [e] := by
  unfold bodySpecRaw
  rw [Spec.bind_D, Spec.bindD_some (VerifierProgram.retSplit_self hce)]
  refine ⟨fun _ ↦ ?_, Spec.start_D _ _ hpost⟩
  obtain ⟨level, rest, W, hc, -⟩ := commitStack_after_ret hce
  exact (commitSpec_D _ _ hc h₀ e).2 hpost

end Specs

end

end LeanVM.Protocol.Relation


