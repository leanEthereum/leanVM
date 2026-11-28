/-
  LeanVM.Protocol.Relation.Front

  The phases between the commitment's out-of-domain sample and ring switching, composed: the
  link, the public input and the Keccak reduction turn a stack failing the relation into a claim
  they leave failing on it.
-/

module

public import LeanVM.Protocol.Relation.Iface
public import LeanVM.Protocol.Relation.Public
public import LeanVM.Protocol.Relation.Frame

/-!
# The front phases

`frontProg layout input` is `verify_execution`'s steps 3 to 5 (`walk`, `lib.rs`): the link, the
public input, the Keccak reduction. The relation on a stack is the link's (`LinkIface.LinkRel`),
the public input's (`PubRel`) and the Keccak segments' (`KeccakRel`). **`frontSpec`**: from the
relation failing on every candidate of a subsingleton `S`, the claims they leave fail on it
(`FrontHolds`: the link's memory term, its committed column claims and its ring claim, the public
input's claims, the reduction's `q_keccak` claims and its ring claim). Each phase checks its part
and carries the others (`Spec.orConst`): the link turns its part, or the Keccak segments', into its
end failing or the Keccak defect surviving at the `KECCAK` row point; the public input turns its
part into its claims failing; the reduction turns the `KECCAK` output lanes' claims failing, or
the defect, into its own claims failing. The link's last boundary, the public input's challenge
and the reduction's first group are one group: the link's follower's lead is `1/|E|` plus the
reduction's `6/|E|`.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

@[expose] public section

/-- On a subsingleton, a disjunction for every member is one disjunct for every member. -/
theorem subsingleton_forall_or {β : Type*} {S : Set β} (hS : S.Subsingleton) {P Q : β → Prop} :
    (∀ q ∈ S, P q ∨ Q q) → (∀ q ∈ S, P q) ∨ (∀ q ∈ S, Q q) := by
  intro h
  rcases S.eq_empty_or_nonempty with rfl | ⟨q, hq⟩
  · exact .inl fun _ h ↦ absurd h (Set.notMem_empty _)
  · rcases h q hq with h1 | h1
    · exact .inl fun q' hq' ↦ (hS hq hq') ▸ h1
    · exact .inr fun q' hq' ↦ (hS hq hq') ▸ h1

/-- `verify_execution`'s steps 3 to 5: the link, the public input, the Keccak reduction. -/
def frontProg (layout : Layout) (input : PublicInput) :
    VerifierProgram (LinkEnd × List ColumnClaim × (List ColumnClaim × List E × List E)) := do
  let link ← verifyLink computedSplit layout
  let pub ← bindPublicInput layout (publicInputDigest input)
  let kr ← keccakValidity layout link
  return (link, pub, kr)

/-- The link's committed column claims: all but the `KECCAK` output lanes'. -/
def committedClaims (e : LinkEnd) : List ColumnClaim :=
  (linkColumnClaims e).filter fun c ↦ (keccakOutputLane c.column).isNone

/-- **The front phases' claims hold** of a stack: the link's memory term, its committed column
claims and its ring claim, the public input's claims, the reduction's `q_keccak` claims and its
ring claim. -/
def FrontHolds (layout : Layout) (qk : Placement) {μ : ℕ} (q : Column μ)
    (r : LinkEnd × List ColumnClaim × (List ColumnClaim × List E × List E)) : Prop :=
  (r.1.memoryValue =
      r.1.memoryScales.1 * rowMle r.1.memoryPoint (columnValue layout q memory0) +
        r.1.memoryScales.2 * rowMle r.1.memoryPoint (columnValue layout q memory1)) ∧
    (∀ c ∈ committedClaims r.1, ColumnClaimHolds layout q c) ∧ RingClaimHolds q r.1.ring ∧
    (∀ c ∈ r.2.1, ColumnClaimHolds layout q c) ∧ (∀ c ∈ r.2.2.1, ColumnClaimHolds layout q c) ∧
    RingClaimHolds q (keccakRingClaim qk r.2.2.2.1 r.2.2.2.2)

/-- The link's end holds exactly when its committed part and its `KECCAK` output lanes' claims
do. -/
theorem linkEndHolds_iff (layout : Layout) {μ : ℕ} (q : Column μ) (e : LinkEnd) :
    LinkEndHolds layout q e ↔
      (e.memoryValue =
        e.memoryScales.1 * rowMle e.memoryPoint (columnValue layout q memory0) +
          e.memoryScales.2 * rowMle e.memoryPoint (columnValue layout q memory1)) ∧
      (∀ c ∈ committedClaims e, ColumnClaimHolds layout q c) ∧ RingClaimHolds q e.ring ∧
      (∀ c ∈ keccakOutputClaims e, ColumnClaimHolds layout q c) := by
  unfold LinkEndHolds committedClaims keccakOutputClaims
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun c hc ↦ h2 c (List.mem_filter.mp hc).1, h3,
      fun c hc ↦ h2 c (List.mem_filter.mp hc).1⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, fun c hc ↦ ?_, h3⟩
    rcases hk : keccakOutputLane c.column with _ | l
    · exact h2 c (List.mem_filter.mpr ⟨hc, by simp [hk]⟩)
    · exact h4 c (List.mem_filter.mpr ⟨hc, by simp [hk]⟩)

/-- **The front phases, round by round**: from the relation failing on every candidate of a
subsingleton `S`, the claims they leave fail on it. -/
noncomputable def frontSpec (LI : LinkIface) (KI : KeccakIface) {bytecode : List K}
    {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ) (input : PublicInput)
    {qk : Placement} (hqk : layout.placements.getD qkeccak none = some qk)
    (S : Set (Column layout.stackLog)) (hS : S.Subsingleton) {T : ENNReal}
    (hT : (Fintype.card E : ENNReal)⁻¹ +
      (((keccakSegmentBits + keccakLaneBits : ℕ) : ENNReal) / Fintype.card E + T) ≤ εmsg) :
    Spec (frontProg layout input)
      (fun _ ↦ ∀ q ∈ S, ¬ (LI.LinkRel layout q ∧ PubRel layout input q ∧ KeccakRel layout q))
      (fun r _ ↦ ∀ q ∈ S, ¬ FrontHolds layout qk q r) εmsg εmsg T := by
  have hT2 : ((keccakSegmentBits + keccakLaneBits : ℕ) : ENNReal) / Fintype.card E + T ≤ εmsg :=
    le_trans le_add_self hT
  have hT3 : T ≤ εmsg := le_trans le_add_self hT2
  have hmin : ∀ {a b : ENNReal}, a ≤ b → min 1 a ≤ b := fun h ↦ (min_le_right _ _).trans h
  unfold frontProg
  -- The link, carrying the public input's part.
  refine Spec.bind (Spec.retInv ((LI.linkSpec bytecode layout ρ hA S hS _ hT).orConst
    (∀ q ∈ S, ¬ PubRel layout input q) hT (hmin hT) |>.mono ?_ (fun _ _ h ↦ h) le_rfl le_rfl
      le_rfl) (LinkShape layout) (LI.linkShape bytecode layout ρ hA)) fun link ↦ ?_
  · intro _ h
    have h' : ∀ q ∈ S, (¬ LI.LinkRel layout q ∨ ¬ KeccakRel layout q) ∨ ¬ PubRel layout input q :=
      fun q hq ↦ by
        have := h q hq
        tauto
    exact subsingleton_forall_or hS h'
  by_cases hls : LinkShape layout link
  swap
  · exact Spec.dead.mono (fun _ h ↦ hls h.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  -- The public input, carrying the link's end.
  refine Spec.bind ((pubSpec layout input S hS (εmax := εmsg)
    (T := ((keccakSegmentBits + keccakLaneBits : ℕ) : ENNReal) / Fintype.card E + T)).orConst
    (∀ q ∈ S, ¬ LinkEndHolds layout q link ∨ KeccakDefectAt layout q link) hT2
    ((min_le_right _ _).trans le_add_self) |>.mono (fun _ h ↦ h.1.symm) (fun _ _ h ↦ h) le_rfl
      le_rfl le_rfl) fun pub ↦ ?_
  -- The Keccak reduction, carrying the rest.
  refine Spec.bind ((KI.keccakSpec bytecode layout ρ hA link hls qk hqk S hS T hT3).orConst
    ((∀ q ∈ S, ¬ ∀ c ∈ pub, ColumnClaimHolds layout q c) ∨
      ∀ q ∈ S, ¬ ((link.memoryValue =
        link.memoryScales.1 * rowMle link.memoryPoint (columnValue layout q memory0) +
          link.memoryScales.2 * rowMle link.memoryPoint (columnValue layout q memory1)) ∧
        (∀ c ∈ committedClaims link, ColumnClaimHolds layout q c) ∧ RingClaimHolds q link.ring))
    hT3 ((min_le_right _ _).trans le_add_self) |>.mono ?_ (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)
    fun kr ↦ ?_
  · intro _ h
    rcases h with h | h
    · exact .inr (.inl h)
    · have h' : ∀ q ∈ S, (¬ (∀ c ∈ keccakOutputClaims link, ColumnClaimHolds layout q c) ∨
          KeccakDefectAt layout q link) ∨ ¬ ((link.memoryValue =
            link.memoryScales.1 * rowMle link.memoryPoint (columnValue layout q memory0) +
              link.memoryScales.2 * rowMle link.memoryPoint (columnValue layout q memory1)) ∧
            (∀ c ∈ committedClaims link, ColumnClaimHolds layout q c) ∧
            RingClaimHolds q link.ring) := fun q hq ↦ by
        rcases h q hq with h1 | h1
        · rw [linkEndHolds_iff] at h1
          tauto
        · exact .inl (.inr h1)
      rcases subsingleton_forall_or hS h' with h'' | h''
      · exact .inl h''
      · exact .inr (.inr h'')
  · refine (Spec.ret (Post := fun r _ ↦ ∀ q ∈ S, ¬ FrontHolds layout qk q r)
      (link, pub, kr)).mono ?_ (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    intro _ h q hq hF
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hF
    rcases h with h | h | h
    · rcases h q hq with h' | h'
      · exact h' h5
      · exact h' h6
    · exact h q hq h4
    · exact h q hq ⟨h1, h2, h3⟩

end

end LeanVM.Protocol.Relation

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

@[expose] public section

/-- **The front phases' results' shapes**: the link's end, the public input's claims at its
challenge on the memory's placement, the Keccak reduction's result. -/
def FrontShape (layout : Layout) (input : PublicInput)
    (r : LinkEnd × List ColumnClaim × (List ColumnClaim × List E × List E)) : Prop :=
  LinkShape layout r.1 ∧
    (∃ c m, layout.placements.getD memory0 none = some m ∧ r.2.1 = publicClaims input m c) ∧
    KeccakShape layout r.2.2

theorem returns_bindPublicInput {layout : Layout} {input : PublicInput} {cs : List ColumnClaim}
    (h : VerifierProgram.Returns (bindPublicInput layout (publicInputDigest input)) cs) :
    ∃ c m, layout.placements.getD memory0 none = some m ∧ cs = publicClaims input m c := by
  rw [bindPublicInput_eq] at h
  obtain ⟨c, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨m, hm, h⟩ := VerifierProgram.returns_bind h
  exact ⟨c, m, returns_liftOption hm, VerifierProgram.returns_ret h⟩

/-- What the front phases return has their shapes. -/
theorem frontShape_of_returns (LI : LinkIface) (KI : KeccakIface) {bytecode : List K}
    {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ) (input : PublicInput)
    {r : LinkEnd × List ColumnClaim × (List ColumnClaim × List E × List E)}
    (h : VerifierProgram.Returns (frontProg layout input) r) : FrontShape layout input r := by
  unfold frontProg at h
  obtain ⟨link, hl, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨pub, hp, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨kr, hk, h⟩ := VerifierProgram.returns_bind h
  rw [VerifierProgram.returns_ret h]
  have hls := LI.linkShape bytecode layout ρ hA link hl
  exact ⟨hls, returns_bindPublicInput hp, KI.keccakShape bytecode layout ρ hA link hls kr hk⟩

/-- **The front phases, with their results' shapes.** -/
noncomputable def frontSpecShaped (LI : LinkIface) (KI : KeccakIface) {bytecode : List K}
    {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ) (input : PublicInput)
    {qk : Placement} (hqk : layout.placements.getD qkeccak none = some qk)
    (S : Set (Column layout.stackLog)) (hS : S.Subsingleton) {T : ENNReal}
    (hT : (Fintype.card E : ENNReal)⁻¹ +
      (((keccakSegmentBits + keccakLaneBits : ℕ) : ENNReal) / Fintype.card E + T) ≤ εmsg) :
    Spec (frontProg layout input)
      (fun _ ↦ ∀ q ∈ S, ¬ (LI.LinkRel layout q ∧ PubRel layout input q ∧ KeccakRel layout q))
      (fun r _ ↦ (∀ q ∈ S, ¬ FrontHolds layout qk q r) ∧ FrontShape layout input r) εmsg εmsg T :=
  (frontSpec LI KI hA input hqk S hS hT).retInv _ fun _ h ↦ frontShape_of_returns LI KI hA input h

end

end LeanVM.Protocol.Relation
