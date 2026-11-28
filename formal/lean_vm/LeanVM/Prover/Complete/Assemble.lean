/-
  LeanVM.Prover.Complete.Assemble

  The honest script wins the verifier's program, phase by phase: `HonestWins` from the link's,
  the Keccak reduction's and the commitment's and opening's phases.
-/

module

public import LeanVM.Prover.Complete.Public
public import LeanVM.Prover.Complete.End
public import LeanVM.Prover.Complete.Witness

/-!
# The phases put together

`verifyExecution` (`Statement/Verifier/Lib.lean`) and `honestScript` (`Statement/Prover/Prove.lean`)
run the same seven phases. The announced sizes (`wins_sizes`), the out-of-domain sample
(`wins_ood`) and the public input (`wins_public`) are proved; the other phases are stated here, each
as the proposition its proof gives:

* `CommitOpenWins`: the stack's commitment, then (after the link, the public input and the Keccak
  reduction) ring switching and the stacked opening, on claims that hold;
* `LinkWins`: the link, leaving claims that hold (`LinkOut`);
* `KeccakWins`: the Keccak reduction, from the link's claims, leaving claims that hold.

`honestWins_of`: they give `HonestWins`, composed with `Wins.bind`.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-- The hypotheses of `LeanVM.Completeness` on an execution, and its witness. -/
structure Admitted (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ : ℕ)
    (W : Witness) : Prop where
  valid : ValidExecution prog input t
  size : t.committedSize ≤ 2 ^ 30
  width : t.pointerWidth ≤ maxPointerWidth
  windows : t.KeccakBlocksInWindows
  rate : 1 ≤ ρ ∧ ρ ≤ 4
  witness : witness? prog input t = some W

/-- What the link leaves, holding of the honest witness: its column claims (each table's
non-pointer columns at its row point), its memory term, its pointer columns' bit slices, and each
table's row point over the table's variables, the points' lengths, and every `KECCAK` output lane
among the values sent, and at most `116` column claims. -/
def LinkOut (W : Witness) (link : LinkEnd) : Prop :=
  (∀ c ∈ linkColumnClaims link, c.HoldsIn W.cols) ∧
    link.memoryValue = link.memoryScales.1 * mleK (W.cols.getD memory0 #[]) link.memoryPoint +
      link.memoryScales.2 * mleK (W.cols.getD memory1 #[]) link.memoryPoint ∧
    link.ring.HoldsOn W.stack ∧
    (∀ t < nTables, (link.columns.getD t ([], [])).1.length = W.layout.tableLogHeights.getD t 0) ∧
    (∀ c ∈ linkColumnClaims link, ∀ p, W.layout.placements.getD c.column none = some p →
      c.point.length = p.variableCount) ∧
    link.memoryPoint.length = W.layout.logMemory ∧
    (∀ piece ∈ link.ring.pieces, ∃ c p, W.layout.placements.getD c none = some p ∧
      piece.placement = some p ∧ piece.point.length = p.variableCount) ∧
    (∀ lane < keccakStateLanes, ∃ v, (keccakOut + lane, v) ∈ (link.columns.getD opKeccak ([], [])).2) ∧
    (linkColumnClaims link).length ≤ 116

/-- **The link wins**, leaving claims that hold. -/
def LinkWins : Prop :=
  ∀ (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ : ℕ) (W : Witness),
    Admitted prog input t ρ W → ∀ cs : List Committed,
    Wins 17 (fun a b g cs' ↦ a = b ∧ g = false ∧ cs' = cs ∧ LinkOut W a)
      (verifyLink computedSplit W.layout)
      (Script.alongside (verifyLink computedSplit W.layout) (linkProve W)) false cs

/-- **The Keccak reduction wins** from the link's claims, its output claims holding of the
columns and its slices of `q_keccak`. -/
def KeccakWins : Prop :=
  ∀ (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ : ℕ) (W : Witness),
    Admitted prog input t ρ W → ∀ link : LinkEnd, LinkOut W link → ∀ cs : List Committed,
    Wins 17 (fun a b g cs' ↦ a = b ∧ g = false ∧ cs' = cs ∧ (∀ c ∈ a.1, c.HoldsIn W.cols) ∧
        SlicesHoldIn (W.cols.getD qkeccak #[]) a.2.1 a.2.2 ∧
        (∀ c ∈ a.1, ∀ p, W.layout.placements.getD c.column none = some p →
          c.point.length = p.variableCount) ∧
        a.2.1.length = W.layout.tableLogHeights.getD opKeccak 0 + qkeccakSlotBits ∧
        a.1.length = 1)
      (keccakValidity W.layout link)
      (Script.alongside (keccakValidity W.layout link)
        (KeccakGkr.keccakPhaseProve (W.layout.tableLogHeights.getD opKeccak 0) W.cols link))
      false cs

/-- **The commitment and the opening win**: the stack's commitment; then, from claims that hold,
ring switching and the stacked opening (`verifyExecution`'s steps 6 and 7 against
`honestScript`'s tail). -/
def CommitOpenWins : Prop :=
  ∀ (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ : ℕ) (W : Witness),
    Admitted prog input t ρ W → ∃ c : Committed,
    Wins 17 (fun _ _ g cs ↦ g = false ∧ cs = [c]) (commitStack W.layout.stackLog ρ)
      (Script.commitS (stackWordFast W.layout.stackLog ρ W.stack)) false [] ∧
    ∀ (oodPoint : List E) (link : LinkEnd) (claims : List ColumnClaim)
      (keccakPoint keccakSlices : List E),
      oodPoint.length = W.layout.stackLog → (∀ c ∈ claims, c.HoldsIn W.cols) →
      link.memoryValue = link.memoryScales.1 * mleK (W.cols.getD memory0 #[]) link.memoryPoint +
        link.memoryScales.2 * mleK (W.cols.getD memory1 #[]) link.memoryPoint →
      link.ring.HoldsOn W.stack → SlicesHoldIn (W.cols.getD qkeccak #[]) keccakPoint keccakSlices →
      (∀ c ∈ claims, ∀ p, W.layout.placements.getD c.column none = some p →
        c.point.length = p.variableCount) →
      link.memoryPoint.length = W.layout.logMemory →
      keccakPoint.length = W.layout.tableLogHeights.getD opKeccak 0 + qkeccakSlotBits →
      (∀ piece ∈ link.ring.pieces, ∃ c p, W.layout.placements.getD c none = some p ∧
        piece.placement = some p ∧ piece.point.length = p.variableCount) →
      claims.length ≤ 509 →
      Wins 17 (fun _ _ _ _ ↦ True)
        (do
          let qkeccakPlacement ← liftOption (W.layout.placements.getD qkeccak none)
          let (ring, batching) ←
            ringSwitch [keccakRingClaim qkeccakPlacement keccakPoint keccakSlices, link.ring]
          let memoryTerm ← memoryTermClaim W.layout link
          verifyStackedOpening W.layout.stackLog ρ
            (ring :: memoryTerm :: claims.filterMap (·.onStack W.layout) ++
              [((fun x ↦ eqEval oodPoint x), mleK W.stack oodPoint)]) batching)
        (do
          let qkeccakPlacement := (W.layout.placements.getD qkeccak none).getD default
          let ring ← ringFast true
          let placed := fun (column : ℕ) ↦ (W.layout.placements.getD column none).getD default
          let columnClaims := claims.filterMap fun c ↦
            (W.layout.placements.getD c.column none).map fun p ↦ ClaimDesc.cells [(p, c.point, 1)]
          openingFast W.layout.stackLog ρ W.stack
            (.ring [keccakRingClaim qkeccakPlacement keccakPoint keccakSlices, link.ring] ring.f
                ring.g ring.rho ::
              .cells [(placed memory0, link.memoryPoint, link.memoryScales.1),
                (placed memory1, link.memoryPoint, link.memoryScales.2)] ::
              columnClaims ++ [.ood oodPoint])
            ring.batching)
        false [c]

/-- **The honest script wins**, from its phases. -/
theorem honestWins_of (hco : CommitOpenWins) (hlink : LinkWins) (hkeccak : KeccakWins) :
    HonestWins := by
  intro prog input t ρ W hv hs hpw hk hρ hW
  have hA : Admitted prog input t ρ W := ⟨hv, hs, hpw, hk, hρ, hW⟩
  obtain ⟨c, hcommit, hopen⟩ := hco prog input t ρ W hA
  obtain ⟨-, steps, -, -, hl, -⟩ := witness?_spec hW
  have hμ : 1 ≤ W.layout.stackLog := by
    have := (buildLayout_spec hl).2.2.2.2.2
    exact le_trans (by decide) this
  unfold leanVmVerifierProgram verifyExecution honestScript
  simp only [VerifierProgram.bind_eq, Script.bind_eq, VerifierProgram.bind_assoc,
    VerifierProgram.pure_eq]
  refine Wins.bind (fun a _ g cs h ↦ ?_) _ _ _ _ (wins_sizes hW hρ [])
  obtain ⟨rfl, rfl, rfl⟩ := h
  dsimp only
  refine Wins.bind (fun _ _ g cs h ↦ ?_) _ _ _ _ hcommit
  obtain ⟨rfl, rfl⟩ := h
  refine Wins.bind (fun ood ood' g cs h ↦ ?_) _ _ _ _
    (wins_ood hμ (by decide) W.stack [c])
  obtain ⟨rfl, hval, hlen, rfl, rfl⟩ := h
  refine Wins.bind (fun link link' g cs h ↦ ?_) _ _ _ _ (hlink prog input t ρ W hA [c])
  obtain ⟨rfl, rfl, rfl, hout⟩ := h
  refine Wins.bind (fun pub pub' g cs h ↦ ?_) _ _ _ _ (wins_public hW false [c])
  obtain ⟨rfl, rfl, rfl, hpub, hpubl, hpublen⟩ := h
  refine Wins.bind (fun kc kc' g cs h ↦ ?_) _ _ _ _ (hkeccak prog input t ρ W hA link hout [c])
  obtain ⟨rfl, rfl, rfl, hkc, hks, hkcl, hkpl, hkclen⟩ := h
  have hclaims : ∀ cl ∈ linkColumnClaims link ++ pub ++ kc.1, cl.HoldsIn W.cols := by
    intro cl hcl
    simp only [List.mem_append] at hcl
    rcases hcl with (h | h) | h
    · exact hout.1 cl h
    · exact hpub cl h
    · exact hkc cl h
  have hlens : ∀ cl ∈ linkColumnClaims link ++ pub ++ kc.1, ∀ p,
      W.layout.placements.getD cl.column none = some p → cl.point.length = p.variableCount := by
    intro cl hcl
    simp only [List.mem_append] at hcl
    rcases hcl with (h | h) | h
    · exact hout.2.2.2.2.1 cl h
    · exact hpubl cl h
    · exact hkcl cl h
  have ho := hopen ood'.1 link (linkColumnClaims link ++ pub ++ kc.1) kc.2.1 kc.2.2 hlen hclaims
    hout.2.1 hout.2.2.1 hks hlens hout.2.2.2.2.2.1 hkpl hout.2.2.2.2.2.2.1
    (by simp only [List.length_append, hpublen, hkclen]; have := hout.2.2.2.2.2.2.2.2; omega)
  have ho' := Wins.bind (f := fun _ ↦ VerifierProgram.ret true) (t := Script.ret)
    (Q := fun a (_ : Unit) _ _ ↦ a = true) (fun _ _ _ _ _ ↦ Wins.ret rfl) _ _ _ _ ho
  rw [Script.bind_ret] at ho'
  rw [hval]
  simpa only [VerifierProgram.bind_eq, Script.bind_eq, VerifierProgram.bind_assoc,
    VerifierProgram.pure_eq] using ho'

end LeanVM.Prover

namespace LeanVM

open LeanVM.Prover

/-- **Completeness from the open phases and the costs**: the witness exists (`witnessExists`) and
the announced sizes, the out-of-domain sample and the public input win (`honestWins_of`). -/
theorem completeness_of_phases (hco : CommitOpenWins) (hlink : LinkWins) (hkeccak : KeccakWins)
    (hcost : HonestCosts) : Completeness :=
  completeness_of witnessExists (honestWins_of hco hlink hkeccak) hcost

end LeanVM

end
