/-
  LeanVM.Guest.B1.VerifySub.NZBridge

  From a child's acceptance by the deferring verifier refusing zero challenges (and by the guest's
  variant refusing a zero fold, tail or level batching challenge or a vanishing combiner) to runs
  of its prefix and of its stacked opening.
-/

module

public import LeanVM.Guest.B1.VerifySub.NoCommit
public import LeanVM.Guest.B1.VerifySub.NZRun
public import LeanVM.Guest.NZProgram

/-!
# The deferring verifier's runs, split at the stacked opening

`flatPre c bytecode pi`: the deferring verifier up to its stacked opening, its phases grouped as
`verify_sub` runs them (Split.lean's `deferredFlat`), returning the layout, the rate and the
claims. The deferring verifier is `flatPre`, then `verifyStackedOpening` (`deferred_pre`); the
guest's variant is `flatPre`, then `Limits.verifyStackedOpeningNZ` (`deferredNZ_pre`, the steps of
Claims.lean's `verifyExecution_claims`).

`accept_rz`, `accept_nz`: an accepted run of either is a run of `flatPre` from the child's start,
then of its stacked opening to the stream's and the openings' end. `opening_rz`, `opening_nz`: the
stacked opening is the claims' check, the batching challenge, then `Whir.whirOpen` (refusing zero
challenges) or `Limits.whirOpenNZ`, then the terminal's check. `refuseZero_bind`: refusing zero
challenges commutes with sequencing.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Verifier.Claims

@[expose] public section

/-! ## The prefix -/

/-- **The deferring verifier up to its stacked opening**, grouped as `verify_sub` runs it. -/
def flatPre (c : BytecodeClaim) (bytecode : List K) (pi : Digest) :
    VerifierProgram (Layout × ℕ × List StackClaim) :=
  (readAnnouncedSizes bytecode).bind fun ls ↦
  (commitStack ls.1.stackLog ls.2).bind fun _ ↦
  (readOod ls.1.stackLog).bind fun ood ↦
  (VerifierProgram.require (busDepth ls.1 < 64)).bind fun _ ↦
  (busChallenges (busDepth ls.1)).bind fun wb ↦
  (Tables.gkrPhase (busDepth ls.1)).bind fun r ↦
  (Tables.tablesSeg (claimedBytecodeValue c) ls.1 pi wb.1 wb.2 r.2.1 r.2.2).bind fun bc ↦
  (keccakPhaseClaims ls.1 bc.2).bind fun kc ↦
  (ringSwitch kc.2.1 kc.2.2).bind fun rs ↦
  VerifierProgram.ret (ls.1, ls.2, stackClaims ls.1 kc.1 rs.1 rs.2 ood)

/-- **The deferring verifier: the prefix, then the stacked opening.** -/
theorem deferred_pre (c : BytecodeClaim) (bytecode : List K) (pi : Digest) :
    deferringVerifierProgram c bytecode pi = (flatPre c bytecode pi).bind fun q ↦
      (verifyStackedOpening q.1.stackLog q.2.1 q.2.2).bind fun _ ↦ VerifierProgram.ret true := by
  rw [deferred_eq]
  simp only [deferredFlat, flatPre, VerifierProgram.bind_assoc, VerifierProgram.ret_bind]

/-- `verifyExecutionClaims` with the stacked opening refusing what makes the guest divide. -/
def verifyExecutionClaimsNZ (ev : List K → List E → E → VerifierProgram Unit) (bytecode : List K)
    (publicInput : Digest) : VerifierProgram Unit := do
  let (layout, logInverseRate) ← readAnnouncedSizes bytecode
  commitStack layout.stackLog logInverseRate
  let ood ← readOod layout.stackLog
  let bus ← verifyBusBalance ev layout
  let claims ← tablePhaseClaims layout bus
  let publicClaims ← publicInputPhase layout publicInput
  let claims := claims ++ publicClaims
  let (claims, keccakPoint, keccakSlices) ← keccakPhaseClaims layout claims
  let (ringTarget, ringWeight) ← ringSwitch keccakPoint keccakSlices
  Limits.verifyStackedOpeningNZ layout.stackLog logInverseRate
    (ringSwitchClaim layout ringTarget ringWeight :: claims.map (·.stackClaim layout) ++ [ood])

/-- **The guest's verifier on the claim-list form** (Claims.lean's `verifyExecution_claims`). -/
theorem verifyExecutionNZ_claims (ev : List K → List E → E → VerifierProgram Unit)
    (bytecode : List K) (publicInput : Digest) :
    Limits.verifyExecutionNZ ev bytecode publicInput =
      verifyExecutionClaimsNZ ev bytecode publicInput := by
  unfold Limits.verifyExecutionNZ verifyExecutionClaimsNZ
  simp only [VerifierProgram.bind_eq]
  refine Claims.bind_congr (Q := fun x ↦ LayoutOk x.1) (fun x hl ↦ ?_) _ (allRet_readSizes bytecode)
  refine Claims.bind_congr (Q := fun _ ↦ True) (fun _ _ ↦ ?_) _ (allRet_true _)
  refine Claims.bind_congr (Q := fun _ ↦ True) (fun ood _ ↦ ?_) _ (allRet_true _)
  refine Claims.bind_congr (fun bus hb ↦ ?_) _ (allRet_verifyBusBalance ev x.1)
  rw [tablePhaseClaims_eq, VerifierProgram.bind_assoc]
  refine Claims.bind_congr (fun rows hr ↦ ?_) _ (allRet_tablePhase hl hb)
  rw [VerifierProgram.ret_bind]
  refine Claims.bind_congr (fun pc hpc ↦ ?_) _ (allRet_publicInputPhase x.1 publicInput)
  rw [keccakPhaseClaims_eq hb.2 hpc hr, VerifierProgram.bind_assoc]
  refine Claims.bind_congr (fun r hout ↦ ?_) _ (allRet_keccakPhase x.1 rows)
  rw [VerifierProgram.ret_bind]
  refine Claims.bind_congr (Q := fun _ ↦ True) (fun rs _ ↦ ?_) _ (allRet_true _)
  have hlt : ∀ c ∈ bus.claims ++ tableColumnClaims rows ++ pc ++ r.1, c.column < 158 := by
    intro c hc
    simp only [List.mem_append] at hc
    rcases hc with ((hc | hc) | hc) | hc
    · have := hb.2 c hc
      simp only [framework, memory0, memory1, memoryFinalCounters, bytecodeFinalCounters,
        List.mem_cons, List.not_mem_nil, or_false] at this
      omega
    · exact tableClaims_lt hr c hc
    · have := hpc c hc
      simp only [memory0, memory1, List.mem_cons, List.not_mem_nil, or_false] at this
      omega
    · rw [hout c hc]; decide
  have hfm := filterMap_onStack hl _ hlt
  rw [List.filter_append,
    (List.filter_eq_self (l := r.1)).mpr fun c hc ↦ by rw [hout c hc]; decide] at hfm
  exact congrArg (fun l ↦ Limits.verifyStackedOpeningNZ x.1.stackLog x.2 (_ :: l ++ [ood])) hfm

/-- **The guest's deferring verifier: the prefix, then its stacked opening.** -/
theorem deferredNZ_pre (c : BytecodeClaim) (bytecode : List K) (pi : Digest) :
    Limits.deferredProgramNZ c bytecode pi = (flatPre c bytecode pi).bind fun q ↦
      (Limits.verifyStackedOpeningNZ q.1.stackLog q.2.1 q.2.2).bind fun _ ↦
        VerifierProgram.ret true := by
  show (Limits.verifyExecutionNZ _ _ _).bind _ = _
  rw [verifyExecutionNZ_claims]
  simp only [verifyExecutionClaimsNZ, flatPre, verifyBusBalance_split, busChallenges,
    Tables.tablesSeg, stackClaims, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
    VerifierProgram.bind_assoc, VerifierProgram.ret_bind]

/-! ## The stacked opening -/

/-- The batching's target over the claims at `λ`. -/
def batchTarget (cl : List StackClaim) (lam : E) : E :=
  dot (powers lam cl.length) (cl.map (·.2))

/-- The batching's weight over the claims at `λ`. -/
def batchBasis (cl : List StackClaim) (lam : E) : List E → E :=
  fun point ↦ dot (powers lam cl.length) (cl.map fun c ↦ c.1 point)

theorem verifyStackedOpening_split (μ r : ℕ) (cl : List StackClaim) :
    verifyStackedOpening μ r cl =
      (VerifierProgram.require (cl.length ≤ maxStackedClaims)).bind fun _ ↦
      VerifierProgram.sampleChallenge.bind fun lam ↦
      (Whir.whirOpen μ r (batchTarget cl lam)).bind fun w ↦
        VerifierProgram.require (w.Accepts (batchBasis cl lam)) := by
  rw [verifyStackedOpening_eq]
  simp only [Whir.verifyWhir_split, VerifierProgram.bind_eq]
  rfl

theorem verifyStackedOpeningNZ_split (μ r : ℕ) (cl : List StackClaim) :
    Limits.verifyStackedOpeningNZ μ r cl =
      (VerifierProgram.require (cl.length ≤ maxStackedClaims)).bind fun _ ↦
      VerifierProgram.sampleChallenge.bind fun lam ↦
      (Limits.whirOpenNZ μ r (batchTarget cl lam)).bind fun w ↦
        VerifierProgram.require (w.Accepts (batchBasis cl lam)) := by
  unfold Limits.verifyStackedOpeningNZ
  simp only [Limits.verifyWhirNZ_split, VerifierProgram.bind_eq]
  rfl

/-! ## Refusing zero challenges -/

theorem bind_ite_fail {α β : Type} (c : Prop) [Decidable c] (P : VerifierProgram α)
    (f : α → VerifierProgram β) :
    (if c then (VerifierProgram.fail : VerifierProgram α) else P).bind f =
      if c then VerifierProgram.fail else P.bind f := by
  split <;> rfl

/-- **Refusing zero challenges commutes with sequencing.** -/
theorem refuseZero_bind {α β : Type} : ∀ (P : VerifierProgram α) (f : α → VerifierProgram β),
    (P.bind f).refusingZeroChallenge =
      P.refusingZeroChallenge.bind fun a ↦ (f a).refusingZeroChallenge
  | .ret _, _ => rfl
  | .fail, _ => rfl
  | .read k, f => congrArg VerifierProgram.read (funext fun x ↦ refuseZero_bind (k x) f)
  | .sample k, f => by
    show VerifierProgram.sample (fun x ↦ if x = 0
        then VerifierProgram.fail else ((k x).bind f).refusingZeroChallenge) =
      VerifierProgram.sample fun x ↦ (if x = 0
          then VerifierProgram.fail else (k x).refusingZeroChallenge).bind
        fun a ↦ (f a).refusingZeroChallenge
    refine congrArg _ (funext fun x ↦ ?_)
    rw [bind_ite_fail, refuseZero_bind (k x) f]
  | .grind _ k, f => congrArg (VerifierProgram.grind _) (refuseZero_bind k f)
  | .commit _ _ k, f => congrArg (VerifierProgram.commit _ _) (refuseZero_bind k f)
  | .query _ _ k, f =>
    congrArg (VerifierProgram.query _ _) (funext fun r ↦ refuseZero_bind (k r) f)

/-! ## From the child's acceptance -/

/-- The deferring verifier's start on a child's proof. -/
def deferStart (seed pi : Digest) (π : Proof) : VerifierProgramState :=
  ⟨⟨keccakF1600 (seedInput seed pi), [], none⟩, π.stream, π.openings, []⟩

theorem runProof_accepts {P : VerifierProgram Bool} {seed : KeccakState} {π : Proof}
    (h : Id.run (runProofWithHash (m := Id) keccak256 keccakF1600 P seed π) = true) :
    ∃ t : VerifierProgramState, runId P ⟨⟨seed, [], none⟩, π.stream, π.openings, []⟩ =
      some (true, t) ∧ t.stream = [] ∧ t.openings = [] := by
  unfold runProofWithHash at h
  revert h
  match hr : Compile.runWithHash (m := Id) keccak256 keccakF1600 P
      ⟨⟨seed, [], none⟩, π.stream, π.openings, []⟩ with
  | some (true, s) =>
    intro h
    change (s.stream.isEmpty && s.openings.isEmpty) = true at h
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    exact ⟨s, hr, h.1, h.2⟩
  | some (false, _) =>
    intro h
    change false = true at h
    exact absurd h Bool.false_ne_true
  | none =>
    intro h
    change false = true at h
    exact absurd h Bool.false_ne_true

/-- A run of `p`, then `ret`, is a run of `p`. -/
theorem runId_bind_ret {α β : Type} {p : VerifierProgram α} {b : β}
    {st : VerifierProgramState} {r : β × VerifierProgramState}
    (h : runId (p.bind fun _ ↦ VerifierProgram.ret b) st = some r) :
    ∃ a, runId p st = some (a, r.2) := by
  obtain ⟨a, st', h1, h2⟩ := runId_bind_some h
  have e : runId (VerifierProgram.ret b) st' = some (b, st') := rfl
  rw [e, Option.some.injEq] at h2
  subst h2
  exact ⟨a, h1⟩

/-- **A proof the deferring verifier refusing zero challenges accepts**: a run of the prefix,
then of its stacked opening refusing zero challenges, to the stream's and the openings' end. -/
theorem accept_rz {bytecode : List K} {seed pi : Digest} {c : BytecodeClaim} {π : Proof}
    (h : Limits.verifyDeferredRefusingZero bytecode seed pi c π = true) :
    ∃ q stq t, runId (flatPre c bytecode pi) (deferStart seed pi π) = some (q, stq) ∧
      runId (verifyStackedOpening q.1.stackLog q.2.1 q.2.2).refusingZeroChallenge stq =
        some ((), t) ∧ t.stream = [] ∧ t.openings = [] := by
  unfold Limits.verifyDeferredRefusingZero at h
  rw [runProof_eq_withHash, keccak256With_keccakF1600] at h
  obtain ⟨t, hrun, ht1, ht2⟩ := runProof_accepts h
  rw [deferred_pre, refuseZero_bind] at hrun
  obtain ⟨q, stq, h1, h2⟩ := runId_bind_some hrun
  rw [refuseZero_bind] at h2
  obtain ⟨u, h3⟩ := runId_bind_ret h2
  exact ⟨q, stq, t, runId_of_rz _ _ _ h1, h3, ht1, ht2⟩

/-- **A proof the guest's deferring verifier accepts**: a run of the prefix, then of its stacked
opening, to the stream's and the openings' end. -/
theorem accept_nz {bytecode : List K} {seed pi : Digest} {c : BytecodeClaim} {π : Proof}
    (h : Limits.verifyDeferredNZ bytecode seed pi c π = true) :
    ∃ q stq t, runId (flatPre c bytecode pi) (deferStart seed pi π) = some (q, stq) ∧
      runId (Limits.verifyStackedOpeningNZ q.1.stackLog q.2.1 q.2.2) stq = some ((), t) ∧
      t.stream = [] ∧ t.openings = [] := by
  obtain ⟨t, hrun, ht1, ht2⟩ := runProof_accepts h
  rw [deferredNZ_pre] at hrun
  obtain ⟨q, stq, h1, h2⟩ := runId_bind_some hrun
  obtain ⟨u, h3⟩ := runId_bind_ret h2
  exact ⟨q, stq, t, h1, h3, ht1, ht2⟩

/-- A sample's run. -/
theorem runId_sample_bind {α : Type} (g : E → VerifierProgram α) (st : VerifierProgramState) :
    runId (VerifierProgram.sampleChallenge.bind g) st =
      runId (g (Id.run (squeeze keccakF1600 st.sponge)).1)
        { st with sponge := (Id.run (squeeze keccakF1600 st.sponge)).2 } := rfl

/-- A requirement's run. -/
theorem runId_require_bind {α : Type} {c : Prop} [Decidable c] {k : Unit → VerifierProgram α}
    {st : VerifierProgramState} {r : α × VerifierProgramState}
    (h : runId ((VerifierProgram.require c).bind k) st = some r) : c ∧ runId (k ()) st = some r := by
  unfold VerifierProgram.require at h
  split at h
  · exact ⟨by assumption, h⟩
  · exact absurd h (by rintro ⟨⟩)

/-- **The stacked opening refusing zero challenges**: the claims' check, a nonzero batching
challenge, then `whirOpen` refusing zero challenges (so `whirOpen`) to an end passing the
terminal's check. -/
theorem opening_rz {μ r : ℕ} {cl : List StackClaim} {st t : VerifierProgramState} {u : Unit}
    (h : runId (verifyStackedOpening μ r cl).refusingZeroChallenge st = some (u, t)) :
    cl.length ≤ maxStackedClaims ∧ ∃ w,
      runId (Whir.whirOpen μ r (batchTarget cl (Id.run (squeeze keccakF1600 st.sponge)).1))
        { st with sponge := (Id.run (squeeze keccakF1600 st.sponge)).2 } = some (w, t) ∧
      runId (Whir.whirOpen μ r
          (batchTarget cl (Id.run (squeeze keccakF1600 st.sponge)).1)).refusingZeroChallenge
        { st with sponge := (Id.run (squeeze keccakF1600 st.sponge)).2 } = some (w, t) ∧
      w.Accepts (batchBasis cl (Id.run (squeeze keccakF1600 st.sponge)).1) := by
  rw [verifyStackedOpening_split, refuseZero_bind] at h
  obtain ⟨u1, st1, h1, h2⟩ := runId_bind_some h
  have e1 : (VerifierProgram.require (cl.length ≤ maxStackedClaims)).refusingZeroChallenge =
      VerifierProgram.require (cl.length ≤ maxStackedClaims) := by
    unfold VerifierProgram.require; split <;> rfl
  rw [e1] at h1
  have hreq : cl.length ≤ maxStackedClaims ∧ st1 = st := by
    unfold VerifierProgram.require at h1
    split at h1
    · rename_i hc
      have e : runId (VerifierProgram.ret ()) st = some ((), st) := rfl
      rw [e, Option.some.injEq, Prod.mk.injEq] at h1
      exact ⟨hc, h1.2.symm⟩
    · exact absurd h1 (by rintro ⟨⟩)
  obtain ⟨hlen, rfl⟩ := hreq
  refine ⟨hlen, ?_⟩
  have e2 : runId ((VerifierProgram.sampleChallenge.bind fun lam ↦
      (Whir.whirOpen μ r (batchTarget cl lam)).bind fun w ↦
        VerifierProgram.require (w.Accepts (batchBasis cl lam))).refusingZeroChallenge) st1 =
      runId (if (Id.run (squeeze keccakF1600 st1.sponge)).1 = 0 then VerifierProgram.fail else
        ((Whir.whirOpen μ r (batchTarget cl (Id.run (squeeze keccakF1600 st1.sponge)).1)).bind
          fun w ↦ VerifierProgram.require (w.Accepts (batchBasis cl
            (Id.run (squeeze keccakF1600 st1.sponge)).1))).refusingZeroChallenge)
        { st1 with sponge := (Id.run (squeeze keccakF1600 st1.sponge)).2 } := rfl
  rw [e2] at h2
  split at h2
  · exact absurd h2 (by rintro ⟨⟩)
  rw [refuseZero_bind] at h2
  obtain ⟨w, st3, h3, h4⟩ := runId_bind_some h2
  have e3 : ∀ c' : Prop, ∀ _ : Decidable c',
      (VerifierProgram.require c').refusingZeroChallenge = VerifierProgram.require c' := by
    intro c' _; unfold VerifierProgram.require; split <;> rfl
  rw [e3] at h4
  unfold VerifierProgram.require at h4
  split at h4
  · rename_i hacc
    have e : runId (VerifierProgram.ret ()) st3 = some ((), st3) := rfl
    rw [e, Option.some.injEq, Prod.mk.injEq] at h4
    obtain ⟨-, rfl⟩ := h4
    exact ⟨w, runId_of_rz _ _ _ h3, h3, hacc⟩
  · exact absurd h4 (by rintro ⟨⟩)

/-- **The guest's stacked opening**: the claims' check, the batching challenge, then
`Limits.whirOpenNZ` to an end passing the terminal's check. -/
theorem opening_nz {μ r : ℕ} {cl : List StackClaim} {st t : VerifierProgramState} {u : Unit}
    (h : runId (Limits.verifyStackedOpeningNZ μ r cl) st = some (u, t)) :
    ∃ w, runId (Limits.whirOpenNZ μ r (batchTarget cl (Id.run (squeeze keccakF1600 st.sponge)).1))
        { st with sponge := (Id.run (squeeze keccakF1600 st.sponge)).2 } = some (w, t) := by
  rw [verifyStackedOpeningNZ_split] at h
  obtain ⟨-, h⟩ := runId_require_bind h
  rw [runId_sample_bind] at h
  obtain ⟨w, st3, h3, h4⟩ := runId_bind_some h
  unfold VerifierProgram.require at h4
  split at h4
  · have e : runId (VerifierProgram.ret ()) st3 = some ((), st3) := rfl
    rw [e, Option.some.injEq, Prod.mk.injEq] at h4
    obtain ⟨-, rfl⟩ := h4
    exact ⟨w, h3⟩
  · exact absurd h4 (by rintro ⟨⟩)

end
end LeanVM.Guest.B1.VerifySub
