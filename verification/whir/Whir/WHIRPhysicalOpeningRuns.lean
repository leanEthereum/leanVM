import Whir.WHIRPhysicalReplay

/-! Every retained physical opening is an actual subexecution of the counted packet reader. Its primitive observations are included in the reader's public trace, including repeated calls. -/
namespace Whir.WHIRPhysicalOpeningRuns
open Concrete Protocol FiatShamirGame DuplexModeGame PublicMerkleProgram MerkleTransport
open RawOracleCoupling RawOracleCoupling.Concrete WHIRPhysicalVerifier WHIRPhysicalReplay

/-- The proof comes from the indexed physical proof array and the sample/root actually retained by the source interpreter. -/
def ObservedOpening {p : ParameterBounds.Profile} (lanes : Nat) (proofs : Array PrunedMerklePaths)
    (outer : List Observation) (opening : QueryOpening p) : Prop :=
  ∃ proof trace, proofs[opening.level.val]? = some proof ∧
    Runs (openQuery p opening.level lanes proof opening.root opening.sample) trace (some opening.result) ∧
    ∀ o ∈ trace, o ∈ outer

theorem ObservedOpening.mono {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {before after : List Observation} {opening : QueryOpening p}
    (observed : ObservedOpening lanes proofs before opening)
    (included : ∀ o ∈ before, o ∈ after) : ObservedOpening lanes proofs after opening := by
  obtain ⟨proof,trace,index,run,subset⟩ := observed
  exact ⟨proof,trace,index,run,fun o member => included o (subset o member)⟩

theorem absorbResponse_openings {p : ParameterBounds.Profile} (state out : WireState p)
    (pending : WHIRHistory.Pending) (root : Option Digest32)
    (ok : absorbResponse state pending = some (out,root)) : out.openings = state.openings := by
  unfold absorbResponse at ok
  cases previous : state.previous with
  | none =>
    simp only [previous] at ok
    split at ok
    · cases Option.some.inj ok
      rfl
    · contradiction
  | some q =>
    simp only [previous] at ok
    change (WHIRPhysicalHistory.reply (fun _ _ => #[]) (fun i => state.rows[i]!) q pending).bind _ =
      some (out,root) at ok
    cases parsed : WHIRPhysicalHistory.reply (fun _ _ => #[]) (fun i => state.rows[i]!) q pending with
    | none => simp [parsed] at ok
    | some response =>
      simp only [parsed,Option.bind_some,Option.some.injEq,Prod.mk.injEq] at ok
      cases ok.1
      rfl

theorem afterNonce_openings {p : ParameterBounds.Profile} {ctx : RawWHIRKeys.Context} {Q : Nat}
    {packet : RawWHIRKeys.Packet ctx Q} (state out : WireState p)
    (nonce : WHIRPowProgram.Outcome ctx Q packet) (ok : afterNonce state nonce = some out) :
    out.openings = state.openings := by
  unfold afterNonce at ok
  split at ok
  · cases Option.some.inj ok
    rfl
  · cases cached : state.outputCache with
    | none => simp [cached] at ok
    | some digest =>
      simp only [cached,Option.map_some,Option.some.injEq] at ok
      subst out
      rfl

theorem takeSample_openings {p : ParameterBounds.Profile} (lanes : Nat)
    (proofs : Array PrunedMerklePaths) (state out : WireState p)
    (q : CausalProbability.Coordinate (ParameterBounds.config p)) (x : StackWHIRReplay.Sample q)
    (trace : List Observation) (run : Runs (takeSample lanes proofs state q x) trace (some out)) :
    ∀ opening ∈ out.openings, opening ∈ state.openings ∨ ObservedOpening lanes proofs trace opening := by
  cases q with
  | query i =>
    simp only [takeSample] at run
    split at run
    · cases hp : proofs[i.val]? with
      | none => cases hr : state.roots[i.val]? <;> simp only [hp,hr] at run <;> cases run
      | some proof =>
        cases hr : state.roots[i.val]? with
        | none => simp only [hp,hr] at run; cases run
        | some root =>
          simp only [hp,hr] at run
          obtain ⟨before,opened,after,equal,openingRun,continued⟩ := (Runs.bind_iff _ _).mp run
          cases opened with
          | none => cases continued
          | some opened =>
            cases continued
            intro opening member
            rcases List.mem_cons.mp member with same | old
            · subst opening
              refine Or.inr ⟨proof,before,hp,openingRun,?_⟩
              intro o member
              rw [equal]
              exact List.mem_append_left _ member
            · exact Or.inl old
    · cases run
  | initial =>
    cases run
    intro opening member
    exact Or.inl member
  | fold i j =>
    cases run
    intro opening member
    exact Or.inl member
  | ood i j =>
    cases run
    intro opening member
    exact Or.inl member
  | tail j =>
    cases run
    intro opening member
    exact Or.inl member

/-- The same successful continuation is retained while all reader-created openings are tied to the outer public observations. -/
theorem readPhysicalPackets_openings {cap : Nat} {R : Type} (ctx : RawWHIRKeys.Context)
    (stack : ctx.mode = .stack) (Q : Nat) (p : ParameterBounds.Profile) (lanes : Nat)
    (proofs : Array PrunedMerklePaths) (packets : List (RawWHIRKeys.Packet ctx Q))
    (profiles : ∀ packet ∈ packets, packet.val.profile = p) (state : WireState p)
    (next : WireState p → List (Sigma (GroupAnswer ctx Q)) → WHIRSourceChronology.Source cap (Option R))
    (observations : List Observation) (result : R)
    (run : Runs (WHIRSourceChronology.erase
      (readPhysicalPackets ctx stack Q p lanes proofs none packets profiles state next)) observations (some result)) :
    ∃ final history suffix, Runs (WHIRSourceChronology.erase (next final history)) suffix (some result) ∧
      (∀ o ∈ suffix, o ∈ observations) ∧
      ∀ opening ∈ final.openings, opening ∈ state.openings ∨ ObservedOpening lanes proofs observations opening := by
  induction packets generalizing state next observations with
  | nil => exact ⟨state,[],observations,run,fun _ h => h,fun _ h => Or.inl h⟩
  | cons packet packets ih =>
    simp only [readPhysicalPackets] at run
    cases parsed : absorbResponse state (packet.val.messages.headD ⟨[],none⟩) with
    | none => simp only [parsed,WHIRSourceChronology.erase] at run; cases run
    | some pair =>
      obtain ⟨absorbed,root⟩ := pair
      simp only [parsed] at run
      split at run
      · rename_i guards
        rw [announce_erase,sourceLift_erase] at run
        obtain ⟨beforeNonce,nonce,afterNonceTrace,nonceEq,_,continued⟩ := (Runs.bind_iff _ _).mp run
        cases boundNonce : afterNonce absorbed nonce with
        | none => simp only [boundNonce,WHIRSourceChronology.erase] at continued; cases continued
        | some bound =>
          simp only [boundNonce] at continued
          split at continued
          · rw [sourceLift_erase] at continued
            obtain ⟨beforeRaw,raw,afterRaw,rawEq,_,read⟩ := (Runs.bind_iff _ _).mp continued
            rw [sourceLift_erase] at read
            obtain ⟨beforeOpen,opened,afterOpen,openEq,openingRun,rest⟩ := (Runs.bind_iff _ _).mp read
            cases opened with
            | none => cases rest
            | some checked =>
              have beforeSubset : ∀ o ∈ beforeOpen, o ∈ observations := by
                intro o member
                rw [nonceEq,rawEq,openEq]
                exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ member))
              have afterSubset : ∀ o ∈ afterOpen, o ∈ observations := by
                intro o member
                rw [nonceEq,rawEq,openEq]
                exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ member))
              obtain ⟨final,history,suffix,last,suffixSubset,retained⟩ := ih _ _ _ _ rest
              refine ⟨final,⟨.inl packet,raw⟩::history,suffix,last,
                fun o member => afterSubset o (suffixSubset o member),?_⟩
              intro opening member
              rcases retained opening member with old | observed
              · have opened := takeSample_openings _ _ _ _ _ _ _ openingRun opening old
                rcases opened with old | observed
                · have kept := (afterNonce_openings _ _ _ boundNonce).trans
                    (absorbResponse_openings _ _ _ _ parsed)
                  exact Or.inl (kept ▸ old)
                · exact Or.inr (observed.mono beforeSubset)
              · exact Or.inr (observed.mono afterSubset)
          · cases continued
      · cases run

/-- Initial wire state has no old opening records, so every returned record is covered by the actual source trace. -/
theorem readPhysicalCompletion_openings {cap : Nat} {R : Type} (ctx : RawWHIRKeys.Context)
    (stack : ctx.mode = .stack) (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q) (lanes : Nat)
    (proofs : Array PrunedMerklePaths) (root : Digest32)
    (next : WireState packet.val.profile → List (Sigma (GroupAnswer ctx Q)) → WHIRSourceChronology.Source cap (Option R))
    (observations : List Observation) (result : R)
    (run : Runs (WHIRSourceChronology.erase
      (readPhysicalPackets ctx stack Q packet.val.profile lanes proofs none (completion ctx Q packet)
        (completion_profiles ctx Q packet) (initialWireState packet.val.profile root) next)) observations (some result)) :
    ∃ state history suffix, Runs (WHIRSourceChronology.erase (next state history)) suffix (some result) ∧
      (∀ o ∈ suffix, o ∈ observations) ∧
      ∀ opening ∈ state.openings, ObservedOpening lanes proofs observations opening := by
  obtain ⟨state,history,suffix,last,subset,retained⟩ :=
    readPhysicalPackets_openings ctx stack Q packet.val.profile lanes proofs _ _ _ next observations result run
  refine ⟨state,history,suffix,last,subset,?_⟩
  intro opening member
  rcases retained opening member with old | observed
  · simp [initialWireState] at old
  · exact observed

/-- Real-answer consistency is obtained from actual real execution, not from a guessed opening certificate. It transfers the retained operational subrun to the concrete ordinary-hash computation. -/
theorem ObservedOpening.real {p : ParameterBounds.Profile} {lanes : Nat} {proofs : Array PrunedMerklePaths}
    {observations : List Observation} {opening : QueryOpening p}
    (observed : ObservedOpening lanes proofs observations opening) (C : PrimitiveOracle) (iv : Digest32)
    (answers : ∀ o ∈ observations, o.answer = realAnswer C iv o.query) :
    ∃ proof, proofs[opening.level.val]? = some proof ∧
      (runReal C iv (openQuery p opening.level lanes proof opening.root opening.sample)).view.result = some opening.result ∧
      ∀ o ∈ (runReal C iv (openQuery p opening.level lanes proof opening.root opening.sample)).view.observations,
        o ∈ observations := by
  obtain ⟨proof,trace,index,run,subset⟩ := observed
  have actual := run.real_result_trace C iv (fun o member => answers o (subset o member))
  exact ⟨proof,index,actual.1,fun o member => subset o (actual.2 ▸ member)⟩

/-- Direct real-game corollary. Its only success premise is the actual reader execution result. -/
theorem readPhysicalCompletion_real_openings {cap : Nat} {R : Type} (ctx : RawWHIRKeys.Context)
    (stack : ctx.mode = .stack) (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q) (lanes : Nat)
    (proofs : Array PrunedMerklePaths) (root : Digest32)
    (next : WireState packet.val.profile → List (Sigma (GroupAnswer ctx Q)) → WHIRSourceChronology.Source cap (Option R))
    (C : PrimitiveOracle) (iv : Digest32) (result : R)
    (accepted : (runReal C iv (WHIRSourceChronology.erase
      (readPhysicalPackets ctx stack Q packet.val.profile lanes proofs none (completion ctx Q packet)
        (completion_profiles ctx Q packet) (initialWireState packet.val.profile root) next))).view.result = some result) :
    ∃ state history suffix, Runs (WHIRSourceChronology.erase (next state history)) suffix (some result) ∧
      ∀ opening ∈ state.openings, ∃ proof, proofs[opening.level.val]? = some proof ∧
        (runReal C iv (openQuery packet.val.profile opening.level lanes proof opening.root opening.sample)).view.result =
          some opening.result ∧
        ∀ o ∈ (runReal C iv (openQuery packet.val.profile opening.level lanes proof opening.root opening.sample)).view.observations,
          o ∈ (runReal C iv (WHIRSourceChronology.erase
            (readPhysicalPackets ctx stack Q packet.val.profile lanes proofs none (completion ctx Q packet)
              (completion_profiles ctx Q packet) (initialWireState packet.val.profile root) next))).view.observations := by
  have run := runReal_runs C iv (WHIRSourceChronology.erase
    (readPhysicalPackets ctx stack Q packet.val.profile lanes proofs none (completion ctx Q packet)
      (completion_profiles ctx Q packet) (initialWireState packet.val.profile root) next))
  rw [accepted] at run
  obtain ⟨state,history,suffix,last,_,retained⟩ :=
    readPhysicalCompletion_openings ctx stack Q packet lanes proofs root next _ result run
  exact ⟨state,history,suffix,last,fun opening member =>
    (retained opening member).real C iv (runReal_answers C iv _)⟩

end Whir.WHIRPhysicalOpeningRuns
