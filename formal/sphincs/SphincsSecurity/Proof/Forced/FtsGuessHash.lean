import SphincsSecurity.Proof.Forced.FtsGuessSigning
import SphincsSecurity.Proof.Forced.SecretGuessErasure
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open FtsProbeSimulation (decodeProbe? decodeProbe?_eq_some_iff decodeProbe?_eq_none_iff)
open FtsGuessSigning (Coordinate)
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def coordinate (probe : FtsSecretProbe) : Coordinate := (probe.index, probe.tree, probe.leafIdx)

theorem probe_canonical_iff (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels) (probe : FtsSecretProbe) :
    probe.input parameter = canonicalGraphInput parameter otsSecret ftsSecret (.ftsLeaf probe.index probe.tree probe.leafIdx) labels ↔
      ftsSecret probe.index probe.tree probe.leafIdx = probe.candidate := by
  simp only [FtsSecretProbe.input, canonicalGraphInput, canonicalGraphSlots, Position.domain,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  constructor
  · intro h
    exact (digestBytes_injective (tweakableHashInput_injective parameter (by trivial) (by trivial) h).2).symm
  · intro h
    rw [h]

theorem programmedHash_probe (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels)
    (residual : QueryImpl HashSpec Id) (probe : FtsSecretProbe) :
    programmedHash parameter otsSecret ftsSecret labels residual (probe.input parameter) =
      if ftsSecret probe.index probe.tree probe.leafIdx = probe.candidate then labels (.ftsLeaf probe.index probe.tree probe.leafIdx)
      else residual (probe.input parameter) := by
  have hd : decodePosition parameter (probe.input parameter) = some (.ftsLeaf probe.index probe.tree probe.leafIdx) :=
    (decodePosition_some_iff _ _ _).mpr ⟨digestBytes probe.candidate, rfl⟩
  rw [programmedHash, hd, Option.elim_some]
  by_cases hh : ftsSecret probe.index probe.tree probe.leafIdx = probe.candidate
  · rw [if_pos ((probe_canonical_iff parameter otsSecret ftsSecret labels probe).mpr hh), if_pos hh]
  · rw [if_neg ((probe_canonical_iff parameter otsSecret ftsSecret labels probe).not.mpr hh), if_neg hh]

theorem programmedHash_nonprobe (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (left right : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels)
    (residual : QueryImpl HashSpec Id) (input : HashInput) (hn : decodeProbe? parameter input = none) :
    programmedHash parameter otsSecret left labels residual input = programmedHash parameter otsSecret right labels residual input := by
  have hn := (decodeProbe?_eq_none_iff parameter input).mp hn
  rw [programmedHash, programmedHash]
  cases hd : decodePosition parameter input with
  | none => rfl
  | some position =>
      simp only [Option.elim_some]
      cases position <;> try rfl
      case ftsLeaf index tree leaf =>
        have hne (secrets : Index → FtsTree → FtsLeaf → Digest) :
            input ≠ canonicalGraphInput parameter otsSecret secrets (.ftsLeaf index tree leaf) labels := by
          intro he
          apply hn ⟨index, tree, leaf, secrets index tree leaf⟩
          simpa only [canonicalGraphInput, canonicalGraphSlots, Position.domain, List.flatMap_cons,
            List.flatMap_nil, List.append_nil, FtsSecretProbe.input] using he.symm
        rw [if_neg (hne left), if_neg (hne right)]

noncomputable def auxiliaryHash (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (labels : CanonicalGraphLabels) (residual : QueryImpl HashSpec Id) : QueryImpl HashSpec Id :=
  fun input => match decodeProbe? parameter input with
  | none => programmedHash parameter otsSecret (fun _ _ _ => 0) labels residual input
  | some _ => residual input

abbrev SigningRecordSpec := Message →ₒ PublicSigningRecord
abbrev Auxiliary := OracleWorld + SigningRecordSpec
abbrev World := SecretGuessObservation.World Auxiliary Coordinate Digest

noncomputable def hashProgram (parameter : PublicParameter) (labels : CanonicalGraphLabels) (input : HashInput) :
    OracleComp World HashOutput :=
  match decodeProbe? parameter input with
  | none => liftM (World.query (.inl (.inl (.inr input))))
  | some probe => do
      let hit : Bool ← liftM (World.query (.inr (.inl (coordinate probe, probe.candidate))))
      if hit then pure (labels (.ftsLeaf probe.index probe.tree probe.leafIdx))
      else liftM (World.query (.inl (.inl (.inr input))))

noncomputable def worldProgram (parameter : PublicParameter) (labels : CanonicalGraphLabels) :
    QueryImpl OracleWorld (OracleComp World)
  | .inl input => liftM (World.query (.inl (.inl (.inl input))))
  | .inr input => hashProgram parameter labels input

noncomputable abbrev fixedAnswers (auxiliary : QueryImpl Auxiliary ProbComp) (secrets : Coordinate → Digest) :
    QueryImpl World ProbComp := SecretGuessObservation.fixedAnswers auxiliary secrets

noncomputable def auxiliaryAnswers (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (labels : CanonicalGraphLabels) (residual : QueryImpl HashSpec Id)
    (signer : QueryImpl SigningRecordSpec ProbComp) : QueryImpl Auxiliary ProbComp
  | .inl input => fixedHashWorld (auxiliaryHash parameter otsSecret labels residual) input
  | .inr message => signer message

theorem fixed_hashProgram (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels) (residual : QueryImpl HashSpec Id)
    (signer : QueryImpl SigningRecordSpec ProbComp) (input : HashInput) :
    simulateQ (fixedAnswers (auxiliaryAnswers parameter otsSecret labels residual signer)
      (FtsGuessSigning.secretTable ftsSecret)) (hashProgram parameter labels input) =
      pure (programmedHash parameter otsSecret ftsSecret labels residual input) := by
  cases hd : decodeProbe? parameter input with
  | none =>
      simp only [hashProgram, hd, simulateQ_spec_query, fixedAnswers, SecretGuessObservation.fixedAnswers,
        auxiliaryAnswers, fixedHashWorld, auxiliaryHash]
      rw [programmedHash_nonprobe parameter otsSecret (fun _ _ _ => 0) ftsSecret labels residual input hd]
  | some probe =>
      have hi := (decodeProbe?_eq_some_iff parameter input probe).mp hd
      rw [hashProgram, hd, simulateQ_bind, simulateQ_spec_query]
      simp only [fixedAnswers, SecretGuessObservation.fixedAnswers, pure_bind, FtsGuessSigning.secretTable, Equiv.coe_fn_mk, coordinate]
      split
      · rename_i hh
        simp only [decide_eq_true_eq] at hh
        rw [simulateQ_pure, ← hi, programmedHash_probe, if_pos hh]
      · rename_i hh
        have hn : ftsSecret probe.index probe.tree probe.leafIdx ≠ probe.candidate := by simpa only [decide_eq_true_eq] using hh
        rw [simulateQ_spec_query]
        simp only [SecretGuessObservation.fixedAnswers, auxiliaryAnswers, fixedHashWorld, auxiliaryHash, hd]
        rw [← hi, programmedHash_probe, if_neg hn]

theorem fixed_worldProgram (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels) (residual : QueryImpl HashSpec Id)
    (signer : QueryImpl SigningRecordSpec ProbComp) (input : OracleWorld.Domain) :
    simulateQ (fixedAnswers (auxiliaryAnswers parameter otsSecret labels residual signer)
      (FtsGuessSigning.secretTable ftsSecret)) (worldProgram parameter labels input) =
      fixedHashWorld (programmedHash parameter otsSecret ftsSecret labels residual) input := by
  cases input with
  | inl input => rfl
  | inr input => exact fixed_hashProgram parameter otsSecret ftsSecret labels residual signer input

theorem fixed_world_translate {Result : Type} (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels) (residual : QueryImpl HashSpec Id)
    (signer : QueryImpl SigningRecordSpec ProbComp) (computation : OracleComp OracleWorld Result) :
    simulateQ (fixedAnswers (auxiliaryAnswers parameter otsSecret labels residual signer)
      (FtsGuessSigning.secretTable ftsSecret)) (simulateQ (worldProgram parameter labels) computation) =
      simulateQ (fixedHashWorld (programmedHash parameter otsSecret ftsSecret labels residual)) computation := by
  rw [← QueryImpl.simulateQ_compose]
  have hi : (fixedAnswers (auxiliaryAnswers parameter otsSecret labels residual signer)
      (FtsGuessSigning.secretTable ftsSecret)).compose (worldProgram parameter labels) =
      fixedHashWorld (programmedHash parameter otsSecret ftsSecret labels residual) := by
    funext input
    exact fixed_worldProgram parameter otsSecret ftsSecret labels residual signer input
  rw [hi]

end SphincsSecurity.Concrete.FtsGuessHash
