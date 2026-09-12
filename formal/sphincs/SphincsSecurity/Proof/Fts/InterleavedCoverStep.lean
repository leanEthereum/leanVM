import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CachedSigningViews
import SphincsSecurity.Proof.Fts.FewTimeConditionalCoverage
import SphincsSecurity.Proof.Fts.JointProbeMessageReserve
import SphincsSecurity.Proof.Fts.FewTimePrehit
import SphincsSecurity.Proof.Fts.FewTimeWeightedOriginRace
import SphincsSecurity.Proof.Base.RomQueryCharge
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

abbrev CoverLogState := QueryCache HashSpec × QueryLog SigningSpec

theorem logTracedMappedAdversaryImpl_run_map (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CoverLogState) :
    (logTracedMappedAdversaryImpl key input).run state =
      (fun result => (result.1, (result.2, state.2 ++ signingLogFragment input result.1))) <$>
        (unloggedMappedAdversaryImpl key input).run state.1 := by
  rw [logTracedMappedAdversaryImpl, QueryImpl.extendState_apply]
  simp only [signingLogUpdate, bind_pure_comp]

theorem logTracedMappedAdversaryImpl_cache_le (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CoverLogState)
    (result : (OracleWorld + SigningSpec).Range input × CoverLogState)
    (hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)) : state.1 ≤ result.2.1 := by
  rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
  obtain ⟨base, hbase, rfl⟩ := hresult
  exact unloggedMappedAdversaryImpl_cache_le key input state.1 base hbase

theorem logTracedMappedAdversaryImpl_signingDigestsCached (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (result : (OracleWorld + SigningSpec).Range input × CoverLogState)
    (hresult : result ∈ support ((logTracedMappedAdversaryImpl key input).run state)) :
    SigningDigestsCached key.parameter result.2.1 key.root result.2.2 := by
  rw [logTracedMappedAdversaryImpl_run_map, support_map] at hresult
  obtain ⟨base, hbase, rfl⟩ := hresult
  cases input with
  | inl world =>
      simpa only [signingLogFragment, List.append_nil] using hsigned.mono
        (unloggedMappedAdversaryImpl_cache_le key (.inl world) state.1 base hbase)
  | inr message =>
      change base ∈ support ((simulateQ romImpl (sign key message)).run state.1) at hbase
      rw [← simulateQ_signWithView_fst_run, support_map] at hbase
      obtain ⟨viewed, hviewed, rfl⟩ := hbase
      exact SigningDigestsCached.after_signing key message state.1 viewed.2 state.2 hsigned viewed.1.1 viewed.1.2 hviewed

end SphincsSecurity.Concrete
