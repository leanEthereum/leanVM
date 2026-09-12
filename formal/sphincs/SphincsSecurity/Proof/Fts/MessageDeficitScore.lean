import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.MessageAdmissibleDeficit
namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

theorem cachedMessageEntryCount_ne_top_of_finite (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    cachedMessageEntryCount cache parameter root message ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (cachedMessageEntryCount_le_enncard cache parameter root message)
  rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  finiteness

theorem cachedMessageEntryCountWhere_ne_top_of_finite (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (P : Concrete.FewTimeView → Prop) :
    cachedMessageEntryCountWhere cache parameter root message P ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (cachedMessageEntryCountWhere_le_enncard cache parameter root message P)
  rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  finiteness

noncomputable def messageDeficitScore (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) : ℝ :=
  (cachedMessageEntryCount cache parameter root message).toReal -
    1024 * (cachedMessageEntryCountWhere cache parameter root message (fun _ => True)).toReal

theorem messageDeficitScore_of_no_inputs (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hcount : cachedMessageEntryCount cache parameter root message = 0) :
    messageDeficitScore parameter root message cache ≤ 0 := by
  simp only [messageDeficitScore, hcount, ENNReal.toReal_zero, zero_sub]
  exact neg_nonpos.mpr (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)

theorem messageDeficitScore_ofReal_eq (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    ENNReal.ofReal (messageDeficitScore key.parameter key.root message cache) =
      1024 * Concrete.messageAdmissibleDeficit key message cache := by
  have hcount := cachedMessageEntryCount_ne_top_of_finite key.parameter key.root message cache hfinite
  have hadmissible := cachedMessageEntryCountWhere_ne_top_of_finite key.parameter key.root message cache hfinite (fun _ => True)
  rw [messageDeficitScore, ENNReal.ofReal_sub _ (mul_nonneg (by norm_num) ENNReal.toReal_nonneg),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hcount, ENNReal.ofReal_toReal hadmissible]
  norm_num only [ENNReal.ofReal_ofNat]
  unfold Concrete.messageAdmissibleDeficit
  rw [ENNReal.mul_sub (by intros; finiteness)]
  norm_num [ftsTreeHeight]
  congr 1
  calc
    _ = cachedMessageEntryCount cache key.parameter key.root message * ((1024 : ENNReal)⁻¹ * 1024) := by
      rw [ENNReal.inv_mul_cancel (by norm_num) (by finiteness), mul_one]
    _ = _ := by ring

end SphincsSecurity
