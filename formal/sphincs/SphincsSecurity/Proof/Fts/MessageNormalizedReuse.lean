import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.MessageDigestHazard
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def normalizedMessageReuseWeight (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  messageDigestReuseWeight key message cache /
    (1 + cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * messageDigestReuseWeight key message cache)

theorem normalizedMessageReuseWeight_eq_inv (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    normalizedMessageReuseWeight key message cache =
      (cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) +
        messageDigestFreshRate key message cache * ((2 ^ randomnessBits : Nat) : ENNReal))⁻¹ := by
  let count := cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True)
  let reuse := messageDigestReuseWeight key message cache
  have hreuseTop : reuse ≠ ⊤ := messageDigestReuseWeight_ne_top key message cache q hq hcache
  have hreuseZero : reuse ≠ 0 := by
    unfold reuse messageDigestReuseWeight
    rw [div_eq_mul_inv]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (by finiteness))
      (ENNReal.inv_ne_zero.mpr (messageDigestFreshRate_ne_top key message cache))
  have hinv : reuse⁻¹ = messageDigestFreshRate key message cache * ((2 ^ randomnessBits : Nat) : ENNReal) := by
    unfold reuse messageDigestReuseWeight
    rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.mpr (by finiteness)))
      (Or.inl (ENNReal.inv_ne_top.mpr (by positivity))), inv_inv, inv_inv, mul_comm]
  have hfactor : 1 + count * reuse = reuse * (count + reuse⁻¹) := by
    rw [mul_add, ENNReal.mul_inv_cancel hreuseZero hreuseTop]
    ring
  change reuse * (1 + count * reuse)⁻¹ = _
  rw [hfactor, ENNReal.mul_inv (Or.inl hreuseZero) (Or.inl hreuseTop), ← mul_assoc,
    ENNReal.mul_inv_cancel hreuseZero hreuseTop, one_mul, hinv]

theorem exactDigestReuseWeight_le_normalizedMessage (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    exactDigestReuseWeight key message cache ≤ normalizedMessageReuseWeight key message cache := by
  have hcount : cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness)
      ((cachedMessageEntryCountWhere_le_enncard cache key.parameter key.root message (fun _ => True)).trans hcache)
  have hreuse := messageDigestReuseWeight_ne_top key message cache q hq hcache
  have hmass : freshDigestSelectionProbability key message cache +
      cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache ≤ 1 :=
    le_self_add.trans_eq (freshSelection_add_count_exactWeight_add_exhaustion key message cache)
  unfold normalizedMessageReuseWeight
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness))).mpr
  calc
    _ = exactDigestReuseWeight key message cache +
        (cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache) *
          messageDigestReuseWeight key message cache := by ring
    _ ≤ freshDigestSelectionProbability key message cache * messageDigestReuseWeight key message cache +
        (cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache) *
          messageDigestReuseWeight key message cache :=
      add_le_add (exactDigestReuseWeight_le_fresh_mul_messageReuseWeight key message cache q hq hcache) le_rfl
    _ = (freshDigestSelectionProbability key message cache +
        cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache) *
          messageDigestReuseWeight key message cache := by rw [add_mul]
    _ ≤ _ := mul_le_of_le_one_left' hmass

end SphincsSecurity.Concrete
