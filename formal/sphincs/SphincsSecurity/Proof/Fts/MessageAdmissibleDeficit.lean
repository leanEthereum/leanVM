import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.MessageNormalizedReuse
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def messageAdmissibleDeficit (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  cachedMessageEntryCount cache key.parameter key.root message * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ -
    cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True)

theorem messageDigestFreshRate_balance (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    messageDigestFreshRate key message cache * ((2 ^ randomnessBits : Nat) : ENNReal) +
      (cachedMessageEntryCount cache key.parameter key.root message + (digestAttemptLimit : ENNReal)) *
        ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ = ((2 ^ 118 : Nat) : ENNReal) := by
  let count := cachedMessageEntryCount cache key.parameter key.root message + (digestAttemptLimit : ENNReal)
  let space : ENNReal := (2 ^ randomnessBits : Nat)
  let admissible : ENNReal := ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹
  have hcount : count ≤ space := by
    apply (add_le_add ((cachedMessageEntryCount_le_enncard cache key.parameter key.root message).trans hcache) le_rfl).trans
    change (q : ENNReal) + (digestAttemptLimit : ENNReal) ≤ ((2 ^ randomnessBits : Nat) : ENNReal)
    rw [← Nat.cast_add]
    exact_mod_cast (show q + digestAttemptLimit ≤ 2 ^ randomnessBits by norm_num [digestAttemptLimit, randomnessBits] at *; omega)
  have hzero : space ≠ 0 := by dsimp only [space]; positivity
  have htop : space ≠ ⊤ := by dsimp only [space]; finiteness
  have hfraction : count * space⁻¹ ≤ 1 :=
    (mul_le_mul' hcount le_rfl).trans_eq (ENNReal.mul_inv_cancel hzero htop)
  have hcancel : (count * space⁻¹) * (space * admissible) = count * admissible := by
    rw [mul_assoc, ← mul_assoc space⁻¹, ENNReal.inv_mul_cancel hzero htop, one_mul]
  change ((1 - count * space⁻¹) * admissible) * space + count * admissible = _
  calc
    _ = ((1 - count * space⁻¹) + count * space⁻¹) * (space * admissible) := by rw [← hcancel]; ring
    _ = space * admissible := by rw [tsub_add_cancel_of_le hfraction, one_mul]
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by dsimp only [space, admissible]; finiteness) (by finiteness)).mp
      norm_num [space, admissible, ENNReal.toReal_mul, ENNReal.toReal_inv, randomnessBits, ftsTreeHeight]

theorem normalizedMessageReuseWeight_le_deficit (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    normalizedMessageReuseWeight key message cache ≤
      (((2 ^ 118 : Nat) : ENNReal) - ((digestAttemptLimit : ENNReal) * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ +
        messageAdmissibleDeficit key message cache))⁻¹ := by
  rw [normalizedMessageReuseWeight_eq_inv key message cache q hq hcache]
  apply ENNReal.inv_le_inv.mpr
  apply tsub_le_iff_left.mpr
  rw [← messageDigestFreshRate_balance key message cache q hq hcache, add_mul]
  have hcount : cachedMessageEntryCount cache key.parameter key.root message * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ ≤
      cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) + messageAdmissibleDeficit key message cache :=
    le_add_tsub
  have h := add_le_add (add_le_add (le_refl (messageDigestFreshRate key message cache * ((2 ^ randomnessBits : Nat) : ENNReal))) hcount)
    (le_refl ((digestAttemptLimit : ENNReal) * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹))
  convert h using 1 <;> first | rfl | ring

theorem normalizedMessageReuseWeight_le_near_uniform_of_deficit
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q)
    (hdeficit : messageAdmissibleDeficit key message cache ≤ ((2 ^ 83 : Nat) : ENNReal)) :
    normalizedMessageReuseWeight key message cache ≤ (1025 / 1024 : ENNReal) * ((2 ^ 118 : Nat) : ENNReal)⁻¹ := by
  apply (normalizedMessageReuseWeight_le_deficit key message cache q hq hcache).trans
  apply (ENNReal.inv_le_inv.mpr (tsub_le_tsub_left (add_le_add le_rfl hdeficit) _)).trans
  have hsmall : (digestAttemptLimit : ENNReal) * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ + ((2 ^ 83 : Nat) : ENNReal) <
      ((2 ^ 118 : Nat) : ENNReal) := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, digestAttemptLimit, ftsTreeHeight]
  apply (ENNReal.toReal_le_toReal (ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr hsmall))) (by finiteness)).mp
  rw [ENNReal.toReal_inv, ENNReal.toReal_sub_of_le hsmall.le (by finiteness)]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div, digestAttemptLimit, ftsTreeHeight]

theorem exactDigestReuseWeight_le_near_uniform_of_deficit
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q)
    (hdeficit : messageAdmissibleDeficit key message cache ≤ ((2 ^ 83 : Nat) : ENNReal)) :
    exactDigestReuseWeight key message cache ≤ (1025 / 1024 : ENNReal) * ((2 ^ 118 : Nat) : ENNReal)⁻¹ :=
  (exactDigestReuseWeight_le_normalizedMessage key message cache q hq hcache).trans
    (normalizedMessageReuseWeight_le_near_uniform_of_deficit key message cache q hq hcache hdeficit)

end SphincsSecurity.Concrete
