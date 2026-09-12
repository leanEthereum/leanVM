import SphincsSecurity.Proof.Base.Prelude
namespace SphincsSecurity.Concrete.PrimitiveMessagePotential

noncomputable def value (space probes remaining : ℝ) : ℝ :=
  1 - ((space - probes - remaining) / (space - probes)) ^ 2

theorem initial (space budget : ℝ) (hspace : space ≠ 0) :
    value space 0 budget = 2 * (budget / space) - (budget / space) ^ 2 := by
  unfold value
  simp only [sub_zero]
  field_simp
  ring

theorem probe_balance (space probes remaining : ℝ)
    (hspace : space - probes ≠ 0) (hnext : space - (probes + 1) ≠ 0) :
    value space probes 1 + (1 - value space probes 1) * value space (probes + 1) remaining =
      value space probes (remaining + 1) := by
  unfold value
  field_simp
  ring

theorem hazard (space probes : ℝ) (hspace : space - probes ≠ 0) :
    value space probes 1 = 1 - (1 - (space - probes)⁻¹) ^ 2 := by
  unfold value
  field_simp

theorem toReal_hazard (space probes : Nat) (hprobes : probes < space) :
    (1 - (1 - ((space - probes : Nat) : ENNReal)⁻¹) ^ 2 : ENNReal).toReal = value space probes 1 := by
  have hminimum : 1 ≤ space - probes := Nat.sub_pos_of_lt hprobes
  have hinverse : ((space - probes : Nat) : ENNReal)⁻¹ ≤ 1 := by
    apply ENNReal.inv_le_one.mpr
    exact_mod_cast hminimum
  have hsub : (1 - ((space - probes : Nat) : ENNReal)⁻¹ : ENNReal) ≤ 1 := tsub_le_self
  have hsquare : (1 - ((space - probes : Nat) : ENNReal)⁻¹) ^ 2 ≤ (1 : ENNReal) := by
    simpa only [pow_two, mul_one] using mul_le_mul' hsub hsub
  have hden : (space : ℝ) - probes ≠ 0 := ne_of_gt (sub_pos.mpr (Nat.cast_lt.mpr hprobes))
  rw [ENNReal.toReal_sub_of_le hsquare (by simp), ENNReal.toReal_one, ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le hinverse (by simp), ENNReal.toReal_one, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Nat.cast_sub hprobes.le, hazard _ _ hden]

theorem bounds (space probes remaining : ℝ) (hremaining : 0 ≤ remaining)
    (hbudget : probes + remaining < space) :
    0 ≤ value space probes remaining ∧ value space probes remaining < 1 := by
  have hden : 0 < space - probes := by linarith
  have hnum : 0 < space - probes - remaining := by linarith
  have hratio : 0 < (space - probes - remaining) / (space - probes) := div_pos hnum hden
  have hone : (space - probes - remaining) / (space - probes) ≤ 1 := by
    apply (div_le_one₀ hden).mpr
    linarith
  unfold value
  constructor
  · nlinarith [sq_nonneg ((space - probes - remaining) / (space - probes)),
      mul_self_le_mul_self hratio.le hone]
  · nlinarith [sq_pos_of_pos hratio]

theorem message_increment (space probes remaining : ℝ) (hspace : space - probes ≠ 0) :
    value space probes (remaining + 1) - value space probes remaining =
      (2 * (space - probes - remaining) - 1) / (space - probes) ^ 2 := by
  unfold value
  field_simp
  ring

theorem message_payment (space probes remaining : ℝ) (hspace : 0 < space)
    (hprobes : 0 ≤ probes) (hremaining : 0 ≤ remaining)
    (hbudget : 2 * (probes + remaining + 1) ≤ space) :
    1 / space + value space probes remaining ≤ value space probes (remaining + 1) := by
  have hden : 0 < space - probes := by linarith
  have hnum : space ≤ 2 * (space - probes - remaining) - 1 := by linarith
  have hsq : (space - probes) ^ 2 ≤ space ^ 2 := by nlinarith
  have hpay : 1 / space ≤ (2 * (space - probes - remaining) - 1) / (space - probes) ^ 2 := by
    calc
      1 / space = space / space ^ 2 := by field_simp
      _ ≤ space / (space - probes) ^ 2 := div_le_div_of_nonneg_left hspace.le (sq_pos_of_pos hden) hsq
      _ ≤ _ := (div_le_div_iff_of_pos_right (sq_pos_of_pos hden)).mpr hnum
  rw [← message_increment space probes remaining (ne_of_gt hden)] at hpay
  linarith

theorem mono_remaining (space probes before after : ℝ) (hbefore : 0 ≤ before)
    (horder : before ≤ after) (hbudget : probes + after < space) :
    value space probes before ≤ value space probes after := by
  have hden : 0 < space - probes := by linarith
  have hsmall : 0 ≤ (space - probes - after) / (space - probes) := div_nonneg (by linarith) hden.le
  have hratio : (space - probes - after) / (space - probes) ≤ (space - probes - before) / (space - probes) :=
    (div_le_div_iff_of_pos_right hden).mpr (by linarith)
  unfold value
  nlinarith [mul_self_le_mul_self hsmall hratio]

theorem mono_probes (space before after remaining : ℝ) (hremaining : 0 ≤ remaining)
    (horder : before ≤ after) (hbudget : after + remaining < space) :
    value space before remaining ≤ value space after remaining := by
  have hafter : 0 < space - after := by linarith
  have hbefore : 0 < space - before := by linarith
  have hquot : remaining / (space - before) ≤ remaining / (space - after) :=
    div_le_div_of_nonneg_left hremaining hafter (by linarith)
  have hratio (probes : ℝ) (hden : space - probes ≠ 0) :
      (space - probes - remaining) / (space - probes) = 1 - remaining / (space - probes) := by
    field_simp
  have hnonnegative : 0 ≤ 1 - remaining / (space - after) := by
    have hle := (div_le_one₀ hafter).mpr (show remaining ≤ space - after by linarith)
    linarith
  unfold value
  rw [hratio before hbefore.ne', hratio after hafter.ne']
  nlinarith [mul_self_le_mul_self hnonnegative (show 1 - remaining / (space - after) ≤
    1 - remaining / (space - before) by linarith)]

theorem nonmessage_step (space probes after remaining probability : ℝ)
    (hremaining : 0 ≤ remaining) (hafter : after ≤ probes + 1) (hbudget : probes + remaining + 1 < space)
    (hhazard : probability ≤ value space probes 1) :
    probability + (1 - probability) * value space after remaining ≤ value space probes (remaining + 1) := by
  have hnext := bounds space (probes + 1) remaining hremaining (by linarith)
  have hfirst := bounds space probes 1 (by norm_num) (by linarith)
  have hcontinuation := mono_probes space after (probes + 1) remaining hremaining hafter (by linarith)
  have hsurvive : 0 ≤ 1 - probability := by linarith
  calc
    _ ≤ probability + (1 - probability) * value space (probes + 1) remaining :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hcontinuation hsurvive)
    _ ≤ value space probes 1 + (1 - value space probes 1) * value space (probes + 1) remaining := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hhazard) (sub_nonneg.mpr hnext.2.le)]
    _ = _ := probe_balance space probes remaining (by linarith) (by linarith)

theorem messages_payment (space probes remaining : ℝ) (calls : Nat) (hspace : 0 < space)
    (hprobes : 0 ≤ probes) (hremaining : 0 ≤ remaining) (hbudget : 2 * (probes + remaining + calls) ≤ space) :
    (calls : ℝ) / space + value space probes remaining ≤ value space probes (remaining + calls) := by
  induction calls with
  | zero => simp
  | succ calls ih =>
      have hcast : ((calls + 1 : Nat) : ℝ) = (calls : ℝ) + 1 := by push_cast; rfl
      rw [hcast] at hbudget ⊢
      have hbefore := ih (by linarith)
      have hlast := message_payment space probes (remaining + calls) hspace hprobes
        (by positivity) (by linarith)
      have heq : remaining + ((calls : ℝ) + 1) = (remaining + calls) + 1 := by ring
      rw [heq]
      calc
        _ = 1 / space + ((calls : ℝ) / space + value space probes remaining) := by ring
        _ ≤ 1 / space + value space probes (remaining + calls) := add_le_add le_rfl hbefore
        _ ≤ _ := hlast

theorem work_payment (space probes remaining : ℝ) (messages cost : Nat) (hspace : 0 < space)
    (hprobes : 0 ≤ probes) (hremaining : 0 ≤ remaining) (hcost : messages ≤ cost)
    (hbudget : 2 * (probes + remaining + cost) ≤ space) :
    (messages : ℝ) / space + value space probes remaining ≤ value space probes (remaining + cost) := by
  have hm : (messages : ℝ) ≤ cost := by exact_mod_cast hcost
  exact (add_le_add (div_le_div_of_nonneg_right hm hspace.le) le_rfl).trans
    (messages_payment space probes remaining cost hspace hprobes hremaining hbudget)

end SphincsSecurity.Concrete.PrimitiveMessagePotential
