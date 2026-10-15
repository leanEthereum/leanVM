import Sphincs.BridgePotentialA3

/-! The rate pays every fresh answer: for each input class, the expected increase of the
potential after one fresh answer, plus the guess it records, is at most the rate of one unit of
budget under the numeric conditions. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.PotentialA

open Concrete HiddenGraph HiddenDebt HiddenBridge EncodingCode

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

theorem three_halves_le {ρ : ℝ} (h : 3 / 2 ≤ ρ) : (1 : ℝ≥0∞) + 2⁻¹ ≤ ENNReal.ofReal ρ := by
  have h1 : (1 : ℝ≥0∞) + 2⁻¹ = ENNReal.ofReal (3 / 2) := by
    rw [show (3 / 2 : ℝ) = 1 + 2⁻¹ by norm_num, ENNReal.ofReal_add (by norm_num) (by norm_num),
      ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  rw [h1]
  exact ENNReal.ofReal_le_ofReal h

variable [Params]

namespace Ctx

variable (K : Ctx)

/-! ### Lower bounds on the rate -/

theorem rate_ge (s : St) : K.vrate s + 64 * K.contactCount s ≤ K.rate s := by
  unfold rate
  exact le_self_add

theorem rate_ge_kf (s : St) : K.vrate s + K.kf s ≤ K.rate s := by
  unfold rate
  rw [add_right_comm]
  exact le_self_add

theorem vrate_armed {s : St} (h : K.Armed s) : K.vrate s = 2 := by
  unfold vrate
  rw [if_pos h]

theorem leafCount_le_contactCount (s : St) {l : Index} (hl : Landed K.p l) :
    K.leafCount s l ≤ K.contactCount s := by
  unfold contactCount
  calc K.leafCount s l = if Landed K.p l then K.leafCount s l else 0 := by rw [if_pos hl]
    _ ≤ _ := Finset.single_le_sum (f := fun l => if Landed K.p l then K.leafCount s l else 0)
        (fun _ _ => bot_le) (Finset.mem_univ l)

theorem encard_le_leafCount (s : St) {l : Index} (hnb : ¬K.BadLeaf s l) (i : ChainIndex) :
    ((K.ContactB s l i).encard : ℝ≥0∞) ≤ K.leafCount s l := by
  unfold leafCount
  rw [if_neg hnb]
  exact Finset.single_le_sum (f := fun i => ((K.ContactB s l i).encard : ℝ≥0∞)) (fun _ _ => bot_le)
    (Finset.mem_univ i)

theorem nonempty_le_leafCount (s : St) {l : Index} (hnb : ¬K.BadLeaf s l) :
    ∑ i, (if (K.ContactB s l i).Nonempty then (1 : ℝ≥0∞) else 0) ≤ K.leafCount s l := by
  unfold leafCount
  rw [if_neg hnb]
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs with hne
  · rw [← ENat.toENNReal_one, ENat.toENNReal_le]
    exact Set.one_le_encard_iff_nonempty.2 hne
  · exact bot_le

theorem not_badLeaf {s : St} (hb : ¬K.Bad s) {l : Index} (hl : Landed K.p l) : ¬K.BadLeaf s l :=
  fun h => hb (Or.inr ⟨l, hl, h⟩)

theorem armed_of_contact {s : St} {l : Index} (hl : Landed K.p l) (hnb : ¬K.BadLeaf s l) {i : ChainIndex}
    (hne : (K.ContactB s l i).Nonempty) : K.Armed s :=
  ⟨l, hl, hnb, Or.inr ⟨i, hne⟩⟩

theorem armed_of_marker {s : St} {l : Index} (hl : Landed K.p l) (hnb : ¬K.BadLeaf s l) {i : ChainIndex}
    (hm : K.Marker s l i) : K.Armed s :=
  ⟨l, hl, hnb, Or.inl ⟨i, hm⟩⟩

/-! ### The arithmetic of each class -/

section Arith

variable {xr : ℝ} (hN : Numeric K.ρ xr) (hxr : 0 ≤ xr) {Y : ℝ≥0∞} (hY : Y ≤ ENNReal.ofReal xr)
include hN

theorem rate_ge_rho (s : St) : ENNReal.ofReal K.ρ ≤ K.rate s :=
  (K.vrate_ge hN.high s).trans (K.vrate_le_rate s)

theorem one_le_rate (s : St) : (1 : ℝ≥0∞) ≤ K.rate s :=
  (one_le_ofReal (by linarith [hN.low])).trans (K.rate_ge_rho hN s)

theorem arithA (s : St) {l : Index} (hl : Landed K.p l) (i : ChainIndex) {g : ℝ≥0∞} (hg : g ≤ 1) :
    g + 2⁻¹ + (if K.Bad s then 0 else ((K.ContactB s l i).encard : ℝ≥0∞)) ≤ K.rate s := by
  have hbase : g + 2⁻¹ ≤ ENNReal.ofReal K.ρ := (add_le_add hg le_rfl).trans (three_halves_le hN.low)
  by_cases hb : K.Bad s
  · rw [if_pos hb, add_zero]
    exact hbase.trans (K.rate_ge_rho hN s)
  · rw [if_neg hb]
    have hnb := K.not_badLeaf hb hl
    by_cases hne : (K.ContactB s l i).Nonempty
    · have ha := K.armed_of_contact hl hnb hne
      have hcc := (K.encard_le_leafCount s hnb i).trans (K.leafCount_le_contactCount s hl)
      calc g + 2⁻¹ + ((K.ContactB s l i).encard : ℝ≥0∞) ≤ 1 + 1 + K.contactCount s :=
            add_le_add (add_le_add hg (by norm_num)) hcc
        _ ≤ 2 + 64 * K.contactCount s := by
            rw [one_add_one_eq_two]
            gcongr
            exact le_mul_of_one_le_left bot_le (by norm_num)
        _ = K.vrate s + 64 * K.contactCount s := by rw [K.vrate_armed ha]
        _ ≤ _ := K.rate_ge s
    · have h0 : K.ContactB s l i = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
      rw [h0, Set.encard_empty, ENat.toENNReal_zero, add_zero]
      exact hbase.trans (K.rate_ge_rho hN s)

include hxr hY in
theorem arithB (s : St) {l : Index} (hl : Landed K.p l) (i : ChainIndex) (v : Digest) {g : ℝ≥0∞}
    (hg : g ≤ 1) :
    g + (if K.BadLeaf s l ∨ v ∈ K.AAns s l i ∨ K.Marker s l i ∨ ∃ i', i' ≠ i ∧ (K.ContactB s l i').Nonempty
        then (if K.Bad s then 0 else 1)
        else Y * ((if K.Armed s then 0 else ENNReal.ofReal (2 - K.ρ)) + 64)) ≤
      K.rate s + (if v ∈ K.AAns s l i then 2⁻¹ else 0) := by
  by_cases hBL : K.BadLeaf s l ∨ v ∈ K.AAns s l i ∨ K.Marker s l i ∨ ∃ i', i' ≠ i ∧ (K.ContactB s l i').Nonempty
  · rw [if_pos hBL]
    by_cases hb : K.Bad s
    · rw [if_pos hb, add_zero]
      exact hg.trans ((K.one_le_rate hN s).trans le_self_add)
    · rw [if_neg hb]
      by_cases hobs : v ∈ K.AAns s l i
      · rw [if_pos hobs]
        calc g + 1 ≤ 1 + 1 := add_le_add hg le_rfl
          _ = (1 + 2⁻¹) + 2⁻¹ := by rw [add_assoc, ENNReal.inv_two_add_inv_two]
          _ ≤ ENNReal.ofReal K.ρ + 2⁻¹ := add_le_add (three_halves_le hN.low) le_rfl
          _ ≤ _ := add_le_add (K.rate_ge_rho hN s) le_rfl
      · rw [if_neg hobs, add_zero]
        have hnb := K.not_badLeaf hb hl
        have ha : K.Armed s := by
          rcases hBL with hbl | hv | hm | ⟨i', -, hne⟩
          · exact absurd hbl hnb
          · exact absurd hv hobs
          · exact K.armed_of_marker hl hnb hm
          · exact K.armed_of_contact hl hnb hne
        calc g + 1 ≤ 1 + 1 := add_le_add hg le_rfl
          _ = K.vrate s := by rw [K.vrate_armed ha, one_add_one_eq_two]
          _ ≤ _ := K.vrate_le_rate s
  · rw [if_neg hBL]
    have hobs : v ∉ K.AAns s l i := fun h => hBL (Or.inr (Or.inl h))
    rw [if_neg hobs, add_zero]
    by_cases ha : K.Armed s
    · rw [if_pos ha, zero_add]
      calc g + Y * 64 ≤ 1 + 1 := add_le_add hg (by rw [mul_comm]; exact arith_small hN hxr hY)
        _ = K.vrate s := by rw [K.vrate_armed ha, one_add_one_eq_two]
        _ ≤ _ := K.vrate_le_rate s
    · rw [if_neg ha]
      calc g + Y * (ENNReal.ofReal (2 - K.ρ) + 64) ≤ 1 + Y * (ENNReal.ofReal (2 - K.ρ) + 64) :=
            add_le_add hg le_rfl
        _ ≤ ENNReal.ofReal K.ρ := arith_contact hN hxr hY
        _ ≤ _ := K.rate_ge_rho hN s

include hxr hY in
theorem arithEnc (s : St) {l : Index} (hl : Landed K.p l) {g : ℝ≥0∞} (hg : g ≤ 1) :
    g + (if K.Bad s then 0 else 63 * ∑ i, (if (K.ContactB s l i).Nonempty then (1 : ℝ≥0∞) else 0)) +
      Y * (if K.Armed s then 0 else 4032 * ENNReal.ofReal (2 - K.ρ)) ≤ K.rate s := by
  by_cases hb : ¬K.Bad s ∧ ∃ i, (K.ContactB s l i).Nonempty
  · obtain ⟨hb, i, hne⟩ := hb
    have hnb := K.not_badLeaf hb hl
    have ha := K.armed_of_contact hl hnb hne
    rw [if_neg hb, if_pos ha, mul_zero, add_zero]
    have hcc := (K.nonempty_le_leafCount s hnb).trans (K.leafCount_le_contactCount s hl)
    calc g + 63 * ∑ i, (if (K.ContactB s l i).Nonempty then (1 : ℝ≥0∞) else 0)
        ≤ 1 + 64 * K.contactCount s := add_le_add hg (mul_le_mul' (by norm_num) hcc)
      _ ≤ 2 + 64 * K.contactCount s := add_le_add (by norm_num) le_rfl
      _ = K.vrate s + 64 * K.contactCount s := by rw [K.vrate_armed ha]
      _ ≤ _ := K.rate_ge s
  · have hzero : (if K.Bad s then 0 else 63 * ∑ i, (if (K.ContactB s l i).Nonempty then (1 : ℝ≥0∞) else 0))
        = 0 := by
      split_ifs with hb'
      · rfl
      · have : ∀ i, ¬(K.ContactB s l i).Nonempty := fun i hne => hb ⟨hb', i, hne⟩
        simp [this]
    rw [hzero, add_zero]
    by_cases ha : K.Armed s
    · rw [if_pos ha, mul_zero, add_zero]
      exact hg.trans (K.one_le_rate hN s)
    · rw [if_neg ha]
      calc g + Y * (4032 * ENNReal.ofReal (2 - K.ρ)) ≤ 1 + Y * (4032 * ENNReal.ofReal (2 - K.ρ)) :=
            add_le_add hg le_rfl
        _ ≤ ENNReal.ofReal K.ρ := PotentialA.arith_enc hN hxr hY
        _ ≤ _ := K.rate_ge_rho hN s

include hxr hY in
/-- A fresh forest step: its guess, and its contact weight with the pairs and the remaining budget
when it carries a record, or one unit otherwise. -/
theorem arithF (s : St) {f : FIn} {g : ℝ≥0∞} (hg : g ≤ 1) (hrec : g = 0 ∨ Recd s f) :
    g + (if Recd s f then Y + K.kf s else 1) ≤ K.rate s := by
  by_cases hr : Recd s f
  · rw [if_pos hr]
    calc g + (Y + K.kf s) ≤ (1 + Y) + K.kf s := by
          rw [← add_assoc]
          exact add_le_add (add_le_add hg le_rfl) le_rfl
      _ ≤ ENNReal.ofReal K.ρ + K.kf s := add_le_add (arith_pair hN hxr hY) le_rfl
      _ ≤ K.vrate s + K.kf s := add_le_add (K.vrate_ge hN.high s) le_rfl
      _ ≤ _ := K.rate_ge_kf s
  · have hg0 : g = 0 := hrec.resolve_right hr
    rw [hg0, if_neg hr, zero_add]
    exact K.one_le_rate hN s

end Arith

/-! ### Second-order shapes -/

theorem secondOrder_of_isA {l : Index} {i : ChainIndex} {x : HashInput} (h : K.IsA l i x) :
    SecondOrderInput K.p K.R x := by
  obtain ⟨st, pay, hst, rfl⟩ := h
  refine Or.inl ⟨topLayer, rootTree, l, i, st, pay, rfl, fun h' => ?_⟩
  have : (K.w l i).val ≤ st.val := h'.2.2.2
  omega

theorem secondOrder_of_isB {l : Index} {i : ChainIndex} {v : Digest} {x : HashInput} (h : K.IsB l i v x) :
    SecondOrderInput K.p K.R x := by
  obtain ⟨st, hst, rfl⟩ := h
  refine Or.inl ⟨topLayer, rootTree, l, i, st, v, rfl, fun h' => ?_⟩
  have : (K.w l i).val ≤ st.val := h'.2.2.2
  omega

/-! ### One fresh answer, paid by the rate -/

section Fresh

variable {xr : ℝ} (hN : Numeric K.ρ xr) (hxr : 0 ≤ xr) {y' : ℕ} (hY : (y' : ℝ≥0∞) * ν ≤ ENNReal.ofReal xr)

include hN in
theorem fresh_other {s : St} (hinv : K.Inv s) {x : HashInput} (hx : s.cache x = none)
    (hAB : ∀ l, Landed K.p l → (∀ i, ¬K.IsA l i x) ∧ ∀ i v, ¬K.IsB l i v x)
    (hE : ∀ l msg ctr, Landed K.p l → x ≠ Wots.encodingInput K.p topLayer rootTree l msg ctr)
    (hF : ∀ f : FIn, x ≠ f.input K.p)
    {w : ℝ≥0∞} (hw : w + K.kindUnit x ≤ ENNReal.ofReal K.ρ) :
    ∑' r, Pr[= r | readOutside x s] * K.pot y' r.2 + ν * w ≤ K.pot (y' + 1) s := by
  have hi := initial_none_of_fresh K.initial s hinv.prepared x hx
  have h := K.step_other y' hx hi hAB hE hF
  rw [K.pot_succ]
  calc _ ≤ K.pot y' s + ν * K.kindUnit x + ν * w := add_le_add h le_rfl
    _ = K.pot y' s + ν * (w + K.kindUnit x) := by ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (hw.trans (K.rate_ge_rho hN s)) bot_le)

include hN in
theorem fresh_A {s : St} (hinv : K.Inv s) {x : HashInput} (hx : s.cache x = none) {l : Index}
    {i : ChainIndex} (hl : Landed K.p l) (hA : K.IsA l i x) (hk : K.tg.kind x = .none) {g : ℝ≥0∞}
    (hg : g ≤ 1) :
    ∑' r, Pr[= r | readOutside x s] * K.pot y' r.2 + ν * g ≤ K.pot (y' + 1) s := by
  have hi := initial_none_of_fresh K.initial s hinv.prepared x hx
  have h := K.step_A hN.high y' hx hi hl hA hk
  have ha := K.arithA hN s hl i hg
  rw [K.pot_succ]
  calc _ ≤ K.pot y' s + (ν / 2 + ν * (if K.Bad s then 0 else ((K.ContactB s l i).encard : ℝ≥0∞))) + ν * g :=
        add_le_add h le_rfl
    _ = K.pot y' s + ν * (g + 2⁻¹ + (if K.Bad s then 0 else ((K.ContactB s l i).encard : ℝ≥0∞))) := by
        rw [div_eq_mul_inv]
        ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left ha bot_le)

include hN hxr hY in
theorem fresh_B {s : St} (hinv : K.Inv s) {x : HashInput} (hx : s.cache x = none) {l : Index}
    {i : ChainIndex} {v : Digest} (hl : Landed K.p l) (hB : K.IsB l i v x) (hk : K.tg.kind x = .none)
    {g : ℝ≥0∞} (hg : g ≤ 1) :
    ∑' r, Pr[= r | readOutside x s] * K.pot y' r.2 + ν * g ≤ K.pot (y' + 1) s := by
  have hi := initial_none_of_fresh K.initial s hinv.prepared x hx
  have h := K.step_B hN.high y' hx hi hl hB hk
  have ha := K.arithB hN hxr hY s hl i v hg
  set cr : ℝ≥0∞ := if v ∈ K.AAns s l i then ν / 2 else 0 with hcr
  have hcrtop : cr ≠ ⊤ := by
    rw [hcr]
    split_ifs
    · exact ENNReal.div_ne_top ν_ne_top (by norm_num)
    · exact ENNReal.zero_ne_top
  have hcr' : ν * (if v ∈ K.AAns s l i then 2⁻¹ else 0) = cr := by
    rw [hcr]
    split_ifs
    · rw [div_eq_mul_inv]
    · rw [mul_zero]
  refine (ENNReal.add_le_add_iff_right hcrtop).1 ?_
  rw [K.pot_succ]
  calc _ = (∑' r, Pr[= r | readOutside x s] * K.pot y' r.2 + cr) + ν * g := by ring
    _ ≤ _ + ν * g := add_le_add h le_rfl
    _ = K.pot y' s + ν * (g + _) := by ring
    _ ≤ K.pot y' s + ν * (K.rate s + (if v ∈ K.AAns s l i then 2⁻¹ else 0)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left ha bot_le)
    _ = _ := by rw [mul_add, hcr', add_assoc]

include hN hxr hY in
theorem fresh_enc {s : St} (hinv : K.Inv s) {x : HashInput} (hx : s.cache x = none) {l : Index}
    {msg : Digest} {ctr : Counter} (hl : Landed K.p l) (hxE : x = Wots.encodingInput K.p topLayer rootTree l msg ctr)
    {g : ℝ≥0∞} (hg : g + K.kindUnit x ≤ 1) :
    ∑' r, Pr[= r | readOutside x s] * K.pot y' r.2 + ν * g ≤ K.pot (y' + 1) s := by
  have hi := initial_none_of_fresh K.initial s hinv.prepared x hx
  have h := K.step_enc hN.high y' hx hi hl hxE
  have ha := K.arithEnc hN hxr hY s hl hg
  rw [K.pot_succ]
  calc _ ≤ _ + ν * g := add_le_add h le_rfl
    _ = K.pot y' s + ν * (g + K.kindUnit x +
        (if K.Bad s then 0 else 63 * ∑ i, (if (K.ContactB s l i).Nonempty then (1 : ℝ≥0∞) else 0)) +
        (y' : ℝ≥0∞) * ν * (if K.Armed s then 0 else 4032 * ENNReal.ofReal (2 - K.ρ))) := by ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left ha bot_le)

include hN hxr hY in
theorem fresh_fchain {s : St} (hinv : K.Inv s) {x : HashInput} (hx : s.cache x = none) {f : FIn}
    (hxF : x = f.input K.p) (hk : K.tg.kind x = .none) {g : ℝ≥0∞} (hg : g ≤ 1) (hrec : g = 0 ∨ Recd s f) :
    ∑' r, Pr[= r | readOutside x s] * K.pot y' r.2 + ν * g ≤ K.pot (y' + 1) s := by
  have hi := initial_none_of_fresh K.initial s hinv.prepared x hx
  have h := K.step_fchain y' hx hi hxF hk
  have ha := K.arithF hN hxr hY s hg hrec
  rw [K.pot_succ]
  calc _ ≤ _ + ν * g := add_le_add h le_rfl
    _ = K.pot y' s + ν * (g + _) := by ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left ha bot_le)

end Fresh

end Ctx

end Sphincs.Security.PotentialA
