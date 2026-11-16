module

public import Quantum.Xmss.EncCost
public import Quantum.Xmss.Assembly.Costs

@[expose] public section

/-!
# The classical costs of the event bound, on a memory holding the selections

Security's cost debts, for any memory `M` that holds Events' selections through `get : M →
Selections` and `put : M → Selections → M` with `get (put m s) = s`. Security's memory
`Finset ValPos × Selections` is the case `get = Prod.snd`, `put m s = (m.1, s)`: Template's
`liftRead (.readH z upd)` is `.readH z fun m o ↦ (m.1, upd m.2 o)`, which keeps the label
(`liftUpd_cases`, `get_liftUpd`). The bad set is any `B` that is Events' `Bad L N` read through
`get` (Security's `BadR`, by `Iff.rfl`). Generic instances keep the kernel away from the concrete
`Fintype`/`DecidableEq` terms of the labelled memory.

* `PR_proj`, `PP_proj`: `readPs_family_proj`, `zero_family_proj`.
* `keyFacts`: `keyFacts_of_trials`, from the trials of a key, each a finite family of branch states
  (`survive_readH_le` and `selectReadCwE_le` through `get`: `survive_getSelectRead_le`,
  `encWt_le`).
* `clsSplit`, per key: `sum_flipCost_trials_le` bounds the flip costs of a key's selecting reads by
  `keyCost` (`flipCost_getSelectReadCw_le`, branches summed by Cauchy-Schwarz).
* `clsTotal`: `clsTotal_of`, the average over good tables of the keys' bounds and the rest, from a
  per-key cap `Cm` on `C`, a cap `nK` on the keys with trials and caps on `∑ p` and `rest`.
-/

open Matrix
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Xmss.Assembly

open Quantum Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss

/-! ## The projectors -/

section proj

variable {M : Type} [Fintype M] [DecidableEq M]

/-- **`PR_proj`** for projectors `readPs` (FlipCost). -/
theorem readPs_family_proj {Θ P : Type} (SR : Θ → P → HwReg X Z M → Prop)
    [∀ θ c, DecidablePred (SR θ c)] (θ : Θ) (c : P) :
    (readPs (SR θ c))ᴴ = readPs (SR θ c) ∧ readPs (SR θ c) * readPs (SR θ c) = readPs (SR θ c) :=
  readPs_proj (SR θ c)

/-- **`PP_proj`** for the zero projectors. -/
theorem zero_family_proj {Θ P n : Type} [Fintype n] (_ : Θ) (_ : P) :
    (0 : Matrix n n ℂ)ᴴ = 0 ∧ (0 : Matrix n n ℂ) * 0 = 0 :=
  ⟨conjTranspose_zero, mul_zero 0⟩

end proj

/-! ## The labelled read updates -/

section label

variable {S : Type}

/-- Template's read update on the labelled memory: the label stays. -/
def liftUpd (upd : Selections → Option X → Selections) :
    Finset S × Selections → Option X → Finset S × Selections :=
  fun m o ↦ (m.1, upd m.2 o)

theorem get_liftUpd (upd : Selections → Option X → Selections) (m : Finset S × Selections)
    (o : Option X) : (liftUpd upd m o).2 = upd m.2 o :=
  rfl

/-- The labelled update keeps the memory or records a selection, if `upd` does. -/
theorem liftUpd_cases {upd : Selections → Option X → Selections} {sel : Selections → Selections}
    {m : Finset S × Selections} {v : X} (h : upd m.2 (some v) = m.2 ∨ upd m.2 (some v) = sel m.2) :
    liftUpd upd m (some v) = m ∨ liftUpd upd m (some v) = (m.1, sel m.2) := by
  rcases h with h | h
  · exact .inl (Prod.ext rfl h)
  · exact .inr (Prod.ext rfl h)

end label

/-! ## Selecting reads on a memory holding the selections -/

section lift

variable {M : Type} [Fintype M] [DecidableEq M]

omit [Fintype M] [DecidableEq M] in
/-- The memories whose key `(l, e)` has no selection. -/
def unselL (get : M → Selections) (l : Layer) (e : KeyIndex) : Set M := {m | get m l e = none}

instance unselLDec (get : M → Selections) (l : Layer) (e : KeyIndex) :
    DecidablePred (· ∈ unselL get l e) :=
  fun m ↦ inferInstanceAs (Decidable (get m l e = none))

/-- The weight of the states where key `(l, e)` is unselected. -/
noncomputable def unselWt (get : M → Selections) (l : Layer) (e : KeyIndex)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ :=
  ∑ q, if q.2.2.2 ∈ unselL get l e then (σ q q).re else 0

/-- The weight of the outcomes of the read `.readH z upd` that leave key `(l, e)` unselected. -/
noncomputable def survWt (get : M → Selections) (l : Layer) (e : KeyIndex) (z : Z)
    (upd : M → Option X → M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ :=
  ∑ r : Option X × M, if upd r.2 r.1 ∈ unselL get l e then
    (MatrixMap.conj (hwReadKraus (.readH z upd) r) σ).trace.re else 0

/-- The weight of the states of `SR` (the selection reads). -/
noncomputable def selWt (SR : HwReg X Z M → Prop) [DecidablePred SR]
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ :=
  ∑ q, if SR q.2 then (σ q q).re else 0

/-- The Enc term of a selecting read of key `(l, e)`: the codeword flips of the states of `SR`
outside `B`. -/
noncomputable def encWt (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)] (L : HonestTable)
    (l : Layer) (e : KeyIndex) (SR : HwReg X Z M → Prop) [DecidablePred SR]
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ :=
  ∑ q, if SR q.2 ∧ q.2 ∉ B then
    ((msgCwCount L (union q.2.2.1 q.2.1) l e * 2 ^ 960 : ℕ) : ℝ) / Fintype.card X * (σ q q).re
  else 0

section nonneg

variable {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
include hσ

omit [DecidableEq M] in
theorem unselWt_nonneg (get : M → Selections) (l : Layer) (e : KeyIndex) :
    0 ≤ unselWt get l e σ :=
  Finset.sum_nonneg fun q _ ↦ by
    have : 0 ≤ (σ q q).re := (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    split_ifs
    · exact this
    · exact le_rfl

omit [DecidableEq M] in
theorem selWt_nonneg (SR : HwReg X Z M → Prop) [DecidablePred SR] : 0 ≤ selWt SR σ :=
  Finset.sum_nonneg fun q _ ↦ by
    have : 0 ≤ (σ q q).re := (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    split_ifs
    · exact this
    · exact le_rfl

omit [DecidableEq M] in
theorem encWt_nonneg (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)] (L : HonestTable)
    (l : Layer) (e : KeyIndex) (SR : HwReg X Z M → Prop) [DecidablePred SR] :
    0 ≤ encWt B L l e SR σ :=
  Finset.sum_nonneg fun q _ ↦ by
    have : 0 ≤ (σ q q).re := (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    split_ifs
    · positivity
    · exact le_rfl

end nonneg

variable {L : HonestTable} {N : ℕ}

omit [Fintype M] [DecidableEq M] in
/-- Filter cards are monotone in the predicate. The decidability instances are implicit, taken
from the statements by unification: synthesizing them for `Bad` would unfold it. -/
theorem card_filter_le_of_imp {α : Type} [Fintype α] {p q : α → Prop} {_ : DecidablePred p}
    {_ : DecidablePred q} {c : ℕ} (hq : (Finset.univ.filter q).card ≤ c)
    (h : ∀ a, p a → q a) : (Finset.univ.filter p).card ≤ c :=
  (Finset.card_le_card (Finset.monotone_filter_right _ fun a _ ↦ h a)).trans hq

omit [Fintype M] [DecidableEq M] in
/-- `B` read through `get`, at a state. -/
theorem mem_B_iff {get : M → Selections} {B : Set (HwReg X Z M)}
    (hB : ∀ r, r ∈ B ↔ (r.1, r.2.1, get r.2.2) ∈ Bad L N) (D : DbReg X Z) (W : Hw X Z) (m : M) :
    (D, W, m) ∈ B ↔ (D, W, get m) ∈ Bad L N :=
  hB (D, W, m)

/-- **The flip cost of a codeword-selecting read on a memory holding the selections**
(`flipCost_selectReadCw_le` through `get`): for `SR` within the selection reads and an update that
keeps the memory or records a codeword selection, `E + p + 2 √(E p)` with `E = encWt`,
`p = tr (readPs SR σ)`. -/
theorem flipCost_getSelectReadCw_le (get : M → Selections) (put : M → Selections → M)
    (hget : ∀ m s, get (put m s) = s) (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)]
    (hB : ∀ r, r ∈ B ↔ (r.1, r.2.1, get r.2.2) ∈ Bad L N)
    (z : Z) (l : Layer) (e : KeyIndex) (x xi : X) (upd : M → Option X → M)
    (hupd : ∀ m v, upd m (some v) = m ∨ upd m (some v) = put m (cwSel (get m) l e x xi v))
    (SR : HwReg X Z M → Prop) [DecidablePred SR]
    (hSR : ∀ s, SR s → SelectRead L s.1 s.2.1 (get s.2.2) z l e x xi)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    flipCost B (hwReadKraus (.readH z upd)) (readPs SR) σ ≤
      ENNReal.ofReal (encWt B L l e SR σ) + ENNReal.ofReal (readPs SR * σ).trace.re +
        2 * (ENNReal.ofReal (encWt B L l e SR σ) * ENNReal.ofReal (readPs SR * σ).trace.re) ^
          (2⁻¹ : ℝ) := by
  have hout : ∀ s : HwReg X Z M, s ∉ B → (s.1, s.2.1, get s.2.2) ∉ Bad L N :=
    fun s hS h ↦ hS ((hB s).2 h)
  refine flipCost_readH_le B z upd (fun m v ↦ put m (cwSel (get m) l e x xi v)) SR
    (fun s ↦ msgCwCount L (union s.2.1 s.1) l e * 2 ^ 960) ?_ hupd ?_ ?_ ?_ ?_ hσ
  · exact fun s hs ↦ ⟨(hSR s hs).hd, (hSR s hs).hw⟩
  · intro s u hs hS h
    exact not_mem_bad_read_keep (hout s hS) (hSR s hs) u
      ((mem_B_iff hB (Function.update s.1.1 z u, s.1.2) s.2.1 s.2.2).1 h)
  · intro s hs hS
    refine card_filter_le_of_imp (card_flip_readCw_le (hout s hS) (hSR s hs)) fun v hv ↦ ?_
    obtain ⟨u, hu⟩ := hv
    have h' := (mem_B_iff hB (Function.update s.1.1 z u, s.1.2) s.2.1
      (put s.2.2 (cwSel (get s.2.2) l e x xi v))).1 hu
    rw [hget] at h'
    exact ⟨u, h'⟩
  · intro s u hs hS
    exact (mem_B_iff hB (Function.update s.1.1 z u, s.1.2) s.2.1 s.2.2).2
      (mem_hwTargetBad_fill ((hB s).1 hS) (hSR s hs).hd u (get s.2.2) fun _ _ ht ↦ ht)
  · intro s u v hs hS
    refine (mem_B_iff hB (Function.update s.1.1 z u, s.1.2) s.2.1
      (put s.2.2 (cwSel (get s.2.2) l e x xi v))).2 ?_
    rw [hget]
    unfold cwSel
    split_ifs
    · exact mem_hwTargetBad_fill ((hB s).1 hS) (hSR s hs).hd u _
        fun _ _ ht ↦ xmssTgt_select_mono (hSR s hs).hm ht
    · exact mem_hwTargetBad_fill ((hB s).1 hS) (hSR s hs).hd u _ fun _ _ ht ↦ ht

omit [DecidableEq M] in
/-- **The Enc term** (`selectReadCwE_le` on any memory): if `msgCwCount ≤ C` on the states of `SR`
outside `B` in the support, then `E ≤ C 2^-128 e`. -/
theorem encWt_le (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)] (L : HonestTable) (l : Layer)
    (e : KeyIndex) (SR : HwReg X Z M → Prop) [DecidablePred SR] (C : ℕ)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hC : ∀ q, SR q.2 → q.2 ∉ B → σ q q ≠ 0 → msgCwCount L (union q.2.2.1 q.2.1) l e ≤ C) :
    encWt B L l e SR σ ≤ C * (2 ^ 128)⁻¹ * selWt SR σ := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hC0 : (0 : ℝ) ≤ C * (2 ^ 128)⁻¹ := by positivity
  rw [encWt, selWt, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  by_cases hq : SR q.2
  · rw [ite_eq_left hq]
    by_cases hb : q.2 ∉ B
    · rw [ite_eq_left ⟨hq, hb⟩]
      by_cases hσq : σ q q = 0
      · rw [hσq, Complex.zero_re, mul_zero, mul_zero]
      refine mul_le_mul_of_nonneg_right ?_ (hre q)
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc, two_pow_div_card_X]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (hC q hq hb hσq)) (by positivity)
    · rw [ite_eq_right fun h ↦ hb h.2]
      exact mul_nonneg hC0 (hre q)
  · rw [ite_eq_right fun h ↦ hq h.1, ite_eq_right hq, mul_zero]

/-- **Survival of a trial read on any memory** (`survive_selectRead_le` through `get`): the update
selects a codeword digest of the unselected key. -/
theorem survive_getSelectRead_le (get : M → Selections) (z : Z) (l : Layer) (e : KeyIndex)
    (x xi : X) (upd : M → Option X → M)
    (hupd : ∀ m v, get m l e = none → get (upd m (some v)) = cwSel (get m) l e x xi v)
    (SR : HwReg X Z M → Prop) [DecidablePred SR]
    (hSR : ∀ s, SR s → SelectRead L s.1 s.2.1 (get s.2.2) z l e x xi)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    survWt get l e z upd σ ≤ unselWt get l e σ - rhoCw * selWt SR σ + (readPs SR * σ).trace.re +
      2 * √(rhoCw * selWt SR σ * (readPs SR * σ).trace.re) :=
  survive_readH_le z upd (unselL get l e) (fun v ↦ Codeword.Valid (trunc128 (xi + v)))
    (card_codeword_div_card_X xi)
    (fun m hm v ↦ by
      show get (upd m (some v)) l e = none ↔ _
      rw [hupd m v hm]
      exact cwSel_eq_none_iff hm x xi v)
    SR (fun s hs ↦ ⟨(hSR s hs).hd, (hSR s hs).hw, (hSR s hs).hm⟩) hσ

/-! ## The trials of one key -/

section trials

variable {β : Type} (Bj : ℕ → Finset β)
  (σ : ℕ → β → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ)
  (SR : ℕ → β → HwReg X Z M → Prop) [∀ j b, DecidablePred (SR j b)]

/-- `w`: the weight reaching trial `j` with key `(l, e)` unselected, over the trial's branches. -/
noncomputable def trialW (get : M → Selections) (l : Layer) (e : KeyIndex) (j : ℕ) : ℝ :=
  ∑ b ∈ Bj j, unselWt get l e (σ j b)

/-- `e`: the weight of the selection reads of trial `j`. -/
noncomputable def trialSel (j : ℕ) : ℝ := ∑ b ∈ Bj j, selWt (SR j b) (σ j b)

/-- `p`: the weight off the selection reads of trial `j`, `∑ tr (readPs SR σ)`. -/
noncomputable def trialRest (j : ℕ) : ℝ := ∑ b ∈ Bj j, (readPs (SR j b) * σ j b).trace.re

/-- `E`: the Enc term of trial `j`. -/
noncomputable def trialEnc (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)] (L : HonestTable)
    (l : Layer) (e : KeyIndex) (j : ℕ) : ℝ :=
  ∑ b ∈ Bj j, encWt B L l e (SR j b) (σ j b)

omit [Fintype M] [DecidableEq M] in
/-- `E + p + 2 √(E p)` as one `ofReal`. -/
theorem ofReal_cost_eq {E p : ℝ} (hE : 0 ≤ E) (hp : 0 ≤ p) :
    ENNReal.ofReal E + ENNReal.ofReal p + 2 * (ENNReal.ofReal E * ENNReal.ofReal p) ^ (2⁻¹ : ℝ) =
      ENNReal.ofReal (E + p + 2 * (√E * √p)) := by
  rw [← ENNReal.ofReal_mul hE, ENNReal.ofReal_rpow_inv_two, Real.sqrt_mul hE,
    ENNReal.ofReal_add (add_nonneg hE hp) (by positivity), ENNReal.ofReal_add hE hp,
    ENNReal.ofReal_mul (by norm_num)]
  norm_num

omit [Fintype M] [DecidableEq M] in
/-- **Branch costs add up to the cost of the sums** (Cauchy-Schwarz on `√(E p)`). -/
theorem sum_cost_le_cost {γ : Type} (s : Finset γ) (E p : γ → ℝ) (hE : ∀ b, 0 ≤ E b)
    (hp : ∀ b, 0 ≤ p b) :
    ∑ b ∈ s, (ENNReal.ofReal (E b) + ENNReal.ofReal (p b) +
      2 * (ENNReal.ofReal (E b) * ENNReal.ofReal (p b)) ^ (2⁻¹ : ℝ)) ≤
    ENNReal.ofReal (∑ b ∈ s, E b) + ENNReal.ofReal (∑ b ∈ s, p b) +
      2 * (ENNReal.ofReal (∑ b ∈ s, E b) * ENNReal.ofReal (∑ b ∈ s, p b)) ^ (2⁻¹ : ℝ) := by
  have hE' := Finset.sum_nonneg fun b (_ : b ∈ s) ↦ hE b
  have hp' := Finset.sum_nonneg fun b (_ : b ∈ s) ↦ hp b
  simp only [ofReal_cost_eq (hE _) (hp _)]
  rw [ofReal_cost_eq hE' hp', ← ENNReal.ofReal_sum_of_nonneg fun b _ ↦ by
    have := hE b; have := hp b; positivity]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have := Real.sum_sqrt_mul_sqrt_le s hE hp
  linarith

/-- **`keyFacts` from the trials of a key.** Trial `j` of key `(l, e)` runs, on each branch
`b ∈ Bj j` (state `σ j b`), the selecting read `.readH (z j b) (upd j b)` whose update selects a
codeword digest of the unselected key, with selection reads `SR j b`. If the weight reaching trial
`j + 1` unselected is at most the surviving outcomes of trial `j` (the reads between keep the
memory) and `msgCwCount ≤ C` on the selection reads outside `B` of the support, then the per-trial
data `trialW`, `trialSel`, `trialRest`, `trialEnc` satisfy Security's `keyFacts`. -/
theorem keyFacts_of_trials (get : M → Selections) (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)]
    (L : HonestTable) (l : Layer) (e : KeyIndex) (J C : ℕ) (hσ : ∀ j b, (σ j b).PosSemidef)
    (z : ℕ → β → Z) (x xi : ℕ → β → X) (upd : ℕ → β → M → Option X → M)
    (hupd : ∀ j b m v, get m l e = none →
      get (upd j b m (some v)) = cwSel (get m) l e (x j b) (xi j b) v)
    (hSR : ∀ j b s, SR j b s → SelectRead L s.1 s.2.1 (get s.2.2) (z j b) l e (x j b) (xi j b))
    (hnext : ∀ j < J, trialW Bj σ get l e (j + 1) ≤
      ∑ b ∈ Bj j, survWt get l e (z j b) (upd j b) (σ j b))
    (hC : ∀ j < J, ∀ b ∈ Bj j, ∀ q, SR j b q.2 → q.2 ∉ B → σ j b q q ≠ 0 →
      msgCwCount L (union q.2.2.1 q.2.1) l e ≤ C) :
    0 ≤ (C : ℝ) ∧ (∀ j, 0 ≤ trialW Bj σ get l e j) ∧ (∀ j, 0 ≤ trialSel Bj σ SR j) ∧
      (∀ j, 0 ≤ trialRest Bj σ SR j) ∧ (∀ j, 0 ≤ trialEnc Bj σ SR B L l e j) ∧
      (∀ j < J, trialW Bj σ get l e (j + 1) ≤ trialW Bj σ get l e j -
        rhoCw * trialSel Bj σ SR j + trialRest Bj σ SR j +
          2 * √(rhoCw * trialSel Bj σ SR j * trialRest Bj σ SR j)) ∧
      (∀ j < J, trialEnc Bj σ SR B L l e j ≤ C * (2 ^ 128)⁻¹ * trialSel Bj σ SR j) := by
  refine ⟨Nat.cast_nonneg _, fun j ↦ Finset.sum_nonneg fun b _ ↦ unselWt_nonneg (hσ j b) get l e,
    fun j ↦ Finset.sum_nonneg fun b _ ↦ selWt_nonneg (hσ j b) _,
    fun j ↦ Finset.sum_nonneg fun b _ ↦ re_trace_readPs_nonneg (SR j b) (hσ j b),
    fun j ↦ Finset.sum_nonneg fun b _ ↦ encWt_nonneg (hσ j b) B L l e _, fun j hj ↦ ?_,
    fun j hj ↦ ?_⟩
  · have hρe : ∀ b, 0 ≤ rhoCw * selWt (SR j b) (σ j b) := fun b ↦
      mul_nonneg rhoCw_pos.le (selWt_nonneg (hσ j b) _)
    have hp : ∀ b, 0 ≤ (readPs (SR j b) * σ j b).trace.re := fun b ↦
      re_trace_readPs_nonneg (SR j b) (hσ j b)
    have hsum : ∑ b ∈ Bj j, survWt get l e (z j b) (upd j b) (σ j b) ≤
        ∑ b ∈ Bj j, (unselWt get l e (σ j b) - rhoCw * selWt (SR j b) (σ j b) +
          (readPs (SR j b) * σ j b).trace.re +
          2 * (√(rhoCw * selWt (SR j b) (σ j b)) * √((readPs (SR j b) * σ j b).trace.re))) :=
      Finset.sum_le_sum fun b _ ↦ by
        rw [← Real.sqrt_mul (hρe b)]
        exact survive_getSelectRead_le get (z j b) l e (x j b) (xi j b) (upd j b) (hupd j b)
          (SR j b) (hSR j b) (hσ j b)
    have hcs := Real.sum_sqrt_mul_sqrt_le (Bj j) hρe hp
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    rw [← Finset.mul_sum] at hcs
    have hsq : √(rhoCw * trialSel Bj σ SR j * trialRest Bj σ SR j) =
        √(rhoCw * ∑ b ∈ Bj j, selWt (SR j b) (σ j b)) *
          √(∑ b ∈ Bj j, (readPs (SR j b) * σ j b).trace.re) :=
      Real.sqrt_mul (mul_nonneg rhoCw_pos.le (Finset.sum_nonneg fun b _ ↦
        selWt_nonneg (hσ j b) _)) _
    rw [hsq]
    have hn := hnext j hj
    unfold trialW trialSel trialRest at *
    linarith
  · unfold trialEnc trialSel
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun b hb ↦
      encWt_le B L l e (SR j b) C (hσ j b) (hC j hj b hb)

/-- **The selecting reads of one key cost at most `keyCost`** (`clsSplit` per key): the flip costs
of trial `j`'s branches add up to `E + p + 2 √(E p)` with `E = trialEnc`, `p = trialRest`. -/
theorem sum_flipCost_trials_le (get : M → Selections) (put : M → Selections → M)
    (hget : ∀ m s, get (put m s) = s) (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)]
    (hB : ∀ r, r ∈ B ↔ (r.1, r.2.1, get r.2.2) ∈ Bad L N)
    (l : Layer) (e : KeyIndex) (J : ℕ) (hσ : ∀ j b, (σ j b).PosSemidef)
    (z : ℕ → β → Z) (x xi : ℕ → β → X) (upd : ℕ → β → M → Option X → M)
    (hupd : ∀ j b m v, upd j b m (some v) = m ∨
      upd j b m (some v) = put m (cwSel (get m) l e (x j b) (xi j b) v))
    (hSR : ∀ j b s, SR j b s → SelectRead L s.1 s.2.1 (get s.2.2) (z j b) l e (x j b) (xi j b)) :
    ∑ j ∈ Finset.range J, ∑ b ∈ Bj j,
        flipCost B (hwReadKraus (.readH (z j b) (upd j b))) (readPs (SR j b)) (σ j b) ≤
      ∑ j ∈ Finset.range J, (ENNReal.ofReal (trialEnc Bj σ SR B L l e j) +
        ENNReal.ofReal (trialRest Bj σ SR j) + 2 * (ENNReal.ofReal (trialEnc Bj σ SR B L l e j) *
          ENNReal.ofReal (trialRest Bj σ SR j)) ^ (2⁻¹ : ℝ)) :=
  Finset.sum_le_sum fun j _ ↦ (Finset.sum_le_sum fun b _ ↦
    flipCost_getSelectReadCw_le get put hget B hB (z j b) l e (x j b) (xi j b) (upd j b)
      (hupd j b) (SR j b) (hSR j b) (hσ j b)).trans
    (sum_cost_le_cost (Bj j) (fun b ↦ encWt B L l e (SR j b) (σ j b))
      (fun b ↦ (readPs (SR j b) * σ j b).trace.re) (fun b ↦ encWt_nonneg (hσ j b) B L l e _)
      fun b ↦ re_trace_readPs_nonneg (SR j b) (hσ j b))

end trials

end lift

/-! ## The total over the keys and the tables -/

section total

/-- The rate of one key's Enc term, `C 2^-128 / ρ_c ≤ Cm 2^-107`. -/
theorem rate_le {C Cm : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ Cm) :
    C * (2 ^ 128)⁻¹ / rhoCw ≤ Cm * (2 ^ 107)⁻¹ := by
  rw [div_eq_mul_inv, mul_assoc]
  refine mul_le_mul hC ?_ (mul_nonneg (by positivity) (inv_nonneg.2 rhoCw_pos.le)) (hC0.trans hC)
  calc (2 ^ 128 : ℝ)⁻¹ * rhoCw⁻¹ ≤ (2 ^ 128)⁻¹ * 2 ^ 21 :=
        mul_le_mul_of_nonneg_left inv_rhoCw_le (by positivity)
    _ = (2 ^ 107)⁻¹ := by norm_num

/-- **One key's bound, linearly**: `keyBound J C w p ≤ 4 a + (12 a + 2) P` for
`C 2^-128 / ρ_c ≤ a`, `w 0 ≤ 1` and `P = ∑ p`. -/
theorem keyBound_le_lin {J : ℕ} {C a : ℝ} (w p : ℕ → ℝ) (hC0 : 0 ≤ C)
    (ha : C * (2 ^ 128)⁻¹ / rhoCw ≤ a) (hw0 : 0 ≤ w 0) (hw1 : w 0 ≤ 1) (hp : ∀ j, 0 ≤ p j) :
    ENNReal.ofReal ((√(C * (2 ^ 128)⁻¹ / rhoCw *
        (√(w 0 + 2 * ∑ j ∈ Finset.range J, p j) + √(∑ j ∈ Finset.range J, p j)) ^ 2) +
      √(∑ j ∈ Finset.range J, p j)) ^ 2) ≤
    ENNReal.ofReal (4 * a + (12 * a + 2) * ∑ j ∈ Finset.range J, p j) := by
  refine ENNReal.ofReal_le_ofReal ?_
  obtain ⟨P, hPdef⟩ : ∃ P, P = ∑ j ∈ Finset.range J, p j := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = C * (2 ^ 128)⁻¹ / rhoCw := ⟨_, rfl⟩
  rw [← hPdef, ← hcdef]
  rw [← hcdef] at ha
  have hP : 0 ≤ P := hPdef ▸ Finset.sum_nonneg fun j _ ↦ hp j
  have hc : 0 ≤ c := hcdef ▸ div_nonneg (by positivity) rhoCw_pos.le
  have hs := Real.sq_sqrt (show 0 ≤ w 0 + 2 * P by positivity)
  have ht := Real.sq_sqrt hP
  have hX : (√(w 0 + 2 * P) + √P) ^ 2 ≤ 2 * w 0 + 6 * P := by
    nlinarith [sq_nonneg (√(w 0 + 2 * P) - √P)]
  have hu := Real.sq_sqrt (show 0 ≤ c * (√(w 0 + 2 * P) + √P) ^ 2 by positivity)
  have h1 : (√(c * (√(w 0 + 2 * P) + √P) ^ 2) + √P) ^ 2 ≤
      2 * (c * (√(w 0 + 2 * P) + √P) ^ 2) + 2 * P := by
    nlinarith [sq_nonneg (√(c * (√(w 0 + 2 * P) + √P) ^ 2) - √P)]
  have h2 : c * (√(w 0 + 2 * P) + √P) ^ 2 ≤ c * (2 + 6 * P) :=
    mul_le_mul_of_nonneg_left (by linarith) hc
  nlinarith

/-- **The keys' bounds, summed**: with `C k ≤ Cm` on the keys `Ks` with trials and `C k = 0` off
them, `∑ₖ keyBound ≤ 4 |Ks| Cm 2^-107 + (12 Cm 2^-107 + 2) ∑ₖ Pₖ`. -/
theorem sum_keyBound_le {K : Type} [Fintype K] (Ks : Finset K) (J : K → ℕ) (C : K → ℝ)
    (w p : K → ℕ → ℝ) {Cm : ℝ} (hCm : 0 ≤ Cm) (hC0 : ∀ k, 0 ≤ C k) (hC : ∀ k ∈ Ks, C k ≤ Cm)
    (hCK : ∀ k ∉ Ks, C k = 0) (hw0 : ∀ k, 0 ≤ w k 0) (hw1 : ∀ k, w k 0 ≤ 1)
    (hp : ∀ k j, 0 ≤ p k j) :
    ∑ k, ENNReal.ofReal ((√(C k * (2 ^ 128)⁻¹ / rhoCw *
        (√(w k 0 + 2 * ∑ j ∈ Finset.range (J k), p k j) +
          √(∑ j ∈ Finset.range (J k), p k j)) ^ 2) +
      √(∑ j ∈ Finset.range (J k), p k j)) ^ 2) ≤
    ENNReal.ofReal (4 * Ks.card * (Cm * (2 ^ 107)⁻¹) +
      (12 * (Cm * (2 ^ 107)⁻¹) + 2) * ∑ k, ∑ j ∈ Finset.range (J k), p k j) := by
  classical
  have ham : 0 ≤ Cm * (2 ^ 107 : ℝ)⁻¹ := by positivity
  have hPk : ∀ k, 0 ≤ ∑ j ∈ Finset.range (J k), p k j := fun k ↦
    Finset.sum_nonneg fun j _ ↦ hp k j
  have hk : ∀ k, ENNReal.ofReal ((√(C k * (2 ^ 128)⁻¹ / rhoCw *
        (√(w k 0 + 2 * ∑ j ∈ Finset.range (J k), p k j) +
          √(∑ j ∈ Finset.range (J k), p k j)) ^ 2) +
      √(∑ j ∈ Finset.range (J k), p k j)) ^ 2) ≤
      ENNReal.ofReal ((if k ∈ Ks then 4 * (Cm * (2 ^ 107)⁻¹) else 0) +
        (12 * (Cm * (2 ^ 107)⁻¹) + 2) * ∑ j ∈ Finset.range (J k), p k j) := fun k ↦ by
    by_cases hks : k ∈ Ks
    · simp only [hks, ↓reduceIte]
      exact keyBound_le_lin (w k) (p k) (hC0 k) (rate_le (hC0 k) (hC k hks)) (hw0 k) (hw1 k)
        (hp k)
    · simp only [hks, ↓reduceIte]
      refine (keyBound_le_lin (a := 0) (w k) (p k) (hC0 k)
        (by rw [hCK k hks, zero_mul, zero_div]) (hw0 k) (hw1 k) (hp k)).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have := hPk k
      nlinarith
  refine (Finset.sum_le_sum fun k _ ↦ hk k).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ ↦ by
    have := hPk k
    split_ifs <;> positivity]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul]
  ring

/-- An average of a function at most `c` on `good` and `0` elsewhere is at most `c`. -/
theorem uavg_ite_le {Θ : Type} [Fintype Θ] (good : Θ → Prop) [DecidablePred good]
    (F : Θ → ℝ≥0∞) {c : ℝ≥0∞} (h : ∀ θ, good θ → F θ ≤ c) :
    uavg (fun θ ↦ if good θ then F θ else 0) ≤ c := by
  unfold uavg
  have hs : ∑ θ, (if good θ then F θ else 0) ≤ Fintype.card Θ * c := by
    calc ∑ θ, (if good θ then F θ else 0) ≤ ∑ _θ : Θ, c :=
          Finset.sum_le_sum fun θ _ ↦ by
            split_ifs with hθ
            · exact h θ hθ
            · exact zero_le
      _ = Fintype.card Θ * c := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  by_cases h0 : (Fintype.card Θ : ℝ≥0∞) = 0
  · rw [h0, zero_mul, nonpos_iff_eq_zero] at hs
    rw [hs, mul_zero]
    exact zero_le
  · calc (Fintype.card Θ : ℝ≥0∞)⁻¹ * ∑ θ, (if good θ then F θ else 0)
        ≤ (Fintype.card Θ : ℝ≥0∞)⁻¹ * (Fintype.card Θ * c) := by gcongr
      _ = c := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top _), one_mul]

/-- **`clsTotal` from caps**: on the good tables let `C ≤ Cm` on at most `nK` keys with trials and
`C = 0` off them, `w 0 ≤ 1`, `∑ₖ Pₖ ≤ Pm` and `rest ≤ R`. Then the average over the good tables of
the keys' bounds and the rest is at most `4 nK Cm 2^-107 + (12 Cm 2^-107 + 2) Pm + R`. -/
theorem clsTotal_of {Θ K : Type} [Fintype Θ] [Fintype K] (good : Θ → Prop) [DecidablePred good]
    (J : Θ → K → ℕ) (C : Θ → K → ℝ) (w p : Θ → K → ℕ → ℝ) (rest : Θ → ℝ≥0∞)
    (Ks : Θ → Finset K) (nK : ℕ) {Cm Pm : ℝ} (R : ℝ≥0∞) (hCm : 0 ≤ Cm)
    (hC0 : ∀ θ, good θ → ∀ k, 0 ≤ C θ k) (hC : ∀ θ, good θ → ∀ k ∈ Ks θ, C θ k ≤ Cm)
    (hCK : ∀ θ, good θ → ∀ k ∉ Ks θ, C θ k = 0) (hK : ∀ θ, good θ → (Ks θ).card ≤ nK)
    (hw0 : ∀ θ, good θ → ∀ k, 0 ≤ w θ k 0) (hw1 : ∀ θ, good θ → ∀ k, w θ k 0 ≤ 1)
    (hp : ∀ θ, good θ → ∀ k j, 0 ≤ p θ k j)
    (hP : ∀ θ, good θ → ∑ k, ∑ j ∈ Finset.range (J θ k), p θ k j ≤ Pm)
    (hR : ∀ θ, good θ → rest θ ≤ R) :
    uavg (fun θ ↦ if good θ then
      ∑ k, ENNReal.ofReal ((√(C θ k * (2 ^ 128)⁻¹ / rhoCw *
        (√(w θ k 0 + 2 * ∑ j ∈ Finset.range (J θ k), p θ k j) +
          √(∑ j ∈ Finset.range (J θ k), p θ k j)) ^ 2) +
        √(∑ j ∈ Finset.range (J θ k), p θ k j)) ^ 2) + rest θ else 0) ≤
    ENNReal.ofReal (4 * nK * (Cm * (2 ^ 107)⁻¹) + (12 * (Cm * (2 ^ 107)⁻¹) + 2) * Pm) + R := by
  refine uavg_ite_le good _ fun θ hθ ↦ add_le_add ?_ (hR θ hθ)
  refine (sum_keyBound_le (Ks θ) (J θ) (C θ) (w θ) (p θ) hCm (hC0 θ hθ) (hC θ hθ) (hCK θ hθ)
    (hw0 θ hθ) (hw1 θ hθ) (hp θ hθ)).trans (ENNReal.ofReal_le_ofReal ?_)
  have ham : 0 ≤ Cm * (2 ^ 107 : ℝ)⁻¹ := by positivity
  have hn : ((Ks θ).card : ℝ) ≤ nK := Nat.cast_le.2 (hK θ hθ)
  have := hP θ hθ
  gcongr

end total

end Quantum.Xmss.Assembly

end
