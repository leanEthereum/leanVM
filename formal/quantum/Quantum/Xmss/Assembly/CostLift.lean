module

public import Quantum.Xmss.EncCost
public import Quantum.Xmss.Assembly.Costs
public import Quantum.Xmss.Assembly.RecordPorts

@[expose] public section

/-!
# The classical costs of the event bound, on a memory holding the selections

The flip costs of Security's event bound, for any memory `M` that holds Events' selections through
`get : M → Selections` and `put : M → Selections → M` with `get (put m s) = s`. Security's memory
`Finset S × Selections` is the case `get = Prod.snd`, `put m s = (m.1, s)`: Template's
`liftRead (.readH z upd)` is `.readH z fun m o ↦ (m.1, upd m.2 o)`, which keeps the label
(`liftUpd_cases`, `get_liftUpd`). The bad set is any `B` that is Events' `Bad L N` read through
`get` (Security's `BadR`, by `Iff.rfl`). Generic instances keep the kernel away from the concrete
`Fintype`/`DecidableEq` terms of the labelled memory.

* **Per port** (`flipCost_le_ports`): a read port is a selecting read of a trial
  (`IsTrial`: an `h`-read with the trial's update, the trial chosen by `trialOf`) or not. Its
  projector `PRof` is `readPs` of the trial's selection reads, and on the other read ports of the
  states whose read cell is empty (`cellEmpty`). For every `s > 0` its flip cost is at most
  `(1 + s) (E + ε + ε') + (1 + 1/s) p`: `E = encW`, the codeword flips of a selecting read
  (`flipCost_getSelectReadCw_le`), `ε + ε' = epsW`, the flip terms of the other reads, and
  `p = massW`, the weight off the selection reads (the read cell recorded or hardwired). The Enc
  term is state-weighted, `E ≤ 2^-128 n` with `n = cntW = tr(σ · msgCwCount · 1_SR)`
  (`encW_le_cntW`, the projector form of `selectReadCwE_le`), with no bound on `msgCwCount` over
  the support.
* **Reads of `k`, `k'` cells** (`cellRead_readK`, `cellRead_readK'`, `flipCost_readK_le`,
  `flipCost_readK'_le`, `card_flip_readK_bad_le`, `card_flip_readK'_bad_le`): a read that keeps the
  memory is a cell read; off its empty cell its `ε, ε'` are at most the contents of the cell that
  flip the event over `|Z|` (`chw_le_card_of_keep`), the capacity-scale counts of
  `card_targetBad_updateK_le`, `card_targetBad_updateK'_le`.
* **Along a run** (`totalWeight_le_lin`, `le_sq_add_of_forall_lin`, `extWeight_hwCost_le_lin`): the
  weights add up along the run of any program, and the total flip cost is at most
  `(√Σ(E + ε + ε') + √Σp)² + Σprog`, the sums along the run. No program structure is used: the
  trials of all keys are summed jointly. The joint count `Σn` is the cross-key potential
  `∑_{k unselected} msgCwCount(·, k)` (at most the message-slot cells, `sum_msgCwCount_le`) summed
  along the run; the survival of a trial read (`survive_getSelectRead_le`) is its per-trial step.
-/

universe u v w u₁ v₁

open Matrix
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Xmss.Assembly

open Quantum Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss

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
/-- The state-weighted count of a selecting read of key `(l, e)`: `tr(σ · msgCwCount · 1_SR)`. -/
noncomputable def nSelWt (L : HonestTable) (l : Layer) (e : KeyIndex) (SR : HwReg X Z M → Prop)
    [DecidablePred SR] (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ :=
  ∑ q, if SR q.2 then (msgCwCount L (union q.2.2.1 q.2.1) l e : ℝ) * (σ q q).re else 0


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

omit [DecidableEq M] in
theorem nSelWt_nonneg (L : HonestTable) (l : Layer) (e : KeyIndex) (SR : HwReg X Z M → Prop)
    [DecidablePred SR] : 0 ≤ nSelWt L l e SR σ :=
  Finset.sum_nonneg fun q _ ↦ by
    have : 0 ≤ (σ q q).re := (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) this
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
/-- **The Enc term, state-weighted** (the projector form of `selectReadCwE_le`):
`E ≤ 2^-128 tr(σ · msgCwCount · 1_SR)`. -/
theorem encWt_le_nSelWt (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)] (L : HonestTable)
    (l : Layer) (e : KeyIndex) (SR : HwReg X Z M → Prop) [DecidablePred SR]
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    encWt B L l e SR σ ≤ (2 ^ 128)⁻¹ * nSelWt L l e SR σ := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  rw [encWt, nSelWt, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  by_cases hq : SR q.2
  · rw [ite_eq_left hq]
    by_cases hb : q.2 ∉ B
    · rw [ite_eq_left ⟨hq, hb⟩, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc,
        two_pow_div_card_X]
      exact le_of_eq (by ring)
    · rw [ite_eq_right fun h ↦ hb h.2]
      exact mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) (hre q))
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

/-! ## Per-port costs -/

section ports

/-- A randomizer trial of key `(l, e)`: the key, the block `x` and the rate `xi` after `π`. -/
structure TrialPt where
  /-- The layer. -/
  l : Layer
  /-- The key. -/
  e : KeyIndex
  /-- The block. -/
  x : X
  /-- The rate after `π`. -/
  xi : X

variable (get : M → Selections) (updOf : TrialPt → M → Option X → M)

omit [Fintype M] [DecidableEq M] in
/-- The read port `c` is the selecting read of a trial: an `h`-read with the trial's update. -/
def IsTrial (c : HwRead X Z M) : Prop := ∃ zt : Z × TrialPt, c = .readH zt.1 (updOf zt.2)

omit [Fintype M] [DecidableEq M] in
open scoped Classical in
/-- The cell and the trial of a selecting read port (a chosen one). -/
noncomputable def trialOf (c : HwRead X Z M) : Z × TrialPt :=
  if h : IsTrial updOf c then Classical.choose h else
    (0, ⟨bottomLayer, ⟨0, by unfold lifetime; positivity⟩, 0, 0⟩)

omit [Fintype M] [DecidableEq M] in
/-- The cell a read port reads is neither recorded nor hardwired. -/
def cellEmpty : HwRead X Z M → HwReg X Z M → Prop
  | .readH z _, s => s.1.1 z = none ∧ s.2.1.1 z = none
  | .readK x _, s => s.1.2.1 x = none ∧ s.2.1.2.1 x = none
  | .readK' x _, s => s.1.2.2 x = none ∧ s.2.1.2.2 x = none

omit [Fintype M] [DecidableEq M] in
/-- The selection reads of a port: `SelectRead` of its trial on a selecting read port; on the other
read ports, the states whose read cell is empty (neither recorded nor hardwired). -/
def trialSR (L : HonestTable) (c : HwRead X Z M) (s : HwReg X Z M) : Prop :=
  (IsTrial updOf c ∧ SelectRead L s.1 s.2.1 (get s.2.2) (trialOf updOf c).1 (trialOf updOf c).2.l
    (trialOf updOf c).2.e (trialOf updOf c).2.x (trialOf updOf c).2.xi) ∨
  (¬IsTrial updOf c ∧ cellEmpty c s)

omit [Fintype M] [DecidableEq M] in
theorem trialSR_of_isTrial {L : HonestTable} {c : HwRead X Z M} (ht : IsTrial updOf c)
    {s : HwReg X Z M} (hs : trialSR get updOf L c s) :
    SelectRead L s.1 s.2.1 (get s.2.2) (trialOf updOf c).1 (trialOf updOf c).2.l
      (trialOf updOf c).2.e (trialOf updOf c).2.x (trialOf updOf c).2.xi := by
  rcases hs with ⟨-, h⟩ | ⟨hn, -⟩
  · exact h
  · exact absurd ht hn

omit [Fintype M] [DecidableEq M] in
theorem eq_readH_trialOf {c : HwRead X Z M} (ht : IsTrial updOf c) :
    c = .readH (trialOf updOf c).1 (updOf (trialOf updOf c).2) := by
  have h := Classical.choose_spec ht
  simp only [trialOf, ht, ↓reduceDIte]
  exact h

/-- Decidability of the selection reads, classically. -/
noncomputable instance trialSRDec (L : HonestTable) (c : HwRead X Z M) :
    DecidablePred (trialSR get updOf L c) :=
  Classical.decPred _

/-- **The read projectors of the flip costs**: off the selection reads of the port. -/
noncomputable def PRof (L : HonestTable) (c : HwRead X Z M) :
    Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ :=
  readPs (trialSR get updOf L c)

theorem PRof_proj (L : HonestTable) (c : HwRead X Z M) :
    (PRof get updOf L c)ᴴ = PRof get updOf L c ∧
      PRof get updOf L c * PRof get updOf L c = PRof get updOf L c :=
  readPs_proj _

/-- The flip operator of a read port for the event `B`: `∑ᵣ K rᴴ Q K r - Q`. -/
noncomputable def flipF (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)] (c : HwRead X Z M) :
    Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ :=
  ∑ r, (hwReadKraus c r)ᴴ * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector B) * hwReadKraus c r -
    (1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector B

open scoped Classical in
/-- The Enc weight of a port: `encWt` on a selecting read port, `0` elsewhere. -/
noncomputable def encW (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)] (L : HonestTable)
    (c : HwRead X Z M) (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  if IsTrial updOf c then
    ENNReal.ofReal (encWt B L (trialOf updOf c).2.l (trialOf updOf c).2.e (trialSR get updOf L c) σ)
  else 0

open scoped Classical in
/-- The flip terms `ε + ε'` of a read port other than a selecting read (projector `PRof`, off its
empty cell), `0` on the selecting read ports. -/
noncomputable def epsW (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)] (L : HonestTable)
    (c : HwRead X Z M) (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  if IsTrial updOf c then 0 else
    ENNReal.ofReal ((1 - PRof get updOf L c) * flipF B c * (1 - PRof get updOf L c) * σ).trace.re +
      ENNReal.ofReal ((1 - PRof get updOf L c) * flipF B c * PRof get updOf L c * flipF B c *
        (1 - PRof get updOf L c) * σ).trace.re

/-- The recorded mass of a read port: `tr (PRof σ)`, the weight off its selection reads (the
read cell recorded or hardwired, on every read port). -/
noncomputable def massW (L : HonestTable) (c : HwRead X Z M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (PRof get updOf L c * σ).trace.re

open scoped Classical in
/-- The weighted count of a port: `nSelWt` on a selecting read port, `0` elsewhere. -/
noncomputable def cntW (L : HonestTable) (c : HwRead X Z M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  if IsTrial updOf c then
    ENNReal.ofReal (nSelWt L (trialOf updOf c).2.l (trialOf updOf c).2.e (trialSR get updOf L c) σ)
  else 0

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
/-- **The cross term, linearized**: `E + p + 2 √(E p) ≤ (1 + s) E + (1 + 1/s) p`. -/
theorem cost_le_lin {E p s : ℝ} (hs : 0 < s) (hE : 0 ≤ E) (hp : 0 ≤ p) :
    ENNReal.ofReal E + ENNReal.ofReal p + 2 * (ENNReal.ofReal E * ENNReal.ofReal p) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (1 + s) * ENNReal.ofReal E + ENNReal.ofReal (1 + s⁻¹) * ENNReal.ofReal p := by
  rw [ofReal_cost_eq hE hp, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hu := Real.sq_sqrt hE
  have hv := Real.sq_sqrt hp
  have hexp : s⁻¹ * (s * √E - √p) ^ 2 = s * E + s⁻¹ * p - 2 * (√E * √p) := by
    have h1 : s⁻¹ * (s * √E - √p) ^ 2 =
        (s⁻¹ * s) * s * √E ^ 2 - 2 * (s⁻¹ * s) * (√E * √p) + s⁻¹ * √p ^ 2 := by ring
    rw [h1, inv_mul_cancel₀ hs.ne', hu, hv]
    ring
  have h0 : 0 ≤ s⁻¹ * (s * √E - √p) ^ 2 := mul_nonneg (inv_nonneg.2 hs.le) (sq_nonneg _)
  nlinarith

omit [Fintype M] [DecidableEq M] in
theorem exists_ofReal_eq_nonneg (a : ℝ) : ∃ A : ℝ, 0 ≤ A ∧ ENNReal.ofReal a = ENNReal.ofReal A := by
  rcases le_total a 0 with h | h
  · exact ⟨0, le_rfl, by rw [ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]⟩
  · exact ⟨a, h, rfl⟩

omit [Fintype M] [DecidableEq M] in
/-- **A flip cost with separate cross term, linearized**:
`ε + p + 2 √(ε' p) ≤ (1 + s) (ε + ε') + (1 + 1/s) p`. -/
theorem cost_le_lin' {a a' p s : ℝ} (hs : 0 < s) (hp : 0 ≤ p) :
    ENNReal.ofReal a + ENNReal.ofReal p + 2 * (ENNReal.ofReal a' * ENNReal.ofReal p) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal (1 + s) * (ENNReal.ofReal a + ENNReal.ofReal a') +
        ENNReal.ofReal (1 + s⁻¹) * ENNReal.ofReal p := by
  obtain ⟨A, hA, ha⟩ := exists_ofReal_eq_nonneg a
  obtain ⟨A', hA', ha'⟩ := exists_ofReal_eq_nonneg a'
  rw [ha, ha']
  have hL : ENNReal.ofReal A + ENNReal.ofReal p +
      2 * (ENNReal.ofReal A' * ENNReal.ofReal p) ^ (2⁻¹ : ℝ) =
      ENNReal.ofReal (A + p + 2 * (√A' * √p)) := by
    rw [← ENNReal.ofReal_mul hA', ENNReal.ofReal_rpow_inv_two, Real.sqrt_mul hA',
      ENNReal.ofReal_add (add_nonneg hA hp) (by positivity), ENNReal.ofReal_add hA hp,
      ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hR : ENNReal.ofReal (1 + s) * (ENNReal.ofReal A + ENNReal.ofReal A') +
      ENNReal.ofReal (1 + s⁻¹) * ENNReal.ofReal p =
      ENNReal.ofReal ((1 + s) * (A + A') + (1 + s⁻¹) * p) := by
    rw [← ENNReal.ofReal_add hA hA', ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [hL, hR]
  refine ENNReal.ofReal_le_ofReal ?_
  have hu := Real.sq_sqrt hA'
  have hv := Real.sq_sqrt hp
  have hexp : s⁻¹ * (s * √A' - √p) ^ 2 = s * A' + s⁻¹ * p - 2 * (√A' * √p) := by
    have h1 : s⁻¹ * (s * √A' - √p) ^ 2 =
        (s⁻¹ * s) * s * √A' ^ 2 - 2 * (s⁻¹ * s) * (√A' * √p) + s⁻¹ * √p ^ 2 := by ring
    rw [h1, inv_mul_cancel₀ hs.ne', hu, hv]
    ring
  have h0 : 0 ≤ s⁻¹ * (s * √A' - √p) ^ 2 := mul_nonneg (inv_nonneg.2 hs.le) (sq_nonneg _)
  nlinarith

theorem flipCost_readEq_le (put : M → Selections → M)
    (hget : ∀ m s, get (put m s) = s) (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)]
    {L : HonestTable} {N : ℕ} (hB : ∀ r, r ∈ B ↔ (r.1, r.2.1, get r.2.2) ∈ Bad L N)
    {c : HwRead X Z M} {z : Z} {t : TrialPt} (hc : c = .readH z (updOf t))
    (hupd : ∀ m v, updOf t m (some v) = m ∨
      updOf t m (some v) = put m (cwSel (get m) t.l t.e t.x t.xi v))
    (SR : HwReg X Z M → Prop) [DecidablePred SR]
    (hSR : ∀ s, SR s → SelectRead L s.1 s.2.1 (get s.2.2) z t.l t.e t.x t.xi)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    flipCost B (hwReadKraus c) (readPs SR) σ ≤
      ENNReal.ofReal (encWt B L t.l t.e SR σ) + ENNReal.ofReal (readPs SR * σ).trace.re +
        2 * (ENNReal.ofReal (encWt B L t.l t.e SR σ) * ENNReal.ofReal (readPs SR * σ).trace.re) ^
          (2⁻¹ : ℝ) := by
  subst hc
  exact flipCost_getSelectReadCw_le get put hget B hB z t.l t.e t.x t.xi (updOf t) hupd SR hSR hσ

/-- **The flip cost of a read port, linearized**: on a selecting read port the codeword-selecting
read's bound (`flipCost_getSelectReadCw_le`), on the other read ports the flip terms off the empty
cell, with the cross terms split by `s`: at most `(1 + s) (E + ε + ε') + (1 + 1/s) p`. -/
theorem flipCost_le_ports (put : M → Selections → M) (hget : ∀ m s, get (put m s) = s)
    (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)] {L : HonestTable} {N : ℕ}
    (hB : ∀ r, r ∈ B ↔ (r.1, r.2.1, get r.2.2) ∈ Bad L N)
    (hupd : ∀ t m v, updOf t m (some v) = m ∨
      updOf t m (some v) = put m (cwSel (get m) t.l t.e t.x t.xi v))
    (c : HwRead X Z M) {s : ℝ} (hs : 0 < s)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    flipCost B (hwReadKraus c) (PRof get updOf L c) σ ≤
      ENNReal.ofReal (1 + s) * (encW get updOf B L c σ + epsW get updOf B L c σ) +
        ENNReal.ofReal (1 + s⁻¹) * massW get updOf L c σ := by
  by_cases ht : IsTrial updOf c
  · simp only [encW, epsW, massW, ht, ↓reduceIte, add_zero]
    have hf := flipCost_readEq_le get updOf put hget B hB (eq_readH_trialOf updOf ht)
      (hupd (trialOf updOf c).2) (trialSR get updOf L c)
      (fun s hs ↦ trialSR_of_isTrial get updOf ht hs) hσ
    exact hf.trans (cost_le_lin hs (encWt_nonneg hσ B L _ _ _)
      (re_trace_readPs_nonneg _ hσ))
  · simp only [encW, epsW, massW, ht, ↓reduceIte, zero_add]
    exact cost_le_lin' hs (re_trace_readPs_nonneg _ hσ)

omit [DecidableEq M] in
/-- **The Enc weight against the weighted count** (`encWt_le_nSelWt`). -/
theorem encW_le_cntW (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)] (L : HonestTable)
    (c : HwRead X Z M) {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef) :
    encW get updOf B L c σ ≤ ENNReal.ofReal (2 ^ 128)⁻¹ * cntW get updOf L c σ := by
  by_cases ht : IsTrial updOf c
  · simp only [encW, cntW, ht, ↓reduceIte]
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (encWt_le_nSelWt B L _ _ _ hσ)
  · simp only [encW, cntW, ht, ↓reduceIte, mul_zero, le_refl]

end ports

end lift

/-! ## Reads of `k` and `k'` cells -/

section readK

/-- **The change weight of a read that keeps the rest**: at most the number of cell contents that
change the event. The outcome only moves the cell. -/
theorem chw_le_card_of_keep {n Y R : Type} [Fintype n] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {e : n ≃ Option Y × R} {τ : Option Y → R → R} (S : Set n) [DecidablePred (· ∈ S)] (r : R)
    (hτ : ∀ y, τ (some y) r = r) :
    chw e τ S r ≤ (Finset.univ.filter fun b : Y ↦ ind S (e.symm (some b, r)) ≠ q0 e S r).card := by
  have hrow : ∀ b : Y, ∑ y : Y, cr (some b) (some y) ^ 2 ≤ 1 := fun b ↦ by
    rw [← sum_cr_sq b, Fintype.sum_option]
    simp only [cr_comm (some b)]
    exact le_add_of_nonneg_left (sq_nonneg _)
  rw [chw, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  simp only [dw, hτ]
  rw [Finset.sum_comm, Fintype.sum_option]
  have hnone : ∑ y : Y, cr none (some y) ^ 2 *
      (if ind S (e.symm (none, r)) = q0 e S r then (0 : ℝ) else 1) = 0 := by
    simp [q0]
  rw [hnone, zero_add]
  refine Finset.sum_le_sum fun b _ ↦ ?_
  rw [← Finset.sum_mul]
  by_cases h1 : ind S (e.symm (some b, r)) = q0 e S r
  · simp [h1]
  · simpa [h1] using hrow b

variable {X₁ Z₁ M : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  [Fintype M] [DecidableEq M]

omit [Fintype M] in
theorem readKrausK_apply [Nonempty Z₁] (x : X₁) (upd : M → Option Z₁ → M) (r : Option Z₁ × M)
    (s' s : HwReg X₁ Z₁ M) (hw : s.2.1.2.1 x = none) :
    readKrausK x upd r s' s = if s.2.2 = r.2 ∧ s'.2 = (s.2.1, upd r.2 r.1) ∧
      (∀ b, b ≠ x → s'.1.2.1 b = s.1.2.1 b) ∧ s'.1.1 = s.1.1 ∧ s'.1.2.2 = s.1.2.2 then
        ((cr (s'.1.2.1 x) r.1 * cr r.1 (s.1.2.1 x) : ℝ) : ℂ) else 0 := by
  rw [readKrausK, clsKraus_apply, kroneckerMap_apply, kroneckerMap_apply, cellRead_apply_none hw,
    Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp_all

omit [Fintype M] in
theorem readKrausK_hw (x : X₁) (upd : M → Option Z₁ → M) (r : Option Z₁ × M)
    {s' s : HwReg X₁ Z₁ M} (h : readKrausK x upd r s' s ≠ 0) : s'.2.1 = s.2.1 := by
  rw [readKrausK, clsKraus_apply] at h
  split_ifs at h with hc
  · rw [hc.2]
  · exact absurd rfl h

variable (x : X₁)

variable (X₁ Z₁ M) in
/-- The rest of a state of the hardwired register beside the cell `x` of `k`: the other cells of
`k`, the databases of `h` and `k'`, the hardwired cells and the memory. -/
abbrev RestK := ({j // j ≠ x} → Option Z₁) × Database Z₁ X₁ × Database X₁ Z₁ × Hw X₁ Z₁ × M

instance restKDecEqFun : DecidableEq ({j // j ≠ x} → Option Z₁) := Fintype.decidablePiFintype

instance restKDecEq : DecidableEq (RestK X₁ Z₁ M x) :=
  @instDecidableEqProd _ _ inferInstance <| @instDecidableEqProd _ _ inferInstance <|
    @instDecidableEqProd _ _ inferInstance <| @instDecidableEqProd _ _ inferInstance inferInstance

instance restKFintype : Fintype (RestK X₁ Z₁ M x) := by
  unfold RestK Hw DbReg Database
  infer_instance

/-- Splitting a state (with the trivial public register) into the cell `x` of `k` and the rest. -/
def splitK (x : X₁) : Unit × HwReg X₁ Z₁ M ≃ Option Z₁ × RestK X₁ Z₁ M x where
  toFun q := (q.2.1.2.1 x, (fun j ↦ q.2.1.2.1 j, q.2.1.1, q.2.1.2.2, q.2.2.1, q.2.2.2))
  invFun p := ((), ((p.2.2.1, fun y ↦ if h : y = x then p.1 else p.2.1 ⟨y, h⟩, p.2.2.2.1),
    p.2.2.2.2.1, p.2.2.2.2.2))
  left_inv q := by
    obtain ⟨⟨⟩, ⟨dh, dk, dk'⟩, W, m⟩ := q
    simp only [Prod.mk.injEq, and_true, true_and]
    funext y
    by_cases hy : y = x
    · subst hy
      simp
    · simp [hy]
  right_inv p := by
    obtain ⟨a, f, dh, dk', W, m⟩ := p
    simp only [↓reduceDIte, Prod.mk.injEq, true_and, and_true]
    funext j
    simp [j.2]

/-- The memory of a rest. -/
def memK (r : RestK X₁ Z₁ M x) : M := r.2.2.2.2

/-- A rest whose cell `x` of `k` is not hardwired. -/
def actK (r : RestK X₁ Z₁ M x) : Prop := r.2.2.2.1.2.1 x = none

/-- The move of a rest under a read with outcome `o`: the memory is updated. -/
def tauK (upd : M → Option Z₁ → M) (o : Option Z₁) (r : RestK X₁ Z₁ M x) : RestK X₁ Z₁ M x :=
  (r.1, r.2.1, r.2.2.1, r.2.2.2.1, upd r.2.2.2.2 o)

omit [Fintype M] in
/-- **The read port of `k` at cell `x` is a cell read.** -/
theorem cellRead_readK [Nonempty Z₁] (upd : M → Option Z₁ → M) :
    CellRead (splitK x) (actK x) (memK x) (tauK x upd)
      (fun r : Option Z₁ × M ↦ hwReadKraus (.readK x upd) r) where
  entry o m0 t s hs := by
    obtain ⟨⟨⟩, ⟨dh', dk', dk₂'⟩, W', m'⟩ := t
    obtain ⟨⟨⟩, ⟨dh, dk, dk₂⟩, W, m⟩ := s
    change W.2.1 x = none at hs
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausK x upd (o, m0)) _ _ = _
    rw [kroneckerMap_apply, Matrix.one_apply_eq, one_mul, readKrausK_apply _ _ _ _ _ hs]
    simp only [splitK, Equiv.coe_fn_mk, memK, tauK]
    refine ite_cond_congr (propext ?_)
    have hf : ((fun j : {j // j ≠ x} ↦ dk' j) = fun j : {j // j ≠ x} ↦ dk j) ↔
        ∀ b, b ≠ x → dk' b = dk b :=
      ⟨fun h b hb ↦ congrFun h ⟨b, hb⟩, fun h ↦ funext fun j ↦ h j j.2⟩
    simp only [Prod.mk.injEq, hf]
    constructor
    · rintro ⟨rfl, ⟨rfl, rfl⟩, h3, rfl, rfl⟩
      exact ⟨rfl, h3, rfl, rfl, rfl, rfl⟩
    · rintro ⟨rfl, h3, rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, ⟨rfl, rfl⟩, h3, rfl, rfl⟩
  inj o r r' hμ hτ := by
    obtain ⟨f, dh, dk', W, m⟩ := r
    obtain ⟨f', dh₁, dk₁', W', m'⟩ := r'
    simp only [tauK, Prod.mk.injEq] at hτ
    simp only [memK] at hμ
    obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hτ
    rw [hμ]
  act_τ o r h := h
  off i t' t ht hK := by
    have h := readKrausK_hw x upd i (s' := t'.2) (s := t.2) fun h0 ↦ hK (by
      change ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausK x upd i) _ _ = 0
      rw [kroneckerMap_apply, h0, mul_zero])
    change ¬ t'.2.2.1.2.1 x = none
    rw [h]
    exact ht

omit [Fintype X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype M] [DecidableEq M] in
/-- Rebuilding a state from its rest and a cell content. -/
theorem splitK_symm_fill (q : Unit × HwReg X₁ Z₁ M) (a : Option Z₁) :
    (splitK x).symm (a, (splitK x q).2) =
      ((), ((q.2.1.1, Function.update q.2.1.2.1 x a, q.2.1.2.2), q.2.2.1, q.2.2.2)) := by
  obtain ⟨⟨⟩, ⟨dh, dk, dk'⟩, W, m⟩ := q
  simp only [splitK, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Prod.mk.injEq, and_true, true_and]
  funext y
  by_cases hy : y = x
  · subst hy
    simp
  · simp [hy]

omit [Fintype X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype M] [DecidableEq M] in
theorem splitK_symm_none (q : Unit × HwReg X₁ Z₁ M) (hq : q.2.1.2.1 x = none) :
    (splitK x).symm (none, (splitK x q).2) = q := by
  rw [splitK_symm_fill]
  obtain ⟨⟨⟩, ⟨dh, dk, dk'⟩, W, m⟩ := q
  simp only [Prod.mk.injEq, and_true, true_and]
  rw [← hq, Function.update_eq_self]

/-- **The flip cost of a read of a `k` cell that keeps the memory.** Let `SR` select states whose
cell `x` of `k` is neither recorded nor hardwired, and at most `c s` contents of the cell move a
selected state outside `S` into `S`, while a selected state in `S` stays in `S`. Then with
`P = readPs SR`, `ε, ε' ≤ E = ∑_{SR, ∉ S} c / |Z| · σ_ss`. -/
theorem flipCost_readK_le [Nonempty Z₁] (S : Set (HwReg X₁ Z₁ M)) [DecidablePred (· ∈ S)]
    (upd : M → Option Z₁ → M) (hupd : ∀ m o, upd m o = m) (SR : HwReg X₁ Z₁ M → Prop)
    [DecidablePred SR] (c : HwReg X₁ Z₁ M → ℕ)
    (hSR : ∀ s, SR s → s.1.2.1 x = none ∧ s.2.1.2.1 x = none)
    (hcnt : ∀ s, SR s → s ∉ S → (Finset.univ.filter fun b : Z₁ ↦
      ((s.1.1, Function.update s.1.2.1 x (some b), s.1.2.2), s.2.1, s.2.2) ∈ S).card ≤ c s)
    (hmono : ∀ s b, SR s → s ∈ S →
      ((s.1.1, Function.update s.1.2.1 x (some b), s.1.2.2), s.2.1, s.2.2) ∈ S)
    {σ : Matrix (Unit × HwReg X₁ Z₁ M) (Unit × HwReg X₁ Z₁ M) ℂ} (hσ : σ.PosSemidef) :
    flipCost S (hwReadKraus (.readK x upd)) (readPs SR) σ ≤
      ENNReal.ofReal (∑ q, if SR q.2 ∧ q.2 ∉ S then
          (c q.2 : ℝ) / Fintype.card Z₁ * (σ q q).re else 0) +
        ENNReal.ofReal (readPs SR * σ).trace.re +
      2 * (ENNReal.ofReal (∑ q, if SR q.2 ∧ q.2 ∉ S then
          (c q.2 : ℝ) / Fintype.card Z₁ * (σ q q).re else 0) *
        ENNReal.ofReal (readPs SR * σ).trace.re) ^ (2⁻¹ : ℝ) := by
  set gd : RestK X₁ Z₁ M x → Prop := fun r ↦ SR ((splitK x).symm (none, r)).2
  have : DecidablePred gd := fun r ↦ inferInstanceAs (Decidable (SR _))
  have hgd_iff : ∀ q, (gd (splitK x q).2 ∧ (splitK x q).1 = none) ↔ SR q.2 := fun q ↦ by
    constructor
    · rintro ⟨h1, h2⟩
      have h0 : q.2.1.2.1 x = none := h2
      simpa only [gd, splitK_symm_none x q h0] using h1
    · intro hq
      have h0 := (hSR _ hq).1
      exact ⟨by simpa only [gd, splitK_symm_none x q h0] using hq, h0⟩
  have hP : readPs SR = readP (splitK x) gd := by
    unfold readPs readP pp
    congr 1
    funext q
    exact ite_cond_congr (propext (hgd_iff q)).symm
  have hgdact : ∀ r, gd r → actK x r := fun r h ↦ (hSR _ h).2
  have hcell := cellRead_readK (M := M) x upd
  have hF : (∑ r : (HwRead.readK x upd : HwRead X₁ Z₁ M).Result,
      (hwReadKraus (.readK x upd) r)ᴴ * indProj (liftSet S) * hwReadKraus (.readK x upd) r -
        indProj (liftSet S)) =
      flipOp (fun r : Option Z₁ × M ↦ hwReadKraus (.readK x upd) r) (liftSet S) := by
    rw [flipOp]
  have hN : (0 : ℝ) < Fintype.card Z₁ := Nat.cast_pos.2 Fintype.card_pos
  have hτ : ∀ (r : RestK X₁ Z₁ M x) (y : Z₁), tauK x upd (some y) r = r := fun r y ↦ by
    simp only [tauK, hupd]
  have hchw : ∀ q : Unit × HwReg X₁ Z₁ M, SR q.2 →
      chw (splitK x) (tauK x upd) (liftSet S) (splitK x q).2 ≤
        if q.2 ∈ S then 0 else (c q.2 : ℝ) := by
    intro q hq
    refine (chw_le_card_of_keep (liftSet S) _ fun y ↦ hτ _ y).trans ?_
    have hq0 : q0 (splitK x) (liftSet S) (splitK x q).2 = if q.2 ∈ S then 1 else 0 := by
      rw [q0, splitK_symm_none x q (hSR _ hq).1]
      rfl
    have hy : ∀ b : Z₁, ind (liftSet S) ((splitK x).symm (some b, (splitK x q).2)) =
        if ((q.2.1.1, Function.update q.2.1.2.1 x (some b), q.2.1.2.2), q.2.2.1, q.2.2.2) ∈ S
          then 1 else 0 := fun b ↦ by
      rw [splitK_symm_fill]
      rfl
    simp only [hq0, hy]
    by_cases hS : q.2 ∈ S
    · simp only [hS, ↓reduceIte]
      rw [Nat.cast_nonpos, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro b _ hb
      exact hb (ite_eq_left (hmono q.2 b hq hS))
    · simp only [hS, ↓reduceIte]
      rw [Nat.cast_le]
      refine (Finset.card_le_card fun b hb ↦ ?_).trans (hcnt q.2 hq hS)
      have hb' := (Finset.mem_filter.1 hb).2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      by_contra hn
      exact hb' (ite_eq_right hn)
  have hE : (∑ q, if gd (splitK x q).2 ∧ (splitK x q).1 = none then
        chw (splitK x) (tauK x upd) (liftSet S) (splitK x q).2 / Fintype.card Z₁ * (σ q q).re
          else 0) ≤
      ∑ q, if SR q.2 ∧ q.2 ∉ S then (c q.2 : ℝ) / Fintype.card Z₁ * (σ q q).re else 0 := by
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [ite_cond_congr (propext (hgd_iff q))]
    have hre : 0 ≤ (σ q q).re := (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    by_cases hq : SR q.2
    · have hc := hchw q hq
      by_cases hS : q.2 ∈ S
      · rw [ite_eq_left hS] at hc
        rw [ite_eq_left hq, ite_eq_right fun h ↦ h.2 hS]
        exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hc hN.le) hre
      · rw [ite_eq_right hS] at hc
        rw [ite_eq_left hq, ite_eq_left ⟨hq, hS⟩]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hc hN.le) hre
    · rw [ite_eq_right hq, ite_eq_right fun h ↦ hq h.1]
  apply flipCost_le_of
  · rw [hF, hP]
    exact (re_trace_eps_le (liftSet S) gd hcell hgdact hσ).trans hE
  · rw [hF, hP]
    exact (re_trace_eps'_le (liftSet S) gd hcell hgdact hσ).trans hE

end readK

section readK'

variable {X₁ Z₁ M : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  [Fintype M] [DecidableEq M]

omit [Fintype M] in
theorem readKrausK'_apply [Nonempty Z₁] (x : X₁) (upd : M → Option Z₁ → M) (r : Option Z₁ × M)
    (s' s : HwReg X₁ Z₁ M) (hw : s.2.1.2.2 x = none) :
    readKrausK' x upd r s' s = if s.2.2 = r.2 ∧ s'.2 = (s.2.1, upd r.2 r.1) ∧
      (∀ b, b ≠ x → s'.1.2.2 b = s.1.2.2 b) ∧ s'.1.1 = s.1.1 ∧ s'.1.2.1 = s.1.2.1 then
        ((cr (s'.1.2.2 x) r.1 * cr r.1 (s.1.2.2 x) : ℝ) : ℂ) else 0 := by
  rw [readKrausK', clsKraus_apply, kroneckerMap_apply, kroneckerMap_apply, cellRead_apply_none hw,
    Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp_all

omit [Fintype M] in
theorem readKrausK'_hw (x : X₁) (upd : M → Option Z₁ → M) (r : Option Z₁ × M)
    {s' s : HwReg X₁ Z₁ M} (h : readKrausK' x upd r s' s ≠ 0) : s'.2.1 = s.2.1 := by
  rw [readKrausK', clsKraus_apply] at h
  split_ifs at h with hc
  · rw [hc.2]
  · exact absurd rfl h

variable (x : X₁)

/-- Splitting a state (with the trivial public register) into the cell `x` of `k'` and the rest
(`RestK`: the other cells of `k'`, the databases of `h` and `k`, the hardwired cells, the
memory). -/
def splitK' (x : X₁) : Unit × HwReg X₁ Z₁ M ≃ Option Z₁ × RestK X₁ Z₁ M x where
  toFun q := (q.2.1.2.2 x, (fun j ↦ q.2.1.2.2 j, q.2.1.1, q.2.1.2.1, q.2.2.1, q.2.2.2))
  invFun p := ((), ((p.2.2.1, p.2.2.2.1, fun y ↦ if h : y = x then p.1 else p.2.1 ⟨y, h⟩),
    p.2.2.2.2.1, p.2.2.2.2.2))
  left_inv q := by
    obtain ⟨⟨⟩, ⟨dh, dk, dk'⟩, W, m⟩ := q
    simp only [Prod.mk.injEq, and_true, true_and]
    funext y
    by_cases hy : y = x
    · subst hy
      simp
    · simp [hy]
  right_inv p := by
    obtain ⟨a, f, dh, dk, W, m⟩ := p
    simp only [↓reduceDIte, Prod.mk.injEq, true_and, and_true]
    funext j
    simp [j.2]

/-- A rest whose cell `x` of `k'` is not hardwired. -/
def actK' (r : RestK X₁ Z₁ M x) : Prop := r.2.2.2.1.2.2 x = none

omit [Fintype M] in
/-- **The read port of `k'` at cell `x` is a cell read.** -/
theorem cellRead_readK' [Nonempty Z₁] (upd : M → Option Z₁ → M) :
    CellRead (splitK' x) (actK' x) (memK x) (tauK x upd)
      (fun r : Option Z₁ × M ↦ hwReadKraus (.readK' x upd) r) where
  entry o m0 t s hs := by
    obtain ⟨⟨⟩, ⟨dh', dk', dk₂'⟩, W', m'⟩ := t
    obtain ⟨⟨⟩, ⟨dh, dk, dk₂⟩, W, m⟩ := s
    change W.2.2 x = none at hs
    change ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausK' x upd (o, m0)) _ _ = _
    rw [kroneckerMap_apply, Matrix.one_apply_eq, one_mul, readKrausK'_apply _ _ _ _ _ hs]
    simp only [splitK', Equiv.coe_fn_mk, memK, tauK]
    refine ite_cond_congr (propext ?_)
    have hf : ((fun j : {j // j ≠ x} ↦ dk₂' j) = fun j : {j // j ≠ x} ↦ dk₂ j) ↔
        ∀ b, b ≠ x → dk₂' b = dk₂ b :=
      ⟨fun h b hb ↦ congrFun h ⟨b, hb⟩, fun h ↦ funext fun j ↦ h j j.2⟩
    simp only [Prod.mk.injEq, hf]
    constructor
    · rintro ⟨rfl, ⟨rfl, rfl⟩, h3, rfl, rfl⟩
      exact ⟨rfl, h3, rfl, rfl, rfl, rfl⟩
    · rintro ⟨rfl, h3, rfl, rfl, rfl, rfl⟩
      exact ⟨rfl, ⟨rfl, rfl⟩, h3, rfl, rfl⟩
  inj o r r' hμ hτ := by
    obtain ⟨f, dh, dk, W, m⟩ := r
    obtain ⟨f', dh₁, dk₁, W', m'⟩ := r'
    simp only [tauK, Prod.mk.injEq] at hτ
    simp only [memK] at hμ
    obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hτ
    rw [hμ]
  act_τ o r h := h
  off i t' t ht hK := by
    have h := readKrausK'_hw x upd i (s' := t'.2) (s := t.2) fun h0 ↦ hK (by
      change ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausK' x upd i) _ _ = 0
      rw [kroneckerMap_apply, h0, mul_zero])
    change ¬ t'.2.2.1.2.2 x = none
    rw [h]
    exact ht

omit [Fintype X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype M] [DecidableEq M] in
theorem splitK'_symm_fill (q : Unit × HwReg X₁ Z₁ M) (a : Option Z₁) :
    (splitK' x).symm (a, (splitK' x q).2) =
      ((), ((q.2.1.1, q.2.1.2.1, Function.update q.2.1.2.2 x a), q.2.2.1, q.2.2.2)) := by
  obtain ⟨⟨⟩, ⟨dh, dk, dk'⟩, W, m⟩ := q
  simp only [splitK', Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Prod.mk.injEq, and_true, true_and]
  funext y
  by_cases hy : y = x
  · subst hy
    simp
  · simp [hy]

omit [Fintype X₁] [Fintype Z₁] [DecidableEq Z₁] [Fintype M] [DecidableEq M] in
theorem splitK'_symm_none (q : Unit × HwReg X₁ Z₁ M) (hq : q.2.1.2.2 x = none) :
    (splitK' x).symm (none, (splitK' x q).2) = q := by
  rw [splitK'_symm_fill]
  obtain ⟨⟨⟩, ⟨dh, dk, dk'⟩, W, m⟩ := q
  simp only [Prod.mk.injEq, and_true, true_and]
  rw [← hq, Function.update_eq_self]

/-- **The flip cost of a read of a `k'` cell that keeps the memory** (as `flipCost_readK_le`). -/
theorem flipCost_readK'_le [Nonempty Z₁] (S : Set (HwReg X₁ Z₁ M)) [DecidablePred (· ∈ S)]
    (upd : M → Option Z₁ → M) (hupd : ∀ m o, upd m o = m) (SR : HwReg X₁ Z₁ M → Prop)
    [DecidablePred SR] (c : HwReg X₁ Z₁ M → ℕ)
    (hSR : ∀ s, SR s → s.1.2.2 x = none ∧ s.2.1.2.2 x = none)
    (hcnt : ∀ s, SR s → s ∉ S → (Finset.univ.filter fun b : Z₁ ↦
      ((s.1.1, s.1.2.1, Function.update s.1.2.2 x (some b)), s.2.1, s.2.2) ∈ S).card ≤ c s)
    (hmono : ∀ s b, SR s → s ∈ S →
      ((s.1.1, s.1.2.1, Function.update s.1.2.2 x (some b)), s.2.1, s.2.2) ∈ S)
    {σ : Matrix (Unit × HwReg X₁ Z₁ M) (Unit × HwReg X₁ Z₁ M) ℂ} (hσ : σ.PosSemidef) :
    flipCost S (hwReadKraus (.readK' x upd)) (readPs SR) σ ≤
      ENNReal.ofReal (∑ q, if SR q.2 ∧ q.2 ∉ S then
          (c q.2 : ℝ) / Fintype.card Z₁ * (σ q q).re else 0) +
        ENNReal.ofReal (readPs SR * σ).trace.re +
      2 * (ENNReal.ofReal (∑ q, if SR q.2 ∧ q.2 ∉ S then
          (c q.2 : ℝ) / Fintype.card Z₁ * (σ q q).re else 0) *
        ENNReal.ofReal (readPs SR * σ).trace.re) ^ (2⁻¹ : ℝ) := by
  set gd : RestK X₁ Z₁ M x → Prop := fun r ↦ SR ((splitK' x).symm (none, r)).2
  have : DecidablePred gd := fun r ↦ inferInstanceAs (Decidable (SR _))
  have hgd_iff : ∀ q, (gd (splitK' x q).2 ∧ (splitK' x q).1 = none) ↔ SR q.2 := fun q ↦ by
    constructor
    · rintro ⟨h1, h2⟩
      have h0 : q.2.1.2.2 x = none := h2
      simpa only [gd, splitK'_symm_none x q h0] using h1
    · intro hq
      have h0 := (hSR _ hq).1
      exact ⟨by simpa only [gd, splitK'_symm_none x q h0] using hq, h0⟩
  have hP : readPs SR = readP (splitK' x) gd := by
    unfold readPs readP pp
    congr 1
    funext q
    exact ite_cond_congr (propext (hgd_iff q)).symm
  have hgdact : ∀ r, gd r → actK' x r := fun r h ↦ (hSR _ h).2
  have hcell := cellRead_readK' (M := M) x upd
  have hF : (∑ r : (HwRead.readK' x upd : HwRead X₁ Z₁ M).Result,
      (hwReadKraus (.readK' x upd) r)ᴴ * indProj (liftSet S) * hwReadKraus (.readK' x upd) r -
        indProj (liftSet S)) =
      flipOp (fun r : Option Z₁ × M ↦ hwReadKraus (.readK' x upd) r) (liftSet S) := by
    rw [flipOp]
  have hN : (0 : ℝ) < Fintype.card Z₁ := Nat.cast_pos.2 Fintype.card_pos
  have hτ : ∀ (r : RestK X₁ Z₁ M x) (y : Z₁), tauK x upd (some y) r = r := fun r y ↦ by
    simp only [tauK, hupd]
  have hchw : ∀ q : Unit × HwReg X₁ Z₁ M, SR q.2 →
      chw (splitK' x) (tauK x upd) (liftSet S) (splitK' x q).2 ≤
        if q.2 ∈ S then 0 else (c q.2 : ℝ) := by
    intro q hq
    refine (chw_le_card_of_keep (liftSet S) _ fun y ↦ hτ _ y).trans ?_
    have hq0 : q0 (splitK' x) (liftSet S) (splitK' x q).2 = if q.2 ∈ S then 1 else 0 := by
      rw [q0, splitK'_symm_none x q (hSR _ hq).1]
      rfl
    have hy : ∀ b : Z₁, ind (liftSet S) ((splitK' x).symm (some b, (splitK' x q).2)) =
        if ((q.2.1.1, q.2.1.2.1, Function.update q.2.1.2.2 x (some b)), q.2.2.1, q.2.2.2) ∈ S
          then 1 else 0 := fun b ↦ by
      rw [splitK'_symm_fill]
      rfl
    simp only [hq0, hy]
    by_cases hS : q.2 ∈ S
    · simp only [hS, ↓reduceIte]
      rw [Nat.cast_nonpos, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro b _ hb
      exact hb (ite_eq_left (hmono q.2 b hq hS))
    · simp only [hS, ↓reduceIte]
      rw [Nat.cast_le]
      refine (Finset.card_le_card fun b hb ↦ ?_).trans (hcnt q.2 hq hS)
      have hb' := (Finset.mem_filter.1 hb).2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      by_contra hn
      exact hb' (ite_eq_right hn)
  have hE : (∑ q, if gd (splitK' x q).2 ∧ (splitK' x q).1 = none then
        chw (splitK' x) (tauK x upd) (liftSet S) (splitK' x q).2 / Fintype.card Z₁ * (σ q q).re
          else 0) ≤
      ∑ q, if SR q.2 ∧ q.2 ∉ S then (c q.2 : ℝ) / Fintype.card Z₁ * (σ q q).re else 0 := by
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [ite_cond_congr (propext (hgd_iff q))]
    have hre : 0 ≤ (σ q q).re := (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    by_cases hq : SR q.2
    · have hc := hchw q hq
      by_cases hS : q.2 ∈ S
      · rw [ite_eq_left hS] at hc
        rw [ite_eq_left hq, ite_eq_right fun h ↦ h.2 hS]
        exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hc hN.le) hre
      · rw [ite_eq_right hS] at hc
        rw [ite_eq_left hq, ite_eq_left ⟨hq, hS⟩]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hc hN.le) hre
    · rw [ite_eq_right hq, ite_eq_right fun h ↦ hq h.1]
  apply flipCost_le_of
  · rw [hF, hP]
    exact (re_trace_eps_le (liftSet S) gd hcell hgdact hσ).trans hE
  · rw [hF, hP]
    exact (re_trace_eps'_le (liftSet S) gd hcell hgdact hσ).trans hE

end readK'

/-! ## The flip counts of `k`, `k'` reads for the XMSS event -/

section readBad

variable {L : HonestTable} {N : ℕ}

open scoped Classical in
/-- **Filling a `k` cell by a read**, neither recorded nor hardwired: the capacity-scale count of
`card_targetBad_updateK_le` (the memory and the hardwired cells kept). -/
theorem card_flip_readK_bad_le {G T : ℕ} (hπ : PermGood L.perm G) {D : DbReg X Z} {W : Hw X Z}
    {m : Selections} (hs : (D, W, m) ∉ Bad L N) (hT : N + dbGrade D ≤ T) {x : X}
    (hD : D.2.1 x = none) (hW : W.2.1 x = none) :
    (Finset.univ.filter fun b : Z ↦
      ((D.1, Function.update D.2.1 x (some b), D.2.2), W, m) ∈ Bad L N).card ≤
        (T + 1) * ((T + 1) * T + 2 * T) * G := by
  by_cases hN : dbGrade W ≤ N
  swap
  · rw [Finset.filter_false_of_mem fun b _ hb ↦ hN hb.1]
    simp
  have hU : union W D ∉ TargetBad L.perm trunc128 (xmssTgtHw L W m) := fun h ↦ hs ⟨hN, h⟩
  have hx : (union W D).k x = none := by
    show (W.2.1 x).or (D.2.1 x) = none
    rw [hW, hD]
    rfl
  refine card_filter_le_of_imp (card_targetBad_updateK_le hπ hU
    ((size_unionK_le W D).trans (by omega)) ((size_unionK'_le W D).trans (by omega)) hx)
    fun b hb ↦ ?_
  have h2 : union W (D.1, Function.update D.2.1 x (some b), D.2.2) ∈
      TargetBad L.perm trunc128 (xmssTgtHw L W m) := hb.2
  rwa [union_updateK W hW] at h2

open scoped Classical in
/-- **Filling a `k'` cell by a read**, neither recorded nor hardwired: the capacity-scale count of
`card_targetBad_updateK'_le`. -/
theorem card_flip_readK'_bad_le {G T : ℕ} (hπ : PermGood L.perm G) {D : DbReg X Z} {W : Hw X Z}
    {m : Selections} (hs : (D, W, m) ∉ Bad L N) (hT : N + dbGrade D ≤ T) {x : X}
    (hD : D.2.2 x = none) (hW : W.2.2 x = none) :
    (Finset.univ.filter fun b : Z ↦
      ((D.1, D.2.1, Function.update D.2.2 x (some b)), W, m) ∈ Bad L N).card ≤
        (T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T := by
  by_cases hN : dbGrade W ≤ N
  swap
  · rw [Finset.filter_false_of_mem fun b _ hb ↦ hN hb.1]
    simp
  have hU : union W D ∉ TargetBad L.perm trunc128 (xmssTgtHw L W m) := fun h ↦ hs ⟨hN, h⟩
  have hx : (union W D).k' x = none := by
    show (W.2.2 x).or (D.2.2 x) = none
    rw [hW, hD]
    rfl
  refine card_filter_le_of_imp (card_targetBad_updateK'_le hπ hU
    ((size_unionH_le W D).trans (by omega)) ((size_unionK_le W D).trans (by omega))
    ((size_unionK'_le W D).trans (by omega)) hx) fun b hb ↦ ?_
  have h2 : union W (D.1, D.2.1, Function.update D.2.2 x (some b)) ∈
      TargetBad L.perm trunc128 (xmssTgtHw L W m) := hb.2
  rwa [union_updateK' W hW] at h2

end readBad

/-! ## Weights along a run -/

section run

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {Λ : LocalSig.{u, v}}
  (I : Λ.Interp) {Ω : QReg → Type w} {A : QReg}

/-- **Summed weights, linearly**: a weight below `c₁ w₁ + c₂ w₂ + w₃` on the positive semidefinite
inputs sums along a run to at most `c₁ W₁ + c₂ W₂ + W₃`. -/
theorem totalWeight_le_lin (w w₁ w₂ w₃ : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (c₁ c₂ : ℝ≥0∞) (h : ∀ i σ, σ.PosSemidef → w i σ ≤ c₁ * w₁ i σ + c₂ * w₂ i σ + w₃ i σ)
    (x : QuantumComp Λ spec Ω A) {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.totalWeight I w x ρ ≤
      c₁ * R.totalWeight I w₁ x ρ + c₂ * R.totalWeight I w₂ x ρ + R.totalWeight I w₃ x ρ := by
  unfold QuantumRuntime.totalWeight
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun j ↦ (R.queryWeight_mono I h x hρ j).trans_eq ?_
  rw [R.queryWeight_add I, R.queryWeight_add I, R.queryWeight_const_mul I,
    R.queryWeight_const_mul I]

/-- Summed weights are monotone and linear: `w ≤ c₁ w₁ + c₂ w₂` gives `W ≤ c₁ W₁ + c₂ W₂`. -/
theorem totalWeight_le_add (w w₁ w₂ : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (c₁ c₂ : ℝ≥0∞) (h : ∀ i σ, σ.PosSemidef → w i σ ≤ c₁ * w₁ i σ + c₂ * w₂ i σ)
    (x : QuantumComp Λ spec Ω A) {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef) :
    R.totalWeight I w x ρ ≤ c₁ * R.totalWeight I w₁ x ρ + c₂ * R.totalWeight I w₂ x ρ := by
  unfold QuantumRuntime.totalWeight
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun j ↦ (R.queryWeight_mono I h x hρ j).trans_eq ?_
  rw [R.queryWeight_add I, R.queryWeight_const_mul I, R.queryWeight_const_mul I]

/-- `(√a + √b)²` in `ℝ≥0∞`. -/
theorem ofReal_sq_sqrt_add (a b : ℝ) :
    ENNReal.ofReal ((√a + √b) ^ 2) = (ENNReal.ofReal √a + ENNReal.ofReal b ^ (2⁻¹ : ℝ)) ^ 2 := by
  rw [ENNReal.ofReal_pow (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
    ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ENNReal.ofReal_rpow_inv_two]

/-- **Optimizing the split**: if `T ≤ (1 + s) a + (1 + 1/s) b + c` for every `s > 0`, then
`T ≤ (√a + √b)² + c`. -/
theorem le_sq_add_of_forall_lin {T a b c : ℝ≥0∞}
    (h : ∀ s : ℝ, 0 < s → T ≤ ENNReal.ofReal (1 + s) * a + ENNReal.ofReal (1 + s⁻¹) * b + c) :
    T ≤ (a ^ (2⁻¹ : ℝ) + b ^ (2⁻¹ : ℝ)) ^ 2 + c := by
  by_cases ha : a = ⊤
  · simp [ha]
  by_cases hb : b = ⊤
  · simp [hb]
  by_cases hc : c = ⊤
  · simp [hc]
  obtain ⟨α, hα, rfl⟩ : ∃ α : ℝ, 0 ≤ α ∧ a = ENNReal.ofReal α :=
    ⟨a.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal ha).symm⟩
  obtain ⟨β, hβ, rfl⟩ : ∃ β : ℝ, 0 ≤ β ∧ b = ENNReal.ofReal β :=
    ⟨b.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hb).symm⟩
  rw [ENNReal.ofReal_rpow_inv_two α, ← ofReal_sq_sqrt_add]
  have hs : ∀ s : ℝ, 0 < s →
      T ≤ ENNReal.ofReal ((1 + s) * α + (1 + s⁻¹) * β) + c := fun s hs ↦ by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity)]
    exact h s hs
  have hu := Real.sq_sqrt hα
  have hv := Real.sq_sqrt hβ
  rcases hα.eq_or_lt with hα0 | hαp
  · -- `a = 0`: `s` large.
    subst hα0
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    have hεr : (0 : ℝ) < ε := hε
    refine (hs ((β + 1) / ε) (by positivity)).trans ?_
    rw [add_right_comm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (by positivity) hεr.le]
    refine add_le_add (ENNReal.ofReal_le_ofReal ?_) le_rfl
    rw [Real.sqrt_zero, zero_add, Real.sq_sqrt hβ, inv_div]
    have h1 : ε / (β + 1) * β ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  rcases hβ.eq_or_lt with hβ0 | hβp
  · -- `b = 0`: `s` small.
    subst hβ0
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    have hεr : (0 : ℝ) < ε := hε
    refine (hs (ε / (α + 1)) (by positivity)).trans ?_
    rw [add_right_comm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (by positivity) hεr.le]
    refine add_le_add (ENNReal.ofReal_le_ofReal ?_) le_rfl
    rw [Real.sqrt_zero, add_zero, Real.sq_sqrt hα]
    have h1 : ε / (α + 1) * α ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  · -- both positive: `s = √b / √a`.
    have hu0 : 0 < √α := Real.sqrt_pos.2 hαp
    have hv0 : 0 < √β := Real.sqrt_pos.2 hβp
    have key : (1 + √β / √α) * α + (1 + (√β / √α)⁻¹) * β = (√α + √β) ^ 2 := by
      calc (1 + √β / √α) * α + (1 + (√β / √α)⁻¹) * β
          = (1 + √β / √α) * √α ^ 2 + (1 + √α / √β) * √β ^ 2 := by rw [inv_div, hu, hv]
        _ = (√α + √β) ^ 2 := by
          have := hu0.ne'
          have := hv0.ne'
          field_simp
          ring
    rw [← key]
    exact hs (√β / √α) (by positivity)

end run

/-! ## The ports of the hardwired runtime -/

section hw

variable {M : Type} [Fintype M] [DecidableEq M] {t : QuantumOracleSpec.{0, 0}} {D : QReg}

omit [Fintype M] [DecidableEq M] in
/-- **The costs on the ports of the hardwired runtime with further ports, split**: a read cost below
`c₁ d₁ + c₂ d₂ + d₃` gives the same split of `extWeight (hwCost dR dP)`, the program costs going
with `d₃`. -/
theorem extWeight_hwCost_le_lin (dR d₁ d₂ d₃ : HwRead X Z M → Matrix (Unit × D) (Unit × D) ℂ → ℝ≥0∞)
    (dP : HwProg X Z → Matrix (Unit × D) (Unit × D) ℂ → ℝ≥0∞) (c₁ c₂ : ℝ≥0∞)
    (h : ∀ c σ, σ.PosSemidef → dR c σ ≤ c₁ * d₁ c σ + c₂ * d₂ c σ + d₃ c σ)
    (i : ((hwSpec X Z M).sum t).Port)
    (σ : Matrix (((hwSpec X Z M).sum t).In i × D) (((hwSpec X Z M).sum t).In i × D) ℂ)
    (hσ : σ.PosSemidef) :
    extWeight (t := t) (hwCost dR dP) i σ ≤
      c₁ * extWeight (t := t) (hwCost d₁ fun _ _ ↦ 0) i σ +
        c₂ * extWeight (t := t) (hwCost d₂ fun _ _ ↦ 0) i σ +
          extWeight (t := t) (hwCost d₃ dP) i σ := by
  rcases i with ((_ | c) | c) | _
  · simp only [extWeight, sumWeight, hwCost, mul_zero, zero_add, le_refl]
  · exact h c σ hσ
  · simp only [extWeight, sumWeight, hwCost, mul_zero, zero_add, le_refl]
  · simp only [extWeight, sumWeight, mul_zero, zero_add, le_refl]

omit [Fintype M] [DecidableEq M] in
/-- A read cost below `c₁ d₁ + c₂ d₂` gives the same split of `extWeight (hwCost dR 0)`. -/
theorem extWeight_hwCost_le_add (dR d₁ d₂ : HwRead X Z M → Matrix (Unit × D) (Unit × D) ℂ → ℝ≥0∞)
    (c₁ c₂ : ℝ≥0∞) (h : ∀ c σ, σ.PosSemidef → dR c σ ≤ c₁ * d₁ c σ + c₂ * d₂ c σ)
    (i : ((hwSpec X Z M).sum t).Port)
    (σ : Matrix (((hwSpec X Z M).sum t).In i × D) (((hwSpec X Z M).sum t).In i × D) ℂ)
    (hσ : σ.PosSemidef) :
    extWeight (t := t) (hwCost dR fun _ _ ↦ 0) i σ ≤
      c₁ * extWeight (t := t) (hwCost d₁ fun _ _ ↦ 0) i σ +
        c₂ * extWeight (t := t) (hwCost d₂ fun _ _ ↦ 0) i σ := by
  rcases i with ((_ | c) | c) | _
  · simp only [extWeight, sumWeight, hwCost, mul_zero, add_zero, le_refl]
  · exact h c σ hσ
  · simp only [extWeight, sumWeight, hwCost, mul_zero, add_zero, le_refl]
  · simp only [extWeight, sumWeight, mul_zero, add_zero, le_refl]

end hw

end Quantum.Xmss.Assembly

end
