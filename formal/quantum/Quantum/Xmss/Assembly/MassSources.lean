module

public import Quantum.Xmss.Assembly.GameTCalls
public import Quantum.Xmss.Hybrid.SchemeSplit

@[expose] public section

/-!
# The sources of the hidden cells, and the reparametrization of the table

Masses' hypotheses on the hidden values (`uavg_totalWeight_portMass_le`): the sources `src` of the
hidden cells on the states of `SlotInv` (GameTCalls), and the reparametrization `e` of the table
into public data and hidden values, with its good set `G`, `hinj`, `hcard`, `hsub` and the bad
fraction. `uavg_totalWeight_portMass_le_reparam` is Masses' bound with all of these discharged.

* **Designated sources** (`dsrc`): a structural slot's first payload value (a chain step's input,
  a leaf's first chain end, a node's left child). It is an input of its own slot only
  (`eq_of_isInput_dsrc`), and a slot's cells depend on its inputs only (`cellK_congr`, ...).
* **Pair goodness** (`PairGood`, `SrcGood`): a cell of one in-table slot is never the cell of
  another slot, or of the same slot with its designated source changed. Under it a cell names at
  most one pair (designated source, value) (`srcF_pair_eq`), so every hidden cell weighs `2^-128`
  (`sourcesSlotInv`, `κ = (card Digest)⁻¹ = 2^-128`, `card_digest_inv`). First-round `k`-cells
  need no goodness: a first block names its slot and carries the designated source's value
  (`cellK_zero_ne`). The hidden sets `hidH`, `hidK`, `hidK'` are the in-table slots' cells on
  source-good values. The template's hidden values are indexed by `HPos`; the sources are value
  positions (`srcFH`: none at a randomizer base `.inr`).
* **The reparametrization** (`tabEquiv`, `reparamE`): SchemeSplit's staged swap (chain starts
  become uniform slots), the chain-start exchange `csx` (their hash outputs move into Reparam's
  pad, an involution), then Reparam's `fwd`. Public data `PX` (Reparam's `(h'', w)` and the rest),
  hidden values `ValPos → Digest`. `reparamE_injOn` (`hinj`), `card_reparam_le` (`hcard`). With a
  uniform pad `RLabel → Digest` at the randomizer-base coordinates (`reparamER` on `TER`):
  `reparamER_injOn`, `card_reparamER_le`, and the same bad fraction (`badFrac_reparamER`).
* **The good set** (`goodT Q`): SchemeSplit's `schemeGood Q`, Reparam's `XGood`, and `SrcGood`.
  `hsub_reparam` (`hsub`, for Masses' in-table `pathH`, `pathK`, `pathK'`): when the computations
  `Q` read every honest path's `h`-cell (`CoversPaths Q`), the table's cells are the template's at
  the public data and hidden values (`cells_transfer`, through `xVal_congr_h` by rank).
* **The positions' computations** (`posM`, SchemeSplit's `Q` indexed by `ValPos`): the honest value
  of a position by hash queries from the parameter and the chain starts' hashes, its last query the
  input of the position's slot; `coversPaths_posM`, at most `posReads = 24 · 176 · 2^16` reads
  (`length_honestEval_posM`).
* **The bad fraction** (`goodT_bad_frac_le`, `goodT_posM_bad_frac_le`): SchemeSplit's
  (`schemeGood_frac_le`), Reparam's (`xGood_bad_frac_le`, with the `PathBad` fraction), and the
  fraction of public data and hidden values that are not source-good.
* `uavg_totalWeight_portMass_le_xmss`: Masses' bound with only `hgame`, `hinv`, `hN` left.
-/

open scoped ENNReal ComplexOrder
open IPFunctor

open Quantum.SufCma

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma HashSig.OverPermutation

/-! ## Designated sources -/

section dsrc

/-- **The designated source of a structural slot**: its first payload value. -/
def dsrc : Slot → ValPos
  | .chain l e step i => cpos l e i step.val
  | .leaf l e => cpos l e ⟨0, by decide⟩ (chainLength - 1)
  | .node l level index => tpos l (level - 1) (2 * index)
  | _ => tpos bottomLayer 0 0

theorem isInput_dsrc {s : Slot} (hs : InTable s) : IsInput (dsrc s) s := by
  cases s with
  | chain l e step i => rfl
  | leaf l e => exact ⟨⟨0, by decide⟩, rfl⟩
  | node l level index => exact Or.inl rfl
  | _ => exact absurd hs id

theorem cpos_eq_cpos {l l' : Layer} {e e' : KeyIndex} {i i' : ChainIndex} {j j' : ℕ}
    (hj : j < chainLength) (hj' : j' < chainLength) (h : cpos l e i j = cpos l' e' i' j') :
    l = l' ∧ e = e' ∧ i = i' ∧ j = j' := by
  simp only [cpos, ValPos.chain.injEq, Fin.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at h4
  exact ⟨h1, h2, h3, h4⟩

theorem tpos_eq_tpos {l l' : Layer} {a a' b b' : ℕ} (ha : a < layerHeight + 1)
    (ha' : a' < layerHeight + 1) (hb : b < 2 ^ 32) (hb' : b' < 2 ^ 32)
    (h : tpos l a b = tpos l' a' b') : l = l' ∧ a = a' ∧ b = b' := by
  simp only [tpos, ValPos.tree.injEq, Fin.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at h2
  rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] at h3
  exact ⟨h1, h2, h3⟩

theorem node_bounds {l : Layer} {level index : ℕ} (hs : InTable (.node l level index)) :
    level - 1 < layerHeight + 1 ∧ 2 * index + 1 < 2 ^ 32 := by
  obtain ⟨h1, h2, h3⟩ := hs
  have hk : 2 ^ (keyBits l - level) ≤ 2 ^ 31 :=
    Nat.pow_le_pow_right (by norm_num) (by have := keyBits_le l; omega)
  simp only [layerHeight] at h2 ⊢
  omega

theorem chainLength_eq : chainLength = 4 := rfl

/-- **A designated source is an input of its own slot only.** -/
theorem eq_of_isInput_dsrc {s s' : Slot} (hs : InTable s) (hs' : InTable s')
    (h : IsInput (dsrc s) s') : s = s' := by
  cases s with
  | chain l e step i =>
    have hst : step.val < chainLength := chainStep_lt step
    cases s' with
    | chain l' e' step' i' =>
      obtain ⟨rfl, rfl, rfl, h4⟩ := cpos_eq_cpos hst (chainStep_lt step') h
      rw [Fin.ext h4]
    | leaf l' e' =>
      obtain ⟨i', h⟩ := h
      have := (cpos_eq_cpos hst chainLength_pred_lt h).2.2.2
      have := step.isLt
      simp only [chainLength_eq] at *
      omega
    | node l' level index =>
      rcases h with h | h <;> exact ValPos.noConfusion h
    | _ => exact absurd hs' id
  | leaf l e =>
    cases s' with
    | chain l' e' step' i' =>
      have := (cpos_eq_cpos chainLength_pred_lt (chainStep_lt step') h).2.2.2
      have := step'.isLt
      simp only [chainLength_eq] at *
      omega
    | leaf l' e' =>
      obtain ⟨i', h⟩ := h
      obtain ⟨rfl, rfl, -⟩ := cpos_eq_cpos chainLength_pred_lt chainLength_pred_lt h
      rfl
    | node l' level index =>
      rcases h with h | h <;> exact ValPos.noConfusion h
    | _ => exact absurd hs' id
  | node l level index =>
    have hb := node_bounds hs
    cases s' with
    | chain l' e' step' i' => exact ValPos.noConfusion h
    | leaf l' e' =>
      obtain ⟨i', h⟩ := h
      exact ValPos.noConfusion h
    | node l' level' index' =>
      have hb' := node_bounds hs'
      have h1 := hs.1
      have h1' := hs'.1
      rcases h with h | h
      · obtain ⟨rfl, h2, h3⟩ := tpos_eq_tpos hb.1 hb'.1 (by omega) (by omega) h
        have : level = level' := by omega
        subst this
        have : index = index' := by omega
        subst this
        rfl
      · have := (tpos_eq_tpos hb.1 hb'.1 (by omega) hb'.2 h).2.2
        omega
    | _ => exact absurd hs' id
  | _ => exact absurd hs id

/-- **A slot's payload depends on its inputs only.** -/
theorem slotPayload_congr {s : Slot} {v v' : ValPos → Digest}
    (h : ∀ q, IsInput q s → v q = v' q) : slotPayload v s = slotPayload v' s := by
  cases s with
  | chain l e step i =>
    show Verification.chainPayload i _ = Verification.chainPayload i _
    rw [h _ rfl]
  | leaf l e =>
    show digestsPayload _ = digestsPayload _
    exact congrArg _ (funext fun i ↦ h _ ⟨i, rfl⟩)
  | node l level index =>
    show nodePayload _ _ = nodePayload _ _
    rw [h _ (Or.inl rfl), h _ (Or.inr rfl)]
  | _ => rfl

theorem slotInput_congr' (pub : Pub) {s : Slot} {v v' : ValPos → Digest}
    (h : ∀ q, IsInput q s → v q = v' q) : slotInput pub s v = slotInput pub s v' := by
  rw [slotInput, slotInput, slotPayload_congr h]

/-- The `k`-cell of round `j` of slot `s`. -/
def srcCellK (pub : Pub) (s : Slot) (v : ValPos → Digest) (j : ℕ) : X :=
  (roundK pub s v j).1

/-- The `k'`-cell of round `j` of slot `s`. -/
def srcCellK' (pub : Pub) (s : Slot) (v : ValPos → Digest) (j : ℕ) : X :=
  (roundK' pub s v j).1

/-- The `h`-cell of round `j` of slot `s`. -/
def srcCellH (pub : Pub) (s : Slot) (v : ValPos → Digest) (j : ℕ) : Z :=
  (roundH pub s v j).1

theorem cellK_congr (pub : Pub) {s : Slot} {v v' : ValPos → Digest}
    (h : ∀ q, IsInput q s → v q = v' q) (j : ℕ) : srcCellK pub s v j = srcCellK pub s v' j := by
  unfold srcCellK roundK
  rw [slotInput_congr' pub h]

theorem cellK'_congr (pub : Pub) {s : Slot} {v v' : ValPos → Digest}
    (h : ∀ q, IsInput q s → v q = v' q) (j : ℕ) : srcCellK' pub s v j = srcCellK' pub s v' j := by
  unfold srcCellK' roundK'
  rw [slotInput_congr' pub h]

theorem cellH_congr (pub : Pub) {s : Slot} {v v' : ValPos → Digest}
    (h : ∀ q, IsInput q s → v q = v' q) (j : ℕ) : srcCellH pub s v j = srcCellH pub s v' j := by
  unfold srcCellH
  rw [roundH_fst, roundH_fst, slotInput_congr' pub h]

end dsrc

/-! ## Sources from pair goodness, over a cell family -/

section pairs

variable {C : Type} (nB : Slot → ℕ) (c : Slot → (ValPos → Digest) → ℕ → C)

/-- **Pair goodness** of the values `v` for the cell family `c` (rounds `j < nB s`), off the pairs
of rounds `ex`: no cell of an in-table slot is a cell of another in-table slot, or of the same slot
with its designated source changed. -/
def PairGood (ex : ℕ → ℕ → Prop) (v : ValPos → Digest) : Prop :=
  ∀ s s', InTable s → InTable s' → ∀ j < nB s, ∀ j' < nB s', ¬ex j j' → ∀ d : Digest,
    (s ≠ s' ∨ d ≠ v (dsrc s)) → c s' v j' ≠ c s (Function.update v (dsrc s) d) j

/-- The cells of the in-table slots at `v`, when `v` is good. -/
def goodCells (Good : (ValPos → Digest) → Prop) (v : ValPos → Digest) : Set C :=
  {y | Good v ∧ ∃ s, InTable s ∧ ∃ j < nB s, c s v j = y}

/-- The pairs (designated source `q`, value `d`) whose update of `v` is good and has `y` as a cell
of the slot `q` is the source of. -/
def SrcCond (Good : (ValPos → Digest) → Prop) (y : C) (v : ValPos → Digest) (q : ValPos)
    (d : Digest) : Prop :=
  Good (Function.update v q d) ∧
    ∃ s, InTable s ∧ dsrc s = q ∧ ∃ j < nB s, c s (Function.update v q d) j = y

open Classical in
/-- The values of the designated source `q` making `y` a good cell. -/
noncomputable def srcF (Good : (ValPos → Digest) → Prop) (y : C) (v : ValPos → Digest)
    (q : ValPos) : Finset Digest :=
  Finset.univ.filter fun d ↦ SrcCond nB c Good y v q d

theorem srcF_update (Good : (ValPos → Digest) → Prop) (y : C) (v : ValPos → Digest)
    (q : ValPos) (d : Digest) : srcF nB c Good y (Function.update v q d) q = srcF nB c Good y v q := by
  ext d'
  simp only [srcF, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [SrcCond, SrcCond, Function.update_idem]

variable {nB c}

theorem mem_srcF {Good : (ValPos → Digest) → Prop} {y : C} {v : ValPos → Digest} {q : ValPos}
    {d : Digest} : d ∈ srcF nB c Good y v q ↔ SrcCond nB c Good y v q d := by
  classical
  unfold srcF
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ d)

/-- **A good cell names at most one source pair.** -/
theorem srcF_pair_eq {ex : ℕ → ℕ → Prop} {Good : (ValPos → Digest) → Prop}
    (hG : ∀ w, Good w → PairGood nB c ex w)
    (hex : ∀ s s', InTable s → InTable s' → ∀ j j', ex j j' → ∀ w d,
      (s ≠ s' ∨ d ≠ w (dsrc s)) → c s' w j' ≠ c s (Function.update w (dsrc s) d) j)
    (hloc : ∀ s v v', (∀ q, IsInput q s → v q = v' q) → ∀ j, c s v j = c s v' j)
    {y : C} {v : ValPos → Digest} {q₁ q₂ : ValPos} {d₁ d₂ : Digest}
    (ha : d₁ ∈ srcF nB c Good y v q₁) (hb : d₂ ∈ srcF nB c Good y v q₂) : q₁ = q₂ ∧ d₁ = d₂ := by
  obtain ⟨hg₁, s₁, hs₁, rfl, j₁, hj₁, hy₁⟩ := mem_srcF.mp ha
  obtain ⟨-, s₂, hs₂, rfl, j₂, hj₂, hy₂⟩ := mem_srcF.mp hb
  set w₁ := Function.update v (dsrc s₁) d₁ with hw₁
  have key : ∀ d, (s₂ ≠ s₁ ∨ d ≠ w₁ (dsrc s₂)) →
      c s₁ w₁ j₁ ≠ c s₂ (Function.update w₁ (dsrc s₂) d) j₂ := fun d hd ↦ by
    by_cases he : ex j₂ j₁
    · exact hex s₂ s₁ hs₂ hs₁ j₂ j₁ he w₁ d hd
    · exact hG w₁ hg₁ s₂ s₁ hs₂ hs₁ j₂ hj₂ j₁ hj₁ he d hd
  by_cases hs : s₁ = s₂
  · subst hs
    by_cases hd : d₁ = d₂
    · exact ⟨rfl, hd⟩
    · refine absurd ?_ (key d₂ (Or.inr ?_))
      · rw [hy₁, hw₁, Function.update_idem, hy₂]
      · rw [hw₁, Function.update_self]
        exact Ne.symm hd
  · refine absurd ?_ (key d₂ (Or.inl (Ne.symm hs)))
    rw [hy₁, ← hy₂]
    refine hloc s₂ _ _ (fun q hq ↦ ?_) j₂
    have hq₁ : q ≠ dsrc s₁ := fun h ↦ hs (eq_of_isInput_dsrc hs₁ hs₂ (h ▸ hq))
    by_cases hq₂ : q = dsrc s₂
    · rw [hq₂, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hq₂, Function.update_of_ne hq₂, hw₁, Function.update_of_ne hq₁]

theorem sum_card_srcF_le_one {ex : ℕ → ℕ → Prop} {Good : (ValPos → Digest) → Prop}
    (hG : ∀ w, Good w → PairGood nB c ex w)
    (hex : ∀ s s', InTable s → InTable s' → ∀ j j', ex j j' → ∀ w d,
      (s ≠ s' ∨ d ≠ w (dsrc s)) → c s' w j' ≠ c s (Function.update w (dsrc s) d) j)
    (hloc : ∀ s v v', (∀ q, IsInput q s → v q = v' q) → ∀ j, c s v j = c s v' j)
    (y : C) (v : ValPos → Digest) :
    ∑ q, (srcF nB c Good y v q).card ≤ 1 := by
  by_cases h : ∃ q d, d ∈ srcF nB c Good y v q
  · obtain ⟨q₀, d₀, hd₀⟩ := h
    rw [Fintype.sum_eq_single q₀ fun q hq ↦ Finset.card_eq_zero.mpr
      (Finset.eq_empty_of_forall_notMem fun d hd ↦ hq (srcF_pair_eq hG hex hloc hd hd₀).1)]
    exact Finset.card_le_one.mpr fun a ha b hb ↦ (srcF_pair_eq hG hex hloc ha hb).2
  · refine (Finset.sum_eq_zero fun q _ ↦ Finset.card_eq_zero.mpr
      (Finset.eq_empty_of_forall_notMem fun d hd ↦ h ⟨q, d, hd⟩)).le.trans zero_le_one

/-- The per-cell weight: at most one source pair, of weight `1 / |Digest|`. -/
theorem sum_srcF_weight_le {ex : ℕ → ℕ → Prop} {Good : (ValPos → Digest) → Prop}
    (hG : ∀ w, Good w → PairGood nB c ex w)
    (hex : ∀ s s', InTable s → InTable s' → ∀ j j', ex j j' → ∀ w d,
      (s ≠ s' ∨ d ≠ w (dsrc s)) → c s' w j' ≠ c s (Function.update w (dsrc s) d) j)
    (hloc : ∀ s v v', (∀ q, IsInput q s → v q = v' q) → ∀ j, c s v j = c s v' j)
    (y : C) (v : ValPos → Digest) :
    ∑ q, ((srcF nB c Good y v q).card : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ ≤
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [← Finset.sum_mul, ← Nat.cast_sum]
  calc ((∑ q, (srcF nB c Good y v q).card : ℕ) : ℝ≥0∞) *
        (Fintype.card Digest : ℝ≥0∞)⁻¹
      ≤ (1 : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
        gcongr
        exact_mod_cast sum_card_srcF_le_one hG hex hloc y v
    _ = _ := one_mul _

/-- A hidden cell not satisfying `P`, where every in-table slot with a disclosed designated
source has its cells satisfying `P`, names its slot's undisclosed designated source. -/
theorem exists_mem_srcF {Good : (ValPos → Digest) → Prop} {y : C} {v : ValPos → Digest}
    {T : Set ValPos} {P : C → Prop} (hy : y ∈ goodCells nB c Good v)
    (hT : ∀ s, InTable s → dsrc s ∈ T → ∀ j < nB s, P (c s v j)) (hP : ¬P y) :
    ∃ q ∈ (Finset.univ : Finset ValPos), q ∉ T ∧ v q ∈ srcF nB c Good y v q := by
  obtain ⟨hg, s, hs, j, hj, rfl⟩ := hy
  refine ⟨dsrc s, by simp, fun hm ↦ hP (hT s hs hm j hj),
    mem_srcF.mpr ⟨?_, s, hs, rfl, j, hj, ?_⟩⟩
  · rw [Function.update_eq_self]
    exact hg
  · rw [Function.update_eq_self]

/-- The restriction of hidden values to the value positions commutes with an update at a value
position. -/
theorem inl_update (v : HPos → Digest) (q : ValPos) (d : Digest) :
    (fun p ↦ Function.update v (.inl q) d (.inl p)) = Function.update (fun p ↦ v (.inl p)) q d :=
  Function.update_comp_eq_of_injective v Sum.inl_injective q d

variable (nB c) in
/-- **The source values at a hidden coordinate**: `srcF` of the values at the value positions,
none at a randomizer base. -/
noncomputable def srcFH (Good : (ValPos → Digest) → Prop) (y : C) (v : HPos → Digest) :
    HPos → Finset Digest
  | .inl q => srcF nB c Good y (fun p ↦ v (.inl p)) q
  | .inr _ => ∅

theorem srcFH_update (Good : (ValPos → Digest) → Prop) (y : C) (v : HPos → Digest) (s : HPos)
    (d : Digest) : srcFH nB c Good y (Function.update v s d) s = srcFH nB c Good y v s := by
  cases s with
  | inl q =>
    rw [srcFH, srcFH, inl_update]
    exact srcF_update nB c Good y _ q d
  | inr _ => rfl

/-- `exists_mem_srcF` over the hidden coordinates: the source is a value position. -/
theorem exists_mem_srcFH {Good : (ValPos → Digest) → Prop} {y : C} {v : HPos → Digest}
    {T : Finset HPos} {P : C → Prop} (hy : y ∈ goodCells nB c Good fun p ↦ v (.inl p))
    (hT : ∀ s, InTable s → .inl (dsrc s) ∈ T → ∀ j < nB s, P (c s (fun p ↦ v (.inl p)) j))
    (hP : ¬P y) :
    ∃ s ∈ inlSet Finset.univ, s ∉ T ∧ v s ∈ srcFH nB c Good y v s := by
  obtain ⟨q, -, hq, hv⟩ := exists_mem_srcF (T := {q | (Sum.inl q : HPos) ∈ T}) (P := P) hy
    (fun s hs hm ↦ hT s hs hm) hP
  refine ⟨Sum.inl q, by simp, hq, hv⟩

/-- `sum_srcF_weight_le` over the hidden coordinates. -/
theorem sum_srcFH_weight_le {ex : ℕ → ℕ → Prop} {Good : (ValPos → Digest) → Prop}
    (hG : ∀ w, Good w → PairGood nB c ex w)
    (hex : ∀ s s', InTable s → InTable s' → ∀ j j', ex j j' → ∀ w d,
      (s ≠ s' ∨ d ≠ w (dsrc s)) → c s' w j' ≠ c s (Function.update w (dsrc s) d) j)
    (hloc : ∀ s v v', (∀ q, IsInput q s → v q = v' q) → ∀ j, c s v j = c s v' j)
    (y : C) (v : HPos → Digest) :
    ∑ s ∈ inlSet Finset.univ, ((srcFH nB c Good y v s).card : ℝ≥0∞) *
        (Fintype.card (XD s) : ℝ≥0∞)⁻¹ ≤ (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [inlSet, Finset.sum_map]
  exact sum_srcF_weight_le hG hex hloc y fun p ↦ v (.inl p)

end pairs

/-! ## The sources of the template's hidden cells -/

section sources

/-! ### First blocks name their slot and carry the designated source -/

theorem cellK_zero (pub : Pub) (s : Slot) (w : ValPos → Digest) :
    srcCellK pub s w 0 = blockOf (firstBlock (slotInput pub s w)) := by
  unfold srcCellK roundK
  dsimp only
  rw [stateAt_zero, zero_add, List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, head?_blocks,
    Option.getD_some]

theorem slotOf_slotInput (pub : Pub) {s : Slot} (hs : InTable s) (w : ValPos → Digest) :
    slotOf pub.param (absorbTail (Equiv.refl (X × Z)) (blocks (slotInput pub s w))) = some s := by
  cases s with
  | chain l e step i => exact slotOf_chain _ _ l e step i _
  | leaf l e => exact slotOf_leaf _ _ l e _
  | node l level index =>
    have hb := node_bounds hs
    exact slotOf_node _ _ l level index
      (lt_of_le_of_lt hs.2.1 (by simp only [layerHeight]; norm_num)) (by omega) _ _
  | _ => exact absurd hs id

/-- **The first block of an in-table slot's input names the slot.** -/
theorem slotOfBlock_cellK_zero (pub : Pub) {s : Slot} (hs : InTable s) (w : ValPos → Digest) :
    slotOfBlock pub.param (srcCellK pub s w 0) = some s := by
  have h := slotOf_slotInput pub hs w
  obtain ⟨rest, ht, -⟩ := absorbTail_blocks (Equiv.refl (X × Z)) (slotInput pub s w)
  rw [ht, slotOf] at h
  rw [cellK_zero]
  split_ifs at h
  · obtain rfl := Option.some.inj h
    exact False.elim hs
  · exact h

/-- **The first block of an in-table slot's input carries its designated source's value.** -/
theorem payloadLo_cellK_zero (pub : Pub) {s : Slot} (hs : InTable s) (w : ValPos → Digest) :
    payloadLo (srcCellK pub s w 0) = w (dsrc s) := by
  rw [cellK_zero]
  cases s with
  | chain l e step i => exact payloadLo_thInput _ _ _ _
  | leaf l e =>
    show payloadLo (blockOf (firstBlock (thInput pub.param _
      (digestsPayload fun i : ChainIndex ↦ w (cpos l e i (chainLength - 1)))))) = _
    rw [show digestsPayload (fun i : ChainIndex ↦ w (cpos l e i (chainLength - 1))) = _ from
      digestsPayload_succ (n := 57) _]
    exact payloadLo_thInput _ _ _ _
  | node l level index => exact payloadLo_thInput _ _ _ _
  | _ => exact absurd hs id

/-- **First-round `k`-cells are distinct** across in-table slots and designated-source values. -/
theorem cellK_zero_ne (pub : Pub) : ∀ s s', InTable s → InTable s' → ∀ j j' : ℕ,
    (j = 0 ∧ j' = 0) → ∀ (w : ValPos → Digest) (d : Digest), (s ≠ s' ∨ d ≠ w (dsrc s)) →
      srcCellK pub s' w j' ≠ srcCellK pub s (Function.update w (dsrc s) d) j := by
  rintro s s' hs hs' j j' ⟨rfl, rfl⟩ w d hd he
  have h1 := slotOfBlock_cellK_zero pub hs' w
  rw [he, slotOfBlock_cellK_zero pub hs] at h1
  obtain rfl := Option.some.inj h1
  have h2 := payloadLo_cellK_zero pub hs (Function.update w (dsrc s) d)
  rw [← he, payloadLo_cellK_zero pub hs, Function.update_self] at h2
  exact hd.elim (fun h ↦ h rfl) fun h ↦ h h2.symm

/-- **Source goodness** at the public datum `pub`: pair goodness of the `k`-cells off the first
rounds (`cellK_zero_ne` covers those), of the `k'`-cells and of the `h`-cells. -/
def SrcGood (pub : Pub) (v : ValPos → Digest) : Prop :=
  PairGood (nBlocks pub) (srcCellK pub) (fun j j' ↦ j = 0 ∧ j' = 0) v ∧
    PairGood (nBlocks pub) (srcCellK' pub) (fun _ _ ↦ False) v ∧
    PairGood (nBlocks pub) (srcCellH pub) (fun _ _ ↦ False) v

/-- The hidden `h`-cells at `pub`, `v`: the `h`-cells of the in-table slots, on good values. -/
def hidH (pub : Pub) (v : ValPos → Digest) : Set Z :=
  goodCells (nBlocks pub) (srcCellH pub) (SrcGood pub) v

/-- The hidden `k`-cells. -/
def hidK (pub : Pub) (v : ValPos → Digest) : Set X :=
  goodCells (nBlocks pub) (srcCellK pub) (SrcGood pub) v

/-- The hidden `k'`-cells. -/
def hidK' (pub : Pub) (v : ValPos → Digest) : Set X :=
  goodCells (nBlocks pub) (srcCellK' pub) (SrcGood pub) v

variable (M : Type)

/-- **The sources of the template's hidden cells** on the states of `SlotInv` (Masses' `src`,
`κ = 2^-128`): a hidden cell that is not hardwired is a cell of an in-table slot whose designated
source is undisclosed (`SlotInv`), and on good values it names at most one pair (designated
source, value). The randomizer bases are no sources. -/
noncomputable def sourcesSlotInv (pub : Pub) :
    Sources X Z HPos M HPos XD (fun r ↦ r.2.2.1) (SlotInv M pub)
      (fun v ↦ hidH pub fun p ↦ v (.inl p)) (fun v ↦ hidK pub fun p ↦ v (.inl p))
      (fun v ↦ hidK' pub fun p ↦ v (.inl p)) (Fintype.card Digest : ℝ≥0∞)⁻¹ where
  sh _ _ := inlSet Finset.univ
  sk _ _ := inlSet Finset.univ
  sk' _ _ := inlSet Finset.univ
  Fh z _ s v := srcFH (nBlocks pub) (srcCellH pub) (SrcGood pub) z v s
  Fk y _ s v := srcFH (nBlocks pub) (srcCellK pub) (SrcGood pub) y v s
  Fk' y _ s v := srcFH (nBlocks pub) (srcCellK' pub) (SrcGood pub) y v s
  hFh z _ s v d := srcFH_update _ z v s d
  hFk y _ s v d := srcFH_update _ y v s d
  hFk' y _ s v d := srcFH_update _ y v s d
  hh _ _ r hI hz hn := exists_mem_srcFH (P := fun z ↦ r.2.1.1 z ≠ none) hz
    (fun s hs hm j hj ↦ (hI s hs _ (isInput_dsrc hs) hm j hj).2.2) fun h ↦ h hn
  hk _ _ r hI hy hn := exists_mem_srcFH (P := fun y ↦ r.2.1.2.1 y ≠ none) hy
    (fun s hs hm j hj ↦ (hI s hs _ (isInput_dsrc hs) hm j hj).1) fun h ↦ h hn
  hk' _ _ r hI hy hn := exists_mem_srcFH (P := fun y ↦ r.2.1.2.2 y ≠ none) hy
    (fun s hs hm j hj ↦ (hI s hs _ (isInput_dsrc hs) hm j hj).2.1) fun h ↦ h hn
  hκh z _ v := sum_srcFH_weight_le (fun _ h ↦ h.2.2) (fun _ _ _ _ _ _ h ↦ h.elim)
    (fun _ _ _ h j ↦ cellH_congr pub h j) z v
  hκk y _ v := sum_srcFH_weight_le (fun _ h ↦ h.1) (cellK_zero_ne pub)
    (fun _ _ _ h j ↦ cellK_congr pub h j) y v
  hκk' y _ v := sum_srcFH_weight_le (fun _ h ↦ h.2.1) (fun _ _ _ _ _ _ h ↦ h.elim)
    (fun _ _ _ h j ↦ cellK'_congr pub h j) y v

theorem card_digest_inv : (Fintype.card Digest : ℝ≥0∞)⁻¹ = (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
  norm_num [digestBits]

end sources

/-! ## The reparametrization of the table -/

section reparam

/-! ### The chain starts: from SchemeSplit's slots into the pad -/

/-- A hash output from its two digest halves (`truncateHash`, `upperHalfOfHash`). -/
def unhalves (a b : Digest) : HashOutput :=
  b ++ a

theorem getLsbD_unhalves (a b : Digest) (i : ℕ) :
    (unhalves a b).getLsbD i = if i < 128 then a.getLsbD i else b.getLsbD (i - 128) :=
  BitVec.getLsbD_append (x := b) (y := a)

theorem unhalves_halves (o : HashOutput) :
    unhalves (truncateHash o) (upperHalfOfHash o) = o := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_unhalves]
  simp only [truncateHash, upperHalfOfHash, digestBits, BitVec.getLsbD_extractLsb']
  by_cases h : i < 128
  · simp [h]
  · have h2 : i - 128 < 128 := by omega
    rw [ite_eq_right h, decide_eq_true h2, Bool.true_and, show 128 + (i - 128) = i by omega]

theorem truncateHash_unhalves (a b : Digest) : truncateHash (unhalves a b) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi' : i < 128 := hi
  simp only [truncateHash, digestBits, BitVec.getLsbD_extractLsb', zero_add, getLsbD_unhalves,
    hi', ↓reduceIte, decide_true, Bool.true_and]

theorem upperHalfOfHash_unhalves (a b : Digest) : upperHalfOfHash (unhalves a b) = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi' : i < 128 := hi
  have h2 : ¬128 + i < 128 := by omega
  simp only [upperHalfOfHash, digestBits, BitVec.getLsbD_extractLsb', getLsbD_unhalves, h2,
    ↓reduceIte, hi', decide_true, Bool.true_and, Nat.add_sub_cancel_left]

/-- The start of chain `2 p + b` of key `e` of layer `l`, for the chain pair `j = (l, e, p)`. -/
def startPos (j : CsIdx) (b : ℕ) (hb : b < 2) : ValPos :=
  .chain j.1 j.2.1 ⟨2 * j.2.2.val + b, by have := j.2.2.isLt; simp only [chainCount] at *; omega⟩
    ⟨0, by decide⟩

theorem startPos_chainPair (l : Layer) (e : KeyIndex) (i : ChainIndex) (b : ℕ) (hb : b < 2)
    (h : b = i.val % 2) : startPos (l, e, chainPair i) b hb = .chain l e i ⟨0, by decide⟩ := by
  have h2 : 2 * (chainPair i).val + b = i.val := by
    show 2 * (i.val / 2) + b = i.val
    omega
  simp only [startPos, ValPos.chain.injEq, true_and, and_true]
  exact Fin.ext h2

theorem hashHalfForChain_two_mul (p : ℕ) (o : HashOutput) :
    hashHalfForChain (2 * p) o = truncateHash o :=
  ite_eq_left (by omega)

theorem hashHalfForChain_two_mul_add_one (p : ℕ) (o : HashOutput) :
    hashHalfForChain (2 * p + 1) o = upperHalfOfHash o :=
  ite_eq_right (by omega)

theorem out256_seedSlotEquiv_symm (o : MasterSeed) (r : Fin 832 → ZMod 2) :
    out256 (seedSlotEquiv.symm (o, r)) = o := by
  rw [← seedSlotEquiv_fst, Equiv.apply_symm_apply]

/-- The pad after the exchange: the chain starts read off SchemeSplit's chain-start slots. -/
def csxU (u₂ : CsIdx → X) (u : ValPos → Digest) : ValPos → Digest
  | .chain l e i j => if j.val = 0 then hashHalfForChain i.val (out256 (u₂ (l, e, chainPair i)))
      else u (.chain l e i j)
  | .tree l level index => u (.tree l level index)

/-- The chain-start slots after the exchange: their hash outputs taken from the pad's chain
starts. -/
def csxS (u₂ : CsIdx → X) (u : ValPos → Digest) : CsIdx → X :=
  fun j ↦ seedSlotEquiv.symm (unhalves (u (startPos j 0 (by decide))) (u (startPos j 1 (by decide))),
    (seedSlotEquiv (u₂ j)).2)

/-- **The chain-start exchange**: the chain starts' hash outputs of SchemeSplit's slots and the
pad's chain starts swap places. An involution. -/
def csx (a : (CsIdx → X) × (ValPos → Digest)) : (CsIdx → X) × (ValPos → Digest) :=
  (csxS a.1 a.2, csxU a.1 a.2)

theorem csxU_startPos (u₂ : CsIdx → X) (u : ValPos → Digest) (j : CsIdx) (b : ℕ) (hb : b < 2) :
    csxU u₂ u (startPos j b hb) = hashHalfForChain (2 * j.2.2.val + b) (out256 (u₂ j)) := by
  obtain ⟨l, e, p⟩ := j
  have hp : chainPair ⟨2 * p.val + b, by have := p.isLt; simp only [chainCount] at *; omega⟩ = p :=
    Fin.ext (by show (2 * p.val + b) / 2 = p.val; omega)
  show (if (0 : ℕ) = 0 then _ else _) = _
  rw [ite_eq_left rfl, hp]

theorem csx_csx (a : (CsIdx → X) × (ValPos → Digest)) : csx (csx a) = a := by
  obtain ⟨u₂, u⟩ := a
  refine Prod.ext (funext fun j ↦ ?_) (funext fun p ↦ ?_)
  · show seedSlotEquiv.symm (unhalves (csxU u₂ u (startPos j 0 (by decide)))
      (csxU u₂ u (startPos j 1 (by decide))),
      (seedSlotEquiv (csxS u₂ u j)).2) = u₂ j
    rw [csxU_startPos, csxU_startPos, add_zero, hashHalfForChain_two_mul,
      hashHalfForChain_two_mul_add_one, unhalves_halves, csxS, Equiv.apply_symm_apply,
      ← seedSlotEquiv_fst, Prod.mk.eta, Equiv.symm_apply_apply]
  · cases p with
    | chain l e i jj =>
      by_cases h0 : jj.val = 0
      · have hj : jj = ⟨0, by decide⟩ := Fin.ext h0
        subst hj
        show (if (0 : ℕ) = 0 then hashHalfForChain i.val (out256 (csxS u₂ u (l, e, chainPair i)))
          else csxU u₂ u (.chain l e i ⟨0, by decide⟩)) = _
        rw [ite_eq_left rfl, csxS, out256_seedSlotEquiv_symm]
        unfold hashHalfForChain
        split_ifs with hpar
        · rw [truncateHash_unhalves, startPos_chainPair l e i 0 _ (by omega)]
        · rw [upperHalfOfHash_unhalves, startPos_chainPair l e i 1 _ (by omega)]
      · show (if jj.val = 0 then _ else csxU u₂ u (.chain l e i jj)) = _
        rw [ite_eq_right h0]
        show (if jj.val = 0 then _ else u (.chain l e i jj)) = _
        rw [ite_eq_right h0]
    | tree l level index => rfl

/-- The public parameter's slot split into the parameter (its first `128` bits) and the rest. -/
def paramEquiv : X ≃ PublicParameter × (Fin 960 → ZMod 2) :=
  (Fin.appendEquiv 128 960).symm.trans ((bitsEquiv 128).symm.prodCongr (Equiv.refl _))

theorem paramEquiv_fst (x : X) : (paramEquiv x).1 = trunc128 x :=
  (trunc128_eq x).symm

/-! ### The reparametrization -/

/-- The tables, with SchemeSplit's extra slots and Reparam's pad. -/
abbrev TE : Type := HonestTable × (SeedSlots × (ValPos → Digest))

/-- Reparam's tables `((h, u), w)`. -/
abbrev RTab : Type := ((Z → X) × (ValPos → Digest)) × XW

/-- The rest of the table: `S₀`, SchemeSplit's public slot bits beyond the parameter, the
exchanged chain-start slots, and the scheme seed `S`. -/
abbrev Rest : Type :=
  MasterSeed × (Fin 832 → ZMod 2) × (Fin 960 → ZMod 2) × (CsIdx → X) × MasterSeed

/-- **The public data**: Reparam's public coordinates `(h'', w)` and the rest. -/
abbrev PX : Type := ((Z → X) × XW) × Rest

/-- SchemeSplit's coordinates with the pad, as Reparam's table and the rest. -/
def shufR : (Hybrid.Pub × MasterSeed) × (ValPos → Digest) ≃ RTab × Rest where
  toFun x :=
    (((x.1.1.1.keys.1, (csx (x.1.1.2.2.2, x.2)).2),
        ((paramEquiv x.1.1.2.2.1).1, x.1.1.1.perm, x.1.1.1.keys.2.1, x.1.1.1.keys.2.2)),
      (x.1.1.1.masterSeed, x.1.1.2.1, (paramEquiv x.1.1.2.2.1).2, (csx (x.1.1.2.2.2, x.2)).1,
        x.1.2))
  invFun y :=
    (((⟨(y.1.1.1, y.1.2.2.2.1, y.1.2.2.2.2), y.1.2.2.1, y.2.1⟩, y.2.2.1,
        paramEquiv.symm (y.1.2.1, y.2.2.2.1), (csx (y.2.2.2.2.1, y.1.1.2)).1), y.2.2.2.2.2),
      (csx (y.2.2.2.2.1, y.1.1.2)).2)
  left_inv x := by
    obtain ⟨⟨⟨⟨⟨h, k, k'⟩, π, S₀⟩, r, u₁, u₂⟩, S⟩, u⟩ := x
    simp only [Prod.mk.eta, csx_csx, Equiv.symm_apply_apply]
  right_inv y := by
    obtain ⟨⟨⟨h, u⟩, P, π, k, k'⟩, S₀, r, ρ, u₂, S⟩ := y
    simp only [Prod.mk.eta, csx_csx, Equiv.apply_symm_apply]

/-- **The table as Reparam's table and the rest**: SchemeSplit's staged swap (the chain starts
become uniform slots), then the chain-start exchange into the pad. -/
noncomputable def tabEquiv : TE ≃ RTab × Rest :=
  ((Equiv.prodAssoc HonestTable SeedSlots (ValPos → Digest)).symm.trans
    (schemeSplit.prodCongr (Equiv.refl _))).trans shufR

/-- **The reparametrization** (Masses' `e`): the table's Reparam table through `fwd` (public
coordinates and hidden values), with the rest public. -/
noncomputable def reparamE (t : TE) : PX × (ValPos → Digest) :=
  (((fwd xmssFix xO (tabEquiv t).1).1, (tabEquiv t).2), (fwd xmssFix xO (tabEquiv t).1).2)

/-- The template's public datum of the public data. -/
def pubX (p : PX) : Pub :=
  xPub p.1.2 p.1.1

variable {ι : Type} {β : ι → Type}

/-- **The good set** (Masses' `G`): SchemeSplit's good set for the computations `Q`, Reparam's
good set, and source goodness of the public data and hidden values. -/
def goodT (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (t : TE) : Prop :=
  (t.1, t.2.1) ∈ schemeGood Q ∧ XGood (tabEquiv t).1 ∧ SrcGood (pubX (reparamE t).1) (reparamE t).2

/-- The reparametrization is injective where Reparam's table is good. -/
theorem reparamE_injOn_xGood : Set.InjOn reparamE {t | XGood (tabEquiv t).1} := by
  intro t₁ h₁ t₂ h₂ he
  have hf : fwd xmssFix xO (tabEquiv t₁).1 = fwd xmssFix xO (tabEquiv t₂).1 :=
    Prod.ext (congrArg (fun y ↦ y.1.1) he) (congrArg (fun y ↦ y.2) he :)
  have hθ := injOn_fwd xO_consistent (good_of_xGood h₁) (good_of_xGood h₂) hf
  exact tabEquiv.injective (Prod.ext hθ (congrArg (fun y ↦ y.1.2) he))

/-- **`hinj`**: the reparametrization is injective on the good set. -/
theorem reparamE_injOn (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) :
    Set.InjOn reparamE {t | goodT Q t} :=
  reparamE_injOn_xGood.mono fun _ h ↦ h.2.1

/-- The rest is finite. -/
noncomputable instance instFintypeRest : Fintype Rest :=
  inferInstanceAs (Fintype (MasterSeed × (Fin 832 → ZMod 2) × (Fin 960 → ZMod 2) × (CsIdx → X) ×
    MasterSeed))

open scoped Classical in
/-- The public data are finite. -/
noncomputable instance instFintypePX : Fintype PX :=
  inferInstanceAs (Fintype (((Z → X) × XW) × Rest))

/-- The public data with the hidden values, as Reparam's table and the rest. -/
def pxEquiv : PX × (ValPos → Digest) ≃ RTab × Rest where
  toFun y := (((y.1.1.1, y.2), y.1.1.2), y.1.2)
  invFun x := (((x.1.1.1, x.1.2), x.2), x.1.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

open scoped Classical in
/-- The public data and hidden values are as many as the tables. -/
theorem card_px_eq : Fintype.card (PX × (ValPos → Digest)) = Fintype.card TE :=
  Fintype.card_congr (pxEquiv.trans tabEquiv.symm)

open scoped Classical in
/-- **`hcard`**. -/
theorem card_reparam_le :
    Fintype.card PX * Fintype.card (ValPos → Digest) ≤ Fintype.card TE :=
  (Fintype.card_prod _ _).symm.trans_le card_px_eq.le

end reparam

/-! ## The table's hidden cells are the template's at the public data (`hsub`) -/

section transfer

theorem inTable_of_mem_layerSlots {l : Layer} {e : KeyIndex} {w : Encoding} {s : Slot}
    (he : e.val < keyCount l) (hs : s ∈ layerSlots l e w) : InTable s := by
  simp only [layerSlots, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_cons,
    List.mem_range] at hs
  rcases hs with ⟨i, -, step, -, rfl⟩ | rfl | ⟨lev, hlev, rfl⟩
  · exact he
  · exact he
  · have hkb := le_keyBits l
    have hlev' : lev < 16 := hlev
    refine ⟨by omega, by simp only [layerHeight]; omega, ?_⟩
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.sub_add_cancel (by omega)]
    exact he

theorem isInput_mem_slotNeed {q : ValPos} {s : Slot} (h : IsInput q s) : q ∈ slotNeed s := by
  cases s with
  | chain l e step i =>
    subst h
    exact Finset.mem_insert_self _ _
  | leaf l e =>
    obtain ⟨i, rfl⟩ := h
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  | node l level index =>
    rcases h with rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  | _ => exact h.elim

/-- A port of a slot realized at `valueAt L` has the slot's cell at the honest values. -/
theorem realize_eq_of_input {L : HonestTable} {s : Slot} :
    ∀ q, IsInput q s →
      valuePos L q = extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L)) q :=
  fun _ hq ↦
    (extendVals_restrictTo (inl_mem_inlSet.mpr (isInput_mem_slotNeed hq)) (valueAt L)).symm

theorem mem_pathH {L : HonestTable} {z : Z} (hz : z ∈ pathH L) :
    ∃ s, InTable s ∧ ∃ j < nBlocks (pubOf L) s, srcCellH (pubOf L) s (valuePos L) j = z := by
  obtain ⟨a, l, e, w, s, he, hs, p, hp, hpc⟩ := hz
  simp only [slotPorts, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  obtain ⟨j, hj, rfl | rfl | rfl⟩ := hp
  · simp [LazyProg.realize] at hpc
  · simp [LazyProg.realize] at hpc
  · simp only [LazyProg.realize, HwProg.programH.injEq] at hpc
    exact ⟨s, inTable_of_mem_layerSlots he hs, j, hj,
      (cellH_congr _ realize_eq_of_input j).trans hpc.1⟩

theorem mem_pathK {L : HonestTable} {x : X} (hx : x ∈ pathK L) :
    ∃ s, InTable s ∧ ∃ j < nBlocks (pubOf L) s, srcCellK (pubOf L) s (valuePos L) j = x := by
  obtain ⟨a, l, e, w, s, he, hs, p, hp, hpc⟩ := hx
  simp only [slotPorts, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  obtain ⟨j, hj, rfl | rfl | rfl⟩ := hp
  · simp only [LazyProg.realize, HwProg.programK.injEq] at hpc
    exact ⟨s, inTable_of_mem_layerSlots he hs, j, hj,
      (cellK_congr _ realize_eq_of_input j).trans hpc.1⟩
  · simp [LazyProg.realize] at hpc
  · simp [LazyProg.realize] at hpc

theorem mem_pathK' {L : HonestTable} {x : X} (hx : x ∈ pathK' L) :
    ∃ s, InTable s ∧ ∃ j < nBlocks (pubOf L) s, srcCellK' (pubOf L) s (valuePos L) j = x := by
  obtain ⟨a, l, e, w, s, he, hs, p, hp, hpc⟩ := hx
  simp only [slotPorts, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  obtain ⟨j, hj, rfl | rfl | rfl⟩ := hp
  · simp [LazyProg.realize] at hpc
  · simp only [LazyProg.realize, HwProg.programK'.injEq] at hpc
    exact ⟨s, inTable_of_mem_layerSlots he hs, j, hj,
      (cellK'_congr _ realize_eq_of_input j).trans hpc.1⟩
  · simp [LazyProg.realize] at hpc

theorem inPos_slotOutPos {s : Slot} (hs : InTable s) : InPos (slotOutPos s) := by
  cases s with
  | chain l e step i =>
    have := step.isLt
    refine ⟨?_, hs⟩
    show 1 ≤ (step.val + 1) % chainLength
    simp only [chainLength_eq] at *
    omega
  | leaf l e =>
    show e.val % 2 ^ 32 < 2 ^ (keyBits l - 0 % (layerHeight + 1))
    have he : e.val < 2 ^ keyBits l := hs
    have := keyCount_le l
    simp only [keyCount] at this
    rw [Nat.zero_mod, Nat.sub_zero, Nat.mod_eq_of_lt (by omega)]
    exact he
  | node l level index =>
    obtain ⟨h1, h2, h3⟩ := hs
    have hb := node_bounds (l := l) (level := level) (index := index) ⟨h1, h2, h3⟩
    show index % 2 ^ 32 < 2 ^ (keyBits l - level % (layerHeight + 1))
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by simp only [layerHeight] at h2 ⊢; omega)]
    exact h3
  | _ => exact absurd hs id

theorem outSlot_slotOutPos {s : Slot} (hs : InTable s) : outSlot (slotOutPos s) = s := by
  cases s with
  | chain l e step i =>
    have := step.isLt
    show Slot.chain l e ⟨(step.val + 1) % chainLength - 1, _⟩ i = _
    congr 1
    exact Fin.ext (by simp only [chainLength_eq] at *; omega)
  | leaf l e =>
    show outSlot (.tree l ⟨0 % (layerHeight + 1), _⟩ ⟨e.val % 2 ^ 32, _⟩) = _
    rw [show outSlot (.tree l ⟨0 % (layerHeight + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
        ⟨e.val % 2 ^ 32, Nat.mod_lt _ (Nat.two_pow_pos 32)⟩) =
        .leaf l (leafKey (e.val % 2 ^ 32)) from ite_eq_left (Nat.zero_mod _)]
    congr 1
    exact Fin.ext (by
      show e.val % 2 ^ 32 % lifetime = e.val
      have := e.isLt
      simp only [lifetime, layerCount, layerHeight] at *
      omega)
  | node l level index =>
    obtain ⟨h1, h2, h3⟩ := hs
    have hb := node_bounds (l := l) (level := level) (index := index) ⟨h1, h2, h3⟩
    have hl : level % (layerHeight + 1) = level := Nat.mod_eq_of_lt (by
      simp only [layerHeight] at h2 ⊢; omega)
    have hl0 : level % (layerHeight + 1) ≠ 0 := by omega
    show outSlot (.tree l ⟨level % (layerHeight + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
      ⟨index % 2 ^ 32, Nat.mod_lt _ (Nat.two_pow_pos 32)⟩) = _
    rw [show outSlot (.tree l ⟨level % (layerHeight + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
        ⟨index % 2 ^ 32, Nat.mod_lt _ (Nat.two_pow_pos 32)⟩) =
        .node l (level % (layerHeight + 1)) (index % 2 ^ 32) from ite_eq_right hl0, hl,
      Nat.mod_eq_of_lt (show index < 2 ^ 32 by omega)]
  | _ => exact absurd hs id

theorem inTable_outSlot {p : ValPos} (hp : InPos p) : InTable (outSlot p) := by
  cases p with
  | chain l e i j => exact hp.2
  | tree l level index =>
    have hp' : index.val < 2 ^ (keyBits l - level.val) := hp
    by_cases hl : level.val = 0
    · rw [show outSlot (.tree l level index) = .leaf l (leafKey index.val) from ite_eq_left hl]
      rw [hl, Nat.sub_zero] at hp'
      show (leafKey index.val).val < keyCount l
      rw [leafKey_val_of_lt hp']
      exact hp'
    · rw [show outSlot (.tree l level index) = .node l level.val index.val from ite_eq_right hl]
      have := level.isLt
      exact ⟨by omega, by omega, hp'⟩

/-- An input of an in-table slot is in the table, or a chain start. -/
theorem inPos_or_start {s : Slot} (hs : InTable s) {q : ValPos} (hq : IsInput q s) :
    InPos q ∨ ∃ l e i, q = .chain l e i ⟨0, by decide⟩ := by
  cases s with
  | chain l e step i =>
    subst hq
    have := step.isLt
    by_cases h0 : step.val = 0
    · refine Or.inr ⟨l, e, i, ?_⟩
      simp only [cpos, h0, ValPos.chain.injEq, true_and]
      exact Fin.ext (Nat.zero_mod _)
    · refine Or.inl ⟨?_, hs⟩
      show 1 ≤ step.val % chainLength
      simp only [chainLength_eq] at *
      omega
  | leaf l e =>
    obtain ⟨i, rfl⟩ := hq
    exact Or.inl ⟨by decide, hs⟩
  | node l level index =>
    obtain ⟨h1, h2, h3⟩ := hs
    have hb := node_bounds (l := l) (level := level) (index := index) ⟨h1, h2, h3⟩
    have hkb := le_keyBits l
    simp only [layerHeight] at h2 hb
    have hpow : 2 ^ (keyBits l - (level - 1)) = 2 * 2 ^ (keyBits l - level) := by
      rw [show keyBits l - (level - 1) = keyBits l - level + 1 by omega, pow_succ, mul_comm]
    have hl : (level - 1) % (layerHeight + 1) = level - 1 := Nat.mod_eq_of_lt (by
      simp only [layerHeight]; omega)
    refine Or.inl ?_
    rcases hq with rfl | rfl
    · show 2 * index % 2 ^ 32 < 2 ^ (keyBits l - (level - 1) % (layerHeight + 1))
      rw [hl, hpow, Nat.mod_eq_of_lt (by omega)]
      omega
    · show (2 * index + 1) % 2 ^ 32 < 2 ^ (keyBits l - (level - 1) % (layerHeight + 1))
      rw [hl, hpow, Nat.mod_eq_of_lt (by omega)]
      omega
  | _ => exact absurd hs id

theorem cellH_pubOf (L : HonestTable) : srcCellH (pubOf L) = srcCellH (xPub (wOf L) L.keys.1) :=
  rfl

theorem cellK_pubOf (L : HonestTable) : srcCellK (pubOf L) = srcCellK (xPub (wOf L) L.keys.1) :=
  rfl

theorem cellK'_pubOf (L : HonestTable) : srcCellK' (pubOf L) = srcCellK' (xPub (wOf L) L.keys.1) :=
  rfl

/-- The block count reads the public parameter only. -/
theorem nBlocks_eq_of_param {pub pub' : Pub} (h : pub.param = pub'.param) :
    nBlocks pub = nBlocks pub' := by
  funext s
  unfold nBlocks slotInput
  rw [h]

/-- **Changing `h` off the honest paths keeps the table's values** (by rank). -/
theorem xVal_congr_h {w : XW} {h h₂ : Z → X} {u : ValPos → Digest}
    (hh : ∀ p, InPos p → ∀ i < nBlocks (xPub w h) (outSlot p),
      h₂ (srcCellH (xPub w h) (outSlot p) (xVal w h u) i) =
        h (srcCellH (xPub w h) (outSlot p) (xVal w h u) i)) :
    ∀ p, InPos p → xVal w h₂ u p = xVal w h u p := by
  suffices H : ∀ n p, xRank p = n → InPos p → xVal w h₂ u p = xVal w h u p from
    fun p hp ↦ H _ p rfl hp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hn hp
  have hlow : ∀ t, xRank t < xRank p → xVal w h₂ u t = xVal w h u t := fun t ht ↦ by
    by_cases htp : InPos t
    · exact ih _ (hn ▸ ht) t rfl htp
    · rw [xVal, xVal, ite_eq_right htp, ite_eq_right htp]
  have hx : ∀ h₀, xVal w h₀ u p = xDig w h₀ (slotInput (xPub w h₀) (outSlot p) (xVal w h₀ u)) :=
    fun h₀ ↦ by rw [show xVal w h₀ u p = recVal w h₀ u p from ite_eq_left hp, recVal_eq_xDig w h₀ u hp]
  have hh' : ∀ i, i + 1 < nBlocks (xPub w h) (outSlot p) →
      h₂ (roundH (xPub w h) (outSlot p) (xVal w h u) i).1 =
        h (roundH (xPub w h) (outSlot p) (xVal w h u) i).1 :=
    fun i hi ↦ hh p hp i (by omega)
  have hlast : h₂ (outCap (xPub w h) (outSlot p) (xVal w h u)) =
      h (outCap (xPub w h) (outSlot p) (xVal w h u)) := by
    have e : (roundH (xPub w h) (outSlot p) (xVal w h u) (nBlocks (xPub w h) (outSlot p) - 1)).1 =
        outCap (xPub w h) (outSlot p) (xVal w h u) :=
      congrArg Prod.fst (roundH_last (xPub w h) (outSlot p) (xVal w h u))
    rw [← e]
    exact hh p hp _ (by have := nBlocks_pos (xPub w h) (outSlot p); omega)
  rw [hx h₂, hx h, slotInput_xPub w h h₂, slotInput_congr (xPub w h) hp hlow]
  have e₂ := trunc128_spongeHash_slotInput (xPub w h₂) (outSlot p) (xVal w h u)
  have e₁ := trunc128_spongeHash_slotInput (xPub w h) (outSlot p) (xVal w h u)
  rw [slotInput_xPub w h h₂] at e₂
  change trunc128 (spongeHash (spongePerm (xPub w h₂).keys (xPub w h₂).perm)
      (blocks (slotInput (xPub w h) (outSlot p) (xVal w h u)))) =
    trunc128 (spongeHash (spongePerm (xPub w h).keys (xPub w h).perm)
      (blocks (slotInput (xPub w h) (outSlot p) (xVal w h u))))
  rw [e₂, e₁, outRate_xPub_congr hh', outCap_xPub_congr hh']
  exact congrArg _ hlast

/-- **The template's cells at Reparam's public data are the table's own** (`rounds_fwd`, for an
in-table slot). -/
theorem cells_fwd {h : Z → X} {u : ValPos → Digest} {w : XW} (hθ : XGood ((h, u), w)) {s : Slot}
    (hs : InTable s) {j : ℕ} (hj : j < nBlocks (xPub w h) s) :
    srcCellK (xPub w (fwd xmssFix xO ((h, u), w)).1.1) s (xVal w h u) j =
        srcCellK (xPub w h) s (xVal w h u) j ∧
      srcCellK' (xPub w (fwd xmssFix xO ((h, u), w)).1.1) s (xVal w h u) j =
        srcCellK' (xPub w h) s (xVal w h u) j ∧
      srcCellH (xPub w (fwd xmssFix xO ((h, u), w)).1.1) s (xVal w h u) j =
        srcCellH (xPub w h) s (xVal w h u) j := by
  have hj' : j < nBlocks (xPub w h) (outSlot (slotOutPos s)) := by
    rwa [outSlot_slotOutPos hs]
  obtain ⟨e1, e2, e3⟩ := rounds_fwd hθ (mem_xI.mpr (inPos_slotOutPos hs)) hj'
  rw [outSlot_slotOutPos hs] at e1 e2 e3
  exact ⟨congrArg Prod.fst e1, congrArg Prod.fst e2, congrArg Prod.fst e3⟩

/-- **The transfer, over the table's coordinates**: for Reparam's table `((h, u), wOf L)` whose
`h` agrees with `L`'s on the honest paths and whose pad carries `L`'s chain starts, the honest
paths' cells of `L` are the template's cells at the public data and the hidden values. -/
theorem cells_transfer (L : HonestTable) {h : Z → X} {u : ValPos → Digest}
    (hθ : XGood ((h, u), wOf L))
    (hu : ∀ l e i, u (.chain l e i ⟨0, by decide⟩) = L.chainStart l e i)
    (hav : ∀ s, InTable s → ∀ j < nBlocks (pubOf L) s,
      h (srcCellH (pubOf L) s (valuePos L) j) = L.keys.1 (srcCellH (pubOf L) s (valuePos L) j))
    {s : Slot} (hs : InTable s) {j : ℕ} (hj : j < nBlocks (pubOf L) s) :
    srcCellK (xPub (wOf L) (fwd xmssFix xO ((h, u), wOf L)).1.1) s (xVal (wOf L) h u) j =
        srcCellK (pubOf L) s (valuePos L) j ∧
      srcCellK' (xPub (wOf L) (fwd xmssFix xO ((h, u), wOf L)).1.1) s (xVal (wOf L) h u) j =
        srcCellK' (pubOf L) s (valuePos L) j ∧
      srcCellH (xPub (wOf L) (fwd xmssFix xO ((h, u), wOf L)).1.1) s (xVal (wOf L) h u) j =
        srcCellH (pubOf L) s (valuePos L) j := by
  set Lk := L.keys.1
  have hstart : ∀ q, ¬InPos q → ∀ s, InTable s → IsInput q s → ∀ h₀,
      xVal (wOf L) h₀ u q = valuePos L q := fun q hq s hs hin h₀ ↦ by
    rcases inPos_or_start hs hin with hp | ⟨l, e, i, rfl⟩
    · exact absurd hp hq
    · rw [xVal, ite_eq_right hq, hu]
      rfl
  have hLk : ∀ s, InTable s → ∀ q, IsInput q s → xVal (wOf L) Lk u q = valuePos L q :=
    fun s hs q hin ↦ by
      by_cases hq : InPos q
      · exact xVal_wOf L u (fun l e i _ ↦ hu l e i) hq
      · exact hstart q hq s hs hin Lk
  have hh : ∀ s, InTable s → ∀ i < nBlocks (xPub (wOf L) Lk) s,
      h (srcCellH (xPub (wOf L) Lk) s (xVal (wOf L) Lk u) i) =
        Lk (srcCellH (xPub (wOf L) Lk) s (xVal (wOf L) Lk u) i) := fun s hs i hi ↦ by
    rw [cellH_congr _ (hLk s hs) i]
    exact hav s hs i hi
  have hx : ∀ p, InPos p → xVal (wOf L) h u p = xVal (wOf L) Lk u p :=
    xVal_congr_h fun p hp i hi ↦ hh _ (inTable_outSlot hp) i hi
  have hvals : ∀ q, IsInput q s → xVal (wOf L) h u q = valuePos L q := fun q hin ↦ by
    by_cases hq : InPos q
    · rw [hx q hq]
      exact hLk s hs q hin
    · exact hstart q hq s hs hin h
  have hh' : ∀ i < j, h (roundH (xPub (wOf L) Lk) s (valuePos L) i).1 =
      Lk (roundH (xPub (wOf L) Lk) s (valuePos L) i).1 :=
    fun i hi ↦ hav s hs i (by omega)
  have hj' : j < nBlocks (xPub (wOf L) Lk) s := hj
  obtain ⟨e1, e2, e3⟩ := cells_fwd hθ hs (by rwa [nBlocks_xPub (wOf L) Lk h])
  rw [e1, e2, e3, cellK_congr _ hvals, cellK'_congr _ hvals, cellH_congr _ hvals, cellK_pubOf,
    cellK'_pubOf, cellH_pubOf]
  refine ⟨congrArg Prod.fst (roundK_xPub_congr hj'.le hh'),
    congrArg Prod.fst (roundK'_xPub_congr hj'.le hh'), roundH_fst_xPub_congr hj' hh'⟩

variable {ι : Type} {β : ι → Type}

/-- **The computations `Q` read the honest paths' `h`-cells**: every `h`-cell of an in-table
slot's honest path is read by some `Q i` evaluated honestly at the table. -/
def CoversPaths (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) :
    Prop :=
  ∀ L : HonestTable, ∀ s, InTable s → ∀ j < nBlocks (pubOf L) s,
    ∃ i, srcCellH (pubOf L) s (valuePos L) j ∈ hCells (schemeData Q L i).2

theorem tabEquiv_fst (t : TE) : (tabEquiv t).1 =
    (((schemeSplit (t.1, t.2.1)).1.1.keys.1,
        csxU (schemeSplit (t.1, t.2.1)).1.2.2.2 t.2.2),
      ((paramEquiv (schemeSplit (t.1, t.2.1)).1.2.2.1).1, (schemeSplit (t.1, t.2.1)).1.1.perm,
        (schemeSplit (t.1, t.2.1)).1.1.keys.2.1, (schemeSplit (t.1, t.2.1)).1.1.keys.2.2)) :=
  rfl

theorem nBlocks_xPub_wOf (L : HonestTable) (h : Z → X) :
    nBlocks (xPub (wOf L) h) = nBlocks (pubOf L) :=
  nBlocks_eq_of_param rfl

/-- `hsub` for the `h`-cells, over Reparam's table `((h, u), wOf L)` of the table `L`. -/
theorem hsubH_core (L : HonestTable) {h : Z → X} {u : ValPos → Digest}
    (hθ : XGood ((h, u), wOf L))
    (hu : ∀ l e i, u (.chain l e i ⟨0, by decide⟩) = L.chainStart l e i)
    (hav : ∀ s, InTable s → ∀ j < nBlocks (pubOf L) s,
      h (srcCellH (pubOf L) s (valuePos L) j) = L.keys.1 (srcCellH (pubOf L) s (valuePos L) j))
    (hgood : SrcGood (xPub (wOf L) (fwd xmssFix xO ((h, u), wOf L)).1.1) (xVal (wOf L) h u)) :
    pathH L ⊆ hidH (xPub (wOf L) (fwd xmssFix xO ((h, u), wOf L)).1.1) (xVal (wOf L) h u) := by
  intro z hz
  obtain ⟨s, hs, j, hj, rfl⟩ := mem_pathH hz
  refine ⟨hgood, s, hs, j, ?_, (cells_transfer L hθ hu hav hs hj).2.2⟩
  rw [nBlocks_xPub_wOf]
  exact hj

/-- `hsub` for the `k`-cells. -/
theorem hsubK_core (L : HonestTable) {h : Z → X} {u : ValPos → Digest}
    (hθ : XGood ((h, u), wOf L))
    (hu : ∀ l e i, u (.chain l e i ⟨0, by decide⟩) = L.chainStart l e i)
    (hav : ∀ s, InTable s → ∀ j < nBlocks (pubOf L) s,
      h (srcCellH (pubOf L) s (valuePos L) j) = L.keys.1 (srcCellH (pubOf L) s (valuePos L) j))
    (hgood : SrcGood (xPub (wOf L) (fwd xmssFix xO ((h, u), wOf L)).1.1) (xVal (wOf L) h u)) :
    pathK L ⊆ hidK (xPub (wOf L) (fwd xmssFix xO ((h, u), wOf L)).1.1) (xVal (wOf L) h u) := by
  intro x hx
  obtain ⟨s, hs, j, hj, rfl⟩ := mem_pathK hx
  refine ⟨hgood, s, hs, j, ?_, (cells_transfer L hθ hu hav hs hj).1⟩
  rw [nBlocks_xPub_wOf]
  exact hj

/-- `hsub` for the `k'`-cells. -/
theorem hsubK'_core (L : HonestTable) {h : Z → X} {u : ValPos → Digest}
    (hθ : XGood ((h, u), wOf L))
    (hu : ∀ l e i, u (.chain l e i ⟨0, by decide⟩) = L.chainStart l e i)
    (hav : ∀ s, InTable s → ∀ j < nBlocks (pubOf L) s,
      h (srcCellH (pubOf L) s (valuePos L) j) = L.keys.1 (srcCellH (pubOf L) s (valuePos L) j))
    (hgood : SrcGood (xPub (wOf L) (fwd xmssFix xO ((h, u), wOf L)).1.1) (xVal (wOf L) h u)) :
    pathK' L ⊆ hidK' (xPub (wOf L) (fwd xmssFix xO ((h, u), wOf L)).1.1) (xVal (wOf L) h u) := by
  intro x hx
  obtain ⟨s, hs, j, hj, rfl⟩ := mem_pathK' hx
  refine ⟨hgood, s, hs, j, ?_, (cells_transfer L hθ hu hav hs hj).2.1⟩
  rw [nBlocks_xPub_wOf]
  exact hj

/-- `hsub` over Reparam's table `θ` of the table `L`. -/
theorem hsub_core (L : HonestTable) (θ : RTab) (hθ : XGood θ) (hw : θ.2 = wOf L)
    (hu : ∀ l e i, θ.1.2 (.chain l e i ⟨0, by decide⟩) = L.chainStart l e i)
    (hav : ∀ s, InTable s → ∀ j < nBlocks (pubOf L) s,
      θ.1.1 (srcCellH (pubOf L) s (valuePos L) j) = L.keys.1 (srcCellH (pubOf L) s (valuePos L) j))
    (hgood : SrcGood (xPub θ.2 (fwd xmssFix xO θ).1.1) (xVal θ.2 θ.1.1 θ.1.2)) :
    pathH L ⊆ hidH (xPub θ.2 (fwd xmssFix xO θ).1.1) (xVal θ.2 θ.1.1 θ.1.2) ∧
      pathK L ⊆ hidK (xPub θ.2 (fwd xmssFix xO θ).1.1) (xVal θ.2 θ.1.1 θ.1.2) ∧
      pathK' L ⊆ hidK' (xPub θ.2 (fwd xmssFix xO θ).1.1) (xVal θ.2 θ.1.1 θ.1.2) := by
  obtain ⟨⟨h, u⟩, w⟩ := θ
  obtain rfl : w = wOf L := hw
  exact ⟨hsubH_core L hθ hu hav hgood, hsubK_core L hθ hu hav hgood,
    hsubK'_core L hθ hu hav hgood⟩

theorem tab_w {t : TE} (hinj : Function.Injective
      (posOf (schemeSplit (t.1, t.2.1)).1 (schemeSplit (t.1, t.2.1)).2)) :
    (tabEquiv t).1.2 = wOf t.1 := by
  obtain ⟨hP, -, -⟩ := schemeSplit_transfer (t.1, t.2.1) hinj
  rw [tabEquiv_fst]
  exact Prod.ext ((paramEquiv_fst _).trans hP) (Prod.ext (schemeSplit_perm _)
    (Prod.ext (congrArg Prod.fst (schemeSplit_keys_snd _))
      (congrArg Prod.snd (schemeSplit_keys_snd _))))

theorem tab_u {t : TE} (hinj : Function.Injective
      (posOf (schemeSplit (t.1, t.2.1)).1 (schemeSplit (t.1, t.2.1)).2)) (l : Layer)
    (e : KeyIndex) (i : ChainIndex) :
    (tabEquiv t).1.1.2 (.chain l e i ⟨0, by decide⟩) = t.1.chainStart l e i := by
  obtain ⟨-, hC, -⟩ := schemeSplit_transfer (t.1, t.2.1) hinj
  rw [tabEquiv_fst, chainStart_eq_csHash, ← congrFun hC]
  show csxU (schemeSplit (t.1, t.2.1)).1.2.2.2 t.2.2 (.chain l e i ⟨0, by decide⟩) = _
  exact ite_eq_left rfl

theorem tab_avoid {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)}
    (hQ : CoversPaths Q) {t : TE} (hsg : (t.1, t.2.1) ∈ schemeGood Q) (s : Slot) (hs : InTable s)
    (j : ℕ) (hj : j < nBlocks (pubOf t.1) s) :
    (tabEquiv t).1.1.1 (srcCellH (pubOf t.1) s (valuePos t.1) j) =
      t.1.keys.1 (srcCellH (pubOf t.1) s (valuePos t.1) j) := by
  obtain ⟨hinj, hread⟩ := mem_schemeGood.mp hsg
  obtain ⟨-, -, hh⟩ := schemeSplit_transfer (t.1, t.2.1) hinj
  obtain ⟨i, hi⟩ := hQ t.1 s hs j hj
  rw [schemeData_eq_of_mem hsg] at hi
  rw [tabEquiv_fst]
  exact hh _ fun a ha ↦ hread i a (ha ▸ hi)

theorem pubX_reparamE (t : TE) :
    pubX (reparamE t).1 = xPub (tabEquiv t).1.2 (fwd xmssFix xO (tabEquiv t).1).1.1 := by
  show xPub (fwd xmssFix xO (tabEquiv t).1).1.2 (fwd xmssFix xO (tabEquiv t).1).1.1 = _
  rw [fwd_fst_snd]

theorem snd_reparamE (t : TE) :
    (reparamE t).2 = xVal (tabEquiv t).1.2 (tabEquiv t).1.1.1 (tabEquiv t).1.1.2 :=
  fwd_snd xmssFix xO (tabEquiv t).1

/-- **`hsub`**: on the good set, the table's hidden cells (Masses' `pathH`, `pathK`, `pathK'`)
lie in the hidden sets of the public data and hidden values. -/
theorem hsub_reparam {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)}
    (hQ : CoversPaths Q) (t : TE) (ht : goodT Q t) :
    pathH t.1 ⊆ hidH (pubX (reparamE t).1) (reparamE t).2 ∧
      pathK t.1 ⊆ hidK (pubX (reparamE t).1) (reparamE t).2 ∧
      pathK' t.1 ⊆ hidK' (pubX (reparamE t).1) (reparamE t).2 := by
  obtain ⟨hsg, hθ, hgood⟩ := ht
  have hinj := (mem_schemeGood.mp hsg).1
  rw [pubX_reparamE, snd_reparamE] at hgood ⊢
  exact hsub_core t.1 (tabEquiv t).1 hθ (tab_w hinj) (tab_u hinj) (tab_avoid hQ hsg) hgood

end transfer

/-! ## The computations reading the honest paths (`CoversPaths`) -/

section pathComp

/-- One hash query. -/
def hashQ (input : HashInput) : OracleComp HashSpec HashOutput :=
  liftM (HashSpec.query input)

/-- Position `j` of chain `i` of key `e` of layer `l` by hash queries, from the parameter `P` and the
chain starts' hashes `Cs` (as `HonestTable.chainValue`). -/
def chainM (P : PublicParameter) (Cs : CsIdx → HashOutput) (l : Layer) (e : KeyIndex)
    (i : ChainIndex) : ℕ → OracleComp HashSpec Digest
  | 0 => pure (hashHalfForChain i.val (Cs (l, e, chainPair i)))
  | j + 1 => if hj : j < chainLength - 1 then
      chainM P Cs l e i j >>= fun d ↦
        hashQ (thInput P (hashDomainFields (.chain l e ⟨j, hj⟩)) (Verification.chainPayload i d)) >>=
          fun o ↦ pure (truncateHash o)
    else pure 0

/-- The tree value of layer `l` at `level`, index `index`, by hash queries (as
`HonestTable.treeValue`). -/
def treeM (P : PublicParameter) (Cs : CsIdx → HashOutput) (l : Layer) :
    ℕ → ℕ → OracleComp HashSpec Digest
  | 0, index =>
      sequenceFin (fun i : ChainIndex ↦ chainM P Cs l (leafKey index) i (chainLength - 1)) >>=
        fun ends ↦ hashQ (thInput P (hashDomainFields (.leaf l (leafKey index)))
          (digestsPayload ends)) >>= fun o ↦ pure (truncateHash o)
  | level + 1, index =>
      treeM P Cs l level (2 * index) >>= fun a ↦ treeM P Cs l level (2 * index + 1) >>= fun b ↦
        hashQ (thInput P (hashDomainFields (.node l (level + 1) index)) (nodePayload a b)) >>=
          fun o ↦ pure (truncateHash o)

/-- **The computation of a position's value** (SchemeSplit's `Q`, indexed by the positions): its
last query is the input of the position's slot. -/
def posM (p : ValPos) (P : PublicParameter) (Cs : CsIdx → HashOutput) :
    OracleComp HashSpec Digest :=
  match p with
  | .chain l e i j => chainM P Cs l e i j.val
  | .tree l level index => treeM P Cs l level.val index.val

variable (L : HonestTable)

theorem eval_chainM (l : Layer) (e : KeyIndex) (i : ChainIndex) : ∀ j,
    evalWithAnswerFn (spongeOut (spongePerm L.keys L.perm)) (chainM L.param (csHash L) l e i j) =
      L.chainValue l e i j
  | 0 => (chainStart_eq_csHash L l e i).symm
  | j + 1 => by
    by_cases hj : j < chainLength - 1
    · simp only [chainM, hj, ↓reduceDIte, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
        eval_chainM l e i j]
      exact (L.chainValue_succ l e i ⟨j, hj⟩).symm
    · simp only [chainM, hj, ↓reduceDIte, evalWithAnswerFn_pure, HonestTable.chainValue]

theorem eval_treeM (l : Layer) : ∀ level index,
    evalWithAnswerFn (spongeOut (spongePerm L.keys L.perm)) (treeM L.param (csHash L) l level index) =
      L.treeValue l level index
  | 0, index => by
    simp only [treeM, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, evalWithAnswerFn_pure,
      eval_chainM]
    rfl
  | level + 1, index => by
    simp only [treeM, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_treeM l level]
    exact (L.treeValue_succ l level index).symm

section queries

variable {α β : Type} (f : QueryImpl HashSpec Id)

theorem mem_queries_bind_right (x : OracleComp HashSpec α) (k : α → OracleComp HashSpec β)
    {q : HashInput} (h : q ∈ queries f (k (evalWithAnswerFn f x))) : q ∈ queries f (x >>= k) := by
  rw [queries, trace_bind]
  exact List.mem_append_right _ h

theorem mem_queries_hashQ_bind (input : HashInput) (k : HashOutput → OracleComp HashSpec β) :
    input ∈ queries f (hashQ input >>= k) := by
  rw [queries, hashQ, trace_query_bind]
  exact List.mem_append_left _ (List.mem_singleton_self _)

theorem length_queries_bind (x : OracleComp HashSpec α) (k : α → OracleComp HashSpec β) :
    (queries f (x >>= k)).length =
      (queries f x).length + (queries f (k (evalWithAnswerFn f x))).length := by
  rw [queries, trace_bind, List.length_append]
  rfl

theorem length_queries_hashQ_pure (input : HashInput) (g : HashOutput → β) :
    (queries f (hashQ input >>= fun o ↦ pure (g o))).length = 1 := by
  rw [queries, hashQ, trace_query_bind]
  rfl

theorem queriesSatisfy_hashQ_pure {P : HashInput → Prop} {input : HashInput} (h : P input)
    (g : HashOutput → β) : QueriesSatisfy f P (hashQ input >>= fun o ↦ pure (g o)) := by
  intro q hq
  rw [queries, hashQ, trace_query_bind] at hq
  rcases List.mem_append.mp hq with hq | hq
  · exact (List.mem_singleton.mp hq) ▸ h
  · exact absurd hq List.not_mem_nil

theorem length_queries_sequenceFin {B : ℕ} : ∀ {n : ℕ} {c : Fin n → OracleComp HashSpec α},
    (∀ i, (queries f (c i)).length ≤ B) → (queries f (sequenceFin c)).length ≤ n * B
  | 0, _, _ => by simp [sequenceFin, queries, trace_pure]
  | n + 1, c, h => by
    simp only [sequenceFin]
    rw [length_queries_bind, length_queries_bind]
    have h1 := h 0
    have h2 := length_queries_sequenceFin (n := n) (c := fun i ↦ c i.succ) fun i ↦ h i.succ
    have h3 : (queries f (pure (Fin.cases (evalWithAnswerFn f (c 0))
        (evalWithAnswerFn f (sequenceFin fun i : Fin n ↦ c i.succ))) :
          OracleComp HashSpec (Fin (n + 1) → α))).length = 0 := rfl
    rw [h3]
    nlinarith

end queries

variable (f : QueryImpl HashSpec Id)

theorem length_queries_chainM (P : PublicParameter) (Cs : CsIdx → HashOutput) (l : Layer)
    (e : KeyIndex) (i : ChainIndex) : ∀ j, (queries f (chainM P Cs l e i j)).length ≤ j
  | 0 => le_of_eq rfl
  | j + 1 => by
    by_cases hj : j < chainLength - 1
    · simp only [chainM, hj, ↓reduceDIte]
      rw [length_queries_bind, length_queries_hashQ_pure]
      have := length_queries_chainM P Cs l e i j
      omega
    · simp only [chainM, hj, ↓reduceDIte]
      exact Nat.zero_le _

theorem length_queries_treeM (P : PublicParameter) (Cs : CsIdx → HashOutput) (l : Layer) :
    ∀ level index, (queries f (treeM P Cs l level index)).length + 1 ≤ 176 * 2 ^ level
  | 0, index => by
    simp only [treeM]
    rw [length_queries_bind, length_queries_hashQ_pure]
    have := length_queries_sequenceFin f (B := chainLength - 1)
      (c := fun i : ChainIndex ↦ chainM P Cs l (leafKey index) i (chainLength - 1))
      fun i ↦ length_queries_chainM f P Cs l (leafKey index) i _
    simp only [chainCount, chainLength, winternitzBits] at this ⊢
    omega
  | level + 1, index => by
    simp only [treeM]
    rw [length_queries_bind, length_queries_bind, length_queries_hashQ_pure]
    have h1 := length_queries_treeM P Cs l level (2 * index)
    have h2 := length_queries_treeM P Cs l level (2 * index + 1)
    rw [pow_succ]
    omega

theorem length_queries_posM (p : ValPos) (P : PublicParameter) (Cs : CsIdx → HashOutput) :
    (queries f (posM p P Cs)).length ≤ 176 * 2 ^ 16 := by
  cases p with
  | chain l e i j =>
    have := length_queries_chainM f P Cs l e i j.val
    have := j.isLt
    simp only [chainLength, winternitzBits] at *
    show (queries f (chainM P Cs l e i j.val)).length ≤ _
    omega
  | tree l level index =>
    have h := length_queries_treeM f P Cs l level.val index.val
    have hl : 2 ^ level.val ≤ 2 ^ 16 :=
      Nat.pow_le_pow_right (by norm_num) (by have := level.isLt; simp only [layerHeight] at this; omega)
    show (queries f (treeM P Cs l level.val index.val)).length ≤ _
    nlinarith

/-- Every hash input of the computations has at most `8` blocks. -/
theorem queriesSatisfy_chainM (P : PublicParameter) (Cs : CsIdx → HashOutput) (l : Layer)
    (e : KeyIndex) (i : ChainIndex) :
    ∀ j, QueriesSatisfy f (fun q ↦ (blocks q).length ≤ 8) (chainM P Cs l e i j)
  | 0 => queriesSatisfy_pure _
  | j + 1 => by
    by_cases hj : j < chainLength - 1
    · simp only [chainM, hj, ↓reduceDIte]
      refine queriesSatisfy_bind (queriesSatisfy_chainM P Cs l e i j)
        (queriesSatisfy_hashQ_pure f ?_ _)
      rw [length_blocks, length_thInput]
      simp only [Verification.chainPayload, List.length_append, length_le16,
        length_littleEndianBytes]
      norm_num
    · simp only [chainM, hj, ↓reduceDIte]
      exact queriesSatisfy_pure _

theorem queriesSatisfy_treeM (P : PublicParameter) (Cs : CsIdx → HashOutput) (l : Layer) :
    ∀ level index, QueriesSatisfy f (fun q ↦ (blocks q).length ≤ 8) (treeM P Cs l level index)
  | 0, index => by
    simp only [treeM]
    refine queriesSatisfy_bind (queriesSatisfy_sequenceFin fun i ↦ queriesSatisfy_chainM f P Cs l
      _ i _) (queriesSatisfy_hashQ_pure f ?_ _)
    rw [length_blocks, length_thInput, length_digestsPayload]
    simp only [chainCount]
    norm_num
  | level + 1, index => by
    simp only [treeM]
    refine queriesSatisfy_bind (queriesSatisfy_treeM P Cs l level _)
      (queriesSatisfy_bind (queriesSatisfy_treeM P Cs l level _) (queriesSatisfy_hashQ_pure f ?_ _))
    rw [length_blocks, length_thInput]
    simp only [nodePayload, List.length_append, length_le16]
    norm_num

theorem length_flatMap_le {γ δ : Type} (g : γ → List δ) (c : ℕ) :
    ∀ l : List γ, (∀ a ∈ l, (g a).length ≤ c) → (l.flatMap g).length ≤ c * l.length
  | [], _ => by simp
  | a :: l, h => by
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a List.mem_cons_self
    have h2 := length_flatMap_le g c l fun b hb ↦ h b (List.mem_cons_of_mem _ hb)
    nlinarith

/-- **The reads of a position's computation**: at most `24 · 176 · 2^16` (at most `176 · 2^16`
queries of at most `8` blocks, `3` reads per block). -/
theorem length_honestEval_posM (p : ValPos) (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z))
    (P : PublicParameter) (Cs : CsIdx → HashOutput) :
    (honestEval t π (posM p P Cs)).2.length ≤ 24 * (176 * 2 ^ 16) := by
  rw [snd_honestEval]
  have hsat : QueriesSatisfy (spongeOut (spongePerm t π)) (fun q ↦ (blocks q).length ≤ 8)
      (posM p P Cs) := by
    cases p with
    | chain l e i j => exact queriesSatisfy_chainM _ P Cs l e i j.val
    | tree l level index => exact queriesSatisfy_treeM _ P Cs l level.val index.val
  refine (length_flatMap_le _ 24 _ fun q hq ↦ ?_).trans
    (Nat.mul_le_mul_left 24 (length_queries_posM _ p P Cs))
  rw [inputReads, length_spongeReads]
  have := hsat q hq
  omega

/-- The reads of a list of blocks include every round's. -/
theorem spongeReads_prefix (π : Equiv.Perm (X × Z)) (h : Z → X) (k k' : X → Z) (a : List X) :
    ∀ b, spongeReads π h k k' a <+: spongeReads π h k k' (a ++ b) := by
  intro b
  induction b using List.reverseRecOn with
  | nil => rw [List.append_nil]
  | append_singleton b x ih =>
    rw [← List.append_assoc, spongeReads_append_singleton]
    exact ih.trans (List.prefix_append _ _)

theorem roundReads_subset_spongeReads (π : Equiv.Perm (X × Z)) (h : Z → X) (k k' : X → Z)
    (msg : List X) {j : ℕ} (hj : j < msg.length) :
    ∀ e ∈ roundReads π h k k' (absorb (spongePerm (h, k, k') π) (msg.take j)) (msg.getD j 0),
      e ∈ spongeReads π h k k' msg := by
  intro e he
  have hpre := spongeReads_prefix π h k k' (msg.take (j + 1)) (msg.drop (j + 1))
  rw [List.take_append_drop] at hpre
  refine hpre.subset ?_
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
    spongeReads_append_singleton]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at he
  exact List.mem_append_right _ he

/-- **A slot's `h`-cells are read when its input is hashed.** -/
theorem cellH_mem_hCells_inputReads (s : Slot) (v : ValPos → Digest) {j : ℕ}
    (hj : j < nBlocks (pubOf L) s) :
    srcCellH (pubOf L) s v j ∈ hCells (inputReads L.keys L.perm (slotInput (pubOf L) s v)) := by
  have hj' : j < (blocks (slotInput (pubOf L) s v)).length := by
    rwa [length_blocks_slotInput]
  rw [mem_hCells, srcCellH, roundH_fst]
  exact ⟨_, roundReads_subset_spongeReads L.perm L.keys.1 L.keys.2.1 L.keys.2.2
    (blocks (slotInput (pubOf L) s v)) hj' _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)))⟩

/-- **A position's computation hashes its slot's honest input.** -/
theorem slotInput_mem_queries {s : Slot} (hs : InTable s) :
    slotInput (pubOf L) s (valuePos L) ∈
      queries (spongeOut (spongePerm L.keys L.perm)) (posM (slotOutPos s) L.param (csHash L)) := by
  cases s with
  | chain l e step i =>
    have hst := step.isLt
    have hmod : (step.val + 1) % chainLength = step.val + 1 :=
      Nat.mod_eq_of_lt (by simp only [chainLength, winternitzBits] at hst ⊢; omega)
    have hmod' : step.val % chainLength = step.val :=
      Nat.mod_eq_of_lt (by simp only [chainLength, winternitzBits] at hst ⊢; omega)
    show _ ∈ queries _ (chainM L.param (csHash L) l e i ((step.val + 1) % chainLength))
    rw [hmod]
    simp only [chainM, hst, ↓reduceDIte]
    refine mem_queries_bind_right _ _ _ ?_
    rw [eval_chainM]
    have hin : slotInput (pubOf L) (.chain l e step i) (valuePos L) =
        thInput L.param (hashDomainFields (.chain l e ⟨step.val, hst⟩))
          (Verification.chainPayload i (L.chainValue l e i step.val)) := by
      show thInput L.param _ (Verification.chainPayload i (L.chainValue l e i
        (step.val % chainLength))) = _
      rw [hmod']
      rfl
    rw [hin]
    exact mem_queries_hashQ_bind _ _ _
  | leaf l e =>
    have he : e.val % 2 ^ 32 = e.val := Nat.mod_eq_of_lt e.isLt
    show _ ∈ queries _ (treeM L.param (csHash L) l (0 % (layerHeight + 1)) (e.val % 2 ^ 32))
    rw [Nat.zero_mod, he]
    simp only [treeM]
    refine mem_queries_bind_right _ _ _ ?_
    rw [evalWithAnswerFn_sequenceFin, leafKey_val]
    have hin : slotInput (pubOf L) (.leaf l e) (valuePos L) =
        thInput L.param (hashDomainFields (.leaf l e)) (digestsPayload fun i ↦
          evalWithAnswerFn (spongeOut (spongePerm L.keys L.perm))
            (chainM L.param (csHash L) l e i (chainLength - 1))) := by
      simp only [eval_chainM]
      rfl
    rw [hin]
    exact mem_queries_hashQ_bind _ _ _
  | node l level index =>
    obtain ⟨h1, h2, h3⟩ := hs
    have hb := node_bounds (l := l) (level := level) (index := index) ⟨h1, h2, h3⟩
    obtain ⟨lev, rfl⟩ : ∃ lev, level = lev + 1 := ⟨level - 1, by omega⟩
    simp only [layerHeight] at h2 hb
    show _ ∈ queries _ (treeM L.param (csHash L) l ((lev + 1) % (layerHeight + 1))
      (index % 2 ^ 32))
    rw [Nat.mod_eq_of_lt (show lev + 1 < layerHeight + 1 by simp only [layerHeight]; omega),
      Nat.mod_eq_of_lt (show index < 2 ^ 32 by omega)]
    simp only [treeM]
    refine mem_queries_bind_right _ _ _ (mem_queries_bind_right _ _ _ ?_)
    rw [eval_treeM, eval_treeM]
    have hin : slotInput (pubOf L) (.node l (lev + 1) index) (valuePos L) =
        thInput L.param (hashDomainFields (.node l (lev + 1) index))
          (nodePayload (L.treeValue l lev (2 * index)) (L.treeValue l lev (2 * index + 1))) := by
      show thInput L.param _ (nodePayload (L.treeValue l ((lev + 1 - 1) % (layerHeight + 1))
        ((2 * index) % 2 ^ 32)) (L.treeValue l ((lev + 1 - 1) % (layerHeight + 1))
          ((2 * index + 1) % 2 ^ 32))) = _
      rw [Nat.add_sub_cancel, Nat.mod_eq_of_lt (show lev < layerHeight + 1 by
        simp only [layerHeight]; omega), Nat.mod_eq_of_lt (show 2 * index < 2 ^ 32 by omega),
        Nat.mod_eq_of_lt (show 2 * index + 1 < 2 ^ 32 by omega)]
      rfl
    rw [hin]
    exact mem_queries_hashQ_bind _ _ _
  | _ => exact absurd hs id

/-- **`CoversPaths` for the positions' computations.** -/
theorem coversPaths_posM : CoversPaths posM := by
  intro L s hs j hj
  refine ⟨slotOutPos s, ?_⟩
  show srcCellH (pubOf L) s (valuePos L) j ∈
    hCells (honestEval L.keys L.perm (posM (slotOutPos s) L.param (csHash L))).2
  rw [snd_honestEval]
  obtain ⟨a, ha⟩ := mem_hCells.mp (cellH_mem_hCells_inputReads L s (valuePos L) hj)
  exact mem_hCells.mpr ⟨a, List.mem_flatMap.mpr ⟨_, slotInput_mem_queries L hs, ha⟩⟩

end pathComp

/-! ## The bad fraction (`bad`) -/

section bad

variable {ι : Type} {β : ι → Type}

theorem card_filter_notMem_eq {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α) :
    (Finset.univ.filter fun x ↦ x ∉ s).card = Fintype.card α - s.card := by
  rw [show (Finset.univ.filter fun x ↦ x ∉ s) = Finset.univ \ s by ext x; simp,
    Finset.card_univ_sdiff]

/-- Counting through a map injective on the counted set. -/
theorem card_filter_le_of_injOn {α γ : Type*} [Fintype α] [Fintype γ] (f : α → γ)
    (p : α → Prop) (r : γ → Prop) [DecidablePred p] [DecidablePred r]
    (hpr : ∀ a, p a → r (f a)) (hinj : ∀ a b, p a → p b → f a = f b → a = b) :
    (Finset.univ.filter p).card ≤ (Finset.univ.filter r).card := by
  refine Finset.card_le_card_of_injOn f (fun a ha ↦ ?_) fun a ha b hb e ↦ ?_
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha ⊢
    exact hpr a ha
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
    exact hinj a b ha hb e

open scoped Classical in
/-- **The bad fraction of the good set**: SchemeSplit's fraction (`schemeGood_frac_le` for the
computations `Q`), Reparam's (`xGood_bad_frac_le`, with the path-collision fraction of `PathBad`
left to PathBad's analysis), and the fraction of public data and hidden values that are not
source-good. -/
theorem goodT_bad_frac_le [Fintype ι] (G : ℕ)
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (q qs₀ qs₁ : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs₀ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter SeedShaped).card ≤ qs₀ i)
    (hqs₁ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ S b, skCell P S b = x).card ≤
        qs₁ i) :
    (Fintype.card TE : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ ¬goodT Q t).card ≤
      (((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z)) +
        ((Fintype.card (Option (Option CsIdx)) * Fintype.card (Option (Option CsIdx)) * (G + 1) :
          ℕ) : ℝ≥0∞) / Fintype.card Z +
        ∑ i, ((qs₀ i : ℝ≥0∞) / 2 ^ 256 + (G + 1) * q i / Fintype.card Z +
          ((qs₁ i : ℝ≥0∞) / 2 ^ 256 +
            Fintype.card (Option CsIdx) * (G + 1) * q i / Fintype.card Z))) +
      (((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z)) +
        ((xI₁.card * xI₁.card * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
        (Fintype.card (((Z → X) × XW) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun y ↦ PathBad y).card) +
      (Fintype.card (PX × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦ ¬SrcGood (pubX y.1) y.2).card := by
  have h3 := card_filter_not_le_three (goodT Q)
    (fun t ↦ ((Equiv.prodAssoc HonestTable SeedSlots (ValPos → Digest)).symm t).1 ∉ schemeGood Q)
    (fun t ↦ ¬XGood (tabEquiv t).1)
    (fun t ↦ XGood (tabEquiv t).1 ∧ ¬SrcGood (pubX (reparamE t).1) (reparamE t).2)
    fun t ht ↦ by
      by_cases h1 : (t.1, t.2.1) ∈ schemeGood Q
      · by_cases h2 : XGood (tabEquiv t).1
        · exact Or.inr (Or.inr ⟨h2, fun h3 ↦ ht ⟨h1, h2, h3⟩⟩)
        · exact Or.inr (Or.inl h2)
      · exact Or.inl h1
  have hA := inv_card_mul_card_filter_comp_fst
    (Equiv.prodAssoc HonestTable SeedSlots (ValPos → Digest)).symm (fun x ↦ x ∉ schemeGood Q)
  rw [card_filter_notMem_eq] at hA
  have hB := inv_card_mul_card_filter_comp_fst tabEquiv (fun θ ↦ ¬XGood θ)
  have hC := card_filter_le_of_injOn reparamE
    (fun t ↦ XGood (tabEquiv t).1 ∧ ¬SrcGood (pubX (reparamE t).1) (reparamE t).2)
    (fun y : PX × (ValPos → Digest) ↦ ¬SrcGood (pubX y.1) y.2) (fun _ h ↦ h.2)
    fun _ _ h₁ h₂ e ↦ reparamE_injOn_xGood h₁.1 h₂.1 e
  rw [card_px_eq]
  calc (Fintype.card TE : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ ¬goodT Q t).card
      ≤ (Fintype.card TE : ℝ≥0∞)⁻¹ *
          (((Finset.univ.filter fun t ↦ ((Equiv.prodAssoc HonestTable SeedSlots
            (ValPos → Digest)).symm t).1 ∉ schemeGood Q).card : ℝ≥0∞) +
          (Finset.univ.filter fun t ↦ ¬XGood (tabEquiv t).1).card +
          (Finset.univ.filter fun t ↦
            XGood (tabEquiv t).1 ∧ ¬SrcGood (pubX (reparamE t).1) (reparamE t).2).card) := by
        gcongr
        exact_mod_cast h3
    _ = (Fintype.card TE : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun t ↦ ((Equiv.prodAssoc HonestTable SeedSlots
            (ValPos → Digest)).symm t).1 ∉ schemeGood Q).card +
        (Fintype.card TE : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ ¬XGood (tabEquiv t).1).card +
        (Fintype.card TE : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦
            XGood (tabEquiv t).1 ∧ ¬SrcGood (pubX (reparamE t).1) (reparamE t).2).card := by
        ring
    _ ≤ _ := by
        gcongr
        · rw [hA, div_eq_mul_inv, mul_comm]
          exact schemeGood_frac_le G Q q qs₀ qs₁ hq hqs₀ hqs₁
        · rw [hB, div_eq_mul_inv, mul_comm]
          exact xGood_bad_frac_le G

/-- The reads bound of the positions' computations. -/
abbrev posReads : ℕ := 24 * (176 * 2 ^ 16)

open scoped Classical in
/-- **The bad fraction with the positions' computations** (`posM`, at most `posReads` reads each,
summed over the positions `ValPos`). -/
theorem goodT_posM_bad_frac_le (G : ℕ) :
    (Fintype.card TE : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ ¬goodT posM t).card ≤
      (((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z)) +
        ((Fintype.card (Option (Option CsIdx)) * Fintype.card (Option (Option CsIdx)) * (G + 1) :
          ℕ) : ℝ≥0∞) / Fintype.card Z +
        ∑ _p : ValPos, ((posReads : ℝ≥0∞) / 2 ^ 256 + (G + 1) * posReads / Fintype.card Z +
          ((posReads : ℝ≥0∞) / 2 ^ 256 +
            Fintype.card (Option CsIdx) * (G + 1) * posReads / Fintype.card Z))) +
      (((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z)) +
        ((xI₁.card * xI₁.card * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
        (Fintype.card (((Z → X) × XW) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun y ↦ PathBad y).card) +
      (Fintype.card (PX × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦ ¬SrcGood (pubX y.1) y.2).card :=
  goodT_bad_frac_le G posM (fun _ ↦ posReads) (fun _ ↦ posReads) (fun _ ↦ posReads)
    (fun p t π P Cs ↦ length_honestEval_posM p t π P Cs)
    (fun p t π P Cs ↦ (Finset.card_filter_le _ _).trans
      ((card_kCells_le _).trans (length_honestEval_posM p t π P Cs)))
    (fun p t π P Cs ↦ (Finset.card_filter_le _ _).trans
      ((card_kCells_le _).trans (length_honestEval_posM p t π P Cs)))

end bad

/-! ## Masses' bound with the sources and the reparametrization -/

section masses

/-! ### The randomizer-base coordinates: a pad

The template's hidden values are indexed by `HPos`. The randomizer-base coordinates `.inr` are a
uniform pad `RLabel → Digest` here: no hidden cell has them as a source (`srcFH`). -/

/-- The padded table with the randomizer-base pad. -/
abbrev TER : Type := HonestTable × ((SeedSlots × (ValPos → Digest)) × (RLabel → Digest))

/-- The padded table without the randomizer-base pad. -/
def toTE (t : TER) : TE := (t.1, t.2.1)

/-- The padded tables as the padded tables of `TE` with the randomizer-base pad. -/
def terEquiv : TER ≃ TE × (RLabel → Digest) :=
  (Equiv.prodAssoc _ _ _).symm

/-- **The reparametrization with the randomizer-base pad**: `reparamE`, the pad at `.inr`. -/
noncomputable def reparamER (t : TER) : PX × (HPos → Digest) :=
  ((reparamE (toTE t)).1, Sum.elim (reparamE (toTE t)).2 t.2.2)

theorem reparamER_injOn {ι : Type} {β : ι → Type}
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) :
    Set.InjOn reparamER {t | goodT Q (toTE t)} := by
  intro t₁ h₁ t₂ h₂ he
  rw [reparamER, reparamER, Prod.mk.injEq] at he
  obtain ⟨h1, h2⟩ := he
  have ht := reparamE_injOn Q h₁ h₂ (Prod.ext h1 (funext fun p ↦ congrFun h2 (Sum.inl p)))
  have h3 : t₁.2.2 = t₂.2.2 := funext fun lab ↦ congrFun h2 (Sum.inr lab)
  exact Prod.ext (congrArg (fun t : TE ↦ t.1) ht) (Prod.ext (congrArg (fun t : TE ↦ t.2) ht) h3)

/-- The public data and hidden values with the randomizer-base pad, as the padded tables. -/
noncomputable def pxrEquiv : PX × (HPos → Digest) ≃ TER :=
  (Equiv.prodCongr (Equiv.refl PX) (Equiv.sumArrowEquivProdArrow ValPos RLabel Digest)).trans
    ((Equiv.prodAssoc PX (ValPos → Digest) (RLabel → Digest)).symm.trans
      ((Equiv.prodCongr (pxEquiv.trans tabEquiv.symm) (Equiv.refl _)).trans terEquiv.symm))

open scoped Classical in
/-- **`hcard`** with the randomizer-base pad. -/
theorem card_reparamER_le :
    Fintype.card PX * Fintype.card (HPos → Digest) ≤ Fintype.card TER :=
  ((Fintype.card_prod PX (HPos → Digest)).symm.trans (Fintype.card_congr pxrEquiv)).le

theorem natCast_mul_inv_mul_cancel (a b c : ℕ) (hc : c ≠ 0) :
    ((a * c : ℕ) : ℝ≥0∞)⁻¹ * ((b * c : ℕ) : ℝ≥0∞) = (a : ℝ≥0∞)⁻¹ * b := by
  have hc' : (c : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hc
  rw [Nat.cast_mul, Nat.cast_mul, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top c))
    (Or.inl (ENNReal.natCast_ne_top a)), mul_assoc, mul_comm (c : ℝ≥0∞)⁻¹, mul_assoc,
    ENNReal.mul_inv_cancel hc' (ENNReal.natCast_ne_top c), mul_one]

/-- The fraction of a predicate failing does not see a product coordinate. -/
theorem badFrac_prod {T R : Type*} [Fintype T] [Fintype R] [Nonempty R] (p : T → Prop)
    [DecidablePred p] :
    (Fintype.card (T × R) : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun x : T × R ↦ ¬p x.1).card =
      (Fintype.card T : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ ¬p t).card := by
  have hf : (Finset.univ.filter fun x : T × R ↦ ¬p x.1).card =
      (Finset.univ.filter fun t ↦ ¬p t).card * Fintype.card R := by
    rw [← Finset.univ_product_univ, Finset.filter_product_left (fun t ↦ ¬p t),
      Finset.card_product, Finset.card_univ]
  rw [hf, Fintype.card_prod]
  exact natCast_mul_inv_mul_cancel _ _ _ Fintype.card_ne_zero

open scoped Classical in
/-- **The bad fraction does not see the randomizer-base pad.** -/
theorem badFrac_reparamER {ι : Type} {β : ι → Type}
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) :
    (Fintype.card TER : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t : TER ↦ ¬goodT Q (toTE t)).card =
      (Fintype.card TE : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ ¬goodT Q t).card := by
  have hc : (Finset.univ.filter fun t : TER ↦ ¬goodT Q (toTE t)).card =
      (Finset.univ.filter fun x : TE × (RLabel → Digest) ↦ ¬goodT Q x.1).card :=
    Finset.card_equiv terEquiv fun t ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl
  rw [hc, Fintype.card_congr terEquiv]
  exact badFrac_prod (goodT Q)

variable {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M)

open scoped Classical in
/-- **Masses' `uavg_totalWeight_portMass_le` with `e`, `G`, `hinj`, `hcard`, `hsub` and `src`
discharged** (`κ = 2^-128`), at the public data `pubX`, for computations `Q` covering the honest
paths' `h`-cells, with the randomizer-base pad (`reparamER`). Left: the game congruence `hgame`,
the invariant `hinv` (GameTCalls) and the call bound `hN`. -/
theorem uavg_totalWeight_portMass_le_reparam
    (Qp : (recHwSpec X Z HPos M).Port → Prop) [DecidablePred Qp]
    (A : Adversary (X × Z)) (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1) {ι : Type} {β : ι → Type}
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (hQ : CoversPaths Q)
    (hgame : ∀ t : TER, goodT Q (toTE t) →
      realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A) =
        realizeT (reparamER t).2 (gameT M upd (pubX (reparamER t).1) A))
    (hinv : ∀ p v, (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (invSupp (runtimeR m₀) Qp (SlotInv M (pubX p) v)) (realizeT v (gameT M upd (pubX p) A)) ρ)
    {N : ℕ} (hN : ∀ (pub : Pub) (v : HPos → Digest),
      IFreeM.IsChargeBound (realizeT v (gameT M upd pub A))
        (portCharge fun i ↦ if Qp i then 1 else 0) N) :
    uavg (fun L : HonestTable ↦ (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (portMass Qp (pathH L) (pathK L) (pathK' L))
        (realizeT (valueAt L) (gameT M upd (pubOf L) A)) ρ) ≤
      N * (2 ^ 128 : ℝ≥0∞)⁻¹ + N * ((Fintype.card TE : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t ↦ ¬goodT Q t).card) := by
  refine (uavg_totalWeight_portMass_le upd Qp A m₀ ρ hρ hρ1 pathH pathK pathK' reparamER
    (fun t ↦ goodT Q (toTE t)) (reparamER_injOn Q) card_reparamER_le pubX hgame
    (fun p v ↦ hidH (pubX p) fun q ↦ v (.inl q)) (fun p v ↦ hidK (pubX p) fun q ↦ v (.inl q))
    (fun p v ↦ hidK' (pubX p) fun q ↦ v (.inl q)) (fun t ht ↦ hsub_reparam hQ (toTE t) ht)
    (fun p ↦ SlotInv M (pubX p)) hinv _ (fun p ↦ sourcesSlotInv M (pubX p)) hN).trans_eq ?_
  rw [card_digest_inv]
  exact congrArg (fun b ↦ N * (2 ^ 128 : ℝ≥0∞)⁻¹ + N * b) (badFrac_reparamER Q)

open scoped Classical in
/-- **Masses' bound for leanXMSS's reparametrization** (`Q = posM`): only `hgame`, `hinv` and `hN`
remain; the bad fraction is bounded by `goodT_posM_bad_frac_le`. -/
theorem uavg_totalWeight_portMass_le_xmss
    (Qp : (recHwSpec X Z HPos M).Port → Prop) [DecidablePred Qp]
    (A : Adversary (X × Z)) (m₀ : Finset HPos × M)
    (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M)))
      (QReg.of Unit × QReg.of (HwReg X Z (Finset HPos × M))) ℂ) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hgame : ∀ t : TER, goodT posM (toTE t) →
      realizeT (valueAt t.1) (gameT M upd (pubOf t.1) A) =
        realizeT (reparamER t).2 (gameT M upd (pubX (reparamER t).1) A))
    (hinv : ∀ p v, (runtimeR m₀).ForallQueries LocalSig.Interp.instruments
      (invSupp (runtimeR m₀) Qp (SlotInv M (pubX p) v)) (realizeT v (gameT M upd (pubX p) A)) ρ)
    {N : ℕ} (hN : ∀ (pub : Pub) (v : HPos → Digest),
      IFreeM.IsChargeBound (realizeT v (gameT M upd pub A))
        (portCharge fun i ↦ if Qp i then 1 else 0) N) :
    uavg (fun L : HonestTable ↦ (runtimeR m₀).totalWeight LocalSig.Interp.instruments
      (portMass Qp (pathH L) (pathK L) (pathK' L))
        (realizeT (valueAt L) (gameT M upd (pubOf L) A)) ρ) ≤
      N * (2 ^ 128 : ℝ≥0∞)⁻¹ + N * ((Fintype.card TE : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t ↦ ¬goodT posM t).card) :=
  uavg_totalWeight_portMass_le_reparam upd Qp A m₀ ρ hρ hρ1 posM coversPaths_posM hgame hinv hN

end masses

end Quantum.Xmss.Assembly

end
