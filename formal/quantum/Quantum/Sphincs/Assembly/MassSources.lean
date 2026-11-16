module

public import Quantum.Sphincs.Assembly.ChgRev
public import Quantum.Sphincs.Assembly.SrcBad
public import Quantum.Sphincs.Assembly.GameTCalls
public import Quantum.Xmss.Assembly.MassesR0

@[expose] public section

/-!
# The sources of leanSPHINCS's hidden cells, and the averaged hidden masses

Masses' hypotheses on the hidden values for leanSPHINCS's canonical runtime-2 game at `msgPol`
(`gameR msgPol A`), over the composed reparametrization `fullE` of
`Quantum.Sphincs.Assembly.ReparamFull`.

* **Designated sources** (SrcBad's `dsrc`: a structural slot's first payload value): an input of
  its own slot only (`eq_of_isInput_dsrc`), and a slot's cells depend on its inputs only
  (`sCellK_congr_isInput`, ...).
* **Sources from pair goodness** (`srcF`, `srcF_pair_eq`): on source-good values (SrcBad's
  `SrcGood`) a cell of an in-table path names at most one pair (designated source, value), so it
  weighs `2^-128`. The hidden sets `hidH`, `hidK`, `hidK'` are the in-table paths' cells at
  `(pub.xw, pub.keys.1, valsOf v)` on source-good values; the sources are the value coordinates
  `.val q` (`srcFH`: none at the other coordinates).
* `sourcesSlotInv M pub`: Masses' `Sources` on GameTCalls' `SlotInv M pub`, `κ = |Digest|⁻¹`.
* **The never-revealed part** `(SK.seed, SK.prf) × SeedStage's slots × W` with `sOf = SK.seed`
  (`skOf`): the `SK.seed`-keyed paths' capacities and rates over SeedStage's slots (`seedHK`,
  `seedK'K`), each point in them for at most `seedEps 18 ≤ 2^-463` of it
  (`sum_indicator_seedHK_le`, `sum_indicator_seedK'K_le`).
* **The good set** `MassG S`: ReparamFull's `FullG` with source goodness added to the static
  condition. `goodT_posM_bad_frac_le`: its bad fraction is ReparamFull's (a parameter `fullGFrac`,
  `2^-197 + 2^-400` by `fullG_frac_le_keccak`), SrcBad's `2^-277` and the static condition's.
* **`hsub` for the in-table paths** (`tabPaths_subset_hid`): on the good set the table's path
  cells (`tabPathH`, ...) lie in the hidden sets at the reparametrized data.
* **The averaged bound** (`uavg_totalWeight_portMass_le_sph`): for ports `Q` other than the program
  ports with at most `N` calls, the table average of the hidden mass at hidden sets lying (on the
  good set) in `hidH ∪ Hhk` (and likewise for `k`, `k'`) is at most
  `N (2^-128 + εK) + N · chgRevAvg + N · massGFrac`. `hgame_fullE` holds off the charged
  coordinates `chgB t` only, so Mismatch's record mass of `chgB t` enters as the named average
  `chgRevAvg` (the first-meeting record mass at `fullE`'s data, over the good set), bounded in
  `Quantum.Sphincs.Assembly.ChgRevAvg` (`chgRevAvg_le`: `3 signatureLimit (epsK + cD)` times the
  trace on static data satisfying ChgRevStatic's `ChgStatic`, `≤ 2^-215`).
-/

open IPFunctor Matrix
open scoped ENNReal ComplexOrder Kronecker

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message MasterSeed PublicParameter chainLength)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (uavg portMass Agree revW totalWeight_portMass_le_mismatch CoinSlots
  LazyProg)
open Quantum.Xmss.Assembly (Sources recHwSpec runtimeR realizeT invSupp XW
  sum_totalWeight_portMass_runtimeR_le_inv totalWeight_portMass_mono totalWeight_portMass_union_le
  totalWeight_portMass_le sum_totalWeight_portMass_le_count card_filter_le_add_of_imp uavg_pad
  card_digest)
open Quantum.Sphincs.Hybrid (Secret SeedKS SeedSlots seedHSlots seedK'Slots seedEps
  sum_indicator_seedHSlots_le sum_indicator_seedK'Slots_le)

namespace Quantum.Sphincs.Assembly

/- Membership in the concrete FORS opening's sets is otherwise decided by evaluating them, and
membership in the positions' enumeration by evaluating it. -/
attribute [local irreducible] forsNeed forsSlots Fin.fintype

/-! ## Designated sources -/

section dsrc

theorem isInput_dsrc {s : Slot} (hs : InTable s) : IsInput (dsrc s) s := by
  cases s with
  | chain l τ e i step => rfl
  | leaf l τ e => exact ⟨⟨0, by decide⟩, rfl⟩
  | node l τ height index => exact Or.inl rfl
  | forsLeaf idx κ s => rfl
  | forsNode idx κ height node => exact Or.inl rfl
  | forsRoots idx => exact ⟨⟨0, by decide⟩, rfl⟩
  | _ => exact hs.elim

theorem cpos_inj {l l' : Layer} {τ τ' : TreeIndex} {e e' : TreeLeafIndex} {i i' : ChainIndex}
    {j j' : ℕ} (hj : j < chainLength) (hj' : j' < chainLength)
    (h : cpos l τ e i j = cpos l' τ' e' i' j') : l = l' ∧ τ = τ' ∧ e = e' ∧ i = i' ∧ j = j' := by
  simp only [cpos, ValPos.chain.injEq, Fin.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rw [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at h5
  exact ⟨h1, h2, h3, h4, h5⟩

theorem chainStep_lt' (step : HashSig.ChainStep) : step.val < chainLength - 1 :=
  step.isLt

/-- An in-table node's left child: in range one level below. -/
theorem node_dsrc_facts {l : Layer} {τ : TreeIndex} {height index : ℕ}
    (hs : InTable (.node l τ height index)) :
    height - 1 ≤ 10 ∧ 2 * index < 2 ^ 10 ∧ 1 ≤ height := by
  obtain ⟨-, h1, h2, h3⟩ := hs
  have hb := two_mul_add_one_lt h3 h1 h2
  have hp := two_pow_layerHeight_le l
  have hH := layerHeight_le l
  have hT : layerHeight topLayer = 10 := rfl
  have hT' : 2 ^ layerHeight topLayer = 2 ^ 10 := rfl
  exact ⟨by omega, by omega, h1⟩

/-- An in-table FORS node's left child: in range one level below. -/
theorem forsNode_dsrc_facts {idx : Index} {κ : ForsTreeIndex} {height node : ℕ}
    (hs : InTable (.forsNode idx κ height node)) :
    height - 1 ≤ 9 ∧ 2 * node < 2 ^ 10 ∧ 1 ≤ height := by
  obtain ⟨h1, h2, h3⟩ := hs
  have hb := two_mul_add_one_lt h3 h1 h2
  have hF : forsTreeHeight = 10 := rfl
  have hF' : 2 ^ forsTreeHeight = 2 ^ 10 := rfl
  exact ⟨by omega, by omega, h1⟩

/-- **A designated source is an input of its own slot only.** -/
theorem eq_of_isInput_dsrc {s s' : Slot} (hs : InTable s) (hs' : InTable s')
    (h : IsInput (dsrc s) s') : s = s' := by
  have hC : chainLength = 4 := rfl
  have hF : forsTreeHeight = 10 := rfl
  cases s with
  | chain l τ e i step =>
    have hst := chainStep_lt' step
    cases s' with
    | chain l' τ' e' i' step' =>
      have hst' := chainStep_lt' step'
      obtain ⟨rfl, rfl, rfl, rfl, h5⟩ := cpos_inj (by omega) (by omega) h
      rw [Fin.ext h5]
    | leaf l' τ' e' =>
      obtain ⟨i', h⟩ := h
      have := (cpos_inj (by omega) (by omega) h).2.2.2.2
      omega
    | node => rcases h with h | h <;> exact ValPos.noConfusion h
    | forsLeaf => exact ValPos.noConfusion h
    | forsNode => rcases h with h | h <;> exact ValPos.noConfusion h
    | forsRoots => obtain ⟨_, h⟩ := h; exact ValPos.noConfusion h
    | _ => exact hs'.elim
  | leaf l τ e =>
    cases s' with
    | chain l' τ' e' i' step' =>
      have hst' := chainStep_lt' step'
      have := (cpos_inj (by omega) (by omega) h).2.2.2.2
      omega
    | leaf l' τ' e' =>
      obtain ⟨i', h⟩ := h
      obtain ⟨rfl, rfl, rfl, -⟩ := cpos_inj (by omega) (by omega) h
      rfl
    | node => rcases h with h | h <;> exact ValPos.noConfusion h
    | forsLeaf => exact ValPos.noConfusion h
    | forsNode => rcases h with h | h <;> exact ValPos.noConfusion h
    | forsRoots => obtain ⟨_, h⟩ := h; exact ValPos.noConfusion h
    | _ => exact hs'.elim
  | node l τ height index =>
    obtain ⟨f1, f2, f3⟩ := node_dsrc_facts hs
    cases s' with
    | chain => exact ValPos.noConfusion h
    | leaf => obtain ⟨_, h⟩ := h; exact ValPos.noConfusion h
    | node l' τ' height' index' =>
      obtain ⟨a, ha, ha2, ha3, h1', h2'⟩ := isInput_node hs' h
      have hH := layerHeight_le l'
      have hT : layerHeight topLayer = 10 := rfl
      obtain ⟨rfl, rfl, e3, e4⟩ := (tpos_eq_iff f1 (by omega) f2 ha3).mp ha
      have : height = height' := by omega
      subst this
      have : index = index' := by omega
      subst this
      rfl
    | forsLeaf => exact ValPos.noConfusion h
    | forsNode => rcases h with h | h <;> exact ValPos.noConfusion h
    | forsRoots => obtain ⟨_, h⟩ := h; exact ValPos.noConfusion h
    | _ => exact hs'.elim
  | forsLeaf idx κ s =>
    cases s' with
    | chain => exact ValPos.noConfusion h
    | leaf => obtain ⟨_, h⟩ := h; exact ValPos.noConfusion h
    | node => rcases h with h | h <;> exact ValPos.noConfusion h
    | forsLeaf idx' κ' s'' =>
      simp only [IsInput, dsrc, ValPos.forsSecret.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl
    | forsNode => rcases h with h | h <;> exact ValPos.noConfusion h
    | forsRoots => obtain ⟨_, h⟩ := h; exact ValPos.noConfusion h
    | _ => exact hs'.elim
  | forsNode idx κ height node =>
    obtain ⟨f1, f2, f3⟩ := forsNode_dsrc_facts hs
    cases s' with
    | chain => exact ValPos.noConfusion h
    | leaf => obtain ⟨_, h⟩ := h; exact ValPos.noConfusion h
    | node => rcases h with h | h <;> exact ValPos.noConfusion h
    | forsLeaf => exact ValPos.noConfusion h
    | forsNode idx' κ' height' node' =>
      obtain ⟨a, ha, ha2, ha3, h1', h2'⟩ := isInput_forsNode hs' h
      obtain ⟨rfl, rfl, e3, e4⟩ := (fpos_eq_iff (by omega) (by omega) f2 ha3).mp ha
      have : height = height' := by omega
      subst this
      have : node = node' := by omega
      subst this
      rfl
    | forsRoots idx' =>
      obtain ⟨κ', h⟩ := h
      have := ((fpos_eq_iff (by omega) (by omega) f2 (by norm_num)).mp h).2.2.1
      omega
    | _ => exact hs'.elim
  | forsRoots idx =>
    cases s' with
    | chain => exact ValPos.noConfusion h
    | leaf => obtain ⟨_, h⟩ := h; exact ValPos.noConfusion h
    | node => rcases h with h | h <;> exact ValPos.noConfusion h
    | forsLeaf => exact ValPos.noConfusion h
    | forsNode idx' κ' height' node' =>
      obtain ⟨a, ha, ha2, ha3, h1', h2'⟩ := isInput_forsNode hs' h
      have := ((fpos_eq_iff (by omega) (by omega) (by norm_num) ha3).mp ha).2.2.1
      omega
    | forsRoots idx' =>
      obtain ⟨κ', h⟩ := h
      obtain ⟨rfl, -⟩ := (fpos_eq_iff le_rfl le_rfl (by norm_num) (by norm_num)).mp h
      rfl
    | _ => exact hs'.elim
  | _ => exact hs.elim

/-- **An in-table slot's input depends on the values at its inputs only.** -/
theorem slotInput_congr_isInput (P : PublicParameter) {s : Slot} (hs : InTable s)
    {f g : ValPos → Digest} (h : ∀ q, IsInput q s → f q = g q) :
    slotInput P s f = slotInput P s g := by
  cases s with
  | chain l τ e i step =>
    change addressedHashInput _ _ (HashSig.littleEndianBytes 16 (f _)) =
      addressedHashInput _ _ (HashSig.littleEndianBytes 16 (g _))
    rw [h _ rfl]
  | leaf l τ e =>
    change addressedHashInput _ _ (HashSig.digestsPayload fun i ↦ f _) =
      addressedHashInput _ _ (HashSig.digestsPayload fun i ↦ g _)
    exact congrArg (addressedHashInput _ _) (congrArg HashSig.digestsPayload (funext fun i ↦
      h _ ⟨i, rfl⟩))
  | node l τ height index =>
    change addressedHashInput _ _ (HashSig.OverPermutation.nodePayload (f _) (f _)) =
      addressedHashInput _ _ (HashSig.OverPermutation.nodePayload (g _) (g _))
    rw [h _ (Or.inl rfl), h _ (Or.inr rfl)]
  | forsLeaf idx κ s =>
    change addressedHashInput _ _ (HashSig.littleEndianBytes 16 (f _)) =
      addressedHashInput _ _ (HashSig.littleEndianBytes 16 (g _))
    rw [h _ rfl]
  | forsNode idx κ height node =>
    change addressedHashInput _ _ (HashSig.OverPermutation.nodePayload (f _) (f _)) =
      addressedHashInput _ _ (HashSig.OverPermutation.nodePayload (g _) (g _))
    rw [h _ (Or.inl rfl), h _ (Or.inr rfl)]
  | forsRoots idx =>
    change addressedHashInput _ _ (HashSig.digestsPayload fun κ ↦ f _) =
      addressedHashInput _ _ (HashSig.digestsPayload fun κ ↦ g _)
    exact congrArg (addressedHashInput _ _) (congrArg HashSig.digestsPayload (funext fun κ ↦
      h _ ⟨κ, rfl⟩))
  | _ => exact hs.elim

theorem slotBlk_congr_isInput (P : PublicParameter) {s : Slot} (hs : InTable s)
    {f g : ValPos → Digest} (h : ∀ q, IsInput q s → f q = g q) :
    slotBlk P s f = slotBlk P s g :=
  congrArg (fun x j ↦ (Quantum.Xmss.blocks x).getD j 0) (slotInput_congr_isInput P hs h)

theorem sCellK_congr_isInput (w : XW) (h : Z → X) {s : Slot} (hs : InTable s)
    {f g : ValPos → Digest} (hfg : ∀ q, IsInput q s → f q = g q) (j : ℕ) :
    sCellK w h s f j = sCellK w h s g j := by
  unfold sCellK
  rw [slotBlk_congr_isInput w.1 hs hfg]

theorem sCellR_congr_isInput (w : XW) (h : Z → X) {s : Slot} (hs : InTable s)
    {f g : ValPos → Digest} (hfg : ∀ q, IsInput q s → f q = g q) (j : ℕ) :
    sCellR w h s f j = sCellR w h s g j := by
  unfold sCellR
  rw [slotBlk_congr_isInput w.1 hs hfg]

theorem sCellZ_congr_isInput (w : XW) (h : Z → X) {s : Slot} (hs : InTable s)
    {f g : ValPos → Digest} (hfg : ∀ q, IsInput q s → f q = g q) (j : ℕ) :
    sCellZ w h s f j = sCellZ w h s g j := by
  unfold sCellZ
  rw [slotBlk_congr_isInput w.1 hs hfg]

end dsrc

/-! ## Sources from pair goodness, over a cell family -/

section pairs

variable {C : Type} (nB : Slot → ℕ) (c : Slot → (ValPos → Digest) → ℕ → C)

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
    (q : ValPos) (d : Digest) :
    srcF nB c Good y (Function.update v q d) q = srcF nB c Good y v q := by
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
theorem srcF_pair_eq {Good : (ValPos → Digest) → Prop}
    (hG : ∀ w, Good w → PairGood nB c (fun _ _ ↦ False) w)
    (hloc : ∀ s, InTable s → ∀ v v', (∀ q, IsInput q s → v q = v' q) → ∀ j, c s v j = c s v' j)
    {y : C} {v : ValPos → Digest} {q₁ q₂ : ValPos} {d₁ d₂ : Digest}
    (ha : d₁ ∈ srcF nB c Good y v q₁) (hb : d₂ ∈ srcF nB c Good y v q₂) : q₁ = q₂ ∧ d₁ = d₂ := by
  obtain ⟨hg₁, s₁, hs₁, rfl, j₁, hj₁, hy₁⟩ := mem_srcF.mp ha
  obtain ⟨-, s₂, hs₂, rfl, j₂, hj₂, hy₂⟩ := mem_srcF.mp hb
  set w₁ := Function.update v (dsrc s₁) d₁ with hw₁
  have key : ∀ d, (s₂ ≠ s₁ ∨ d ≠ w₁ (dsrc s₂)) →
      c s₁ w₁ j₁ ≠ c s₂ (Function.update w₁ (dsrc s₂) d) j₂ := fun d hd ↦
    hG w₁ hg₁ s₂ s₁ hs₂ hs₁ j₂ hj₂ j₁ hj₁ not_false d hd
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
    refine hloc s₂ hs₂ _ _ (fun q hq ↦ ?_) j₂
    have hq₁ : q ≠ dsrc s₁ := fun h ↦ hs (eq_of_isInput_dsrc hs₁ hs₂ (h ▸ hq))
    by_cases hq₂ : q = dsrc s₂
    · rw [hq₂, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hq₂, Function.update_of_ne hq₂, hw₁, Function.update_of_ne hq₁]

theorem sum_card_srcF_le_one {Good : (ValPos → Digest) → Prop}
    (hG : ∀ w, Good w → PairGood nB c (fun _ _ ↦ False) w)
    (hloc : ∀ s, InTable s → ∀ v v', (∀ q, IsInput q s → v q = v' q) → ∀ j, c s v j = c s v' j)
    (y : C) (v : ValPos → Digest) :
    ∑ q, (srcF nB c Good y v q).card ≤ 1 := by
  by_cases h : ∃ q d, d ∈ srcF nB c Good y v q
  · obtain ⟨q₀, d₀, hd₀⟩ := h
    rw [Fintype.sum_eq_single q₀ fun q hq ↦ Finset.card_eq_zero.mpr
      (Finset.eq_empty_of_forall_notMem fun d hd ↦ hq (srcF_pair_eq hG hloc hd hd₀).1)]
    exact Finset.card_le_one.mpr fun a ha b hb ↦ (srcF_pair_eq hG hloc ha hb).2
  · refine (Finset.sum_eq_zero fun q _ ↦ Finset.card_eq_zero.mpr
      (Finset.eq_empty_of_forall_notMem fun d hd ↦ h ⟨q, d, hd⟩)).le.trans zero_le_one

/-- The per-cell weight: at most one source pair, of weight `1 / |Digest|`. -/
theorem sum_srcF_weight_le {Good : (ValPos → Digest) → Prop}
    (hG : ∀ w, Good w → PairGood nB c (fun _ _ ↦ False) w)
    (hloc : ∀ s, InTable s → ∀ v v', (∀ q, IsInput q s → v q = v' q) → ∀ j, c s v j = c s v' j)
    (y : C) (v : ValPos → Digest) :
    ∑ q, ((srcF nB c Good y v q).card : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ ≤
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [← Finset.sum_mul, ← Nat.cast_sum]
  calc ((∑ q, (srcF nB c Good y v q).card : ℕ) : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹
      ≤ (1 : ℝ≥0∞) * (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
        gcongr
        exact_mod_cast sum_card_srcF_le_one hG hloc y v
    _ = _ := one_mul _

/-- A hidden cell not satisfying `P`, where every in-table slot with a disclosed designated
source has its cells satisfying `P`, names its slot's undisclosed designated source. -/
theorem exists_mem_srcF {Good : (ValPos → Digest) → Prop} {y : C} {v : ValPos → Digest}
    {T : Set ValPos} {P : C → Prop} (hy : y ∈ goodCells nB c Good v)
    (hT : ∀ s, InTable s → dsrc s ∈ T → ∀ j < nB s, P (c s v j)) (hP : ¬P y) :
    ∃ q, q ∉ T ∧ v q ∈ srcF nB c Good y v q := by
  obtain ⟨hg, s, hs, j, hj, rfl⟩ := hy
  refine ⟨dsrc s, fun hm ↦ hP (hT s hs hm j hj), mem_srcF.mpr ⟨?_, s, hs, rfl, j, hj, ?_⟩⟩
  · rw [Function.update_eq_self]
    exact hg
  · rw [Function.update_eq_self]

/-- The values at the positions commute with an update at a value coordinate. -/
theorem valsOf_update (v : (s : HPos) → XD s) (q : ValPos) (d : XD (.val q)) :
    valsOf (Function.update v (.val q) d) = Function.update (valsOf v) q d :=
  Function.update_comp_eq_of_injective' v (fun _ _ h ↦ HPos.val.inj h) q d

variable (nB c) in
/-- **The source values at a hidden coordinate**: `srcF` of the values at the positions, none at
the other coordinates. -/
noncomputable def srcFH (Good : (ValPos → Digest) → Prop) (y : C) :
    (s : HPos) → ((s : HPos) → XD s) → Finset (XD s)
  | .val q, v => srcF nB c Good y (valsOf v) q
  | .rnd _, _ => ∅
  | .dig _ _, _ => ∅
  | .str _ _, _ => ∅
  | .asg _ _, _ => ∅

theorem srcFH_update (Good : (ValPos → Digest) → Prop) (y : C) (v : (s : HPos) → XD s)
    (s : HPos) (d : XD s) :
    srcFH nB c Good y s (Function.update v s d) = srcFH nB c Good y s v := by
  cases s with
  | val q =>
    show srcF nB c Good y (valsOf (Function.update v (.val q) d)) q = srcF nB c Good y (valsOf v) q
    exact (congrArg (fun w ↦ srcF nB c Good y w q) (valsOf_update v q d)).trans
      (srcF_update nB c Good y _ q d)
  | rnd _ => rfl
  | dig _ _ => rfl
  | str _ _ => rfl
  | asg _ _ => rfl

/-- Every value coordinate is among the value coordinates. -/
theorem val_mem_valSet_univ (q : ValPos) : HPos.val q ∈ valSet (Finset.univ : Finset ValPos) :=
  val_mem_valSet.mpr (by simp)

/-- `exists_mem_srcF` over the hidden coordinates: the source is a value coordinate. -/
theorem exists_mem_srcFH {Good : (ValPos → Digest) → Prop} {y : C} {v : (s : HPos) → XD s}
    {T : Finset HPos} {P : C → Prop} (hy : y ∈ goodCells nB c Good (valsOf v))
    (hT : ∀ s, InTable s → HPos.val (dsrc s) ∈ T → ∀ j < nB s, P (c s (valsOf v) j))
    (hP : ¬P y) :
    ∃ s ∈ valSet Finset.univ, s ∉ T ∧ v s ∈ srcFH nB c Good y s v := by
  obtain ⟨q, hq, hv⟩ := exists_mem_srcF (T := {q | HPos.val q ∈ T}) (P := P) hy
    (fun s hs hm ↦ hT s hs hm) hP
  exact ⟨.val q, val_mem_valSet_univ q, hq, hv⟩

/-- `sum_srcF_weight_le` over the hidden coordinates. -/
theorem sum_srcFH_weight_le {Good : (ValPos → Digest) → Prop}
    (hG : ∀ w, Good w → PairGood nB c (fun _ _ ↦ False) w)
    (hloc : ∀ s, InTable s → ∀ v v', (∀ q, IsInput q s → v q = v' q) → ∀ j, c s v j = c s v' j)
    (y : C) (v : (s : HPos) → XD s) :
    ∑ s ∈ valSet Finset.univ, ((srcFH nB c Good y s v).card : ℝ≥0∞) *
        (Fintype.card (XD s) : ℝ≥0∞)⁻¹ ≤ (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [valSet, Finset.sum_map]
  exact sum_srcF_weight_le hG hloc y (valsOf v)

end pairs

/-! ## The sources of the template's hidden cells -/

section sources

/-- The hidden `h`-cells at `pub`, `v`: the `h`-cells of the in-table paths, on source-good
values. -/
def hidH (pub : Pub) (v : (s : HPos) → XD s) : Set Z :=
  goodCells (nBlk pub.seed) (sCellZ pub.xw pub.keys.1) (SrcGood pub.xw pub.keys.1) (valsOf v)

/-- The hidden `k`-cells. -/
def hidK (pub : Pub) (v : (s : HPos) → XD s) : Set X :=
  goodCells (nBlk pub.seed) (sCellK pub.xw pub.keys.1) (SrcGood pub.xw pub.keys.1) (valsOf v)

/-- The hidden `k'`-cells. -/
def hidK' (pub : Pub) (v : (s : HPos) → XD s) : Set X :=
  goodCells (nBlk pub.seed) (sCellR pub.xw pub.keys.1) (SrcGood pub.xw pub.keys.1) (valsOf v)

variable (M : Type) [Fintype M] [DecidableEq M]

/-- **The sources of the template's hidden cells** on the states of `SlotInv` (Masses' `Sources`,
`κ = |Digest|⁻¹ = 2^-128`): a hidden cell that is not hardwired is a cell of an in-table slot
whose designated source is undisclosed (`SlotInv`), and on source-good values it names at most one
pair (designated source, value). Only the value coordinates are sources. -/
noncomputable def sourcesSlotInv (pub : Pub) :
    Sources X Z HPos M HPos XD (fun r ↦ r.2.2.1) (SlotInv M pub) (hidH pub) (hidK pub)
      (hidK' pub) (Fintype.card Digest : ℝ≥0∞)⁻¹ where
  sh _ _ := valSet Finset.univ
  sk _ _ := valSet Finset.univ
  sk' _ _ := valSet Finset.univ
  Fh z _ s v := srcFH (nBlk pub.seed) (sCellZ pub.xw pub.keys.1) (SrcGood pub.xw pub.keys.1) z s v
  Fk y _ s v := srcFH (nBlk pub.seed) (sCellK pub.xw pub.keys.1) (SrcGood pub.xw pub.keys.1) y s v
  Fk' y _ s v := srcFH (nBlk pub.seed) (sCellR pub.xw pub.keys.1) (SrcGood pub.xw pub.keys.1) y s v
  hFh z _ s v d := srcFH_update _ z v s d
  hFk y _ s v d := srcFH_update _ y v s d
  hFk' y _ s v d := srcFH_update _ y v s d
  hh _ _ r hI hz hn := exists_mem_srcFH (P := fun z ↦ r.2.1.1 z ≠ none) hz
    (fun s hs hm j hj ↦ (hI s hs _ (isInput_dsrc hs) hm j hj).2.2) fun h ↦ h hn
  hk _ _ r hI hy hn := exists_mem_srcFH (P := fun y ↦ r.2.1.2.1 y ≠ none) hy
    (fun s hs hm j hj ↦ (hI s hs _ (isInput_dsrc hs) hm j hj).1) fun h ↦ h hn
  hk' _ _ r hI hy hn := exists_mem_srcFH (P := fun y ↦ r.2.1.2.2 y ≠ none) hy
    (fun s hs hm j hj ↦ (hI s hs _ (isInput_dsrc hs) hm j hj).2.1) fun h ↦ h hn
  hκh z _ v := sum_srcFH_weight_le (fun _ h ↦ h.2.2)
    (fun _ hs _ _ h j ↦ sCellZ_congr_isInput _ _ hs h j) z v
  hκk y _ v := sum_srcFH_weight_le (fun _ h ↦ h.1)
    (fun _ hs _ _ h j ↦ sCellK_congr_isInput _ _ hs h j) y v
  hκk' y _ v := sum_srcFH_weight_le (fun _ h ↦ h.2.1)
    (fun _ hs _ _ h j ↦ sCellR_congr_isInput _ _ hs h j) y v

theorem card_digest_inv : (Fintype.card Digest : ℝ≥0∞)⁻¹ = (2 ^ 128 : ℝ≥0∞)⁻¹ := by
  rw [card_digest]
  norm_num

end sources

/-! ## The never-revealed part with `sOf = SK.seed` -/

section seedK

variable {W : Type} [Fintype W]

/-- **`SK.seed` in a never-revealed part** `(SK.seed, SK.prf)`, SeedStage's slots, the rest `W`
(ReparamFull's `KK`). -/
def skOf (k : Secret × (SeedKS × W)) : MasterSeed :=
  k.1.1

/-- The `SK.seed`-keyed paths' capacities over SeedStage's slots in the never-revealed part. -/
def seedHK (p : PP) (k : Secret × (SeedKS × W)) : Set Z :=
  seedHSlots (pubP p).perm (pubP p).seed (skOf k) k.2.1

/-- The `SK.seed`-keyed paths' rates over SeedStage's slots (on a `PermGood π 18`). -/
def seedK'K (p : PP) (k : Secret × (SeedKS × W)) : Set X :=
  seedK'Slots 18 (pubP p).perm (pubP p).seed (skOf k) k.2.1

/-- **A point is an `SK.seed`-keyed path capacity** for at most `seedEps 18 ≤ 2^-463` of the
never-revealed part. -/
theorem sum_indicator_seedHK_le (p : PP) (z : Z) :
    ∑ k : Secret × (SeedKS × W), (seedHK p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤
      seedEps 18 * Fintype.card (Secret × (SeedKS × W)) :=
  sum_indicator_seedHSlots_le (K := Secret) (W := W) (fun s ↦ s.1) 18 _ _ z

/-- **A point is an `SK.seed`-keyed path rate** for at most `seedEps 18` of the never-revealed
part. -/
theorem sum_indicator_seedK'K_le (p : PP) (x : X) :
    ∑ k : Secret × (SeedKS × W), (seedK'K p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤
      seedEps 18 * Fintype.card (Secret × (SeedKS × W)) :=
  sum_indicator_seedK'Slots_le (K := Secret) (W := W) (fun s ↦ s.1) 18 _ _ x

end seedK

/-! ## The good set and its bad fraction -/

section good

/-- Source goodness at the template data, with a static condition `S`. -/
def SrcS (S : PP → ((s : HPos) → XD s) → Prop) (p : PP) (v : (s : HPos) → XD s) : Prop :=
  SrcGood (pubP p).xw (pubP p).keys.1 (valsOf v) ∧ S p v

/-- **The good set of the masses**: ReparamFull's good set with source goodness added to the static
condition. -/
def MassG (S : PP → ((s : HPos) → XD s) → Prop) (t : FT) : Prop :=
  FullG (SrcS S) t

open scoped Classical in
/-- The bad fraction of the masses' good set. -/
noncomputable def massGFrac (S : PP → ((s : HPos) → XD s) → Prop) : ℝ≥0∞ :=
  (Fintype.card FT : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ ¬MassG S t).card

theorem srcGood_psiE_iff (y : YS) :
    SrcGood (pubP (psiE y).1).xw (pubP (psiE y).1).keys.1 (valsOf (psiE y).2.1) ↔
      SrcGood (eYP y).1.1.2 (eYP y).1.1.1 (eYP y).2 := by
  rw [pubP, sPub_xw, sPub_keys_fst]
  exact Iff.rfl

open scoped Classical in
/-- **The source-bad fraction on the coordinates**: at most `2^-277`. -/
theorem frac_srcGood_le :
    (Fintype.card YS : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : YS ↦
        ¬SrcGood (pubP (psiE y).1).xw (pubP (psiE y).1).keys.1 (valsOf (psiE y).2.1)).card ≤
      ENNReal.ofReal (1 / 2 ^ 277) := by
  have hf : (Finset.univ.filter fun y : YS ↦
      ¬SrcGood (pubP (psiE y).1).xw (pubP (psiE y).1).keys.1 (valsOf (psiE y).2.1)) =
      Finset.univ.filter fun y : YS ↦ ¬SrcGood (eYP y).1.1.2 (eYP y).1.1.1 (eYP y).2 :=
    Finset.filter_congr fun y _ ↦ by rw [srcGood_psiE_iff]
  rw [hf, frac_comp_equiv eYP (fun x ↦ ¬SrcGood x.1.1.2 x.1.1.1 x.2)]
  exact srcBad_frac_le_keccak RestF

open scoped Classical in
/-- **The bad fraction of the masses' good set**: for any bound `fullGFrac` of ReparamFull's bad
fraction beside its static condition (`fullG_frac_le_keccak`), `fullGFrac`, SrcBad's `2^-277` and
the static condition's fraction of the coordinates. -/
theorem goodT_posM_bad_frac_le (S : PP → ((s : HPos) → XD s) → Prop) {fullGFrac : ℝ≥0∞}
    (hfull : (Fintype.card FT : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ ¬FullG (SrcS S) t).card ≤
      fullGFrac + (Fintype.card YS : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : YS ↦ ¬SrcS S (psiE y).1 (psiE y).2.1).card) :
    massGFrac S ≤ fullGFrac + ENNReal.ofReal (1 / 2 ^ 277) +
      (Fintype.card YS : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : YS ↦ ¬S (psiE y).1 (psiE y).2.1).card := by
  have h4 : (Fintype.card YS : ℝ≥0∞)⁻¹ *
      (Finset.univ.filter fun y : YS ↦ ¬SrcS S (psiE y).1 (psiE y).2.1).card ≤
      (Fintype.card YS : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : YS ↦
        ¬SrcGood (pubP (psiE y).1).xw (pubP (psiE y).1).keys.1 (valsOf (psiE y).2.1)).card +
      (Fintype.card YS : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : YS ↦ ¬S (psiE y).1 (psiE y).2.1).card := by
    rw [← mul_add]
    gcongr
    exact_mod_cast card_filter_le_add_of_imp _ _ _ fun y hy ↦ by
      by_cases hg : SrcGood (pubP (psiE y).1).xw (pubP (psiE y).1).keys.1 (valsOf (psiE y).2.1)
      · exact Or.inr fun hS ↦ hy ⟨hg, hS⟩
      · exact Or.inl hg
  refine hfull.trans ?_
  rw [add_assoc]
  exact add_le_add le_rfl (h4.trans (add_le_add frac_srcGood_le le_rfl))

open scoped Classical in
/-- **The bad fraction at Keccak's sizes** (with ReparamFull's current `fullG_frac_le_keccak`):
`2^-197 + 2^-400 + 2^-277` and the static condition's fraction. -/
theorem goodT_posM_bad_frac_le_keccak (S : PP → ((s : HPos) → XD s) → Prop) :
    massGFrac S ≤ ENNReal.ofReal (1 / 2 ^ 197) + ENNReal.ofReal (1 / 2 ^ 400) +
      ENNReal.ofReal (1 / 2 ^ 277) + (Fintype.card YS : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : YS ↦ ¬S (psiE y).1 (psiE y).2.1).card :=
  goodT_posM_bad_frac_le S (fullG_frac_le_keccak (SrcS S))

end good

/-! ## The table's path cells are the template's at the reparametrized data -/

section transfer

/-- The table's in-table paths' `h`-cells (the template's at `(pubOf L, valueAt L)`). -/
def tabPathH (L : HonestTable) : Set Z :=
  {z | ∃ s, InTable s ∧ ∃ j < nBlk (pubOf L).seed s,
    sCellZ (pubOf L).xw (pubOf L).keys.1 s (valsOf (valueAt L)) j = z}

/-- The table's in-table paths' `k`-cells. -/
def tabPathK (L : HonestTable) : Set X :=
  {x | ∃ s, InTable s ∧ ∃ j < nBlk (pubOf L).seed s,
    sCellK (pubOf L).xw (pubOf L).keys.1 s (valsOf (valueAt L)) j = x}

/-- The table's in-table paths' `k'`-cells. -/
def tabPathK' (L : HonestTable) : Set X :=
  {x | ∃ s, InTable s ∧ ∃ j < nBlk (pubOf L).seed s,
    sCellR (pubOf L).xw (pubOf L).keys.1 s (valsOf (valueAt L)) j = x}

theorem valsOf_trueV (L : HonestTable) (v : (s : HPos) → XD s) :
    valsOf (trueV L v) = valsOf v :=
  rfl

/-- A realized port of an absorption is a round's `k`-, `k'`- or `h`-cell. -/
theorem mem_pathCells_cases {pub : Pub} {b : ℕ → X} {cor : X → X → X} {n : ℕ} {c : HwProg X Z}
    (h : c ∈ pathCells pub b cor n) :
    ∃ j < n, c = .programK (cellK pub b j).1 (cellK pub b j).2 ∨
      c = .programK' (cellK' pub b j).1 (cellK' pub b j).2 ∨
      c = .programH (cellH pub b (n - 1) cor j).1 (cellH pub b (n - 1) cor j).2 := by
  simp only [pathCells, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at h
  exact h

/-- **Agreeing realized ports carry the same cells**: every cell of slot `s`'s path at `(pub, v)`
is a cell of its path at `(pub', v')`. -/
theorem cells_of_ports_eq {pub pub' : Pub} {v v' : (s : HPos) → XD s} {s : Slot} (hs : InTable s)
    (he : (slotPorts pub s).map (LazyProg.realize v) =
      (slotPorts pub' s).map (LazyProg.realize v'))
    {j : ℕ} (hj : j < nBlk pub.seed s) :
    (∃ j' < nBlk pub'.seed s,
      sCellK pub'.xw pub'.keys.1 s (valsOf v') j' = sCellK pub.xw pub.keys.1 s (valsOf v) j) ∧
    (∃ j' < nBlk pub'.seed s,
      sCellR pub'.xw pub'.keys.1 s (valsOf v') j' = sCellR pub.xw pub.keys.1 s (valsOf v) j) ∧
    (∃ j' < nBlk pub'.seed s,
      sCellZ pub'.xw pub'.keys.1 s (valsOf v') j' = sCellZ pub.xw pub.keys.1 s (valsOf v) j) := by
  rw [realize_slotPorts pub hs, realize_slotPorts pub' hs] at he
  obtain ⟨m1, m2, m3⟩ := mem_pathCells_round pub (slotBlk pub.seed s (valsOf v))
    (cor128 (valsOf v (slotOutPos s))) hj
  rw [he] at m1 m2 m3
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨j', hj', h | h | h⟩ := mem_pathCells_cases m1
    · exact ⟨j', hj', (HwProg.programK.inj h).1.symm⟩
    · cases h
    · cases h
  · obtain ⟨j', hj', h | h | h⟩ := mem_pathCells_cases m2
    · cases h
    · exact ⟨j', hj', (HwProg.programK'.inj h).1.symm⟩
    · cases h
  · obtain ⟨j', hj', h | h | h⟩ := mem_pathCells_cases m3
    · cases h
    · cases h
    · have e := (HwProg.programH.inj h).1
      rw [cellH_fst, cellH_fst] at e
      exact ⟨j', hj', e.symm⟩

/-- **`hsub` for the in-table paths**: on the good set, the table's path cells lie in the
template's hidden sets at the reparametrized data (`slotPorts_agree`, source goodness). -/
theorem tabPaths_subset_hid {S : PP → ((s : HPos) → XD s) → Prop} {t : FT} (ht : MassG S t) :
    tabPathH (tabOf t) ⊆ hidH (pubP (fullE t).1) (fullE t).2.1 ∧
      tabPathK (tabOf t) ⊆ hidK (pubP (fullE t).1) (fullE t).2.1 ∧
      tabPathK' (tabOf t) ⊆ hidK' (pubP (fullE t).1) (fullE t).2.1 := by
  have hsrc := ht.2.2.1
  have hD := fullD_of_core ht.1
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, j, hj, rfl⟩
    obtain ⟨j', hj', e⟩ := (cells_of_ports_eq hs (slotPorts_agree hD hs) hj).2.2
    rw [valsOf_trueV] at e
    exact ⟨hsrc, s, hs, j', hj', e⟩
  · rintro _ ⟨s, hs, j, hj, rfl⟩
    obtain ⟨j', hj', e⟩ := (cells_of_ports_eq hs (slotPorts_agree hD hs) hj).1
    rw [valsOf_trueV] at e
    exact ⟨hsrc, s, hs, j', hj', e⟩
  · rintro _ ⟨s, hs, j, hj, rfl⟩
    obtain ⟨j', hj', e⟩ := (cells_of_ports_eq hs (slotPorts_agree hD hs) hj).2.1
    rw [valsOf_trueV] at e
    exact ⟨hsrc, s, hs, j', hj', e⟩

end transfer

/-! ## The average through the reparametrization, with a mismatch term -/

section avg

/-- **The average through an injection on a good set, with a mismatch term.** The finite type `Θ`
is mapped by `e` into public data `P`, hidden values `V` and a never-revealed part `K`, injectively
on the good set `G`, with `|P| |V × K| ≤ |Θ|`. If `f ≤ a + b + N r` on `G` (`a` of the public datum
and the hidden values, `b` also of the never-revealed part), `f ≤ N` off `G`, and per public datum
`a` sums over `V` to at most `N κ |V|` and `b` over `K` to at most `N εK |K|`, then the average of
`f` is at most `N (κ + εK)`, plus `N` times the average of `r` over `G`, plus `N` times the bad
fraction. -/
theorem avg_le_of_injOn_mismatch {Θ P V K : Type*} [Fintype Θ] [Fintype P] [Fintype V]
    [Fintype K] (e : Θ → P × (V × K)) (G : Θ → Prop) [DecidablePred G]
    (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card P * Fintype.card (V × K) ≤ Fintype.card Θ)
    (f r : Θ → ℝ≥0∞) (a : P → V → ℝ≥0∞) (b : P → V → K → ℝ≥0∞) (N : ℝ≥0∞)
    (hfg : ∀ t, G t → f t ≤ a (e t).1 (e t).2.1 + b (e t).1 (e t).2.1 (e t).2.2 + N * r t)
    (hf : ∀ t, ¬G t → f t ≤ N) (κ εK : ℝ≥0∞)
    (ha : ∀ p, ∑ v, a p v ≤ N * κ * Fintype.card V)
    (hb : ∀ p v, ∑ k, b p v k ≤ N * εK * Fintype.card K) :
    (Fintype.card Θ : ℝ≥0∞)⁻¹ * ∑ t, f t ≤
      N * (κ + εK) + N * ((Fintype.card Θ : ℝ≥0∞)⁻¹ * ∑ t, if G t then r t else 0) +
        N * ((Fintype.card Θ : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ ¬G t).card) := by
  classical
  set n : ℝ≥0∞ := (Fintype.card Θ : ℝ≥0∞) with hn
  let g : P × (V × K) → ℝ≥0∞ := fun y ↦ a y.1 y.2.1 + b y.1 y.2.1 y.2.2
  have hgsum : ∀ p, ∑ w : V × K, g (p, w) ≤ N * (κ + εK) * Fintype.card (V × K) := fun p ↦ by
    calc ∑ w : V × K, g (p, w) = ∑ v, ∑ k, (a p v + b p v k) := Fintype.sum_prod_type _
      _ = ∑ v, ((Fintype.card K : ℝ≥0∞) * a p v + ∑ k, b p v k) := by
          refine Finset.sum_congr rfl fun v _ ↦ ?_
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ v, ((Fintype.card K : ℝ≥0∞) * a p v + N * εK * Fintype.card K) :=
          Finset.sum_le_sum fun v _ ↦ add_le_add le_rfl (hb p v)
      _ = (Fintype.card K : ℝ≥0∞) * ∑ v, a p v +
            Fintype.card V * (N * εK * Fintype.card K) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
      _ ≤ (Fintype.card K : ℝ≥0∞) * (N * κ * Fintype.card V) +
            Fintype.card V * (N * εK * Fintype.card K) :=
          add_le_add (mul_le_mul_of_nonneg_left (ha p) zero_le) le_rfl
      _ = N * (κ + εK) * Fintype.card (V × K) := by
          rw [Fintype.card_prod, Nat.cast_mul]
          ring
  have hgood : ∑ t ∈ Finset.univ.filter G, g (e t) ≤ N * (κ + εK) * n := by
    have himg : ∑ t ∈ Finset.univ.filter G, g (e t) =
        ∑ y ∈ (Finset.univ.filter G).image e, g y := by
      refine (Finset.sum_image (f := g) ?_).symm
      intro x hx y hy h
      exact hinj (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
        (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2 h
    calc ∑ t ∈ Finset.univ.filter G, g (e t)
        ≤ ∑ y : P × (V × K), g y := by
          rw [himg]
          exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = ∑ p, ∑ w : V × K, g (p, w) := Fintype.sum_prod_type _
      _ ≤ ∑ _p : P, N * (κ + εK) * Fintype.card (V × K) := Finset.sum_le_sum fun p _ ↦ hgsum p
      _ = N * (κ + εK) * ((Fintype.card P : ℝ≥0∞) * Fintype.card (V × K)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
      _ ≤ N * (κ + εK) * n := mul_le_mul_of_nonneg_left
          (by rw [hn, ← Nat.cast_mul]; exact Nat.cast_le.mpr hcard) zero_le
  have h1 : ∑ t ∈ Finset.univ.filter G, f t ≤
      ∑ t ∈ Finset.univ.filter G, g (e t) + N * ∑ t, (if G t then r t else 0) := by
    rw [← Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun t ht ↦ hfg t (Finset.mem_filter.mp ht).2
  have h2 : ∑ t ∈ Finset.univ.filter (fun t ↦ ¬G t), f t ≤
      (Finset.univ.filter fun t ↦ ¬G t).card * N :=
    calc ∑ t ∈ Finset.univ.filter (fun t ↦ ¬G t), f t
        ≤ ∑ _t ∈ Finset.univ.filter (fun t ↦ ¬G t), N :=
          Finset.sum_le_sum fun t ht ↦ hf t (Finset.mem_filter.mp ht).2
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hn1 : n⁻¹ * n ≤ 1 := by
    by_cases h0 : n = 0
    · simp [h0]
    · rw [ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top _)]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ G]
  calc n⁻¹ * (∑ t ∈ Finset.univ.filter G, f t + ∑ t ∈ Finset.univ.filter (fun t ↦ ¬G t), f t)
      ≤ n⁻¹ * (N * (κ + εK) * n + N * ∑ t, (if G t then r t else 0) +
          (Finset.univ.filter fun t ↦ ¬G t).card * N) :=
        mul_le_mul_of_nonneg_left (add_le_add (h1.trans (add_le_add hgood le_rfl)) h2) zero_le
    _ = N * (κ + εK) * (n⁻¹ * n) + N * (n⁻¹ * ∑ t, if G t then r t else 0) +
          N * (n⁻¹ * (Finset.univ.filter fun t ↦ ¬G t).card) := by ring
    _ ≤ _ := add_le_add (add_le_add
        ((mul_le_mul_of_nonneg_left hn1 zero_le).trans_eq (mul_one _)) le_rfl) le_rfl

/-- The padded tables beside the honest table. -/
abbrev FE : Type :=
  SeedSlots × CoinSlots Message × CoinSlots Hybrid.DLab × SeedKS × (ValPos → Digest) × StrPad

open scoped Classical in
noncomputable instance instFintypeFE : Fintype FE :=
  inferInstanceAs (Fintype (SeedSlots × CoinSlots Message × CoinSlots Hybrid.DLab × SeedKS ×
    (ValPos → Digest) × StrPad))

instance instNonemptyFE : Nonempty FE :=
  ⟨Classical.arbitrary _⟩

/-- The padded tables as the honest table and the rest. -/
def ftSplit : FT ≃ HonestTable × FE where
  toFun t := (t.1.1.1.1.1.1, (t.1.1.1.1.1.2, t.1.1.1.1.2, t.1.1.1.2, t.1.1.2, t.1.2, t.2))
  invFun x := ((((((x.1, x.2.1), x.2.2.1), x.2.2.2.1), x.2.2.2.2.1), x.2.2.2.2.2.1),
    x.2.2.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Averages over the padded tables of a function of the table** are table averages. -/
theorem uavg_tabOf (F : HonestTable → ℝ≥0∞) : uavg (fun t : FT ↦ F (tabOf t)) = uavg F := by
  have h : uavg (fun t : FT ↦ F (tabOf t)) = uavg (fun x : HonestTable × FE ↦ F x.1) := by
    rw [uavg, uavg, Fintype.card_congr ftSplit]
    exact congrArg _ (Equiv.sum_comp ftSplit (fun x : HonestTable × FE ↦ F x.1))
  rw [h]
  exact uavg_pad F

end avg

/-! ## The averaged hidden masses -/

section masses

variable (Q : (recHwSpec X Z HPos Selections).Port → Prop) [DecidablePred Q] (A : SAdversary)
  (ρ : Matrix (QReg.of Unit × QReg.of (HwReg X Z (Mem HPos)))
    (QReg.of Unit × QReg.of (HwReg X Z (Mem HPos))) ℂ)

/-- The first-meeting record mass of the charged coordinates read off the reparametrized data
(`chgBK`, ChgRev's `revFirst`). -/
noncomputable def chgRev (t : FT) : ℝ≥0∞ :=
  revFirst m0R LocalSig.Interp.instruments (chgBK (fullE t))
    (gameR msgPol A (pubP (fullE t).1) (fullE t).2.1) ρ

open scoped Classical in
/-- **The mismatch term**: the first-meeting record mass of the charged coordinates `chgBK` in the
canonical game at the reparametrized data, averaged over the padded tables of the good set (`0`
elsewhere). -/
noncomputable def chgRevAvg (S : PP → ((s : HPos) → XD s) → Prop) : ℝ≥0∞ :=
  (Fintype.card FT : ℝ≥0∞)⁻¹ * ∑ t, if MassG S t then chgRev A ρ t else 0

/-- The hidden mass of the template's hidden sets. -/
noncomputable def massA (p : PP) (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight LocalSig.Interp.instruments
    (portMass Q (hidH (pubP p) v) (hidK (pubP p) v) (hidK' (pubP p) v))
    (gameR msgPol A (pubP p) v) ρ

/-- The hidden mass of the never-revealed part's hidden sets. -/
noncomputable def massB (Hhk : PP → KK → Set Z) (Hkk Hk'k : PP → KK → Set X) (p : PP)
    (v : (s : HPos) → XD s) (k : KK) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight LocalSig.Interp.instruments
    (portMass Q (Hhk p k) (Hkk p k) (Hk'k p k)) (gameR msgPol A (pubP p) v) ρ

/-- **On the good set, Mismatch**: the mass at the table is at most the template's and the never
revealed part's masses at the reparametrized data plus `N` times the charged record mass. -/
theorem mass_le_mismatch (hρ : ρ.PosSemidef)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Mem HPos)) ↦ p.2.2.2.1)
      {∅} ρ)
    (S : PP → ((s : HPos) → XD s) → Prop)
    (Hh : HonestTable → Set Z) (Hk Hk' : HonestTable → Set X)
    (Hhk : PP → KK → Set Z) (Hkk Hk'k : PP → KK → Set X)
    (hsub : ∀ t, MassG S t →
      Hh (tabOf t) ⊆ hidH (pubP (fullE t).1) (fullE t).2.1 ∪ Hhk (fullE t).1 (fullE t).2.2 ∧
      Hk (tabOf t) ⊆ hidK (pubP (fullE t).1) (fullE t).2.1 ∪ Hkk (fullE t).1 (fullE t).2.2 ∧
      Hk' (tabOf t) ⊆ hidK' (pubP (fullE t).1) (fullE t).2.1 ∪ Hk'k (fullE t).1 (fullE t).2.2)
    {N : ℕ} (hN : ∀ (pub : Pub) (v : (s : HPos) → XD s),
      IFreeM.IsChargeBound (gameR msgPol A pub v) (portCharge fun i ↦ if Q i then 1 else 0) N)
    (t : FT) (ht : MassG S t) :
    (runtimeR m0R).totalWeight LocalSig.Interp.instruments
        (portMass Q (Hh (tabOf t)) (Hk (tabOf t)) (Hk' (tabOf t)))
        (gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t))) ρ ≤
      massA Q A ρ (fullE t).1 (fullE t).2.1 +
        massB Q A ρ Hhk Hkk Hk'k (fullE t).1 (fullE t).2.1 (fullE t).2.2 + N * chgRev A ρ t := by
  obtain ⟨v, hv, hgeq⟩ := ((fullE_spec (SrcS S) A).2 t ht).1
  have hv' : Agree (Finset.univ \ chgBK (fullE t)) v (fullE t).2.1 :=
    hv.mono (Finset.sdiff_subset_sdiff le_rfl (chgB_subset_chgBK (fullD_of_core ht.1)))
  obtain ⟨h1, h2, h3⟩ := hsub t ht
  refine (le_of_eq (congrArg (fun x ↦ (runtimeR m0R).totalWeight LocalSig.Interp.instruments
    (portMass Q (Hh (tabOf t)) (Hk (tabOf t)) (Hk' (tabOf t))) x ρ) hgeq)).trans
    ((totalWeight_portMass_le_mismatch_first m0R LocalSig.Interp.instruments
    (gameT Selections cwUpd msgPol (pubP (fullE t).1) A)
    (disc_gameT Selections cwUpd msgPol _ A ∅) (keepsLab_gameT Selections cwUpd msgPol _ A) ρ hρ
    hs (chgBK (fullE t)) (Finset.disjoint_empty_left _) Q (Hh (tabOf t)) (Hk (tabOf t))
    (Hk' (tabOf t)) hv' (hN _ v)).trans (add_le_add ?_ le_rfl))
  exact (totalWeight_portMass_mono _ Q m0R h1 h2 h3 _ hρ).trans
    (totalWeight_portMass_union_le _ Q m0R _ _ _ _ _ _ _ hρ)

/-- **The per-table mismatch step**: on the good set, the port mass at the table is at most the
port mass at the reparametrized data plus `N` times the charged first-meeting record mass. -/
theorem mass_le_chgRev (hρ : ρ.PosSemidef)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Mem HPos)) ↦ p.2.2.2.1)
      {∅} ρ)
    (S : PP → ((s : HPos) → XD s) → Prop)
    {N : ℕ} (hN : ∀ (pub : Pub) (v : (s : HPos) → XD s),
      IFreeM.IsChargeBound (gameR msgPol A pub v) (portCharge fun i ↦ if Q i then 1 else 0) N)
    (t : FT) (ht : MassG S t) (Hh : Set Z) (Hk Hk' : Set X) :
    (runtimeR m0R).totalWeight LocalSig.Interp.instruments (portMass Q Hh Hk Hk')
        (gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t))) ρ ≤
      (runtimeR m0R).totalWeight LocalSig.Interp.instruments (portMass Q Hh Hk Hk')
        (gameR msgPol A (pubP (fullE t).1) (fullE t).2.1) ρ + N * chgRev A ρ t := by
  obtain ⟨v, hv, hgeq⟩ := ((fullE_spec (SrcS S) A).2 t ht).1
  have hv' : Agree (Finset.univ \ chgBK (fullE t)) v (fullE t).2.1 :=
    hv.mono (Finset.sdiff_subset_sdiff le_rfl (chgB_subset_chgBK (fullD_of_core ht.1)))
  rw [hgeq]
  exact totalWeight_portMass_le_mismatch_first m0R LocalSig.Interp.instruments
    (gameT Selections cwUpd msgPol (pubP (fullE t).1) A)
    (disc_gameT Selections cwUpd msgPol _ A ∅) (keepsLab_gameT Selections cwUpd msgPol _ A) ρ hρ
    hs (chgBK (fullE t)) (Finset.disjoint_empty_left _) Q Hh Hk Hk' hv' (hN _ v)

/-- Every mass is at most the number of calls. -/
theorem mass_le_calls (hρ : ρ.PosSemidef) (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (Hh₀ : Set Z) (Hk₀ Hk'₀ : Set X)
    {N : ℕ} (hN : ∀ (pub : Pub) (v : (s : HPos) → XD s),
      IFreeM.IsChargeBound (gameR msgPol A pub v) (portCharge fun i ↦ if Q i then 1 else 0) N)
    (pub : Pub) (v : (s : HPos) → XD s) :
    (runtimeR m0R).totalWeight LocalSig.Interp.instruments (portMass Q Hh₀ Hk₀ Hk'₀)
      (gameR msgPol A pub v) ρ ≤ N :=
  (totalWeight_portMass_le _ Q m0R _ _ _ _ hρ (hN _ _)).trans
    ((mul_le_mul_of_nonneg_left hρ1 zero_le).trans_eq (mul_one _))

/-- **The template's hidden masses** sum over the hidden values to at most `N κ |V|`
(`sourcesSlotInv`, GameTCalls' invariant). -/
theorem sum_massA_le (hQ : ∀ c, ¬Q (.inl (.inr c))) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Mem HPos)) ↦ p.2.2.2.1)
      {∅} ρ)
    {N : ℕ} (hN : ∀ (pub : Pub) (v : (s : HPos) → XD s),
      IFreeM.IsChargeBound (gameR msgPol A pub v) (portCharge fun i ↦ if Q i then 1 else 0) N)
    (p : PP) :
    ∑ v, massA Q A ρ p v ≤
      N * (Fintype.card Digest : ℝ≥0∞)⁻¹ * Fintype.card ((s : HPos) → XD s) := by
  refine (sum_totalWeight_portMass_runtimeR_le_inv LocalSig.Interp.instruments Q m0R
    (fun r ↦ r.2.2.1) (fun v ↦ gameR msgPol A (pubP p) v) (fun _ ↦ ρ) (fun _ ↦ hρ)
    (fun j ↦ viewByOn_gameT Selections cwUpd msgPol (pubP p) A m0R ρ j)
    (SlotInv Selections (pubP p))
    (fun v ↦ forallQueries_gameT cwUpd valFree_msgPol hQ m0R (pubP p) A v ρ hs)
    (hidH (pubP p)) (hidK (pubP p)) (hidK' (pubP p)) _ (sourcesSlotInv Selections (pubP p))
    (fun v ↦ hN (pubP p) v)).trans ?_
  calc (Fintype.card Digest : ℝ≥0∞)⁻¹ *
        (N * ∑ _v : (s : HPos) → XD s, ENNReal.ofReal ρ.trace.re)
      ≤ (Fintype.card Digest : ℝ≥0∞)⁻¹ * (N * ∑ _v : (s : HPos) → XD s, (1 : ℝ≥0∞)) := by
        gcongr
    _ = N * (Fintype.card Digest : ℝ≥0∞)⁻¹ * Fintype.card ((s : HPos) → XD s) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        ring

/-- **The never-revealed part's hidden masses** sum over it to at most `N εK |K|`. -/
theorem sum_massB_le (hρ : ρ.PosSemidef) (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (Hhk : PP → KK → Set Z) (Hkk Hk'k : PP → KK → Set X) (εK : ℝ≥0∞)
    (hcH : ∀ p z, ∑ k, (Hhk p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤ εK * Fintype.card KK)
    (hcK : ∀ p y, ∑ k, (Hkk p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤ εK * Fintype.card KK)
    (hcK' : ∀ p y, ∑ k, (Hk'k p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤ εK * Fintype.card KK)
    {N : ℕ} (hN : ∀ (pub : Pub) (v : (s : HPos) → XD s),
      IFreeM.IsChargeBound (gameR msgPol A pub v) (portCharge fun i ↦ if Q i then 1 else 0) N)
    (p : PP) (v : (s : HPos) → XD s) :
    ∑ k, massB Q A ρ Hhk Hkk Hk'k p v k ≤ N * εK * Fintype.card KK := by
  refine (sum_totalWeight_portMass_le_count LocalSig.Interp.instruments Q m0R _ hρ (Hhk p)
    (Hkk p) (Hk'k p) εK (hcH p) (hcK p) (hcK' p) (hN _ v)).trans ?_
  calc (εK * Fintype.card KK) * (N * ENNReal.ofReal ρ.trace.re)
      ≤ (εK * Fintype.card KK) * (N * 1) := by gcongr
    _ = N * εK * Fintype.card KK := by ring

/-- `card_coords` at the product instance of the hidden values and the never-revealed part. -/
theorem card_coords_le :
    Fintype.card PP * @Fintype.card (((s : HPos) → XD s) × KK)
      (@instFintypeProd _ _ instFintypeHidVals instFintypeKK) ≤ Fintype.card FT := by
  rw [← Fintype.card_prod]
  exact (Fintype.card_congr coordEquiv).le

open scoped Classical in
/-- **The averaged total hidden mass at the ports `Q` of the canonical game at `msgPol`**, over
the padded tables. The ports `Q` are not program ports and are called at most `N` times. On the
good set `MassG S` the table's hidden sets lie in the template's (`hidH`, with the sources
`sourcesSlotInv`) united with sets of the public datum and the never-revealed part, each point in
these for at most `εK` of `KK`. The game at the table is the game at the reparametrized data
realized at values agreeing off `chgB t` (`hgame_fullE`), paid by Mismatch's record mass. -/
theorem sum_totalWeight_portMass_le_sph (hQ : ∀ c, ¬Q (.inl (.inr c))) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Mem HPos)) ↦ p.2.2.2.1)
      {∅} ρ)
    (S : PP → ((s : HPos) → XD s) → Prop)
    (Hh : HonestTable → Set Z) (Hk Hk' : HonestTable → Set X)
    (Hhk : PP → KK → Set Z) (Hkk Hk'k : PP → KK → Set X)
    (hsub : ∀ t, MassG S t →
      Hh (tabOf t) ⊆ hidH (pubP (fullE t).1) (fullE t).2.1 ∪ Hhk (fullE t).1 (fullE t).2.2 ∧
      Hk (tabOf t) ⊆ hidK (pubP (fullE t).1) (fullE t).2.1 ∪ Hkk (fullE t).1 (fullE t).2.2 ∧
      Hk' (tabOf t) ⊆ hidK' (pubP (fullE t).1) (fullE t).2.1 ∪ Hk'k (fullE t).1 (fullE t).2.2)
    (εK : ℝ≥0∞)
    (hcH : ∀ p z, ∑ k, (Hhk p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤ εK * Fintype.card KK)
    (hcK : ∀ p y, ∑ k, (Hkk p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤ εK * Fintype.card KK)
    (hcK' : ∀ p y, ∑ k, (Hk'k p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤ εK * Fintype.card KK)
    {N : ℕ} (hN : ∀ (pub : Pub) (v : (s : HPos) → XD s),
      IFreeM.IsChargeBound (gameR msgPol A pub v) (portCharge fun i ↦ if Q i then 1 else 0) N) :
    uavg (fun t : FT ↦ (runtimeR m0R).totalWeight LocalSig.Interp.instruments
      (portMass Q (Hh (tabOf t)) (Hk (tabOf t)) (Hk' (tabOf t)))
        (gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t))) ρ) ≤
      N * ((Fintype.card Digest : ℝ≥0∞)⁻¹ + εK) + N * chgRevAvg A ρ S + N * massGFrac S :=
  @avg_le_of_injOn_mismatch FT PP ((s : HPos) → XD s) KK instFintypeFT instFintypePP
    instFintypeHidVals instFintypeKK fullE (MassG S) _ (fullE_spec (SrcS S) A).1
    card_coords_le _ (chgRev A ρ) (massA Q A ρ) (massB Q A ρ Hhk Hkk Hk'k) N
    (fun t ht ↦ mass_le_mismatch Q A ρ hρ hs S Hh Hk Hk' Hhk Hkk Hk'k hsub hN t ht)
    (fun _ _ ↦ mass_le_calls Q A ρ hρ hρ1 _ _ _ hN _ _) _ εK
    (sum_massA_le Q A ρ hQ hρ hρ1 hs hN)
    (sum_massB_le Q A ρ hρ hρ1 Hhk Hkk Hk'k εK hcH hcK hcK' hN)

open scoped Classical in
/-- **Masses' bound for leanSPHINCS** (the table average): at most
`N (2^-128 + εK) + N · chgRevAvg + N · massGFrac`. The bad fraction `massGFrac S` is bounded by
`goodT_posM_bad_frac_le`; the mismatch term `chgRevAvg A ρ S` by ChgRevAvg's `chgRevAvg_le`. -/
theorem uavg_totalWeight_portMass_le_sph (hQ : ∀ c, ¬Q (.inl (.inr c))) (hρ : ρ.PosSemidef)
    (hρ1 : ENNReal.ofReal ρ.trace.re ≤ 1)
    (hs : QuerySupportedOn (fun p : QReg.of Unit × QReg.of (HwReg X Z (Mem HPos)) ↦ p.2.2.2.1)
      {∅} ρ)
    (S : PP → ((s : HPos) → XD s) → Prop)
    (Hh : HonestTable → Set Z) (Hk Hk' : HonestTable → Set X)
    (Hhk : PP → KK → Set Z) (Hkk Hk'k : PP → KK → Set X)
    (hsub : ∀ t, MassG S t →
      Hh (tabOf t) ⊆ hidH (pubP (fullE t).1) (fullE t).2.1 ∪ Hhk (fullE t).1 (fullE t).2.2 ∧
      Hk (tabOf t) ⊆ hidK (pubP (fullE t).1) (fullE t).2.1 ∪ Hkk (fullE t).1 (fullE t).2.2 ∧
      Hk' (tabOf t) ⊆ hidK' (pubP (fullE t).1) (fullE t).2.1 ∪ Hk'k (fullE t).1 (fullE t).2.2)
    (εK : ℝ≥0∞)
    (hcH : ∀ p z, ∑ k, (Hhk p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) z ≤ εK * Fintype.card KK)
    (hcK : ∀ p y, ∑ k, (Hkk p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤ εK * Fintype.card KK)
    (hcK' : ∀ p y, ∑ k, (Hk'k p k).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ≤ εK * Fintype.card KK)
    {N : ℕ} (hN : ∀ (pub : Pub) (v : (s : HPos) → XD s),
      IFreeM.IsChargeBound (gameR msgPol A pub v) (portCharge fun i ↦ if Q i then 1 else 0) N) :
    uavg (fun L : HonestTable ↦ (runtimeR m0R).totalWeight LocalSig.Interp.instruments
      (portMass Q (Hh L) (Hk L) (Hk' L)) (gameR msgPol A (pubOf L) (valueAt L)) ρ) ≤
      N * ((2 ^ 128 : ℝ≥0∞)⁻¹ + εK) + N * chgRevAvg A ρ S + N * massGFrac S := by
  rw [← uavg_tabOf, ← card_digest_inv]
  exact sum_totalWeight_portMass_le_sph Q A ρ hQ hρ hρ1 hs S Hh Hk Hk' Hhk Hkk Hk'k hsub εK hcH
    hcK hcK' hN

end masses

end Quantum.Sphincs.Assembly

end
