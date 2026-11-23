module

public import Quantum.Qrom.Xmss.Costs.RecUMove

@[expose] public section

/-!
# The first reveals of the randomizer bases

At a first reveal of `{loC rnd}` (the base not yet in the memory label) the run before it does
not depend on the base `θ (loC rnd)` (`viewBy_runtimeR_of_disc`), so summed over the bases the
recorded trial cells of `rnd`'s search count each recorded cell once per trial: the first-reveal
charges are at most `2^32 / 2^128` times the recorded trial cells of `rnd` (Disclose's view lemma
with a weight per state, `sum_queryWeight_view_le_wt`). Those drop the potential `Ψ`.

* **Trial cells name their search** (`IsBlkQ`, `isBlkQ_unique`): a message-digest cell names its
  parameter, key and message, and a key and message name the randomizer position (`rndLab`).
* **The potential `Ψ`** (`revPotQ`): the recorded `h`-cells that are trial cells of a search whose
  base is unrevealed. It is one-cell Lipschitz, the searches' reads (whose base is revealed,
  `labInvQ`) and the programs do not raise it, and a first reveal of `rnd` lowers it by `rnd`'s
  recorded trial cells (`revDropQ`). Along the prefix the drops add up to at most the sponge
  calls `q` (`totalWeight_dropQW_le`).
* **The first reveals** (`sum_totalWeight_firstQW_le`): summed over the hidden values, at most
  `2^32 · q / 2^128` per hidden value.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Sponge HashSig LeanXmss
open Quantum.Xmss.Hybrid (diagMass setProj restrictTo ViewByOn lazy_const suppAt_empty
  totalWeight_le_totalWeight totalWeight_fintype_sum totalWeight_const_mul_weight
  totalWeight_chargeTrace_le sum_totalWeight_le_of_forall)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT extCls ModedP recKraus initU
  forallQueries_of_modedP totalWeight_le_potential_of_forallQueries tsum_potential_sponge_le
  tsum_potential_le_of_keep potential_basis_init potential_diagPot_sqrt kWt
  sum_queryWeight_view_le_wt viewBy_runtimeR_of_disc eq_of_recKraus_ne_zero
  querySupportedOn_traceRight)

attribute [local irreducible] xmssRom

/- Instance search for the register's decidable equality exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-! ## Trial cells name their search -/

/-- **A trial cell of `rnd`'s searches**: a message-digest cell of its key and message, under
any parameter and randomizer. -/
def IsBlkQ (rnd : Pos) (x : HashDomain) : Prop :=
  ∃ l e msg, rndLab rnd = some (l, e, msg) ∧
    ∃ (P : PublicParameter) (r : Randomizer), x = cell P (.msg l e) (msg, r)

theorem messageBytes_injective : Function.Injective messageBytes := fun _ _ h ↦
  littleEndianBytes_inj (n := 32) (congrArg Subtype.val h)

theorem rootBytes_injective : Function.Injective rootBytes := fun _ _ h ↦
  littleEndianBytes_inj (n := 16) (congrArg Subtype.val h)

theorem rndLab_injective {rnd rnd' : Pos} {k : Layer × KeyIndex × MsgBytes}
    (h : rndLab rnd = some k) (h' : rndLab rnd' = some k) : rnd = rnd' := by
  match rnd, rnd', h, h' with
  | .rndBottom e m, .rndBottom e' m', h, h' =>
    have h1 := Option.some.inj (h.trans h'.symm)
    rw [(Prod.mk.inj (Prod.mk.inj h1).2).1,
      messageBytes_injective (Prod.mk.inj (Prod.mk.inj h1).2).2]
  | .rndTop e r, .rndTop e' r', h, h' =>
    have h1 := Option.some.inj (h.trans h'.symm)
    rw [(Prod.mk.inj (Prod.mk.inj h1).2).1, rootBytes_injective (Prod.mk.inj (Prod.mk.inj h1).2).2]
  | .rndBottom _ _, .rndTop _ _, h, h' =>
    exact absurd (congrArg Prod.fst (Option.some.inj (h.trans h'.symm)))
      (show bottomLayer ≠ topLayer by decide)
  | .rndTop _ _, .rndBottom _ _, h, h' =>
    exact absurd (congrArg Prod.fst (Option.some.inj (h.trans h'.symm)))
      (show topLayer ≠ bottomLayer by decide)
  | .seed, _, h, _ => cases h
  | .param, _, h, _ => cases h
  | .prf .., _, h, _ => cases h
  | .chain .., _, h, _ => cases h
  | .leaf .., _, h, _ => cases h
  | .node .., _, h, _ => cases h
  | .rndBottom .., .seed, _, h' => cases h'
  | .rndBottom .., .param, _, h' => cases h'
  | .rndBottom .., .prf .., _, h' => cases h'
  | .rndBottom .., .chain .., _, h' => cases h'
  | .rndBottom .., .leaf .., _, h' => cases h'
  | .rndBottom .., .node .., _, h' => cases h'
  | .rndTop .., .seed, _, h' => cases h'
  | .rndTop .., .param, _, h' => cases h'
  | .rndTop .., .prf .., _, h' => cases h'
  | .rndTop .., .chain .., _, h' => cases h'
  | .rndTop .., .leaf .., _, h' => cases h'
  | .rndTop .., .node .., _, h' => cases h'

/-- A message-digest cell names its parameter. -/
theorem param_eq_of_cell_msg {P P' : PublicParameter} {l l' : Layer} {e e' : KeyIndex}
    {d : Payload (.msg l e)} {d' : Payload (.msg l' e')}
    (h : cell P (.msg l e) d = cell P' (.msg l' e') d') : P = P' := by
  have h1 : slotInput P (.msg l e) d = slotInput P' (.msg l' e') d' := by
    rw [← decodeInput_cell, h, decodeInput_cell]
  simp only [slotInput, thInput, hasherInput, List.append_assoc] at h1
  exact littleEndianBytes_inj (n := 16)
    (List.append_inj h1 (by simp only [littleEndianBytes, List.length_ofFn])).1

/-- **A trial cell names its search.** -/
theorem isBlkQ_unique {rnd rnd' : Pos} {x : HashDomain} (h : IsBlkQ rnd x)
    (h' : IsBlkQ rnd' x) : rnd = rnd' := by
  obtain ⟨l, e, msg, hr, P, r, rfl⟩ := h
  obtain ⟨l', e', msg', hr', P', r', he⟩ := h'
  obtain rfl := param_eq_of_cell_msg he
  have h1 := cell_injective P (s := .msg l e) (s' := .msg l' e') trivial trivial he
  obtain ⟨hs, hd⟩ := Sigma.mk.inj h1
  injection hs with hl he'
  subst hl he'
  have hm : msg = msg' := congrArg Prod.fst (eq_of_heq hd)
  subst hm
  exact rndLab_injective hr hr'

theorem isBlkQ_rndCell {rnd : Pos} {l : Layer} {e : KeyIndex} {msg : MsgBytes}
    (hr : rndLab rnd = some (l, e, msg)) (P : PublicParameter) (b : Randomizer) (j : ℕ) :
    IsBlkQ rnd (rndCell P rnd b j) := by
  rw [rndCell_eq hr]
  exact ⟨l, e, msg, hr, P, _, rfl⟩

theorem rndCell_base_inj {rnd : Pos} {l : Layer} {e : KeyIndex} {msg : MsgBytes}
    (hr : rndLab rnd = some (l, e, msg)) (P : PublicParameter) (j : ℕ) :
    Function.Injective fun b : Randomizer ↦ rndCell P rnd b j := by
  intro b b' h
  simp only [rndCell_eq hr] at h
  have h1 := cell_injective P (s := .msg l e) (s' := .msg l e) trivial trivial h
  have h2 : b + BitVec.ofNat digestBits j = b' + BitVec.ofNat digestBits j :=
    congrArg Prod.snd (eq_of_heq (Sigma.mk.inj h1).2)
  exact add_right_cancel h2

/-! ## The potential `Ψ` -/

open scoped Classical in
/-- The unrevealed randomizer positions (under the label `T`) of which `x` is a trial cell. -/
noncomputable def blkCntQ (T : Finset HPos) (x : HashDomain) : ℝ :=
  ∑ rnd : Pos, if loC rnd ∉ T ∧ IsBlkQ rnd x then 1 else 0

open scoped Classical in
/-- **The potential `Ψ`**: the recorded `h`-cells that are trial cells of unrevealed searches. -/
noncomputable def revPotQ (s : RReg SelMem) : ℝ :=
  ∑ x : HashDomain, if s.1.1 x ≠ none then blkCntQ s.2.2.1 x else 0

open scoped Classical in
/-- `Ψ` with the cell `z` counted as recorded. -/
noncomputable def revPotAtQ (z : HashDomain) (s : RReg SelMem) : ℝ :=
  ∑ x : HashDomain, if x = z then blkCntQ s.2.2.1 z else
    if s.1.1 x ≠ none then blkCntQ s.2.2.1 x else 0

open scoped Classical in
/-- The recorded trial cells of `rnd`'s search. -/
noncomputable def blkRecQ (rnd : Pos) (s : RReg SelMem) : ℕ :=
  (Finset.univ.filter fun x : HashDomain ↦ s.1.1 x ≠ none ∧ IsBlkQ rnd x).card

open scoped Classical in
/-- **The drop of `Ψ` at a first reveal of `rnd`**: its recorded trial cells. -/
noncomputable def revDropQ (rnd : Pos) (s : RReg SelMem) : ℝ :=
  if loC rnd ∈ s.2.2.1 then 0 else (blkRecQ rnd s : ℝ)

theorem blkCntQ_nonneg (T : Finset HPos) (x : HashDomain) : 0 ≤ blkCntQ T x :=
  Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num

theorem blkCntQ_le_one (T : Finset HPos) (x : HashDomain) : blkCntQ T x ≤ 1 := by
  classical
  unfold blkCntQ
  by_cases h : ∃ rnd, IsBlkQ rnd x
  · obtain ⟨r₀, hr₀⟩ := h
    rw [Finset.sum_eq_single r₀ (fun rnd _ hne ↦ ite_eq_right fun hc ↦
      hne (isBlkQ_unique hc.2 hr₀)) (fun h ↦ absurd (Finset.mem_univ _) h)]
    split_ifs <;> norm_num
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun rnd _ ↦ ite_eq_right fun hc ↦ h ⟨rnd, hc.2⟩)
      zero_le_one

theorem blkCntQ_eq_zero {T : Finset HPos} {rnd : Pos} {x : HashDomain} (hx : IsBlkQ rnd x)
    (hT : loC rnd ∈ T) : blkCntQ T x = 0 := by
  classical
  exact Finset.sum_eq_zero fun _ _ ↦ ite_eq_right fun hc ↦ hc.1 (isBlkQ_unique hx hc.2 ▸ hT)

theorem revPotQ_nonneg (s : RReg SelMem) : 0 ≤ revPotQ s :=
  Finset.sum_nonneg fun x _ ↦ by
    split_ifs
    · exact blkCntQ_nonneg _ x
    · exact le_rfl

theorem revPotQ_congr {s s' : RReg SelMem} (hk : s'.1.1 = s.1.1) (hl : s'.2.2.1 = s.2.2.1) :
    revPotQ s' = revPotQ s := by
  unfold revPotQ
  rw [hk, hl]

theorem revPotQ_le_revPotAtQ (z : HashDomain) (s : RReg SelMem) : revPotQ s ≤ revPotAtQ z s :=
  Finset.sum_le_sum fun x _ ↦ by
    by_cases hx : x = z
    · subst hx
      rw [ite_eq_left rfl]
      split_ifs
      · exact le_rfl
      · exact blkCntQ_nonneg _ x
    · rw [ite_eq_right hx]

theorem revPotAtQ_eq {z : HashDomain} {rnd : Pos} (hz : IsBlkQ rnd z) {s : RReg SelMem}
    (hs : loC rnd ∈ s.2.2.1) : revPotAtQ z s = revPotQ s :=
  Finset.sum_congr rfl fun x _ ↦ by
    by_cases hx : x = z
    · subst hx
      rw [ite_eq_left rfl, blkCntQ_eq_zero hz hs]
      split_ifs <;> rfl
    · rw [ite_eq_right hx]

theorem revPotAtQ_congr (z : HashDomain) {s s' : RReg SelMem}
    (hk : ∀ x, x ≠ z → s'.1.1 x = s.1.1 x) (hl : s'.2.2.1 = s.2.2.1) :
    revPotAtQ z s' = revPotAtQ z s :=
  Finset.sum_congr rfl fun x _ ↦ by
    rw [hl]
    by_cases hx : x = z
    · rw [ite_eq_left hx, ite_eq_left hx]
    · rw [ite_eq_right hx, ite_eq_right hx, hk x hx]

/-- **`Ψ` is one-cell Lipschitz.** -/
theorem oneCellLipschitz_revPotQ : OneCellLipschitz (X := HashOutput) (Z := HashDomain)
    (M := QMem) revPotQ where
  h D b z v := by
    classical
    set f : HashDomain → ℝ := fun x ↦ if D.1 x ≠ none then blkCntQ b.2.1 x else 0
    set f' : HashDomain → ℝ := fun x ↦
      if Function.update D.1 z v x ≠ none then blkCntQ b.2.1 x else 0
    have hd : ∑ x, (f' x - f x) = f' z - f z :=
      Finset.sum_eq_single z (fun x _ hx ↦ by simp [f, f', Function.update_of_ne hx])
        (fun h ↦ absurd (Finset.mem_univ z) h)
    have hf' : f' z ≤ 1 := by
      simp only [f']
      split_ifs
      · exact blkCntQ_le_one _ z
      · exact zero_le_one
    have hf : 0 ≤ f z := by
      simp only [f]
      split_ifs
      · exact blkCntQ_nonneg _ z
      · exact le_rfl
    show ∑ x, f' x ≤ ∑ x, f x + 1
    rw [Finset.sum_sub_distrib] at hd
    linarith
  k _ _ _ _ := le_of_eq_of_le (revPotQ_congr rfl rfl) (le_add_of_nonneg_right zero_le_one)
  k' _ _ _ _ := le_of_eq_of_le (revPotQ_congr rfl rfl) (le_add_of_nonneg_right zero_le_one)

/-- **A program does not raise `Ψ`**: it discards its cell from the databases. -/
theorem revPotQ_progMap_le (c : HwProg HashOutput HashDomain) (s : RReg SelMem) :
    revPotQ (progMap c s) ≤ revPotQ s := by
  obtain ⟨⟨dh, dk, dk'⟩, W, ⟨L, m⟩⟩ := s
  rcases c with ⟨z, w⟩ | ⟨x, w⟩ | ⟨x, w⟩
  · refine Finset.sum_le_sum fun y _ ↦ ?_
    show (if Function.update dh z none y ≠ none then blkCntQ L y else 0) ≤
      if dh y ≠ none then blkCntQ L y else 0
    by_cases hy : y = z
    · subst hy
      rw [Function.update_self, ite_eq_right (fun h ↦ h rfl)]
      split_ifs
      · exact blkCntQ_nonneg _ y
      · exact le_rfl
    · rw [Function.update_of_ne hy]
  · exact le_of_eq (revPotQ_congr rfl rfl)
  · exact le_of_eq (revPotQ_congr rfl rfl)

/-- The register after a record of `T`. -/
def recMapQ {X₁ Z₁ S₁ M₁ : Type} [DecidableEq S₁] (T : Finset S₁)
    (s : HwReg X₁ Z₁ (Finset S₁ × M₁)) : HwReg X₁ Z₁ (Finset S₁ × M₁) :=
  (s.1, s.2.1, (s.2.2.1 ∪ T, s.2.2.2))

theorem blkCntQ_union_le (T T' : Finset HPos) (x : HashDomain) :
    blkCntQ (T ∪ T') x ≤ blkCntQ T x :=
  Finset.sum_le_sum fun rnd _ ↦ by
    by_cases h : loC rnd ∉ T ∪ T' ∧ IsBlkQ rnd x
    · rw [ite_eq_left h, ite_eq_left ⟨fun hl ↦ h.1 (Finset.mem_union_left _ hl), h.2⟩]
    · rw [ite_eq_right h]
      split_ifs <;> norm_num

open scoped Classical in
theorem ind_add_blkCntQ_le {T : Finset HPos} {rnd : Pos} (hl : loC rnd ∉ T) (x : HashDomain) :
    (if IsBlkQ rnd x then (1 : ℝ) else 0) + blkCntQ (T ∪ {loC rnd}) x ≤ blkCntQ T x := by
  classical
  unfold blkCntQ
  have h1 : (if IsBlkQ rnd x then (1 : ℝ) else 0) =
      ∑ r : Pos, if r = rnd then (if loC r ∉ T ∧ IsBlkQ r x then 1 else 0) else 0 := by
    rw [Finset.sum_ite_eq' Finset.univ rnd, ite_eq_left (Finset.mem_univ _)]
    by_cases hb : IsBlkQ rnd x
    · rw [ite_eq_left hb, ite_eq_left ⟨hl, hb⟩]
    · rw [ite_eq_right hb, ite_eq_right fun h ↦ hb h.2]
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun r _ ↦ ?_
  by_cases hr : r = rnd
  · subst hr
    have h0 : ¬(loC r ∉ T ∪ {loC r} ∧ IsBlkQ r x) :=
      fun h ↦ h.1 (Finset.mem_union_right _ (Finset.mem_singleton_self _))
    rw [ite_eq_left rfl, ite_eq_right h0, add_zero]
  · rw [ite_eq_right hr, zero_add]
    by_cases h : loC r ∉ T ∪ {loC rnd} ∧ IsBlkQ r x
    · rw [ite_eq_left h, ite_eq_left ⟨fun hl' ↦ h.1 (Finset.mem_union_left _ hl'), h.2⟩]
    · rw [ite_eq_right h]
      split_ifs <;> norm_num

/-- The drop at a record of `T`: a first reveal's recorded trial cells, nothing otherwise. -/
noncomputable def revDropOQ (T : Finset HPos) (s : RReg SelMem) : ℝ :=
  match rndOfT T with
  | some rnd => revDropQ rnd s
  | none => 0

theorem revDropOQ_nonneg (T : Finset HPos) (s : RReg SelMem) : 0 ≤ revDropOQ T s := by
  unfold revDropOQ
  split
  · unfold revDropQ
    split_ifs
    · exact le_rfl
    · exact Nat.cast_nonneg _
  · exact le_rfl

/-- **A record drops `Ψ` by at least the first-reveal drop.** -/
theorem revDropOQ_add_le (T : Finset HPos) (s : RReg SelMem) :
    revDropOQ T s + revPotQ (recMapQ T s) ≤ revPotQ s := by
  classical
  obtain ⟨D, W, ⟨L, m⟩⟩ := s
  have hle : revPotQ (recMapQ T (D, W, (L, m))) ≤ revPotQ (D, W, (L, m)) :=
    Finset.sum_le_sum fun y _ ↦ by
      show (if D.1 y ≠ none then blkCntQ (L ∪ T) y else 0) ≤
        if D.1 y ≠ none then blkCntQ L y else 0
      split_ifs
      · exact blkCntQ_union_le L T y
      · exact le_rfl
  unfold revDropOQ
  rcases ho : rndOfT T with _ | rnd
  · rw [zero_add]
    exact hle
  · show revDropQ rnd (D, W, (L, m)) + _ ≤ _
    unfold revDropQ
    split_ifs with hl
    · rw [zero_add]
      exact hle
    · have hT : T = {loC rnd} := (rndOfT_spec ho).2
      subst hT
      show ((Finset.univ.filter fun y : HashDomain ↦ D.1 y ≠ none ∧ IsBlkQ rnd y).card : ℝ) +
        ∑ y : HashDomain, (if D.1 y ≠ none then blkCntQ (L ∪ {loC rnd}) y else 0) ≤
          ∑ y : HashDomain, if D.1 y ≠ none then blkCntQ L y else 0
      rw [Finset.card_filter, Nat.cast_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun y _ ↦ ?_
      by_cases hD : D.1 y ≠ none
      · rw [ite_eq_left hD, ite_eq_left hD]
        have h := ind_add_blkCntQ_le hl y
        by_cases hb : IsBlkQ rnd y
        · rw [ite_eq_left hb] at h
          rw [ite_eq_left ⟨hD, hb⟩, Nat.cast_one]
          exact h
        · rw [ite_eq_right hb] at h
          rw [ite_eq_right fun h' ↦ hb h'.2, Nat.cast_zero]
          exact h
      · rw [ite_eq_right hD, ite_eq_right hD, ite_eq_right fun h ↦ hD h.1, Nat.cast_zero,
          zero_add]

/-! ## Diagonal potentials along a record port -/

section recGen

variable {X₁ Z₁ S₁ M₁ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  [Fintype S₁] [DecidableEq S₁] [Fintype M₁] [DecidableEq M₁]

omit [Fintype S₁] [Fintype M₁] in
theorem recKraus_apply_eqQ (T : Finset S₁) (m : Finset S₁ × M₁)
    (t s : Unit × HwReg X₁ Z₁ (Finset S₁ × M₁)) :
    recKraus (X := X₁) (Z := Z₁) T m t s =
      if m = s.2.2.2 ∧ t = ((), recMapQ T s.2) then 1 else 0 := by
  obtain ⟨⟨⟩, D', W', m'⟩ := t
  obtain ⟨⟨⟩, D, W, mm⟩ := s
  simp only [recKraus, kroneckerMap_apply, Matrix.one_apply_eq, one_mul, clsKraus_apply,
    Matrix.one_apply, recMapQ, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- **A record port on a diagonal potential**: the weights after it are those of the recorded
states. -/
theorem tsum_potential_rec_eqQ {φ : HwReg X₁ Z₁ (Finset S₁ × M₁) → ℝ} (hφ0 : ∀ s, 0 ≤ φ s)
    (T : Finset S₁)
    {σ : Matrix (Unit × HwReg X₁ Z₁ (Finset S₁ × M₁)) (Unit × HwReg X₁ Z₁ (Finset S₁ × M₁)) ℂ}
    (hσ : σ.PosSemidef) :
    ∑' m, potential (diagPot fun s ↦ √(φ s))
        (MatrixMap.conj (recKraus (X := X₁) (Z := Z₁) T m) σ) =
      ENNReal.ofReal (∑ q, φ (recMapQ T q.2) * (σ q q).re) := by
  have hpost : ∀ m, 0 ≤ dW (fun q : Unit × HwReg X₁ Z₁ (Finset S₁ × M₁) ↦ φ q.2)
      (MatrixMap.conj (recKraus (X := X₁) (Z := Z₁) T m) σ) := fun m ↦
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (hφ0 q.2)
      (Complex.nonneg_iff.1 (posSemidef_conj _ hσ).diag_nonneg).1
  have hpot : ∀ τ : Matrix (Unit × HwReg X₁ Z₁ (Finset S₁ × M₁))
      (Unit × HwReg X₁ Z₁ (Finset S₁ × M₁)) ℂ,
      potential (diagPot fun s ↦ √(φ s)) τ = ENNReal.ofReal (dW (fun q ↦ φ q.2) τ) :=
    fun τ ↦ potential_diagPot_sqrt hφ0 τ
  have hinj : ∀ q q' : Unit × HwReg X₁ Z₁ (Finset S₁ × M₁), q.2.2.2 = q'.2.2.2 →
      ((), recMapQ T q.2) = ((), recMapQ T q'.2) → q = q' := fun q q' hi hf ↦
    Prod.ext (Subsingleton.elim _ _) (Prod.ext (congrArg (fun t ↦ t.2.1) hf)
      (Prod.ext (congrArg (fun t ↦ t.2.2.1) hf) hi))
  simp only [hpot]
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun m _ ↦ hpost m, sum_dW_conj,
    gram_classical_diag (recKraus (X := X₁) (Z := Z₁) T) (fun q ↦ q.2.2.2)
      (fun q ↦ ((), recMapQ T q.2)) (recKraus_apply_eqQ T) hinj, re_trace_diagonal_mul]

end recGen

/-! ## `Ψ` along the prefix -/

/-- **The label invariant of the searches**: in the search of `rnd`, its base is revealed. -/
def labInvQ : SrchMode → Set (RReg SelMem)
  | .free => Set.univ
  | .grd rnd _ _ => {s | loC rnd ∈ s.2.2.1}

/-- **The allowed calls keep the label invariant.** -/
theorem labInvQ_step (P : PublicParameter) (θ : HPos → Digest) (μ : SrchMode)
    (i : (RSpec SelMem).Port) (r : (RSpec SelMem).Result i)
    (σ : Matrix ((RSpec SelMem).In i × (runtimeR m0Q).D)
      ((RSpec SelMem).In i × (runtimeR m0Q).D) ℂ)
    (hok : srchOkZ P μ i)
    (hσ : QuerySupportedOn (fun m : (RSpec SelMem).In i × (runtimeR m0Q).D ↦ m.2)
      (labInvQ μ) σ) :
    QuerySupportedOn (fun m : (RSpec SelMem).Out i × (runtimeR m0Q).D ↦ m.2)
      (labInvQ (srchNxZ θ μ i r)) (((runtimeR m0Q).step i).branch r σ) := by
  rcases i with ((i | c) | c) | T
  · exact querySupportedOn_univ _ _
  · rcases μ with _ | ⟨rnd, b, j⟩
    · exact hok.elim
    have hb : ((runtimeR m0Q).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty HashOutput HashDomain)
        m0Q c r) σ
    rw [hb]
    obtain ⟨-, l, e, msg, -, rfl⟩ := hok
    show QuerySupportedOn _ (labInvQ (srchRdNx (.grd rnd b j) (.readH (trialCell P l e msg b j)
      (trialUpdQ l e (trialCell P l e msg b j))) r))
      (MatrixMap.conj (hwReadKraus (.readH (trialCell P l e msg b j)
        (trialUpdQ l e (trialCell P l e msg b j))) r) σ)
    refine hσ.conj fun q' q hK hq ↦ ?_
    obtain ⟨-, hK'⟩ := one_kronecker_ne_zero (a := q.1) (a' := q'.1) (b := q.2) (b' := q'.2) hK
    obtain ⟨hm, hm'⟩ := readKrausH_ne_zero_mem _ _ r hK'
    have hl : q'.2.2.2.1 = q.2.2.2.1 := by rw [hm', hm]; rfl
    show q'.2 ∈ labInvQ (match Codeword.decode (truncateHash (r.1.getD 0)) with
      | some _ => SrchMode.free
      | none => SrchMode.grd rnd b (j + 1))
    split
    · trivial
    · show loC rnd ∈ q'.2.2.2.1
      rw [hl]
      exact hq
  · exact querySupportedOn_univ _ _
  · rcases ho : rndOfT T with _ | rnd
    · have hn : srchNxZ θ μ (.inr T) r = .free := by
        show revNxQ T _ = _
        unfold revNxQ
        rw [ho]
      rw [hn]
      exact querySupportedOn_univ _ _
    · have hn : srchNxZ θ μ (.inr T) r = .grd rnd (θ (loC rnd)) 0 := by
        show revNxQ T _ = _
        unfold revNxQ
        rw [ho]
      have hT : T = {loC rnd} := (rndOfT_spec ho).2
      rw [hn]
      refine QuerySupportedOn.conj (K := recKraus (X := HashOutput) (Z := HashDomain) T r) hσ
        fun q' q hK _ ↦ ?_
      rw [eq_of_recKraus_ne_zero (u := q.1) (u' := q'.1) (s := q.2) (s' := q'.2) hK]
      show loC rnd ∈ q.2.2.2.1 ∪ T
      rw [hT]
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- **The drops of `Ψ` at the record ports.** -/
noncomputable def dropQW : ∀ i : (RSpec SelMem).Port,
    Matrix ((RSpec SelMem).In i × RD) ((RSpec SelMem).In i × RD) ℂ → ℝ≥0∞
  | .inr T, σ => ENNReal.ofReal (∑ q : Unit × RReg SelMem, revDropOQ T q.2 * (σ q q).re)
  | _, _ => 0

/-- The traces at the sponge ports. -/
noncomputable def spongeTrQ (i : (RSpec SelMem).Port)
    (σ : Matrix ((RSpec SelMem).In i × RD) ((RSpec SelMem).In i × RD) ℂ) : ℝ≥0∞ :=
  ((if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 0 else 1 : ℕ) : ℝ≥0∞) *
    ENNReal.ofReal σ.trace.re

/-- **The step of `Ψ`**: a sponge call raises it by at most its trace; a search's read, a program
and a record do not raise it, a record lowering it by the first-reveal drop. -/
theorem revPotQ_step (P : PublicParameter) (i : (RSpec SelMem).Port)
    (σ : Matrix ((RSpec SelMem).In i × (runtimeR m0Q).D)
      ((RSpec SelMem).In i × (runtimeR m0Q).D) ℂ) (hσ : σ.PosSemidef)
    (hI : ∃ μ, srchOkZ P μ i ∧
      QuerySupportedOn (fun m : (RSpec SelMem).In i × (runtimeR m0Q).D ↦ m.2) (labInvQ μ) σ) :
    dropQW i σ + ∑' r, potential (diagPot fun s ↦ √(revPotQ s))
        (((runtimeR m0Q).step i).branch r σ) ≤
      potential (diagPot fun s ↦ √(revPotQ s)) σ + spongeTrQ i σ := by
  have hφ0 := revPotQ_nonneg
  rcases i with ((p | c) | c) | T
  · have hb : ∀ r : Unit, ((runtimeR m0Q).step (.inl (.inl (.inl p)))).branch r σ =
        MatrixMap.conj ((spongeHardwired HashOutput HashDomain (hwEmpty HashOutput HashDomain)
          m0Q).U p) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty HashOutput HashDomain)
        m0Q p r) σ
    have hc : spongeTrQ (.inl (.inl (.inl p))) σ = ENNReal.ofReal σ.trace.re := by
      simp [spongeTrQ, extCls, hwCls]
      rfl
    rw [hc]
    show 0 + _ ≤ _
    rw [zero_add]
    exact (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans
      (tsum_potential_sponge_le hφ0 oneCellLipschitz_revPotQ (hwEmpty HashOutput HashDomain)
        m0Q p hσ)
  · obtain ⟨μ, hok, hs⟩ := hI
    have hb : ∀ r, ((runtimeR m0Q).step (.inl (.inl (.inr c)))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty HashOutput HashDomain)
        m0Q c r) σ
    have hc : spongeTrQ (.inl (.inl (.inr c))) σ = 0 := by
      simp [spongeTrQ, extCls, hwCls]
    rw [hc, add_zero]
    show 0 + _ ≤ _
    rw [zero_add]
    refine (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans ?_
    show ∑' r : c.Result, potential (diagPot fun s ↦ √(revPotQ s))
      (MatrixMap.conj (hwReadKraus c r) σ) ≤ _
    rcases μ with _ | ⟨rnd, b, j⟩
    · exact hok.elim
    obtain ⟨hj, l, e, msg, hr, rfl⟩ := hok
    rw [trialRead_eq]
    have hx : IsBlkQ rnd (trialCell P l e msg b j) := by
      have := isBlkQ_rndCell hr P b j
      rwa [rndCell_eq hr] at this
    refine tsum_potential_le_of_keep _ (sum_hwReadKraus _) hφ0
      (revPotQ_le_revPotAtQ (trialCell P l e msg b j)) (fun r a a' h ↦ ?_) hσ
      (fun q hq ↦ (revPotAtQ_eq hx (hs q q hq).1).symm)
    obtain ⟨-, hK'⟩ := one_kronecker_ne_zero (a := a.1) (a' := a'.1) (b := a.2) (b' := a'.2) h
    obtain ⟨hm, hm'⟩ := readKrausH_ne_zero_mem _ _ r hK'
    exact revPotAtQ_congr _ (readKrausH_ne_zero_cells _ _ r hK') (by rw [hm', hm]; rfl)
  · have hb : ∀ r, ((runtimeR m0Q).step (.inl (.inr c))).branch r σ =
        MatrixMap.conj (hwProgKraus c r) σ := fun r ↦
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty HashOutput HashDomain)
        m0Q c r) σ
    have hc : spongeTrQ (.inl (.inr c)) σ = 0 := by
      simp [spongeTrQ, extCls, hwCls]
    rw [hc, add_zero]
    show 0 + _ ≤ _
    rw [zero_add]
    refine (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans ?_
    refine (le_of_eq (tsum_potential_prog_eq hφ0 c hσ)).trans ?_
    refine le_of_le_of_eq ?_ (potential_diagPot_sqrt hφ0 σ).symm
    refine ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun q _ ↦ ?_)
    exact mul_le_mul_of_nonneg_right (revPotQ_progMap_le c q.2)
      (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  · have hc : spongeTrQ (.inr T) σ = 0 := by
      simp [spongeTrQ, extCls]
    rw [hc, add_zero]
    show ENNReal.ofReal (∑ q : Unit × RReg SelMem, revDropOQ T q.2 * (σ q q).re) +
      ∑' m, potential (diagPot fun s ↦ √(revPotQ s))
        (MatrixMap.conj (recKraus (X := HashOutput) (Z := HashDomain) T m) σ) ≤ _
    rw [tsum_potential_rec_eqQ hφ0 T hσ]
    refine le_of_le_of_eq ?_ (potential_diagPot_sqrt hφ0 σ).symm
    have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    have h1 : 0 ≤ ∑ q : Unit × RReg SelMem, revDropOQ T q.2 * (σ q q).re :=
      Finset.sum_nonneg fun q _ ↦ mul_nonneg (revDropOQ_nonneg _ _) (hre q)
    have h2 : 0 ≤ ∑ q : Unit × RReg SelMem, revPotQ (recMapQ T q.2) * (σ q q).re :=
      Finset.sum_nonneg fun q _ ↦ mul_nonneg (hφ0 _) (hre q)
    refine (ENNReal.ofReal_add h1 h2).symm.trans_le (ENNReal.ofReal_le_ofReal ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (revDropOQ_add_le T q.2) (hre q)

/-- **The first-reveal drops of `Ψ` along a moded run**: at most the sponge charge (the potential
starts at `0`). -/
theorem totalWeight_dropQW_le {Ω : QReg → Type} (P : PublicParameter) (θ : HPos → Digest)
    {fin : (Σ u, Ω u) → SrchMode → Prop}
    (x : QuantumComp LocalSig.instruments.{0} (RSpec SelMem) Ω (QReg.of Unit))
    (hx : ModedP (srchOkZ P) (srchNxZ θ) fin .free x) {q : ℕ}
    (hq : IFreeM.IsChargeBound x (portCharge fun i ↦
      if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 0 else 1) q) :
    (runtimeR m0Q).totalWeight .instruments dropQW x initQ ≤ q := by
  have hφ0 := revPotQ_nonneg
  have hfa := forallQueries_of_modedP (runtimeR m0Q) .instruments labInvQ
    (fun μ i r σ hok h ↦ labInvQ_step P θ μ i r σ hok h) x .free hx (ρ := initQ)
    (querySupportedOn_univ _ _)
  have h := totalWeight_le_potential_of_forallQueries (runtimeR m0Q) .instruments
    (diagPot fun s ↦ √(revPotQ s)) _
    (fun i σ ↦ ∃ μ, srchOkZ P μ i ∧
      QuerySupportedOn (fun m : (RSpec SelMem).In i × (runtimeR m0Q).D ↦ m.2) (labInvQ μ) σ)
    (fun i E σ hP ↦ by
      obtain ⟨μ, hok, hs⟩ := hP
      exact ⟨μ, hok, querySupportedOn_traceRight hs⟩)
    dropQW spongeTrQ (fun i σ hσ hI ↦ revPotQ_step P i σ hσ hI) x initQ_posSemidef hfa
  have h0 : potential (diagPot fun s ↦ √(revPotQ s)) initQ = 0 := by
    unfold initQ initU
    rw [potential_basis_init m0Q hφ0 ()]
    refine (congrArg ENNReal.ofReal (Finset.sum_eq_zero fun y _ ↦ ite_eq_right fun h ↦
      h rfl)).trans ENNReal.ofReal_zero
  refine h.trans ((add_le_add (le_of_eq h0) le_rfl).trans ?_)
  rw [zero_add]
  refine (totalWeight_chargeTrace_le (runtimeR m0Q) .instruments _ x hq
    initQ_posSemidef).trans ?_
  calc (q : ℝ≥0∞) * ENNReal.ofReal initQ.trace.re ≤ q * 1 := by
        gcongr
        exact ofReal_trace_initQ_le_one
    _ = q := mul_one _

/-! ## The first reveals, against `Ψ` -/

theorem card_digest_recU : Fintype.card Digest = 2 ^ 128 := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
  rfl

theorem paramC_ne_loC {rnd : Pos} (h : (rndLab rnd).isSome) : paramC ≠ loC rnd := by
  intro he
  have h1 : Pos.param = rnd := loC_injective he
  subst h1
  exact absurd h (by simp [rndLab])

theorem diagMass_zero_set {α : Type} [Fintype α] (σ : Matrix α α ℂ) :
    diagMass (∅ : Set α) σ = 0 := by
  simp [diagMass]

/-- The first-run states of trial `J` at the reveals, at the hidden values `θ`. -/
def firstSetQ (θ : HPos → Digest) (J : ℕ) :
    ∀ i : (RSpec SelMem).Port, Set ((RSpec SelMem).In i × RD)
  | .inr T => match rndOfT T with
    | some rnd => {q | loC rnd ∉ q.2.2.2.1 ∧
        q.2.1.1 (rndCell (θ paramC) rnd (θ (loC rnd)) J) ≠ none}
    | none => ∅
  | _ => ∅

/-- The source of a reveal: its base, if unrevealed. -/
noncomputable def firstSrcQ : ∀ i : (RSpec SelMem).Port, (RSpec SelMem).In i × RD →
    Finset HPos
  | .inr T, q => match rndOfT T with
    | some rnd => if loC rnd ∈ q.2.2.2.1 then ∅ else {loC rnd}
    | none => ∅
  | _, _ => ∅

open scoped Classical in
/-- The source values of trial `J` at a reveal: the bases whose trial-`J` cell is recorded (the
parameter read off the hidden values with the source coordinate erased). -/
noncomputable def firstFQ (J : ℕ) : ∀ i : (RSpec SelMem).Port, (RSpec SelMem).In i × RD →
    (s : HPos) → ((s : HPos) → HD s) → Finset (HD s)
  | .inr T, q => fun s v ↦ match rndOfT T with
    | some rnd => Finset.univ.filter fun b : Digest ↦
        q.2.1.1 (rndCell (Function.update v s 0 paramC) rnd b J) ≠ none
    | none => ∅
  | _, _ => fun _ _ ↦ ∅

/-- The weight per state of a reveal: its recorded trial cells over `|Digest|`, if first. -/
noncomputable def firstKQ : ∀ i : (RSpec SelMem).Port, (RSpec SelMem).In i × RD → ℝ≥0∞
  | .inr T, q => match rndOfT T with
    | some rnd => (Fintype.card Digest : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (revDropQ rnd q.2)
    | none => 0
  | _, _ => 0

/-- Membership in a filter of the whole type, the decidability found by unification. -/
theorem mem_filter_univ_of' {α : Type} {_ : Fintype α} {p : α → Prop} {_ : DecidablePred p}
    {a : α} (h : p a) : a ∈ Finset.univ.filter p :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩

theorem card_firstFQ_le {T : Finset HPos} {rnd : Pos} (hT : rndOfT T = some rnd) (J : ℕ)
    (q : (RSpec SelMem).In (.inr T) × RD) (s : HPos) (v : HPos → Digest) :
    (firstFQ J (.inr T) q s v).card ≤ blkRecQ rnd q.2 := by
  obtain ⟨⟨l, e, msg⟩, hr⟩ := Option.isSome_iff_exists.mp (rndOfT_spec hT).1
  dsimp only [firstFQ, blkRecQ]
  rw [hT]
  dsimp only
  classical
  exact Quantum.Xmss.Assembly.card_filter_le_of_injective (rndCell_base_inj hr _ J) _ _
    fun b hb ↦ ⟨hb, isBlkQ_rndCell hr _ _ J⟩

theorem mem_firstFQ {T : Finset HPos} {rnd : Pos} (hT : rndOfT T = some rnd) (J : ℕ)
    (q : (RSpec SelMem).In (.inr T) × RD) (s : HPos) (v : HPos → Digest)
    (h : q.2.1.1 (rndCell (Function.update v s 0 paramC) rnd (v s) J) ≠ none) :
    v s ∈ firstFQ J (.inr T) q s v := by
  dsimp only [firstFQ]
  rw [hT]
  dsimp only
  exact mem_filter_univ_of' h

/-- **The view lemma at the first reveals, trial by trial.** -/
theorem sum_totalWeight_firstSetQ_le (A : Adversary) (J : ℕ) :
    ∑ θ : HPos → Digest, (runtimeR m0Q).totalWeight .instruments
        (fun i ↦ diagMass (firstSetQ θ J i)) (prefixQ A θ) initQ ≤
      ∑ θ : HPos → Digest, (runtimeR m0Q).totalWeight .instruments
        (fun i ↦ kWt (firstKQ i)) (prefixQ A θ) initQ := by
  classical
  have h := sum_totalWeight_le_of_forall (runtimeR m0Q) LocalSig.Interp.instruments
    (fun θ i ↦ diagMass (firstSetQ θ J i)) (fun i ↦ kWt (firstKQ i))
    (fun θ ↦ prefixQ A θ) (fun _ ↦ initQ) 1 fun n ↦ by
      rw [one_mul]
      refine sum_queryWeight_view_le_wt (runtimeR m0Q) LocalSig.Interp.instruments
        (fun r ↦ r.2.2.1) (fun θ ↦ prefixQ A θ) (fun _ ↦ initQ) (fun _ ↦ initQ_posSemidef) n
        (fun _ ↦ True)
        ((viewBy_runtimeR_of_disc LocalSig.Interp.instruments m0Q (prefixT SelMem cwUpd A)
          ∅ (disc_prefixT SelMem cwUpd A ∅) (fun _ ↦ initQ) (lazy_const _ initQ)
          (fun _ ↦ suppAt_empty _ initQ) n).viewByOn fun _ ↦ True)
        (fun θ ↦ firstSetQ θ J) (fun _ _ h ↦ absurd trivial h) firstSrcQ (firstFQ J)
        (fun i p s v d ↦ ?_) (fun v i p hp ↦ ?_) firstKQ (fun i p v ↦ ?_)
      · rcases i with ((i | c) | c) | T
        · rfl
        · rfl
        · rfl
        · show (match rndOfT T with
            | some rnd => Finset.univ.filter fun b : Digest ↦
                p.2.1.1 (rndCell (Function.update (Function.update v s d) s 0 paramC) rnd b J)
                  ≠ none
            | none => ∅) = (match rndOfT T with
            | some rnd => Finset.univ.filter fun b : Digest ↦
                p.2.1.1 (rndCell (Function.update v s 0 paramC) rnd b J) ≠ none
            | none => ∅)
          rw [Function.update_idem]
      · rcases i with ((i | c) | c) | T
        · exact hp.elim
        · exact hp.elim
        · exact hp.elim
        · have hp' : p ∈ (match rndOfT T with
              | some rnd => {q : (RSpec SelMem).In (.inr T) × RD | loC rnd ∉ q.2.2.2.1 ∧
                  q.2.1.1 (rndCell (v paramC) rnd (v (loC rnd)) J) ≠ none}
              | none => ∅) := hp
          rcases hT : rndOfT T with _ | rnd
          · rw [hT] at hp'
            exact hp'.elim
          · rw [hT] at hp'
            have hne := paramC_ne_loC (rndOfT_spec hT).1
            refine ⟨loC rnd, ?_, hp'.1, ?_⟩
            · show loC rnd ∈ (match rndOfT T with
                | some rnd => if loC rnd ∈ p.2.2.2.1 then ∅ else {loC rnd}
                | none => ∅)
              rw [hT]
              dsimp only
              rw [ite_eq_right hp'.1]
              exact Finset.mem_singleton_self _
            · exact mem_firstFQ hT J p (loC rnd) v (by rw [Function.update_of_ne hne]; exact hp'.2)
      · rcases i with ((i | c) | c) | T
        · exact le_of_eq_of_le Finset.sum_empty zero_le
        · exact le_of_eq_of_le Finset.sum_empty zero_le
        · exact le_of_eq_of_le Finset.sum_empty zero_le
        · rcases hT : rndOfT T with _ | rnd
          · show ∑ s ∈ (match rndOfT T with
                | some rnd => if loC rnd ∈ p.2.2.2.1 then ∅ else {loC rnd}
                | none => ∅), _ ≤ _
            rw [hT, Finset.sum_empty]
            exact zero_le
          · show ∑ s ∈ (match rndOfT T with
                | some rnd => if loC rnd ∈ p.2.2.2.1 then ∅ else {loC rnd}
                | none => ∅), ((firstFQ J (.inr T) p s v).card : ℝ≥0∞) *
                  (Fintype.card Digest : ℝ≥0∞)⁻¹ ≤
                (match rndOfT T with
                | some rnd => (Fintype.card Digest : ℝ≥0∞)⁻¹ *
                    ENNReal.ofReal (revDropQ rnd p.2)
                | none => 0)
            rw [hT]
            dsimp only
            by_cases hl : loC rnd ∈ p.2.2.2.1
            · rw [ite_eq_left hl, Finset.sum_empty]
              exact zero_le
            · rw [ite_eq_right hl, Finset.sum_singleton, mul_comm]
              refine mul_le_mul_of_nonneg_left ?_ zero_le
              have hd : revDropQ rnd p.2 = (blkRecQ rnd p.2 : ℝ) := ite_eq_right hl
              rw [hd, ENNReal.ofReal_natCast]
              exact Nat.cast_le.mpr (card_firstFQ_le hT J p _ v)
  rwa [one_mul] at h

theorem firstQW_eq_sum (θ : HPos → Digest) (i : (RSpec SelMem).Port)
    (σ : Matrix ((RSpec SelMem).In i × RD) ((RSpec SelMem).In i × RD) ℂ) :
    firstQW (θ paramC) θ i σ =
      ∑ J : Fin randomizerAttemptLimit, diagMass (firstSetQ θ J.val i) σ := by
  rcases i with ((i | c) | c) | T
  · exact (Finset.sum_eq_zero fun _ _ ↦ diagMass_zero_set σ).symm
  · exact (Finset.sum_eq_zero fun _ _ ↦ diagMass_zero_set σ).symm
  · exact (Finset.sum_eq_zero fun _ _ ↦ diagMass_zero_set σ).symm
  · show (match rndOfT T with
      | some rnd => ∑ J : Fin randomizerAttemptLimit,
          diagMass {q : Unit × RReg SelMem | loC rnd ∉ q.2.2.2.1 ∧
            q.2.1.1 (rndCell (θ paramC) rnd (θ (loC rnd)) J) ≠ none} σ
      | none => 0) = ∑ J : Fin randomizerAttemptLimit, diagMass (match rndOfT T with
      | some rnd => {q : (RSpec SelMem).In (.inr T) × RD | loC rnd ∉ q.2.2.2.1 ∧
          q.2.1.1 (rndCell (θ paramC) rnd (θ (loC rnd)) J.val) ≠ none}
      | none => ∅) σ
    rcases rndOfT T with _ | rnd
    · exact (Finset.sum_eq_zero fun _ _ ↦ diagMass_zero_set σ).symm
    · rfl

theorem kWt_firstKQ_inr (T : Finset HPos)
    (σ : Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ) (hσ : σ.PosSemidef) :
    ∑ q : Unit × RReg SelMem, firstKQ (.inr T) q * ENNReal.ofReal (σ q q).re ≤
      (Fintype.card Digest : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (∑ q : Unit × RReg SelMem, revDropOQ T q.2 * (σ q q).re) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  rw [ENNReal.ofReal_sum_of_nonneg fun q _ ↦ mul_nonneg (revDropOQ_nonneg _ _) (hre q),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  rw [ENNReal.ofReal_mul (revDropOQ_nonneg _ _), ← mul_assoc]
  refine mul_le_mul_of_nonneg_right (le_of_eq ?_) zero_le
  show (match rndOfT T with
    | some rnd => (Fintype.card Digest : ℝ≥0∞)⁻¹ * ENNReal.ofReal (revDropQ rnd q.2)
    | none => 0) = (Fintype.card Digest : ℝ≥0∞)⁻¹ * ENNReal.ofReal (match rndOfT T with
    | some rnd => revDropQ rnd q.2
    | none => 0)
  rcases rndOfT T with _ | rnd
  · rw [ENNReal.ofReal_zero, mul_zero]
  · rfl

theorem kWt_firstKQ_le (i : (RSpec SelMem).Port)
    (σ : Matrix ((RSpec SelMem).In i × RD) ((RSpec SelMem).In i × RD) ℂ)
    (hσ : σ.PosSemidef) :
    kWt (firstKQ i) σ ≤ (Fintype.card Digest : ℝ≥0∞)⁻¹ * dropQW i σ := by
  rcases i with ((i | c) | c) | T
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun _ _ ↦ zero_mul _) zero_le
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun _ _ ↦ zero_mul _) zero_le
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun _ _ ↦ zero_mul _) zero_le
  · exact kWt_firstKQ_inr T σ hσ

/-- **The first-reveal charges, summed over the hidden values**: at most `2^32 / 2^128` times
the sponge charge per hidden value. -/
theorem sum_totalWeight_firstQW_le (A : Adversary) {q : ℕ}
    (hq : ∀ θ, IFreeM.IsChargeBound (prefixQ A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 0 else 1) q) :
    ∑ θ : HPos → Digest, (runtimeR m0Q).totalWeight .instruments (firstQW (θ paramC) θ)
        (prefixQ A θ) initQ ≤
      (randomizerAttemptLimit : ℝ≥0∞) * (2 ^ 128 : ℝ≥0∞)⁻¹ * q *
        Fintype.card (HPos → Digest) := by
  have hcard : (Fintype.card Digest : ℝ≥0∞)⁻¹ = (2 ^ 128 : ℝ≥0∞)⁻¹ := by
    rw [card_digest_recU]
    norm_num
  calc ∑ θ : HPos → Digest, (runtimeR m0Q).totalWeight .instruments (firstQW (θ paramC) θ)
        (prefixQ A θ) initQ
      = ∑ θ : HPos → Digest, ∑ J : Fin randomizerAttemptLimit,
          (runtimeR m0Q).totalWeight .instruments (fun i ↦ diagMass (firstSetQ θ J.val i))
            (prefixQ A θ) initQ := Finset.sum_congr rfl fun θ _ ↦ by
        exact (congrArg (fun w ↦ (runtimeR m0Q).totalWeight .instruments w (prefixQ A θ) initQ)
          (funext fun i ↦ funext fun σ ↦ firstQW_eq_sum θ i σ)).trans
          (totalWeight_fintype_sum (runtimeR m0Q) .instruments
            (fun (J : Fin randomizerAttemptLimit) i ↦ diagMass (firstSetQ θ J.val i))
            (prefixQ A θ) initQ)
    _ = ∑ J : Fin randomizerAttemptLimit, ∑ θ : HPos → Digest,
          (runtimeR m0Q).totalWeight .instruments (fun i ↦ diagMass (firstSetQ θ J.val i))
            (prefixQ A θ) initQ := Finset.sum_comm
    _ ≤ ∑ _J : Fin randomizerAttemptLimit, ∑ θ : HPos → Digest,
          (runtimeR m0Q).totalWeight .instruments (fun i ↦ kWt (firstKQ i)) (prefixQ A θ)
            initQ := Finset.sum_le_sum fun J _ ↦ sum_totalWeight_firstSetQ_le A J.val
    _ ≤ ∑ _J : Fin randomizerAttemptLimit, ∑ _θ : HPos → Digest,
          (2 ^ 128 : ℝ≥0∞)⁻¹ * q := Finset.sum_le_sum fun J _ ↦ Finset.sum_le_sum fun θ _ ↦ by
        refine (totalWeight_le_totalWeight (runtimeR m0Q) .instruments
          (fun i σ hσ ↦ kWt_firstKQ_le i σ hσ) _ initQ_posSemidef).trans ?_
        refine (le_of_eq (totalWeight_const_mul_weight (runtimeR m0Q) .instruments
          (Fintype.card Digest : ℝ≥0∞)⁻¹ dropQW (prefixQ A θ) initQ)).trans ?_
        rw [hcard]
        exact mul_le_mul_of_nonneg_left (totalWeight_dropQW_le (θ paramC) θ (prefixQ A θ)
          (modedP_prefixQ A θ) (hq θ)) zero_le
    _ = _ := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
        ring

end Quantum.Qrom.Xmss

end
