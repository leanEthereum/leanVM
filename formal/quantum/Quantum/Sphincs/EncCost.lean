module

public import Quantum.Sphincs.Events

@[expose] public section

/-!
# The encoding cost of leanSPHINCS's selecting reads

A WOTS+C trial of key `K = (l, τ, e)` reads the final `h` cell of its one-block input
`PK.seed ‖ ADRS_enc(K) ‖ M_K ‖ BE32(c)` and selects when the trial's digest `trunc128 (xi + v)` is
a codeword (`cwSel`, `cwUpd`). A selecting read flips a state into `Bad` only if the selected
digest is the output of another tail at the encoding slot of `K`, and that output is then a
codeword. The signer makes about `1 / ρ_c` trials of a key, `ρ_c ≥ 2^-14` the codeword fraction
(`inv_two_pow_14_le_rhoCw`), so the Enc cost of a key is about `n_cw 2^-128 / ρ_c`, `n_cw` the
tails at its encoding slot whose outputs are codewords. This is leanXMSS's encoding cost on
Events' `Bad d N = TgtBad d N ∪ CovBadOf d N` over the labelled memory `Mem S`, with the generic
parts (`card_flip_readH_out_le`, `survive_readH_le`, `sum_trials_le`, `sum_cost_le`,
`flipCost_readH_le`, `sum_flipCost_prog_le_card`) reused.

* **The codeword-restricted flip count** (`card_flip_readCw_le`, `flipCost_selectReadCw_le`): for a
  read update that keeps the memory or records the selection only for a codeword digest, at most
  `encCwCount * 2^960` values flip a state, `encCwCount` the `h` cells whose head-tail lies at the
  encoding slot of `K` and whose output is a codeword. A read never flips into the coverage part
  (`mem_tgtBad_of_mem_bad_readH`). The selecting-read term is `E ≤ C 2^-128 e` with `e` the weight
  of the selection reads (`selectReadCwE_le`). In a good database the counts of all keys add up to
  at most the encoding-slot cells (`sum_encCwCount_le`, `encSlotCount_le_size`).
* **Survival** (`survive_selectRead_le`): the outcomes of a trial that leave the key unselected
  weigh at most `w - ρ_c e + p + 2 √(ρ_c e p)`, with `w` the weight of the states where the key is
  unselected, `e` the weight of the selection reads and `p` the rest (`readPs`).
* **One key** (`encCost_key_le`, `encCost_key_le_pow`): the selecting reads' costs
  `E + p + 2 √(E p)` over any number of trials sum to at most
  `(√(C 2^-128 / ρ_c · (√(w₀ + 2P) + √P)²) + √P)²`, with `w₀` the weight reaching the first trial,
  `P` the total of the `p` terms and `C` a bound on `encCwCount` on the key's selection reads; with
  `ρ_c ≥ 2^-14`, at most `(√(C 2^-114 (√(w₀ + 2P) + √P)²) + √P)²`.
* **Program ports** (`flipCost_programH_avg_le`, `flipCost_programH_eq_zero`,
  `flipCost_programH_honest`, `flipCost_programH_hmsg`, `flipCost_programH_short`,
  `flipCost_programK_avg_le`, `flipCost_programK'_avg_le`): programming an `h` cell costs
  `2^-128 + 2^16 price S★` averaged over the value, nothing at the final cell of an exempted
  structural slot's honest path, of an exempted `H_msg` call or at an intermediate cell of a
  multi-block honest path, and twice the capacity-scale counts for `k`, `k'`.
-/

open Matrix Finset Quantum Quantum.Sponge Sphincs
open HashSig (Digest Message Randomizer)
open Quantum.Xmss (X Z trunc128 card_X fiber_div_card_X card_fiber_trunc128_le two_pow_div_card_X)
open scoped ENNReal ComplexOrder

namespace Quantum.Sphincs

/-! ## Recording a selection keeps every target -/

/-- **Recording a selection of an unselected key keeps every Struct and Enc target.** -/
theorem sphTgt_select_mono {d : EvData} {Ex : Set Slot} {sel : Selections} {K : Key} {x : X}
    {y' : Digest} (hm : sel K = none) {t : List X} {y : Digest}
    (h : d.sphTgt Ex sel t = some y) : d.sphTgt Ex (sel.select K x y') t = some y := by
  obtain ⟨s, hs, hst | hst⟩ := sphTgt_eq_some_iff.1 h
  · exact sphTgt_eq_some_iff.2 ⟨s, hs, .inl hst⟩
  obtain ⟨l, τ, e, x', rfl, hc, hne⟩ := encTgt_eq_some_iff.1 hst
  have hK : (l, τ, e) ≠ K := fun hK ↦ by
    rw [hK, hm] at hc
    cases hc
  exact sphTgt_enc hs (by rw [Selections.select_of_ne _ x y' hK]; exact hc) hne

/-- The trial's memory update on the labelled memory keeps the memory or records the selection. -/
theorem lift_cwUpd_some {S : Type} (K : Key) (x xi : X) (m : Mem S) (v : X) :
    ((m.1, cwUpd K x xi m.2 (some v)) : Mem S) = m ∨
      ((m.1, cwUpd K x xi m.2 (some v)) : Mem S) = (m.1, cwSel m.2 K x xi v) := by
  rcases cwUpd_some K x xi m.2 v with h | h
  · exact .inl (by rw [h])
  · exact .inr (by rw [h])

/-- On an unselected key the trial's memory update on the labelled memory is `cwSel`. -/
theorem lift_cwUpd_some_of_none {S : Type} (K : Key) (x xi : X) {m : Mem S} (hm : m.2 K = none)
    (v : X) : ((m.1, cwUpd K x xi m.2 (some v)) : Mem S) = (m.1, cwSel m.2 K x xi v) :=
  congrArg (Prod.mk m.1) (cwUpd_some_of_none K x xi hm v)

/-- The second component of a pair, as a lemma: rewriting with it keeps the unifier from comparing
`(a, cwSel _).2` with `cwSel _`, which unfolds the codeword test. -/
theorem snd_pair {α β : Type} (a : α) (b : β) : (a, b).2 = b :=
  rfl

/-! ## The codeword-restricted counts -/

/-- The `h` cells of `U` whose head-tail lies at the encoding slot of key `K` and whose output is a
codeword: the tails at that slot that reach a codeword. -/
noncomputable def encCwCount (d : EvData) (U : Dbs X Z) (K : Key) : ℕ :=
  tailOutCount d.perm U trunc128 (fun t ↦ slotOf d.pk t = some (.enc K.1 K.2.1 K.2.2))
    Codeword.Valid

theorem encCwCount_le_encCount (d : EvData) (U : Dbs X Z) (K : Key) :
    encCwCount d U K ≤ encCount d U K :=
  tailOutCount_le_tailCount _ _ _ _ _

/-- The `h` cells of `U` whose head-tail lies at an encoding slot. -/
noncomputable def encSlotCount (d : EvData) (U : Dbs X Z) : ℕ :=
  tailCount d.perm U fun t ↦ ∃ K : Key, slotOf d.pk t = some (.enc K.1 K.2.1 K.2.2)

theorem encSlotCount_le_size (d : EvData) (U : Dbs X Z) : encSlotCount d U ≤ U.h.size :=
  tailCount_le_size _ _ _

/-- **The keys share the encoding-slot cells**: in a good database each cell has one head-tail, at
one slot, so the codeword counts of all keys add up to at most the encoding-slot cells. -/
theorem sum_encCwCount_le {d : EvData} {U : Dbs X Z} (hG : Good d.perm U) :
    ∑ K : Key, encCwCount d U K ≤ encSlotCount d U := by
  have hP : ∀ (K K' : Key) (t : List X), slotOf d.pk t = some (.enc K.1 K.2.1 K.2.2) →
      slotOf d.pk t = some (.enc K'.1 K'.2.1 K'.2.2) → K = K' := fun K K' t h h' ↦ by
    obtain ⟨h1, h2, h3⟩ := Slot.enc.inj (Option.some.inj (h.symm.trans h'))
    exact Prod.ext h1 (Prod.ext h2 h3)
  -- Named arguments: unifying the generic sum with this one would unfold `Finset.univ`.
  have h := sum_tailOutCount_le (κ := Key) (π := d.perm) (out := trunc128) hG
    (fun K t ↦ slotOf d.pk t = some (.enc K.1 K.2.1 K.2.2)) hP Codeword.Valid
  exact h

/-! ## The codeword-restricted flip count -/

section Flip

variable {S : Type} {d : EvData} {N : ℕ}

open scoped Classical in
/-- **`card_flip_readCw_le`**: a selection read of key `K` that records the selection only for a
codeword digest flips a state outside `Bad` for at most `encCwCount * 2^960` values of the read
cell: the flips are the codeword outputs of the other tails at the encoding slot of `K`. -/
theorem card_flip_readCw_le {D : DbReg X Z} {W : Hw X Z} {T : Finset S} {sel : Selections}
    {z : Z} {K : Key} {x xi : X} (hs : (D, W, (T, sel)) ∉ Bad d N)
    (hr : SelectRead d D W sel z K x xi) :
    #(univ.filter fun v : X ↦ ∃ u : Option X,
      ((Function.update D.1 z u, D.2), W, ((T, cwSel sel K x xi v) : Mem S)) ∈ Bad d N) ≤
        encCwCount d (union W D) K * 2 ^ 960 := by
  refine le_trans (card_le_card (filter_univ_mono fun v ⟨u, hu⟩ ↦ ⟨u, ?_⟩))
    (card_flip_readH_out_le card_fiber_trunc128_le (fun h ↦ hs (.inl h)) hr.hw hr.hd
      (fun t ↦ slotOf d.pk t = some (.enc K.1 K.2.1 K.2.2)) Codeword.Valid [x] xi
      (fun v ↦ ((T, cwSel sel K x xi v) : Mem S))
      (fun v t y ht ↦ by
        unfold cwSel at ht
        split_ifs at ht with hv
        · rcases sphTgt_select ht with h | ⟨h1, h2, h3⟩
          · exact .inl h
          · exact .inr ⟨hv, h1, h2, h3⟩
        · exact .inl ht)
      (fun hG v t xi' hi ↦ by
        unfold cwSel
        split_ifs
        · exact hr.head_none hG T hi
        · obtain ⟨rfl, -⟩ := hG.isHeadTail_unique hi hr.head
          exact sphTgt_enc_none hr.slot hr.hm))
  exact mem_tgtBad_of_mem_bad_readH hs hr.hw hr.hd (fun hG ↦ hr.covHead hG) hu

/-- **Filling an empty cell keeps the event**, for a memory whose Struct and Enc targets contain the
old ones (the coverage part reads no memory). -/
theorem mem_bad_fill {D : DbReg X Z} {W : Hw X Z} {m : Mem S} (hs : (D, W, m) ∈ Bad d N) {z : Z}
    (hz : D.1 z = none) (u : Option X) (T' : Finset S) (sel' : Selections)
    (htgt : ∀ t y, d.sphTgt (d.exS W) m.2 t = some y → d.sphTgt (d.exS W) sel' t = some y) :
    ((Function.update D.1 z u, D.2), W, ((T', sel') : Mem S)) ∈ Bad d N := by
  rcases hs with h | h
  · exact .inl (mem_hwTargetBad_fill h hz u (T', sel') htgt)
  · exact .inr (mem_hwTargetBad_fill h hz u (T', sel') fun _ _ ht ↦ ht)

variable [Fintype (Mem S)] [DecidableEq (Mem S)]

open scoped Classical in
/-- **The flip cost of a codeword-selecting read** of the final `h` cell `z` of the WOTS+C trial
of key `K` with block `x` and rate `xi`. The read updates the memory with `upd`, which for a value
`v` keeps it or records the selection only for a codeword digest (`cwSel`; the template's update
`(m.1, cwUpd K x xi m.2 o)`, `lift_cwUpd_some`). With `P` the projector on the states that are not
selection reads (`SelectRead`: the cell recorded or hardwired, the key already selected, or the
trial's tail not the head-tail of the cell), the flip cost is `E + p + 2 √(E p)` with
`E = ∑_{SelectRead, ∉ Bad} encCwCount · 2^960 / |X| · σ_ss` and `p = tr (P σ)`. -/
theorem flipCost_selectReadCw_le (z : Z) (K : Key) (x xi : X) (upd : Mem S → Option X → Mem S)
    (hupd : ∀ m v, upd m (some v) = m ∨ upd m (some v) = (m.1, cwSel m.2 K x xi v))
    {σ : Matrix (Unit × HwReg X Z (Mem S)) (Unit × HwReg X Z (Mem S)) ℂ} (hσ : σ.PosSemidef) :
    flipCost (Bad d N) (hwReadKraus (.readH z upd))
        (readPs fun s : HwReg X Z (Mem S) ↦ SelectRead d s.1 s.2.1 s.2.2.2 z K x xi) σ ≤
      ENNReal.ofReal (∑ q, if SelectRead d q.2.1 q.2.2.1 q.2.2.2.2 z K x xi ∧ q.2 ∉ Bad d N then
          ((encCwCount d (union q.2.2.1 q.2.1) K * 2 ^ 960 : ℕ) : ℝ) / Fintype.card X *
            (σ q q).re else 0) +
        ENNReal.ofReal ((readPs fun s : HwReg X Z (Mem S) ↦ SelectRead d s.1 s.2.1 s.2.2.2 z K x
          xi) * σ).trace.re +
      2 * (ENNReal.ofReal (∑ q, if SelectRead d q.2.1 q.2.2.1 q.2.2.2.2 z K x xi ∧
          q.2 ∉ Bad d N then ((encCwCount d (union q.2.2.1 q.2.1) K * 2 ^ 960 : ℕ) : ℝ) /
            Fintype.card X * (σ q q).re else 0) *
        ENNReal.ofReal ((readPs fun s : HwReg X Z (Mem S) ↦ SelectRead d s.1 s.2.1 s.2.2.2 z K x
          xi) * σ).trace.re) ^
          (2⁻¹ : ℝ) := by
  refine flipCost_readH_le (Bad d N) z upd (fun (m : Mem S) v ↦ (m.1, cwSel m.2 K x xi v))
    (fun s : HwReg X Z (Mem S) ↦ SelectRead d s.1 s.2.1 s.2.2.2 z K x xi)
    (fun s : HwReg X Z (Mem S) ↦ encCwCount d (union s.2.1 s.1) K * 2 ^ 960) ?_ hupd ?_ ?_ ?_ ?_
    hσ
  · exact fun _ hs ↦ ⟨hs.hd, hs.hw⟩
  · exact fun _ u hs hS ↦ not_mem_bad_read_keep hS hs u
  · -- The filter's decidability instances differ syntactically from `card_flip_readCw_le`'s.
    intro s hs hS
    convert card_flip_readCw_le hS hs using 3
  · exact fun s u hs hS ↦ mem_bad_fill hS hs.hd u s.2.2.1 s.2.2.2 fun _ _ ht ↦ ht
  · intro s u v hs hS
    refine mem_bad_fill hS hs.hd u s.2.2.1 (cwSel s.2.2.2 K x xi v) fun t y ht ↦ ?_
    rcases cwSel_eq s.2.2.2 K x xi v with h | h
    · rw [h]
      exact ht
    · rw [h]
      exact sphTgt_select_mono hs.hm ht

omit [DecidableEq (Mem S)] in
open scoped Classical in
/-- **The selecting-read term** of `flipCost_selectReadCw_le`: if `encCwCount ≤ C` on the selection
reads of the support outside `Bad`, then `E ≤ C 2^-128 e`, with `e` the weight of the selection
reads. -/
theorem selectReadCwE_le (z : Z) (K : Key) (x xi : X) (C : ℕ)
    {σ : Matrix (Unit × HwReg X Z (Mem S)) (Unit × HwReg X Z (Mem S)) ℂ} (hσ : σ.PosSemidef)
    (hC : ∀ q, SelectRead d q.2.1 q.2.2.1 q.2.2.2.2 z K x xi → q.2 ∉ Bad d N → σ q q ≠ 0 →
      encCwCount d (union q.2.2.1 q.2.1) K ≤ C) :
    (∑ q, if SelectRead d q.2.1 q.2.2.1 q.2.2.2.2 z K x xi ∧ q.2 ∉ Bad d N then
        ((encCwCount d (union q.2.2.1 q.2.1) K * 2 ^ 960 : ℕ) : ℝ) / Fintype.card X *
          (σ q q).re else 0) ≤
      C * (2 ^ 128)⁻¹ * ∑ q, if SelectRead d q.2.1 q.2.2.1 q.2.2.2.2 z K x xi then
        (σ q q).re else 0 := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hC0 : (0 : ℝ) ≤ C * (2 ^ 128)⁻¹ := by positivity
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  by_cases hq : SelectRead d q.2.1 q.2.2.1 q.2.2.2.2 z K x xi
  · rw [ite_eq_left hq]
    by_cases hb : q.2 ∉ Bad d N
    · rw [ite_eq_left ⟨hq, hb⟩]
      by_cases hσq : σ q q = 0
      · rw [hσq, Complex.zero_re, mul_zero, mul_zero]
      refine mul_le_mul_of_nonneg_right ?_ (hre q)
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc, two_pow_div_card_X]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (hC q hq hb hσq)) (by positivity)
    · rw [ite_eq_right fun h ↦ hb h.2]
      exact mul_nonneg hC0 (hre q)
  · rw [ite_eq_right fun h ↦ hq h.1, ite_eq_right hq, mul_zero]

end Flip

/-! ## Survival of a trial -/

/-- `rhoCw`, as the fraction of codeword values of a trial cell. -/
theorem cwCount_mul_div_card_X : ((cwCount * 2 ^ 960 : ℕ) : ℝ) / Fintype.card X = rhoCw := by
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc, two_pow_div_card_X, rhoCw,
    div_eq_mul_inv]

/-- The codeword values of a trial cell are a fraction `rhoCw` of its values. -/
theorem card_codeword_div_card_X (xi : X) :
    ((univ.filter fun v : X ↦ Codeword.Valid (trunc128 (xi + v))).card : ℝ) /
      Fintype.card X = rhoCw := by
  rw [card_codeword_trunc128, cwCount_mul_div_card_X]

/-- The memories whose key `K` has no selection. -/
def unselMem (S : Type) (K : Key) : Set (Mem S) := {m | m.2 K = none}

instance unselMemDec (S : Type) (K : Key) : DecidablePred (· ∈ unselMem S K) :=
  fun m ↦ inferInstanceAs (Decidable (m.2 K = none))

section Survive

variable {S : Type} [Fintype (Mem S)] [DecidableEq (Mem S)]

open scoped Classical in
/-- **Survival of a trial read**: the outcomes of a trial of the unselected key `K` that leave it
unselected weigh at most `w - ρ_c e + p + 2 √(ρ_c e p)`, with `w` the weight of the states where the
key is unselected, `e` the weight of the selection reads `SR` (cell empty and not hardwired, key
unselected) and `p = tr (P σ)` the rest: on an empty cell the trial's digest is a codeword with
probability `rhoCw`. -/
theorem survive_selectRead_le (z : Z) (K : Key) (x xi : X) (upd : Mem S → Option X → Mem S)
    (hupd : ∀ m v, m.2 K = none → upd m (some v) = (m.1, cwSel m.2 K x xi v))
    (SR : HwReg X Z (Mem S) → Prop) [DecidablePred SR]
    (hSR : ∀ s, SR s → s.1.1 z = none ∧ s.2.1.1 z = none ∧ s.2.2 ∈ unselMem S K)
    {σ : Matrix (Unit × HwReg X Z (Mem S)) (Unit × HwReg X Z (Mem S)) ℂ}
    (hσ : σ.PosSemidef) :
    (∑ r : Option X × Mem S, if upd r.2 r.1 ∈ unselMem S K then
        (MatrixMap.conj (hwReadKraus (.readH z upd) r) σ).trace.re else 0) ≤
      (∑ q, if q.2.2.2 ∈ unselMem S K then (σ q q).re else 0) -
        rhoCw * (∑ q, if SR q.2 then (σ q q).re else 0) + (readPs SR * σ).trace.re +
        2 * √(rhoCw * (∑ q, if SR q.2 then (σ q q).re else 0) * (readPs SR * σ).trace.re) :=
  survive_readH_le z upd (unselMem S K) (fun v ↦ Codeword.Valid (trunc128 (xi + v)))
    (card_codeword_div_card_X xi)
    (fun m hm v ↦ (Iff.of_eq ((congrArg (fun m' : Mem S ↦ m'.2 K = none) (hupd m v hm)).trans
      (congrArg (fun s : Selections ↦ s K = none) (snd_pair m.1 (cwSel m.2 K x xi v))))).trans
      (cwSel_eq_none_iff (m := m.2) (K := K) hm x xi v)) SR hSR hσ

end Survive

/-! ## One key: the trial sequence -/

/-- **The Enc cost of one key.** Let trial `j` of the key start from the state `σ_j`, with `w j`
the weight of its states where the key is unselected, `e j` the weight of its selection reads and
`p j` the rest (`readPs`), let the survival bounds hold (`survive_selectRead_le`, the reads between
two `h` reads keep the memory), and let the selecting read's term be `E j ≤ C 2^-128 e j`
(`selectReadCwE_le`, `C` bounding `encCwCount` on the selection reads outside `Bad` of the key's
trials). Then the selecting reads' costs `E + p + 2 √(E p)` (`flipCost_selectReadCw_le`) over all
trials sum to at most `(√(C 2^-128 / ρ_c · (√(w 0 + 2P) + √P)²) + √P)²`, for any number of
trials. -/
theorem encCost_key_le {J : ℕ} {C : ℝ} (hC : 0 ≤ C) (w e p E : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (he : ∀ j, 0 ≤ e j) (hp : ∀ j, 0 ≤ p j) (hE0 : ∀ j, 0 ≤ E j)
    (hrec : ∀ j < J, w (j + 1) ≤ w j - rhoCw * e j + p j + 2 * √(rhoCw * e j * p j))
    (hE : ∀ j < J, E j ≤ C * (2 ^ 128)⁻¹ * e j) :
    ∑ j ∈ range J, (ENNReal.ofReal (E j) + ENNReal.ofReal (p j) +
      2 * (ENNReal.ofReal (E j) * ENNReal.ofReal (p j)) ^ (2⁻¹ : ℝ)) ≤
    ENNReal.ofReal ((√(C * (2 ^ 128)⁻¹ / rhoCw *
        (√(w 0 + 2 * ∑ j ∈ range J, p j) + √(∑ j ∈ range J, p j)) ^ 2) +
      √(∑ j ∈ range J, p j)) ^ 2) := by
  refine (Quantum.Xmss.sum_cost_le J E p hE0 hp).trans (ENNReal.ofReal_le_ofReal ?_)
  have hk : 0 ≤ C * (2 ^ 128 : ℝ)⁻¹ := by positivity
  have htr := Quantum.Xmss.sum_trials_le rhoCw_pos.le w e p hw he hp hrec
  have hEsum : ∑ j ∈ range J, E j ≤ C * (2 ^ 128)⁻¹ / rhoCw *
      (√(w 0 + 2 * ∑ j ∈ range J, p j) + √(∑ j ∈ range J, p j)) ^ 2 := by
    calc ∑ j ∈ range J, E j ≤ ∑ j ∈ range J, C * (2 ^ 128)⁻¹ * e j :=
          Finset.sum_le_sum fun j hj ↦ hE j (Finset.mem_range.1 hj)
      _ = C * (2 ^ 128)⁻¹ / rhoCw * (rhoCw * ∑ j ∈ range J, e j) := by
          rw [← Finset.mul_sum]
          field_simp [rhoCw_pos.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left htr (div_nonneg hk rhoCw_pos.le)
  have hsq := Real.sqrt_le_sqrt hEsum
  exact pow_le_pow_left₀ (by positivity) (by linarith) 2

/-- **The Enc cost of one key, with `ρ_c ≥ 2^-14`**: at most
`(√(C 2^-114 (√(w 0 + 2P) + √P)²) + √P)²`. -/
theorem encCost_key_le_pow {J : ℕ} {C : ℝ} (hC : 0 ≤ C) (w e p E : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (he : ∀ j, 0 ≤ e j) (hp : ∀ j, 0 ≤ p j) (hE0 : ∀ j, 0 ≤ E j)
    (hrec : ∀ j < J, w (j + 1) ≤ w j - rhoCw * e j + p j + 2 * √(rhoCw * e j * p j))
    (hE : ∀ j < J, E j ≤ C * (2 ^ 128)⁻¹ * e j) :
    ∑ j ∈ range J, (ENNReal.ofReal (E j) + ENNReal.ofReal (p j) +
      2 * (ENNReal.ofReal (E j) * ENNReal.ofReal (p j)) ^ (2⁻¹ : ℝ)) ≤
    ENNReal.ofReal ((√(C * (2 ^ 114)⁻¹ *
        (√(w 0 + 2 * ∑ j ∈ range J, p j) + √(∑ j ∈ range J, p j)) ^ 2) +
      √(∑ j ∈ range J, p j)) ^ 2) := by
  refine (encCost_key_le hC w e p E hw he hp hE0 hrec hE).trans (ENNReal.ofReal_le_ofReal ?_)
  have hk : C * (2 ^ 128 : ℝ)⁻¹ / rhoCw ≤ C * (2 ^ 114)⁻¹ := by
    rw [div_eq_mul_inv, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC
    calc (2 ^ 128 : ℝ)⁻¹ * rhoCw⁻¹ ≤ (2 ^ 128)⁻¹ * 2 ^ 14 :=
          mul_le_mul_of_nonneg_left inv_rhoCw_le (by positivity)
      _ = (2 ^ 114)⁻¹ := by norm_num
  have hsq := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hk (sq_nonneg
    (√(w 0 + 2 * ∑ j ∈ range J, p j) + √(∑ j ∈ range J, p j))))
  exact pow_le_pow_left₀ (by positivity) (by linarith) 2

/-! ## Program ports -/

section Prog

variable {S : Type} [Fintype (Mem S)] [DecidableEq (Mem S)] {d : EvData} {N : ℕ}

open scoped Classical in
/-- **Programming `h` cells, averaged over the value**: `(2^-128 + 2^16 price S★) tr σ`, on states
whose cell is not hardwired (`card_flip_programH_bad_le`, `freshRate_h_eq`). -/
theorem flipCost_programH_avg_le (z : Z)
    {σ : Matrix (Unit × HwReg X Z (Mem S)) (Unit × HwReg X Z (Mem S)) ℂ} (hσ : σ.PosSemidef)
    (hsupp : ∀ q, σ q q ≠ 0 → q.2.2.1.1 z = none) :
    (Fintype.card X : ℝ≥0∞)⁻¹ * ∑ v : X, flipCost (Bad d N) (hwProgKraus (.programH z v)) 0 σ ≤
      ((2 ^ 128)⁻¹ + ENNReal.ofReal ((2 ^ 16 * price d.cover : ℚ) : ℝ)) *
        ENNReal.ofReal σ.trace.re := by
  have h := sum_flipCost_prog_le_card (Bad d N) (fun v : X ↦ HwProg.programH z v)
    (2 ^ 960 + 2 ^ 838 * coverMass d.cover) hσ
    fun q hq hσq ↦ card_flip_programH_bad_le (D := q.2.1) (W := q.2.2.1) (m := q.2.2.2) hq
      (hsupp q hσq)
  calc (Fintype.card X : ℝ≥0∞)⁻¹ * ∑ v : X, flipCost (Bad d N) (hwProgKraus (.programH z v)) 0 σ
      ≤ (Fintype.card X : ℝ≥0∞)⁻¹ *
          (((2 ^ 960 + 2 ^ 838 * coverMass d.cover : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) :=
        mul_le_mul_right h _
    _ = (((2 ^ 960 : ℕ) : ℝ≥0∞) / Fintype.card X +
          ((2 ^ 838 * coverMass d.cover : ℕ) : ℝ≥0∞) / Fintype.card X) *
          ENNReal.ofReal σ.trace.re := by
        rw [Nat.cast_add, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ← mul_add, mul_assoc]
    _ = _ := by rw [freshRate_h_eq]

open scoped Classical in
/-- **A program of `h` cells after which no value is in the event flips nothing.** -/
theorem flipCost_programH_eq_zero (z : Z)
    {σ : Matrix (Unit × HwReg X Z (Mem S)) (Unit × HwReg X Z (Mem S)) ℂ} (hσ : σ.PosSemidef)
    (hsupp : ∀ q, σ q q ≠ 0 → q.2 ∉ Bad d N → ∀ v : X,
      ((Function.update q.2.1.1 z none, q.2.1.2),
        (Function.update q.2.2.1.1 z (some v), q.2.2.1.2), q.2.2.2) ∉ Bad d N) :
    ∑ v : X, flipCost (Bad d N) (hwProgKraus (.programH z v)) 0 σ = 0 := by
  refine le_antisymm ((sum_flipCost_prog_le_card (Bad d N) (fun v : X ↦ HwProg.programH z v) 0 hσ
    fun q hq hσq ↦ ?_).trans (by simp)) (by simp)
  exact (card_programH_bad_eq_zero (D := q.2.1) (W := q.2.2.1) (m := q.2.2.2)
    (hsupp q hσq hq)).le

open scoped Classical in
/-- **Programming the final `h` cells of exempted structural slots' honest paths flips nothing**:
on states whose cell is not hardwired and is the final cell of the honest path of a structural
slot exempted once the cell is hardwired (`not_mem_bad_programH_honest`). -/
theorem flipCost_programH_honest (z : Z)
    {σ : Matrix (Unit × HwReg X Z (Mem S)) (Unit × HwReg X Z (Mem S)) ℂ} (hσ : σ.PosSemidef)
    (hsupp : ∀ q, σ q q ≠ 0 → q.2.2.1.1 z = none ∧ ∃ s xi₀, InTable s ∧
      (∀ v, s ∈ d.exS (Function.update q.2.2.1.1 z (some v), q.2.2.1.2)) ∧
        IsHeadTail d.perm (union q.2.2.1 q.2.1) (d.honTail s) z xi₀) :
    ∑ v : X, flipCost (Bad d N) (hwProgKraus (.programH z v)) 0 σ = 0 :=
  flipCost_programH_eq_zero z hσ fun q hσq hq v ↦ by
    obtain ⟨hW, s, xi₀, hT, hex, hi⟩ := hsupp q hσq
    exact not_mem_bad_programH_honest (D := q.2.1) (W := q.2.2.1) (m := q.2.2.2) hq hW v hT
      (hex v) hi

open scoped Classical in
/-- **Programming the `h` cells of exempted `H_msg` calls flips nothing**: on states whose cell is
not hardwired and is the final cell of an `H_msg` call's honest path, of call 1 or of a pair
exempted once the cell is hardwired (`not_mem_bad_programH_hmsg`). -/
theorem flipCost_programH_hmsg (z : Z)
    {σ : Matrix (Unit × HwReg X Z (Mem S)) (Unit × HwReg X Z (Mem S)) ℂ} (hσ : σ.PosSemidef)
    (hsupp : ∀ q, σ q q ≠ 0 → q.2.2.1.1 z = none ∧ ∃ (R : Randomizer) (msg : Message)
      (c : DigestCall) (xi₀ : X),
      (∀ v, c = 0 → (R, msg) ∈ d.covEx (Function.update q.2.2.1.1 z (some v), q.2.2.1.2)) ∧
        IsHeadTail d.perm (union q.2.2.1 q.2.1) (d.honTail (.hmsg R msg c)) z xi₀) :
    ∑ v : X, flipCost (Bad d N) (hwProgKraus (.programH z v)) 0 σ = 0 :=
  flipCost_programH_eq_zero z hσ fun q hσq hq v ↦ by
    obtain ⟨hW, R, msg, c, xi₀, hex, hi⟩ := hsupp q hσq
    exact not_mem_bad_programH_hmsg (D := q.2.1) (W := q.2.2.1) (m := q.2.2.2) hq hW v (hex v) hi

open scoped Classical in
/-- **Programming intermediate `h` cells of multi-block honest paths flips nothing**: on states
whose cell is not hardwired and whose head-tail is at a structural slot with a length other than
the slot's honest tail (`not_mem_bad_programH_short`). -/
theorem flipCost_programH_short (z : Z)
    {σ : Matrix (Unit × HwReg X Z (Mem S)) (Unit × HwReg X Z (Mem S)) ℂ} (hσ : σ.PosSemidef)
    (hsupp : ∀ q, σ q q ≠ 0 → q.2.2.1.1 z = none ∧ ∃ s t₀ xi₀, slotOf d.pk t₀ = some s ∧
      InTable s ∧ (d.honTail s).length ≠ t₀.length ∧
        IsHeadTail d.perm (union q.2.2.1 q.2.1) t₀ z xi₀) :
    ∑ v : X, flipCost (Bad d N) (hwProgKraus (.programH z v)) 0 σ = 0 :=
  flipCost_programH_eq_zero z hσ fun q hσq hq v ↦ by
    obtain ⟨hW, s, t₀, xi₀, h1, h2, h3, h4⟩ := hsupp q hσq
    exact not_mem_bad_programH_short (D := q.2.1) (W := q.2.2.1) (m := q.2.2.2) hq hW v h1 h2 h3
      h4

open scoped Classical in
/-- **Programming `k` cells, averaged over the value**: twice the capacity-scale count of
`preimageRateBound` over `|Z|`, on states whose cell is not hardwired, with at most `T - N`
database entries per function. -/
theorem flipCost_programK_avg_le {G T : ℕ} (hπ : PermGood d.perm G) (x : X)
    {σ : Matrix (Unit × HwReg X Z (Mem S)) (Unit × HwReg X Z (Mem S)) ℂ} (hσ : σ.PosSemidef)
    (hsupp : ∀ q, σ q q ≠ 0 → q.2.2.1.2.1 x = none ∧ N + dbGrade q.2.1 ≤ T) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ v : Z, flipCost (Bad d N) (hwProgKraus (.programK x v)) 0 σ ≤
      ((2 * ((T + 1) * ((T + 1) * T + 2 * T) * G) : ℕ) : ℝ≥0∞) / Fintype.card Z *
        ENNReal.ofReal σ.trace.re := by
  have h := sum_flipCost_prog_le_card (Bad d N) (fun v : Z ↦ HwProg.programK x v)
    (2 * ((T + 1) * ((T + 1) * T + 2 * T) * G)) hσ fun q hq hσq ↦
      card_flip_programK_bad_le (D := q.2.1) (W := q.2.2.1) (m := q.2.2.2) hπ hq
        (hsupp q hσq).2 (hsupp q hσq).1
  rw [ENNReal.div_eq_inv_mul, mul_assoc]
  exact mul_le_mul_right h _

open scoped Classical in
/-- **Programming `k'` cells, averaged over the value**: twice the capacity-scale count of
`preimageRateBound` over `|Z|`, on states whose cell is not hardwired, with at most `T - N`
database entries per function. -/
theorem flipCost_programK'_avg_le {G T : ℕ} (hπ : PermGood d.perm G) (x : X)
    {σ : Matrix (Unit × HwReg X Z (Mem S)) (Unit × HwReg X Z (Mem S)) ℂ} (hσ : σ.PosSemidef)
    (hsupp : ∀ q, σ q q ≠ 0 → q.2.2.1.2.2 x = none ∧ N + dbGrade q.2.1 ≤ T) :
    (Fintype.card Z : ℝ≥0∞)⁻¹ * ∑ v : Z, flipCost (Bad d N) (hwProgKraus (.programK' x v)) 0 σ ≤
      ((2 * ((T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T) : ℕ) : ℝ≥0∞) /
        Fintype.card Z * ENNReal.ofReal σ.trace.re := by
  have h := sum_flipCost_prog_le_card (Bad d N) (fun v : Z ↦ HwProg.programK' x v)
    (2 * ((T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T)) hσ fun q hq hσq ↦
      card_flip_programK'_bad_le (D := q.2.1) (W := q.2.2.1) (m := q.2.2.2) hπ hq
        (hsupp q hσq).2 (hsupp q hσq).1
  rw [ENNReal.div_eq_inv_mul, mul_assoc]
  exact mul_le_mul_right h _

end Prog

end Quantum.Sphincs

end
