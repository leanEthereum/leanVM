module

public import Quantum.Sphincs.Assembly.CostLift
public import Quantum.Xmss.Assembly.EncPotential

@[expose] public section

/-!
# The cross-key potential of leanSPHINCS's selecting reads

The joint count of the selecting reads of all WOTS+C trials of all keys `K = (l, τ, e)` is bounded
by a diagonal potential argument, as for leanXMSS (`Quantum.Xmss.Assembly.EncPotential`, whose
generic parts are reused: `OutAt`, `tailOutOff`, `re_trace_flipOp_le_good`, `dW`,
`sum_dW_conj_of_keep`, `totalWeight_le_potential_runtimeR_inv`), on CostLift's trial reads
(`TrialPt`, `IsTrial`, `trialOf`, `trialSR`, `massW`, `encW`). This file supplies the leanSPHINCS
potential, the trial-read port and the per-port quantities of the selecting reads.

* **The potential** (`encPot`): on a good union, `∑_{K unselected} encCwCount(·, K)`; `0` on a bad
  union. Label-free (`encPot_labelFree`), zero at the empty register (`encPot_init`). At a read
  cell `z` and a key `K₀` it splits (`encPot_eq`) into the other keys off `z` (`encA`), the key
  `K₀` off `z` (`encB`, `encOff`) and the indicator of the cell `z` counting for some unselected
  key (`encCSet`; at most one key in a good union: a tail has one slot).
* **A trial read** (`trialRead_drop_real`, `trialRead_potential_le`): `2^-15 e` plus the potential
  after the read is at most the potential before plus `trialChg`, with `ρ_c ≥ 2^-14`
  (`drop_of_survive_rho`); the other keys keep their part (`encA_keep`); after the read the cell
  counts only off `TrialGood` (the key unselected, the trial's block at the encoding slot of `K`
  and the head-tail of `z`).
* **Along a run** (`totalWeight_cntGW_le`): the joint count `cntGW` along a run of `runtimeR` is at
  most `2^15 (q + P)` plus `2^15` times the charges, given the port conditions of the sponge, other
  read and program ports as hypotheses.
* **Links to the flip costs** (`encW_le_cntGW`, `trialChg_le_massW`, `cwRecW_le_massW`): the
  codeword flips are at most `2^-128 cntGW` on states with a good union off the event; the trial
  charge is at most `(3C + 3) massW + (2/|X| + 4/|X|²) tr σ` where the count is at most `C`; the
  codeword-recorded mass `cwRecW` is part of `massW`.
-/

universe u v w

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Assembly Quantum.Xmss.Hybrid Sphincs
open Quantum.Xmss (X Z trunc128 card_X extProgCharge)

namespace Quantum.Sphincs.Assembly

/-! ## The potential -/

/-- The encoding slot of key `K`. -/
def EncAt (d : EvData) (K : Key) (t : List X) : Prop :=
  slotOf d.pk t = some (.enc K.1 K.2.1 K.2.2)

theorem encAt_unique (d : EvData) (K K' : Key) (t : List X) (h : EncAt d K t)
    (h' : EncAt d K' t) : K = K' := by
  obtain ⟨h1, h2, h3⟩ := Slot.enc.inj (Option.some.inj (h.symm.trans h'))
  exact Prod.ext h1 (Prod.ext h2 h3)

theorem encCwCount_eq_tailOutCount (d : EvData) (U : Dbs X Z) (K : Key) :
    encCwCount d U K = tailOutCount d.perm U trunc128 (EncAt d K) Codeword.Valid :=
  rfl

/-- **Off the event, with few hardwired cells, the union is good.** -/
theorem good_of_not_mem_bad {S : Type} {d : EvData} {N : ℕ} {D : DbReg X Z} {W : Hw X Z}
    {m : Mem S} (h : (D, W, m) ∉ Bad d N) (hN : dbGrade W ≤ N) : Good d.perm (union W D) :=
  (not_mem_targetBad_iff.1 (union_not_mem_of_not_mem_hwTargetBad (fun h' ↦ h (.inl h')) hN)).1

section pot

variable {M : Type} [Fintype M] [DecidableEq M] (get : M → Selections)

open scoped Classical in
/-- **The cross-key potential**: on a good union, the codeword counts `encCwCount` of the
unselected keys; `0` on a bad union. -/
noncomputable def encPot (d : EvData) (s : HwReg X Z M) : ℝ :=
  if Good d.perm (union s.2.1 s.1) then
    ∑ K : Key, if get s.2.2 K = none then (encCwCount d (union s.2.1 s.1) K : ℝ) else 0
  else 0

open scoped Classical in
/-- The count of key `K` off the cell `z`, on a good union. -/
noncomputable def encOff (d : EvData) (z : Z) (K : Key) (s : HwReg X Z M) : ℝ :=
  if Good d.perm (union s.2.1 s.1) then
    (tailOutOff d.perm (union s.2.1 s.1) trunc128 (EncAt d K) Codeword.Valid z : ℝ) else 0

/-- The part of the potential of the keys other than `K₀`, off the cell `z`. -/
noncomputable def encA (d : EvData) (z : Z) (K₀ : Key) (s : HwReg X Z M) : ℝ :=
  ∑ K : Key, if K ≠ K₀ ∧ get s.2.2 K = none then encOff d z K s else 0

/-- The part of the potential of key `K₀`, off the cell `z`. -/
noncomputable def encB (d : EvData) (z : Z) (K₀ : Key) (s : HwReg X Z M) : ℝ :=
  if get s.2.2 K₀ = none then encOff d z K₀ s else 0

/-- The states whose cell `z` counts for an unselected key, on a good union. -/
def encCSet (d : EvData) (z : Z) : Set (HwReg X Z M) :=
  {s | Good d.perm (union s.2.1 s.1) ∧ ∃ K : Key, get s.2.2 K = none ∧
    OutAt d.perm (union s.2.1 s.1) trunc128 (EncAt d K) Codeword.Valid z}

/-- Membership in `encCSet`, decided classically. -/
noncomputable instance encCSetDec (d : EvData) (z : Z) :
    DecidablePred (· ∈ encCSet get d z) :=
  Classical.decPred _

omit [Fintype M] [DecidableEq M] in
theorem encOff_nonneg (d : EvData) (z : Z) (K : Key) (s : HwReg X Z M) :
    0 ≤ encOff d z K s := by
  unfold encOff
  split_ifs <;> positivity

omit [Fintype M] [DecidableEq M] in
theorem encPot_nonneg (d : EvData) (s : HwReg X Z M) : 0 ≤ encPot get d s := by
  unfold encPot
  split_ifs
  · exact Finset.sum_nonneg fun K _ ↦ by split_ifs <;> positivity
  · exact le_rfl

omit [Fintype M] [DecidableEq M] in
/-- **The potential at a read cell `z` and a key `K₀`**: the other keys off `z`, the key `K₀` off
`z`, and the cell `z` itself (at most one key counts it in a good union). -/
theorem encPot_eq (d : EvData) (z : Z) (K₀ : Key) (q : Unit × HwReg X Z M) :
    encPot get d q.2 = encA get d z K₀ q.2 + encB get d z K₀ q.2 +
      ind (liftSet (encCSet get d z)) q := by
  classical
  have hind : ind (liftSet (encCSet get d z)) q = if q.2 ∈ encCSet get d z then 1 else 0 := by
    unfold ind
    exact if_congr (mem_liftSet _ q) rfl rfl
  rw [hind]
  unfold encPot encA encB encOff
  by_cases hG : Good d.perm (union q.2.2.1 q.2.1)
  · simp only [hG, ↓reduceIte]
    have hsplit : ∀ K : Key, (if get q.2.2.2 K = none then
        (encCwCount d (union q.2.2.1 q.2.1) K : ℝ) else 0) =
        (if get q.2.2.2 K = none then (tailOutOff d.perm (union q.2.2.1 q.2.1) trunc128
          (EncAt d K) Codeword.Valid z : ℝ) else 0) +
        (if get q.2.2.2 K = none ∧ OutAt d.perm (union q.2.2.1 q.2.1) trunc128 (EncAt d K)
          Codeword.Valid z then 1 else 0) := fun K ↦ by
      rw [encCwCount_eq_tailOutCount, tailOutCount_eq_off_add _ _ _ _ _ z]
      by_cases hu : get q.2.2.2 K = none
      · by_cases ho : OutAt d.perm (union q.2.2.1 q.2.1) trunc128 (EncAt d K) Codeword.Valid z
        · simp only [hu, ho, and_self, ↓reduceIte, Nat.cast_add, Nat.cast_one]
        · simp only [hu, ho, and_false, ↓reduceIte, add_zero]
      · simp only [hu, false_and, ↓reduceIte, add_zero]
    rw [Finset.sum_congr rfl fun K _ ↦ hsplit K, Finset.sum_add_distrib,
      sum_ite_split (fun K : Key ↦ get q.2.2.2 K = none) _ K₀,
      sum_ite_one_of_unique _ fun K K' h h' ↦ outAt_unique hG (EncAt d) (encAt_unique d)
        Codeword.Valid h.2 h'.2]
    have hmem : q.2 ∈ encCSet get d z ↔ ∃ K : Key, get q.2.2.2 K = none ∧
        OutAt d.perm (union q.2.2.1 q.2.1) trunc128 (EncAt d K) Codeword.Valid z :=
      ⟨fun h ↦ h.2, fun h ↦ ⟨hG, h⟩⟩
    rw [if_congr hmem rfl rfl]
  · have hmem : q.2 ∉ encCSet get d z := fun h ↦ hG h.1
    simp only [hG, ↓reduceIte, hmem, ite_self, Finset.sum_const_zero, add_zero]

end pot

/-! ## A selecting read, against the potential -/

/-- **The trial updates**: a trial read of an unselected key records the codeword selection
(`cwSel`), and no read changes the other keys. -/
structure CwTrialUpd {M : Type} (get : M → Selections) (updOf : TrialPt → M → Option X → M) :
    Prop where
  sel : ∀ t m v, get m t.K = none → get (updOf t m (some v)) = cwSel (get m) t.K t.x t.xi v
  keep : ∀ t m o (K : Key), K ≠ t.K → get (updOf t m o) K = get m K

/-- **The template's trial updates on the labelled memory** (`cwUpd`, the label kept) record
codeword selections. -/
theorem cwTrialUpd_cwUpd (S : Type) :
    CwTrialUpd (Prod.snd : Mem S → Selections)
      (fun t m o ↦ (m.1, cwUpd t.K t.x t.xi m.2 o)) where
  sel t m v hm := (snd_pair m.1 _).trans (cwUpd_some_of_none t.K t.x t.xi hm v)
  keep t m o K hK := by
    refine (congrFun (snd_pair m.1 (cwUpd t.K t.x t.xi m.2 o)) K).trans ?_
    rcases o with _ | v
    · rfl
    · rcases cwUpd_some t.K t.x t.xi m.2 v with h | h <;> rw [h]
      rcases cwSel_eq m.2 t.K t.x t.xi v with h' | h' <;> rw [h']
      exact Selections.select_of_ne _ _ _ hK

/-- **A survival bound as a drop**: for a codeword rate `ρ ≥ 2^-14`, the survival bound
`A ≤ w - ρ e + p + 2 √(ρ e p)` gives `2^-15 e + A ≤ w + 3 p` (`2 √(ρ e p) ≤ ρ e / 2 + 2 p`). -/
theorem drop_of_survive_rho {A w e p ρ : ℝ} (he : 0 ≤ e) (hp : 0 ≤ p) (hρ : (2 ^ 14 : ℝ)⁻¹ ≤ ρ)
    (h : A ≤ w - ρ * e + p + 2 * √(ρ * e * p)) : (2 ^ 15 : ℝ)⁻¹ * e + A ≤ w + 3 * p := by
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρ
  have hρe : 0 ≤ ρ * e := mul_nonneg hρ0 he
  have hsq : 2 * √(ρ * e * p) ≤ ρ * e / 2 + 2 * p := by
    rw [Real.sqrt_mul hρe]
    have h1 := Real.sq_sqrt hρe
    have h2 := Real.sq_sqrt hp
    nlinarith [sq_nonneg (√(ρ * e) - 2 * √p)]
  have h15 : (2 ^ 15 : ℝ)⁻¹ * e ≤ ρ / 2 * e := by
    refine mul_le_mul_of_nonneg_right ?_ he
    have : (2 ^ 15 : ℝ)⁻¹ = (2 ^ 14 : ℝ)⁻¹ / 2 := by norm_num
    rw [this]
    linarith
  nlinarith

section trial

variable {M : Type} [Fintype M] [DecidableEq M] (get : M → Selections)
  (updOf : TrialPt → M → Option X → M)

/-- **The states where the read cell cannot count after a trial read**: a bad union, or the
trial's key unselected, the trial's block at the encoding slot of its key and the head-tail of the
cell `z` (the support invariant of the trial reads). -/
def TrialGood (d : EvData) (z : Z) (t : TrialPt) (s : HwReg X Z M) : Prop :=
  ¬ Good d.perm (union s.2.1 s.1) ∨ (get s.2.2 t.K = none ∧ EncAt d t.K [t.x] ∧
    IsHeadTail d.perm (union s.2.1 s.1) [t.x] z t.xi)

omit [Fintype M] [DecidableEq M] in
/-- **After a trial read the read cell does not count**: on `TrialGood` states, recording any value
`y` at `z` with the trial's update leaves `encCSet`. -/
theorem not_mem_encCSet_of_trialGood (hu : CwTrialUpd get updOf) {d : EvData} {z : Z}
    {t : TrialPt} {s s' : HwReg X Z M} {y : X} (hg : TrialGood get d z t s)
    (hk : (union s'.2.1 s'.1).k = (union s.2.1 s.1).k)
    (hk' : (union s'.2.1 s'.1).k' = (union s.2.1 s.1).k') (hz : (union s'.2.1 s'.1).h z = some y)
    (hm : s'.2.2 = updOf t s.2.2 (some y)) : s' ∉ encCSet get d z := by
  rintro ⟨hG', K, hun, t', xi', w, hP, hi, hw, hcw⟩
  have hG : Good d.perm (union s.2.1 s.1) := (good_congr hk hk').1 hG'
  rcases hg with hg | ⟨hm0, hslot, hhead⟩
  · exact hg hG
  have hhead' := (isHeadTail_congr hk.symm hk'.symm).1 hhead
  obtain ⟨rfl, rfl⟩ := hG'.isHeadTail_unique hi hhead'
  obtain rfl := encAt_unique d _ _ _ hP hslot
  rw [hz] at hw
  obtain rfl := Option.some.inj hw
  rw [hm, hu.sel t _ y hm0] at hun
  exact ((cwSel_eq_none_iff hm0 t.x t.xi y).1 hun) hcw

omit [Fintype M] [DecidableEq M] in
open scoped Classical in
/-- The counts off `z` do not see the cell `z` nor the memory. -/
theorem encOff_offCell (d : EvData) (z : Z) (K : Key) :
    OffCell z (encOff (M := M) d z K) := by
  intro s s' h1 h2 h3
  obtain ⟨hk, hk', hh⟩ := union_congr_off h1 h2 h3
  unfold encOff
  rw [tailOutOff_congr hk hk' hh]
  exact if_congr (good_congr hk hk') rfl rfl

omit [Fintype M] [DecidableEq M] in
theorem encA_congr (d : EvData) (z : Z) (K₀ : Key) {s s' : HwReg X Z M}
    (h1 : ∀ b, b ≠ z → s'.1.1 b = s.1.1 b) (h2 : s'.1.2 = s.1.2) (h3 : s'.2.1 = s.2.1)
    (hm : ∀ K : Key, K ≠ K₀ → get s'.2.2 K = get s.2.2 K) :
    encA get d z K₀ s' = encA get d z K₀ s := by
  unfold encA
  refine Finset.sum_congr rfl fun K _ ↦ ?_
  by_cases hK : K = K₀
  · rw [ite_eq_right fun h ↦ absurd hK h.1, ite_eq_right fun h ↦ absurd hK h.1]
  · rw [hm K hK, encOff_offCell d z K s s' h1 h2 h3]

omit [Fintype M] in
/-- A nonzero entry of a trial read keeps the part of the potential of the other keys. -/
theorem encA_keep (hu : CwTrialUpd get updOf) (d : EvData) (z : Z) (t : TrialPt)
    (r : Option X × M) (a a' : Unit × HwReg X Z M)
    (h : hwReadKraus (.readH z (updOf t)) r a' a ≠ 0) :
    encA get d z t.K a'.2 = encA get d z t.K a.2 := by
  obtain ⟨-, h'⟩ := one_kronecker_ne_zero (a := a.1) (a' := a'.1) (b := a.2) (b' := a'.2) h
  obtain ⟨h1, h2, h3⟩ := readKrausH_ne_zero_rest z (updOf t) r h'
  obtain ⟨hm1, hm2⟩ := readKrausH_mem z (updOf t) r h'
  refine encA_congr get d z _ h1 h2 h3 fun K hK ↦ ?_
  rw [hm2, hu.keep t _ _ K hK, hm1]

open scoped Classical in
/-- **A trial read against the potential** (real form). For a trial `t` read at the cell `z`, on
a state with no decompressed `⊥` there, `2^-15 e` plus the potential after the read is at most
the potential before plus `3 p` and the cell's own charge: `e` and `p` are the count of key `t.K`
off `z` on the selection reads and off them (`survive_readH_weighted_le`, `drop_of_survive_rho`),
the other keys keep their part (`encA_keep`), and the cell `z` counts after the read only off
`TrialGood` (at most `2`), by re-compression (`2/|X| + 4/|X|²`) and on its recorded mass
(`re_trace_flipOp_le_good`). -/
theorem trialRead_drop_real (hu : CwTrialUpd get updOf) (d : EvData) (z : Z) (t : TrialPt)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hnb : CellNoBot (splitH' z) (actH z) σ) :
    (2 ^ 15 : ℝ)⁻¹ * (∑ q, if SelectRead d q.2.1 q.2.2.1 (get q.2.2.2) z t.K t.x t.xi then
        encOff d z t.K q.2 * (σ q q).re else 0) +
      ∑ r : Option X × M, dW (fun q ↦ encPot get d q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) ≤
    dW (fun q ↦ encPot get d q.2) σ +
      3 * (∑ q, if SelectRead d q.2.1 q.2.2.1 (get q.2.2.2) z t.K t.x t.xi then 0 else
        encOff d z t.K q.2 * (σ q q).re) +
      ∑ q, ((if TrialGood get d z t q.2 then 2 / (Fintype.card X : ℝ) +
        (2 / (Fintype.card X : ℝ)) ^ 2 else 2) + pd (splitH' z) (actH z) (fun _ _ ↦ True) q) *
        (σ q q).re := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hsplit : ∀ τ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ,
      dW (fun q ↦ encPot get d q.2) τ = dW (fun q ↦ encA get d z t.K q.2) τ +
        dW (fun q ↦ encB get d z t.K q.2) τ +
        dW (fun q ↦ ind (liftSet (encCSet get d z)) q) τ := fun τ ↦ by
    simp only [dW, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [encPot_eq get d z t.K q]
    ring
  -- The other keys.
  have hA : ∑ r : Option X × M, dW (fun q ↦ encA get d z t.K q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) =
        dW (fun q ↦ encA get d z t.K q.2) σ :=
    sum_dW_conj_of_keep (fun r : Option X × M ↦ hwReadKraus (.readH z (updOf t)) r) _
      (fun r a a' h ↦ encA_keep get updOf hu d z t r a a' h) (sum_readKrausH z (updOf t)) σ
  -- The key of the trial, off the cell.
  have hn0 : ∀ s : HwReg X Z M, 0 ≤ encOff d z t.K s := encOff_nonneg d z t.K
  have hupdT : ∀ m ∈ {m : M | get m t.K = none}, ∀ v,
      updOf t m (some v) ∈ {m : M | get m t.K = none} ↔
        ¬ Codeword.Valid (trunc128 (t.xi + v)) := fun m hm v ↦ by
    have hm' : get m t.K = none := hm
    show get (updOf t m (some v)) t.K = none ↔ _
    rw [hu.sel t m v hm']
    exact cwSel_eq_none_iff hm' t.x t.xi v
  have hsurv := survive_readH_weighted_le z (updOf t) {m : M | get m t.K = none}
    (fun v ↦ Codeword.Valid (trunc128 (t.xi + v))) (card_codeword_div_card_X t.xi) hupdT
    (fun s ↦ SelectRead d s.1 s.2.1 (get s.2.2) z t.K t.x t.xi)
    (fun s hs ↦ ⟨hs.hd, hs.hw, hs.hm⟩) hn0 (encOff_offCell d z t.K) hσ
  have he : 0 ≤ ∑ q, if SelectRead d q.2.1 q.2.2.1 (get q.2.2.2) z t.K t.x t.xi then
      encOff d z t.K q.2 * (σ q q).re else 0 :=
    Finset.sum_nonneg fun q _ ↦ by
      split_ifs
      · exact mul_nonneg (hn0 _) (hre q)
      · exact le_rfl
  have hp : 0 ≤ ∑ q, if SelectRead d q.2.1 q.2.2.1 (get q.2.2.2) z t.K t.x t.xi then 0 else
      encOff d z t.K q.2 * (σ q q).re :=
    Finset.sum_nonneg fun q _ ↦ by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (hn0 _) (hre q)
  have hdrop := drop_of_survive_rho he hp inv_two_pow_14_le_rhoCw hsurv
  have hBpost : ∀ r : Option X × M, dW (fun q ↦ encB get d z t.K q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) =
      if updOf t r.2 r.1 ∈ {m : M | get m t.K = none} then
        ∑ q, encOff d z t.K q.2 *
          ((MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) q q).re else 0 := by
    intro r
    have hq : ∀ q, encB get d z t.K q.2 *
        ((MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) q q).re =
        if updOf t r.2 r.1 ∈ {m : M | get m t.K = none} then encOff d z t.K q.2 *
          ((MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) q q).re else 0 := by
      intro q
      by_cases hqm : q.2.2.2 = updOf t r.2 r.1
      · have hB : encB get d z t.K q.2 =
            if updOf t r.2 r.1 ∈ {m : M | get m t.K = none} then
              encOff d z t.K q.2 else 0 := by
          show (if get q.2.2.2 t.K = none then encOff d z t.K q.2 else 0) = _
          rw [hqm]
          exact if_congr Iff.rfl rfl rfl
        rw [hB]
        split_ifs <;> ring
      · rw [conj_readH_diag_eq_zero z (updOf t) r σ hqm, Complex.zero_re, mul_zero, mul_zero,
          ite_self]
    unfold dW
    rw [Finset.sum_congr rfl fun q _ ↦ hq q]
    split_ifs
    · rfl
    · exact Finset.sum_const_zero
  have hBpre : dW (fun q ↦ encB get d z t.K q.2) σ =
      ∑ q, if q.2.2.2 ∈ {m : M | get m t.K = none} then
        encOff d z t.K q.2 * (σ q q).re else 0 := by
    unfold dW
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    show (if get q.2.2.2 t.K = none then encOff d z t.K q.2 else 0) * (σ q q).re = _
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1 h2
    · exact absurd h2 h1
    · exact zero_mul _
  -- The cell itself.
  have hgood : ∀ q : Unit × HwReg X Z M, TrialGood get d z t q.2 → actH z (splitH' z q).2 →
      ∀ y, ind (liftSet (encCSet get d z))
        ((splitH' z).symm (some y, tauH z (updOf t) (some y) (splitH' z q).2)) = 0 := by
    intro q hg ha y
    have ha' : q.2.2.1.1 z = none := ha
    have hnot : ((Function.update q.2.1.1 z (some y), q.2.1.2), q.2.2.1,
        updOf t q.2.2.2 (some y)) ∉ encCSet get d z := by
      exact not_mem_encCSet_of_trialGood get updOf hu hg (union_k_h _ _ _ _)
        (union_k'_h _ _ _ _) (union_h_upd q.2.2.1 q.2.1.1 q.2.1.2 z y ha') rfl
    rw [splitH'_symm_tau]
    exact ind_eq_zero_of_not_mem (liftSet (encCSet get d z)) hnot
  have hgoodH : ∀ q : Unit × HwReg X Z M, TrialGood get d z t q.2 → ¬ actH z (splitH' z q).2 →
      ind (liftSet (encCSet get d z)) (phiH z (updOf t) q) = 0 := by
    intro q hg ha
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 (show q.2.2.1.1 z ≠ none from ha)
    refine ind_eq_zero_of_not_mem _ fun h ↦ not_mem_encCSet_of_trialGood get updOf hu (y := w)
      (s' := (q.2.1, q.2.2.1, updOf t q.2.2.2 (q.2.2.1.1 z))) hg rfl rfl ?_ ?_
      ((mem_liftSet _ _).1 h)
    · show (q.2.2.1.1 z).or (q.2.1.1 z) = some w
      rw [hw]
      rfl
    · show updOf t q.2.2.2 (q.2.2.1.1 z) = updOf t q.2.2.2 (some w)
      rw [hw]
  have hC := re_trace_flipOp_le_good (liftSet (encCSet get d z)) (cellRead_readH z (updOf t))
    (clsOff_readH z (updOf t)) (fun q ↦ TrialGood get d z t q.2) hgood hgoodH hσ hnb
  have hsumeq : (∑ r : Option X × M, (hwReadKraus (.readH z (updOf t)) r)ᴴ *
      diagonal (fun q ↦ ((ind (liftSet (encCSet get d z)) q : ℝ) : ℂ)) *
        hwReadKraus (.readH z (updOf t)) r) =
      flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z (updOf t)) r)
        (liftSet (encCSet get d z)) + indProj (liftSet (encCSet get d z)) := by
    rw [flipOp, sub_add_cancel]
    rfl
  have hCpost : ∑ r : Option X × M, dW (fun q ↦ ind (liftSet (encCSet get d z)) q)
      (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) =
      dW (fun q ↦ ind (liftSet (encCSet get d z)) q) σ +
        (flipOp (fun r : Option X × M ↦ hwReadKraus (.readH z (updOf t)) r)
          (liftSet (encCSet get d z)) * σ).trace.re := by
    rw [sum_dW_conj, hsumeq, Matrix.add_mul, Matrix.trace_add, Complex.add_re, add_comm,
      dW_eq_trace]
    rfl
  -- Together.
  have hpost : ∑ r : Option X × M, dW (fun q ↦ encPot get d q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) =
      ∑ r : Option X × M, dW (fun q ↦ encA get d z t.K q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) +
      ∑ r : Option X × M, dW (fun q ↦ encB get d z t.K q.2)
        (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) +
      ∑ r : Option X × M, dW (fun q ↦ ind (liftSet (encCSet get d z)) q)
        (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) := by
    simp only [hsplit, Finset.sum_add_distrib]
  rw [hpost, hsplit σ, hA, hCpost, Finset.sum_congr rfl fun r _ ↦ hBpost r, hBpre]
  linarith [hdrop, hC]

open scoped Classical in
/-- The count of a trial's key off the read cell on the selection reads (the `e` of the survival
bound): on a selection read the cell is empty, so this is `encCwCount` on a good union
(`encOff_of_selectRead`). -/
noncomputable def trialCnt (d : EvData) (z : Z) (t : TrialPt)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ :=
  ∑ q, if SelectRead d q.2.1 q.2.2.1 (get q.2.2.2) z t.K t.x t.xi then
    encOff d z t.K q.2 * (σ q q).re else 0

open scoped Classical in
/-- The weighted mass off the selection reads (the `p` of the survival bound). -/
noncomputable def trialOffW (d : EvData) (z : Z) (t : TrialPt)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ :=
  ∑ q, if SelectRead d q.2.1 q.2.2.1 (get q.2.2.2) z t.K t.x t.xi then 0 else
    encOff d z t.K q.2 * (σ q q).re

open scoped Classical in
/-- The charge of the read cell itself: `2/|X| + 4/|X|²` on `TrialGood` states, `2` elsewhere,
plus the recorded mass of the cell (`pd`). -/
noncomputable def trialCellW (d : EvData) (z : Z) (t : TrialPt)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ :=
  ∑ q, ((if TrialGood get d z t q.2 then 2 / (Fintype.card X : ℝ) +
    (2 / (Fintype.card X : ℝ)) ^ 2 else 2) + pd (splitH' z) (actH z) (fun _ _ ↦ True) q) *
    (σ q q).re

open scoped Classical in
/-- **The joint count of the selecting reads**, per port: `trialCnt` at a trial read port. -/
noncomputable def cntGW (d : EvData) (c : HwRead X Z M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  if IsTrial updOf c then
    ENNReal.ofReal (trialCnt get d (trialOf updOf c).1 (trialOf updOf c).2 σ) else 0

open scoped Classical in
/-- **The charge of a trial read port** against the potential: `3 p` plus the cell's charge. -/
noncomputable def trialChg (d : EvData) (c : HwRead X Z M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  if IsTrial updOf c then ENNReal.ofReal (3 * trialOffW get d (trialOf updOf c).1
    (trialOf updOf c).2 σ + trialCellW get d (trialOf updOf c).1 (trialOf updOf c).2 σ) else 0

omit [DecidableEq M] in
theorem trialCnt_nonneg (d : EvData) (z : Z) (t : TrialPt)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    0 ≤ trialCnt get d z t σ :=
  Finset.sum_nonneg fun q _ ↦ by
    split_ifs
    · exact mul_nonneg (encOff_nonneg d z _ _) (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    · exact le_rfl

/-- The potential of the hardwired register as a weighted diagonal. -/
theorem potential_encPot (d : EvData)
    (τ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) :
    potential (diagPot fun s ↦ √(encPot get d s)) τ =
      ENNReal.ofReal (dW (fun q ↦ encPot get d q.2) τ) :=
  potential_diagPot_sqrt (encPot_nonneg get d) τ

/-- **A trial read port against the potential**: on a state with no decompressed `⊥` at the read
cell, `2^-15 cntGW` plus the potential after the read is at most the potential before plus
`trialChg` (`trialRead_drop_real`). -/
theorem trialRead_potential_le (hu : CwTrialUpd get updOf) (d : EvData) {c : HwRead X Z M}
    (ht : IsTrial updOf c) {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef) (hnb : ReadNoBot c σ) :
    (2 ^ 15 : ℝ≥0∞)⁻¹ * cntGW get updOf d c σ +
        ∑' r, potential (diagPot fun s ↦ √(encPot get d s)) (MatrixMap.conj (hwReadKraus c r) σ) ≤
      potential (diagPot fun s ↦ √(encPot get d s)) σ + trialChg get updOf d c σ := by
  have hc := eq_readH_trialOf updOf ht
  simp only [cntGW, trialChg, ht, ↓reduceIte]
  generalize trialOf updOf c = zt at hc ⊢
  subst hc
  obtain ⟨z, t⟩ := zt
  have hreal := trialRead_drop_real get updOf hu d z t hσ hnb
  have h15 : (2 ^ 15 : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((2 ^ 15 : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
  have hpost : ∀ r : Option X × M, 0 ≤ dW (fun q ↦ encPot get d q.2)
      (MatrixMap.conj (hwReadKraus (.readH z (updOf t)) r) σ) := fun r ↦
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (encPot_nonneg get d q.2)
      (Complex.nonneg_iff.1 (posSemidef_conj _ hσ).diag_nonneg).1
  rw [tsum_fintype]
  simp only [potential_encPot]
  rw [← ENNReal.ofReal_sum_of_nonneg fun r _ ↦ hpost r, h15,
    ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (mul_nonneg (by positivity) (trialCnt_nonneg get d z t hσ))
      (Finset.sum_nonneg fun r _ ↦ hpost r)]
  refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
  have hr := hreal
  unfold trialCnt trialOffW trialCellW
  linarith [hr]

omit [Fintype M] [DecidableEq M] in
/-- **On a selection read the count off the read cell is the codeword count** (the cell is
empty), on a good union. -/
theorem encOff_of_selectRead (d : EvData) {s : HwReg X Z M} {z : Z} {t : TrialPt}
    (hs : SelectRead d s.1 s.2.1 (get s.2.2) z t.K t.x t.xi)
    (hG : Good d.perm (union s.2.1 s.1)) :
    encOff d z t.K s = (encCwCount d (union s.2.1 s.1) t.K : ℝ) := by
  have hz : (union s.2.1 s.1).h z = none := by
    rw [union_h, hs.hw, hs.hd]
    rfl
  have hout : ¬ OutAt d.perm (union s.2.1 s.1) trunc128 (EncAt d t.K) Codeword.Valid z :=
    fun ⟨_, _, _, _, _, hw, _⟩ ↦ by rw [hz] at hw; cases hw
  unfold encOff
  rw [ite_eq_left hG, encCwCount_eq_tailOutCount d _ t.K,
    tailOutCount_eq_off_add _ _ _ _ _ z, ite_eq_right hout, add_zero]

omit [DecidableEq M] in
/-- **The codeword flips of the selecting reads against the joint count**: on states off `B`
whose union is good, the codeword flips (`encW`) are at most `2^-128 cntGW` (for `B` Events'
`Bad d N`, `good_of_not_mem_bad`). -/
theorem encW_le_cntGW (B : Set (HwReg X Z M)) [DecidablePred (· ∈ B)] {d : EvData}
    (c : HwRead X Z M) {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef)
    (hG : ∀ q, σ q q ≠ 0 → q.2 ∉ B → Good d.perm (union q.2.2.1 q.2.1)) :
    encW get updOf B d c σ ≤ ENNReal.ofReal (2 ^ 128)⁻¹ * cntGW get updOf d c σ := by
  by_cases ht : IsTrial updOf c
  · simp only [encW, cntGW, ht, ↓reduceIte]
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    rw [encWt, trialCnt, Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    by_cases hq : trialSR get updOf d c q.2 ∧ q.2 ∉ B
    · rw [ite_eq_left hq]
      have hsr := trialSR_of_isTrial get updOf ht hq.1
      rw [ite_eq_left hsr]
      by_cases h0 : σ q q = 0
      · rw [h0, Complex.zero_re, mul_zero, mul_zero, mul_zero]
      · rw [encOff_of_selectRead get d hsr (hG q h0 hq.2), Nat.cast_mul, Nat.cast_pow,
          Nat.cast_ofNat, mul_div_assoc, Quantum.Xmss.two_pow_div_card_X]
        exact le_of_eq (by ring)
    · rw [ite_eq_right hq]
      refine mul_nonneg (by positivity) ?_
      split_ifs
      · exact mul_nonneg (encOff_nonneg d _ _ _) (hre q)
      · exact le_rfl
  · simp only [encW, cntGW, ht, ↓reduceIte, mul_zero, le_refl]

open scoped Classical in
/-- **The trial charge against the recorded mass** (`massW`, the weight off the selection reads):
if the count off the read cell is at most `C` on the support, the charge is at most
`(3C + 3) massW + (2/|X| + 4/|X|²) tr σ`. -/
theorem trialChg_le_massW (d : EvData) {c : HwRead X Z M} (ht : IsTrial updOf c) {C : ℝ}
    (hC0 : 0 ≤ C) {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hC : ∀ q, encOff d (trialOf updOf c).1 (trialOf updOf c).2.K q.2 ≤ C ∨ σ q q = 0) :
    trialChg get updOf d c σ ≤ ENNReal.ofReal (3 * C + 3) * massW get updOf d c σ +
      ENNReal.ofReal ((2 / (Fintype.card X : ℝ) + (2 / (Fintype.card X : ℝ)) ^ 2) *
        σ.trace.re) := by
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  simp only [trialChg, massW, PRof, ht, ↓reduceIte]
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
  set z := (trialOf updOf c).1
  set t := (trialOf updOf c).2
  set a : ℝ := 2 / (Fintype.card X : ℝ) + (2 / (Fintype.card X : ℝ)) ^ 2
  have ha : a ≤ 1 := by
    have hN : (4 : ℝ) ≤ Fintype.card X := by
      rw [card_X, Nat.cast_pow, Nat.cast_ofNat]
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ 1088 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have h2 : 2 / (Fintype.card X : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have h0 : 0 ≤ 2 / (Fintype.card X : ℝ) := by positivity
    nlinarith
  have hsr : ∀ q : Unit × HwReg X Z M, trialSR get updOf d c q.2 ↔
      SelectRead d q.2.1 q.2.2.1 (get q.2.2.2) z t.K t.x t.xi := fun q ↦
    ⟨trialSR_of_isTrial get updOf ht, fun h ↦ .inl ⟨ht, h⟩⟩
  rw [re_trace_readPs, Matrix.trace, Complex.re_sum, Finset.mul_sum, Finset.mul_sum, trialOffW,
    trialCellW, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  rw [Matrix.diag_apply]
  have hpd := pd_mem (e := splitH' z) (act := actH z) (fun _ _ ↦ True) q
  by_cases hq : SelectRead d q.2.1 q.2.2.1 (get q.2.2.2) z t.K t.x t.xi
  · have hg : TrialGood get d z t q.2 := by
      by_cases hG : Good d.perm (union q.2.2.1 q.2.1)
      · exact .inr ⟨hq.hm, hq.slot, hq.head⟩
      · exact .inl hG
    have hpd0 : pd (splitH' z) (actH z) (fun _ _ ↦ True) q = 0 := by
      unfold pd
      split_ifs
      · rw [show (splitH' z q).1 = q.2.1.1 z from rfl, hq.hd]
        rfl
      · rfl
    rw [ite_eq_left hq, ite_eq_left ((hsr q).2 hq), ite_eq_left hg, hpd0]
    simp only [mul_zero, add_zero, zero_add]
    exact le_rfl
  · rw [ite_eq_right hq, ite_eq_right fun h ↦ hq ((hsr q).1 h)]
    have hpd1 : pd (splitH' z) (actH z) (fun _ _ ↦ True) q ≤ 1 := by
      rcases hpd with h | h <;> rw [h]; norm_num
    have hcell : (if TrialGood get d z t q.2 then a else 2) ≤ 2 := by
      split_ifs
      · linarith
      · exact le_rfl
    have hoff : encOff d z t.K q.2 * (σ q q).re ≤ C * (σ q q).re := by
      rcases hC q with h | h
      · exact mul_le_mul_of_nonneg_right h (hre q)
      · rw [h, Complex.zero_re, mul_zero, mul_zero]
    have ha0 : 0 ≤ a := by positivity
    nlinarith [hre q, mul_le_mul_of_nonneg_right (add_le_add hcell hpd1) (hre q)]

open scoped Classical in
/-- **The codeword-recorded mass of a trial read port**: the states whose read cell `z` is recorded
by the adversary (in the database, not hardwired) with a value `v` that selects the trial's
unselected key (`trunc128 (xi + v)` a codeword). This contains the flip-recorded mass of
ReadCost's cross term for the trial's selecting update (a recorded value moves the memory only by
a selection). -/
noncomputable def cwRecW (c : HwRead X Z M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  if IsTrial updOf c then ENNReal.ofReal (∑ q, if q.2.2.1.1 (trialOf updOf c).1 = none ∧
      get q.2.2.2 (trialOf updOf c).2.K = none ∧
      ∃ v, q.2.1.1 (trialOf updOf c).1 = some v ∧
        Codeword.Valid (trunc128 ((trialOf updOf c).2.xi + v)) then (σ q q).re else 0)
  else 0

/-- The codeword-recorded mass is part of the mass off the selection reads (`massW`). -/
theorem cwRecW_le_massW (d : EvData) (c : HwRead X Z M)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    cwRecW get updOf c σ ≤ massW get updOf d c σ := by
  by_cases ht : IsTrial updOf c
  · simp only [cwRecW, massW, PRof, ht, ↓reduceIte]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [re_trace_readPs]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    have hre : 0 ≤ (σ q q).re := (Complex.nonneg_iff.1 hσ.diag_nonneg).1
    split_ifs with h1 h2
    · obtain ⟨v, hv, -⟩ := h1.2.2
      have hd := (trialSR_of_isTrial get updOf ht h2).hd
      rw [hd] at hv
      cases hv
    · exact le_rfl
    · exact le_rfl
    · exact hre
  · simp only [cwRecW, ht, ↓reduceIte, zero_le]

end trial

/-! ## The joint count of the selecting reads -/

section joint

variable {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']
  (get : Finset S × M' → Selections) (updOf : TrialPt → Finset S × M' → Option X → Finset S × M')
  {Λ : LocalSig.{u, v}} {Ω : QReg → Type w}

omit [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
theorem encPot_labelFree (hlab : ∀ (T T' : Finset S) (m : M'), get (T, m) = get (T', m))
    (d : EvData) : PotLabelFree (encPot get d) := by
  intro D W T T' m
  simp only [encPot, hlab T T' m]

omit [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
theorem encPot_init (d : EvData) (m₀ : Finset S × M') :
    encPot get d ((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀) = 0 := by
  unfold encPot
  split_ifs
  · refine Finset.sum_eq_zero fun K _ ↦ ?_
    split_ifs
    · rw [encCwCount_eq_tailOutCount, tailOutCount_eq_zero (fun z ↦ union_empty_h z),
        Nat.cast_zero]
    · rfl
  · rfl

/-- **The joint count of the selecting reads along a run of `runtimeR`**, before averaging. Let
the trial updates record codeword selections (`CwTrialUpd`) and not read the memory label; let the
calls of `x` satisfy port invariants `Inv` (through `P`) under which every trial read port has no
decompressed `⊥` at its cell, every sponge call raises the potential `encPot` by at most its trace
plus `cS`, every other read by at most `cR` and every program call by at most its trace plus `cP`.
With at most `q` sponge calls and `P'` program calls, the joint count `cntGW` (the codeword counts
of the trials' keys on their selection reads, on good unions) along the run is at most
`2^15 (q + P')` plus `2^15` times the charges along the run: `cS`, `cP`, `cR` and at the trial
reads `trialChg`. -/
theorem totalWeight_cntGW_le (hu : CwTrialUpd get updOf)
    (hlab : ∀ (T T' : Finset S) (m : M'), get (T, m) = get (T', m)) (d : EvData)
    (m₀ : Finset S × M')
    (P : ∀ (i : (recHwSpec X Z S M').Port) (E : QReg),
      Matrix (((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) × E)
        (((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) × E) ℂ → Prop)
    (Inv : ∀ i : (recHwSpec X Z S M').Port,
      Matrix ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D)
        ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) ℂ → Prop)
    (hP : ∀ i E σ, P i E σ → Inv i (MatrixMap.traceRight _ E σ))
    (cS : ∀ p : SpongePort, Matrix (spongeIn X Z p × HwReg X Z (Finset S × M'))
      (spongeIn X Z p × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (cR : HwRead X Z (Finset S × M') → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (cP : HwProg X Z → Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞)
    (hS : ∀ p (σ : Matrix (spongeIn X Z p × HwReg X Z (Finset S × M'))
        (spongeIn X Z p × HwReg X Z (Finset S × M')) ℂ), σ.PosSemidef →
      Inv (.inl (.inl (.inl p))) σ →
      ∑' _r : Unit, potential (diagPot fun s ↦ √(encPot get d s))
          (MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U p) σ) ≤
        potential (diagPot fun s ↦ √(encPot get d s)) σ + (ENNReal.ofReal σ.trace.re + cS p σ))
    (hR : ∀ c (σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ),
      ¬ IsTrial updOf c → σ.PosSemidef → Inv (.inl (.inl (.inr c))) σ →
      ∑' r, potential (diagPot fun s ↦ √(encPot get d s)) (MatrixMap.conj (hwReadKraus c r) σ) ≤
        potential (diagPot fun s ↦ √(encPot get d s)) σ + cR c σ)
    (hnb : ∀ c (σ : Matrix (Unit × HwReg X Z (Finset S × M'))
        (Unit × HwReg X Z (Finset S × M')) ℂ), IsTrial updOf c → Inv (.inl (.inl (.inr c))) σ →
      ReadNoBot c σ)
    (hPr : ∀ c (σ : Matrix (Unit × HwReg X Z (Finset S × M'))
        (Unit × HwReg X Z (Finset S × M')) ℂ), σ.PosSemidef → Inv (.inl (.inr c)) σ →
      ∑' r, potential (diagPot fun s ↦ √(encPot get d s)) (MatrixMap.conj (hwProgKraus c r) σ) ≤
        potential (diagPot fun s ↦ √(encPot get d s)) σ + (ENNReal.ofReal σ.trace.re + cP c σ))
    (I : Λ.Interp) {B : Type} [Fintype B] [DecidableEq B] (u : B)
    (x : QuantumComp Λ (recHwSpec X Z S M') Ω (QReg.of B)) {q P' : ℕ}
    (hq : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Finset S × M') (recSpec S M') i then 0 else 1) q)
    (hp : IFreeM.IsChargeBound x (portCharge (extProgCharge X Z (Finset S × M') (recSpec S M')))
      P')
    (hx : (runtimeR m₀).ForallQueries I P x
      ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)) :
    (runtimeR m₀).totalWeight I (extWeight (hwCost (cntGW get updOf d) fun _ _ ↦ 0)) x
        ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) ≤
      2 ^ 15 * (q + P' : ℕ) + 2 ^ 15 * (runtimeR m₀).totalWeight I
        (portCh X Z S M' cS (fun c σ ↦ trialChg get updOf d c σ + cR c σ) cP) x
        ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) := by
  set ρ := (SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix
  have hρ : ρ.PosSemidef :=
    ((SubState.basis u).prod (runtimeR (X := X) (Z := Z) m₀).init).posSemidef
  have hφ0 := encPot_nonneg get d
  have hp0 : potential (diagPot fun s ↦ √(encPot get d s)) ρ = 0 :=
    (potential_basis_init m₀ hφ0 u).trans
      ((congrArg ENNReal.ofReal (encPot_init get d m₀)).trans ENNReal.ofReal_zero)
  have htr : ENNReal.ofReal ρ.trace.re ≤ 1 := (ofReal_trace_basis_init m₀ u).le
  have hR' : ∀ c (σ : Matrix (Unit × HwReg X Z (Finset S × M'))
      (Unit × HwReg X Z (Finset S × M')) ℂ), σ.PosSemidef → Inv (.inl (.inl (.inr c))) σ →
      (2 ^ 15 : ℝ≥0∞)⁻¹ * cntGW get updOf d c σ + ∑' r, potential
        (diagPot fun s ↦ √(encPot get d s)) (MatrixMap.conj (hwReadKraus c r) σ) ≤
        potential (diagPot fun s ↦ √(encPot get d s)) σ +
          (0 + (trialChg get updOf d c σ + cR c σ)) := by
    intro c σ hσ hI
    rw [zero_add]
    by_cases ht : IsTrial updOf c
    · exact (trialRead_potential_le get updOf hu d ht hσ (hnb c σ ht hI)).trans
        (add_le_add le_rfl le_self_add)
    · have h0 : cntGW get updOf d c σ = 0 := by simp only [cntGW, ht, ↓reduceIte]
      have h1 : trialChg get updOf d c σ = 0 := by simp only [trialChg, ht, ↓reduceIte]
      rw [h0, h1, mul_zero, zero_add, zero_add]
      exact hR c σ ht hσ hI
  have h := totalWeight_le_potential_runtimeR_inv m₀ hφ0 (encPot_labelFree get hlab d) P Inv hP
    (fun c σ ↦ (2 ^ 15 : ℝ≥0∞)⁻¹ * cntGW get updOf d c σ)
    (fun p σ ↦ ENNReal.ofReal σ.trace.re + cS p σ)
    (fun c σ ↦ 0 + (trialChg get updOf d c σ + cR c σ))
    (fun c σ ↦ ENNReal.ofReal σ.trace.re + cP c σ) hS hR' hPr I x hρ hx
  have hlow : (2 ^ 15 : ℝ≥0∞)⁻¹ *
      (runtimeR m₀).totalWeight I (extWeight (hwCost (cntGW get updOf d) fun _ _ ↦ 0)) x ρ ≤
      (runtimeR m₀).totalWeight I (extWeight (hwCost
        (fun c σ ↦ (2 ^ 15 : ℝ≥0∞)⁻¹ * cntGW get updOf d c σ) fun _ _ ↦ 0)) x ρ := by
    refine (le_of_eq (totalWeight_const_mul_weight (runtimeR m₀) I _
      (extWeight (hwCost (cntGW get updOf d) fun _ _ ↦ 0)) x ρ).symm).trans
      (totalWeight_le_totalWeight (runtimeR m₀) I (fun i σ _ ↦ ?_) x hρ)
    rcases i with ((_ | _) | _) | _
    · exact le_of_eq (mul_zero _)
    · exact le_rfl
    · exact le_of_eq (mul_zero _)
    · exact le_of_eq (mul_zero _)
  have hsplit := (totalWeight_le_totalWeight (runtimeR m₀) I
    (w := portCh X Z S M' (fun p σ ↦ ENNReal.ofReal σ.trace.re + cS p σ)
      (fun c σ ↦ 0 + (trialChg get updOf d c σ + cR c σ))
      (fun c σ ↦ ENNReal.ofReal σ.trace.re + cP c σ))
    (w' := fun i σ ↦ portCh X Z S M' (fun _ σ ↦ ENNReal.ofReal σ.trace.re) (fun _ _ ↦ 0)
        (fun _ σ ↦ ENNReal.ofReal σ.trace.re) i σ +
      portCh X Z S M' cS (fun c σ ↦ trialChg get updOf d c σ + cR c σ) cP i σ)
    (fun i σ _ ↦ le_of_eq (congrFun (congrFun (portCh_add _ _ _ _ _ _) i) σ)) x hρ).trans
    (le_of_eq (totalWeight_add_weight (runtimeR m₀) I _ _ x ρ))
  have ht := (totalWeight_portCh_trace_le m₀ I x hq hp hρ).trans
    ((mul_le_mul_of_nonneg_left htr zero_le).trans_eq (mul_one _))
  have hmain := hlow.trans (h.trans ((add_le_add (le_of_eq hp0) le_rfl).trans_eq (zero_add _)
    |>.trans (hsplit.trans (add_le_add ht le_rfl))))
  have h2 : (2 ^ 15 : ℝ≥0∞) ≠ 0 := by positivity
  have h2' : (2 ^ 15 : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have e : ∀ w : ℝ≥0∞, w = 2 ^ 15 * ((2 ^ 15 : ℝ≥0∞)⁻¹ * w) := fun w ↦ by
    rw [← mul_assoc, ENNReal.mul_inv_cancel h2 h2', one_mul]
  exact (e _).trans_le ((mul_le_mul_of_nonneg_left hmain zero_le).trans_eq (mul_add _ _ _))

end joint

end Quantum.Sphincs.Assembly

end
