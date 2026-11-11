module

public import Qrom.ProtHit
public import Mathlib.Data.List.NodupEquivFin

@[expose] public section

/-!
# Presampling the signer's digests by order

A game `gA Dg` whose signer answers the message `m` with the digest `Dg m`, read only for the
messages already signed, and a game `gB δ` that answers the `i`-th signed message with `δ i`, run
every program to the same joint post-state on the side state `s` when `Dg` and `δ` agree on the
messages signed in `s` (`Qrom.OvGame.conj_jointPost_eq_of_agreeOn` across the two families).
Averaged over `Dg` and over `δ`, an event of the first family is therefore at most an event of the
second that holds whenever the first does on corresponding digests
(`Qrom.OvGame.deferral_le`). The second event may read all of `δ`, such as a cover by all the
presampled digests.
-/

open Matrix OracleSpec
open scoped Kronecker ENNReal ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace Qrom

open Quantum Quantum.MatrixMap

namespace OvGame

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {S P : Type} [Fintype S] [DecidableEq S] {Res : P → Type} [∀ j, Fintype (Res j)]
  [∀ j, DecidableEq (Res j)]
variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}
variable {M V : Type} [Fintype M] [DecidableEq M] [Fintype V] [DecidableEq V] [Nonempty V]
variable {q : ℕ}

/-- `Dg` and `δ` agree on the messages of `l`: the `i`-th message of `l` has digest `δ i`. -/
def Corr (l : List M) (Dg : M → V) (δ : Fin q → V) : Prop :=
  ∀ i (hi : i < l.length) (hq : i < q), Dg (l.get ⟨i, hi⟩) = δ ⟨i, hq⟩

theorem Corr.of_prefix {l l' : List M} {Dg : M → V} {δ : Fin q → V} (h : Corr l Dg δ)
    (hp : l' <+: l) : Corr l' Dg δ := by
  intro i hi hq
  have hil : i < l.length := lt_of_lt_of_le hi hp.length_le
  rw [← h i hil hq]
  congr 1
  exact List.IsPrefix.getElem hp hi

/-! ## Fibers of the prefix maps -/

/-- The digests of the messages of `l`, in order. -/
def preA (l : List M) (Dg : M → V) : Fin l.length → V := fun i ↦ Dg (l.get i)

/-- The first `k` presampled digests. -/
def preB {k : ℕ} (hk : k ≤ q) (δ : Fin q → V) : Fin k → V := fun i ↦ δ (Fin.castLE hk i)

theorem corr_iff (l : List M) (hk : l.length ≤ q) (Dg : M → V) (δ : Fin q → V) :
    Corr l Dg δ ↔ preA l Dg = preB hk δ := by
  constructor
  · intro h
    funext i
    exact h i.1 i.2 (lt_of_lt_of_le i.2 hk)
  · intro h i hi hq
    have := congrFun h ⟨i, hi⟩
    simpa [preA, preB] using this

/-- The digest functions with given digests on the messages of a list without repetition are
the functions on the other messages. -/
noncomputable def fiberAEquiv (l : List M) (nd : l.Nodup) (a : Fin l.length → V) :
    {Dg : M → V // preA l Dg = a} ≃ ({m // m ∉ l} → V) where
  toFun Dg := fun m ↦ Dg.1 m.1
  invFun b := ⟨fun m ↦ if h : m ∈ l then a ((List.Nodup.getEquiv l nd).symm ⟨m, h⟩) else b ⟨m, h⟩, by
    funext i
    have hm : l.get i ∈ l := List.get_mem l i
    simp only [preA, hm, dite_true]
    congr 1
    apply (List.Nodup.getEquiv l nd).injective
    simp [List.Nodup.getEquiv]⟩
  left_inv Dg := by
    obtain ⟨Dg, hDg⟩ := Dg
    apply Subtype.ext
    funext m
    by_cases h : m ∈ l
    · simp only [h, dite_true]
      rw [← hDg]
      simp only [preA]
      congr 1
      simp [List.Nodup.getEquiv]
    · simp [h]
  right_inv b := by
    funext m
    simp [m.2]

theorem card_fiberA (l : List M) (nd : l.Nodup) (a : Fin l.length → V) :
    (Finset.univ.filter fun Dg : M → V ↦ preA l Dg = a).card =
      Fintype.card V ^ (Fintype.card M - l.length) := by
  rw [← Fintype.card_subtype, Fintype.card_congr (fiberAEquiv l nd a), Fintype.card_fun,
    Fintype.card_subtype_compl, ← Fintype.card_congr (List.Nodup.getEquiv l nd), Fintype.card_fin]

/-- The presampled digests with given first `k` entries are the remaining entries. -/
noncomputable def fiberBEquiv {k : ℕ} (hk : k ≤ q) (a : Fin k → V) :
    {δ : Fin q → V // preB hk δ = a} ≃ ({i : Fin q // ¬ i.1 < k} → V) where
  toFun δ := fun i ↦ δ.1 i.1
  invFun b := ⟨fun i ↦ if h : i.1 < k then a ⟨i.1, h⟩ else b ⟨i, h⟩, by
    funext i
    simp [preB, i.2]⟩
  left_inv δ := by
    obtain ⟨δ, hδ⟩ := δ
    apply Subtype.ext
    funext i
    by_cases h : i.1 < k
    · simp only [h, dite_true]
      rw [← hδ]
      rfl
    · simp [h]
  right_inv b := by
    funext i
    simp [i.2]

theorem card_fiberB {k : ℕ} (hk : k ≤ q) (a : Fin k → V) :
    (Finset.univ.filter fun δ : Fin q → V ↦ preB hk δ = a).card = Fintype.card V ^ (q - k) := by
  rw [← Fintype.card_subtype, Fintype.card_congr (fiberBEquiv hk a), Fintype.card_fun]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_fin]
  congr 1
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun i : Fin q ↦ i.1 < k) = (Finset.range k).attachFin
      (fun n hn ↦ lt_of_lt_of_le (Finset.mem_range.mp hn) hk) := by
    ext i
    simp
  rw [this, Finset.card_attachFin, Finset.card_range]

/-! ## The presampling inequality -/

section presample

variable (gA : (M → V) → OvGame X Y S P Res) (gB : (Fin q → V) → OvGame X Y S P Res)
  (sig : S → List M)

/-- The side states whose signed messages are a prefix of those of `s`. -/
def prefF (s : S) : Finset S := Finset.univ.filter fun s' ↦ sig s' <+: sig s

/-- The same, as a set. -/
abbrev pref (s : S) : Set S := ↑(prefF sig s)

theorem mem_pref {s s' : S} : s' ∈ pref sig s ↔ sig s' <+: sig s := by
  simp [pref, prefF]

/-- Corresponding digests give the same weight to the side state `s`. -/
theorem blockW_eq_of_corr
    (hmonoA : ∀ Dg j s, sig s <+: sig ((gA Dg).trans j s).2)
    (hmonoB : ∀ δ j s, sig s <+: sig ((gB δ).trans j s).2)
    (hcorr : ∀ Dg δ s, Corr (sig s) Dg δ → (gA Dg).ov s = (gB δ).ov s)
    (hcorrTr : ∀ Dg δ j s, Corr (sig ((gA Dg).trans j s).2) Dg δ ∨
      Corr (sig ((gB δ).trans j s).2) Dg δ → (gA Dg).trans j s = (gB δ).trans j s)
    (hinit : ∀ Dg δ, (gA Dg).init = (gB δ).init) (I : L.Interp) (G : X → Y)
    (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A) (p : Σ u, W u) (s : S)
    {Dg : M → V} {δ : Fin q → V} (h : Corr (sig s) Dg δ) :
    blockW s (((gA Dg).sampled G).jointPost I x ρ p).matrix =
      blockW s (((gB δ).sampled G).jointPost I x ρ p).matrix := by
  have hj := conj_jointPost_eq_of_agreeOn (U := pref sig s) (g₁ := gA Dg) (g₂ := gB δ) I
    (fun j' s' hs ↦ (mem_pref sig).mpr ((hmonoA Dg j' s').trans ((mem_pref sig).mp hs)))
    (fun j' s' hs ↦ (mem_pref sig).mpr ((hmonoB δ j' s').trans ((mem_pref sig).mp hs)))
    (fun s' hs' ↦ hcorr Dg δ s' (h.of_prefix ((mem_pref sig).mp hs')))
    (fun s' _ j hU ↦ hcorrTr Dg δ j s' (hU.imp (fun h' ↦ h.of_prefix ((mem_pref sig).mp h'))
      fun h' ↦ h.of_prefix ((mem_pref sig).mp h')))
    (hinit Dg δ) G x ρ p
  rw [← blockW_proj (pref sig s) s ((mem_pref sig).mpr List.prefix_rfl), hj,
    blockW_proj (pref sig s) s ((mem_pref sig).mpr List.prefix_rfl)]

/-- **The presampling inequality on one leaf and one side state.** -/
theorem deferral_block_le (hnd : ∀ s, (sig s).Nodup) (hlen : ∀ s, (sig s).length ≤ q)
    (hmonoA : ∀ Dg j s, sig s <+: sig ((gA Dg).trans j s).2)
    (hmonoB : ∀ δ j s, sig s <+: sig ((gB δ).trans j s).2)
    (hcorr : ∀ Dg δ s, Corr (sig s) Dg δ → (gA Dg).ov s = (gB δ).ov s)
    (hcorrTr : ∀ Dg δ j s, Corr (sig ((gA Dg).trans j s).2) Dg δ ∨
      Corr (sig ((gB δ).trans j s).2) Dg δ → (gA Dg).trans j s = (gB δ).trans j s)
    (hinit : ∀ Dg δ, (gA Dg).init = (gB δ).init)
    (eA : (M → V) → (Σ u, W u) → S → Bool) (eB : (Fin q → V) → (Σ u, W u) → S → Bool)
    (hev : ∀ Dg δ p s, Corr (sig s) Dg δ → eA Dg p s = true → eB δ p s = true)
    (I : L.Interp) (G : X → Y) (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A)
    (p : Σ u, W u) (s : S) :
    (Fintype.card (M → V) : ℝ≥0∞)⁻¹ * ∑ Dg, (if eA Dg p s then
        blockW s (((gA Dg).sampled G).jointPost I x ρ p).matrix else 0) ≤
      (Fintype.card (Fin q → V) : ℝ≥0∞)⁻¹ * ∑ δ, (if eB δ p s then
        blockW s (((gB δ).sampled G).jointPost I x ρ p).matrix else 0) := by
  set l := sig s
  set k := l.length
  have hk : k ≤ q := hlen s
  have hkM : k ≤ Fintype.card M := (hnd s).length_le_card
  have hblk := fun {Dg} {δ} (h : Corr l Dg δ) ↦
    blockW_eq_of_corr gA gB sig hmonoA hmonoB hcorr hcorrTr hinit I G x ρ p s h
  obtain ⟨v₀⟩ : Nonempty V := inferInstance
  rw [← Finset.sum_fiberwise Finset.univ (preA l), ← Finset.sum_fiberwise Finset.univ (preB hk),
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  -- representatives of the two fibers of `a`
  set δa : Fin q → V := fun i ↦ if h : i.1 < k then a ⟨i.1, h⟩ else v₀
  have hδa : preB hk δa = a := by
    funext i
    simp [preB, δa, i.2]
  set Dga : M → V := fun m ↦ if h : m ∈ l then a ((List.Nodup.getEquiv l (hnd s)).symm ⟨m, h⟩)
    else v₀
  have hDga : preA l Dga = a := by
    funext i
    have hm : l.get i ∈ l := List.get_mem l i
    simp only [preA, Dga, hm, dite_true]
    congr 1
    apply (List.Nodup.getEquiv l (hnd s)).injective
    simp [List.Nodup.getEquiv]
  set wa := blockW s (((gB δa).sampled G).jointPost I x ρ p).matrix
  have hwA : ∀ Dg ∈ Finset.univ.filter (fun Dg ↦ preA l Dg = a),
      blockW s (((gA Dg).sampled G).jointPost I x ρ p).matrix = wa := by
    intro Dg hDg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hDg
    exact hblk ((corr_iff l hk Dg δa).mpr (hDg.trans hδa.symm))
  have hwB : ∀ δ ∈ Finset.univ.filter (fun δ ↦ preB hk δ = a),
      blockW s (((gB δ).sampled G).jointPost I x ρ p).matrix = wa := by
    intro δ hδ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hδ
    rw [← hblk ((corr_iff l hk Dga δ).mpr (hDga.trans hδ.symm)),
      hblk ((corr_iff l hk Dga δa).mpr (hDga.trans hδa.symm))]
  have hcards : (Fintype.card (M → V) : ℝ≥0∞)⁻¹ *
      (Finset.univ.filter fun Dg ↦ preA l Dg = a).card =
      (Fintype.card (Fin q → V) : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun δ ↦ preB hk δ = a).card := by
    rw [card_fiberA l (hnd s) a, card_fiberB hk a, Fintype.card_fun, Fintype.card_fun,
      Fintype.card_fin]
    have hV : (Fintype.card V : ℝ≥0∞) ≠ 0 := by simp
    have hVt : (Fintype.card V : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have e1 : (Fintype.card V : ℝ≥0∞) ^ Fintype.card M =
        (Fintype.card V : ℝ≥0∞) ^ (Fintype.card M - k) * (Fintype.card V : ℝ≥0∞) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hkM]
    have e2 : (Fintype.card V : ℝ≥0∞) ^ q =
        (Fintype.card V : ℝ≥0∞) ^ (q - k) * (Fintype.card V : ℝ≥0∞) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    push_cast
    rw [e1, e2, ENNReal.mul_inv (Or.inl (pow_ne_zero _ hV)) (Or.inl (ENNReal.pow_ne_top hVt)),
      ENNReal.mul_inv (Or.inl (pow_ne_zero _ hV)) (Or.inl (ENNReal.pow_ne_top hVt)),
      mul_comm ((Fintype.card V : ℝ≥0∞) ^ (Fintype.card M - k))⁻¹, mul_assoc,
      ENNReal.inv_mul_cancel (pow_ne_zero _ hV) (ENNReal.pow_ne_top hVt),
      mul_comm ((Fintype.card V : ℝ≥0∞) ^ (q - k))⁻¹, mul_assoc,
      ENNReal.inv_mul_cancel (pow_ne_zero _ hV) (ENNReal.pow_ne_top hVt)]
  by_cases hex : ∃ Dg ∈ Finset.univ.filter (fun Dg ↦ preA l Dg = a), eA Dg p s = true
  · obtain ⟨Dg₀, hDg₀, he₀⟩ := hex
    have hall : ∀ δ ∈ Finset.univ.filter (fun δ ↦ preB hk δ = a), eB δ p s = true := by
      intro δ hδ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hδ hDg₀
      exact hev Dg₀ δ p s ((corr_iff l hk Dg₀ δ).mpr (hDg₀.trans hδ.symm)) he₀
    calc (Fintype.card (M → V) : ℝ≥0∞)⁻¹ *
          ∑ Dg ∈ Finset.univ.filter (fun Dg ↦ preA l Dg = a),
            (if eA Dg p s then blockW s (((gA Dg).sampled G).jointPost I x ρ p).matrix else 0)
        ≤ (Fintype.card (M → V) : ℝ≥0∞)⁻¹ *
          ∑ _Dg ∈ Finset.univ.filter (fun Dg ↦ preA l Dg = a), wa := by
          gcongr with Dg hDg
          split_ifs
          · exact (hwA Dg hDg).le
          · exact zero_le
      _ = (Fintype.card (Fin q → V) : ℝ≥0∞)⁻¹ *
          ∑ _δ ∈ Finset.univ.filter (fun δ ↦ preB hk δ = a), wa := by
          rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc,
            ← mul_assoc, hcards]
      _ = _ := by
          congr 1
          refine Finset.sum_congr rfl fun δ hδ ↦ ?_
          rw [ite_eq_left (hall δ hδ), hwB δ hδ]
  · push Not at hex
    have hz : ∑ Dg ∈ Finset.univ.filter (fun Dg ↦ preA l Dg = a),
        (if eA Dg p s then blockW s (((gA Dg).sampled G).jointPost I x ρ p).matrix else 0) = 0 :=
      Finset.sum_eq_zero fun Dg hDg ↦ by simp [hex Dg hDg]
    rw [hz, mul_zero]
    exact zero_le

/-- **Presampling the signer's digests.** -/
theorem deferral_le (hnd : ∀ s, (sig s).Nodup) (hlen : ∀ s, (sig s).length ≤ q)
    (hmonoA : ∀ Dg j s, sig s <+: sig ((gA Dg).trans j s).2)
    (hmonoB : ∀ δ j s, sig s <+: sig ((gB δ).trans j s).2)
    (hcorr : ∀ Dg δ s, Corr (sig s) Dg δ → (gA Dg).ov s = (gB δ).ov s)
    (hcorrTr : ∀ Dg δ j s, Corr (sig ((gA Dg).trans j s).2) Dg δ ∨
      Corr (sig ((gB δ).trans j s).2) Dg δ → (gA Dg).trans j s = (gB δ).trans j s)
    (hinit : ∀ Dg δ, (gA Dg).init = (gB δ).init)
    (eA : (M → V) → (Σ u, W u) → S → Bool) (eB : (Fin q → V) → (Σ u, W u) → S → Bool)
    (hev : ∀ Dg δ p s, Corr (sig s) Dg δ → eA Dg p s = true → eB δ p s = true)
    (I : L.Interp) (G : X → Y) (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A) :
    (Fintype.card (M → V) : ℝ≥0∞)⁻¹ * ∑ Dg, sideW (gA Dg) G I x ρ (eA Dg) ≤
      (Fintype.card (Fin q → V) : ℝ≥0∞)⁻¹ * ∑ δ, sideW (gB δ) G I x ρ (eB δ) := by
  simp only [sideW_eq_sum]
  rw [← Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable),
    ← Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable), ← ENNReal.tsum_mul_left,
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun p ↦ ?_
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ (α := Fin q → V)), Finset.mul_sum,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun s _ ↦
    deferral_block_le gA gB sig hnd hlen hmonoA hmonoB hcorr hcorrTr hinit eA eB hev I G x ρ p s

end presample

end OvGame

end Qrom
