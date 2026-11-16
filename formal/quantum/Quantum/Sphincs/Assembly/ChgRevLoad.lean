module

public import Quantum.Xmss.Hybrid.Seed
public import Quantum.Xmss.Hybrid.R0Stage

@[expose] public section

/-!
# Loads of capacities that are translates of a uniform function at distinct rates

The capacity of a one-block input `b` is `base b + k' (rate b)`. When the rates are distinct, the
values `k' (rate b)` of a uniform `k'` are independent and uniform, so collisions between the
capacities are rare. Here, over abstract types:

* `card_pow_mul_sum_forall_le`: the values at `|J|` distinct points all lying in sets of at most
  `s` elements that do not depend on these values: at most `(s / |Z|)^|J|` of the functions.
* `card_mul_sum_sibs_le`: a pair among `sibs` with equal capacities: at most `|sibs| / |Z|`.
* `loadK`: the pairs of an own block (`μ b = m`) and a foreign block with equal capacities. More
  than `2 L` of them needs three own blocks at one capacity or `L + 1` foreign blocks hitting the
  own capacities (`triple_or_hits_of_lt`); `card_pow_mul_sum_triple_le`,
  `card_pow_mul_sum_hits_le` count both.
-/

open scoped ENNReal

namespace Quantum.Sphincs.Assembly

/-! ## Values at distinct points in small sets -/

section resample

variable {X Z B : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [DecidableEq B]

/-- **Values at distinct points in small sets.** If the values of `g` at the distinct points
`ι b` (`b ∈ J`) must lie in sets of at most `s` elements that do not depend on these values, at
most `(s / |Z|)^|J|` of the functions qualify. -/
theorem card_pow_mul_sum_forall_le (ι : B → X) (hι : Function.Injective ι)
    (S : B → (X → Z) → Finset Z) (s : ℕ) (J : Finset B)
    (hS : ∀ b ∈ J, ∀ g, (S b g).card ≤ s)
    (hdep : ∀ b ∈ J, ∀ b' ∈ J, ∀ g w, S b (Function.update g (ι b') w) = S b g) :
    Fintype.card Z ^ J.card * ∑ g : X → Z, (if ∀ b ∈ J, g (ι b) ∈ S b g then 1 else 0) ≤
      s ^ J.card * Fintype.card (X → Z) := by
  induction J using Finset.induction_on with
  | empty => simp
  | insert b₀ J hb₀ ih =>
    have hS' : ∀ b ∈ J, ∀ g, (S b g).card ≤ s := fun b hb ↦ hS b (Finset.mem_insert_of_mem hb)
    have hdep' : ∀ b ∈ J, ∀ b' ∈ J, ∀ g w, S b (Function.update g (ι b') w) = S b g :=
      fun b hb b' hb' ↦ hdep b (Finset.mem_insert_of_mem hb) b' (Finset.mem_insert_of_mem hb')
    have hstep : ∀ g : X → Z, ∑ w : Z,
        (if ∀ b ∈ insert b₀ J, Function.update g (ι b₀) w (ι b) ∈
          S b (Function.update g (ι b₀) w) then 1 else 0) ≤
        s * (if ∀ b ∈ J, g (ι b) ∈ S b g then 1 else 0) := by
      intro g
      have hiff : ∀ w, (∀ b ∈ insert b₀ J, Function.update g (ι b₀) w (ι b) ∈
          S b (Function.update g (ι b₀) w)) ↔ (w ∈ S b₀ g ∧ ∀ b ∈ J, g (ι b) ∈ S b g) := by
        intro w
        rw [Finset.forall_mem_insert, Function.update_self,
          hdep b₀ (Finset.mem_insert_self _ _) b₀ (Finset.mem_insert_self _ _)]
        refine and_congr Iff.rfl (forall₂_congr fun b hb ↦ ?_)
        have hne : ι b ≠ ι b₀ := fun h ↦ hb₀ (hι h ▸ hb)
        rw [Function.update_of_ne hne,
          hdep b (Finset.mem_insert_of_mem hb) b₀ (Finset.mem_insert_self _ _)]
      simp only [hiff]
      split_ifs with hJ
      · rw [mul_one, ← Finset.card_filter]
        exact (Finset.card_le_card fun w hw ↦ (Finset.mem_filter.mp hw).2.1).trans
          (hS b₀ (Finset.mem_insert_self _ _) g)
      · simp [hJ]
    have h1 := Quantum.Xmss.Hybrid.card_mul_sum_eq_sum_sum_update
      (fun g : X → Z ↦ if ∀ b ∈ insert b₀ J, g (ι b) ∈ S b g then 1 else 0) (ι b₀)
    have h2 : Fintype.card Z * ∑ g : X → Z,
        (if ∀ b ∈ insert b₀ J, g (ι b) ∈ S b g then 1 else 0) ≤
        s * ∑ g : X → Z, (if ∀ b ∈ J, g (ι b) ∈ S b g then 1 else 0) := by
      rw [h1, Finset.mul_sum]
      exact Finset.sum_le_sum fun g _ ↦ hstep g
    rw [Finset.card_insert_of_notMem hb₀, pow_succ, pow_succ]
    calc Fintype.card Z ^ J.card * Fintype.card Z *
          ∑ g : X → Z, (if ∀ b ∈ insert b₀ J, g (ι b) ∈ S b g then 1 else 0)
        = Fintype.card Z ^ J.card * (Fintype.card Z *
          ∑ g : X → Z, (if ∀ b ∈ insert b₀ J, g (ι b) ∈ S b g then 1 else 0)) := by ring
      _ ≤ Fintype.card Z ^ J.card *
          (s * ∑ g : X → Z, (if ∀ b ∈ J, g (ι b) ∈ S b g then 1 else 0)) :=
          Nat.mul_le_mul_left _ h2
      _ = s * (Fintype.card Z ^ J.card *
          ∑ g : X → Z, (if ∀ b ∈ J, g (ι b) ∈ S b g then 1 else 0)) := by ring
      _ ≤ s * (s ^ J.card * Fintype.card (X → Z)) := Nat.mul_le_mul_left _ (ih hS' hdep')
      _ = s ^ J.card * s * Fintype.card (X → Z) := by ring

end resample

/-! ## Capacities at distinct rates -/

section caps

variable {X Z B : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z]
  [Fintype B] [DecidableEq B] (rate : B → X) (base : B → Z)

/-- The capacity of a block: its base translated by `k'` at its rate. -/
def blkCap (g : X → Z) (b : B) : Z :=
  base b + g (rate b)

omit [Fintype X] [Fintype Z] [DecidableEq Z] [Fintype B] [DecidableEq B] in
theorem blkCap_update_of_ne (g : X → Z) {b : B} {x : X} (hx : rate b ≠ x) (w : Z) :
    blkCap rate base (Function.update g x w) b = blkCap rate base g b := by
  unfold blkCap
  rw [Function.update_of_ne hx]

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Fintype B] [DecidableEq B] in
theorem blkCap_eq_iff' (g : X → Z) (b : B) (c : Z) :
    blkCap rate base g b = c ↔ g (rate b) = c - base b := by
  unfold blkCap
  rw [eq_sub_iff_add_eq, add_comm]

omit [Fintype B] in
/-- **Two blocks with equal capacities**: at most `1 / |Z|` of the functions. -/
theorem card_mul_sum_blkCap_eq_le (hr : Function.Injective rate) {b₁ b₂ : B} (h : b₁ ≠ b₂) :
    Fintype.card Z * ∑ g : X → Z,
        (if blkCap rate base g b₁ = blkCap rate base g b₂ then 1 else 0) ≤
      Fintype.card (X → Z) := by
  have hne : rate b₁ ≠ rate b₂ := fun e ↦ h (hr e)
  have h' := card_pow_mul_sum_forall_le rate hr
    (fun _ g ↦ ({blkCap rate base g b₁ - base b₂} : Finset Z)) 1 {b₂}
    (fun _ _ _ ↦ (Finset.card_singleton _).le) fun b hb b' hb' g w ↦ by
      rw [Finset.mem_singleton] at hb'
      subst hb'
      rw [blkCap_update_of_ne rate base g hne]
  simp only [Finset.card_singleton, pow_one, one_mul] at h'
  refine le_trans (le_of_eq ?_) h'
  congr 1
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  simp only [Finset.mem_singleton, forall_eq, eq_comm (a := blkCap rate base g b₁), blkCap_eq_iff']

omit [Fintype B] in
/-- **A pair among `sib` with equal capacities**: at most `|I| / |Z|` of the functions. -/
theorem card_mul_sum_sibs_le (hr : Function.Injective rate) {I : Type} [Fintype I]
    (sib : I → B × B) (hsib : ∀ i, (sib i).1 ≠ (sib i).2) :
    Fintype.card Z * ∑ g : X → Z,
        (if ∃ i, blkCap rate base g (sib i).1 = blkCap rate base g (sib i).2 then 1 else 0) ≤
      Fintype.card I * Fintype.card (X → Z) := by
  calc Fintype.card Z * ∑ g : X → Z,
        (if ∃ i, blkCap rate base g (sib i).1 = blkCap rate base g (sib i).2 then 1 else 0)
      ≤ Fintype.card Z * ∑ g : X → Z, ∑ i,
          (if blkCap rate base g (sib i).1 = blkCap rate base g (sib i).2 then 1 else 0) := by
        refine Nat.mul_le_mul_left _ (Finset.sum_le_sum fun g _ ↦ ?_)
        split_ifs with h
        · obtain ⟨i, he⟩ := h
          exact le_trans (by simp [he]) (Finset.single_le_sum
            (f := fun i ↦ if blkCap rate base g (sib i).1 = blkCap rate base g (sib i).2 then 1
              else 0)
            (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i))
        · exact Nat.zero_le _
    _ = ∑ i, Fintype.card Z * ∑ g : X → Z,
          (if blkCap rate base g (sib i).1 = blkCap rate base g (sib i).2 then 1 else 0) := by
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ _i : I, Fintype.card (X → Z) :=
        Finset.sum_le_sum fun i _ ↦ card_mul_sum_blkCap_eq_le rate base hr (hsib i)
    _ = Fintype.card I * Fintype.card (X → Z) := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]

variable {Mg : Type} [DecidableEq Mg] (μ : B → Mg)

/-- The blocks of `m`. -/
def ownB (m : Mg) : Finset B :=
  Finset.univ.filter fun b ↦ μ b = m

/-- The blocks of the other labels. -/
def fgnB (m : Mg) : Finset B :=
  Finset.univ.filter fun b ↦ μ b ≠ m

/-- **The load of `m`**: the pairs of a block of `m` and a block of another label with equal
capacities. -/
def loadK (g : X → Z) (m : Mg) : ℕ :=
  ((ownB μ m ×ˢ fgnB μ m).filter fun p ↦ blkCap rate base g p.1 = blkCap rate base g p.2).card

/-- Three distinct blocks of `m` at one capacity. -/
def TripleK (g : X → Z) (m : Mg) : Prop :=
  ∃ b₁ ∈ ownB μ m, ∃ b₂ ∈ ownB μ m, ∃ b₃ ∈ ownB μ m, b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₂ ≠ b₃ ∧
    blkCap rate base g b₂ = blkCap rate base g b₁ ∧ blkCap rate base g b₃ = blkCap rate base g b₁

/-- The foreign blocks hitting a capacity of `m`. -/
def hitsK (g : X → Z) (m : Mg) : Finset B :=
  (fgnB μ m).filter fun b' ↦ ∃ b ∈ ownB μ m, blkCap rate base g b = blkCap rate base g b'

omit [Fintype X] [DecidableEq X] [Fintype Z] in
/-- **A large load** needs three blocks of `m` at one capacity or more than `L` foreign blocks
hitting the capacities of `m`. -/
theorem triple_or_hits_of_lt (g : X → Z) (m : Mg) (L : ℕ) (h : 2 * L < loadK rate base μ g m) :
    TripleK rate base μ g m ∨ L + 1 ≤ (hitsK rate base μ g m).card := by
  by_contra hc
  push Not at hc
  obtain ⟨hT, hH⟩ := hc
  set P := (ownB μ m ×ˢ fgnB μ m).filter fun p ↦ blkCap rate base g p.1 = blkCap rate base g p.2
    with hP
  have himg : P.image Prod.snd ⊆ hitsK rate base μ g m := by
    intro b' hb'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb'
    obtain ⟨hpm, he⟩ := Finset.mem_filter.mp hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hpm
    exact Finset.mem_filter.mpr ⟨h2, p.1, h1, he⟩
  have hfib : ∀ b' ∈ P.image Prod.snd, (P.filter fun p ↦ p.2 = b').card ≤ 2 := by
    intro b' _
    have hinj : ((P.filter fun p ↦ p.2 = b').image Prod.fst).card =
        (P.filter fun p ↦ p.2 = b').card :=
      Finset.card_image_of_injOn fun p hp q hq e ↦ by
        have := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
        have := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
        exact Prod.ext e (by simp_all)
    rw [← hinj]
    by_contra hlt
    push Not at hlt
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hlt
    have hmem : ∀ x ∈ (P.filter fun p ↦ p.2 = b').image Prod.fst,
        x ∈ ownB μ m ∧ blkCap rate base g x = blkCap rate base g b' := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpm, he⟩ := Finset.mem_filter.mp hp1
      exact ⟨(Finset.mem_product.mp hpm).1, hp2 ▸ he⟩
    obtain ⟨ha1, ha2⟩ := hmem a ha
    obtain ⟨hb1, hb2⟩ := hmem b hb
    obtain ⟨hc1, hc2⟩ := hmem c hc
    exact hT ⟨a, ha1, b, hb1, c, hc1, hab, hac, hbc, hb2.trans ha2.symm, hc2.trans ha2.symm⟩
  have hcard := Finset.card_le_mul_card_image P 2 hfib
  have := (Finset.card_le_card himg).trans (Nat.lt_succ_iff.mp hH)
  unfold loadK at h
  rw [← hP] at h
  omega

/-- **Three blocks of `m` at one capacity**: at most `n³ / |Z|²` of the functions, for `n` blocks
of `m`. -/
theorem card_pow_mul_sum_triple_le (hr : Function.Injective rate) (m : Mg) [DecidablePred
    (TripleK rate base μ · m)] :
    Fintype.card Z ^ 2 * ∑ g : X → Z, (if TripleK rate base μ g m then 1 else 0) ≤
      (ownB μ m).card ^ 3 * Fintype.card (X → Z) := by
  set O := ownB μ m
  have hpt : ∀ b₁ b₂ b₃ : B, b₁ ≠ b₂ → b₁ ≠ b₃ → b₂ ≠ b₃ →
      Fintype.card Z ^ 2 * ∑ g : X → Z, (if blkCap rate base g b₂ = blkCap rate base g b₁ ∧
        blkCap rate base g b₃ = blkCap rate base g b₁ then 1 else 0) ≤ Fintype.card (X → Z) := by
    intro b₁ b₂ b₃ h12 h13 h23
    have h' := card_pow_mul_sum_forall_le rate hr
      (fun b g ↦ ({blkCap rate base g b₁ - base b} : Finset Z)) 1 {b₂, b₃}
      (fun _ _ _ ↦ (Finset.card_singleton _).le) fun b _ b' hb' g w ↦ by
        have hne : rate b₁ ≠ rate b' := by
          rcases Finset.mem_insert.mp hb' with rfl | hb'
          · exact fun e ↦ h12 (hr e)
          · rw [Finset.mem_singleton.mp hb']
            exact fun e ↦ h13 (hr e)
        show ({blkCap rate base (Function.update g (rate b') w) b₁ - base b} : Finset Z) = _
        rw [blkCap_update_of_ne rate base g hne]
    rw [Finset.card_pair h23, one_pow, one_mul] at h'
    refine le_trans (le_of_eq ?_) h'
    congr 1
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq, blkCap_eq_iff']
  calc Fintype.card Z ^ 2 * ∑ g : X → Z, (if TripleK rate base μ g m then 1 else 0)
      ≤ Fintype.card Z ^ 2 * ∑ g : X → Z, ∑ b₁ ∈ O, ∑ b₂ ∈ O, ∑ b₃ ∈ O,
          (if b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₂ ≠ b₃ ∧ blkCap rate base g b₂ = blkCap rate base g b₁ ∧
            blkCap rate base g b₃ = blkCap rate base g b₁ then 1 else 0) := by
        refine Nat.mul_le_mul_left _ (Finset.sum_le_sum fun g _ ↦ ?_)
        split_ifs with h
        · obtain ⟨b₁, h1, b₂, h2, b₃, h3, hc⟩ := h
          refine le_trans ?_ (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) h1)
          refine le_trans ?_ (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) h2)
          refine le_trans ?_ (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) h3)
          simp [hc]
        · exact Nat.zero_le _
    _ = ∑ b₁ ∈ O, ∑ b₂ ∈ O, ∑ b₃ ∈ O, Fintype.card Z ^ 2 * ∑ g : X → Z,
          (if b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₂ ≠ b₃ ∧ blkCap rate base g b₂ = blkCap rate base g b₁ ∧
            blkCap rate base g b₃ = blkCap rate base g b₁ then 1 else 0) := by
        rw [Finset.mul_sum]
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b₁ _ ↦ ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b₂ _ ↦ ?_
        rw [Finset.sum_comm]
    _ ≤ ∑ _b₁ ∈ O, ∑ _b₂ ∈ O, ∑ _b₃ ∈ O, Fintype.card (X → Z) := by
        refine Finset.sum_le_sum fun b₁ _ ↦ Finset.sum_le_sum fun b₂ _ ↦
          Finset.sum_le_sum fun b₃ _ ↦ ?_
        by_cases hd : b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₂ ≠ b₃
        · refine le_trans (le_of_eq ?_) (hpt b₁ b₂ b₃ hd.1 hd.2.1 hd.2.2)
          congr 1
          refine Finset.sum_congr rfl fun g _ ↦ ?_
          simp only [hd, ne_eq, not_false_eq_true, true_and]
        · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
          rw [Finset.sum_eq_zero fun g _ ↦ by
            rw [ite_eq_right_iff]
            exact fun h ↦ (hd ⟨h.1, h.2.1, h.2.2.1⟩).elim, mul_zero]
    _ = O.card ^ 3 * Fintype.card (X → Z) := by
        simp only [Finset.sum_const, smul_eq_mul]
        ring

/-- **More than `L` foreign blocks hitting the capacities of `m`**: at most
`C(|B|, L + 1) (n / |Z|)^(L + 1)` of the functions, for `n` blocks of `m`. -/
theorem card_pow_mul_sum_hits_le (hr : Function.Injective rate) (m : Mg) (L : ℕ) :
    Fintype.card Z ^ (L + 1) * ∑ g : X → Z,
        (if L + 1 ≤ (hitsK rate base μ g m).card then 1 else 0) ≤
      (Fintype.card B).choose (L + 1) * (ownB μ m).card ^ (L + 1) * Fintype.card (X → Z) := by
  set O := ownB μ m
  set Sx : B → (X → Z) → Finset Z := fun b g ↦ O.image fun b₁ ↦ blkCap rate base g b₁ - base b
    with hSx
  have hpt : ∀ J ∈ (fgnB μ m).powersetCard (L + 1),
      Fintype.card Z ^ (L + 1) * ∑ g : X → Z, (if ∀ b ∈ J, g (rate b) ∈ Sx b g then 1 else 0) ≤
        O.card ^ (L + 1) * Fintype.card (X → Z) := by
    intro J hJ
    obtain ⟨hJF, hJc⟩ := Finset.mem_powersetCard.mp hJ
    have h' := card_pow_mul_sum_forall_le rate hr Sx O.card J
      (fun _ _ _ ↦ Finset.card_image_le) fun b _ b' hb' g w ↦ by
        show O.image (fun b₁ ↦ blkCap rate base (Function.update g (rate b') w) b₁ - base b) =
          O.image fun b₁ ↦ blkCap rate base g b₁ - base b
        refine Finset.image_congr fun b₁ hb₁ ↦ ?_
        have h1 : μ b₁ = m := (Finset.mem_filter.mp hb₁).2
        have h2 : μ b' ≠ m := (Finset.mem_filter.mp (hJF hb')).2
        have hne : rate b₁ ≠ rate b' := fun e ↦ h2 (hr e ▸ h1)
        exact congrArg (· - base b) (blkCap_update_of_ne rate base g hne w)
    rw [hJc] at h'
    refine le_trans (le_of_eq ?_) h'
    congr 1
    exact Finset.sum_congr rfl fun g _ ↦ by
      by_cases hc : ∀ b ∈ J, g (rate b) ∈ Sx b g <;> simp [hc]
  calc Fintype.card Z ^ (L + 1) * ∑ g : X → Z,
        (if L + 1 ≤ (hitsK rate base μ g m).card then 1 else 0)
      ≤ Fintype.card Z ^ (L + 1) * ∑ g : X → Z, ∑ J ∈ (fgnB μ m).powersetCard (L + 1),
          (if ∀ b ∈ J, g (rate b) ∈ Sx b g then 1 else 0) := by
        refine Nat.mul_le_mul_left _ (Finset.sum_le_sum fun g _ ↦ ?_)
        split_ifs with h
        · obtain ⟨J, hJ, hJc⟩ := Finset.exists_subset_card_eq h
          have hJm : J ∈ (fgnB μ m).powersetCard (L + 1) :=
            Finset.mem_powersetCard.mpr ⟨hJ.trans (Finset.filter_subset _ _), hJc⟩
          refine le_trans ?_ (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hJm)
          have hall : ∀ b ∈ J, g (rate b) ∈ Sx b g := fun b hb ↦ by
            obtain ⟨-, b₁, hb₁, he⟩ := Finset.mem_filter.mp (hJ hb)
            refine Finset.mem_image.mpr ⟨b₁, hb₁, ?_⟩
            rw [he]
            unfold blkCap
            abel
          split_ifs
          exact le_rfl
        · exact Nat.zero_le _
    _ = ∑ J ∈ (fgnB μ m).powersetCard (L + 1), Fintype.card Z ^ (L + 1) * ∑ g : X → Z,
          (if ∀ b ∈ J, g (rate b) ∈ Sx b g then 1 else 0) := by
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ _J ∈ (fgnB μ m).powersetCard (L + 1), O.card ^ (L + 1) * Fintype.card (X → Z) :=
        Finset.sum_le_sum hpt
    _ = (fgnB μ m).card.choose (L + 1) * (O.card ^ (L + 1) * Fintype.card (X → Z)) := by
        rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
    _ ≤ (Fintype.card B).choose (L + 1) * (O.card ^ (L + 1) * Fintype.card (X → Z)) :=
        Nat.mul_le_mul_right _ (Nat.choose_le_choose _ (Finset.card_le_univ _))
    _ = _ := by ring

variable {I : Type}

/-- **The static condition**: distinct rates, no pair of `sib` at one capacity, every load at most
`Lm`. -/
def StaticK (sib : I → B × B) (g : X → Z) (Lm : ℕ) : Prop :=
  Function.Injective rate ∧ (∀ i, blkCap rate base g (sib i).1 ≠ blkCap rate base g (sib i).2) ∧
    ∀ m, loadK rate base μ g m ≤ Lm

omit [Fintype X] [DecidableEq X] [Fintype Z] in
/-- **The ordered pairs of a block of a label of `S` and a block of another label at one
capacity**: at most `|S| Lm` when every load is at most `Lm`. -/
theorem card_filter_pairs_le (g : X → Z) (S : Finset Mg) (Lm : ℕ)
    (hL : ∀ m, loadK rate base μ g m ≤ Lm) :
    (Finset.univ.filter fun j : B × B ↦ μ j.1 ∈ S ∧ μ j.1 ≠ μ j.2 ∧
      blkCap rate base g j.1 = blkCap rate base g j.2).card ≤ S.card * Lm := by
  calc (Finset.univ.filter fun j : B × B ↦ μ j.1 ∈ S ∧ μ j.1 ≠ μ j.2 ∧
          blkCap rate base g j.1 = blkCap rate base g j.2).card
      ≤ (S.biUnion fun m ↦ (ownB μ m ×ˢ fgnB μ m).filter fun p ↦
          blkCap rate base g p.1 = blkCap rate base g p.2).card := by
        refine Finset.card_le_card fun j hj ↦ ?_
        obtain ⟨-, hS, hne, he⟩ := Finset.mem_filter.mp hj
        refine Finset.mem_biUnion.mpr ⟨μ j.1, hS, Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, he⟩⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h ↦ hne h.symm⟩
    _ ≤ ∑ m ∈ S, loadK rate base μ g m := Finset.card_biUnion_le
    _ ≤ ∑ _m ∈ S, Lm := Finset.sum_le_sum fun m _ ↦ hL m
    _ = S.card * Lm := by rw [Finset.sum_const, smul_eq_mul]

end caps

/-- **The blocks of a label** in `R × (Mg × C)`, labelled by the middle coordinate: `|R| |C|`. -/
theorem card_ownB_prod {R Mg C : Type} [Fintype R] [Fintype Mg] [DecidableEq Mg] [Fintype C]
    (m : Mg) : (ownB (fun b : R × (Mg × C) ↦ b.2.1) m).card = Fintype.card R * Fintype.card C := by
  have h : ownB (fun b : R × (Mg × C) ↦ b.2.1) m =
      (Finset.univ : Finset R) ×ˢ (({m} : Finset Mg) ×ˢ (Finset.univ : Finset C)) := by
    ext ⟨r, m', c⟩
    simp [ownB, eq_comm]
  rw [h, Finset.card_product, Finset.card_product, Finset.card_singleton, one_mul,
    Finset.card_univ, Finset.card_univ]

/-! ## The fraction of the static condition's failures -/

section frac

variable {X Z B Mg I W : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup Z] [Fintype B] [DecidableEq B] [Fintype Mg] [DecidableEq Mg] [Fintype I]
  [Fintype W]

/-- `c a ≤ N d` gives `N⁻¹ a ≤ d / c` in `ℝ≥0∞`. -/
theorem inv_mul_le_div_of_mul_le {a c d N : ℕ} (hc : c ≠ 0) (h : c * a ≤ N * d) :
    (N : ℝ≥0∞)⁻¹ * a ≤ (d : ℝ≥0∞) / c := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h0 : c * a = 0 := by rw [zero_mul] at h; omega
    rw [(Nat.mul_eq_zero.mp h0).resolve_left hc, Nat.cast_zero, mul_zero]
    exact zero_le
  · have hc' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc
    have hN' : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
    rw [ENNReal.div_eq_inv_mul]
    calc (N : ℝ≥0∞)⁻¹ * a = (N : ℝ≥0∞)⁻¹ * (c : ℝ≥0∞)⁻¹ * (c * a) := by
          rw [mul_assoc, ← mul_assoc (c : ℝ≥0∞)⁻¹, ENNReal.inv_mul_cancel hc'
            (ENNReal.natCast_ne_top _), one_mul]
      _ ≤ (N : ℝ≥0∞)⁻¹ * (c : ℝ≥0∞)⁻¹ * (N * d) :=
          mul_le_mul' le_rfl (by exact_mod_cast h)
      _ = (c : ℝ≥0∞)⁻¹ * d := by
          rw [mul_comm (N : ℝ≥0∞)⁻¹, mul_assoc, ← mul_assoc (N : ℝ≥0∞)⁻¹,
            ENNReal.inv_mul_cancel hN' (ENNReal.natCast_ne_top _), one_mul]

omit [AddCommGroup Z] in
/-- A count over `(π, g, w)`, bounded for each `(g, w)`. -/
theorem card_mul_sum_perm_le (F : Equiv.Perm (X × Z) → (X → Z) → W → ℕ) (c d : ℕ)
    (h : ∀ g w, c * ∑ π, F π g w ≤ Fintype.card (Equiv.Perm (X × Z)) * d) :
    c * ∑ q : (Equiv.Perm (X × Z) × (X → Z)) × W, F q.1.1 q.1.2 q.2 ≤
      Fintype.card ((Equiv.Perm (X × Z) × (X → Z)) × W) * d := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  calc ∑ π, c * ∑ g, ∑ w, F π g w
      = ∑ g, ∑ w, c * ∑ π, F π g w := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ ↦ ?_
        rw [Finset.sum_comm]
    _ ≤ ∑ _g : X → Z, ∑ _w : W, Fintype.card (Equiv.Perm (X × Z)) * d :=
        Finset.sum_le_sum fun g _ ↦ Finset.sum_le_sum fun w _ ↦ h g w
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_prod]
        ring

omit [AddCommGroup Z] in
/-- A count over `(π, g, w)`, bounded for each `(π, w)`. -/
theorem card_mul_sum_fun_le (F : Equiv.Perm (X × Z) → (X → Z) → W → ℕ) (c d : ℕ)
    (h : ∀ π w, c * ∑ g, F π g w ≤ Fintype.card (X → Z) * d) :
    c * ∑ q : (Equiv.Perm (X × Z) × (X → Z)) × W, F q.1.1 q.1.2 q.2 ≤
      Fintype.card ((Equiv.Perm (X × Z) × (X → Z)) × W) * d := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  calc ∑ π, c * ∑ g, ∑ w, F π g w
      = ∑ π, ∑ w, c * ∑ g, F π g w := by
        refine Finset.sum_congr rfl fun π _ ↦ ?_
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ _π : Equiv.Perm (X × Z), ∑ _w : W, Fintype.card (X → Z) * d :=
        Finset.sum_le_sum fun π _ ↦ Finset.sum_le_sum fun w _ ↦ h π w
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_prod]
        ring

omit [DecidableEq Mg] in
/-- A sum over the labels of counts of `ite`s bounds the count of the existential. -/
theorem sum_ite_exists_le {G : Type} [Fintype G] (P : Mg → G → Prop) [∀ m, DecidablePred (P m)]
    [DecidablePred fun g ↦ ∃ m, P m g] :
    ∑ g, (if ∃ m, P m g then 1 else 0) ≤ ∑ m, ∑ g, (if P m g then 1 else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun g _ ↦ ?_
  split_ifs with h
  · obtain ⟨m, hm⟩ := h
    exact le_trans (by simp [hm]) (Finset.single_le_sum
      (f := fun m ↦ if P m g then 1 else 0) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ m))
  · exact Nat.zero_le _

/-- The rates of the blocks at `(π, g, w)`. -/
abbrev rtQ (pt : W → B → X × Z) (q : (Equiv.Perm (X × Z) × (X → Z)) × W) (b : B) : X :=
  (q.1.1 (pt q.2 b)).1

/-- The bases of the blocks at `(π, g, w)`. -/
abbrev btQ (pt : W → B → X × Z) (q : (Equiv.Perm (X × Z) × (X → Z)) × W) (b : B) : Z :=
  (q.1.1 (pt q.2 b)).2

open scoped Classical in
/-- **The static condition fails rarely**: over `(π, g, w)` with distinct points `pt w`, the rates
`(π (pt w b)).1` collide for `|B|² / |X|`, a pair of `sib` shares a capacity for `|I| / |Z|`,
three blocks of a label share one for `|Mg| n³ / |Z|²`, and more than `L` foreign blocks hit the
capacities of a label for `|Mg| (|B| n)^(L+1) / ((L+1)! |Z|^(L+1))`, for at most `n` blocks per
label. -/
theorem frac_not_staticK_le [Nonempty X] (pt : W → B → X × Z) (hpt : ∀ w, Function.Injective (pt w))
    (μ : B → Mg) (sib : I → B × B) (hsib : ∀ i, (sib i).1 ≠ (sib i).2) (L n : ℕ)
    (hn : ∀ m, (ownB μ m).card ≤ n) :
    (Fintype.card ((Equiv.Perm (X × Z) × (X → Z)) × W) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun q : (Equiv.Perm (X × Z) × (X → Z)) × W ↦
          ¬StaticK (rtQ pt q) (btQ pt q) μ sib q.1.2 (2 * L)).card ≤
      ((Fintype.card B * Fintype.card B : ℕ) : ℝ≥0∞) / (Fintype.card X : ℕ) +
        ((Fintype.card I : ℕ) : ℝ≥0∞) / (Fintype.card Z : ℕ) +
        ((Fintype.card Mg * n ^ 3 : ℕ) : ℝ≥0∞) / (Fintype.card Z ^ 2 : ℕ) +
        ((Fintype.card Mg * (Fintype.card B * n) ^ (L + 1) : ℕ) : ℝ≥0∞) /
          ((L + 1).factorial * Fintype.card Z ^ (L + 1) : ℕ) := by
  have hcover : ∀ q : (Equiv.Perm (X × Z) × (X → Z)) × W,
      ¬StaticK (rtQ pt q) (btQ pt q) μ sib q.1.2 (2 * L) →
      ¬Function.Injective (rtQ pt q) ∨
      (Function.Injective (rtQ pt q) ∧ ∃ i, blkCap (rtQ pt q) (btQ pt q) q.1.2 (sib i).1 =
        blkCap (rtQ pt q) (btQ pt q) q.1.2 (sib i).2) ∨
      (∃ m, Function.Injective (rtQ pt q) ∧ TripleK (rtQ pt q) (btQ pt q) μ q.1.2 m) ∨
      (∃ m, Function.Injective (rtQ pt q) ∧
        L + 1 ≤ (hitsK (rtQ pt q) (btQ pt q) μ q.1.2 m).card) := by
    intro q hq
    by_cases hi : Function.Injective (rtQ pt q)
    · by_cases hs : ∀ i, blkCap (rtQ pt q) (btQ pt q) q.1.2 (sib i).1 ≠
          blkCap (rtQ pt q) (btQ pt q) q.1.2 (sib i).2
      · have hl : ∃ m, 2 * L < loadK (rtQ pt q) (btQ pt q) μ q.1.2 m := by
          by_contra hl
          push Not at hl
          exact hq ⟨hi, hs, hl⟩
        obtain ⟨m, hm⟩ := hl
        rcases triple_or_hits_of_lt (rtQ pt q) (btQ pt q) μ q.1.2 m L hm with h | h
        · exact Or.inr (Or.inr (Or.inl ⟨m, hi, h⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨m, hi, h⟩))
      · push Not at hs
        exact Or.inr (Or.inl ⟨hi, hs⟩)
    · exact Or.inl hi
  have hcard : (Finset.univ.filter fun q : (Equiv.Perm (X × Z) × (X → Z)) × W ↦
        ¬StaticK (rtQ pt q) (btQ pt q) μ sib q.1.2 (2 * L)).card ≤
      (Finset.univ.filter fun q : (Equiv.Perm (X × Z) × (X → Z)) × W ↦
          ¬Function.Injective (rtQ pt q)).card +
        (Finset.univ.filter fun q : (Equiv.Perm (X × Z) × (X → Z)) × W ↦
          Function.Injective (rtQ pt q) ∧ ∃ i, blkCap (rtQ pt q) (btQ pt q) q.1.2 (sib i).1 =
            blkCap (rtQ pt q) (btQ pt q) q.1.2 (sib i).2).card +
        (Finset.univ.filter fun q : (Equiv.Perm (X × Z) × (X → Z)) × W ↦
          ∃ m, Function.Injective (rtQ pt q) ∧ TripleK (rtQ pt q) (btQ pt q) μ q.1.2 m).card +
        (Finset.univ.filter fun q : (Equiv.Perm (X × Z) × (X → Z)) × W ↦
          ∃ m, Function.Injective (rtQ pt q) ∧
            L + 1 ≤ (hitsK (rtQ pt q) (btQ pt q) μ q.1.2 m).card).card := by
    refine (Finset.card_le_card fun q hq ↦ ?_).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
    have h := hcover q (Finset.mem_filter.mp hq).2
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases h with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hX : Fintype.card X ≠ 0 := Fintype.card_ne_zero
  have hZ : Fintype.card Z ≠ 0 := Fintype.card_ne_zero
  -- the rates
  have c1 : Fintype.card X * (Finset.univ.filter fun q : (Equiv.Perm (X × Z) × (X → Z)) × W ↦
      ¬Function.Injective (rtQ pt q)).card ≤
      Fintype.card ((Equiv.Perm (X × Z) × (X → Z)) × W) * (Fintype.card B * Fintype.card B) := by
    rw [Finset.card_filter]
    exact card_mul_sum_perm_le (fun π _ w ↦ if ¬Function.Injective (fun b ↦ (π (pt w b)).1)
      then 1 else 0) _ _ fun g w ↦
        Quantum.Xmss.Hybrid.card_mul_sum_not_injective_rate_le (pt w) (hpt w)
  -- the pairs of `sib`
  have c2 : Fintype.card Z * (Finset.univ.filter fun q : (Equiv.Perm (X × Z) × (X → Z)) × W ↦
      Function.Injective (rtQ pt q) ∧ ∃ i, blkCap (rtQ pt q) (btQ pt q) q.1.2 (sib i).1 =
        blkCap (rtQ pt q) (btQ pt q) q.1.2 (sib i).2).card ≤
      Fintype.card ((Equiv.Perm (X × Z) × (X → Z)) × W) * Fintype.card I := by
    rw [Finset.card_filter]
    refine card_mul_sum_fun_le (fun π g w ↦ if Function.Injective (fun b ↦ (π (pt w b)).1) ∧
      ∃ i, blkCap (fun b ↦ (π (pt w b)).1) (fun b ↦ (π (pt w b)).2) g (sib i).1 =
        blkCap (fun b ↦ (π (pt w b)).1) (fun b ↦ (π (pt w b)).2) g (sib i).2 then 1 else 0) _ _
      fun π w ↦ ?_
    by_cases hi : Function.Injective (fun b ↦ (π (pt w b)).1)
    · simp only [hi, true_and]
      rw [mul_comm (Fintype.card (X → Z))]
      exact card_mul_sum_sibs_le _ _ hi sib hsib
    · simp [hi]
  -- three blocks of a label
  have c3 : Fintype.card Z ^ 2 * (Finset.univ.filter fun q : (Equiv.Perm (X × Z) × (X → Z)) × W ↦
      ∃ m, Function.Injective (rtQ pt q) ∧ TripleK (rtQ pt q) (btQ pt q) μ q.1.2 m).card ≤
      Fintype.card ((Equiv.Perm (X × Z) × (X → Z)) × W) * (Fintype.card Mg * n ^ 3) := by
    rw [Finset.card_filter]
    refine card_mul_sum_fun_le (fun π g w ↦ if ∃ m, Function.Injective (fun b ↦ (π (pt w b)).1) ∧
      TripleK (fun b ↦ (π (pt w b)).1) (fun b ↦ (π (pt w b)).2) μ g m then 1 else 0) _ _
      fun π w ↦ ?_
    refine (Nat.mul_le_mul_left _ (sum_ite_exists_le _)).trans ?_
    rw [Finset.mul_sum]
    calc ∑ m, Fintype.card Z ^ 2 * ∑ g : X → Z,
          (if Function.Injective (fun b ↦ (π (pt w b)).1) ∧
            TripleK (fun b ↦ (π (pt w b)).1) (fun b ↦ (π (pt w b)).2) μ g m then 1 else 0)
        ≤ ∑ _m : Mg, n ^ 3 * Fintype.card (X → Z) := Finset.sum_le_sum fun m _ ↦ by
          by_cases hi : Function.Injective (fun b ↦ (π (pt w b)).1)
          · simp only [hi, true_and]
            exact (card_pow_mul_sum_triple_le _ _ μ hi m).trans
              (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (hn m) 3))
          · simp [hi]
      _ = Fintype.card (X → Z) * (Fintype.card Mg * n ^ 3) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring
  -- many foreign blocks hitting a label's capacities
  have hch : (Fintype.card B).choose (L + 1) * (L + 1).factorial ≤ Fintype.card B ^ (L + 1) := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow _ _
  have c4 : ((L + 1).factorial * Fintype.card Z ^ (L + 1)) *
      (Finset.univ.filter fun q : (Equiv.Perm (X × Z) × (X → Z)) × W ↦
        ∃ m, Function.Injective (rtQ pt q) ∧
          L + 1 ≤ (hitsK (rtQ pt q) (btQ pt q) μ q.1.2 m).card).card ≤
      Fintype.card ((Equiv.Perm (X × Z) × (X → Z)) × W) *
        (Fintype.card Mg * (Fintype.card B * n) ^ (L + 1)) := by
    rw [Finset.card_filter]
    refine card_mul_sum_fun_le (fun π g w ↦ if ∃ m, Function.Injective (fun b ↦ (π (pt w b)).1) ∧
      L + 1 ≤ (hitsK (fun b ↦ (π (pt w b)).1) (fun b ↦ (π (pt w b)).2) μ g m).card then 1
        else 0) _ _ fun π w ↦ ?_
    refine (Nat.mul_le_mul_left _ (sum_ite_exists_le _)).trans ?_
    rw [Finset.mul_sum]
    calc ∑ m, (L + 1).factorial * Fintype.card Z ^ (L + 1) * ∑ g : X → Z,
          (if Function.Injective (fun b ↦ (π (pt w b)).1) ∧
            L + 1 ≤ (hitsK (fun b ↦ (π (pt w b)).1) (fun b ↦ (π (pt w b)).2) μ g m).card
              then 1 else 0)
        ≤ ∑ _m : Mg, (Fintype.card B * n) ^ (L + 1) * Fintype.card (X → Z) :=
          Finset.sum_le_sum fun m _ ↦ by
          by_cases hi : Function.Injective (fun b ↦ (π (pt w b)).1)
          · simp only [hi, true_and]
            have h := card_pow_mul_sum_hits_le (fun b ↦ (π (pt w b)).1) (fun b ↦ (π (pt w b)).2)
              μ hi m L
            calc (L + 1).factorial * Fintype.card Z ^ (L + 1) * ∑ g : X → Z,
                  (if L + 1 ≤ (hitsK (fun b ↦ (π (pt w b)).1) (fun b ↦ (π (pt w b)).2) μ g m).card
                    then 1 else 0)
                = (L + 1).factorial * (Fintype.card Z ^ (L + 1) * ∑ g : X → Z,
                  (if L + 1 ≤ (hitsK (fun b ↦ (π (pt w b)).1) (fun b ↦ (π (pt w b)).2) μ g m).card
                    then 1 else 0)) := by ring
              _ ≤ (L + 1).factorial * ((Fintype.card B).choose (L + 1) *
                  (ownB μ m).card ^ (L + 1) * Fintype.card (X → Z)) := Nat.mul_le_mul_left _ h
              _ = ((Fintype.card B).choose (L + 1) * (L + 1).factorial) *
                  (ownB μ m).card ^ (L + 1) * Fintype.card (X → Z) := by ring
              _ ≤ Fintype.card B ^ (L + 1) * n ^ (L + 1) * Fintype.card (X → Z) :=
                  Nat.mul_le_mul_right _ (Nat.mul_le_mul hch (Nat.pow_le_pow_left (hn m) _))
              _ = (Fintype.card B * n) ^ (L + 1) * Fintype.card (X → Z) := by rw [mul_pow]
          · simp [hi]
      _ = Fintype.card (X → Z) * (Fintype.card Mg * (Fintype.card B * n) ^ (L + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring
  have hZ2 : Fintype.card Z ^ 2 ≠ 0 := pow_ne_zero _ hZ
  have hZL : (L + 1).factorial * Fintype.card Z ^ (L + 1) ≠ 0 :=
    Nat.mul_ne_zero (Nat.factorial_ne_zero _) (pow_ne_zero _ hZ)
  calc (Fintype.card ((Equiv.Perm (X × Z) × (X → Z)) × W) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun q : (Equiv.Perm (X × Z) × (X → Z)) × W ↦
          ¬StaticK (rtQ pt q) (btQ pt q) μ sib q.1.2 (2 * L)).card
      ≤ (Fintype.card ((Equiv.Perm (X × Z) × (X → Z)) × W) : ℝ≥0∞)⁻¹ *
          (((Finset.univ.filter fun q : (Equiv.Perm (X × Z) × (X → Z)) × W ↦
            ¬Function.Injective (rtQ pt q)).card : ℝ≥0∞) +
          ((Finset.univ.filter fun q : (Equiv.Perm (X × Z) × (X → Z)) × W ↦
            Function.Injective (rtQ pt q) ∧ ∃ i, blkCap (rtQ pt q) (btQ pt q) q.1.2 (sib i).1 =
              blkCap (rtQ pt q) (btQ pt q) q.1.2 (sib i).2).card : ℝ≥0∞) +
          ((Finset.univ.filter fun q : (Equiv.Perm (X × Z) × (X → Z)) × W ↦
            ∃ m, Function.Injective (rtQ pt q) ∧
              TripleK (rtQ pt q) (btQ pt q) μ q.1.2 m).card : ℝ≥0∞) +
          ((Finset.univ.filter fun q : (Equiv.Perm (X × Z) × (X → Z)) × W ↦
            ∃ m, Function.Injective (rtQ pt q) ∧
              L + 1 ≤ (hitsK (rtQ pt q) (btQ pt q) μ q.1.2 m).card).card : ℝ≥0∞)) := by
        gcongr
        exact_mod_cast hcard
    _ ≤ _ := by
        rw [mul_add, mul_add, mul_add]
        exact add_le_add (add_le_add (add_le_add (inv_mul_le_div_of_mul_le hX c1)
          (inv_mul_le_div_of_mul_le hZ c2)) (inv_mul_le_div_of_mul_le hZ2 c3))
          (inv_mul_le_div_of_mul_le hZL c4)

end frac

end Quantum.Sphincs.Assembly

end
