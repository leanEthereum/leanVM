/-
  LeanVM.Guest.B1.Sig.Steps

  Completeness one atom at a time, and the guest's literal runs: `shifts` (G:2289), the
  Booleanity checks of a bit hint, the powers `g^s`.
-/

module

public import LeanVM.Guest.B1.Sig.Template
public import LeanVM.Guest.B1.Sig.Walk
public import LeanVM.Guest.B1.Sig.HashValues
public import LeanVM.Guest.Value.Bits

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## One atom at a time -/

/-- An atom writing the fresh value `k`. -/
theorem Completes.atom_cons {k hi : Nat} {a : Atom} {ss : List Stmt} {σ : Val} {P : Val → Prop} (e : E)
    (hk : k + 1 ≤ hi) (hb : NumBelow (k + 1) a.vals) (ha : a.Holds rd (Function.update σ (.n k) e))
    (h : Completes C rd (k + 1) hi ss (Function.update σ (.n k) e) P) :
    Completes C rd k hi (.atom a :: ss) σ P := by
  obtain ⟨σ', he, hp, hh⟩ := h
  refine ⟨σ', (ext_update σ e le_rfl (Nat.lt_succ_self k)).trans he (Nat.le_succ k) hk, hp,
    fun next kret hn => ?_⟩
  rw [holdsList_cons_atom]
  refine ⟨?_, hh next kret hn⟩
  exact (atom_congr a fun v hv => let ⟨j, hj, e⟩ := hb v hv; e ▸ he.agree j hj).mp ha

/-- An atom over values below the range. -/
theorem Completes.atom_cons0 {k hi : Nat} {a : Atom} {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (hb : NumBelow k a.vals) (ha : a.Holds rd σ) (h : Completes C rd k hi ss σ P) :
    Completes C rd k hi (.atom a :: ss) σ P := by
  obtain ⟨σ', he, hp, hh⟩ := h
  refine ⟨σ', he, hp, fun next kret hn => ?_⟩
  rw [holdsList_cons_atom]
  refine ⟨?_, hh next kret hn⟩
  exact (atom_congr a fun v hv => let ⟨j, hj, e⟩ := hb v hv; e ▸ he.agree j hj).mp ha

theorem Completes.nil (lo hi : Nat) (σ : Val) {P : Val → Prop} (hp : P σ) : Completes C rd lo hi [] σ P :=
  ⟨σ, Ext.refl _ _ _, hp, fun _ _ hn => hn⟩

/-- A block over values below the range that holds already. -/
theorem Completes.append_holds {k hi : Nat} {xs ys : List Stmt} {σ : Val} {P : Val → Prop}
    (hb : NumBelow k (Stmt.valsList xs)) (hx : ∀ (next : Prop) (kret : List E → Prop), next →
      Stmt.HoldsList C rd σ xs next kret) (h : Completes C rd k hi ys σ P) :
    Completes C rd k hi (xs ++ ys) σ P := by
  obtain ⟨σ', he, hp, hh⟩ := h
  refine ⟨σ', he, hp, fun next kret hn => ?_⟩
  rw [holdsList_append]
  exact (holdsList_frame hb he.agree _ _).mp (hx _ kret (hh next kret hn))

/-! ## Bits and their shifts -/

theorem bitE_eq_eOfNat (c : Bool) : bitE c = eOfNat c.toNat := by
  cases c
  · simp [bitE, eOfNat_zero]
  · simp [bitE, eOfNat_one]

theorem div_two_pow_eq (N k : Nat) : N / 2 ^ k = 2 * (N / 2 ^ (k + 1)) + (N.testBit k).toNat := by
  rw [Nat.testBit_eq_decide_div_mod_eq, pow_succ, ← Nat.div_div_eq_div_mul]
  have := Nat.div_add_mod (N / 2 ^ k) 2
  rcases Nat.mod_two_eq_zero_or_one (N / 2 ^ k) with h | h <;> simp [h] <;> omega

theorem shift_step {N k : Nat} (hN : N < 2 ^ 64) :
    gen * eOfNat (N / 2 ^ (k + 1)) + bitE (N.testBit k) = eOfNat (N / 2 ^ k) := by
  have hle : N / 2 ^ k ≤ N := Nat.div_le_self _ _
  rw [div_two_pow_eq N k] at hle ⊢
  rw [gen_mul_eOfNat (by omega), bitE_eq_eOfNat,
    show 2 * (N / 2 ^ (k + 1)) = 2 ^ 1 * (N / 2 ^ (k + 1)) by ring,
    eOfNat_add_of_lt (by cases N.testBit k <;> simp)]

theorem top_bit {N n : Nat} (hN : N < 2 ^ (n + 1)) : bitE (N.testBit n) = eOfNat (N / 2 ^ n) := by
  have h := div_two_pow_eq N n
  rw [Nat.div_eq_of_lt hN] at h
  rw [bitE_eq_eOfNat]
  congr 1
  omega

/-- A block of `shifts`. -/
def shiftBlock (bitBase n outBase r' : Nat) : List Stmt :=
  let r := r' + 1
  [cst (outBase + 3 * r - 2) (word 2 0 0),
    mulS (.n (outBase + 3 * r - 1)) (.n (outBase + 3 * r - 2)) (.n (outBase + 3 * r - 3)),
    addS (.n (outBase + 3 * r)) (.n (bitBase + n - 1 - r)) (.n (outBase + 3 * r - 1))]

theorem shifts_eq (bitBase n outBase : Nat) :
    shifts bitBase n outBase = .atom (.copy (.n outBase) (.n (bitBase + n - 1))) ::
      (List.range (n - 1)).flatMap (shiftBlock bitBase n outBase) := rfl

theorem word_two : word 2 0 0 = gen := by rw [word_eq_eOfNat]; rfl

/-- **`shifts` is sound**: over the bits of `N < 2^n`, output `r` is `N >> (n - 1 - r)`. -/
theorem shifts_sound {σ : Val} {bitBase n outBase N : Nat} (hn : 0 < n) (hn64 : n ≤ 64) (hN : N < 2 ^ n)
    (hbits : ∀ j < n, σ (.n (bitBase + j)) = bitE (N.testBit j)) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (shifts bitBase n outBase) next kret) :
    (∀ r < n, σ (.n (outBase + 3 * r)) = eOfNat (N / 2 ^ (n - 1 - r))) ∧ next := by
  rw [shifts_eq, holdsList_cons_atom, holdsList_flatMap_range _ (fun _ => rfl)] at h
  obtain ⟨h0, hb, hn'⟩ := h
  refine ⟨fun r hr => ?_, hn'⟩
  induction r with
  | zero =>
      simp only [Atom.Holds] at h0
      rw [Nat.mul_zero, Nat.add_zero, h0, show bitBase + n - 1 = bitBase + (n - 1) by omega,
        hbits _ (by omega), Nat.sub_zero, top_bit (by rw [show n - 1 + 1 = n by omega]; exact hN)]
  | succ r ih =>
      have := hb r (by omega)
      simp only [shiftBlock, cst, addS, mulS, holdsList_cons_atom, holdsList_nil, Atom.Holds] at this
      obtain ⟨h1, h2, h3, -⟩ := this
      rw [h3, h2, h1, show outBase + 3 * (r + 1) - 3 = outBase + 3 * r by omega, ih (by omega),
        show bitBase + n - 1 - (r + 1) = bitBase + (n - 1 - (r + 1)) by omega, hbits _ (by omega), word_two,
        add_comm, show n - 1 - r = n - 1 - (r + 1) + 1 by omega,
        shift_step (lt_of_lt_of_le hN (Nat.pow_le_pow_right (by norm_num) hn64))]

/-- **`shifts` is complete**, over bits below its outputs. -/
theorem shifts_complete {σ : Val} {bitBase n outBase N : Nat} (hn : 0 < n) (hn64 : n ≤ 64) (hN : N < 2 ^ n)
    (hlt : bitBase + n ≤ outBase) (hbits : ∀ j < n, σ (.n (bitBase + j)) = bitE (N.testBit j)) :
    Completes C rd outBase (outBase + 3 * (n - 1) + 1) (shifts bitBase n outBase) σ
      (fun σ' => (∀ r < n, σ' (.n (outBase + 3 * r)) = eOfNat (N / 2 ^ (n - 1 - r))) ∧
        AgreeBelow outBase σ σ') := by
  have hN64 : N < 2 ^ 64 := lt_of_lt_of_le hN (Nat.pow_le_pow_right (by norm_num) hn64)
  rw [shifts_eq]
  have hb0 : bitE (N.testBit (n - 1)) = eOfNat (N / 2 ^ (n - 1)) :=
    top_bit (by rw [show n - 1 + 1 = n by omega]; exact hN)
  refine Completes.atom_cons (eOfNat (N / 2 ^ (n - 1))) (by omega)
    (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _))) ?_ ?_
  · simp only [Atom.Holds, Function.update_self]
    rw [Function.update_of_ne (by simp only [ne_eq, V.mk.injEq, true_and]; omega),
      show bitBase + n - 1 = bitBase + (n - 1) by omega, hbits _ (by omega), hb0]
  · set σ0 := Function.update σ (.n outBase) (eOfNat (N / 2 ^ (n - 1)))
    have hag0 : AgreeBelow outBase σ σ0 := (ext_update σ _ le_rfl (Nat.lt_succ_self _)).agree
    have := Completes.flatMap_range (C := C) (rd := rd) (f := shiftBlock bitBase n outBase)
      (base := fun j => outBase + 1 + 3 * j)
      (Inv := fun j σ' => (∀ r ≤ j, σ' (.n (outBase + 3 * r)) = eOfNat (N / 2 ^ (n - 1 - r))) ∧
        AgreeBelow outBase σ σ') (fun j => by omega) (n - 1)
      (fun j hj => by
        simp only [shiftBlock, cst, addS, mulS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals,
          List.cons_append, List.nil_append, List.append_nil]
        exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
          (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
          (.cons ⟨_, by omega, rfl⟩ (.nil _))))))))
      (fun j hj σ1 ⟨hv1, hag1⟩ => by
        set k := outBase + 1 + 3 * j
        have hblk : shiftBlock bitBase n outBase j = [cst k (word 2 0 0),
            mulS (.n (k + 1)) (.n k) (.n (outBase + 3 * j)),
            addS (.n (k + 2)) (.n (bitBase + (n - 1 - (j + 1)))) (.n (k + 1))] := by
          simp only [shiftBlock]
          rw [show outBase + 3 * (j + 1) - 2 = k by omega, show outBase + 3 * (j + 1) - 1 = k + 1 by omega,
            show outBase + 3 * (j + 1) - 3 = outBase + 3 * j by omega, show outBase + 3 * (j + 1) = k + 2 by omega,
            show bitBase + n - 1 - (j + 1) = bitBase + (n - 1 - (j + 1)) by omega]
        rw [hblk, show outBase + 1 + 3 * (j + 1) = k + 3 by omega]
        have hprev := hv1 j le_rfl
        have hbit : σ1 (.n (bitBase + (n - 1 - (j + 1)))) = bitE (N.testBit (n - 1 - (j + 1))) := by
          rw [← hag1 _ (by omega), hbits _ (by omega)]
        set σ2 := Function.update σ1 (.n k) (word 2 0 0)
        set σ3 := Function.update σ2 (.n (k + 1)) (gen * eOfNat (N / 2 ^ (n - 1 - j)))
        set σ4 := Function.update σ3 (.n (k + 2)) (eOfNat (N / 2 ^ (n - 1 - (j + 1))))
        have ne : ∀ a b : Nat, a ≠ b → (V.n a) ≠ V.n b := fun a b h e => h (by cases e; rfl)
        have h2a : σ2 (.n k) = word 2 0 0 := Function.update_self _ _ _
        have h2b : ∀ i < k, σ2 (.n i) = σ1 (.n i) := fun i hi => Function.update_of_ne (ne _ _ (by omega)) _ _
        have h3a : σ3 (.n (k + 1)) = gen * eOfNat (N / 2 ^ (n - 1 - j)) := Function.update_self _ _ _
        have h3b : ∀ i < k + 1, σ3 (.n i) = σ2 (.n i) := fun i hi => Function.update_of_ne (ne _ _ (by omega)) _ _
        have h4a : σ4 (.n (k + 2)) = eOfNat (N / 2 ^ (n - 1 - (j + 1))) := Function.update_self _ _ _
        have h4b : ∀ i < k + 2, σ4 (.n i) = σ3 (.n i) := fun i hi => Function.update_of_ne (ne _ _ (by omega)) _ _
        refine Completes.atom_cons (word 2 0 0) (by omega) (.cons ⟨_, by omega, rfl⟩ (.nil _)) h2a ?_
        refine Completes.atom_cons (gen * eOfNat (N / 2 ^ (n - 1 - j))) (by omega)
          (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _)))) ?_ ?_
        · change σ3 (.n (k + 1)) = σ3 (.n k) * σ3 (.n (outBase + 3 * j))
          rw [h3a, h3b _ (by omega), h3b _ (by omega), h2a, h2b _ (by omega), hprev, word_two]
        rw [show k + 1 + 1 = k + 2 by omega]
        refine Completes.atom_cons (eOfNat (N / 2 ^ (n - 1 - (j + 1)))) (by omega)
          (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _)))) ?_ ?_
        · change σ4 (.n (k + 2)) = σ4 (.n (bitBase + (n - 1 - (j + 1)))) + σ4 (.n (k + 1))
          rw [h4a, h4b _ (by omega), h4b _ (by omega), h3a, h3b _ (by omega), h2b _ (by omega), hbit,
            show n - 1 - j = n - 1 - (j + 1) + 1 by omega, add_comm (bitE _), shift_step hN64]
        refine Completes.nil _ _ _ ⟨fun r hr => ?_, fun i hi => ?_⟩
        · rcases Nat.lt_or_eq_of_le hr with hr | rfl
          · change σ4 (.n (outBase + 3 * r)) = _
            rw [h4b _ (by omega), h3b _ (by omega), h2b _ (by omega)]
            exact hv1 r (by omega)
          · rw [show outBase + 3 * (j + 1) = k + 2 by omega]; exact h4a
        · change σ (.n i) = σ4 (.n i)
          rw [hag1 i hi, h4b _ (by omega), h3b _ (by omega), h2b _ (by omega)])
      σ0 ⟨fun r hr => by
        rw [Nat.le_zero.mp hr, Nat.mul_zero, Nat.add_zero, Nat.sub_zero]; exact Function.update_self _ _ _, hag0⟩
    refine this.mono (by omega) (by omega) fun σ' ⟨h1, h2⟩ => ⟨fun r hr => h1 r (by omega), h2⟩

/-- The Booleanity checks. -/
theorem booleans_iff {σ : Val} (base : Nat) : ∀ (n : Nat) {next : Prop} {kret : List E → Prop},
    Stmt.HoldsList C rd σ (booleans base n) next kret ↔
      (∀ j < n, σ (.n (base + j)) * σ (.n (base + j)) = σ (.n (base + j))) ∧ next
  | 0, _, _ => by simp [booleans]
  | n + 1, next, kret => by
      rw [booleans, List.range_succ, List.map_append, holdsList_append, ← booleans, booleans_iff base n]
      simp only [List.map_cons, List.map_nil, mulS, holdsList_cons_atom, holdsList_nil, Atom.Holds]
      constructor
      · rintro ⟨h1, h2, hn⟩
        exact ⟨fun j hj => (Nat.lt_succ_iff_lt_or_eq.mp hj).elim (h1 j) (fun e => e ▸ h2.symm), hn⟩
      · rintro ⟨h, hn⟩
        exact ⟨fun j hj => h j (by omega), (h n (by omega)).symm, hn⟩

theorem valsList_booleans (base : Nat) : ∀ n, NumBelow (base + n) (Stmt.valsList (booleans base n))
  | 0 => NumBelow.nil _
  | n + 1 => by
      rw [booleans, List.range_succ, List.map_append, valsList_append, ← booleans]
      refine ((valsList_booleans base n).mono (by omega)).append ?_
      simp only [List.map_cons, List.map_nil, mulS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals,
        List.append_nil]
      exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _)))

/-- The powers `g^s`. -/
theorem powers_iff {σ : Val} (b : Nat) {next : Prop} {kret : List E → Prop} :
    Stmt.HoldsList C rd σ (powers b) next kret ↔ (∀ s < 10, σ (.n (b + s)) = gen ^ s) ∧ next := by
  simp only [powers, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, cst, holdsList_cons_atom, holdsList_nil, Atom.Holds]
  have hg : ∀ s < 10, word (2 ^ s) 0 0 = gen ^ s := fun s hs => by
    rw [word_eq_eOfNat, gen_pow_eq_eOfNat (by omega)]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hn⟩
    refine ⟨fun s hs => ?_, hn⟩
    rw [← hg s hs]
    interval_cases s <;> assumption
  · rintro ⟨h, hn⟩
    exact ⟨(h 0 (by omega)).trans (hg 0 (by omega)).symm, (h 1 (by omega)).trans (hg 1 (by omega)).symm,
      (h 2 (by omega)).trans (hg 2 (by omega)).symm, (h 3 (by omega)).trans (hg 3 (by omega)).symm,
      (h 4 (by omega)).trans (hg 4 (by omega)).symm, (h 5 (by omega)).trans (hg 5 (by omega)).symm,
      (h 6 (by omega)).trans (hg 6 (by omega)).symm, (h 7 (by omega)).trans (hg 7 (by omega)).symm,
      (h 8 (by omega)).trans (hg 8 (by omega)).symm, (h 9 (by omega)).trans (hg 9 (by omega)).symm, hn⟩

theorem powers_complete {σ : Val} (b : Nat) :
    Completes C rd b (b + 10) (powers b) σ
      (fun σ' => (∀ s < 10, σ' (.n (b + s)) = gen ^ s) ∧ AgreeBelow b σ σ') := by
  set σ' := upds σ ((List.range 10).map fun s => (b + s, gen ^ s))
  have he : Ext b (b + 10) σ σ' := upds_ext σ _ (by simp)
  have hv : ∀ s < 10, σ' (.n (b + s)) = gen ^ s := by
    intro s hs
    simp only [σ', List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append]
    interval_cases s <;> simp [upds]
  exact ⟨σ', he, ⟨hv, he.agree⟩, fun next kret hn => powers_iff b |>.mpr ⟨hv, hn⟩⟩

end
end LeanVM.Guest.B1.Sig
