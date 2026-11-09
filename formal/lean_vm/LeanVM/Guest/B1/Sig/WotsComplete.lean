/-
  LeanVM.Guest.B1.Sig.WotsComplete

  The walks of a WOTS+C arm are in single-assignment form: each step defines its constants and the
  slot it writes, never a value an earlier statement names.
-/

module

public import LeanVM.Guest.B1.Sig.FwdComplete
public import LeanVM.Guest.B1.Sig.SeqComplete
public import LeanVM.Guest.B1.Sig.WotsSound

/-!
# The walks, in single-assignment form

`InR a n x`: `x` is one of the `n` values from `a`. `StepShape W B`: a step from its constants'
base `c` and its output slot `o` (both at least `B`) is in single-assignment form, defines values
in those two ranges and names only them, its input and values below `B`. `walkT_ssa`: a walk laid
out with disjoint constants and slots is in single-assignment form, defines values in its fresh
range and its slots and names only them and values below `B`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- `x` is one of the `n` values from `a`. -/
def InR (a n : Nat) (x : V) : Prop := ∃ j < n, x = .n (a + j)

theorem SSA.append' {xs ys : List Stmt} (h1 : SSA xs) (h2 : SSA ys) {P Q : V → Prop}
    (hv : ∀ x ∈ Stmt.valsList xs, P x) (ho : ∀ x ∈ outsList ys, Q x) (hd : ∀ x, Q x → ¬ P x) :
    SSA (xs ++ ys) :=
  SSA.append h1 h2 fun x hx hm => hd x (ho x hx) (hv x hm)

/-- A scheme's step is in single-assignment form from fresh bases above `B`. -/
def StepShape (W : WotsT) (B : Nat) : Prop :=
  ∀ i s v c o, B ≤ c → B ≤ o → (c + W.size ≤ o ∨ o + 1 ≤ c) → ¬ InR c W.size v → ¬ InR o 1 v →
    SSA (W.step i s v c o) ∧
      (∀ x ∈ outsList (W.step i s v c o), InR c W.size x ∨ InR o 1 x) ∧
      (∀ x ∈ Stmt.valsList (W.step i s v c o), x = v ∨ NBv B x ∨ InR c W.size x ∨ InR o 1 x)

theorem hint_ssa (s : String) (vs : List V) : SSA [hintW s vs] :=
  ⟨trivial, fun _ _ h => by simp [aReads] at h, fun _ h => by simp [outsList] at h, trivial⟩

theorem outsList_hint (s : String) (vs : List V) : outsList [hintW s vs] = vs := by
  simp [outsList, hintW, aOuts]

theorem valsList_hint (s : String) (vs : List V) : Stmt.valsList [hintW s vs] = vs := by
  simp [hintW, Stmt.vals, Atom.vals, Hint.vals, Dest.vals]

/-- The steps of a walk, `m` of them. -/
def walkSteps (W : WotsT) (i : Nat) (slot : Nat → Nat) (stride d b : Nat) (m : Nat) : List Stmt :=
  (List.range m).flatMap fun j =>
    W.step i (d + j) (if j = 0 then .n b else .n (slot (d + j - 1))) (b + 1 + j * stride) (slot (d + j))

/-- A walk's layout: its constants and slots above `B`, the slots increasing and apart from its
start and constants. -/
structure WalkLay (W : WotsT) (B : Nat) (slot : Nat → Nat) (stride d b : Nat) : Prop where
  base : B ≤ b
  slotB : ∀ s < 3, B ≤ slot s
  inc : ∀ s t, s < t → t < 3 → slot s + 1 ≤ slot t
  strideOK : W.size ≤ stride
  apart : ∀ s < 3, ∀ j < 3 - d, slot s + 1 ≤ b + 1 + j * stride ∨ b + 1 + j * stride + W.size ≤ slot s
  start : ∀ s < 3, slot s + 1 ≤ b ∨ b < slot s

theorem walkSteps_ssa {W : WotsT} {B : Nat} (hW : StepShape W B) {i : Nat} {slot : Nat → Nat}
    {stride d b : Nat} (hd : d < 3) (hl : WalkLay W B slot stride d b) :
    ∀ m, m ≤ 3 - d →
      SSA (walkSteps W i slot stride d b m) ∧
      (∀ x ∈ outsList (walkSteps W i slot stride d b m),
        (∃ j < m, InR (b + 1 + j * stride) W.size x) ∨ ∃ s, d ≤ s ∧ s < d + m ∧ InR (slot s) 1 x) ∧
      (∀ x ∈ Stmt.valsList (walkSteps W i slot stride d b m), NBv B x ∨ x = .n b ∨
        (∃ j < m, InR (b + 1 + j * stride) W.size x) ∨ ∃ s, s < 3 ∧ s < d + m ∧ InR (slot s) 1 x)
  | 0, _ => ⟨by simp [walkSteps, SSA], by simp [walkSteps, outsList], by simp [walkSteps]⟩
  | m + 1, hm => by
      obtain ⟨i1, i2, i3⟩ := walkSteps_ssa hW hd hl m (by omega)
      have hsplit : walkSteps W i slot stride d b (m + 1) = walkSteps W i slot stride d b m ++
          W.step i (d + m) (if m = 0 then .n b else .n (slot (d + m - 1))) (b + 1 + m * stride)
            (slot (d + m)) := by
        simp only [walkSteps, List.range_succ, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
      have hcs : b + 1 + m * stride + W.size ≤ slot (d + m) ∨ slot (d + m) + 1 ≤ b + 1 + m * stride := by
        rcases hl.apart (d + m) (by omega) m (by omega) with h | h <;> omega
      have hv1 : ¬ InR (b + 1 + m * stride) W.size (if m = 0 then .n b else .n (slot (d + m - 1))) := by
        rintro ⟨j, hj, e⟩
        split at e
        · simp only [V.mk.injEq, true_and] at e; omega
        · simp only [V.mk.injEq, true_and] at e
          rcases hl.apart (d + m - 1) (by omega) m (by omega) with h | h <;> omega
      have hv2 : ¬ InR (slot (d + m)) 1 (if m = 0 then .n b else .n (slot (d + m - 1))) := by
        rintro ⟨j, hj, e⟩
        split at e
        · simp only [V.mk.injEq, true_and] at e
          rcases hl.start (d + m) (by omega) with h | h <;> omega
        · simp only [V.mk.injEq, true_and] at e
          have := hl.inc (d + m - 1) (d + m) (by omega) (by omega)
          omega
      obtain ⟨s1, s2, s3⟩ := hW i (d + m) _ _ _ (by have := hl.base; omega)
        (hl.slotB (d + m) (by omega)) hcs hv1 hv2
      rw [hsplit]
      refine ⟨SSA.append' i1 s1 i3 s2 ?_, ?_, ?_⟩
      · rintro x hx (hB | rfl | ⟨j, hj, hx'⟩ | ⟨s, hs, hsm, hx'⟩)
        · rcases hx with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;> obtain ⟨k, hk, e⟩ := hB <;>
            simp only [V.mk.injEq, true_and] at e
          · have := hl.base; omega
          · have := hl.slotB (d + m) (by omega); omega
        · rcases hx with ⟨j, hj, e⟩ | ⟨j, hj, e⟩ <;> simp only [V.mk.injEq, true_and] at e
          · omega
          · rcases hl.start (d + m) (by omega) with h | h <;> omega
        · obtain ⟨j', hj', rfl⟩ := hx'
          rcases hx with ⟨j'', hj'', e⟩ | ⟨j'', hj'', e⟩ <;> simp only [V.mk.injEq, true_and] at e
          · have : j * stride + W.size ≤ m * stride := by
              have := Nat.mul_le_mul_right stride (show j + 1 ≤ m by omega)
              have := hl.strideOK
              rw [Nat.add_mul, one_mul] at *
              omega
            omega
          · rcases hl.apart (d + m) (by omega) j (by omega) with h | h <;> omega
        · obtain ⟨j', hj', rfl⟩ := hx'
          rcases hx with ⟨j'', hj'', e⟩ | ⟨j'', hj'', e⟩ <;> simp only [V.mk.injEq, true_and] at e
          · rcases hl.apart s hs m (by omega) with h | h <;> omega
          · have := hl.inc s (d + m) (by omega) (by omega)
            omega
      · intro x hx
        rw [outsList_append] at hx
        rcases List.mem_append.mp hx with hx | hx
        · rcases i2 x hx with ⟨j, hj, h⟩ | ⟨s, h1, h2, h⟩
          · exact Or.inl ⟨j, by omega, h⟩
          · exact Or.inr ⟨s, h1, by omega, h⟩
        · rcases s2 x hx with h | h
          · exact Or.inl ⟨m, by omega, h⟩
          · exact Or.inr ⟨d + m, by omega, by omega, h⟩
      · intro x hx
        rw [valsList_append] at hx
        rcases List.mem_append.mp hx with hx | hx
        · rcases i3 x hx with h | h | ⟨j, hj, h⟩ | ⟨s, h1, h2, h⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl ⟨j, by omega, h⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨s, h1, by omega, h⟩))
        · rcases s3 x hx with rfl | h | h | h
          · split
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr (Or.inr ⟨d + m - 1, by omega, by omega, 0, by omega, by simp⟩))
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inl ⟨m, by omega, h⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨d + m, by omega, by omega, h⟩))

theorem walkT_eq_steps (W : WotsT) (i : Nat) (slot : Nat → Nat) (stride d b : Nat) (hd : d ≠ 3) :
    walkT W i slot stride d b = [hintW "chain_starts" [.n b]] ++ walkSteps W i slot stride d b (3 - d) := by
  simp [walkT, hd, walkSteps]

/-- A walk's region: its fresh values and its slots. -/
def WalkR (slot : Nat → Nat) (stride d b : Nat) (x : V) : Prop :=
  InR b (walkSize stride d) x ∨ ∃ s < 3, InR (slot s) 1 x

/-- **A walk is in single-assignment form**, defining and naming values of its region (and values
below `B`). -/
theorem walkT_ssa {W : WotsT} {B : Nat} (hW : StepShape W B) {i : Nat} {slot : Nat → Nat}
    {stride d b : Nat} (hd : d ≤ 3) (hl : WalkLay W B slot stride d b) :
    SSA (walkT W i slot stride d b) ∧
      (∀ x ∈ outsList (walkT W i slot stride d b), WalkR slot stride d b x) ∧
      (∀ x ∈ Stmt.valsList (walkT W i slot stride d b), NBv B x ∨ WalkR slot stride d b x) := by
  by_cases h3 : d = 3
  · subst h3
    simp only [walkT, ↓reduceIte]
    refine ⟨hint_ssa _ _, fun x hx => ?_, fun x hx => ?_⟩
    · rw [outsList_hint] at hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact Or.inr ⟨2, by omega, 0, by omega, by simp⟩
    · rw [valsList_hint] at hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact Or.inr (Or.inr ⟨2, by omega, 0, by omega, by simp⟩)
  · rw [walkT_eq_steps W i slot stride d b h3]
    obtain ⟨i1, i2, i3⟩ := walkSteps_ssa (i := i) hW (show d < 3 by omega) hl (3 - d) le_rfl
    have hws : walkSize stride d = 1 + (3 - d) * stride := by simp [walkSize, h3]
    have hconst : ∀ j < 3 - d, ∀ x, InR (b + 1 + j * stride) W.size x → InR b (walkSize stride d) x := by
      rintro j hj x ⟨t, ht, rfl⟩
      refine ⟨1 + j * stride + t, ?_, by simp; omega⟩
      rw [hws]
      have := Nat.mul_le_mul_right stride (show j + 1 ≤ 3 - d by omega)
      have := hl.strideOK
      rw [Nat.add_mul, one_mul] at *
      omega
    refine ⟨SSA.append' (hint_ssa _ _) i1 (P := fun x => x = .n b) (Q := fun x =>
        (∃ j < 3 - d, InR (b + 1 + j * stride) W.size x) ∨ ∃ s, d ≤ s ∧ s < d + (3 - d) ∧ InR (slot s) 1 x)
        (fun x hx => by rw [valsList_hint] at hx; simpa using hx) i2 ?_, fun x hx => ?_, fun x hx => ?_⟩
    · rintro x (⟨j, hj, t, ht, rfl⟩ | ⟨s, h1, h2, t, ht, rfl⟩) e <;> simp only [V.mk.injEq, true_and] at e
      · omega
      · rcases hl.start s (by omega) with h | h <;> omega
    · rw [outsList_append, outsList_hint] at hx
      rcases List.mem_append.mp hx with hx | hx
      · simp only [List.mem_singleton] at hx
        subst hx
        exact Or.inl ⟨0, by rw [hws]; omega, by simp⟩
      · rcases i2 x hx with ⟨j, hj, h⟩ | ⟨s, h1, h2, h⟩
        · exact Or.inl (hconst j hj x h)
        · exact Or.inr ⟨s, by omega, h⟩
    · rw [valsList_append, valsList_hint] at hx
      rcases List.mem_append.mp hx with hx | hx
      · simp only [List.mem_singleton] at hx
        subst hx
        exact Or.inr (Or.inl ⟨0, by rw [hws]; omega, by simp⟩)
      · rcases i3 x hx with h | rfl | ⟨j, hj, h⟩ | ⟨s, h1, h2, h⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨0, by rw [hws]; omega, by simp⟩)
        · exact Or.inr (Or.inl (hconst j hj x h))
        · exact Or.inr (Or.inr ⟨s, h1, h⟩)

/-- The digit of chain `r` in arm `k`. -/
abbrev dig (k r : Nat) : Nat := k / 4 ^ r % 4

theorem dig_le (k r : Nat) : dig k r ≤ 3 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))

/-- **The walks of an arm are in single-assignment form**, each walk's region apart from the
others'. -/
theorem walksT_ssa {W : WotsT} {B : Nat} (hW : StepShape W B) (slots : Nat → Nat → Nat)
    (first k stride : Nat) :
    ∀ (m r b : Nat),
      (∀ t < m, WalkLay W B (slots (r + t)) stride (dig k (r + t)) (walkBase stride k r t b)) →
      (∀ t < m, ∀ t' < m, t ≠ t' → ∀ x,
        WalkR (slots (r + t)) stride (dig k (r + t)) (walkBase stride k r t b) x →
        ¬ WalkR (slots (r + t')) stride (dig k (r + t')) (walkBase stride k r t' b) x) →
      SSA (walksT W slots first k stride m r b).1 ∧
        (∀ x ∈ outsList (walksT W slots first k stride m r b).1, ∃ t < m,
          WalkR (slots (r + t)) stride (dig k (r + t)) (walkBase stride k r t b) x) ∧
        (∀ x ∈ Stmt.valsList (walksT W slots first k stride m r b).1, NBv B x ∨ ∃ t < m,
          WalkR (slots (r + t)) stride (dig k (r + t)) (walkBase stride k r t b) x)
  | 0, _, _, _, _ => ⟨trivial, by simp [walksT, outsList], by simp [walksT]⟩
  | m + 1, r, b, hl, hd => by
      have hl0 := hl 0 (by omega)
      simp only [Nat.add_zero, walkBase] at hl0
      obtain ⟨a1, a2, a3⟩ := walkT_ssa (i := first + r) hW (dig_le k r) hl0
      have hbase : ∀ t, walkBase stride k (r + 1) t (b + walkSize stride (dig k r)) =
          walkBase stride k r (t + 1) b := fun t => rfl
      obtain ⟨r1, r2, r3⟩ := walksT_ssa hW slots first k stride m (r + 1) (b + walkSize stride (dig k r))
        (fun t ht => by
          rw [hbase, show r + 1 + t = r + (t + 1) by omega]
          exact hl (t + 1) (by omega))
        (fun t ht t' ht' hne x hx => by
          rw [hbase, show r + 1 + t = r + (t + 1) by omega] at hx
          rw [hbase, show r + 1 + t' = r + (t' + 1) by omega]
          exact hd (t + 1) (by omega) (t' + 1) (by omega) (by omega) x hx)
      have hB : ∀ t < m + 1, ∀ x, WalkR (slots (r + t)) stride (dig k (r + t)) (walkBase stride k r t b) x →
          ¬ NBv B x := by
        intro t ht x hx ⟨j, hj, e⟩
        have hlt := hl t ht
        rcases hx with ⟨u, hu, rfl⟩ | ⟨s, hs, u, hu, rfl⟩ <;> simp only [V.mk.injEq, true_and] at e
        · have := hlt.base; omega
        · have := hlt.slotB s hs; omega
      refine ⟨SSA.append' a1 r1 (P := fun x => NBv B x ∨ WalkR (slots r) stride (dig k r) b x)
          (Q := fun x => ∃ t < m, WalkR (slots (r + 1 + t)) stride (dig k (r + 1 + t))
            (walkBase stride k (r + 1) t (b + walkSize stride (dig k r))) x) a3 r2 ?_, ?_, ?_⟩
      · rintro x ⟨t, ht, hx⟩ (hb | hw)
        · rw [hbase, show r + 1 + t = r + (t + 1) by omega] at hx
          exact hB (t + 1) (by omega) x hx hb
        · rw [hbase, show r + 1 + t = r + (t + 1) by omega] at hx
          refine hd (t + 1) (by omega) 0 (by omega) (by omega) x hx ?_
          simpa [walkBase] using hw
      · intro x hx
        simp only [walksT] at hx
        rw [outsList_append] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact ⟨0, by omega, by simpa [walkBase] using a2 x hx⟩
        · obtain ⟨t, ht, h⟩ := r2 x hx
          rw [hbase, show r + 1 + t = r + (t + 1) by omega] at h
          exact ⟨t + 1, by omega, h⟩
      · intro x hx
        simp only [walksT] at hx
        rw [valsList_append] at hx
        rcases List.mem_append.mp hx with hx | hx
        · rcases a3 x hx with h | h
          · exact Or.inl h
          · exact Or.inr ⟨0, by omega, by simpa [walkBase] using h⟩
        · rcases r3 x hx with h | ⟨t, ht, h⟩
          · exact Or.inl h
          · rw [hbase, show r + 1 + t = r + (t + 1) by omega] at h
            exact Or.inr ⟨t + 1, by omega, h⟩

/-- A step's canonical inputs and outputs, from canonical external values (`good`, a property of
the values below `B`) and a canonical input. -/
def StepCanon (W : WotsT) (B : Nat) (good : Val → Prop) : Prop :=
  (∀ σ σ', AgreeBelow B σ σ' → good σ → good σ') ∧
  ∀ i s v c o σ, B ≤ c → B ≤ o → (c + W.size ≤ o ∨ o + 1 ≤ c) → ¬ InR c W.size v →
    ¬ InR o 1 v → good σ → IsCanonical128 (σ v) →
    KCanon (fwd (W.step i s v c o) σ) (W.step i s v c o) ∧
      ∀ j < 1, IsCanonical128 (fwd (W.step i s v c o) σ (.n (o + j)))

theorem walk_step_conds {W : WotsT} {B : Nat} {slot : Nat → Nat} {stride d b m : Nat} (hd : d < 3)
    (hl : WalkLay W B slot stride d b) (hm : m < 3 - d) :
    B ≤ b + 1 + m * stride ∧ B ≤ slot (d + m) ∧
      (b + 1 + m * stride + W.size ≤ slot (d + m) ∨ slot (d + m) + 1 ≤ b + 1 + m * stride) ∧
      ¬ InR (b + 1 + m * stride) W.size (if m = 0 then .n b else .n (slot (d + m - 1))) ∧
      ¬ InR (slot (d + m)) 1 (if m = 0 then .n b else .n (slot (d + m - 1))) := by
  refine ⟨by have := hl.base; omega, hl.slotB (d + m) (by omega), ?_, ?_, ?_⟩
  · rcases hl.apart (d + m) (by omega) m hm with h | h <;> omega
  · rintro ⟨j, hj, e⟩
    split at e
    · simp only [V.mk.injEq, true_and] at e; omega
    · simp only [V.mk.injEq, true_and] at e
      rcases hl.apart (d + m - 1) (by omega) m hm with h | h <;> omega
  · rintro ⟨j, hj, e⟩
    split at e
    · simp only [V.mk.injEq, true_and] at e
      rcases hl.start (d + m) (by omega) with h | h <;> omega
    · simp only [V.mk.injEq, true_and] at e
      have := hl.inc (d + m - 1) (d + m) (by omega) (by omega)
      omega

/-- **A walk's `KECCAK`s read canonical inputs** and its slots hold canonical cells. -/
theorem walkSteps_canon {W : WotsT} {B : Nat} {good : Val → Prop} (hW : StepShape W B)
    (hc : StepCanon W B good) {i : Nat} {slot : Nat → Nat} {stride d b : Nat} (hd : d < 3)
    (hl : WalkLay W B slot stride d b) :
    ∀ m, m ≤ 3 - d → ∀ σ, good σ → IsCanonical128 (σ (.n b)) →
      KCanon (fwd (walkSteps W i slot stride d b m) σ) (walkSteps W i slot stride d b m) ∧
      ∀ s, d ≤ s → s < d + m → ∀ j < 1, IsCanonical128 (fwd (walkSteps W i slot stride d b m) σ (.n (slot s + j)))
  | 0, _, σ, _, _ => ⟨fun _ _ _ _ h => by simp [walkSteps] at h, fun s h1 h2 => by omega⟩
  | m + 1, hm, σ, hg, hb => by
      obtain ⟨i1, i2⟩ := walkSteps_canon (i := i) hW hc hd hl m (by omega) σ hg hb
      obtain ⟨c1, c2, c3, c4, c5⟩ := walk_step_conds hd hl (show m < 3 - d by omega)
      have hsplit : walkSteps W i slot stride d b (m + 1) = walkSteps W i slot stride d b m ++
          W.step i (d + m) (if m = 0 then .n b else .n (slot (d + m - 1))) (b + 1 + m * stride)
            (slot (d + m)) := by
        simp only [walkSteps, List.range_succ, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
      have hs := (walkSteps_ssa (i := i) hW hd hl (m + 1) hm)
      rw [hsplit] at hs ⊢
      have hdisj := SSA.disj hs.1
      obtain ⟨-, i2s, -⟩ := walkSteps_ssa (i := i) hW hd hl m (by omega)
      have hag : AgreeBelow B σ (fwd (walkSteps W i slot stride d b m) σ) := fwd_agree (fun v hv ⟨j, hj, e⟩ => by
        subst e
        rcases i2s _ hv with ⟨t, ht, u, hu, e⟩ | ⟨s, h1, h2, u, hu, e⟩ <;> simp only [V.mk.injEq, true_and] at e
        · have := hl.base; omega
        · have := hl.slotB s (by omega); omega) σ
      have hv : IsCanonical128 (fwd (walkSteps W i slot stride d b m) σ
          (if m = 0 then .n b else .n (slot (d + m - 1)))) := by
        split
        · rename_i h0; subst h0; simpa [walkSteps, fwd] using hb
        · have := i2 (d + m - 1) (by omega) (by omega) 0 (by omega)
          simpa using this
      obtain ⟨k1, k2⟩ := hc.2 i (d + m) _ _ _ (fwd (walkSteps W i slot stride d b m) σ) c1 c2 c3 c4 c5
        (hc.1 _ _ hag hg) hv
      obtain ⟨-, so, -⟩ := hW i (d + m) _ _ _ c1 c2 c3 c4 c5
      refine ⟨KCanon.append i1 k1 hdisj, fun s h1 h2 j hj => ?_⟩
      rw [fwd_append]
      by_cases hs' : s = d + m
      · subst hs'
        exact k2 j hj
      · rw [fwd_of_not_mem _ _ fun hm => ?_]
        · exact i2 s h1 (by omega) j hj
        · rcases so _ hm with ⟨u, hu, e⟩ | ⟨u, hu, e⟩ <;> simp only [V.mk.injEq, true_and] at e
          · rcases hl.apart s (by omega) m (by omega) with h | h <;> omega
          · have := hl.inc s (d + m) (by omega) (by omega)
            omega

theorem fwd_hint (s : String) (vs : List V) (σ : Val) : fwd [hintW s vs] σ = σ := rfl

/-- A walk's start or hinted tip is canonical. -/
def StartCanon (σ : Val) (slot : Nat → Nat) (d b : Nat) : Prop :=
  IsCanonical128 (σ (walkStartV slot d b))

/-- **A walk's `KECCAK`s read canonical inputs**, and its tip is canonical. -/
theorem walkT_canon {W : WotsT} {B : Nat} {good : Val → Prop} (hW : StepShape W B)
    (hc : StepCanon W B good) {i : Nat} {slot : Nat → Nat} {stride d b : Nat} (hd : d ≤ 3)
    (hl : WalkLay W B slot stride d b) (σ : Val) (hg : good σ) (hs : StartCanon σ slot d b) :
    KCanon (fwd (walkT W i slot stride d b) σ) (walkT W i slot stride d b) ∧
      IsCanonical128 (fwd (walkT W i slot stride d b) σ (.n (slot 2))) := by
  by_cases h3 : d = 3
  · subst h3
    simp only [walkT, ↓reduceIte, fwd_hint]
    refine ⟨fun _ _ _ _ h => by simp [hintW] at h, ?_⟩
    simpa [StartCanon, walkStartV] using hs
  · have hs' : IsCanonical128 (σ (.n b)) := by simpa [StartCanon, walkStartV, h3] using hs
    rw [walkT_eq_steps W i slot stride d b h3, fwd_append, fwd_hint]
    obtain ⟨k1, k2⟩ := walkSteps_canon (i := i) hW hc (show d < 3 by omega) hl (3 - d) le_rfl σ hg hs'
    refine ⟨KCanon.append (xs := [hintW "chain_starts" [.n b]]) (fun _ _ _ _ h => by simp [hintW] at h)
      k1 (SSA.disj (walkT_eq_steps W i slot stride d b h3 ▸ (walkT_ssa (i := i) hW hd hl).1)), ?_⟩
    simpa using k2 2 (by omega) (by omega) 0 (by omega)

/-- **The walks' `KECCAK`s read canonical inputs**, and their tips are canonical. -/
theorem walksT_canon {W : WotsT} {B : Nat} {good : Val → Prop} (hW : StepShape W B)
    (hc : StepCanon W B good) (slots : Nat → Nat → Nat) (first k stride : Nat) :
    ∀ (m r b : Nat),
      (∀ t < m, WalkLay W B (slots (r + t)) stride (dig k (r + t)) (walkBase stride k r t b)) →
      (∀ t < m, ∀ t' < m, t ≠ t' → ∀ x,
        WalkR (slots (r + t)) stride (dig k (r + t)) (walkBase stride k r t b) x →
        ¬ WalkR (slots (r + t')) stride (dig k (r + t')) (walkBase stride k r t' b) x) →
      ∀ σ, good σ →
      (∀ t < m, StartCanon σ (slots (r + t)) (dig k (r + t)) (walkBase stride k r t b)) →
      KCanon (fwd (walksT W slots first k stride m r b).1 σ) (walksT W slots first k stride m r b).1 ∧
        ∀ t < m, IsCanonical128 (fwd (walksT W slots first k stride m r b).1 σ (.n (slots (r + t) 2)))
  | 0, _, _, _, _, σ, _, _ => ⟨fun _ _ _ _ h => by simp [walksT] at h, fun t ht => by omega⟩
  | m + 1, r, b, hl, hd, σ, hg, hs => by
      have hl0 := hl 0 (by omega)
      simp only [Nat.add_zero, walkBase] at hl0
      have hs0 := hs 0 (by omega)
      simp only [Nat.add_zero, walkBase] at hs0
      have hbase : ∀ t, walkBase stride k (r + 1) t (b + walkSize stride (dig k r)) =
          walkBase stride k r (t + 1) b := fun t => rfl
      obtain ⟨a1, a2, a3⟩ := walkT_ssa (i := first + r) hW (dig_le k r) hl0
      obtain ⟨c1, c2⟩ := walkT_canon (i := first + r) hW hc (dig_le k r) hl0 σ hg hs0
      set σ1 := fwd (walkT W (first + r) (slots r) stride (dig k r) b) σ with hσ1
      have hnb : ∀ v ∈ outsList (walkT W (first + r) (slots r) stride (dig k r) b), ¬ NBvF B v := by
        intro v hv ⟨j, hj, e⟩
        subst e
        rcases a2 _ hv with ⟨u, hu, e⟩ | ⟨s, hs', u, hu, e⟩ <;> simp only [V.mk.injEq, true_and] at e
        · have := hl0.base; omega
        · have := hl0.slotB s hs'; omega
      have hg1 : good σ1 := hc.1 _ _ (fwd_agree hnb σ) hg
      have hwr : ∀ t, t + 1 < m + 1 → ∀ v ∈ outsList (walkT W (first + r) (slots r) stride (dig k r) b),
          ¬ WalkR (slots (r + (t + 1))) stride (dig k (r + (t + 1))) (walkBase stride k r (t + 1) b) v := by
        intro t ht v hv hw
        exact hd 0 (by omega) (t + 1) ht (by omega) v (by simpa [walkBase] using a2 v hv) hw
      obtain ⟨r1, r2⟩ := walksT_canon hW hc slots first k stride m (r + 1) (b + walkSize stride (dig k r))
        (fun t ht => by
          rw [hbase, show r + 1 + t = r + (t + 1) by omega]
          exact hl (t + 1) (by omega))
        (fun t ht t' ht' hne x hx => by
          rw [hbase, show r + 1 + t = r + (t + 1) by omega] at hx
          rw [hbase, show r + 1 + t' = r + (t' + 1) by omega]
          exact hd (t + 1) (by omega) (t' + 1) (by omega) (by omega) x hx)
        σ1 hg1 (fun t ht => by
          rw [hbase, show r + 1 + t = r + (t + 1) by omega]
          have := hs (t + 1) (by omega)
          unfold StartCanon at this ⊢
          rw [hσ1, fwd_of_not_mem _ _ fun hm => hwr t (by omega) _ hm ?_]
          · exact this
          · unfold walkStartV
            split
            · exact Or.inr ⟨2, by omega, 0, by omega, by simp⟩
            · rename_i h3
              exact Or.inl ⟨0, by simp [walkSize, h3], by simp⟩)
      obtain ⟨-, rs2, -⟩ := walksT_ssa hW slots first k stride m (r + 1) (b + walkSize stride (dig k r))
        (fun t ht => by
          rw [hbase, show r + 1 + t = r + (t + 1) by omega]
          exact hl (t + 1) (by omega))
        (fun t ht t' ht' hne x hx => by
          rw [hbase, show r + 1 + t = r + (t + 1) by omega] at hx
          rw [hbase, show r + 1 + t' = r + (t' + 1) by omega]
          exact hd (t + 1) (by omega) (t' + 1) (by omega) (by omega) x hx)
      have hdisj := SSA.disj (walksT_ssa hW slots first k stride (m + 1) r b hl hd).1
      simp only [walksT] at hdisj ⊢
      refine ⟨KCanon.append c1 r1 hdisj, fun t ht => ?_⟩
      rw [fwd_append]
      rcases t with _ | t
      · rw [fwd_of_not_mem _ _ fun hm => ?_]
        · simpa using c2
        · obtain ⟨t', ht', hw⟩ := rs2 _ hm
          rw [hbase, show r + 1 + t' = r + (t' + 1) by omega] at hw
          exact hd (t' + 1) (by omega) 0 (by omega) (by omega) _ hw
            (Or.inr ⟨2, by omega, 0, by omega, by simp⟩)
      · have := r2 t (by omega)
        rwa [show r + 1 + t = r + (t + 1) by omega] at this

theorem NBv.mono' {b b' : Nat} {v : V} (h : NBv b v) (hle : b ≤ b') : NBv b' v := by
  obtain ⟨j, hj, rfl⟩ := h; exact ⟨j, by omega, rfl⟩

theorem StepShape.mono {W : WotsT} {B B' : Nat} (h : StepShape W B) (hle : B ≤ B') : StepShape W B' := by
  intro i s v c o hc ho hco h1 h2
  obtain ⟨a1, a2, a3⟩ := h i s v c o (by omega) (by omega) hco h1 h2
  refine ⟨a1, a2, fun x hx => ?_⟩
  rcases a3 x hx with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (h.mono' hle))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem StepCanon.mono {W : WotsT} {B B' : Nat} {good : Val → Prop} (h : StepCanon W B good)
    (hle : B ≤ B') : StepCanon W B' good :=
  ⟨fun σ σ' hσ hg => h.1 σ σ' (fun k hk => hσ k (by omega)) hg,
    fun i s v c o σ hc ho hco h1 h2 hg hv => h.2 i s v c o σ (by omega) (by omega) hco h1 h2 hg hv⟩

end
end LeanVM.Guest.B1.Sig
