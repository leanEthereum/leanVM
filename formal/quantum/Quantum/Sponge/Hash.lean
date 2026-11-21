module

public import Quantum.Decomposition
public import Quantum.Sponge.Database

@[expose] public section

/-!
# The sponge, and the paths its evaluations leave in a database

The sponge on blocks of the rate `X`: from the state `(0, 0)`, each block is added into the rate
and `φ` applied; the hash is the final rate (one squeeze of a full rate, as in Section 3.3 of
ePrint 2025/731). For `φ = spongePerm (h, k, k') π`, the blocks absorbed into `σ_k` form a Msponge
tail (`absorbTail`): the `j`-th is the `j`-th message block plus the rate after round `j - 1`. A
database that holds the evaluation's `k` and `k'` points and the final capacity's `h` point holds
that tail and the hash as its head plus `h` (`isHeadPath_of_agrees`), and distinct messages give
distinct tails (`absorbTail_injective`). So a collision of the sponge is a collision of paths in
any database holding both evaluations.
-/

namespace Quantum.Sponge

section absorb

variable {X Z : Type} [AddCommGroup X] [Zero Z]

/-- One absorption: add the block into the rate, then apply `φ`. -/
def absorbStep (φ : Equiv.Perm (X × Z)) (s : X × Z) (b : X) : X × Z :=
  φ (s.1 + b, s.2)

/-- The state after absorbing `m` from `(0, 0)`. -/
def absorb (φ : Equiv.Perm (X × Z)) (m : List X) : X × Z :=
  m.foldl (absorbStep φ) (0, 0)

/-- The sponge's hash: the rate after absorbing `m`. -/
def spongeHash (φ : Equiv.Perm (X × Z)) (m : List X) : X :=
  (absorb φ m).1

/-- The blocks entering `φ` while absorbing `m`: each message block plus the rate before it, the
Msponge tail of `m`. -/
def absorbTail (φ : Equiv.Perm (X × Z)) (m : List X) : List X :=
  ((m.foldl (fun p b ↦ (absorbStep φ p.1 b, p.2 ++ [p.1.1 + b])) (((0, 0) : X × Z), [])).2)

theorem absorb_append_singleton (φ : Equiv.Perm (X × Z)) (m : List X) (b : X) :
    absorb φ (m ++ [b]) = absorbStep φ (absorb φ m) b := by
  simp [absorb, List.foldl_append]

omit [Zero Z] in
private theorem foldl_tail_fst (φ : Equiv.Perm (X × Z)) (m : List X) (p : (X × Z) × List X) :
    (m.foldl (fun p b ↦ (absorbStep φ p.1 b, p.2 ++ [p.1.1 + b])) p).1 =
      m.foldl (absorbStep φ) p.1 := by
  induction m generalizing p with
  | nil => rfl
  | cons b m ih => exact ih _

theorem absorbTail_append_singleton (φ : Equiv.Perm (X × Z)) (m : List X) (b : X) :
    absorbTail φ (m ++ [b]) = absorbTail φ m ++ [(absorb φ m).1 + b] := by
  simp only [absorbTail, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [foldl_tail_fst]
  rfl

@[simp]
theorem absorbTail_nil (φ : Equiv.Perm (X × Z)) : absorbTail φ [] = [] :=
  rfl

theorem length_absorbTail (φ : Equiv.Perm (X × Z)) (m : List X) :
    (absorbTail φ m).length = m.length := by
  induction m using List.reverseRecOn with
  | nil => rfl
  | append_singleton m b ih => simp [absorbTail_append_singleton, ih]

/-- Distinct messages enter `φ` through distinct block sequences. -/
theorem absorbTail_injective (φ : Equiv.Perm (X × Z)) : Function.Injective (absorbTail φ) := by
  intro m
  induction m using List.reverseRecOn with
  | nil =>
    intro m' h
    have := congrArg List.length h
    rw [length_absorbTail, length_absorbTail] at this
    exact (List.eq_nil_of_length_eq_zero this.symm).symm
  | append_singleton m b ih =>
    intro m' h
    induction m' using List.reverseRecOn with
    | nil =>
      have := congrArg List.length h
      simp [length_absorbTail] at this
    | append_singleton m' b' _ =>
      rw [absorbTail_append_singleton, absorbTail_append_singleton] at h
      obtain ⟨h1, h2⟩ := List.append_inj' h rfl
      obtain rfl := ih h1
      simp only [List.cons.injEq, and_true] at h2
      rw [add_left_cancel h2]

end absorb

variable {X Z : Type} [AddCommGroup X] [AddCommGroup Z] (π : Equiv.Perm (X × Z)) (h : Z → X)
  (k k' : X → Z)

/-- The round of `spongePerm (h, k, k') π` on a state: `σ_k`, `π`, `σ_k'`, `ω_h`. -/
theorem spongePerm_apply (s : X × Z) :
    spongePerm (h, k, k') π s =
      ((π (s.1, s.2 + k s.1)).1 + h ((π (s.1, s.2 + k s.1)).2 + k' (π (s.1, s.2 + k s.1)).1),
        (π (s.1, s.2 + k s.1)).2 + k' (π (s.1, s.2 + k s.1)).1) := by
  rfl

/-- `D` holds the `k` and `k'` points of every round of absorbing `m` under
`spongePerm (h, k, k') π`. -/
def AgreesRounds (D : Dbs X Z) (m : List X) : Prop :=
  ∀ j (hj : j < m.length),
    let s := absorb (spongePerm (h, k, k') π) (m.take j)
    let xp := s.1 + m[j]
    D.k xp = some (k xp) ∧ D.k' (π (xp, s.2 + k xp)).1 = some (k' (π (xp, s.2 + k xp)).1)

theorem AgreesRounds.of_append {D : Dbs X Z} {m : List X} {b : X}
    (hD : AgreesRounds π h k k' D (m ++ [b])) : AgreesRounds π h k k' D m := by
  intro j hj
  have hj' : j < (m ++ [b]).length := by simp; omega
  have := hD j hj'
  simp only [List.take_append_of_le_length hj.le, List.getElem_append_left hj] at this
  exact this

/-- Absorbing `m` reaches its capacity along its tail, in any database holding its rounds. -/
theorem isTail_absorbTail {D : Dbs X Z} {m : List X} (hD : AgreesRounds π h k k' D m) :
    IsTail π D (absorbTail (spongePerm (h, k, k') π) m) (absorb (spongePerm (h, k, k') π) m).2 := by
  induction m using List.reverseRecOn with
  | nil => exact IsTail.nil
  | append_singleton m b ih =>
    have hr := hD m.length (by simp)
    simp only [List.take_left', List.getElem_append_right (le_refl _), Nat.sub_self,
      List.getElem_cons_zero] at hr
    rw [absorbTail_append_singleton, absorb_append_singleton]
    exact IsTail.snoc (ih hD.of_append) hr.1 rfl hr.2

/-- **A sponge evaluation is a path.** If `D` holds the rounds of absorbing a nonempty `m` and the
`h` point of its final capacity, then `D` holds the tail `absorbTail φ m`, ending in the
intermediate pair `(xi, zi)` and the capacity `zi + k' xi`, whose `h` cell gives the hash:
`spongeHash φ m = xi + h (zi + k' xi)`. -/
theorem isHeadPath_of_agrees {D : Dbs X Z} {m : List X} (hm : m ≠ [])
    (hD : AgreesRounds π h k k' D m)
    (hh : D.h (absorb (spongePerm (h, k, k') π) m).2 =
      some (h (absorb (spongePerm (h, k, k') π) m).2)) :
    ∃ t0 zp xp a xi zi b w,
      absorbTail (spongePerm (h, k, k') π) m = t0 ++ [xp] ∧ IsTail π D t0 zp ∧
        D.k xp = some a ∧ π (xp, zp + a) = (xi, zi) ∧ D.k' xi = some b ∧
          D.h (zi + b) = some w ∧ spongeHash (spongePerm (h, k, k') π) m = xi + w := by
  obtain ⟨m, b, rfl⟩ := List.eq_nil_or_concat m |>.resolve_left hm
  set φ := spongePerm (h, k, k') π
  have hr := hD m.length (by simp)
  simp only [List.concat_eq_append, List.take_left', List.getElem_append_right (le_refl _),
    Nat.sub_self, List.getElem_cons_zero] at hr
  simp only [List.concat_eq_append] at hD hh ⊢
  set s := absorb φ m
  set xp := s.1 + b
  refine ⟨absorbTail φ m, s.2, xp, k xp, (π (xp, s.2 + k xp)).1, (π (xp, s.2 + k xp)).2,
    k' (π (xp, s.2 + k xp)).1, h ((π (xp, s.2 + k xp)).2 + k' (π (xp, s.2 + k xp)).1),
    absorbTail_append_singleton φ m b, isTail_absorbTail π h k k' hD.of_append, hr.1, rfl, hr.2,
    ?_, ?_⟩
  · rw [absorb_append_singleton] at hh
    exact hh
  · rw [spongeHash, absorb_append_singleton]
    rfl

end Quantum.Sponge

end
