module

public import Quantum.Sponge.Indifferentiability.Paths
public import Mathlib.Data.Set.Finite.List

@[expose] public section

/-!
# The sponge from the Msponge and back (`fix`, Lemma 5.5)

Section 5.2 of Alagic, Carolan, Majenz and Tokat (ePrint 2025/731). The sponge absorbs block `b`
by adding the current rate, so it feeds the Msponge the tail `fix m`, whose `i`-th block is `m_i`
plus the sponge's rate after `m_1 … m_{i-1}`, that is the Msponge of the tail so far.

* `fixFwd g m`: from a Msponge oracle `g`, the sponge's rate after `m` (the paper's `C_2^g`, `0`
  for `[]`) and the tail `fix_g m`; `fixInv f t`: from a sponge oracle `f`, the Msponge's output on
  `t` (`C_1^f`) and the message `fix⁻¹_f t`. They query their oracle only on nonempty lists no
  longer than the input (`fixFwd_congr`, `fixInv_congr`) and invert each other
  (`fixFwd_fixInv`, `fixInv_fixFwd`).
* `Msg X l`: block lists of length `1` to `l`. On oracles `Msg X l → X`, `toSponge = C_2` and
  `toMsponge = C_1` are inverse bijections (`spongeEquiv`), so **Lemma 5.5**: the joint laws of
  `(g, C_2^g)` and `(C_1^f, f)` under uniform `g`, `f` agree (`sum_toSponge`).
* `fixFwd_msp`, `toSponge_msp`: on total tables the sponge is `C_2` of the Msponge `msp`, along the
  tail `absorbTail`.
-/

namespace Quantum.Sponge

section lists

variable {X : Type} [AddCommGroup X]

/-- The sponge from a Msponge oracle `g` (`C_2^g` and `fix_g`): block `b` enters the tail as `b`
plus the current rate, and the rate becomes `g` of the tail so far. The final rate (`0` for `[]`)
and the tail. -/
def fixFwd (g : List X → X) (m : List X) : X × List X :=
  m.foldl (fun p b ↦ (g (p.2 ++ [p.1 + b]), p.2 ++ [p.1 + b])) (0, [])

/-- The Msponge from a sponge oracle `f` (`C_1^f` and `fix⁻¹_f`): tail block `c` enters the
message as `c` minus the current rate, and the rate becomes `f` of the message so far. The final
rate (`0` for `[]`) and the message. -/
def fixInv (f : List X → X) (t : List X) : X × List X :=
  t.foldl (fun p c ↦ (f (p.2 ++ [c - p.1]), p.2 ++ [c - p.1])) (0, [])

@[simp] theorem fixFwd_nil (g : List X → X) : fixFwd g [] = (0, []) :=
  rfl

@[simp] theorem fixInv_nil (f : List X → X) : fixInv f [] = (0, []) :=
  rfl

theorem fixFwd_append_singleton (g : List X → X) (m : List X) (b : X) :
    fixFwd g (m ++ [b]) =
      (g ((fixFwd g m).2 ++ [(fixFwd g m).1 + b]), (fixFwd g m).2 ++ [(fixFwd g m).1 + b]) := by
  simp [fixFwd, List.foldl_append]

theorem fixInv_append_singleton (f : List X → X) (t : List X) (c : X) :
    fixInv f (t ++ [c]) =
      (f ((fixInv f t).2 ++ [c - (fixInv f t).1]), (fixInv f t).2 ++ [c - (fixInv f t).1]) := by
  simp [fixInv, List.foldl_append]

theorem length_fixFwd (g : List X → X) (m : List X) : (fixFwd g m).2.length = m.length := by
  induction m using List.reverseRecOn with
  | nil => rfl
  | append_singleton m b ih => simp [fixFwd_append_singleton, ih]

theorem length_fixInv (f : List X → X) (t : List X) : (fixInv f t).2.length = t.length := by
  induction t using List.reverseRecOn with
  | nil => rfl
  | append_singleton t c ih => simp [fixInv_append_singleton, ih]

theorem fixFwd_fst_of_ne_nil (g : List X → X) {m : List X} (hm : m ≠ []) :
    (fixFwd g m).1 = g (fixFwd g m).2 := by
  obtain ⟨m, b, rfl⟩ := List.eq_nil_or_concat m |>.resolve_left hm
  simp [fixFwd_append_singleton]

theorem fixInv_fst_of_ne_nil (f : List X → X) {t : List X} (ht : t ≠ []) :
    (fixInv f t).1 = f (fixInv f t).2 := by
  obtain ⟨t, c, rfl⟩ := List.eq_nil_or_concat t |>.resolve_left ht
  simp [fixInv_append_singleton]

/-- `fixFwd` only queries `g` on nonempty lists no longer than its input. -/
theorem fixFwd_congr {g₁ g₂ : List X → X} {m : List X}
    (h : ∀ t : List X, t ≠ [] → t.length ≤ m.length → g₁ t = g₂ t) :
    fixFwd g₁ m = fixFwd g₂ m := by
  induction m using List.reverseRecOn with
  | nil => rfl
  | append_singleton m b ih =>
    have ih := ih fun t ht hl ↦ h t ht (by simp; omega)
    rw [fixFwd_append_singleton, fixFwd_append_singleton, ih,
      h _ (by simp) (by simp [length_fixFwd])]

/-- `fixInv` only queries `f` on nonempty lists no longer than its input. -/
theorem fixInv_congr {f₁ f₂ : List X → X} {t : List X}
    (h : ∀ m : List X, m ≠ [] → m.length ≤ t.length → f₁ m = f₂ m) :
    fixInv f₁ t = fixInv f₂ t := by
  induction t using List.reverseRecOn with
  | nil => rfl
  | append_singleton t c ih =>
    have ih := ih fun m hm hl ↦ h m hm (by simp; omega)
    rw [fixInv_append_singleton, fixInv_append_singleton, ih,
      h _ (by simp) (by simp [length_fixInv])]

/-- `fix_g` undoes `fix⁻¹` of the sponge oracle `C_2^g`. -/
theorem fixFwd_fixInv (g : List X → X) (t : List X) :
    fixFwd g (fixInv (fun m ↦ (fixFwd g m).1) t).2 =
      ((fixInv (fun m ↦ (fixFwd g m).1) t).1, t) := by
  induction t using List.reverseRecOn with
  | nil => rfl
  | append_singleton t c ih =>
    rw [fixInv_append_singleton, fixFwd_append_singleton, ih]
    simp

/-- `fix⁻¹_f` undoes `fix` of the Msponge oracle `C_1^f`. -/
theorem fixInv_fixFwd (f : List X → X) (m : List X) :
    fixInv f (fixFwd (fun t ↦ (fixInv f t).1) m).2 =
      ((fixFwd (fun t ↦ (fixInv f t).1) m).1, m) := by
  induction m using List.reverseRecOn with
  | nil => rfl
  | append_singleton m b ih =>
    rw [fixFwd_append_singleton, fixInv_append_singleton, ih]
    simp

/-- `C_1^{C_2^g} = g` on nonempty lists. -/
theorem fixInv_fixFwd_fst (g : List X → X) {t : List X} (ht : t ≠ []) :
    (fixInv (fun m ↦ (fixFwd g m).1) t).1 = g t := by
  have h := fixFwd_fixInv g t
  have hne : (fixInv (fun m ↦ (fixFwd g m).1) t).2 ≠ [] := by
    rw [← List.length_pos_iff, length_fixInv]
    exact List.length_pos_iff.2 ht
  rw [← congrArg Prod.fst h, fixFwd_fst_of_ne_nil g hne, congrArg Prod.snd h]

/-- `C_2^{C_1^f} = f` on nonempty lists. -/
theorem fixFwd_fixInv_fst (f : List X → X) {m : List X} (hm : m ≠ []) :
    (fixFwd (fun t ↦ (fixInv f t).1) m).1 = f m := by
  have h := fixInv_fixFwd f m
  have hne : (fixFwd (fun t ↦ (fixInv f t).1) m).2 ≠ [] := by
    rw [← List.length_pos_iff, length_fixFwd]
    exact List.length_pos_iff.2 hm
  rw [← congrArg Prod.fst h, fixInv_fst_of_ne_nil f hne, congrArg Prod.snd h]

end lists

/-! ## Bounded messages -/

/-- Block lists of length `1` to `l`: the bounded messages of the sponge and of the Msponge. -/
def Msg (X : Type) (l : ℕ) : Type :=
  {m : List X // m ≠ [] ∧ m.length ≤ l}

instance instDecidableEqMsg {X : Type} [DecidableEq X] (l : ℕ) : DecidableEq (Msg X l) :=
  inferInstanceAs (DecidableEq {m : List X // m ≠ [] ∧ m.length ≤ l})

instance instFiniteMsg {X : Type} [Finite X] (l : ℕ) : Finite (Msg X l) :=
  ((List.finite_length_le X l).subset fun _ hm ↦ hm.2).to_subtype

noncomputable instance instFintypeMsg {X : Type} [Finite X] (l : ℕ) : Fintype (Msg X l) :=
  Fintype.ofFinite _

section msg

variable {X : Type} [AddCommGroup X] {l : ℕ}

/-- An oracle on bounded messages, extended by `0` to all lists. -/
def extMsg (g : Msg X l → X) : List X → X :=
  fun m ↦ if h : m ≠ [] ∧ m.length ≤ l then g ⟨m, h⟩ else 0

theorem extMsg_of_le (g : Msg X l → X) {m : List X} (hm : m ≠ []) (hl : m.length ≤ l) :
    extMsg g m = g ⟨m, hm, hl⟩ :=
  dite_eq_left ⟨hm, hl⟩

/-- `C_2^g`: the sponge from a Msponge oracle on bounded messages. -/
def toSponge (g : Msg X l → X) : Msg X l → X :=
  fun m ↦ (fixFwd (extMsg g) m.1).1

/-- `C_1^f`: the Msponge from a sponge oracle on bounded messages. -/
def toMsponge (f : Msg X l → X) : Msg X l → X :=
  fun t ↦ (fixInv (extMsg f) t.1).1

theorem toMsponge_toSponge (g : Msg X l → X) : toMsponge (toSponge g) = g := by
  funext t
  rw [toMsponge, fixInv_congr (f₂ := fun m ↦ (fixFwd (extMsg g) m).1) fun m hm hl ↦ by
    rw [extMsg_of_le _ hm (hl.trans t.2.2)]; rfl, fixInv_fixFwd_fst _ t.2.1,
    extMsg_of_le _ t.2.1 t.2.2]
  rfl

theorem toSponge_toMsponge (f : Msg X l → X) : toSponge (toMsponge f) = f := by
  funext m
  rw [toSponge, fixFwd_congr (g₂ := fun t ↦ (fixInv (extMsg f) t).1) fun t ht hl ↦ by
    rw [extMsg_of_le _ ht (hl.trans m.2.2)]; rfl, fixFwd_fixInv_fst _ m.2.1,
    extMsg_of_le _ m.2.1 m.2.2]
  rfl

/-- `C_2` and `C_1` are inverse bijections of the oracles on bounded messages. -/
def spongeEquiv : (Msg X l → X) ≃ (Msg X l → X) where
  toFun := toSponge
  invFun := toMsponge
  left_inv := toMsponge_toSponge
  right_inv := toSponge_toMsponge

/-- **Lemma 5.5** (joint laws, perfect): for uniform oracles, `(g, C_2^g)` and `(C_1^f, f)` have
the same joint law. -/
theorem sum_toSponge [Fintype X] [DecidableEq X] {β : Type*} [AddCommMonoid β]
    (F : (Msg X l → X) → (Msg X l → X) → β) :
    ∑ g, F g (toSponge g) = ∑ f, F (toMsponge f) f := by
  classical
  exact Fintype.sum_equiv spongeEquiv _ _ fun g ↦ by
    show _ = F (toMsponge (toSponge g)) (toSponge g)
    rw [toMsponge_toSponge]

end msg

/-! ## The sponge is `C_2` of the Msponge -/

section sponge

variable {X Z : Type} [AddCommGroup X] [AddCommGroup Z] (π : Equiv.Perm (X × Z)) (h : Z → X)
  (k k' : X → Z)

/-- On total tables, `C_2` of the Msponge `msp` is the sponge's hash, along the tail
`absorbTail`. -/
theorem fixFwd_msp (m : List X) :
    fixFwd (msp π h k k') m =
      (spongeHash (spongePerm (h, k, k') π) m, absorbTail (spongePerm (h, k, k') π) m) := by
  induction m using List.reverseRecOn with
  | nil => rfl
  | append_singleton m b ih =>
    rw [fixFwd_append_singleton, ih, spongeHash_eq_msp π h k k' (m := m ++ [b]) (by simp),
      absorbTail_append_singleton]
    rfl

/-- **The sponge is `C_2^{MSp}`** on bounded messages. -/
theorem toSponge_msp {l : ℕ} (m : Msg X l) :
    toSponge (fun t : Msg X l ↦ msp π h k k' t.1) m = spongeHash (spongePerm (h, k, k') π) m.1 := by
  rw [toSponge, fixFwd_congr (g₂ := msp π h k k') fun t ht hl ↦ extMsg_of_le _ ht
    (hl.trans m.2.2), fixFwd_msp]

end sponge

end Quantum.Sponge

end
