/-
  LeanVM.Guest.B1.Whir.CCapsHints

  The honest cap's cells and flags (`capCell`, `capFl`) are the hint generator's arrays (`levelCapPushes`, `Hints.levelHints`' `merkle_caps` and `merkle_cap_active`).
-/

module

public import LeanVM.Guest.B1.Whir.CCaps
public import LeanVM.Guest.B1.Merkle.QueryPops

/-!
# The honest cap is the generator's

`levelCapPushes` writes, per opening, its climb's nodes and their siblings at the cap's levels and the root into an array of zero digests, and flags the parents of the nodes written. At openings that climb from their leaf indices and agree wherever they meet, every write at a node is its `nodeD`, so the arrays are `capCell` and `capFl` of `atIdx phase`.

* `ArrInv`, `ArrInv.foldl`: an array holding `g` on a set of indices and `z` elsewhere, kept by a fold of writes each of its index's value;
* `mem_capStepsOf`: the cap's steps are the openings' climbs' levels from `depth - cd`;
* `levelCapPushes_eq`: the generator's cap and flags are `capCell` and `capFl`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Writes into an array -/

/-- An array of `N` entries, `g v` at the `v` with `P v` and `z` elsewhere. -/
def ArrInv {β : Type} (N : ℕ) (z : β) (g : ℕ → β) (P : ℕ → Prop) (a : Array β) : Prop :=
  ∃ F : ℕ → β, a.toList = (List.range N).map F ∧ ∀ v < N, (P v → F v = g v) ∧ (¬ P v → F v = z)

theorem ArrInv.congr {β : Type} {N : ℕ} {z : β} {g : ℕ → β} {P Q : ℕ → Prop} {a : Array β}
    (h : ArrInv N z g P a) (hPQ : ∀ v, P v ↔ Q v) : ArrInv N z g Q a := by
  obtain ⟨F, hF, hP⟩ := h
  exact ⟨F, hF, fun v hv => by rw [← hPQ v]; exact hP v hv⟩

theorem arrInv_replicate {β : Type} (N : ℕ) (z : β) (g : ℕ → β) :
    ArrInv N z g (fun _ => False) (Array.replicate N z) :=
  ⟨fun _ => z, by simp, fun _ _ => ⟨False.elim, fun _ => rfl⟩⟩

/-- **A write of its index's value.** -/
theorem ArrInv.set {β : Type} {N : ℕ} {z : β} {g : ℕ → β} {P : ℕ → Prop} {a : Array β}
    (h : ArrInv N z g P a) (i : ℕ) : ArrInv N z g (fun v => P v ∨ v = i) (a.set! i (g i)) := by
  obtain ⟨F, hF, hP⟩ := h
  refine ⟨fun v => if v = i then g i else F v, ?_, fun v hv => ?_⟩
  · simp only [Array.set!, Array.toList_setIfInBounds, hF]
    refine List.ext_getElem (by simp) fun v h1 h2 => ?_
    simp only [List.getElem_set, List.getElem_map, List.getElem_range]
    by_cases e : i = v
    · subst e; simp
    · simp [e, Ne.symm e]
  · by_cases e : v = i
    · subst e; simp
    · simp only [e, ↓reduceIte, or_false]
      exact hP v hv

/-- **A fold of writes**, each of its index's value. -/
theorem ArrInv.foldl {α β : Type} {N : ℕ} {z : β} {g : ℕ → β} (step : Array β → α → Array β)
    (W : α → ℕ → Prop) : ∀ (l : List α) (P : ℕ → Prop) (a : Array β),
    (∀ x ∈ l, ∀ (P : ℕ → Prop) (a : Array β), ArrInv N z g P a → ArrInv N z g (fun v => P v ∨ W x v) (step a x)) →
    ArrInv N z g P a → ArrInv N z g (fun v => P v ∨ ∃ x ∈ l, W x v) (l.foldl step a)
  | [], P, a, _, h => h.congr fun v => by simp
  | x :: l, P, a, hs, h =>
    (ArrInv.foldl step W l _ (step a x) (fun y hy => hs y (List.mem_cons_of_mem _ hy))
      (hs x List.mem_cons_self P a h)).congr fun v => by
        simp only [List.mem_cons, exists_eq_or_imp, or_assoc]

theorem xor_one_even (m : ℕ) : (2 * m) ^^^ 1 = 2 * m + 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  rcases i with _ | i <;> simp

theorem xor_one_odd (m : ℕ) : (2 * m + 1) ^^^ 1 = 2 * m := by
  rw [← xor_one_even, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-! ## The generator's steps -/

/-- A phase's openings at their leaf indices. -/
def atIdx (phase : List Opening) : List (ℕ × Opening) := phase.map fun o => (o.leafIndex, o)

/-- The generator's steps above the path depth `pd`. -/
def capStepsOf (depth pd : ℕ) (phase : List Opening) : List (ℕ × Digest × Digest) :=
  phase.flatMap fun o => (Hints.climbSteps (2 ^ depth + o.leafIndex) (merkleLeafDigest o.leaf) o.path).1.drop pd

theorem climbSteps_snd : ∀ (ss : List Digest) (idx : ℕ) (node : Digest),
    (Hints.climbSteps idx node ss).2 = climbD node idx ss
  | [], _, _ => rfl
  | s :: ss, idx, node => by
    simp only [Hints.climbSteps]
    rw [climbSteps_snd ss, climbD_cons]

theorem index_div {D q l : ℕ} (hl : l ≤ D) : (2 ^ D + q) / 2 ^ l = heapNode D q l := by
  unfold heapNode Guest.Limits.merkleHeapIndex
  rw [show 2 ^ D = 2 ^ (D - l) * 2 ^ l by rw [← pow_add]; congr 1; omega, Nat.add_comm,
    Nat.add_mul_div_right _ _ (by positivity), Nat.add_comm]

theorem heapNode_xor {D q l : ℕ} (hl : l < D) :
    heapNode D q l ^^^ 1 = Guest.Limits.siblingHeapIndex D q l := by
  rw [heapNode_child hl, sibNode_eq]
  rcases Nat.mod_two_eq_zero_or_one (q / 2 ^ l) with h | h <;> rw [h]
  · rw [Nat.add_zero, xor_one_even]
  · rw [xor_one_odd]; rfl

theorem heapNode_ge (D q l : ℕ) : 2 ^ (D - l) ≤ heapNode D q l := by
  unfold heapNode Guest.Limits.merkleHeapIndex; exact Nat.le_add_right _ _

theorem sib_ge {D q l : ℕ} (hl : l < D) : 2 ^ (D - l) ≤ Guest.Limits.siblingHeapIndex D q l := by
  rw [sibNode_eq]
  have := heapNode_ge D q (l + 1)
  have e : 2 ^ (D - l) = 2 * 2 ^ (D - (l + 1)) := by
    rw [← pow_succ']; congr 1; omega
  omega

/-- **The cap's steps** are the openings' climbs' levels from `pd`: the node, its climbed digest, its sibling. -/
theorem mem_capStepsOf {depth pd : ℕ} {phase : List Opening}
    (hq : ∀ o ∈ phase, o.path.length = depth) (x : ℕ × Digest × Digest) :
    x ∈ capStepsOf depth pd phase ↔ ∃ o ∈ phase, ∃ l, pd ≤ l ∧ l < depth ∧
      x = (heapNode depth o.leafIndex l, climbD (merkleLeafDigest o.leaf) o.leafIndex (o.path.take l),
        o.path.getD l default) := by
  unfold capStepsOf
  rw [List.mem_flatMap]
  refine exists_congr fun o => and_congr_right fun ho => ?_
  rw [climbSteps_fst, List.mem_drop_iff_getElem, hq o ho]
  simp only [List.length_map, List.length_range, List.getElem_map, List.getElem_range]
  have key : ∀ l, l < depth → ((2 ^ depth + o.leafIndex) / 2 ^ l,
      climbD (merkleLeafDigest o.leaf) (2 ^ depth + o.leafIndex) (o.path.take l),
      o.path.getD l (Vector.replicate 4 0)) = (heapNode depth o.leafIndex l,
      climbD (merkleLeafDigest o.leaf) o.leafIndex (o.path.take l), o.path.getD l default) := by
    intro l hl
    rw [index_div hl.le, climbD_mod _ _ _ o.leafIndex (by
      rw [List.length_take, min_eq_left (by rw [hq o ho]; omega),
        show 2 ^ depth = 2 ^ (depth - l) * 2 ^ l by rw [← pow_add]; congr 1; omega,
        Nat.add_comm, Nat.add_mul_mod_self_right])]
    rfl
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨pd + j, by omega, by omega, key _ (by omega)⟩
  · rintro ⟨l, h1, h2, rfl⟩
    exact ⟨l - pd, by omega, by rw [Nat.add_sub_cancel' h1]; exact key _ h2⟩

/-! ## The arrays -/

variable {depth : ℕ} {phase : List Opening}

/-- A node below `2^(cd+1)` an opening touches is written by the generator, and conversely. -/
theorem touched_iff (hq : ∀ o ∈ phase, o.leafIndex < 2 ^ depth ∧ o.path.length = depth) {cd v : ℕ}
    (hv : v < 2 * 2 ^ cd) :
    Touched depth (atIdx phase) v ↔ (∃ x ∈ capStepsOf depth (depth - cd) phase, v = x.1 ∨ v = x.1 ^^^ 1) ∨
      ∃ o ∈ phase, v = 1 := by
  have hq' : ∀ o ∈ phase, o.path.length = depth := fun o ho => (hq o ho).2
  constructor
  · rintro ⟨a, ha, d, hg⟩
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ha
    rcases hg with ⟨l, hl, rfl, -⟩ | ⟨l, hl, rfl, -⟩
    · change heapNode depth o.leafIndex l < 2 * 2 ^ cd at hv
      rcases Nat.lt_or_ge l depth with hlt | hge
      · have := heapNode_ge depth o.leafIndex l
        have hp : 2 ^ (depth - l) < 2 ^ (cd + 1) := by rw [pow_succ]; omega
        have hl' := (Nat.pow_lt_pow_iff_right (by omega)).mp hp
        exact Or.inl ⟨_, (mem_capStepsOf hq' _).mpr ⟨o, ho, l, by omega, hlt, rfl⟩, Or.inl rfl⟩
      · exact Or.inr ⟨o, ho, by rw [show l = depth by omega]; exact heapNode_top (hq o ho).1⟩
    · change Guest.Limits.siblingHeapIndex depth o.leafIndex l < 2 * 2 ^ cd at hv
      have := sib_ge (q := o.leafIndex) hl
      have hp : 2 ^ (depth - l) < 2 ^ (cd + 1) := by rw [pow_succ]; omega
      have hl' := (Nat.pow_lt_pow_iff_right (by omega)).mp hp
      exact Or.inl ⟨_, (mem_capStepsOf hq' _).mpr ⟨o, ho, l, by omega, hl, rfl⟩,
        Or.inr (heapNode_xor hl).symm⟩
  · rintro (⟨x, hx, hvx⟩ | ⟨o, ho, rfl⟩)
    · obtain ⟨o, ho, l, -, hl, rfl⟩ := (mem_capStepsOf hq' _).mp hx
      have ha : (o.leafIndex, o) ∈ atIdx phase := List.mem_map.mpr ⟨o, ho, rfl⟩
      rcases hvx with rfl | rfl
      · exact ⟨_, ha, _, nodeIs_climb hl.le⟩
      · rw [heapNode_xor hl]; exact ⟨_, ha, _, nodeIs_sib hl⟩
    · have ha : (o.leafIndex, o) ∈ atIdx phase := List.mem_map.mpr ⟨o, ho, rfl⟩
      have := nodeIs_climb (depth := depth) (a := (o.leafIndex, o)) (l := depth) le_rfl
      rw [heapNode_top (hq o ho).1] at this
      exact ⟨_, ha, _, this⟩

/-- A digest's cells: zero on the zero digest. -/
theorem digestCells_zero : Hints.digestCells (Vector.replicate 4 0) = [0, 0] := by
  simp [Hints.digestCells, digestHalves, Value.zero_eq_ofLimbs]

/-- A run of `2n` cells, two at a time. -/
theorem range_two_mul {α : Type} (f : ℕ → α) : ∀ n : ℕ,
    (List.range (2 * n)).map f = (List.range n).flatMap fun v => [f (2 * v), f (2 * v + 1)]
  | 0 => rfl
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, List.range_add, List.map_append, range_two_mul f n,
      List.range_succ (n := n), List.flatMap_append]
    simp [List.range_succ]

/-- **The generator's cap and flags are the honest cap's**, at openings that climb from their leaf indices and agree. -/
theorem levelCapPushes_eq {count : ℕ}
    (hq : ∀ o ∈ phase, o.leafIndex < 2 ^ depth ∧ o.path.length = depth)
    (hag : Guest.Limits.OpeningsAgree depth (atIdx phase)) :
    levelCapPushes depth count phase =
      [("merkle_caps", (List.range (4 * 2 ^ Hints.capDepthOf count depth)).map (capCell depth (atIdx phase))),
        ("merkle_cap_active", (List.range (2 ^ Hints.capDepthOf count depth)).map
          (capFl depth (atIdx phase) (Hints.capDepthOf count depth)))] := by
  classical
  have hq' : ∀ o ∈ phase, o.path.length = depth := fun o ho => (hq o ho).2
  generalize hcd : Hints.capDepthOf count depth = cd
  have e : levelCapPushes depth count phase =
      [("merkle_caps", (phase.foldl (fun (a : Array Digest) o => a.set! 1
          (Hints.climbSteps (2 ^ depth + o.leafIndex) (merkleLeafDigest o.leaf) o.path).2)
        ((capStepsOf depth (depth - cd) phase).foldl (fun (a : Array Digest) step ↦
          (a.set! step.1 step.2.1).set! (step.1 ^^^ 1) step.2.2)
          (Array.replicate (2 * 2 ^ cd) (Vector.replicate 4 0)))).toList.flatMap Hints.digestCells),
       ("merkle_cap_active", ((capStepsOf depth (depth - cd) phase).foldl
          (fun (a : Array E) step ↦ a.set! (step.1 / 2) 1) (Array.replicate (2 ^ cd) 0)).toList)] := by
    rw [levelCapPushes, hcd, List.foldl_map, capStepsOf, List.flatMap_map]
  rw [e]
  set B := atIdx phase
  set S := capStepsOf depth (depth - cd) phase
  have hmemB : ∀ o ∈ phase, (o.leafIndex, o) ∈ B := fun o ho => List.mem_map.mpr ⟨o, ho, rfl⟩
  -- the nodes
  have hsteps : ArrInv (2 * 2 ^ cd) (Vector.replicate 4 0) (nodeD depth B)
      (fun v => False ∨ ∃ x ∈ S, v = x.1 ∨ v = x.1 ^^^ 1) (S.foldl (fun (a : Array Digest) step ↦
        (a.set! step.1 step.2.1).set! (step.1 ^^^ 1) step.2.2) (Array.replicate (2 * 2 ^ cd) (Vector.replicate 4 0))) :=
    ArrInv.foldl _ (fun (x : ℕ × Digest × Digest) v => v = x.1 ∨ v = x.1 ^^^ 1) S _ _ (fun x hx P a ha => by
      obtain ⟨o, ho, l, -, hl, rfl⟩ := (mem_capStepsOf hq' _).mp hx
      have h1 := nodeD_eq hag (hmemB o ho) (nodeIs_climb (a := (o.leafIndex, o)) hl.le)
      have h2 := nodeD_eq hag (hmemB o ho) (nodeIs_sib (a := (o.leafIndex, o)) hl)
      rw [← heapNode_xor hl] at h2
      have := (ha.set (heapNode depth o.leafIndex l)).set (heapNode depth o.leafIndex l ^^^ 1)
      rw [h1, h2] at this
      exact this.congr fun v => by simp only [or_assoc]) (arrInv_replicate _ _ _)
  have hroot := ArrInv.foldl (fun (a : Array Digest) o => a.set! 1
      (Hints.climbSteps (2 ^ depth + o.leafIndex) (merkleLeafDigest o.leaf) o.path).2)
    (fun _ v => v = 1) phase _ _ (fun o ho P a ha => by
      have := nodeD_eq hag (hmemB o ho) (nodeIs_climb (a := (o.leafIndex, o)) (l := depth) le_rfl)
      rw [heapNode_top (hq o ho).1, List.take_of_length_le (by rw [hq' o ho])] at this
      have h := ha.set 1
      rw [this, ← climbD_mod _ _ (2 ^ depth + o.leafIndex) o.leafIndex (by
        rw [hq' o ho, Nat.add_comm, Nat.add_mod_right]), ← climbSteps_snd] at h
      exact h) hsteps
  have hact : ArrInv (2 ^ cd) (0 : E) (fun _ => 1) (fun v => False ∨ ∃ x ∈ S, v = x.1 / 2)
      (S.foldl (fun (a : Array E) step ↦ a.set! (step.1 / 2) 1) (Array.replicate (2 ^ cd) 0)) :=
    ArrInv.foldl _ (fun (x : ℕ × Digest × Digest) v => v = x.1 / 2) S _ _ (fun x _ P a ha => ha.set (x.1 / 2))
      (arrInv_replicate _ _ _)
  obtain ⟨F, hF, hFP⟩ := hroot
  obtain ⟨Fa, hFa, hFaP⟩ := hact
  rw [hF, hFa]
  refine congrArg₂ (fun a b => [("merkle_caps", a), ("merkle_cap_active", b)]) ?_ ?_
  · rw [show 4 * 2 ^ cd = 2 * (2 * 2 ^ cd) by ring, range_two_mul (capCell depth B), List.flatMap_map]
    refine List.flatMap_congr fun v hv => ?_
    have hv' := List.mem_range.mp hv
    have ht := touched_iff hq (cd := cd) hv'
    obtain ⟨p1, p2⟩ := hFP v hv'
    by_cases hT : Touched depth B v
    · rw [p1 (by simp only [false_or]; exact ht.mp hT), capCell_even hT, capCell_odd hT]
      rfl
    · have c0 := capCell_off hT 0 (by omega)
      have c1 := capCell_off hT 1 (by omega)
      rw [Nat.add_zero] at c0
      rw [p2 (by simp only [false_or]; exact fun h => hT (ht.mpr h)), digestCells_zero, c0, c1]
  · refine List.map_congr_left fun v hv => ?_
    obtain ⟨p1, p2⟩ := hFaP v (List.mem_range.mp hv)
    rcases capFl_cases (depth := depth) (batch := B) cd v with ⟨e1, a, ha, l, h1, h2, rfl⟩ | ⟨e1, hn⟩
    · rw [e1]
      refine p1 ?_
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ha
      refine Or.inr ⟨_, (mem_capStepsOf hq' _).mpr ⟨o, ho, l - 1, by omega, by omega, rfl⟩, ?_⟩
      show _ = heapNode depth o.leafIndex (l - 1) / 2
      rw [← heapNode_parent (by omega), show l - 1 + 1 = l by omega]
    · rw [e1]
      refine p2 ?_
      rintro (h | ⟨x, hx, rfl⟩)
      · exact h
      · obtain ⟨o, ho, l, h1, hl, rfl⟩ := (mem_capStepsOf hq' _).mp hx
        exact hn ⟨_, hmemB o ho, l + 1, by omega, by omega, (heapNode_parent hl).symm⟩

end
end LeanVM.Guest.B1.Whir
