/-
  LeanVM.Guest.B1.Da.Help

  Shared lemmas of LeanDA's proofs: loops, trees in memory, words.
-/

module

public import LeanVM.Guest.B1.Da.Tree
public import LeanVM.Guest.B1.Da.Factors

/-!
# LeanDA's shared lemmas

* `loop_from`: a `mul_range` loop started at `g^a` gives its body at every `g^j`, `a ≤ j < m`;
  `loop_params`: a checked loop's parameters;
* `shift`: reading through `p·g^a·(g^j)^c` at `k` is reading `p` at `a + c·j + k`;
* `leaves_of_reads`: leaves a `da_levels` run read (`ReadsAt` of their cells) are the nodes the
  memory holds;
* `levels_root_of`: a `da_levels` run dispatched on `g^L` over `2^L` nodes of digests `g` returns
  the cells of `mRoot L g`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader}

theorem ofK_add (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

/-- **A loop from `g^a`**: a run at `g^a` gives the body at every `g^j`, `a ≤ j < m`. -/
theorem loop_from {f : String} {ps : List E} {N : E} {m a : ℕ} {B : E → Prop}
    (hm : m < ordG) (hN : N = gen ^ m)
    (hstep : ∀ x, coreProgram.Rel rd f (x :: ps) [] →
      B x ∧ (x * gen + N ≠ 0 → coreProgram.Rel rd f (x * gen :: ps) []))
    (h : coreProgram.Rel rd f (gen ^ a :: ps) []) : ∀ j, a ≤ j → j < m → B (gen ^ j) := by
  have key : ∀ t k, k + t = m → coreProgram.Rel rd f (gen ^ k :: ps) [] →
      ∀ j, k ≤ j → j < m → B (gen ^ j) := by
    intro t
    induction t with
    | zero => intro k hk _ j h1 h2; omega
    | succ t ih =>
      intro k hk hrun j h1 h2
      obtain ⟨hB, hnext⟩ := hstep _ hrun
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact hB
      · have hne : gen ^ k * gen + N ≠ 0 := by
          intro he
          rw [gen_pow_add_eq_zero_iff, hN] at he
          have := gen_pow_inj hm (by unfold ordG at hm; omega) he
          omega
        have := hnext hne
        rw [gen_pow_mul_gen] at this
        exact ih (k + 1) (by omega) this j hlt h2
  intro j h1 h2
  exact key (m - a) a (by omega) h j h1 h2

/-- Unpacking a checked loop's parameters. -/
theorem loop_params {j : ℕ} {f : String} (hshape : loopShapeF (coreProgram.getD j default) f = true)
    {n : ℕ} (hlen : (coreProgram.getD j default).params.length = n) :
    (coreProgram.getD j default).params = (List.range n).map V.n := by
  have hs := hshape
  simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hs
  rw [hs.1.2, hlen]

theorem shift {p v : E} {a c j k : ℕ} :
    LoadHolds rd (p * gen ^ a * (gen ^ j) ^ c) k v ↔ LoadHolds rd p (a + c * j + k) v := by
  rw [ptr_pow, loadHolds_mul_gen_pow]

theorem shift2 {p v : E} {c j k : ℕ} :
    LoadHolds rd (p * (gen ^ j) ^ c) k v ↔ LoadHolds rd p (c * j + k) v := by
  rw [← pow_mul, loadHolds_mul_gen_pow, mul_comm j c]

theorem pairCells_getD : ∀ (l : List (E × E)) (i : ℕ),
    (pairCells l).getD (2 * i) 0 = (l.getD i 0).1 ∧ (pairCells l).getD (2 * i + 1) 0 = (l.getD i 0).2
  | [], _ => by simp [pairCells]
  | p :: l, 0 => by simp [pairCells]
  | p :: l, i + 1 => by
    have ih := pairCells_getD l i
    simp only [pairCells, List.flatMap_cons, List.cons_append, List.nil_append] at ih ⊢
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, List.getD_cons_succ, List.getD_cons_succ,
      List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
    exact ih

/-- **Leaves a run read are the memory's nodes.** -/
theorem leaves_of_reads {tree : E} {n : ℕ} {leaves : List (E × E)} {f : ℕ → E × E}
    (hl : leaves.length = n) (hr : ReadsAt rd tree (pairCells leaves))
    (hf : ∀ i < n, LoadHolds rd tree (2 * i) (f i).1 ∧ LoadHolds rd tree (2 * i + 1) (f i).2) :
    leaves = (List.range n).map f := by
  have hpl : (pairCells leaves).length = 2 * n := by
    simp [pairCells, List.length_flatMap, hl, mul_comm]
  refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
  have hi : i < n := by omega
  obtain ⟨e1, e2⟩ := pairCells_getD leaves i
  have r1 := hr (2 * i) (by omega)
  have r2 := hr (2 * i + 1) (by omega)
  rw [← List.getD_eq_getElem _ 0 (by omega), e1, List.getD_eq_getElem _ _ h1] at r1
  rw [← List.getD_eq_getElem _ 0 (by omega), e2, List.getD_eq_getElem _ _ h1] at r2
  obtain ⟨f1, f2⟩ := hf i hi
  rw [List.getElem_map, List.getElem_range]
  exact Prod.ext (loadHolds_unique r1 f1) (loadHolds_unique r2 f2)

/-- **A dispatched `da_levels` run over digests' cells returns the root's cells.** -/
theorem levels_root_of {tree c0 c1 : E} {k L : ℕ} (hk : k < 11) (hL : L ≤ 10)
    (hkL : ofK (Parameters.addressOfIndex k) = gen ^ L)
    (hrel : coreProgram.Rel rd (daLevelsName k) [tree] [c0, c1]) {g : ℕ → Digest}
    (hf : ∀ i < 2 ^ L, LoadHolds rd tree (2 * i) (digestHalves (g i)).1 ∧
      LoadHolds rd tree (2 * i + 1) (digestHalves (g i)).2) :
    (c0, c1) = digestHalves (mRoot L g) := by
  have hkl : k = L := by
    rw [← gen_pow_eq_ofK] at hkL
    exact gen_pow_inj (by omega) (by omega) hkL
  subst hkl
  obtain ⟨leaves, hl, hr, hrets⟩ := da_levels_holds k (by omega) rd _ _ hrel
  have := leaves_of_reads (f := fun i => digestHalves (g i)) hl hr hf
  simp only [List.cons.injEq, and_true] at hrets
  rw [hrets.1, hrets.2, this, cellRoot_mRoot]

/-- `guard_sound` for any continuation of `ret`. -/
theorem guardK_sound {σ : Val} {P : List Stmt} {gc : V} {f : String} {one N : V} {rest : List V}
    (h : guardOk P gc f one N rest = true) {kret : List E → Prop}
    (hall : ∀ s ∈ P, Stmt.Holds (coreProgram.Rel rd) rd σ s True kret) :
    1 + σ N ≠ 0 → coreProgram.Rel rd f (1 :: σ N :: rest.map σ) [] := by
  simp only [guardOk, Bool.and_eq_true] at h
  obtain ⟨⟨hc, ha⟩, h1⟩ := h
  have hat := atoms_of_flat hall
  have hcall := callIf_of_flat hall hc
  split at ha
  · rename_i p q hpq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
    obtain ⟨hp1, rfl⟩ := ha
    intro hne
    have hgc : σ gc = 1 + σ q := by rw [addOf_sound hpq hat, const_sound hp1 hat, word_one]
    have := hcall.2 (by rw [hgc]; exact hne)
    rwa [List.map_cons, List.map_cons, const_sound h1 hat, word_one] at this
  · exact absurd ha (by simp)

set_option maxRecDepth 100000 in
theorem word_g64 : word 27 0 = gen ^ 64 := by
  rw [word_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  congr 1

set_option maxRecDepth 100000 in
theorem word_g128 : word 325 0 = gen ^ 128 := by
  rw [word_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  congr 1

theorem list_sum_range (f : ℕ → E) : ∀ n, ((List.range n).map f).sum = ∑ e ∈ Finset.range n, f e
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f n,
      Finset.sum_range_succ]
    simp

end
end LeanVM.Guest.B1.Da
