/-
  LeanVM.Protocol.Relation.Link.GroupLinksSplit

  The program's split and `index_mle` at a Boolean point of the instructions.
-/

module

public import LeanVM.Protocol.Relation.Link.IdxDeg
public import LeanVM.Protocol.Relation.Link.GroupCube
import LeanVM.Parameters.Field

/-!
# The program's split at an instruction

At the Boolean point of instruction `k` (`boolL`), the equality weights select `k`:

* `lk_splitAt_bool`: `Bytecode::split` (`splitAt`) holds one for the instruction's opcode `F`
  (`opcodeOf` of its slot `3`, if at most `OP_KECCAK`), its operand slots `4 ≤ s < 2^BYTECODE_SLOT_BITS`
  under `F`, and `g^k` times those that `pc` lists, zero elsewhere;
* `indexMle_boolL`: `index_mle` there is `g^k`.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Link LeanVM.Protocol.Hotwire Finset

@[expose] public section

theorem lks_powersFrom_getD (acc base : E) : ∀ (n b : ℕ), b < n →
    (powersFrom acc base n).getD b 0 = acc * base ^ b
  | n + 1, 0, _ => by simp [powersFrom]
  | n + 1, b + 1, h => by
    rw [powersFrom, List.getD_cons_succ, lks_powersFrom_getD _ base n b (by omega), pow_succ]
    ring

theorem lks_list_sum (l : List E) : l.sum = ∑ i ∈ range l.length, l.getD i 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.sum_cons, ih, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- The program's rows at the Boolean point of instruction `k` select row `k`. -/
theorem lks_sumE_rows {lb k : ℕ} (hk : k < 2 ^ lb) (G : (E × E) × ℕ → E)
    (hG : ∀ gk j, G ((0, gk), j) = 0) :
    sumE ((((eqKernel (boolL lb k)).zip (powers gen (2 ^ (boolL lb k).length))).zipIdx).map G) =
      G ((1, gpow k), k) := by
  have hl : (eqKernel (boolL lb k)).length = 2 ^ lb := by rw [eqKernel_length, length_boolL]
  have hp : (powers gen (2 ^ lb)).length = 2 ^ lb := IdxDeg.length_powersFrom _ _ _
  rw [length_boolL, sumE, ← List.sum_eq_foldl, lks_list_sum, List.length_map, List.length_zipIdx,
    List.length_zip, hl, hp, min_self, sum_eq_single k]
  · rw [IdxDeg.getD_map_zipIdx_zip _ _ (by rw [hl]; exact hk) (by rw [hp]; exact hk), eqKernel_boolL hk,
      ite_eq_left rfl, powers, lks_powersFrom_getD _ _ _ _ hk, one_mul, gpow]
  · intro j hj hjk
    rw [IdxDeg.getD_map_zipIdx_zip _ _ (by rw [hl]; exact mem_range.mp hj) (by rw [hp]; exact mem_range.mp hj),
      eqKernel_boolL hk, ite_eq_right hjk, hG]
  · intro h
    exact absurd (mem_range.mpr hk) h

/-- **The program's split at instruction `k`**: the opcode's count, the operand slots and those read
times `pc`, for a program of `2^lb` instructions. -/
theorem lk_splitAt_bool {bytecode : List K} {lb k : ℕ} (hn : bytecode.length >>> bytecodeSlotBits = 2 ^ lb)
    (hk : k < 2 ^ lb) (pc : List (ℕ × ℕ)) (F s : ℕ) :
    let sp := splitAt bytecode (boolL lb k) pc
    let op := opcodeOf (bytecode.getD (3 * 2 ^ lb + k) 0)
    sp.count.getD F 0 = (if F ≤ opKeccak ∧ op = F then 1 else 0) ∧
    (sp.slots.getD F []).getD s 0 =
      (if F ≤ opKeccak ∧ op = F ∧ 4 ≤ s ∧ s < 2 ^ bytecodeSlotBits then
        ofK (bytecode.getD (s * 2 ^ lb + k) 0) else 0) ∧
    (sp.pc.getD F []).getD s 0 =
      (if F ≤ opKeccak ∧ op = F ∧ 4 ≤ s ∧ s < 2 ^ bytecodeSlotBits ∧ pc.contains (F, s) then
        gpow k * ofK (bytecode.getD (s * 2 ^ lb + k) 0) else 0) := by
  dsimp only
  by_cases hF : F ≤ opKeccak
  · have hF' : F < opKeccak + 1 := Nat.lt_succ_of_le hF
    refine ⟨?_, ?_, ?_⟩
    · unfold splitAt
      dsimp only
      rw [IdxPoly.getD_map_range, ite_eq_left hF', lks_sumE_rows hk]
      · dsimp only
        rw [hn]
        by_cases ho : opcodeOf (bytecode.getD (3 * 2 ^ lb + k) 0) = F
        · rw [ite_eq_left ho, ite_eq_left ⟨hF, ho⟩]
        · rw [ite_eq_right ho, ite_eq_right (fun h ↦ ho h.2)]
      · intro gk j
        simp
    · unfold splitAt
      dsimp only
      rw [IdxPoly.getD_map_range, ite_eq_left hF', IdxPoly.getD_map_range]
      by_cases hs : s < 2 ^ bytecodeSlotBits
      · rw [ite_eq_left hs]
        by_cases h4 : 4 ≤ s
        · rw [ite_eq_left h4, lks_sumE_rows hk]
          · dsimp only
            rw [hn]
            by_cases ho : opcodeOf (bytecode.getD (3 * 2 ^ lb + k) 0) = F
            · rw [ite_eq_left ho, ite_eq_left ⟨hF, ho, h4, hs⟩, one_mul]
            · rw [ite_eq_right ho, ite_eq_right (fun h ↦ ho h.2.1)]
          · intro gk j
            simp
        · rw [ite_eq_right h4, ite_eq_right (fun h ↦ h4 h.2.2.1)]
      · rw [ite_eq_right hs, ite_eq_right (fun h ↦ hs h.2.2.2)]
    · unfold splitAt
      dsimp only
      rw [IdxPoly.getD_map_range, ite_eq_left hF', IdxPoly.getD_map_range]
      by_cases hs : s < 2 ^ bytecodeSlotBits
      · rw [ite_eq_left hs]
        by_cases h4 : 4 ≤ s ∧ pc.contains (F, s) = true
        · rw [ite_eq_left h4, lks_sumE_rows hk]
          · dsimp only
            rw [hn]
            by_cases ho : opcodeOf (bytecode.getD (3 * 2 ^ lb + k) 0) = F
            · rw [ite_eq_left ho, ite_eq_left ⟨hF, ho, h4.1, hs, h4.2⟩, one_mul]
            · rw [ite_eq_right ho, ite_eq_right (fun h ↦ ho h.2.1)]
          · intro gk j
            simp
        · rw [ite_eq_right h4, ite_eq_right (fun h ↦ h4 ⟨h.2.2.1, h.2.2.2.2⟩)]
      · rw [ite_eq_right hs, ite_eq_right (fun h ↦ hs h.2.2.2.1)]
  · have hF' : ¬ F < opKeccak + 1 := by omega
    refine ⟨?_, ?_, ?_⟩ <;> unfold splitAt <;> dsimp only <;>
      rw [IdxPoly.getD_map_range, ite_eq_right hF'] <;> simp [hF]

theorem lks_indexMleFrom_boolL (g : E) : ∀ (n j : ℕ) (acc : E), j < 2 ^ n →
    indexMleFrom g (boolL n j) acc = acc * g ^ j
  | 0, j, acc, hj => by
    obtain rfl : j = 0 := by simpa using hj
    simp [boolL_zero, indexMleFrom]
  | n + 1, j, acc, hj => by
    obtain ⟨c, m, hc, rfl⟩ : ∃ c m, c < 2 ∧ j = c + 2 * m :=
      ⟨j % 2, j / 2, Nat.mod_lt _ (by norm_num), (Nat.mod_add_div j 2).symm⟩
    rw [boolL_succ n c m hc, indexMleFrom,
      lks_indexMleFrom_boolL (g ^ 2) n m _ (by rw [pow_succ] at hj; omega), pow_add, pow_mul]
    rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
    · rw [ite_eq_right (by norm_num)]
      ring
    · rw [ite_eq_left rfl]
      have h2 : (1 : E) + 1 = 0 := CharTwo.add_self_eq_zero 1
      linear_combination (acc * (g ^ 2) ^ m) * h2

/-- **`index_mle` at instruction `k`'s Boolean point** is `g^k`. -/
theorem indexMle_boolL {n j : ℕ} (hj : j < 2 ^ n) : indexMle (boolL n j) = gpow j := by
  rw [indexMle, lks_indexMleFrom_boolL gen n j 1 hj, one_mul, gpow]

end

end LeanVM.Protocol.Relation

/-! The split's theorems use Lean's three standard axioms only. -/

/-- info: 'LeanVM.Protocol.Relation.lk_splitAt_bool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.lk_splitAt_bool

/-- info: 'LeanVM.Protocol.Relation.indexMle_boolL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.indexMle_boolL
