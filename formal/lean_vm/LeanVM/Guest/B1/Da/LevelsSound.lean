/-
  LeanVM.Guest.B1.Da.LevelsSound

  `da_levels`' specializations compute their meanings (TRIAGE G #92).
-/

module

public import LeanVM.Guest.B1.Da.LevelsChk0
public import LeanVM.Guest.B1.Da.LevelsChk1
public import LeanVM.Guest.B1.Da.LevelsChk2
public import LeanVM.Guest.B1.Da.LevelsChk3
public import LeanVM.Guest.B1.Da.LevelsChk4
public import LeanVM.Guest.B1.Da.LevelsChk5
public import LeanVM.Guest.B1.Da.LevelsChk6

/-!
# `da_levels`, sound

`dl_sound`: a checked entry of `dlTab` computes `MeaningDaLevels k`: its level loops (`lvl_step`,
`loop_sound`) make every node the digest of the previous level's pair (`levels_root`), the leaves
read by level `0` (or the root's loads at `k = 0`). `da_levels_holds`: the eleven entries are
checked (`LevelsChk*`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader}

theorem ptr_pow (tree : E) (a c p : ℕ) : tree * gen ^ a * (gen ^ p) ^ c = tree * gen ^ (a + c * p) := by
  rw [← pow_mul, mul_assoc, ← pow_add, mul_comm p c]

/-- Reading through `tree·g^a` at `i` is reading `tree` at `a + i`. -/
theorem shift_load {tree v : E} {a i : ℕ} (h : LoadHolds rd (tree * gen ^ a) i v) :
    LoadHolds rd tree (a + i) v ∧ memAt rd tree (a + i) = v ∧ memAt rd (tree * gen ^ a) i = v :=
  ⟨(loadHolds_mul_gen_pow rd _ _ _ _).mp h, memAt_of_load ((loadHolds_mul_gen_pow rd _ _ _ _).mp h),
    memAt_of_load h⟩

theorem pairCells_range (f : ℕ → E) : ∀ n,
    pairCells ((List.range n).map fun i => (f (2 * i), f (2 * i + 1))) = (List.range (2 * n)).map f
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, pairCells, List.flatMap_append, ← pairCells,
      pairCells_range f n, show 2 * (n + 1) = 2 * n + 2 by ring, List.range_add, List.map_append,
      List.map_map]
    simp [List.range_succ]

theorem off_zero (k : ℕ) : off k 0 = 0 := by simp [off]

theorem off_self (k : ℕ) : off k k = 4 * 2 ^ k - 4 := by simp [off]

theorem off_lt {k lvl : ℕ} (hk : k ≤ 10) : off k lvl < 2 ^ 64 := by
  have : 2 ^ k ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) hk
  unfold off; omega

/-- **A checked specialization computes its meaning.** -/
theorem dl_sound {k : ℕ} (hk : k ≤ 10) (hok : dlEntryOk k = true) :
    ∀ (rd : Reader) (args rets : List E),
      coreProgram.Rel rd (daLevelsName k) args rets → MeaningDaLevels k rd args rets := by
  unfold dlEntryOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨-, hname⟩, hidx⟩, hlen⟩, hdl⟩, hloops⟩ := hok
  intro rd args rets hrel
  rw [← hname] at hrel
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem (find_of_idx hidx hlen) _ _).mp hrel
  unfold dlOk at hdl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hdl
  obtain ⟨⟨hparams, -⟩, hdl⟩ := hdl
  split at hdl
  · rename_i P vs hsr
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hdl
    obtain ⟨⟨⟨⟨rfl, hflat⟩, hguards⟩, hr0⟩, hr1⟩ := hdl
    rw [splitRet_eq hsr, holdsList_append] at hb
    obtain ⟨hall, hret⟩ := holdsList_flat P (List.all_eq_true.mpr hflat) _ _ hb
    simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hret
    rw [hparams] at hpar
    subst hpar
    have hat := atoms_of_flat hall
    have h2k : 2 ^ k ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) hk
    -- the levels
    have hlvl : ∀ lvl < k, ∀ p < 2 ^ (k - lvl - 1),
        LvlStep rd (σ (.n 0)) (off k lvl) (off k (lvl + 1)) (gen ^ p) := by
      intro lvl hl
      have hlo := hloops lvl hl
      unfold loopOk at hlo
      split at hlo
      · rename_i j hj
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hlo
        have hm : 2 ^ (k - lvl - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact loop_sound (ps := [gen ^ 2 ^ (k - lvl - 1), σ (.n 0)])
          (N := gen ^ 2 ^ (k - lvl - 1)) (m := 2 ^ (k - lvl - 1)) (by unfold ordG; omega) rfl
          (fun y hy => by
            obtain ⟨h1, h2⟩ := lvl_step hj hlo.1 hlo.2 (off_lt hk) (off_lt hk) hy
            exact ⟨h1 _ _ rfl, h2⟩)
          (fun hne => by simpa using guardPow_sound (hguards lvl hl) hall (by omega) hne)
      · exact absurd hlo (by simp)
    -- the nodes
    have hnode : ∀ j < k, ∀ p < 2 ^ (k - j - 1), node rd (σ (.n 0)) k (j + 1) p =
        nodeCells (node rd (σ (.n 0)) k j (2 * p)) (node rd (σ (.n 0)) k j (2 * p + 1)) := by
      intro j hj p hp
      obtain ⟨hld, -, h0, h1⟩ := hlvl j hj p hp
      rw [ptr_pow] at hld h0 h1
      rw [ptr_pow] at h0 h1
      have m : ∀ i < 4, memAt rd (σ (.n 0) * gen ^ (off k j + 4 * p)) i =
          memAt rd (σ (.n 0)) (off k j + 4 * p + i) := fun i hi => by
        obtain ⟨-, e1, e2⟩ := shift_load (hld i hi)
        rw [e2, ← e1]
      obtain ⟨-, e0, -⟩ := shift_load h0
      obtain ⟨-, e1, -⟩ := shift_load h1
      rw [m 0 (by omega), m 1 (by omega), m 2 (by omega), m 3 (by omega)] at e0 e1
      simp only [add_zero] at e0
      simp only [node]
      rw [e0, e1]
      have a0 : off k j + 2 * (2 * p) = off k j + 4 * p + 0 := by ring
      have a1 : off k j + 2 * (2 * p) + 1 = off k j + 4 * p + 1 := by ring
      have a2 : off k j + 2 * (2 * p + 1) = off k j + 4 * p + 2 := by ring
      have a3 : off k j + 2 * (2 * p + 1) + 1 = off k j + 4 * p + 3 := by ring
      rw [a1, a3, a0, a2]
      simp only [add_zero]
    have hroot := levels_root hnode
    -- the leaves
    have hleaves : (List.range (2 ^ k)).map (node rd (σ (.n 0)) k 0) =
        (List.range (2 ^ k)).map fun i =>
          (memAt rd (σ (.n 0)) (2 * i), memAt rd (σ (.n 0)) (2 * i + 1)) := by
      simp [node, off_zero]
    have hread : ∀ c < 2 * 2 ^ k, LoadHolds rd (σ (.n 0)) c (memAt rd (σ (.n 0)) c) ∧
        (0 < k → IsCanonical128 (memAt rd (σ (.n 0)) c)) := by
      intro c hc
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · have l0 := load_sound hr0 hat
        have l1 := load_sound hr1 hat
        simp only [pow_zero, mul_one] at l0 l1
        refine ⟨?_, fun h => absurd h (by omega)⟩
        rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
        · rw [memAt_of_load l0]; exact l0
        · rw [memAt_of_load l1]; exact l1
      · obtain ⟨hld, hcan, -, -⟩ := hlvl 0 hk0 (c / 4) (by
          have : 2 ^ k = 2 * 2 ^ (k - 0 - 1) := by rw [← pow_succ']; congr 1; omega
          omega)
        rw [ptr_pow, off_zero, zero_add] at hld
        rw [ptr_pow, off_zero, zero_add] at hcan
        obtain ⟨hl, e1, e2⟩ := shift_load (hld (c % 4) (by omega))
        rw [show 4 * (c / 4) + c % 4 = c by omega] at hl e1
        refine ⟨by rw [e1]; exact hl, fun _ => ?_⟩
        have := hcan _ (List.mem_map.mpr ⟨c % 4, List.mem_range.mpr (by omega), rfl⟩)
        rw [← e1] at this
        exact this
    refine ⟨(List.range (2 ^ k)).map (node rd (σ (.n 0)) k 0), by simp, ?_, ?_, ?_⟩
    · rw [hleaves, pairCells_range (memAt rd (σ (.n 0)))]
      intro c hc
      simp only [List.length_map, List.length_range] at hc
      rw [List.getElem_map, List.getElem_range]
      exact (hread c hc).1
    · intro hk0 x hx
      rw [hleaves, pairCells_range (memAt rd (σ (.n 0)))] at hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact (hread c (List.mem_range.mp hc)).2 hk0
    · rw [← hret, hroot]
      simp only [node, off_self, mul_zero, add_zero]
      rw [show 4 * 2 ^ k - 4 + 1 = 4 * 2 ^ k - 3 by have := Nat.one_le_two_pow (n := k); omega,
        memAt_of_load (load_sound hr0 hat), memAt_of_load (load_sound hr1 hat)]
  · exact absurd hdl (by simp)

/-- **`da_levels`' specializations compute their meanings.** -/
theorem da_levels_holds : da_levels_sound_Spec := by
  intro k hk
  interval_cases k
  · exact dl_sound (by norm_num) dl_ok0
  · exact dl_sound (by norm_num) dl_ok1
  · exact dl_sound (by norm_num) dl_ok2
  · exact dl_sound (by norm_num) dl_ok3
  · exact dl_sound (by norm_num) dl_ok4
  · exact dl_sound (by norm_num) dl_ok5
  · exact dl_sound (by norm_num) dl_ok6
  · exact dl_sound (by norm_num) dl_ok7
  · exact dl_sound (by norm_num) dl_ok8
  · exact dl_sound (by norm_num) dl_ok9
  · exact dl_sound (by norm_num) dl_ok10

end
end LeanVM.Guest.B1.Da
