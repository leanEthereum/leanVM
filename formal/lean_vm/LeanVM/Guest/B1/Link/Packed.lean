/-
  LeanVM.Guest.B1.Link.Packed

  The Statement's packed draw on the carried sponge.
-/

module

public import LeanVM.Guest.B1.Common.Run

/-!
# Packed draws

A packed draw (`samplesPacked`, `transcript.rs`'s `samples_packed`) right after a squeeze
permutes the capacity alone, eight challenges a permutation, the cells `0 .. 7` of its output
(`packedChallengeOf_cell`). `pkSqueeze p cap`: the `8 p` cells of `p` such permutations from the
capacity `cap`, and the capacity after them; `runsTo_samplePacked`: a packed draw of `n`
challenges, `8 (p - 1) < n ≤ 8 p`, from the carried capacity, is their first `n`.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- Cell `i` of a state, in the even layout, `0` past `13`. -/
def cellAt (S : KeccakState) (i : ℕ) : E := if h : i < 13 then cellsOfState S false ⟨i, h⟩ else 0

/-- **A packed challenge is a cell**: challenge `i < 8` of a packed draw is the state's cell `i`. -/
theorem packedChallengeOf_cell (S : KeccakState) {i : ℕ} (hi : i < 8) :
    packedChallengeOf S i = cellAt S i := by
  unfold cellAt
  simp only [show i < 13 by omega, ↓reduceDIte]
  interval_cases i <;> simp [packedChallengeOf, cellsOfState, cellLanes]

/-- A permutation of the capacity alone. -/
def pkPerm (cap : List E) : KeccakState := permOf (List.replicate 8 0 ++ cap)

/-- `p` permutations of the capacity alone: their cells `0 .. 7`, in order, and the capacity after. -/
def pkSqueeze : ℕ → List E → List E × List E
  | 0, cap => ([], cap)
  | p + 1, cap => ((List.range 8).map (cellAt (pkPerm cap)) ++ (pkSqueeze p (capOf (pkPerm cap))).1,
      (pkSqueeze p (capOf (pkPerm cap))).2)

theorem pkSqueeze_length : ∀ (p : ℕ) (cap : List E), (pkSqueeze p cap).1.length = 8 * p
  | 0, _ => rfl
  | p + 1, cap => by simp [pkSqueeze, pkSqueeze_length p]; ring

/-- The carried sponge with nothing waiting permutes the capacity alone. -/
theorem perm_empty {cap : List E} {sp : Sponge} (h : (⟨cap, []⟩ : Fs).Carries sp) :
    keccakF1600 (duplexInput sp) = pkPerm cap := by
  rw [perm_eq h, Fs.perm, rateOf_eq_cells [] (by simp)]
  rfl

theorem spc_step (f m : ℕ) (sp : Sponge) :
    squeezePackedChunks (m := Id) keccakF1600 (f + 1) sp (m + 1) =
      ((List.range (min 8 (m + 1))).map (packedChallengeOf (keccakF1600 (duplexInput sp))) ++
        (squeezePackedChunks (m := Id) keccakF1600 f ⟨keccakF1600 (duplexInput sp), [], sp.ground⟩
          (m + 1 - min 8 (m + 1))).1,
       (squeezePackedChunks (m := Id) keccakF1600 f ⟨keccakF1600 (duplexInput sp), [], sp.ground⟩
          (m + 1 - min 8 (m + 1))).2) := rfl

theorem spc_zero (f : ℕ) (sp : Sponge) : squeezePackedChunks (m := Id) keccakF1600 f sp 0 = ([], sp) := by
  cases f <;> rfl

/-- **The draw's permutations**: `8 (p - 1) < m ≤ 8 p` challenges from the carried capacity. -/
theorem spc_carried : ∀ (p : ℕ) (cap : List E) (sp : Sponge) (f m : ℕ), (⟨cap, []⟩ : Fs).Carries sp →
    p ≤ f → 8 * p - 8 < m → m ≤ 8 * p →
    ((squeezePackedChunks (m := Id) keccakF1600 f sp m).1 = (pkSqueeze p cap).1.take m ∧
      (⟨(pkSqueeze p cap).2, []⟩ : Fs).Carries (squeezePackedChunks (m := Id) keccakF1600 f sp m).2)
  | 0, cap, sp, f, m, h, _, _, hm => by
    obtain rfl : m = 0 := by omega
    rw [spc_zero]
    exact ⟨rfl, h⟩
  | p + 1, cap, sp, f + 1, m + 1, h, hf, hm1, hm2 => by
    rw [spc_step, perm_empty h]
    have hc1 : (⟨capOf (pkPerm cap), []⟩ : Fs).Carries ⟨pkPerm cap, [], sp.ground⟩ := ⟨rfl, rfl, h.2.2⟩
    have hrange : (List.range (min 8 (m + 1))).map (packedChallengeOf (pkPerm cap)) =
        (List.range (min 8 (m + 1))).map (cellAt (pkPerm cap)) :=
      List.map_congr_left fun i hi ↦ packedChallengeOf_cell _ (by simp at hi; omega)
    rw [hrange]
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · rw [show m + 1 - min 8 (m + 1) = 0 by omega, spc_zero]
      refine ⟨?_, by simpa [pkSqueeze] using hc1⟩
      rw [show min 8 (m + 1) = m + 1 by omega]
      simp only [pkSqueeze, List.append_nil]
      rw [← List.map_take, List.take_range, show min (m + 1) 8 = m + 1 by omega]
    · obtain ⟨ih1, ih2⟩ := spc_carried p (capOf (pkPerm cap)) _ f (m + 1 - 8) hc1 (by omega)
        (by omega) (by omega)
      rw [show min 8 (m + 1) = 8 by omega]
      refine ⟨?_, ih2⟩
      rw [ih1, pkSqueeze, show m + 1 = 8 + (m + 1 - 8) by omega, List.take_add]
      simp

/-- **A packed draw from the carried capacity** of `n` challenges, `8 (p - 1) < n ≤ 8 p`. -/
theorem runsTo_samplePacked (cap : List E) {n p : ℕ} (hn1 : 8 * p - 8 < n) (hn2 : n ≤ 8 * p) :
    RunsTo (VerifierProgram.sampleChallengesPacked n) ⟨cap, []⟩ []
      ((pkSqueeze p cap).1.take n) ⟨(pkSqueeze p cap).2, []⟩ := by
  intro sp hs rest os roots
  have hp : p ≤ n := by omega
  obtain ⟨e1, e2⟩ := spc_carried p cap sp n n hs hp hn1 hn2
  refine ⟨_, e2, ?_⟩
  have hg := hs.2.2
  rcases n with _ | n
  · simp only [VerifierProgram.sampleChallengesPacked, runId, List.nil_append]
    obtain ⟨st, pd, gr⟩ := sp
    simp only at hg
    subst hg
    simp only [Compile.runWithHash, Compile.samplesPacked] at e1 e2 ⊢
    rw [← e1]
    rfl
  · obtain ⟨st, pd, gr⟩ := sp
    simp only at hg
    subst hg
    show some (_, _) = some (_, _)
    simp only [Compile.samplesPacked, List.length_nil, Nat.sub_zero] at e1 e2 ⊢
    rw [← e1]
    rfl

end
end LeanVM.Guest.B1.Link
