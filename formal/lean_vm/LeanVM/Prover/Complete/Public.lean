/-
  LeanVM.Prover.Complete.Public

  Binding the public input: the honest script receives the challenge, and the verifier's claims on
  the memory columns hold of the honest columns.
-/

module

public import LeanVM.Prover.Complete.Prefix
import LeanVM.Protocol.Relation.Placement
import LeanVM.Parameters.Field

/-!
# Binding the public input

`bindPublicInput` (`Statement/Verifier/Lib.lean`) samples a challenge `c` and claims, for each
memory limb, the line through the public input's two words at `c` on the memory column at
`(c, 0, …, 0)`. The honest witness's memory columns are the memory's limbs (`colsOf`) and its
first two words the public input (`boundaryOK`), and the extension of a column at `(c, 0, …, 0)`
is the line through its first two entries (`mleA_cons_zeros`): `wins_public`.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Extraction LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash

variable {B : ℕ}

/-! ## The extension at `(c, 0, …, 0)` -/

theorem size_foldPairsA (r : E) (t : Array E) : (foldPairsA r t).size = t.size / 2 := by
  simp [foldPairsA]

theorem getD_foldPairsA_zero (r : E) {t : Array E} (ht : 2 ≤ t.size) :
    (foldPairsA r t).getD 0 0 = t.getD 0 0 * (1 + r) + t.getD 1 0 * r := by
  have h : 0 < t.size / 2 := by omega
  simp [foldPairsA, Array.getD_eq_getD_getElem?, h,
    Array.getElem?_eq_getElem (show 0 < t.size by omega),
    Array.getElem?_eq_getElem (show 1 < t.size by omega)]

/-- Folding at zeros keeps the first entry, on a table of `2^k` entries or more. -/
theorem getD_foldl_zeros : ∀ (k : ℕ) (t : Array E), 2 ^ k ≤ t.size →
    ((List.replicate k (0 : E)).foldl (fun cur r ↦ foldPairsA r cur) t).getD 0 0 = t.getD 0 0
  | 0, t, _ => rfl
  | k + 1, t, ht => by
    rw [List.replicate_succ, List.foldl_cons]
    have h2 : 2 ≤ t.size := le_trans (by
      have := Nat.one_le_two_pow (n := k); rw [pow_succ]; omega) ht
    rw [getD_foldl_zeros k _ (by rw [size_foldPairsA, pow_succ] at *; omega),
      getD_foldPairsA_zero 0 h2]
    simp

/-- **The extension at `(c, 0, …, 0)`** is the line through the first two entries. -/
theorem mleA_cons_zeros (c : E) (n : ℕ) {t : Array E} (ht : 2 ^ (n + 1) ≤ t.size) :
    mleA t (c :: List.replicate n 0) = t.getD 0 0 * (1 + c) + t.getD 1 0 * c := by
  have h2 : 2 ≤ t.size := le_trans (by
    have := Nat.one_le_two_pow (n := n); rw [pow_succ]; omega) ht
  unfold mleA
  rw [List.foldl_cons, getD_foldl_zeros n _ (by rw [size_foldPairsA]; rw [pow_succ] at ht; omega),
    getD_foldPairsA_zero c h2]

theorem multilinearEval_pair (a b c : E) : multilinearEval [a, b] [c] = a * (1 + c) + b * c := by
  simp [multilinearEval, foldPairs]

/-! ## The memory columns -/

/-- The honest memory columns: limb `l` of every memory word. -/
theorem cols_memory {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    {W : Witness} (hW : witness? prog input t = some W) :
    W.cols.getD memory0 #[] = Array.ofFn (n := 2 ^ t.logMemorySize) (fun x ↦ (t.memory x).limb 0) ∧
      W.cols.getD memory1 #[] =
        Array.ofFn (n := 2 ^ t.logMemorySize) (fun x ↦ (t.memory x).limb 1) := by
  obtain ⟨-, steps, -, -, -, -, -, hcols, -⟩ := witness?_spec hW
  rw [hcols]
  have h0 : memory0 < nColumns := by decide
  have h1 : (1 : ℕ) < nColumns := by decide
  refine ⟨?_, ?_⟩
  · simp [colsOf, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, h0]
  · simp [colsOf, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, h1, memory0, memory1]

/-- **Binding the public input.** The honest script receives the challenge; the verifier's claims
on the memory columns hold of the honest columns. -/
theorem wins_public {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    {W : Witness} (hW : witness? prog input t = some W) (g : Bool) (cs : List Committed) :
    Wins B (fun a b g' cs' ↦ a = b ∧ g' = false ∧ cs' = cs ∧ (∀ c ∈ a, c.HoldsIn W.cols) ∧
        (∀ c ∈ a, ∀ p, W.layout.placements.getD c.column none = some p →
          c.point.length = p.variableCount) ∧ a.length = 2)
      (bindPublicInput W.layout (publicInputDigest input))
      (Script.alongside (bindPublicInput W.layout (publicInputDigest input)) Script.sampleE)
      g cs := by
  obtain ⟨hb, steps, -, -, hl, -⟩ := witness?_spec hW
  obtain ⟨hlm, -⟩ := buildLayout_spec hl
  -- the memory's placement
  have hsome := placement_isSome hl (c := memory0) (by decide) (by decide)
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
  have hvar : p.variableCount = t.logMemorySize := by
    rw [placement_variableCount hl hp, (columnKappas_memory _ _).1, hlm]
  -- the boundary
  unfold boundaryOK at hb
  split at hb
  · rename_i hκ
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨hw0, hw1⟩ := hb
    have hw0' : t.memory 0 = input.word0 := by rw [← hw0]; rfl
    have hol : ∀ a : K, K.ofLane a.lane = a := fun _ ↦ rfl
    obtain ⟨hc0, hc1⟩ := cols_memory hW
    have hκ1 : 1 ≤ t.logMemorySize := hκ.1
    obtain ⟨n, hn⟩ : ∃ n, t.logMemorySize = n + 1 := ⟨t.logMemorySize - 1, by omega⟩
    simp only [bindPublicInput, VerifierProgram.bind_eq, VerifierProgram.sampleChallenge,
      Script.sampleE]
    refine Wins.sample fun c ↦ ?_
    simp only [VerifierProgram.ret_bind, hp, LeanVM.Protocol.Verifier.liftOption]
    refine ⟨rfl, rfl, rfl, fun cl hcl ↦ ?_, fun cl hcl q hq ↦ ?_, rfl⟩
    rotate_left
    · simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hcl
      have hq' : q.variableCount = t.logMemorySize := by
        rw [placement_variableCount hl hq]
        rcases hcl with rfl | rfl
        · rw [(columnKappas_memory _ _).1, hlm]
        · rw [(columnKappas_memory _ _).2.1, hlm]
      rcases hcl with rfl | rfl <;> simp [hq', hvar] <;> omega
    simp only [List.zipWith_cons_cons, List.zipWith_nil_right, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hcl
    rcases hcl with rfl | rfl
    · simp only [ColumnClaim.HoldsIn, mleK, hc0, multilinearEval_pair, hvar, hn,
        Nat.add_sub_cancel]
      rw [mleA_cons_zeros c n (by simp [hn])]
      simp [Array.getD_eq_getD_getElem?, hn, hw0', hw1, hol, PublicInput.word0, PublicInput.word1,
        publicInputDigest, digestHalves]
    · simp only [ColumnClaim.HoldsIn, mleK, hc1, multilinearEval_pair, hvar, hn,
        Nat.add_sub_cancel]
      rw [mleA_cons_zeros c n (by simp [hn])]
      simp [Array.getD_eq_getD_getElem?, hn, hw0', hw1, hol, PublicInput.word0, PublicInput.word1,
        publicInputDigest, digestHalves]
  · cases hb

end LeanVM.Prover

end
