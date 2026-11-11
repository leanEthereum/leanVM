/-
  LeanVM.Guest.B1.Whir.CLvLam

  A non-final level's batching challenge honestly on f128: the nonce read and permuted, the
  grind's check, `λ` and `1/λ`.
-/

module

public import LeanVM.Guest.B1.Whir.CLvSq

/-!
# The batching challenge, honestly (G:1632-1641)

`osLam_complete`: the batching nonce `n2` at the cursor; its permutation `lamS cap n2` on the
carried capacity (`fs_absorb_nonce`); the grind's check on its cell `1`; `λ` its cell `0` and
`1/λ` (`λ ≠ 0`); the zero run allocated if it was not.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {H : CallRel → Reader → Prop}

/-- The batching nonce's permutation on the capacity `cap`. -/
def lamS (cap : List E) (n2 : E) : KeccakState := (⟨cap, []⟩ : Fs).nonceState n2

/-- The zero run's values. -/
def padVals : List E := [word 1 0, word 0 0, word 0 0, word 0 0, word 0 0]

/-- **The zero run**, allocated if it was not: its cells after the first zero. -/
theorem osPad_blk (σ : Val) (pad : Option ℕ) (k : ℕ) (hp : ∀ C rd, H C rd → PadOk σ pad)
    (hpb : ∀ p, pad = some p → p + 4 < k) :
    BlkA H σ k (osPad pad k).2.2 (osPad pad k).1 (fun σ' ↦ PadOk σ' (some (osPad pad k).2.1)) := by
  cases pad with
  | some q =>
    refine ⟨fun _ ↦ 0, fun C rd hH σ' ha _ ↦ ⟨allOk_nil, fun p hp ↦ ?_⟩⟩
    simp only [osPad, Option.some.injEq] at hp
    subst hp
    have hb := hpb q rfl
    obtain ⟨z1, z2, z3, z4⟩ := hp C rd hH q rfl
    rw [ha _ (by omega), ha _ (by omega), ha _ (by omega), ha _ (by omega)]
    exact ⟨z1, z2, z3, z4⟩
  | none =>
    refine ⟨lstF k padVals, fun C rd hH σ' ha hr ↦ ?_⟩
    have v : ∀ j < 5, σ' (.n (k + j)) = padVals.getD j 0 := fun j hj ↦
      lstF_at hr (by simp [osPad, padVals]) j (by simp [padVals]; omega)
    have v0 := v 0 (by omega)
    have v1 := v 1 (by omega)
    have v2 := v 2 (by omega)
    have v3 := v 3 (by omega)
    have v4 := v 4 (by omega)
    simp only [padVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero,
      word_zero] at v0 v1 v2 v3 v4
    refine ⟨?_, fun p hp ↦ ?_⟩
    · simp only [osPad, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_const, osCst, v0, v1, v2,
        v3, v4, word_zero]
    · simp only [osPad, Option.some.injEq] at hp
      subst hp
      exact ⟨v1, v2, v3, v4⟩

theorem osPad_next (pad : Option ℕ) (k : ℕ) : k ≤ (osPad pad k).2.2 := by
  cases pad <;> simp [osPad]

theorem osPad_ptr (pad : Option ℕ) (k : ℕ) (hpb : ∀ p, pad = some p → p + 4 < k) :
    (osPad pad k).2.1 + 4 < (osPad pad k).2.2 ∨ ((osPad pad k).2.1 + 4 < k) := by
  cases pad with
  | some q => right; exact hpb q rfl
  | none => left; simp [osPad]

/-- The values after the batching nonce's permutation: `λ`, one and `1/λ`. -/
def lamVals (S : KeccakState) : List E := [rdCell S 0, word 1 0, (rdCell S 0)⁻¹]

/-- **The batching challenge, honestly** (G:1632-1641). -/
theorem osLam_complete {st : OsSt} (σ : Val) (hsf : st.Sf) (hok : ∀ C rd, H C rd → st.Ok σ)
    (hco1 : st.co + 1 < u128Bound) (n2 : E) (hlam : rdCell (lamS (st.fsv σ) n2) 0 ≠ 0)
    (hn : ∀ C rd, H C rd → LoadHolds rd (st.cur σ) 0 n2)
    (hg : ∀ C rd, H C rd → C ("grind_check__L" ++ natStr batchGrind)
      [rdCell (lamS (st.fsv σ) n2) 1, σ (.n osTabs)] []) :
    BlkA H σ st.k (osLam st).2.k (osLam st).1 (fun σ' ↦
      OsStep σ σ' st (osLam st).2 ∧
      (osLam st).2.F σ' = ⟨capOf (lamS (st.fsv σ) n2), []⟩ ∧
      σ' (.n (osLam st).2.lam) = rdCell (lamS (st.fsv σ) n2) 0 ∧
      σ' (.n (osLam st).2.lamInv) = (rdCell (lamS (st.fsv σ) n2) 0)⁻¹ ∧
      (osLam st).2.cur σ' = st.cur σ * gen ∧ (osLam st).2.claim = st.claim ∧
      (osLam st).2.ys = st.ys ∧ (osLam st).2.sent = st.sent ∧ (osLam st).2.batched = st.batched) := by
  set k := st.k with hk
  set cap := st.fsv σ with hcap
  set S := lamS cap n2 with hS
  set p := (osPad st.pad (k + 3)).2.1 with hp
  set j := (osPad st.pad (k + 3)).2.2 with hj
  have k36 : 36 ≤ k := hsf.k
  have kj : k + 3 ≤ j := osPad_next _ _
  have hpj : p + 4 < j := by
    rcases osPad_ptr st.pad (k + 3) (fun q hq ↦ by have := hsf.padB q hq; omega) with h | h <;> omega
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fs_five st hsf.fs
  have hfb : ∀ f ∈ st.fs, f < k := hsf.below.fs
  have hc : cap = [σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)] := by
    simp [hcap, OsSt.fsv, hf]
  -- the nonce
  have b1 : BlkA H σ k (k + 3) [osLd k st.cb st.co, osCp (k + 1) k, osCst (k + 2) (word 0 4)]
      (fun σ' ↦ σ' (.n (k + 1)) = n2 ∧ σ' (.n (k + 2)) = word 0 4) := by
    refine ⟨lstF k [n2, n2, word 0 4], fun C rd hH σ' ha hr ↦ ?_⟩
    have v : ∀ i < 3, σ' (.n (k + i)) = [n2, n2, word 0 4].getD i 0 := fun i hi ↦
      lstF_at hr (by simp) i (by simp; omega)
    have v0 := v 0 (by omega)
    have v1 := v 1 (by omega)
    have v2 := v 2 (by omega)
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2
    refine ⟨?_, v1, v2⟩
    have l0 := hn C rd hH
    rw [OsSt.cur, loadHolds_mul_gen_pow, Nat.add_zero] at l0
    simp only [osLd, osCp, osCst, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load,
      holds_copy, holds_const, v0, v1, v2, ha _ hsf.below.cb]
    exact l0
  -- the zero run
  have b2 := BlkA.seq (H := H) (show k ≤ k + 3 by omega) kj b1 (B := (osPad st.pad (k + 3)).1)
    (OutB := fun σ' ↦ PadOk σ' (some p)) fun σ1 ha1 _ ↦
      osPad_blk σ1 st.pad (k + 3) (fun C rd hH ↦ ((hok C rd hH).agree ha1).pad)
        (fun q hq ↦ by have := hsf.padB q hq; omega)
  -- the permutation
  have b3 := BlkA.seq (H := H) (show k ≤ j by omega) (show j ≤ j + 13 by omega) b2
    (B := [osKeccak ([k + 1, k + 2, p + 1, p + 1, p + 1, p + 2, p + 3, p + 4] ++ st.fs) j])
    (OutB := fun σ' ↦ ∀ i < 13, σ' (.n (j + i)) = rdCell S i) fun σ1 ha1 ho1 ↦ by
      refine (keccak_blk ⟨cap, [(n2, dsPowNonce)]⟩ (by simp) (by simp [hf]) (fun i hi ↦ ?_)
        (fun C rd hH ↦ ?_)).mono fun σ' h i hi ↦ by
          rw [h i hi, hS, lamS, Fs.nonceState]
          simp [Fs.absorb, rateScalars]
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hi
        all_goals first | omega | (have := hfb i hi; omega)
      · obtain ⟨⟨e1, e2⟩, hpad⟩ := ho1 C rd hH
        obtain ⟨z1, z2, z3, z4⟩ := hpad p rfl
        have v : ∀ f ∈ st.fs, σ1 (.n f) = σ (.n f) := fun f hf' ↦ ha1 f (hfb f hf')
        rw [hf] at v
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at v
        simp only [List.map_append, List.map_cons, List.map_nil, hf, e1, e2, z1, z2, z3, z4, v.1,
          v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2, hc]
        simp [pendCells, Keccak.scalarCells, dsPowNonce, word]
        rfl
  -- the grind
  have b4 := BlkA.seq (H := H) (show k ≤ j + 13 by omega) (show j + 13 ≤ j + 13 from le_rfl) b3
    (B := [.call ("grind_check__L" ++ natStr batchGrind) ([j + 1, osTabs].map V.n) []])
    (OutB := fun σ' ↦ ([j + 1, osTabs].map V.n).map σ' = [rdCell S 1, σ (.n osTabs)])
    fun σ1 ha1 ho1 ↦ by
      have h := call0_blk (H := H) (σ := σ1) (k := j + 13)
        (f := "grind_check__L" ++ natStr batchGrind) (args := [j + 1, osTabs]) (fun i hi ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · omega
          · show 9 < j + 13; omega) fun C rd hH ↦ by
        obtain ⟨-, e3⟩ := ho1 C rd hH
        simp only [List.map_cons, List.map_nil]
        rw [e3 1 (by omega), ha1 _ (show 9 < k by omega)]
        exact hg C rd hH
      refine h.monoH fun C rd hH σ' ha e ↦ ?_
      obtain ⟨-, e3⟩ := ho1 C rd hH
      rw [e]
      simp only [List.map_cons, List.map_nil]
      rw [e3 1 (by omega), ha1 _ (show 9 < k by omega)]
  -- `λ` and `1/λ`
  have b5 := BlkA.seq (H := H) (show k ≤ j + 13 by omega) (show j + 13 ≤ j + 13 + 3 by omega) b4
    (B := [osCp (j + 13) j, osCst (j + 14) (word 1 0), osMul (j + 14) (j + 15) (j + 13)])
    (OutB := fun σ' ↦ ∀ i < 3, σ' (.n (j + 13 + i)) = (lamVals S).getD i 0) fun σ1 ha1 ho1 ↦ by
      refine ⟨lstF (j + 13) (lamVals S), fun C rd hH σ' ha hr ↦ ?_⟩
      have v : ∀ i < 3, σ' (.n (j + 13 + i)) = (lamVals S).getD i 0 := fun i hi ↦
        lstF_at hr (by simp [lamVals]) i (by simp [lamVals]; omega)
      refine ⟨?_, v⟩
      obtain ⟨⟨-, e3⟩, -⟩ := ho1 C rd hH
      have v0 := v 0 (by omega)
      have v1 := v 1 (by omega)
      have v2 := v 2 (by omega)
      simp only [lamVals, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2
      have ej : σ' (.n j) = rdCell S 0 := by rw [ha _ (by omega)]; simpa using e3 0 (by omega)
      simp only [osCp, osCst, osMul, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_copy,
        holds_const, holds_mul, ej, v0, v1, v2, word_one]
      refine ⟨trivial, trivial, ?_⟩
      exact (inv_mul_cancel₀ hlam).symm
  have ek : (osLam st).2.k = j + 13 + 3 := rfl
  rw [ek]
  refine BlkA.congr (BlkA.monoH b5.agree fun C rd hH σ' ha ⟨ho, hag⟩ ↦ ?_) (by
    simp only [osLam, List.append_assoc, List.cons_append, List.nil_append]; rfl)
  obtain ⟨⟨⟨⟨-, hpad⟩, e3⟩, -⟩, e5⟩ := ho
  have hok' := hok C rd hH
  refine ⟨⟨⟨⟨rfl, ⟨?_, ?_, ?_, ?_⟩, hco1, fun q hq ↦ ?_, by omega⟩,
    matsOk_agree hok'.mats hsf.below.mats fun i hi ↦ hag i hi, hpad⟩, by omega, hag⟩,
    ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro f hf
    have hf' : f ∈ [j + 8, j + 9, j + 10, j + 11, j + 12] := hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
    rcases hf' with rfl | rfl | rfl | rfl | rfl <;> omega
  · show st.cb < j + 13 + 3; have := hsf.below.cb; omega
  · show st.claim < j + 13 + 3; have := hsf.below.claim; omega
  · intro m hm; obtain ⟨a, b, d⟩ := hsf.below.mats m hm
    exact ⟨by omega, by omega, by omega⟩
  · have hq' : some p = some q := hq
    simp only [Option.some.injEq] at hq'; subst hq'; omega
  · show (⟨[j + 8, j + 9, j + 10, j + 11, j + 12].map (fun i ↦ σ' (.n i)), []⟩ : Fs) = _
    simp only [List.map_cons, List.map_nil]
    rw [e3 8 (by omega), e3 9 (by omega), e3 10 (by omega), e3 11 (by omega), e3 12 (by omega)]
    simp only [capOf, ← rdCell_eq]
    rfl
  · show σ' (.n (j + 13)) = _
    simpa [lamVals] using e5 0 (by omega)
  · show σ' (.n (j + 15)) = _
    simpa [lamVals] using e5 2 (by omega)
  · show σ' (.n st.cb) * gen ^ (st.co + 1) = σ (.n st.cb) * gen ^ st.co * gen
    rw [hag _ hsf.below.cb, pow_succ, mul_assoc]

end
end LeanVM.Guest.B1.Whir
