/-
  LeanVM.Guest.B1.Whir.CLvLam

  A non-final level's batching challenge honestly: the squeeze's permutation, `λ` and `1/λ`.
-/

module

public import LeanVM.Guest.B1.Whir.CLvCommit

/-!
# The batching challenge, honestly

`osLam_complete`: the squeeze's permutation `lamS cap` of the carried capacity; `λ` its cell `0`
and `1/λ` (`λ ≠ 0`); the zero run allocated if it was not.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {H : CallRel → Reader → Prop}

/-- The squeeze's permutation on the capacity `cap`. -/
def lamS (cap : List E) : KeccakState := (⟨cap, []⟩ : Fs).perm

/-- The values after the squeeze's permutation: `λ`, one and `1/λ`. -/
def lamVals (S : KeccakState) : List E := [rdCell S 0, word 1 0, (rdCell S 0)⁻¹]

/-- **The batching challenge, honestly**. -/
theorem osLam_complete {st : OsSt} (σ : Val) (hsf : st.Sf) (hok : ∀ C rd, H C rd → st.Ok σ)
    (hco : st.co < u128Bound) (hlam : rdCell (lamS (st.fsv σ)) 0 ≠ 0) :
    BlkA H σ st.k (osLam st).2.k (osLam st).1 (fun σ' ↦
      OsStep σ σ' st (osLam st).2 ∧
      (osLam st).2.F σ' = ⟨capOf (lamS (st.fsv σ)), []⟩ ∧
      σ' (.n (osLam st).2.lam) = rdCell (lamS (st.fsv σ)) 0 ∧
      σ' (.n (osLam st).2.lamInv) = (rdCell (lamS (st.fsv σ)) 0)⁻¹ ∧
      (osLam st).2.cur σ' = st.cur σ ∧ (osLam st).2.claim = st.claim ∧
      (osLam st).2.ys = st.ys ∧ (osLam st).2.sent = st.sent ∧ (osLam st).2.batched = st.batched) := by
  set k := st.k with hk
  set cap := st.fsv σ with hcap
  set S := lamS cap with hS
  set p := (osPad st.pad (k + 5)).2.1 with hp
  set j := (osPad st.pad (k + 5)).2.2 with hj
  have k33 : 33 ≤ k := hsf.k
  have kj : k + 5 ≤ j := osPad_next _ _
  have hpj : p + 4 < j := by
    rcases osPad_ptr st.pad (k + 5) (fun q hq ↦ by have := hsf.padB q hq; omega) with h | h <;> omega
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fs_five st hsf.fs
  have hfb : ∀ f ∈ st.fs, f < k := hsf.below.fs
  have hc : cap = [σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)] := by
    simp [hcap, OsSt.fsv, hf]
  -- the capacity copied
  have b1 : BlkA H σ k (k + 5) (st.fs.zipIdx.map fun (f, i) ↦ osCp (k + i) f)
      (fun σ' ↦ ∀ i < 5, σ' (.n (k + i)) = cap.getD i 0) := by
    refine ⟨lstF k cap, fun C rd hH σ' ha hr ↦ ?_⟩
    have hcl : cap.length = 5 := by simp [hcap, OsSt.fsv, hsf.fs]
    have v : ∀ i < 5, σ' (.n (k + i)) = cap.getD i 0 := fun i hi ↦
      lstF_at hr (by omega) i (by omega)
    refine ⟨?_, v⟩
    have u : ∀ f ∈ st.fs, σ' (.n f) = σ (.n f) := fun f hf' ↦ ha f (hfb f hf')
    rw [hf] at u ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at u
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, allOk_cons, allOk_nil,
      and_true, stmtOk_atom, holds_copy, osCp, Nat.zero_add, Nat.reduceAdd]
    rw [show k = k + 0 from rfl, v 0 (by omega), v 1 (by omega), v 2 (by omega), v 3 (by omega),
      v 4 (by omega), u.1, u.2.1, u.2.2.1, u.2.2.2.1, u.2.2.2.2, hc]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  -- the zero run
  have b2 := BlkA.seq (H := H) (show k ≤ k + 5 by omega) kj b1 (B := (osPad st.pad (k + 5)).1)
    (OutB := fun σ' ↦ PadOk σ' (some p)) fun σ1 ha1 _ ↦
    osPad_blk σ1 st.pad (k + 5) (fun C rd hH ↦ by
      have := ((hok C rd hH).agree (fun i hi ↦ ha1 i hi)).pad
      intro q hq
      obtain ⟨z1, z2, z3, z4⟩ := (hok C rd hH).pad q hq
      have hb := hsf.padB q hq
      rw [ha1 _ (by omega), ha1 _ (by omega), ha1 _ (by omega), ha1 _ (by omega)]
      exact ⟨z1, z2, z3, z4⟩) (fun q hq ↦ by have := hsf.padB q hq; omega)
  -- the permutation
  have b3 := BlkA.seq (H := H) (show k ≤ j by omega) (show j ≤ j + 13 by omega) b2
    (B := [osKeccak ([p + 1, p + 1, p + 1, p + 1, p + 1, p + 2, p + 3, p + 4] ++ [k, k + 1, k + 2, k + 3, k + 4]) j])
    (OutB := fun σ' ↦ ∀ i < 13, σ' (.n (j + i)) = rdCell S i) fun σ1 ha1 ho1 ↦ by
      refine (keccak_blk ⟨cap, []⟩ (by simp) (by simp) (fun i hi ↦ ?_)
        (fun C rd hH ↦ ?_)).mono fun σ' h i hi ↦ by
          rw [h i hi, hS, lamS]
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl)
        all_goals omega
      · obtain ⟨w, z⟩ := ho1 C rd hH
        obtain ⟨z1, z2, z3, z4⟩ := z p rfl
        have hcl : cap.length = 5 := by simp [hcap, OsSt.fsv, hsf.fs]
        simp only [List.map_append, List.map_cons, List.map_nil, z1, z2, z3, z4]
        rw [show k = k + 0 from rfl, w 0 (by omega), w 1 (by omega),
          w 2 (by omega), w 3 (by omega), w 4 (by omega), hc]
        simp [pendCells]
  -- `λ` and `1/λ`
  have b5 := BlkA.seq (H := H) (show k ≤ j + 13 by omega) (show j + 13 ≤ j + 13 + 3 by omega) b3
    (B := [osCp (j + 13) j, osCst (j + 14) (word 1 0), osMul (j + 14) (j + 15) (j + 13)])
    (OutB := fun σ' ↦ ∀ i < 3, σ' (.n (j + 13 + i)) = (lamVals S).getD i 0) fun σ1 ha1 ho1 ↦ by
      refine ⟨lstF (j + 13) (lamVals S), fun C rd hH σ' ha hr ↦ ?_⟩
      have v : ∀ i < 3, σ' (.n (j + 13 + i)) = (lamVals S).getD i 0 := fun i hi ↦
        lstF_at hr (by simp [lamVals]) i (by simp [lamVals]; omega)
      refine ⟨?_, v⟩
      obtain ⟨-, e3⟩ := ho1 C rd hH
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
  obtain ⟨⟨⟨-, hpad⟩, e3⟩, e5⟩ := ho
  have hok' := hok C rd hH
  refine ⟨⟨⟨⟨rfl, ⟨?_, ?_, ?_, ?_⟩, hco, fun q hq ↦ ?_, by omega⟩,
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
  · show σ' (.n st.cb) * gen ^ st.co = σ (.n st.cb) * gen ^ st.co
    rw [hag _ hsf.below.cb]

end
end LeanVM.Guest.B1.Whir
