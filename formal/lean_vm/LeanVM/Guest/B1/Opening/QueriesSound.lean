/-
  LeanVM.Guest.B1.Opening.QueriesSound

  One query, assembled: its row opens into the cap, its fold is the Spec's `foldRow`, and at the
  final level the fold is the final polynomial.
-/

module

public import LeanVM.Guest.B1.Opening.WalkPath
public import LeanVM.Guest.B1.Opening.QueriesLeaf
public import LeanVM.Guest.B1.Opening.QueriesFlatC
public import LeanVM.Guest.AcceptableChild

/-!
# One query, assembled (`opening_query`)

`oqQuery_sound`: the statements of `oqQueryT` (the row and its packs, the padding run, the leaf
hash, the call of a sound `walk_path`, the fold and, at the final level, the check) at the point
`x = eOfNat q`, `q` the position whose windows the window pointer's run holds, read the windows,
open the row `oqRow` at `q` (`QueryOpensS`), read the rounds at `coefs` (`oqRounds`), none of
whose combiners vanishes at `q`, and give the fold's value `foldRow (lanesOf base row) q rounds`;
at the final level it is `novelSum` of the coefficients read at `hs` over `wsChain` at `x`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## The row's lanes -/

theorem extRow_limbs : ∀ cs : List E, extRow (cs.flatMap fun c ↦ [c.limb 0, c.limb 1]) = cs
  | [] => rfl
  | c :: cs => by
    rw [List.flatMap_cons, List.cons_append, List.cons_append, List.nil_append, extRow, extRow_limbs cs,
      ofLimbs_limb]

theorem length_oqRow (s : Oq) (b : ℕ) (σ : Val) : (oqRow s b σ).length = rowLen s.base s.folds := by
  unfold oqRow rowLen Oq.I
  split <;> simp [List.length_flatMap, mul_comm]

/-- The lanes of the row are the guest's: the cells, reversed at level 0, where they are in `K`. -/
theorem lanesOf_oqRow {s : Oq} {b : ℕ} (hK : s.base = 1 → ∀ j < s.I, IsInK (σ (.n (b + j)))) :
    lanesOf s.base (oqRow s b σ) = oqLanes s b σ := by
  unfold lanesOf oqRow oqLanes oqCells
  by_cases hb : s.base = 1
  · simp only [hb, ↓reduceIte, List.map_reverse, List.map_map]
    congr 1
    refine List.map_congr_left fun j hj ↦ ?_
    obtain ⟨a, ha⟩ := (isInK_iff _).mp (hK hb j (List.mem_range.mp hj))
    simp only [Function.comp_apply, ha]
    simp [ofK_eq_ofLimbs]
  · simp only [hb, ↓reduceIte]
    have := extRow_limbs ((List.range s.I).map fun j ↦ σ (.n (b + j)))
    rwa [List.flatMap_map] at this

/-! ## One query -/

/-- The query's pieces, by membership: its atoms, and the walk's call. -/
theorem oqQuery_pieces {C : CallRel} {s : Oq} {x bp cap flags coefs hs : V} {b : ℕ} {emit : Bool}
    {pr : ℕ} {walk : String} (hA : BlockOkC C rd σ (oqQueryT s x bp cap flags coefs hs b emit pr walk)) :
    (∀ a, Stmt.atom a ∈ oqPrepT s b → a.Holds rd σ) ∧
      (emit = true → ∀ a, Stmt.atom a ∈ oqPadT (oqK1 s b) → a.Holds rd σ) ∧
      (∀ a, Stmt.atom a ∈ oqLeafT s b (oqPr s b emit pr) (oqKL s b emit) → a.Holds rd σ) ∧
      C walk [σ (.n (oqOut s (oqKL s b emit) (s.B - 1) 0)), σ (.n (oqOut s (oqKL s b emit) (s.B - 1) 1)),
        σ bp, σ cap, σ flags] [] ∧
      (∀ a, Stmt.atom a ∈ oqFoldT s coefs x b (oqCh s b emit) → a.Holds rd σ) ∧
      (s.final = 1 → ∀ a, Stmt.atom a ∈ oqFinT s x hs (oqVal s (oqCh s b emit)) → a.Holds rd σ) := by
  refine ⟨fun a h => hA.atom ?_, fun he a h => hA.atom ?_, fun a h => hA.atom ?_, ?_,
    fun a h => hA.atom ?_, fun hf a h => hA.atom ?_⟩
  · simp only [oqQueryT, List.mem_append]; simp_all
  · simp only [oqQueryT, List.mem_append]; simp_all
  · simp only [oqQueryT, List.mem_append]; simp_all
  · have := hA.call (f := walk) (args := [.n (oqOut s (oqKL s b emit) (s.B - 1) 0),
      .n (oqOut s (oqKL s b emit) (s.B - 1) 1), bp, cap, flags]) (rets := []) (by simp [oqQueryT])
    simpa using this
  · simp only [oqQueryT, List.mem_append]; simp_all
  · simp only [oqQueryT, List.mem_append]; simp_all

/-- The packed cells of a level-0 row, and its words' `K` membership. -/
theorem oqQuery_packs {s : Oq} (hb : s.base = 1) (hI : s.I % 2 = 0) {b : ℕ}
    (hP : ∀ a, Stmt.atom a ∈ oqPrepT s b → a.Holds rd σ) :
    (∀ j < s.I, IsInK (σ (.n (b + j)))) ∧ ∀ j < s.ncells, σ (.n (oqPk s b j)) =
      E.ofLimbs ((oqRow s b σ).getD (2 * j) 0) ((oqRow s b σ).getD (2 * j + 1) 0) := by
  have hP' : ∀ a, Stmt.atom a ∈ oqPacksT b s.I → a.Holds rd σ := fun a h ↦
    hP a (by simp only [oqPrepT, hb, ↓reduceIte]; exact List.mem_append_right _ h)
  have hr : ∀ i < s.I, (oqRow s b σ).getD i 0 = (σ (.n (b + i))).limb 0 := fun i hi ↦ by
    simp [oqRow, hb, List.getD_eq_getElem?_getD, hi]
  refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_⟩
  · have := oqPack_sound hP' (j := j / 2) (by omega)
    rcases Nat.mod_two_eq_zero_or_one j with e | e
    · rw [show b + 2 * (j / 2) = b + j by omega] at this; exact this.1
    · rw [show b + 2 * (j / 2) + 1 = b + j by omega] at this; exact this.2.1
  · have hj' : j < s.I / 2 := by simpa [Oq.ncells, hb] using hj
    have := (oqPack_sound hP' hj').2.2
    simp only [oqPk, hb, ↓reduceIte]
    rw [this, hr _ (by omega), hr _ (by omega), Nat.add_assoc]

/-- **One query** (`opening_query` with a sound `walk_path`) at the point `x = eOfNat q`: with the
padding run `1, 0, 0, 0, 0` and the window pointer's run holding the windows of
`q < 2^(pd + cd)`, the query reads its windows, opens the row at `q`, reads the rounds, and its
fold's value is `foldRow`; at the final level the fold is
`novelSum` of the coefficients at `hs` over `wsChain` at the point. -/
theorem oqQuery_sound {P : Program} {s : Oq} (hs : s.RowShape) {walk : String}
    (hW : WalkSound P walk s.pd s.cd)
    {x bp cap flags coefs hsV : V} {b : ℕ} {emit : Bool} {pr : ℕ}
    (hA : BlockOkC (P.Rel rd) rd σ (oqQueryT s x bp cap flags coefs hsV b emit pr walk))
    (hpad : σ (.n (oqPr s b emit pr)) = word 1 0)
    (hz : ∀ i < 4, σ (.n (oqPr s b emit pr + 1 + i)) = 0)
    {q : ℕ} (hq : q < 2 ^ (s.pd + s.cd)) (hx : σ x = eOfNat q)
    (hwin : ∀ i v, LoadHolds rd (σ bp) i v → i < qwN (s.pd + s.cd) s.cd →
      v = gen ^ qwVal (s.pd + s.cd) s.cd q i) :
    (∀ i < qwN (s.pd + s.cd) s.cd, LoadHolds rd (σ bp) i (gen ^ qwVal (s.pd + s.cd) s.cd q i)) ∧
    (∃ sibs, QueryOpensS rd s.base s.folds (s.pd + s.cd) s.cd (σ cap) (σ flags) q (oqRow s b σ) sibs) ∧
    RoundsAt rd (σ coefs) (oqRounds s (oqCh s b emit) σ) ∧
    σ (.n (oqVal s (oqCh s b emit))) =
      foldRow (lanesOf s.base (oqRow s b σ)) (K.ofBits q) (oqRounds s (oqCh s b emit) σ) := by
  obtain ⟨hP, -, hL, hcall, hF, -⟩ := oqQuery_pieces hA
  have hf : 1 ≤ s.folds := by rcases hs with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  -- the row's lanes
  have hI : s.I % 2 = 0 := by
    unfold Oq.I; rw [show s.folds = s.folds - 1 + 1 by omega, pow_succ]; omega
  have hKr : s.base = 1 → ∀ j < s.I, IsInK (σ (.n (b + j))) := fun hb ↦ (oqQuery_packs hb hI hP).1
  -- the leaf
  have hleaf : (σ (.n (oqOut s (oqKL s b emit) (s.B - 1) 0)),
      σ (.n (oqOut s (oqKL s b emit) (s.B - 1) 1))) = digestHalves (merkleLeafDigest (oqRow s b σ)) := by
    by_cases hb : s.base = 1
    · have hpk := (oqQuery_packs hb hI hP).2
      refine oqLeaf_sound hs hL hpad hz (cs := (List.range s.ncells).map fun j ↦
        E.ofLimbs ((oqRow s b σ).getD (2 * j) 0) ((oqRow s b σ).getD (2 * j + 1) 0)) (by simp)
        (fun j hj ↦ by rw [hpk j hj]; simp [List.getD_eq_getElem?_getD, hj]) ?_
      refine cellsBytes_packed _ _ ?_
      rw [length_oqRow]; simp [rowLen, hb, Oq.ncells, Oq.I]
      have : 2 ^ s.folds = 2 * 2 ^ (s.folds - 1) := by rw [← pow_succ']; congr 1; omega
      omega
    · refine oqLeaf_sound hs hL hpad hz (cs := oqCells s b σ) (by simp [oqCells, Oq.ncells, hb])
        (fun j hj ↦ by simp [oqPk, hb, oqCells, List.getD_eq_getElem?_getD,
          show j < s.I by simpa [Oq.ncells, hb] using hj]) ?_
      rw [cellsBytes_limbs]
      simp [oqRow, hb, oqCells, List.flatMap_map]
  obtain ⟨-, hwl, sibs, hsl, hflag, hc0, hc1⟩ := hW rd _ _ _ _ _ _ hcall _ q hleaf hq hwin
  obtain ⟨hRA, hval⟩ := oqFold_sound hf hF
  refine ⟨hwl, ⟨sibs, length_oqRow s b σ, by simpa using hsl, ?_, ?_, ?_⟩, hRA, ?_⟩
  · rw [show s.pd + s.cd - s.cd = s.pd by omega]; exact hc0
  · rw [show s.pd + s.cd - s.cd = s.pd by omega]; exact hc1
  · rw [show s.pd + s.cd - s.cd + 1 = s.pd + 1 by omega]; exact hflag
  · rw [hval, foldRow_eq, lanesOf_oqRow hKr, hx]
    rfl

end
end LeanVM.Guest.B1
