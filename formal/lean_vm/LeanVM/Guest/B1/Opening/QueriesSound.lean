/-
  LeanVM.Guest.B1.Opening.QueriesSound

  One query is `QueryOpens`; the soundness direction of `opening_queries`.
-/

module

public import LeanVM.Guest.B1.Opening.WalkPath
public import LeanVM.Guest.AcceptableChild

/-!
# One query, assembled (`opening_query`, lean_ethereum.py:1346-1390 at 40f877dc)

`oqQuery_sound`: the statements of `oqQueryT` (the row, the dot product, the padding run, the
leaf hash, the call of a sound `walk_path`) give `QueryOpens` at the position whose windows the
window pointer's run holds, and read each of its windows.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The query's pieces, by membership: its atoms, and the walk's call. -/
theorem oqQuery_pieces {C : CallRel} {s : Oq} {bp cap flags wp : V} {b : ℕ} {emit : Bool} {pr : ℕ}
    {walk : String} (hA : BlockOkC C rd σ (oqQueryT s bp cap flags wp b emit pr walk)) :
    (∀ a, Stmt.atom a ∈ oqPacksT b s.R → a.Holds rd σ) ∧
      (∀ a, Stmt.atom a ∈ oqDotT s wp b → a.Holds rd σ) ∧
      (emit = true → ∀ a, Stmt.atom a ∈ oqPadT (oqK1 b s.R + s.D) → a.Holds rd σ) ∧
      (∀ a, Stmt.atom a ∈ oqLeafT s b (oqPr s b emit pr) (oqKL s b emit) → a.Holds rd σ) ∧
      C walk [σ (.n (oqOut s (oqKL s b emit) (s.B - 1) 0)), σ (.n (oqOut s (oqKL s b emit) (s.B - 1) 1)),
        σ bp, σ cap, σ flags] [] := by
  refine ⟨fun a h => hA.atom ?_, fun a h => hA.atom ?_, fun he a h => hA.atom ?_,
    fun a h => hA.atom ?_, ?_⟩
  · simp only [oqQueryT, List.mem_append]; simp_all
  · simp only [oqQueryT, List.mem_append]; simp_all
  · simp only [oqQueryT, List.mem_append]; simp_all
  · simp only [oqQueryT, List.mem_append]; simp_all
  · have := hA.call (f := walk) (args := [.n (oqOut s (oqKL s b emit) (s.B - 1) 0),
      .n (oqOut s (oqKL s b emit) (s.B - 1) 1), bp, cap, flags]) (rets := []) (by simp [oqQueryT])
    simpa using this

/-- The row's packed cells and the leaf's digest of a query. -/
theorem oqQuery_leaf {C : CallRel} {s : Oq} (hs : s.RowShape) {bp cap flags wp : V} {b : ℕ}
    {emit : Bool} {pr : ℕ} {walk : String}
    (hA : BlockOkC C rd σ (oqQueryT s bp cap flags wp b emit pr walk))
    (hpad : σ (.n (oqPr s b emit pr)) = word 1 0 0)
    (hz : ∀ i < 4, σ (.n (oqPr s b emit pr + 1 + i)) = 0) :
    (σ (.n (oqOut s (oqKL s b emit) (s.B - 1) 0)), σ (.n (oqOut s (oqKL s b emit) (s.B - 1) 1))) =
      digestHalves (merkleLeafDigest (oqRow b s.R σ)) := by
  obtain ⟨hP, -, -, hL, -⟩ := oqQuery_pieces hA
  have hR2 : s.R % 2 = 0 := by rcases hs with ⟨hb, hI⟩ | ⟨hb, hI⟩ <;> simp [Oq.R, hb, hI]
  have hpk : ∀ j < s.ncells, σ (.n (oqPk b s.R j)) =
      E.ofLimbs ((oqRow b s.R σ).getD (2 * j) 0) ((oqRow b s.R σ).getD (2 * j + 1) 0) 0 :=
    fun j hj => by
      have hj' : j < s.R / 2 := hj
      rw [(oqPack_sound hP hj').2.2, getD_oqRow (by omega), getD_oqRow (by omega)]
      rfl
  exact oqLeaf_sound hs hL hpad hz (by simp [oqRow, Oq.ncells]; omega) hpk

/-- **One query is `QueryOpens`** (`opening_query` with a sound `walk_path`): with the padding run
`1, 0, 0, 0, 0` and the window pointer's run holding the windows of `q < 2^(pd + cd)`, the query
reads its windows, opens the hinted row at `q`, and its value is the row's dot product with the
weights. -/
theorem oqQuery_sound {s : Oq} (hs : s.RowShape) {walk : String} (hW : WalkSound walk s.pd s.cd)
    {bp cap flags wp : V} {b : ℕ} {emit : Bool} {pr : ℕ}
    (hA : BlockOkC (coreProgram.Rel rd) rd σ (oqQueryT s bp cap flags wp b emit pr walk))
    (hpad : σ (.n (oqPr s b emit pr)) = word 1 0 0)
    (hz : ∀ i < 4, σ (.n (oqPr s b emit pr + 1 + i)) = 0)
    {q : ℕ} (hq : q < 2 ^ (s.pd + s.cd))
    (hwin : ∀ i v, LoadHolds rd (σ bp) i v → i < qwN (s.pd + s.cd) s.cd →
      v = gen ^ qwVal (s.pd + s.cd) s.cd q i) :
    (∀ i < qwN (s.pd + s.cd) s.cd, LoadHolds rd (σ bp) i (gen ^ qwVal (s.pd + s.cd) s.cd q i)) ∧
    QueryOpens rd s.base s.I (s.pd + s.cd) s.cd (σ cap) (σ flags) (σ wp) q (oqRow b s.R σ)
      (σ (.n (oqDot s b))) := by
  obtain ⟨hP, hD, -, -, hcall⟩ := oqQuery_pieces hA
  have hrl : (oqRow b s.R σ).length = s.R := by simp [oqRow]
  have hWd := oqWord_sound hs hP hD
  obtain ⟨hw, hdot⟩ := oqDot_sound hs hD hWd
  obtain ⟨-, hwl, sibs, hsl, hflag, hc0, hc1⟩ :=
    hW rd _ _ _ _ _ _ hcall _ q (oqQuery_leaf hs hA hpad hz) hq hwin
  refine ⟨hwl, ?_⟩
  unfold QueryOpens
  rw [show s.pd + s.cd - s.cd = s.pd by omega]
  refine ⟨by rw [hrl]; rfl, sibs, oqW s b σ, hsl, fun l hl => hw l (by simpa [Oq.lo] using hl),
    hc0, hc1, hflag, ?_⟩
  rw [hdot, rowDot_eq]
  congr 1

end
end LeanVM.Guest.B1
