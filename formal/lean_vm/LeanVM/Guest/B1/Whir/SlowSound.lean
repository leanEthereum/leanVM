/-
  LeanVM.Guest.B1.Whir.SlowSound

  `level_residual_slow` is sound and complete at each of its specializations.
-/

module

public import LeanVM.Guest.B1.Whir.SlowComplete
public import LeanVM.Guest.B1.Whir.HelperAll
import LeanVM.Guest.B1.Common.Vc

/-!
# `level_residual_slow`, every specialization

`lrsTable_sound`: each entry of `lrsTable` (`level_residual_slow__L{Q}_L{pre}_L{yr}_L{vo}`) returns
`lrsVal` at the positions and challenges it reads: its body and its loop are their templates
(`lrsTable_ok`), its `residual_query_slow` is in `rqsTable` and its template (`rqsTable_ok`), and the
shapes meet `rqs_sound`'s and `lrs_sound`'s conditions (`lrsTable_shapes`, `rqsTable_shapes`, by
the kernel). `lrsTable_zero` and `lrsTable_complete`: a call at a zero flag returns `0`, and one at
a nonzero flag in `K` returns its sum on a memory whose buffers hold the sum's partial values and
`λ`'s powers (`SlowComplete.lean`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-- Every `residual_query_slow` reads a fold challenge and has a first inverse `1`. -/
theorem rqsTable_shapes : ∀ e ∈ rqsTable, 1 ≤ e.2.1 ∧ vanishInv e.2.2.2 = 1 := by decide +kernel

/-- Every `level_residual_slow` walks at least one query, below `2^30`, and its sum calls a
`residual_query_slow` of its own shape. -/
theorem lrsTable_shapes : ∀ e ∈ lrsTable, 1 ≤ e.2.1 ∧ e.2.1 < 2 ^ 30 ∧
    (e.2.2.2.2.2.2.2, e.2.2.1, e.2.2.2.1, e.2.2.2.2.1) ∈ rqsTable := by decide +kernel

theorem osParams_three : osParams 3 = [.n 0, .n 1, .n 2] := rfl

theorem osParams_four : osParams 4 = lsumParams := rfl

theorem osParams_five : osParams 5 = lrsParams := rfl

theorem osParams_eight : osParams 8 = lrsLoopParams := rfl

/-- **`residual_query_slow`, every specialization**: at a call of depth `d`, the query weight. -/
theorem rqsTable_sound {rd : Reader} {e : String × ℕ × ℕ × ℕ} (he : e ∈ rqsTable) {fc tc : E}
    {cs : ℕ → E} (hf : ∀ t < e.2.1, LoadHolds rd fc t (cs t))
    (hy : ∀ j < e.2.2.1, LoadHolds rd tc j (cs (e.2.1 + j))) (d : ℕ) :
    RqOk (coreProgram.relN rd d) e.1 (e.2.1 + e.2.2.1) e.2.2.2 fc tc cs := by
  intro x r h
  obtain ⟨fn, hfn, hp, hb⟩ := rqsTable_ok e he
  obtain ⟨hpre, hinv⟩ := rqsTable_shapes e he
  cases d with
  | zero => exact h.elim
  | succ d =>
    rw [B1.relN_succ_iff_fnSem hfn] at h
    have := rqs_sound hpre hinv (hp.trans osParams_three) hb h hf hy
    simpa using this

/-- **`level_residual_slow`, every specialization**: a call returns `lrsVal` at the `Q` positions
at `positions`, the `pre` fold challenges at `fold_cs` and the `yr` tail challenges at `tail_cs`
it reads (`slowVal` of `SlowSpec.lean`, `SlowRet`). -/
theorem lrsTable_sound (rd : Reader) {e : String × ℕ × ℕ × ℕ × ℕ × String × String × String}
    (he : e ∈ lrsTable) {a r : List E} (h : coreProgram.Rel rd e.1 a r) (pos cs : ℕ → E)
    (hpos : ∀ k < e.2.1, LoadHolds rd (a.getD 0 0) k (pos k))
    (hf : ∀ t < e.2.2.1, LoadHolds rd (a.getD 1 0) t (cs t))
    (hy : ∀ j < e.2.2.2.1, LoadHolds rd (a.getD 2 0) j (cs (e.2.2.1 + j))) :
    r = [lrsVal e.2.1 (e.2.2.1 + e.2.2.2.1) e.2.2.2.2.1 pos cs (a.getD 3 0) (a.getD 4 0)] := by
  obtain ⟨⟨fo, hfo, hpo, hbo⟩, ⟨fs, hfs, hps, hbs⟩, ⟨fl, hfl, hpl, hbl⟩⟩ := lrsTable_ok e he
  obtain ⟨hQ, hQb, hrq⟩ := lrsTable_shapes e he
  obtain ⟨d, hd⟩ := h
  cases d with
  | zero => exact hd.elim
  | succ d =>
    rw [B1.relN_succ_iff_fnSem hfo] at hd
    refine lrs_sound (hpo.trans osParams_five) hbo hd fun r hs ↦ ?_
    cases d with
    | zero => exact hs.elim
    | succ d =>
      rw [B1.relN_succ_iff_fnSem hfs] at hs
      have ha : ∀ i < 4, (a.take 4).getD i 0 = a.getD i 0 := fun i hi ↦ by
        simp [List.getD_eq_getElem?_getD, hi]
      have := lsum_sound (fun _ _ _ h ↦ ⟨d, h⟩) hQ hQb (hps.trans osParams_four) hbs hfl
        (hpl.trans osParams_eight) hbl hs (pos := pos)
        (fun d' ↦ by rw [ha 1 (by omega), ha 2 (by omega)]; exact rqsTable_sound hrq hf hy d')
        (by rw [ha 0 (by omega)]; exact hpos)
      rw [ha 3 (by omega)] at this
      simpa using this

/-- **At a zero flag `level_residual_slow` returns `0`**, whatever its other arguments: the
completeness of every level whose challenges' product is not zero. -/
theorem lrsTable_zero (rd : Reader) {e : String × ℕ × ℕ × ℕ × ℕ × String × String × String}
    (he : e ∈ lrsTable) (p f t l : E) : coreProgram.Rel rd e.1 [p, f, t, l, 0] [0] := by
  obtain ⟨⟨fo, hfo, hpo, hbo⟩, -, -⟩ := lrsTable_ok e he
  refine ⟨1, fo, hfo, fun v ↦ [p, f, t, l, 0].getD v.idx 0, by rw [hpo]; rfl, ?_⟩
  rw [hbo]
  simp only [lrsBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  refine ⟨?_, fun _ ↦ ⟨rfl, rfl, rfl⟩, fun h ↦ absurd rfl h⟩
  rw [show (([p, f, t, l, 0] : List E).getD (V.n 4).idx 0) = ofK 0 by rw [ofK_zero]; rfl]
  exact ofK_isInK 0

/-- **At a nonzero flag `level_residual_slow` returns its sum**, on a memory whose buffers `acc`,
`pw` hold the partial sums `lrsAcc` and `λ^(2 + k)` up to `Q`, the positions and the challenges
read. -/
theorem lrsTable_complete (rd : Reader) {e : String × ℕ × ℕ × ℕ × ℕ × String × String × String}
    (he : e ∈ lrsTable) {posp fc tc lam z acc pw : E} {pos cs : ℕ → E} (hz : z ≠ 0) (hzK : IsInK z)
    (hpos : ∀ k < e.2.1, LoadHolds rd posp k (pos k))
    (hf : ∀ t < e.2.2.1, LoadHolds rd fc t (cs t))
    (hy : ∀ j < e.2.2.2.1, LoadHolds rd tc j (cs (e.2.2.1 + j)))
    (hacc : ∀ k ≤ e.2.1, LoadHolds rd acc k (lrsAcc (e.2.2.1 + e.2.2.2.1) e.2.2.2.2.1 pos cs lam k))
    (hpw : ∀ k ≤ e.2.1, LoadHolds rd pw k (lam ^ 2 * lam ^ k)) :
    coreProgram.Rel rd e.1 [posp, fc, tc, lam, z]
      [lrsVal e.2.1 (e.2.2.1 + e.2.2.2.1) e.2.2.2.2.1 pos cs lam z] := by
  obtain ⟨⟨fo, hfo, hpo, hbo⟩, ⟨fs, hfs, hps, hbs⟩, ⟨fl, hfl, hpl, hbl⟩⟩ := lrsTable_ok e he
  obtain ⟨hQ, hQb, hrqm⟩ := lrsTable_shapes e he
  obtain ⟨fr, hfr, hpr, hbr⟩ := rqsTable_ok _ hrqm
  obtain ⟨hpre, hinv⟩ := rqsTable_shapes _ hrqm
  have hrq : ∀ k < e.2.1, coreProgram.relN rd 1 e.2.2.2.2.2.2.2 [pos k, fc, tc]
      [∏ t ∈ Finset.range (e.2.2.1 + e.2.2.2.1), rqsFac e.2.2.2.2.1 (e.2.2.1 + e.2.2.2.1) cs (pos k) t] :=
    fun k _ ↦ (B1.relN_succ_iff_fnSem hfr 0 _ _).mpr
      (rqs_complete hpre hinv (hpr.trans osParams_three) hbr hf hy)
  have hsum := (B1.relN_succ_iff_fnSem hfs (e.2.1 + 1) _ _).mpr
    (lsum_complete hQ hQb (hps.trans osParams_four) hbs hfl (hpl.trans osParams_eight) hbl hacc hpw
      hpos hrq)
  have hv : lrsVal e.2.1 (e.2.2.1 + e.2.2.2.1) e.2.2.2.2.1 pos cs lam z =
      lrsAcc (e.2.2.1 + e.2.2.2.1) e.2.2.2.2.1 pos cs lam e.2.1 := by
    simp only [lrsVal, hz, ↓reduceIte, lrsAcc]
  rw [hv]
  exact ⟨e.2.1 + 1 + 1 + 1, (B1.relN_succ_iff_fnSem hfo _ _ _).mpr
    (lrs_complete (hpo.trans osParams_five) hbo hz hzK hsum)⟩

end
end LeanVM.Guest.B1.Whir
