/-
  LeanVM.Guest.B1.Whir.SlowSound

  `level_residual_slow` is sound at each of its specializations.
-/

module

public import LeanVM.Guest.B1.Whir.SlowLevel
public import LeanVM.Guest.B1.Whir.HelperAll
import LeanVM.Guest.B1.Common.Vc

/-!
# `level_residual_slow`, every specialization

`lrsTable_sound`: each entry of `lrsTable` (`level_residual_slow__L{Q}_L{pre}_L{yr}_L{vo}`) returns
`slowVal` at the positions and challenges it reads: its body and its loop are their templates
(`lrsTable_ok`), its `residual_query_slow` is in `rqsTable` and its template (`rqsTable_ok`), and the
shapes meet `rqs_sound`'s and `lrs_sound`'s conditions (`lrsTable_shapes`, `rqsTable_shapes`, by
the kernel).
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

/-- **`level_residual_slow`, every specialization**: a call returns `slowVal` at the `Q` positions
at `positions`, the `pre` fold challenges at `fold_cs` and the `yr` tail challenges at `tail_cs`
it reads (`SlowRet`). -/
theorem lrsTable_sound (rd : Reader) {e : String × ℕ × ℕ × ℕ × ℕ × String × String × String}
    (he : e ∈ lrsTable) {a r : List E} (h : coreProgram.Rel rd e.1 a r) (pos cs : ℕ → E)
    (hpos : ∀ k < e.2.1, LoadHolds rd (a.getD 0 0) k (pos k))
    (hf : ∀ t < e.2.2.1, LoadHolds rd (a.getD 1 0) t (cs t))
    (hy : ∀ j < e.2.2.2.1, LoadHolds rd (a.getD 2 0) j (cs (e.2.2.1 + j))) :
    r = [slowVal e.2.1 (e.2.2.1 + e.2.2.2.1) e.2.2.2.2.1 pos cs (a.getD 3 0) (a.getD 4 0)] := by
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

end
end LeanVM.Guest.B1.Whir
