/-
  LeanVM.Guest.B1.Place.LsLoops

  `level_residual_sum`'s loop holds at its honest arguments and, with its `residual_query_slow`,
  places nothing.
-/

module

public import LeanVM.Guest.B1.Whir.SlowSound
public import LeanVM.Guest.B1.Whir.SlowComplete
public import LeanVM.Guest.B1.Place.LrPure
import LeanVM.Guest.B1.Common.Vc

/-!
# The slow residual's loop

* `lsLoop_rel`: at an entry of `lrsTable`, the loop, entered at `1` with the bound `g^Q`, on a
  memory holding the positions, the challenges and the sum's buffers (`lrsAcc`, `λ^(2 + j)`),
  from `lrsLoop_complete` and `rqs_complete`.
* `rqs_pure`, `lrsLoop_pure`: the loop places nothing and calls only itself and its
  `residual_query_slow`, which places nothing and calls nothing.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier LeanVM.Guest.Memory

@[expose] public section

theorem rqsSteps_pure (S : List String) (pre vo : ℕ) :
    ∀ f t, (rqsSteps pre vo t f).all (Stmt.pure S) = true
  | 0, _ => rfl
  | f + 1, t => by
    rw [rqsSteps, List.all_append, rqsSteps_pure S pre vo f (t + 1), Bool.and_true]
    simp [rqsStep, Stmt.pure, atomUnplaced]

/-- **`residual_query_slow` places nothing and calls nothing.** -/
theorem rqs_pure (S : List String) (pre yr vo : ℕ) : Stmt.pureList S (rqsBody pre yr vo) = true := by
  rw [pureList_eq_all, rqsBody, rqsPre, List.all_append, List.all_append, List.all_append,
    rqsSteps_pure]
  simp [rqsHead, Stmt.pure, atomUnplaced]

/-- **The loop places nothing and calls only itself and its `residual_query_slow`.** -/
theorem lrsLoop_pure (rq self : String) : Stmt.pureList [self, rq] (lrsLoopBody rq self) = true := by
  simp [lrsLoopBody, Stmt.pureList, Stmt.pure, atomUnplaced]

/-- **The loop of an entry of `lrsTable` holds at its honest arguments**: entered at `1` with the
bound `g^Q`, on a memory holding the positions, the challenges and the sum's buffers. -/
theorem lsLoop_rel {rd : Reader} {e : String × ℕ × ℕ × ℕ × ℕ × String × String × String}
    (he : e ∈ lrsTable) {acc pw P F T lam : E} {pos cs : ℕ → E}
    (hacc : ∀ k ≤ e.2.1, LoadHolds rd acc k (lrsAcc (e.2.2.1 + e.2.2.2.1) e.2.2.2.2.1 pos cs lam k))
    (hpw : ∀ k ≤ e.2.1, LoadHolds rd pw k (lam ^ 2 * lam ^ k))
    (hpos : ∀ k < e.2.1, LoadHolds rd P k (pos k)) (hf : ∀ t < e.2.2.1, LoadHolds rd F t (cs t))
    (hy : ∀ j < e.2.2.2.1, LoadHolds rd T j (cs (e.2.2.1 + j))) :
    coreProgram.Rel rd e.2.2.2.2.2.2.1 [1, gen ^ e.2.1, acc, pw, P, F, T, lam] [] := by
  obtain ⟨-, -, ⟨fl, hfl, hpl, hbl⟩⟩ := lrsTable_ok e he
  obtain ⟨hQ, -, hrqm⟩ := lrsTable_shapes e he
  obtain ⟨fr, hfr, hpr, hbr⟩ := rqsTable_ok _ hrqm
  obtain ⟨hpre, hinv⟩ := rqsTable_shapes _ hrqm
  have hrq : ∀ k < e.2.1, coreProgram.relN rd 1 e.2.2.2.2.2.2.2 [pos k, F, T]
      [∏ t ∈ Finset.range (e.2.2.1 + e.2.2.2.1), rqsFac e.2.2.2.2.1 (e.2.2.1 + e.2.2.2.1) cs (pos k) t] :=
    fun k _ ↦ (B1.relN_succ_iff_fnSem hfr 0 _ _).mpr
      (rqs_complete hpre hinv (hpr.trans osParams_three) hbr hf hy)
  have h := lrsLoop_complete hfl (hpl.trans osParams_eight) hbl hacc hpw hpos hrq (e.2.1 - 1) 0
    (by omega)
  rw [pow_zero] at h
  exact ⟨_, h⟩

end
end LeanVM.Guest.B1.Whir
