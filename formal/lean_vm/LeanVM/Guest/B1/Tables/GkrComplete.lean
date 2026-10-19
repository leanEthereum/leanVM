/-
  LeanVM.Guest.B1.Tables.GkrComplete

  `verify_bus_gkr`'s loops backward: from the honest words in memory, each loop's relation.
-/

module

public import LeanVM.Guest.B1.Tables.Gkr
public import LeanVM.Guest.B1.Main.LoopsC

/-!
# `verify_bus_gkr`'s loops, backward

`__loop11` copies the final point row into `zeta`: it holds once every iteration's two cells hold
one word (`loop11_complete`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

theorem loop11_back {gmu zeta row : E} (d j : ℕ) (hK : IsInK (gen ^ j * gen + gmu)) {v : E}
    (hr : LoadHolds rd (row * gen ^ j) 0 v) (hz : LoadHolds rd (zeta * gen ^ j) 0 v)
    (hnext : gen ^ j * gen + gmu ≠ 0 →
      coreProgram.relN rd d "__loop11" [gen ^ j * gen, gmu, zeta, row] []) :
    coreProgram.relN rd (d + 1) "__loop11" [gen ^ j, gmu, zeta, row] [] := by
  set x := gen ^ j
  rw [relN_succ_iff find_loop11]
  refine ⟨setl (Val.ofArgs [x, gmu, zeta, row]) 4 [row * x, v, zeta * x, gen, x * gen,
    x * gen + gmu, gen, x * gen], by
      simp only [show Fn.params Data.core41 = [.n 0, .n 1, .n 2, .n 3] from rfl, List.map_cons,
        List.map_nil]; b1_look, ?_⟩
  simp only [show Fn.body Data.core41 = Data.core41.body from rfl, Data.core41.body,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen]
  b1_look
  simp only [true_and, and_true]
  exact ⟨hr, hz, hK, hnext⟩

/-- **`__loop11`** copies `m` words from the row into `zeta`. -/
theorem loop11_complete {zeta row : E} {m : ℕ} (hm0 : 0 < m)
    (hB : ∀ j < m, ∃ v, LoadHolds rd (row * gen ^ j) 0 v ∧ LoadHolds rd (zeta * gen ^ j) 0 v) :
    coreProgram.Rel rd "__loop11" [1, gen ^ m, zeta, row] [] :=
  Main.loop_complete (B := fun j => ∃ v, LoadHolds rd (row * gen ^ j) 0 v ∧
      LoadHolds rd (zeta * gen ^ j) 0 v) hm0 rfl hB
    fun d j hj hK hnext => by
      obtain ⟨v, hr, hz⟩ := hj
      exact loop11_back d j hK hr hz hnext

theorem loop101_back {N rounds pos prow nrow : E} (d j : ℕ) {cv cv' : Digest}
    {cur claim e claim' rk : E}
    (h0 : LoadHolds rd (rounds * (pos * gen ^ j) ^ 4) 0 (digestScalars cv).1)
    (h1 : LoadHolds rd (rounds * (pos * gen ^ j) ^ 4) 1 (digestScalars cv).2)
    (h2 : LoadHolds rd (rounds * (pos * gen ^ j) ^ 4) 2 cur)
    (h3 : LoadHolds rd (rounds * (pos * gen ^ j) ^ 4) 3 claim)
    (he : LoadHolds rd (prow * gen ^ j) 0 e) (hrk : LoadHolds rd (nrow * gen ^ j) 2 rk)
    (h4 : LoadHolds rd (rounds * (pos * gen ^ j) ^ 4) 4 (digestScalars cv').1)
    (h5 : LoadHolds rd (rounds * (pos * gen ^ j) ^ 4) 5 (digestScalars cv').2)
    (h6 : LoadHolds rd (rounds * (pos * gen ^ j) ^ 4) 6 (cur * gen ^ 4))
    (h7 : LoadHolds rd (rounds * (pos * gen ^ j) ^ 4) 7 claim')
    (hsc : coreProgram.relN rd d "sumcheck_round5"
      [(digestScalars cv).1, (digestScalars cv).2, cur, claim, e]
      [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ 4, claim', rk])
    (hK : IsInK (gen ^ j * gen + N))
    (hnext : gen ^ j * gen + N ≠ 0 →
      coreProgram.relN rd d "__loop101" [gen ^ j * gen, N, rounds, pos, prow, nrow] []) :
    coreProgram.relN rd (d + 1) "__loop101" [gen ^ j, N, rounds, pos, prow, nrow] [] := by
  set x := gen ^ j
  have e9 : rounds * (pos * x * (pos * x) * (pos * x * (pos * x))) = rounds * (pos * x) ^ 4 := by
    ring
  rw [relN_succ_iff find_loop101]
  refine ⟨setl (Val.ofArgs [x, N, rounds, pos, prow, nrow]) 6 [pos * x, pos * x * (pos * x),
    pos * x * (pos * x) * (pos * x * (pos * x)), rounds * (pos * x * (pos * x) * (pos * x * (pos * x))),
    (digestScalars cv).1, (digestScalars cv).2, cur, claim, prow * x, e, (digestScalars cv').1,
    (digestScalars cv').2, cur * gen ^ 4, claim', rk, nrow * x, gen, x * gen, x * gen + N, gen,
    x * gen], by
      simp only [show Fn.params Data.core574 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
        List.map_cons, List.map_nil]; b1_look, ?_⟩
  simp only [show Fn.body Data.core574 = Data.core574.body from rfl, Data.core574.body,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen]
  b1_look
  simp only [true_and, and_true, e9]
  exact ⟨h0, h1, h2, h3, he, hsc, hrk, h4, h5, h6, h7, hK, hnext⟩

/-- **`__loop101`** runs `m` rounds of the layer's sumcheck from the honest round states. -/
theorem loop101_complete {rounds pos prow nrow : E} {m : ℕ} (hm0 : 0 < m)
    (hB : ∀ j < m, GkrRound rd rounds pos prow nrow (gen ^ j)) :
    coreProgram.Rel rd "__loop101" [1, gen ^ m, rounds, pos, prow, nrow] [] := by
  choose cv cur claim e ws claim' rk cv' h0 h1 h2 h3 he hwl hws hrun hrk h4 h5 h6 h7 using
    fun j (hj : j < m) => hB j hj
  have hsc : ∀ j (hj : j < m), coreProgram.Rel rd "sumcheck_round5"
      [(digestScalars (cv j hj)).1, (digestScalars (cv j hj)).2, cur j hj, claim j hj, e j hj]
      [(digestScalars (cv' j hj)).1, (digestScalars (cv' j hj)).2, cur j hj * gen ^ 4,
        claim' j hj, rk j hj] := fun j hj => by
    rw [sumcheck_round5_iff]
    obtain ⟨c1, c2, c3, c4, hc⟩ : ∃ c1 c2 c3 c4, ws j hj = [c1, c2, c3, c4] := by
      match ws j hj, hwl j hj with
      | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
    have hr := hws j hj
    have hu := hrun j hj
    rw [hc] at hr hu
    exact ⟨cv j hj, c1, c2, c3, c4, claim' j hj, rk j hj, cv' j hj, rfl, hr, hu, rfl⟩
  classical
  obtain ⟨D, hD⟩ := Main.rel_uniform (rd := rd) (F := fun _ => "sumcheck_round5")
    (A := fun j => if hj : j < m then [(digestScalars (cv j hj)).1, (digestScalars (cv j hj)).2,
      cur j hj, claim j hj, e j hj] else [])
    (R := fun j => if hj : j < m then [(digestScalars (cv' j hj)).1,
      (digestScalars (cv' j hj)).2, cur j hj * gen ^ 4, claim' j hj, rk j hj] else []) m
    fun j hj => by simp only [hj, ↓reduceDIte]; exact hsc j hj
  refine Main.loop_complete_from (D := D) (B := fun j => j < m) hm0 rfl (fun j hj => hj) ?_
  intro d j hd hj hK hnext
  have := relN_mono coreProgram hd _ _ _ (hD j hj)
  simp only [hj, ↓reduceDIte] at this
  exact loop101_back d j (h0 j hj) (h1 j hj) (h2 j hj) (h3 j hj) (he j hj) (hrk j hj) (h4 j hj)
    (h5 j hj) (h6 j hj) (h7 j hj) this hK hnext

end
end LeanVM.Guest.B1.VerifySub
