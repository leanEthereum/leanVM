/-
  LeanVM.Guest.B1.Whir.QueryBits

  The positions and windows a level's decodes leave, position by position.
-/

module

public import LeanVM.Guest.B1.Whir.Squeezes

/-!
# The positions table (G:1568-1574, 848-891)

`decode_query_windows` of challenge `jj` writes positions `jj·per .. jj·per + per - 1` and their
windows (`per = 192 / depth`). `positions_of_decodes`: for every `k < q`, the position
`queriesOf … [k]` (the Spec's, `Whir/Positions.lean`) is at `qpos·g^(po + k)`, and the pointer at
`qbp·g^(po + k)` names a frame run of its windows.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

theorem testBit_chunk (W t d l : ℕ) (hl : l < d) :
    ((W >>> (t * d)) % 2 ^ d).testBit l = W.testBit (t * d + l) := by
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [hl, Nat.add_comm]

/-- **The positions table**: position `k < q` at `qpos·g^(po + k)` and its windows' pointer at
`qbp·g^(po + k)`. -/
theorem positions_of_decodes {d cd po q nsq : ℕ} (hd : 1 ≤ 192 / d) (hq : q ≤ nsq * (192 / d))
    {qpos qbp tabs : E} (ws : List E)
    (hdec : ∀ jj < nsq, MeaningDecodeQueryWindows d cd rd [ws.getD jj 0,
      qpos * gen ^ (po + jj * (192 / d)), qbp * gen ^ (po + jj * (192 / d)), tabs] []) :
    ∀ k < q, LoadHolds rd qpos (po + k) (eOfNat ((queriesOf (192 / d) d ws q).getD k 0)) ∧
      ∃ bp, LoadHolds rd qbp (po + k) bp ∧
        FrameRun rd bp (qwN d cd) fun i ↦ gen ^ qwVal d cd ((queriesOf (192 / d) d ws q).getD k 0) i := by
  intro k hk
  set per := 192 / d
  have hjj : k / per < nsq := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; exact lt_of_lt_of_le hk hq
  have ht : k % per < per := Nat.mod_lt _ (by omega)
  have hk' : po + k = po + k / per * per + k % per := by
    have := Nat.div_add_mod k per; rw [Nat.mul_comm] at this; omega
  obtain ⟨-, hall⟩ := hdec (k / per) hjj
  obtain ⟨hpos, p, hptr, hrun⟩ := hall (k % per) ht
  have hg : (queriesOf per d ws q).getD k 0 = qwPosOf d (ws.getD (k / per) 0) (k % per) := by
    simp [queriesOf, qwPosOf, List.getD_eq_getElem?_getD, hk]
  rw [hg]
  refine ⟨?_, p, ?_, hrun⟩
  · rw [hk', ← loadHolds_mul_gen_pow]; exact hpos
  · rw [hk', ← loadHolds_mul_gen_pow]; exact hptr

end
end LeanVM.Guest.B1.Whir
