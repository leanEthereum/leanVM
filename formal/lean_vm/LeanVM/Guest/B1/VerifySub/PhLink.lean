/-
  LeanVM.Guest.B1.VerifySub.PhLink

  `verify_sub`'s link phase, sound: its words run `verifyLink` with the fresh claim's split, `rm`
  is the next squeeze, and the link's end is as the later phases read it.
-/

module

public import LeanVM.Guest.B1.VerifySub.PhLinkSpine
public import LeanVM.Guest.B1.VerifySub.PhLinkFacts
public import LeanVM.Guest.B1.VerifySub.PhLinkEnd
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

/-!
# The link phase

`phLink : PhLink`. The transcript (`VsRun.linkRun`, `PhLinkSpine.lean`) runs `verifyLink` from
`vsF3` to `lkEnd` once the index side's claim is `indexClaim` and the terminal check holds; the
section's facts (`vsLinkFactsOfRun`, `PhLinkFacts.lean`) give the link arithmetic's hypotheses,
so `readsOfFacts` and `linkSecStatement` give the claim and `terminalOfFacts` the check. The end's
columns and pieces are the concrete tables' (`PhLinkEnd.lean`), its memory term's scale `below_mem`
the section's (`IRReads`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Link
open LeanVM.Guest.B1.Link LeanVM.Guest.B1.Link.Arith

@[expose] public section

theorem lkReadsAt_range_map {rd : Reader} {p : E} {n : ℕ} {g : ℕ → E}
    (h : ∀ k < n, LoadHolds rd p k (g k)) : ReadsAt rd p ((List.range n).map g) := by
  intro k hk
  simp only [List.length_map, List.length_range] at hk
  simp only [List.getElem_map, List.getElem_range]
  exact h k hk

theorem loadHolds_getD {rd : Reader} {p : E} {l : List E} (h : ReadsAt rd p l) {k : ℕ}
    (hk : k < l.length) : LoadHolds rd p k (l.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

set_option maxHeartbeats 2000000 in
/-- **The link phase**, sound. -/
theorem phLink : PhLink := by
  intro bytecode κ L C V σ rets R
  have Sh := R.shapeOk
  obtain ⟨c, p, r, chi, qPoint, message, hc, hcg, hp, hd2, hr, hrl, hchi, hchil, hq, hql, hm, hml,
    hsq, hrun⟩ := R.linkRun
  obtain ⟨hA, hTS, hLF, hTF⟩ :=
    vsLinkFactsOfRun bytecode L C V σ rets c p r chi qPoint message R Sh hc hcg hp hd2 hr hrl hchi
      hchil hq hql hm hml
  have hIR := readsOfFacts L.read σ _ c _ _ r _ _ _ chi qPoint message p hA hTS Sh.logBc hLF
  have hSec := linkSecStatement L.read σ _ c _ _ r _ _ _ chi qPoint message hA hIR hTS Sh.logBc
  have hTail := terminalOfFacts L.read σ _ c _ _ r _ _ _ chi qPoint message p (σ (.n 1077)) hA hTS
    Sh.logBc hLF hTF
  obtain ⟨xs, hxs, hcur, hlink⟩ := hrun hSec.1 hTail
  -- the cursor past the link
  have hK := R.slice vsKeccakT_eq
  simp only [vsKeccakT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hK
  obtain ⟨-, -, k2909, k2910, k2911, k2912, -⟩ := hK
  have hlen80 : tailNValues (vsLayout bytecode σ) = 80 := tailNValues_tables Sh.tablesEq
  refine ⟨xs, _, _, hxs, ?_, hlink, hsq, r, chi, qPoint, hr, ?_, ?_, hchi, ?_, ?_, ?_, hql, ?_, rfl,
    ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show σ (.n 2910) = _
    rw [k2910, k2909, word_g144, hcur]
  · have := Sh.widthGe; rw [hrl]; exact this
  · have := Sh.logMemoryLe; rw [hrl]; exact this
  · rw [hchil]; exact Sh.gN
  · intro t ht; rw [hchil]; exact Sh.heightsLe t ht
  · -- `eq_q`
    have heq := eqqAt hA hql (fun t ht ↦ by rw [Nat.zero_add]; exact loadHolds_getD hq (by omega))
    intro k hk
    simp only [List.length_take, length_eqKernel, hql] at hk
    rw [List.getElem_take, ← List.getD_eq_getElem _ 0, loadHolds_mul_gen_pow]
    exact heq k (by omega)
  · -- the sent values
    show ReadsAt L.read (σ (.n 1076)) ((tailRowSide (vsLayout bytecode σ) c _ _ r _ _ _ chi qPoint
      message).columns.flatMap fun c ↦ c.2.map (·.2))
    rw [end_columns_values Sh.tablesEq c _ _ r _ _ _ chi qPoint hml]
    exact lkReadsAt_range_map fun k hk ↦ loadHolds_getD hm (by omega)
  · -- the memory term's scales
    have h802 := linkAtom hA (i := 214) (a := .load (.n 802) (.n 801) 0) (by decide +kernel)
    have e := hIR.belowMem
    rw [rdw_of_load h802] at e
    show (_, _) = (σ (.n 802), eY * σ (.n 802))
    rw [e]
    rfl
  · exact end_pieces Sh.tablesEq c _ _ r _ _ _ chi qPoint hml
  · show ReadsAt L.read (σ (.n 1076) * gen ^ 80) (message.drop (tailNValues (vsLayout bytecode σ)))
    rw [hlen80]
    intro k hk
    rw [loadHolds_mul_gen_pow, List.getElem_drop]
    exact hm _ (by simp at hk; omega)
  · show (message.drop (tailNValues (vsLayout bytecode σ))).length = 64
    rw [hlen80, List.length_drop, hml]
  · exact end_columns_shape Sh.tablesEq c _ _ r _ _ _ chi qPoint hml
  · exact end_keccak_point Sh.tablesEq c _ _ r _ _ _ chi qPoint hml
  · refine ⟨_, end_keccak Sh.tablesEq c _ _ r _ _ _ chi qPoint hml, ?_, by simp [keccakStateLanes]⟩
    show ReadsAt L.read (σ (.n 2912)) _
    rw [k2912, k2911, show (36028797018963968 : ℕ) = 2 ^ 55 from rfl, word_two_pow (by norm_num)]
    refine lkReadsAt_range_map fun k hk ↦ ?_
    rw [loadHolds_mul_gen_pow]
    exact loadHolds_getD hm (by omega)

end
end LeanVM.Guest.B1.VerifySub
