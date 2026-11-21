/-
  LeanVM.Guest.B1.Ring.CompleteB

  `ring_switch_target`, `rs_eq_run` and `ring_switch_weight` complete, placed, within a bound
  (`CompleteAtB`): their frame, their chain and their callees' words.
-/

module

public import LeanVM.Guest.B1.Ring.WeightComplete
public import LeanVM.Guest.B1.Tables.FlatAtT
public import LeanVM.Guest.B1.Terminal.KidsDepB
public import LeanVM.Core.Memory.SizeTotal
public import LeanVM.Guest.Data.NameStrings

/-!
# The ring switch, placed, within a bound

`rst_completeAtB`, `rs_completeAtB`, `rsw_completeAtB`: `rst_completeAt`, `rs_completeAt`,
`rsw_completeAt` with the size bounded before the memory (B1-c's `completeAt_flatDTB`,
`completeAt_flatOutDTB` and `completeAt_flatDepRB`, forgetting the tree's shape).
`ring_switch_target`'s only callee is a pure loop (`ring_switch_target_loop0`, called from `1`, its
end the constant `g^8`); `rs_eq_run`'s are the pure `rs_eq_run_loop0` and `rs_eq_rows__L{r}`,
whose words are hypotheses (`TotalLeOn`, `TotalLe`, fs-generic); `ring_switch_weight`'s is
`rs_eq_run`, which returns its chain.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Core.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`ring_switch_target` is complete, placed, within `fs "ring_switch_target" + 72 + B14`**: its
frame, its chain (`72` words) and `ring_switch_target_loop0`'s words, at most `B14` when called from
`1`
(`hl14`). -/
theorem rst_completeAtB (κ : ℕ) {bs bm : ℕ} {s chs : List E} (hs : s.length = 64)
    (hc : chs.length = 16) {B14 : ℕ}
    (hl14 : TotalLeOn coreProgram fs name% «ring_switch_target_loop0» (fun a => a.getD 0 0 = 1) fun
        _ => B14) :
    CompleteAtB fs cert κ "ring_switch_target" [(bs, s), (bm, chs)]
      [ofK (Parameters.addressOfIndex bs), ofK (Parameters.addressOfIndex bm)]
      (Returns [ringTarget s (chs.take ringMapWidth) (chs.drop ringMapWidth)])
      (fs "ring_switch_target" + 72 + B14) := by
  have e : fs "ring_switch_target" + 72 + B14 = fs "ring_switch_target" + [72].sum + B14 := by simp
  rw [e]
  refine B1.CompleteAtDTB.toCompleteAtB (completeAt_flatDTB (fs := fs) (cert := cert) find_rst
    rst_not_loop κ _ _ _ rst_body' rst_flat rst_addrs [72] (fun _ ↦ [chainWords s (chs.drop 8)])
    (fun _ ↦ by simp [chainWords_length])
    (fun fp ↦ [⟨name% «ring_switch_target_loop0», true, [1, ofK (Parameters.addressOfIndex bm),
      ofK (Parameters.addressOfIndex bs), ofK (Parameters.addressOfIndex (fp + fs "ring_switch_target"))],
      l13Lin bs bm (fp + fs "ring_switch_target") s chs, Returns []⟩])
    (fun _ => True) [fun _ => True] [B14] B14 ?_ (fun _ => by simp [kidsBoundL]) (fun _ => le_rfl)
    ?_ ?_ ?_)
  · -- the loop, placed, within `B14`
    intro fp
    refine ⟨fun _ => ?_, trivial⟩
    exact completeAtDTB_of_relIn l13_pure (List.mem_singleton_self _)
      (fun rd t rets' hn hv hb => hl14 rd t _ rets' hn rfl hv hb)
      fun rd _ hL ↦ l13_relIn_lin hs hc hL
  · -- the loop's words: the caller's and the chain
    intro fp k hk _ i hi
    rw [List.mem_singleton] at hk
    subst hk
    obtain ⟨q, hq, hi⟩ := hi
    simp only [l13Lin, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact Or.inl ⟨_, by simp, hi⟩
    · exact Or.inl ⟨_, by simp, hi⟩
    · exact Or.inr ⟨_, by simp [bufL, bases], hi⟩
  · intro fp rd hB hLin k hk
    rw [List.mem_singleton] at hk
    subst hk
    intro q hq
    simp only [l13Lin, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact hLin (bs, s) (by simp)
    · exact hLin (bm, chs) (by simp)
    · exact hB (fp + fs "ring_switch_target", chainWords s (chs.drop 8)) (by simp [bufL, bases])
  · -- the honest valuation
    intro fp outs ho rd _ hB hLin
    rcases outs with _ | ⟨o, _ | ⟨o', os⟩⟩
    · exact absurd ho (by simp [OutsOk])
    swap
    · exact absurd ho.2 (by simp [OutsOk])
    obtain ⟨ho', -⟩ := ho
    obtain ⟨ho1, -⟩ := ho' rfl
    obtain ⟨σ, h1, h2, h3, h4, h5, h6, h7⟩ := rst_hσ hs hc fp rd hB hLin o ho1
    exact ⟨σ, h1, h2, h3, h4, h5, h6, h7, trivial⟩


/-- **`rs_eq_run` is complete, placed, within `fs "rs_eq_run" + 64 · (count / 8 + 2) +
(fs "rs_eq_run_loop0" + count / 8 · K6 + R)`**: its frame, its chain and its callees' words,
`rs_eq_run_loop0`'s run within `K6` an iteration and its one phantom frame (`h6`), the remainder's
`rs_eq_rows__L{r}` within `R` (`hR`). -/
theorem rs_completeAtB (κ : ℕ) {bz bp count : ℕ} {zs ps : List E} (hcount : count < 64)
    (hz : zs.length = count) (hp : ps.length = count) {K6 R : ℕ}
    (h6 : TotalLeOn coreProgram fs name% «rs_eq_run_loop0» LoopPre
      fun a ↦ logG (a.getD 1 0) * K6 + fs name% «rs_eq_run_loop0»)
    (hR : ∀ r < 8, TotalLe coreProgram fs (rsEqRowsNames.getD r "") fun _ ↦ R) :
    CompleteAtB fs cert κ "rs_eq_run" [(bz, zs), (bp, ps)]
      [ofK (addressOfIndex bz), ofK (addressOfIndex bp), gen ^ count] (RsOut zs ps count)
      (fs "rs_eq_run" + rsSize count + (fs name% «rs_eq_run_loop0» + count / 8 * K6 + R)) := by
  have e : fs "rs_eq_run" + rsSize count + (fs name% «rs_eq_run_loop0» + count / 8 * K6 + R) =
      fs "rs_eq_run" + [rsSize count].sum + (fs name% «rs_eq_run_loop0» + count / 8 * K6 + R) := by
    simp
  rw [e]
  refine B1.CompleteAtDTB.toCompleteAtB (completeAt_flatOutDTB (fs := fs) (cert := cert)
    find_rs_eq_run rs_not_loop κ _ _
    (fun fp ↦ [ofK (addressOfIndex (fp + fs "rs_eq_run")) * gen ^ (64 * rswH count)]) _ rs_body'
    rs_flat rs_addrs [rsSize count] (fun _ ↦ [rswChain zs ps count])
    (fun _ ↦ by simpa using rswChain_le_size zs ps count)
    (fun fp ↦ ⟨_, rfl, bufL_rs _ _ _ _⟩)
    (fun fp ↦ rsKids (fp + fs "rs_eq_run") bz bp count zs ps) (fun _ => True)
    [fun _ => True, fun _ => True] [fs name% «rs_eq_run_loop0» + count / 8 * K6, R]
    (fs name% «rs_eq_run_loop0» + count / 8 * K6 + R) (fun fp ↦ ?_) (fun fp ↦ ?_)
    (fun _ ↦ le_rfl) ?_ ?_ ?_)
  · -- the callees, within their bounds
    refine ⟨fun ht ↦ ?_, fun _ ↦ ?_, trivial⟩
    · simp only [decide_eq_true_eq] at ht
      have hq0 : 0 < count / 8 := by
        rcases Nat.eq_zero_or_pos (count / 8) with h0 | h0
        · exfalso; apply ht; rw [h0, pow_zero]; exact Core.Value.e_add_self 1
        · exact h0
      exact (completeAt_of_rel_pureBat rs_pure (by simp [rsPureNames])
        (fun rd hL ↦ (rs_kids_rel hcount (rsMem_of hz hp hL)).1.2 ht) κ
        fun rd t hn hv hb ↦ by
          have := h6 rd t _ [] hn (loopPre_gen hq0 (by omega) _) hv hb
          simp only [List.getD_cons_succ, List.getD_cons_zero] at this
          rw [Core.Value.gen_pow_eq_ofK, logG_spec (show count / 8 < 2 ^ 64 - 1 by omega)] at this
          simpa [Nat.add_comm] using this).toDTB
    · exact (completeAt_of_rel_pureBat rs_pure (rows_mem_pure _ (by omega))
        (fun rd hL ↦ (rs_kids_rel hcount (rsMem_of hz hp hL)).2) κ
        fun rd t hn hv hb ↦ hR (count % 8) (by omega) rd t _ _ hn hv hb).toDTB
  · -- the callees' words
    simp only [kidsBoundL, rsKids, List.headD_cons, List.tail_cons, add_zero, ↓reduceIte]
    split <;> omega
  · intro fp k hk _ i hi
    rw [bufL_rs]
    exact rs_kids_region ⟨by simp, by simp⟩ k hk i hi
  · intro fp rd hB hLin
    rw [bufL_rs] at hB
    exact rs_kids_mem ⟨by simp, by simp⟩ hB hLin
  · intro fp outs ho rd _ hB hLin
    rw [bufL_rs] at hB ⊢
    have hL : MemL rd (rsLin (fp + fs "rs_eq_run") bz bp count zs ps) := by
      intro q hq
      simp only [rsLin, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      exacts [hB _ (by simp), hLin _ (by simp), hLin _ (by simp)]
    obtain ⟨σ, h1, h2, h3, h4, h5, h6, h7⟩ := rs_hσ hcount hz hp ho hL
    refine ⟨σ, h1, h2, h3, h4, by rw [h5]; simp [bases], h6, fun q hq ↦ ?_, trivial⟩
    obtain ⟨i, hi, hr⟩ := h7 q hq
    exact ⟨i, hi, Or.inr hr⟩

/-- **`ring_switch_weight` is complete, placed, within `fs "ring_switch_weight" + Brs`**: its frame
and `rs_eq_run`'s words, its chain included, at most `Brs` on `count` coordinates (`rs_completeAtB`:
`Brs = fs "rs_eq_run" + 64 · (count / 8 + 2) + (fs "rs_eq_run_loop0" + count / 8 · K6 + R)`). -/
theorem rsw_completeAtB (κ : ℕ) {bz bp bc count : ℕ} {zs ps cs : List E} (hcount : count < 64)
    (hz : zs.length = count) (hp : ps.length = count) (hc : cs.length = 64) {K6 R : ℕ}
    (h6 : TotalLeOn coreProgram fs name% «rs_eq_run_loop0» LoopPre
      fun a ↦ logG (a.getD 1 0) * K6 + fs name% «rs_eq_run_loop0»)
    (hR : ∀ r < 8, TotalLe coreProgram fs (rsEqRowsNames.getD r "") fun _ ↦ R) :
    CompleteAtB fs cert κ "ring_switch_weight" [(bz, zs), (bp, ps), (bc, cs)]
      [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^ count]
      (Returns [ringWeight zs (ps.map (1 + ·)) cs])
      (fs "ring_switch_weight" + (fs "rs_eq_run" + rsSize count +
        (fs name% «rs_eq_run_loop0» + count / 8 * K6 + R))) := by
  have e : fs "ring_switch_weight" + (fs "rs_eq_run" + rsSize count +
      (fs name% «rs_eq_run_loop0» + count / 8 * K6 + R)) =
      fs "ring_switch_weight" + ([] : List ℕ).sum + [fs "rs_eq_run" + rsSize count +
        (fs name% «rs_eq_run_loop0» + count / 8 * K6 + R)].sum := by simp
  rw [e]
  refine completeAt_flatDepRB (fs := fs) (cert := cert) find_rsw rsw_not_loop κ _ _ _ rsw_body'
    rsw_flat rsw_addrs rsw_notIte [] (fun _ ↦ []) (fun _ ↦ List.Forall₂.nil)
    (fun _ ↦ [rswKid bz bp count zs ps]) _ (fun _ ↦ ⟨fun _ ↦ ⟨fun _ ↦
      rs_completeAtB κ hcount hz hp h6 hR, fun h ↦ absurd h (by simp [rswKid])⟩, trivial⟩)
    (fun _ outs _ ↦ rsw_regions (fun i h ↦ Or.inl h) outs)
    (fun _ outs _ rd _ _ hLin _ ↦ rsw_lins hLin outs)
    (fun _ outs hl ho rd _ _ hLin hLo ↦ ?_)
  obtain ⟨σ, h1, h2, h3, h4, h5, h6, h7⟩ := rsw_hσ hcount hz hp hc outs hl ho hLin hLo
  refine ⟨σ, h1, h2, h3, h4, h5, h6, fun q hq ↦ ?_⟩
  obtain ⟨i, hi, h | h⟩ := h7 q hq
  · exact ⟨i, hi, Or.inl h⟩
  · exact ⟨i, hi, Or.inr (Or.inr h)⟩

end
end LeanVM.Guest.B1.VerifySub
