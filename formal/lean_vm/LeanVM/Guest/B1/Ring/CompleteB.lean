/-
  LeanVM.Guest.B1.Ring.CompleteB

  `ring_switch_target` and `ring_switch_weight` complete, placed, within a bound (`CompleteAtB`):
  their frame, their chain and their loop's or `rs_eq_run`'s words.
-/

module

public import LeanVM.Guest.B1.Ring.WeightComplete
public import LeanVM.Guest.B1.Tables.FlatAtT
public import LeanVM.Guest.B1.KeccakGkr.FlatGB
public import LeanVM.Guest.Memory.SizeTotal
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«ring_switch_weight»

/-!
# The ring switch, placed, within a bound

`rst_completeAtB`, `rsw_completeAtB`: `rst_completeAt`, `rsw_completeAt` with the size bounded
before the memory. `ring_switch_target`'s only callee is a pure loop, `ring_switch_target_loop0`
called from `1` (its end the constant `g^8`), whose words are a hypothesis (`TotalLeOn`,
fs-generic; B1-c's `completeAt_flatDTB`, forgetting the tree's shape); `ring_switch_weight`'s is
`rs_eq_run` on `count ≤ 34` coordinates, within `Brs` (`rs_completeAtB`, `completeAt_flatGB`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
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


/-- **`ring_switch_weight` is complete, placed, within
`fs "ring_switch_weight" + 64 · (count + 1) + Brs`**: its frame and `rs_eq_run`'s words, at most
`Brs` on `count ≤ 34` coordinates (`rs_completeAtB`, the callees' words as `RsBound` says). -/
theorem rsw_completeAtB (κ : ℕ) {bz bp bc count : ℕ} {zs ps cs : List E} (hc34 : count ≤ 34)
    (hz : zs.length = count) (hp : ps.length = count) (hc : cs.length = 64) {Brs : ℕ}
    (hrs : RsBound fs Brs) :
    CompleteAtB fs cert κ "ring_switch_weight" [(bz, zs), (bp, ps), (bc, cs)]
      [ofK (addressOfIndex bz), ofK (addressOfIndex bp), ofK (addressOfIndex bc), gen ^ count]
      (Returns [ringWeight zs (ps.map (1 + ·)) cs])
      (fs "ring_switch_weight" + 64 * (count + 1) + Brs) := by
  refine (completeAt_flatGB (fs := fs) (cert := cert) find_rsw rsw_not_loop κ _ _ _ rsw_body' rsw_flat
    rsw_addrs rsw_noLoadIte [] (fun _ _ ↦ []) (fun _ _ ↦ .nil)
    (fun _ ↦ [rswKid bz bp count zs ps]) [Brs] Brs
    (fun _ ↦ ⟨fun _ _ ↦ (rs_completeAtB κ hc34 hz hp hrs).toFB, trivial⟩)
    (fun _ ↦ by simp [kidsGBound, rswKid]) ?_).mono le_rfl (by simp only [List.sum_nil, add_zero]; omega)
  intro fp fps outs hl _ ho rd _ _ hLin hto
  obtain ⟨h1, h2, σ, h3, h4, h5, h6, h7⟩ := rsw_hσ hz hp hc fps outs hl ho rd hLin hto
  refine ⟨h1, regionsOk_mono (fun i h ↦ Or.inl h) h2, σ, h3, h4, h5, by rw [rsw_allocs]; rfl,
    by rw [rsw_allocs]; rfl, h6, fun q hq ↦ ?_⟩
  obtain ⟨i, hi, h | h⟩ := h7 q hq
  · exact ⟨i, hi, Or.inl h⟩
  · exact ⟨i, hi, Or.inr (Or.inr h)⟩

end
end LeanVM.Guest.B1.VerifySub
