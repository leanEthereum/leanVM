/-
  LeanVM.Guest.B1.VsC.VsHonBwF

  The honest buffers' facts: their sizes, `BwFs`, `Bw1`, `Ret1`'s constants, `BwNat`.
-/

module

public import LeanVM.Guest.B1.VsC.VsHonRet

/-!
# The honest buffers' facts

At `y := x.honCtx N ec bp bp1` with `x.Ok` and `N.Ok x.seed x.c`: the sizes (`honCtx_hbw`), `BwFs`, `Bw1`, `Ret1`'s
constants and `r680`, `BwNat y N.L`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Link LeanVM.Guest.B1.Stack
open LeanVM.Guest.B1.Link (pkSqueeze pkSqueeze_length)
open LeanVM.Prover.Exec (allocBase)
open LeanVM.Guest.B1.VerifySub (qkeccakVarsCap keccakTauMin keccakTauMax)

@[expose] public section

attribute [local semireducible] VsCtx.lay

/-- A block list's word `n t + k` is block `t`'s word `k`, every block of `n` words. -/
theorem flatMap_range_getElem? {f : ℕ → List E} {n : ℕ} :
    ∀ m, (∀ t < m, (f t).length = n) → ∀ t k, t < m → k < n →
      ((List.range m).flatMap f)[n * t + k]? = (f t)[k]?
  | 0, _, _, _, ht, _ => absurd ht (Nat.not_lt_zero _)
  | m + 1, hf, t, k, ht, hk => by
    have hl : ((List.range m).flatMap f).length = n * m := by
      rw [List.length_flatMap]
      have : ∀ m', m' ≤ m → ((List.range m').map fun a => (f a).length).sum = n * m' := by
        intro m' hm'
        induction m' with
        | zero => rfl
        | succ q ih =>
          rw [List.range_succ, List.map_append, List.sum_append, ih (by omega), List.map_singleton,
            List.sum_singleton, hf q (by omega), Nat.mul_succ]
      exact this m le_rfl
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_or_ge t m with h | h
    · rw [List.getElem?_append_left (by rw [hl]; nlinarith),
        flatMap_range_getElem? m (fun t' h' => hf t' (by omega)) t k h hk]
    · have e : t = m := by omega
      subst e
      rw [List.getElem?_append_right (by rw [hl]; omega), hl, Nat.add_sub_cancel_left]

theorem padTo_getElem? {n k : ℕ} {l : List E} (hk : k < l.length) : (padTo n l)[k]? = l[k]? :=
  List.getElem?_append_left hk


/-- The context's numbers from the child (`frontNum_of_child`), without `Hon`. -/
theorem ctx_nums (x : VsCtx) (hok : x.Ok) :
    19 ≤ x.wdS ∧ x.wdS ≤ 24 ∧ x.nS ≤ 24 ∧ (∀ t < 6, x.hg t ≤ 24) ∧
      (padStream x.c.proof.stream).length = 256 * x.p ∧ x.p ≤ 32 := by
  obtain ⟨layout, r, hann, -, hN⟩ := frontNum_of_child hok.child
  have hl : x.lay = layout := VsCtx.lay_of hann
  obtain ⟨t, ht, he⟩ := hN.hn
  refine ⟨?_, ?_, ?_, fun t ht => ?_, hN.hws, hN.hp⟩
  · show 19 ≤ widthOf x.lay; rw [hl]; exact hN.hw19
  · show widthOf x.lay ≤ 24; rw [hl]; exact hN.hw24
  · show hMax x.lay ≤ 24; rw [hl, ← he]; exact hN.h24 t ht
  · show x.lay.tableLogHeights.getD t 0 ≤ 24; rw [hl]; exact hN.h24 t ht

theorem honSqN_length : ∀ (n : ℕ) (s : Fs), (s.squeezeN n).1.length = n
  | 0, _ => rfl
  | n + 1, s => by simp only [Fs.squeezeN, List.length_cons, honSqN_length n]

theorem honB4_length (x : VsCtx) (hok : x.Ok) : x.honB4.length = 153 := by
  obtain ⟨h19, h24, hn, -⟩ := ctx_nums x hok
  have hc := chal_fits hn h19 h24
  have h153 : guest_const% LINK_CHAL_CAP = 153 := rfl
  rw [h153] at hc
  unfold VsCtx.honB4
  refine padTo_length ?_
  rw [List.length_cons, pkSqueeze_length]
  exact hc

namespace VsCtx

section
variable {x : VsCtx} {N : NatOpen} {ec : ℕ → ℕ} {bp bp1 : ℕ}

/-- A word `ret` fixes to a constant, at the honest context. -/
theorem honCtx_w {i : ℕ} (hi : vsPlain i) {v : E} (hv : ∀ σ, (x.honCtx N ec bp bp1).ret i σ = v) :
    (x.honCtx N ec bp bp1).w i = v :=
  vsW_retC rfl honCtx_hret hi hv

theorem honCtx_w573 : ∀ j < 8, (x.honCtx N ec bp bp1).w (573 + j) = x.omN.getD j 0 := by
  intro j hj
  exact honCtx_w (by interval_cases j <;> decide) (honCtx_retFs.r573 j hj)

theorem honCtx_w680 : ∀ j < 5, (x.honCtx N ec bp bp1).w (680 + j) =
    (pkSqueeze x.pk [x.omN.getD 2 0, x.omN.getD 3 0, x.omN.getD 4 0, x.omN.getD 5 0, x.omN.getD 6 0]).2.getD j 0 := by
  intro j hj
  exact honCtx_w (by interval_cases j <;> decide) (honCtx_r680 j hj)

theorem honCtx_w575 : [(x.honCtx N ec bp bp1).w 575, (x.honCtx N ec bp bp1).w 576, (x.honCtx N ec bp bp1).w 577,
    (x.honCtx N ec bp bp1).w 578, (x.honCtx N ec bp bp1).w 579] =
    [x.omN.getD 2 0, x.omN.getD 3 0, x.omN.getD 4 0, x.omN.getD 5 0, x.omN.getD 6 0] := by
  rw [honCtx_w573 2 (by omega), honCtx_w573 3 (by omega), honCtx_w573 4 (by omega), honCtx_w573 5 (by omega),
    honCtx_w573 6 (by omega)]

theorem honCtx_b3 : vsLinkShape x.lay =
    [gen ^ hMax x.lay, gen ^ widthOf x.lay, flagOf x.lay, (vsLinkShape x.lay).getD 3 0] := by
  have e : x.lay.tableRows.sum = cyclesOf x.lay := by unfold cyclesOf; exact List.sum_eq_foldl
  unfold vsLinkShape
  rw [e]
  rfl

variable (hN : N.Ok x.seed x.c)
include hN

theorem lay_heights_length : x.lay.tableLogHeights.length = 6 := by
  rw [VsCtx.lay_nat hN, hN.shape.heights]
  simp [hN.shape.rows_length, tableLogFloors]; decide

omit hN in
theorem honCtx_bwFs : (x.honCtx N ec bp bp1).BwFs := by
  refine ⟨fun k hk => ?_, rfl⟩
  show (padTo 30 (natOodZ x.seed x.c x.lay.stackLog))[k]? = _
  exact padTo_getElem? hk

theorem honCtx_b0 : heightsW (x.honCtx N ec bp bp1).hg = x.lay.tableLogHeights.map Prover.count := by
  have hl := lay_heights_length hN
  show heightsW (fun t => x.lay.tableLogHeights.getD t 0) = _
  generalize x.lay.tableLogHeights = l at hl
  match l, hl with
  | [a0, a1, a2, a3, a4, a5], _ => rfl


end

end VsCtx

end
end LeanVM.Guest.B1.VsC
