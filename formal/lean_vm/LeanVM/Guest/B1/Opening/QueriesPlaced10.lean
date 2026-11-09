/-
  LeanVM.Guest.B1.Opening.QueriesPlaced10

  `opening_queries` placed, assembled: the function and its loop at the bump allocator's places.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced9

/-!
# `opening_queries`, placed, assembled

`oqMain1_placed`, `oqMain0_placed`: `opening_queries` placed at `fp` (`RelAtIn` the caller's
region `R`), of `fs name + (N + 1) + odd·fs walk + (N + 1)·fs loop + N·k·fs walk` words (`k` queries
an iteration): its chain buffer of `N + 1` words at `fp + fs name`, its odd first query's walk
after it, its loop's iteration `j` at `fp + fs name + (N + 1) + odd·fs walk + j·fs loop`, the
iterations' walks after the loop's frames, every iteration reading `R` and the chain buffer, from
the honest data of its queries (`OqIt1Ok`, `OqIt0Ok`: their windows) and of its odd first query.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The region of the loop: the caller's and the chain buffer. -/
def oqLoopR (R : ℕ → Prop) (b n : ℕ) (i : ℕ) : Prop := R i ∨ (b ≤ i ∧ i < b + n)

/-- **`opening_queries` at level 0, placed.** -/
theorem oqMain1_placed (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hpd1 : 1 ≤ s.pd) (hcd : 2 ≤ s.cd) {odd : ℕ} (hodd : odd ≤ 1)
    {name wlk loop : String} (hW : WalkFn wlk s.pd s.cd) {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbm : fm.body = oqMainT s odd wlk loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s odd wlk loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp N : ℕ} (hN : N + 1 < ordG)
    {cap flags lam lamN qptrs wp : E} (hlam : lam ≠ 0)
    {r : List K} {w : ℕ → E} {q : ℕ} {sb : List Digest} {bp hNv : E}
    (h1 : odd = 1 → LoadHolds rd qptrs 0 bp ∧
      (⟨s, 13, true, 0, r, w, q, sb, cap, flags⟩ : QD).Ok rd wp bp ∧
      LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) 0 (rowDot s.base s.I r w *
          lam⁻¹) ∧
      OqIn R (qptrs.limb 0 * Parameters.addressOfIndex 0) ∧ OqQReg R s cap flags wp bp q)
    (h0 : odd ≠ 1 → LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) 0 0)
    (hNl : LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) N hNv)
    {r1 r2 : ℕ → List K} {w1 w2 : ℕ → ℕ → E} {q1 q2 : ℕ → ℕ} {sb1 sb2 : ℕ → List Digest}
    {bp1 bp2 v : ℕ → E}
    (hit : ∀ j < N, OqIt1Ok rd (oqLoopR R (fp + fs name) (N + 1)) s odd j qptrs cap flags wp
      (ofK (Parameters.addressOfIndex (fp + fs name))) lam⁻¹
      (r1 j) (r2 j) (w1 j) (w2 j) (q1 j) (q2 j) (sb1 j) (sb2 j) (bp1 j) (bp2 j) (v j)) :
    RelAtIn coreProgram fs cert rd R (fun _ ↦ False) fp
      (fs name + (N + 1) + odd * fs wlk + ((N + 1) * fs loop + N * (2 * fs wlk)))
      name [cap, flags, lam, lamN, qptrs, wp, gen ^ N] [hNv * lamN] := by
  refine oqMain_relAtIn hP fs cert hs hpd1 hcd hodd hW hfm hpm hbm hN hlam h1 h0 hNl ?_
  by_cases hN0 : N = 0
  · subst hN0
    have : ¬ (1 + gen ^ 0 ≠ 0) := by rw [pow_zero]; simpa using e_add_self (1 : E)
    split
    · next h => exact absurd h this
    · ring
  · have hne : 1 + gen ^ N ≠ 0 := by
      intro h
      have h' : gen ^ 0 = gen ^ N := by rw [pow_zero]; exact e_add_eq_zero_iff.mp h
      have := gen_pow_inj (a := 0) (b := N) (by decide) (lt_trans (Nat.lt_succ_self N) hN) h'
      omega
    split
    · have := oqLoop1_relAtIn (fp := fp + fs name + (N + 1) + odd * fs wlk) hP fs cert hs hpd1 hcd hW
        hfl hpl hbl hlp (by omega : N < ordG) hit 0 (by omega)
      simp only [Nat.zero_mul, Nat.add_zero, Nat.sub_zero, pow_zero] at this
      exact this
    · next h => exact absurd hne h

/-- **`opening_queries` deeper, placed.** -/
theorem oqMain0_placed (hP : coreProgram.Wf) (fs : String → ℕ) (cert : String → V → ℕ)
    {s : Oq} (hs : s.RowShape) (hpd1 : 1 ≤ s.pd) (hcd : 2 ≤ s.cd) {name wlk loop : String}
    (hW : WalkFn wlk s.pd s.cd) {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbm : fm.body = oqMainT s 0 wlk loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s wlk loop) (hlp : coreProgram.loop loop = true)
    {rd : Reader} {R : ℕ → Prop} {fp N : ℕ} (hN : N + 1 < ordG)
    {cap flags lam lamN qptrs wp : E} (hlam : lam ≠ 0) {hNv : E}
    (h0 : LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) 0 0)
    (hNl : LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) N hNv)
    {r : ℕ → List K} {w : ℕ → ℕ → E} {q : ℕ → ℕ} {sb : ℕ → List Digest} {bp v : ℕ → E}
    (hit : ∀ j < N, OqIt0Ok rd (oqLoopR R (fp + fs name) (N + 1)) s j qptrs cap flags wp
      (ofK (Parameters.addressOfIndex (fp + fs name))) lam⁻¹ (r j) (w j) (q j) (sb j) (bp j)
          (v j)) :
    RelAtIn coreProgram fs cert rd R (fun _ ↦ False) fp
      (fs name + (N + 1) + 0 * fs wlk + ((N + 1) * fs loop + N * fs wlk))
      name [cap, flags, lam, lamN, qptrs, wp, gen ^ N] [hNv * lamN] := by
  refine oqMain_relAtIn (r := []) (w := fun _ ↦ 0) (q := 0) (sb := []) (bp := 0) hP fs cert hs
    hpd1 hcd (by omega) hW hfm hpm hbm hN hlam (fun h ↦ absurd h (by decide)) (fun _ ↦ h0) hNl ?_
  by_cases hN0 : N = 0
  · subst hN0
    have : ¬ (1 + gen ^ 0 ≠ 0) := by rw [pow_zero]; simpa using e_add_self (1 : E)
    split
    · next h => exact absurd h this
    · ring
  · have hne : 1 + gen ^ N ≠ 0 := by
      intro h
      have h' : gen ^ 0 = gen ^ N := by rw [pow_zero]; exact e_add_eq_zero_iff.mp h
      have := gen_pow_inj (a := 0) (b := N) (by decide) (lt_trans (Nat.lt_succ_self N) hN) h'
      omega
    split
    · have := oqLoop0_relAtIn (fp := fp + fs name + (N + 1)) hP fs cert hs hpd1 hcd hW
        hfl hpl hbl hlp (by omega : N < ordG) hit 0 (by omega)
      simp only [Nat.zero_mul, Nat.add_zero, Nat.sub_zero, pow_zero] at this
      rw [Nat.zero_mul, Nat.add_zero]
      exact this
    · next h => exact absurd hne h

end
end LeanVM.Guest.B1
