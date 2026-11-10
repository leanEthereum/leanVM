/-
  LeanVM.Guest.B1.Tables.VtC.ABc

  The slot sumcheck's honest values two ways: the specification's (`AHon`'s `bcRec`) and the
  guest's tail rounds (`BBc`'s `vtBcR1 .. vtBcR3`) agree.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.AHon
public import LeanVM.Guest.B1.Tables.VtC.BBc

/-!
# The slot sumcheck, two ways

`vt_bc_sumcheck`: the guest's rounds (`bcRound` on the share's sponge) are a run of the
specification's `sumcheck _ 3`. `vt_bc_honest`: from a carried sponge, by determinism against
`bc_run`, the specification's slot point, final claim and closing sponge are the guest's.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **The guest's slot rounds are the specification's sumcheck.** -/
theorem vt_bc_sumcheck (F0 : Fs) (w : List E) (hwl : w.length = 10) :
    RunsTo (sumcheck (w.getD 0 0) 3 (List.replicate busBits none))
      (F0.absorb (w.getD 0 0) dsObserve)
      ([w.getD 1 0, w.getD 2 0] ++ ([w.getD 3 0, w.getD 4 0] ++ ([w.getD 5 0, w.getD 6 0] ++
        ([w.getD 7 0, w.getD 8 0] ++ []))))
      (vtBcPoint F0 w, (vtBcR3 F0 w).2.1) ⟨(vtBcR3 F0 w).1, []⟩ := by
  have sq : ∀ s : Fs, s.squeeze.2 = ⟨s.squeeze.2.cap, []⟩ := fun s ↦ rfl
  have hR4 := runsTo_sumcheck_nil (⟨(vtBcR3 F0 w).1, []⟩ : Fs) (vtBcR3 F0 w).2.1 3
  have hR3 := vt_tail_cons (vtBcR2 F0 w).1 (w.getD 7 0) (w.getD 8 0) (vtBcR2 F0 w).2.1
    (rest := []) (ys := []) (pt := []) (fin := (vtBcR3 F0 w).2.1)
    (s2 := ⟨(vtBcR3 F0 w).1, []⟩) (by rw [sq]; exact hR4)
  have hR2 := vt_tail_cons (vtBcR1 F0 w).1 (w.getD 5 0) (w.getD 6 0) (vtBcR1 F0 w).2.1
    (by rw [sq]; exact hR3)
  have hR1 := vt_tail_cons (vtBcF F0 w).squeeze.2.cap (w.getD 3 0) (w.getD 4 0) (vtBcCl1 F0 w)
    (by rw [sq]; exact hR2)
  have hF : ((F0.absorb (w.getD 0 0) dsObserve).absorb (w.getD 1 0) dsObserve).absorbAll
      [w.getD 2 0] dsObserve = vtBcF F0 w := by
    rw [vtBcF, vt_list10 w hwl]
    simp [Fs.absorbAll]
  have hR0 := runsTo_sumcheck_cons
    (runsTo_roundPolyNone (F0.absorb (w.getD 0 0) dsObserve) (w.getD 0 0) (w.getD 1 0)
      [w.getD 2 0] 3 rfl (by decide))
    (by rw [hF, sq, ← tail_eval]; exact hR1)
  rw [hF] at hR0
  refine RunsTo.of_eq hR0 rfl rfl ?_ rfl
  simp only [vtBcPoint, vtBcR0, vtBcR1, vtBcR2, vtBcR3, bcRound]

theorem bcWs_eq {w : List E} (hwl : w.length = 10) :
    bcWs w = [w.getD 1 0, w.getD 2 0] ++ ([w.getD 3 0, w.getD 4 0] ++ ([w.getD 5 0, w.getD 6 0] ++
      ([w.getD 7 0, w.getD 8 0] ++ []))) := by
  match w, hwl with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9], _ => rfl

/-- **The specification's slot sumcheck is the guest's**: its point, final claim and closing
sponge. -/
theorem vt_bc_honest {s : Fs} (hc : ∃ sp, s.Carries sp) {w : List E} (hwl : w.length = 10) :
    bcSlots s w = vtBcPoint s w ∧ bcClaim s w = (vtBcR3 s w).2.1 ∧
      bcEnd s w = (⟨(vtBcR3 s w).1, []⟩ : Fs).absorb (w.getD 9 0) dsObserve := by
  have c1 := RunsTo.carries (runsTo_readE s (w.getD 0 0)) hc
  have h1 := bc_run (bcS0 s w) (w.getD 0 0) (bcWs_length hwl)
  have h2 := vt_bc_sumcheck s w hwl
  rw [← bcWs_eq hwl] at h2
  obtain ⟨e1, e2, -⟩ := runsTo_det h1 h2 c1 (r1 := []) (r2 := []) rfl
  simp only [Prod.mk.injEq] at e1
  refine ⟨e1.1, e1.2, ?_⟩
  unfold bcEnd
  rw [e2]

end
end LeanVM.Guest.B1.Tables
