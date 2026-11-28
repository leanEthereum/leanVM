/-
  LeanVM.Guest.B1.VsC.Os.LeftPre

  `open_stacked`'s honest data at a call `OpenStackedCompleteA` takes.
-/

module

public import LeanVM.Guest.B1.VsC.Os.CHonest
public import LeanVM.Guest.B1.VsC.OpenStackedA

/-!
# The honest data at a call

`osHonest_of_open`: on `OpenStackedCompleteA`'s hypotheses (a sponge carrying the capacity
cells, the opening's accepting run, its query steps' openings agreeing), the cells are some
state's capacity and the body has its honest data (`OsHonestA`, `os_honest_proved`) at the arm `m`
and the rate `r`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

/-- **The body's honest data at a call of `open_stacked__L{m}`.** -/
theorem osHonest_of_open {m r : ℕ} {root : Digest} {fsv : List E} {target : E} {xs : List E}
    {os : List (List Opening)} {w : WhirEnd} {s' : Fs} {roots' : List (Digest × ℕ × ℕ)}
    {qs : List (ℕ × List ℕ)} (cur tabs : E) (hm : m ≤ 14) (hr1 : 1 ≤ r) (hr4 : r ≤ 4)
    (hcar : ∃ sp : Sponge, (⟨fsv, []⟩ : Fs).Carries sp)
    (hrun : RunsWith (whirOpen (minOpenLog + m) r target) ⟨fsv, []⟩ xs os
      [(root, stackShape (minOpenLog + m) r)] w s' roots')
    (hq : OpenRunQueries (minOpenLog + m) r root target ⟨fsv, []⟩ xs os qs) :
    ∃ S : KeccakState, fsv = capOf S ∧ Nonempty (OsHonestA (osCfgR m (r - 1))
      (rateSel r :: fsv ++ [target, (digestHalves root).1, (digestHalves root).2, cur, tabs])
      cur tabs xs w.target w.inner w.residual (w.point ++ List.replicate (pointCap - (minOpenLog + m)) 0)
      (w.point.map (1 + ·) ++ List.replicate (pointCap - (minOpenLog + m)) 1)) := by
  obtain ⟨⟨st, pe, gr⟩, hc, hp, hg⟩ := hcar
  change capOf st = fsv at hc
  change pe = [] at hp
  change gr = none at hg
  subst hc hp hg
  refine ⟨st, rfl, ?_⟩
  have hca : CapsAgree (minOpenLog + m) r target st xs os root := by
    intro b hb
    have h := (hq ⟨st, [], none⟩ ⟨rfl, rfl, rfl⟩ [] []).1
    simp only [List.append_nil] at h
    exact h b hb
  have h := os_honest_proved (minOpenLog + m) r (by omega) (by show 16 + m ≤ 30; omega) hr1 hr4 st root target
    cur tabs xs os w s' roots' hrun hca
  rwa [Nat.add_sub_cancel_left] at h

end
end LeanVM.Guest.B1.VsC
