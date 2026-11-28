module

public import LeanVM.Guest.Local.Hop

/-!
# A run through a nested statement passes one arm's path

The code-level counterpart of `Pos.runs_arm`. A branch or table jump at offset `u` (the nested
statement's anchor) and its join `j`: the arms' blocks `arms` tile the offsets strictly between
them (`tiles L j (u + 1) arms`, as a jump over them checks, `Hop.lean`). A run of the machine
from `u` to `j` (a list of hops, `Layout.Hops`) whose first hop does not go straight to `j`
lands in one arm `c` of the list, and passes every offset of that arm's own path
(`arm_passes`): an offset of the arm's path before its landing would be skipped by the first hop
while its block's range, the arm's, holds the landing (`Hop`); one after it is passed by
`Layout.visits`, the arm's range holding the run's first offset after `u`.

Which arm a run takes, and that it takes no other, depends on the code's jumps (the arm's exit
jumps to the join), not on the layout; a fact established on the path of the arm taken holds at
the join either way.
-/

namespace LeanVM.Guest.Local

namespace Layout

public section

variable {L : Layout}

/-- **A run from an anchor to its join passes one arm's path.** -/
theorem arm_passes (hL : L.ok = true) {u j v : ℕ} {t arms : List ℕ} (ht : tiles L j (u + 1) arms = true)
    (hh : Hops (Hop L) u (v :: t)) (hl : lastOf u (v :: t) = j) (hv : v < j) :
    ∃ c ∈ arms, ∀ w r, L.InRun r w → (L.run r).b = c → w ∈ v :: t := by
  obtain ⟨hop, hrest⟩ := hh
  obtain ⟨c, hcm, -, hc, hcs, hce⟩ := tiles_cover ht v (by have := hop.1; omega) hv
  refine ⟨c, hcm, fun w r hr hb ↦ ?_⟩
  have hw := run_range hL hr
  rw [hb] at hw
  by_cases hwv : w < v
  · have := (hop.2 w r (by have := hw.1; omega) hwv hr).2
    rw [hb] at this
    exact absurd hc this
  · have hlast : lastOf v t = j := hl
    exact visits hL hr v t hrest (by omega) (by rw [hlast]; have := hw.2; omega)
      (Or.inl (by rw [hb]; exact hc.1))

end

end Layout

end LeanVM.Guest.Local
