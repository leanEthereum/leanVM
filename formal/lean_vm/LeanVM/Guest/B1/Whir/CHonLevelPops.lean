/-
  LeanVM.Guest.B1.Whir.CHonLevelPops

  On the honest run, `level_queries`' entries at each level's honest witness are `Hints.levelHints`' for the level's phase, stream by stream.
-/

module

public import LeanVM.Guest.B1.Whir.CHonCapHints
public import LeanVM.Guest.B1.Whir.CHonFields5
public import LeanVM.Guest.B1.Merkle.LevelPopsP

/-!
# The honest run's levels pop the generator's hints

`HonRun.sameStreams`: `lq_sameStreams` at the honest witness of `os_honest_proved` (`capW`, `flW`, the positions, rows and siblings of `osHonest_run`): level `l`'s entries are `Hints.levelHints (l = 0)` of its depth, its query count and its phase.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1 LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace HonRun

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

/-- **Level `l`'s entries at the honest witness are the generator's**, stream by stream. -/
theorem sameStreams {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) :
    SameStreams (lqCapE (capW Ls μ r l) (flW Ls μ r l) ++
      oqPops (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l)
        (oqW (fun k ↦ ((Ls.getD l default).qs μ).getD k 0)
          (fun k ↦ ((Ls.getD l default).phase.map (·.leaf)).getD k [])
          (fun k ↦ ((Ls.getD l default).phase.map (fun o ↦ o.path.take
            (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).depth -
              ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).capDepth))).getD k []))
        (oqQA (osCfgR (μ - minOpenLog) (r - 1)) l))
      (Hints.levelHints (decide (l = 0)) ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).depth
        ((Ls.getD l default).qs μ).length (Ls.getD l default).phase) := by
  obtain ⟨hcdq, hpdq, -, hcdd, hQ⟩ := hR.cdpd hl
  obtain ⟨-, -, hbase, -⟩ := (hR.lvb hl).qsh
  have hidx := hR.idx hl
  have hop := hR.phase_opens hl
  have hst := hR.fld_static l hl
  have hplen : (Ls.getD l default).phase.length = ((Ls.getD l default).qs μ).length := by
    rw [← hidx, List.length_map]
  rw [hQ, ← hplen] at hst
  rw [show oqQA (osCfgR (μ - minOpenLog) (r - 1)) l = (Ls.getD l default).phase.length by rw [hQ, hplen]]
  refine lq_sameStreams (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l) ?_ (by omega)
    (by rw [← hR.capDepth_hints hl, hpdq]) (fun k hk => ?_) (fun o ho => ?_) (fun o ho => ?_) (hR.capHints hl)
  · rw [oqSA, oq_base, hbase]
    by_cases h : l = 0 <;> simp [h]
  · have hk' : k < ((Ls.getD l default).qs μ).length := by omega
    have hi : ((Ls.getD l default).qs μ).getD k 0 = ((Ls.getD l default).phase[k]).leafIndex := by
      rw [← hidx, map_getD_eq _ _ _ hk]
    simp only [oqW]
    rw [hi, map_getD_eq _ _ _ hk, map_getD_eq _ _ _ hk, hpdq]
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ho
    have := (hst k hk).2.1
    simp only at this
    rwa [map_getD_eq _ _ _ hk] at this
  · rw [(hop o ho).2, hpdq]
    omega

end HonRun

end
end LeanVM.Guest.B1.Whir
