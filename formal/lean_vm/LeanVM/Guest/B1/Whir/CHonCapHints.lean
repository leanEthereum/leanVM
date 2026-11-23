/-
  LeanVM.Guest.B1.Whir.CHonCapHints

  On the honest run, each level's hinted cap and flags (`capW`, `flW`) are the hint generator's (`levelCapPushes`) for its phase.
-/

module

public import LeanVM.Guest.B1.Whir.CHonFields4
public import LeanVM.Guest.B1.Whir.CCapsHints
public import LeanVM.Guest.B1.Whir.CapDepthOk

/-!
# The honest run's caps are the generator's

* `HonRun.idx`: a level's openings sit at its positions;
* `HonRun.phase_opens`: each opening's leaf index is below `2^depth` and its path `depth` long;
* `HonRun.capDepth_hints`: the level's cap depth is `Hints.capDepthOf` of its query count and depth;
* `HonRun.capHints`: `capW` and `flW` are `levelCapPushes` of the level's depth, query count and phase.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem zip_map_self {α β : Type} (f : α → β) : ∀ l : List α, (l.map f).zip l = l.map fun a => (f a, a)
  | [] => rfl
  | a :: l => by rw [List.map_cons, List.zip_cons_cons, zip_map_self f l, List.map_cons]

namespace HonRun

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

/-- **Level `l`'s openings sit at its positions.** -/
theorem idx {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) :
    (Ls.getD l default).phase.map Opening.leafIndex = (Ls.getD l default).qs μ := by
  have hy := hR.yr
  by_cases hlt : l < (osCfgR (μ - minOpenLog) (r - 1)).yrLevel
  · obtain ⟨rw, W, hd, -, -, -, -, hnext, -⟩ := hR.step hlt
    have hrw : (Ls.getD l default).rw = rw := by unfold LvAt.rw; rw [hd]
    have hqs : (Ls.getD l default).qs μ = W.qs (rsF (Ls.getD l default).level (Ls.getD l default).cap rw)
        (μ - (rsSt (Ls.getD l default).level (Ls.getD l default).s (Ls.getD l default).cap rw).alphas.length)
        (μ - (rsSt (Ls.getD l default).level (Ls.getD l default).s (Ls.getD l default).cap rw).alphas.length +
          (Ls.getD l default).level.logInvRate) (Ls.getD l default).level.queries := by
      unfold LvAt.qs; rw [hd]; simp only [LvAt.F, LvAt.mu, LvAt.dp, LvAt.s1, hrw]
    have hph : (Ls.getD l default).phase = W.phase := by unfold LvAt.phase; rw [hd]
    rw [hqs, hph]
    exact hnext.idx
  · have he : l = (osCfgR (μ - minOpenLog) (r - 1)).yrLevel := by omega
    subst he
    obtain ⟨rw, W, hd, -, -, -, -, hfin, -⟩ := hR.last
    have hrw : (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).rw = rw := by unfold LvAt.rw; rw [hd]
    have hqs : (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).qs μ =
        W.qs (rsF (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).level
          (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).cap rw)
        (μ - (rsSt (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).level
          (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).s
          (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).cap rw).alphas.length +
          (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).level.logInvRate)
        (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).level.queries := by
      unfold LvAt.qs; rw [hd]; simp only [LvAt.F, LvAt.mu, LvAt.dp, LvAt.s1, hrw]
    have hph : (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).phase = W.phase := by
      unfold LvAt.phase; rw [hd]
    rw [hqs, hph]
    exact hfin.idx

/-- **Level `l`'s openings climb from below `2^depth`, by `depth` siblings.** -/
theorem phase_opens {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) :
    ∀ o ∈ (Ls.getD l default).phase, o.leafIndex < 2 ^ ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).depth ∧
      o.path.length = ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).depth := by
  obtain ⟨qs, ph, hq, hp, hlen, hok⟩ := hR.opens hl
  have hidx := hR.idx hl
  have hps := hR.qs_lt hl
  rw [hq, hp] at hidx
  rw [hq] at hps
  rw [hp]
  intro o ho
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ho
  have hkq : k < qs.length := by omega
  have hi : ph[k].leafIndex = qs[k] := by
    have := congrArg (·[k]?) hidx
    simp only [List.getElem?_map, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hkq,
      Option.map_some, Option.some.injEq] at this
    exact this
  obtain ⟨-, h2, -⟩ := openOne_facts (hok k hkq hk)
  exact ⟨by rw [hi]; exact hps _ (List.getElem_mem hkq), h2⟩

/-- **Level `l`'s cap depth is the generator's** for its query count. -/
theorem capDepth_hints {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) :
    ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).capDepth =
      Hints.capDepthOf ((Ls.getD l default).qs μ).length ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).depth := by
  have hmem : (osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default ∈ osLevelsR (μ - minOpenLog) (r - 1) := by
    rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl
  have hcd := capDepth_eq (by have := hR.m11; unfold ligNSizes; omega) (by have := hR.r4; omega) hmem
  rw [← (hR.lvb hl).q, ← LvAt.qs_length] at hcd
  exact hcd

/-- **Level `l`'s hinted cap and flags are the generator's.** -/
theorem capHints {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) :
    [("merkle_caps", capW Ls μ r l), ("merkle_cap_active", flW Ls μ r l)] =
      levelCapPushes ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).depth
        ((Ls.getD l default).qs μ).length (Ls.getD l default).phase := by
  obtain ⟨hcdq, -, -, -, -⟩ := hR.cdpd hl
  have hidx := hR.idx hl
  have hag := hR.agree l (by rw [hR.len]; exact hl) _ _ _ (hR.roots l hl).2
  rw [← hidx, zip_map_self] at hag
  have hcd := hR.capDepth_hints hl
  rw [levelCapPushes_eq (hR.phase_opens hl) hag, ← hcd, ← hcdq]
  have hcv : (hdOf μ r Ls).cv l = capCell ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).depth
      (atIdx (Ls.getD l default).phase) := by
    show capCellH (heightAt Ls l) _ _ = _
    rw [hR.height_eq hl, capCellH, ← hidx, zip_map_self]
    rfl
  have hfv : (hdOf μ r Ls).fv l = capFl ((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default).depth
      (atIdx (Ls.getD l default).phase) (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).cd := by
    show capFlH (heightAt Ls l) _ _ _ = _
    rw [hR.height_eq hl, capFlH, ← hidx, zip_map_self, hcdq]
    rfl
  rw [capW, flW, hcv, hfv]

end HonRun

end
end LeanVM.Guest.B1.Whir
