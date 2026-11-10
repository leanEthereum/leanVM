/-
  LeanVM.Guest.B1.Whir.CHonRun

  The honest run's levels, indexed: their openings' agreement, their configuration's facts and
  their words in the stream.
-/

module

public import LeanVM.Guest.B1.Whir.CHonLv
public import LeanVM.Guest.B1.Whir.CCapsRun
public import LeanVM.Guest.B1.Whir.FactsSound

/-!
# The run's levels, indexed (continued)

`lvsAt_agree`: each level's openings agree at its root's height (`LvsAgree`, indexed).
`levelsB_at`: a candidate's checked facts at each level of the run (`MidOk`, `FinOk`).
`lvsAt_suffix`: each level's words end the stream.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **Each level's openings agree**, indexed. -/
theorem lvsAt_agree (logN lane : ℕ) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState) (cap : List E)
      (R : List (Digest × ℕ × ℕ)) (xs : List E) (os : List (List Opening)) (w : WhirEnd)
      (ds : List LvD), LvsRunD logN lane index levels s cap R xs os w ds →
      LvsAgree logN index levels s cap R ds →
      ∀ i < (lvsAt logN index levels s cap R xs os ds).length, ∀ root height width,
        ((lvsAt logN index levels s cap R xs os ds).getD i default).R[index + i]? =
          some (root, height, width) →
        Guest.Limits.OpeningsAgree height
          ((((lvsAt logN index levels s cap R xs os ds).getD i default).qs logN).zip
            ((lvsAt logN index levels s cap R xs os ds).getD i default).phase)
  | [level], index, s, cap, R, xs, os, w, [LvD.fin rw W], _, hA, i, h => by
    obtain rfl : i = 0 := by simp [lvsAt] at h; omega
    exact hA
  | level :: next :: rest, index, s, cap, R, xs, os, w, LvD.next rw W :: ds, hD, hA, i, h => by
    obtain ⟨xs', os', hrl, hrok, hxs, hos, hnext, hD'⟩ := hD
    have hxs' : xs.drop (rw.length + W.words.length) = xs' := by rw [hxs]; exact drop_words
    have hos' : os.tail = os' := by rw [hos]; rfl
    rcases i with _ | i
    · exact hA.1
    · have ih := lvsAt_agree logN lane (next :: rest) (index + 1) _ _ _ xs' os' w ds hD' hA.2 i
      simp only [lvsAt, List.length_cons, List.getD_cons_succ] at h ⊢
      rw [hxs', hos'] at h ⊢
      intro root height width hR
      exact ih (by omega) root height width (by rw [← hR, show index + 1 + i = index + (i + 1) by ring])
  | [], _, _, _, _, _, _, _, _, hD, _, _, _ => by simp [LvsRunD] at hD
  | [_], _, _, _, _, _, _, _, [], hD, _, _, _ => by simp [LvsRunD] at hD
  | [_], _, _, _, _, _, _, _, LvD.next _ _ :: _, hD, _, _, _ => by simp [LvsRunD] at hD
  | [_], _, _, _, _, _, _, _, LvD.fin _ _ :: _ :: _, hD, _, _, _ => by simp [LvsRunD] at hD
  | _ :: _ :: _, _, _, _, _, _, _, _, [], hD, _, _, _ => by simp [LvsRunD] at hD
  | _ :: _ :: _, _, _, _, _, _, _, _, LvD.fin _ _ :: _, hD, _, _, _ => by simp [LvsRunD] at hD

/-- **A candidate's checked facts at each level.** -/
theorem levelsB_at {c : OsCfg} {logN : ℕ} :
    ∀ (lvl : ℕ) (lvs : List OsLv) (cfg : List Whir.Level), levelsB c logN lvl lvs cfg = true →
      lvs.length = cfg.length ∧
      (∀ i, i + 1 < lvs.length → ∀ level next, cfg[i]? = some level → cfg[i + 1]? = some next →
        MidOk c logN (lvl + i) (lvs.getD i default) level next (lvs.getD (i + 1) default)) ∧
      (∀ level, cfg[lvs.length - 1]? = some level →
        FinOkF c logN (lvl + (lvs.length - 1)) (lvs.getD (lvs.length - 1) default) level)
  | lvl, [lv], [level], hb => by
    simp only [levelsB, decide_eq_true_eq] at hb
    refine ⟨rfl, fun i hi ↦ absurd hi (by simp), fun l' hl' ↦ ?_⟩
    simp only [List.length_cons, List.length_nil, Nat.sub_self, List.getElem?_cons_zero,
      Option.some.injEq] at hl'
    subst hl'
    simpa using hb
  | lvl, lv :: lv' :: lvs, level :: next :: cfg, hb => by
    simp only [levelsB, Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨e, hm, hf⟩ := levelsB_at (lvl + 1) (lv' :: lvs) (next :: cfg) hb.2
    refine ⟨by simp at e ⊢; omega, fun i hi l1 l2 h1 h2 ↦ ?_, fun l' hl' ↦ ?_⟩
    · rcases i with _ | i
      · simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h1 h2
        subst h1 h2
        simpa using hb.1
      · have := hm i (by simp at hi ⊢; omega) l1 l2 (by simpa using h1) (by simpa using h2)
        rw [show lvl + (i + 1) = lvl + 1 + i by ring]
        simpa using this
    · have hl : (lv :: lv' :: lvs).length - 1 = (lv' :: lvs).length - 1 + 1 := by simp
      rw [hl, List.getElem?_cons_succ] at hl'
      have := hf l' hl'
      rw [hl, List.getD_cons_succ, show lvl + ((lv' :: lvs).length - 1 + 1) =
        lvl + 1 + ((lv' :: lvs).length - 1) by ring]
      exact this
  | _, [], _, hb => by simp [levelsB] at hb
  | _, [_], [], hb => by simp [levelsB] at hb
  | _, [_], _ :: _ :: _, hb => by simp [levelsB] at hb
  | _, _ :: _ :: _, [], hb => by simp [levelsB] at hb
  | _, _ :: _ :: _, [_], hb => by simp [levelsB] at hb

/-- **Each level's words end the stream.** -/
theorem lvsAt_suffix {logN lane index : ℕ} {levels : List Whir.Level} {s : WhirState} {cap : List E}
    {R : List (Digest × ℕ × ℕ)} {xs : List E} {os : List (List Opening)} {w : WhirEnd}
    {L : List LvAt} (h : LvsAtRun logN lane index levels s cap R xs os w L) :
    ∀ i < L.length, ∃ p, xs = p ++ (L.getD i default).xs
  | 0, hi => ⟨[], by rw [(h.start hi).2.2.2.1]; rfl⟩
  | i + 1, hi => by
    obtain ⟨p, hp⟩ := lvsAt_suffix h i (by omega)
    obtain ⟨rw, W, -, -, -, hx, -⟩ := h.next i hi
    exact ⟨p ++ (rw ++ W.words), by rw [hp, hx]; simp⟩

end
end LeanVM.Guest.B1.Whir
