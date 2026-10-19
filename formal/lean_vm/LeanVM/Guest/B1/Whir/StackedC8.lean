/-
  LeanVM.Guest.B1.Whir.StackedC8

  Every level of the stacked opening's run, inverted into the levels' data.
-/

module

public import LeanVM.Guest.B1.Whir.StackedC7
public import LeanVM.Guest.B1.Whir.StackedLevels

/-!
# The levels' data (TRIAGE #36)

`os_chain_of_run`: a run of `whirLevelsOpen` from level `lvl` gives one `OsLvH` per level left,
each level's data `OsLvOk` from the state the previous one ends at (`OsChain`), the last one's
tail run to the end.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- The levels' data from level `lvl` on, each from where the previous one ends, the last one's
tail running to `e`, `sp'`. -/
def OsChain (cfg : OsCfg) (μ lane : ℕ) (xs : List E) (Lall : List Whir.Level) (e : WhirEnd) (sp' : St) :
    ℕ → Digest → ℕ → WhirState → List Opening → List (Digest × ℕ × ℕ) → List OsLvH → Prop
  | _, _, _, _, _, _, [] => False
  | lvl, cv, p, w, osp, roots, H :: Hs =>
    OsLvOk cfg lvl xs p μ (Lall.getD lvl default) cv w osp roots H ∧
      (lvl = cfg.yrLevel → Hs = [] ∧
        Runs (osTailOpen (μ - osLevelF cfg lvl) lane (osHWEnd cfg lvl xs p H) (osHMs cfg lvl xs p))
          ⟨osHCvEnd cfg lvl xs p H.cv1, xs.drop (osHPEnd cfg lvl p), H.osq, roots⟩ e sp') ∧
      (lvl ≠ cfg.yrLevel → OsChain cfg μ lane xs Lall e sp' (lvl + 1) (osHCvEnd cfg lvl xs p H.cv1)
        (osHPEnd cfg lvl p) (osHWEnd cfg lvl xs p H) H.osq (osHRootsEnd cfg lvl roots H) Hs)

theorem os_glue_folds' (lam : E) (s : WhirState) (pending : List (E × List E × (List E → E))) :
    (glue lam s pending).folds = s.folds := os_glue_folds lam s pending

/-- **The levels' data**: a run of `whirLevelsOpen` from level `lvl`, at the state the guest's
invariant names, has the levels' data. -/
theorem os_chain_of_run {cfg : OsCfg} {μ lane : ℕ} {Lall : List Whir.Level}
    (hlen : Lall.length = cfg.levels.length)
    (hspec : ∀ i < Lall.length, LvSpec cfg μ i (Lall.getD i default) (Lall.drop (i + 1)))
    (hyl : cfg.yrLevel = cfg.levels.length - 1) {xs : List E} {e : WhirEnd} {sp' : St} :
    ∀ (j lvl : ℕ) (cv : Digest) (p : ℕ) (w : WhirState) (osp : List Opening) (roots : List (Digest × ℕ × ℕ)),
      lvl + j + 1 = Lall.length → w.folds.length = (cfg.lv lvl).foldsOff → roots.length = lvl + 1 →
      Runs (whirLevelsOpen μ lane lvl (Lall.drop lvl) w) ⟨cv, xs.drop p, osp, roots⟩ e sp' →
      ∃ Hs : List OsLvH, Hs.length = j + 1 ∧ OsChain cfg μ lane xs Lall e sp' lvl cv p w osp roots Hs := by
  intro j
  induction j with
  | zero =>
    intro lvl cv p w osp roots hj hfl hrl h
    have hl : lvl < Lall.length := by omega
    have hs := hspec lvl hl
    have hLrest : Lall.drop (lvl + 1) = [] := List.drop_eq_nil_of_le (by omega)
    rw [hLrest] at hs
    rw [List.drop_eq_getElem_cons hl, show Lall[lvl] = Lall.getD lvl default by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl], hLrest] at h
    obtain ⟨H, hok, htail, -⟩ := os_level_inv hs hfl (by omega) h
    have hy : lvl = cfg.yrLevel := by rw [hyl]; omega
    exact ⟨[H], rfl, hok, fun _ => ⟨rfl, htail rfl⟩, fun h' => absurd hy h'⟩
  | succ j ih =>
    intro lvl cv p w osp roots hj hfl hrl h
    have hl : lvl < Lall.length := by omega
    have hs := hspec lvl hl
    rw [List.drop_eq_getElem_cons hl, show Lall[lvl] = Lall.getD lvl default by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]] at h
    have hl1 : lvl + 1 < Lall.length := by omega
    have hcons : Lall.drop (lvl + 1) = Lall.getD (lvl + 1) default :: Lall.drop (lvl + 2) := by
      rw [List.drop_eq_getElem_cons hl1]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl1]
    obtain ⟨H, hok, -, hnext⟩ := os_level_inv hs hfl (by omega) h
    have hny : lvl ≠ cfg.yrLevel := by rw [hyl]; omega
    have hs' := hs
    rw [hcons] at hs'
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnx⟩ := hs'
    obtain ⟨-, hfo', -, -⟩ := hnx _ rfl
    obtain ⟨Hs, hHl, hch⟩ := ih (lvl + 1) _ _ _ _ _ (by omega)
      (by rw [osHWEnd, os_glue_folds', hok.w1len, hfo'])
      (by rw [osHRootsEnd, ite_neg' hny, List.length_append, hrl]; rfl)
      (hnext (by rw [hcons]; simp))
    exact ⟨H :: Hs, by simp [hHl], hok, fun h' => absurd h' hny, fun _ => hch⟩

end
end LeanVM.Guest.B1
