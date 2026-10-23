/-
  LeanVM.Guest.B1.Whir.OsCapRun

  A level's openings from the run fill its honest cap.
-/

module

public import LeanVM.Guest.B1.Whir.OsCap
public import LeanVM.Guest.B1.Whir.StackedC5

/-!
# The level's openings fill its cap (TRIAGE #29, #30)

`os_openAll_inv`: `openAll` consumes one opening per position, each of the shape and climbing to
the root; `os_capOk_of`: a level's positions zipped with its openings satisfy `OsCapOk`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- **`openAll`, inverted**: one opening per position, each of the shape and climbing to the root. -/
theorem os_openAll_inv {root : Digest} {hh ww : ℕ} : ∀ (ps : List ℕ) (os : List Opening) (rows : List (List K))
    (rest : List Opening), openAll (m := Id) blake2sBytes root hh ww ps os = some (rows, rest) →
    ∃ os1, os = os1 ++ rest ∧ os1.length = ps.length ∧ rows = os1.map (·.leaf) ∧
      ∀ j (hj : j < os1.length), (os1[j]).leaf.length = ww ∧ (os1[j]).path.length = hh ∧
        climb (m := Id) blake2sBytes (hashWords (os1[j]).leaf) (ps.getD j 0) (os1[j]).path = root
  | [], os, rows, rest, h => by
    simp only [openAll] at h
    cases h
    exact ⟨[], rfl, rfl, rfl, fun j hj => absurd hj (by simp)⟩
  | _ :: _, [], _, _, h => by simp [openAll] at h
  | q :: ps, o :: os, rows, rest, h => by
    simp only [openAll, bind] at h
    split at h
    · rename_i hok
      match hr : openAll (m := Id) blake2sBytes root hh ww ps os, h with
      | some (rows', rest'), h =>
        simp only [Option.map_some, pure] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨os1, rfl, hl, rfl, hj⟩ := os_openAll_inv ps os _ _ hr
        simp only [openOne] at hok
        split at hok
        · rename_i hsh
          have htop : climb (m := Id) blake2sBytes (hashWords o.leaf) q o.path = root := by
            have := of_decide_eq_true hok
            exact Vector.toList_inj.mp this
          refine ⟨o :: os1, rfl, by simp [hl], by simp, fun j hj' => ?_⟩
          rcases j with _ | j
          · exact ⟨hsh.1, hsh.2, by simpa using htop⟩
          · simpa using hj j (by simpa using hj')
        · cases hok
    · cases h

/-- **A level's openings fill its cap**: its positions, below `2^depth`, zipped with its openings. -/
theorem os_capOk_of {cfg : OsCfg} {lvl : ℕ} {xs : List E} {p : ℕ} {cv1 : Digest} {osp osq : List Opening}
    {rt : Digest} {hh ww : ℕ} {rows : List (List K)}
    (hoa : openAll (m := Id) blake2sBytes rt hh ww (osHQs cfg lvl xs p cv1) osp = some (rows, osq))
    (hag : BatchAgrees hh ((osHQs cfg lvl xs p cv1).zip osp)) (hhd : hh = (cfg.lv lvl).depth)
    (hq : 0 < (cfg.lv lvl).queries) (hcd1 : 1 ≤ (cfg.lv lvl).capDepth)
    (hcd2 : (cfg.lv lvl).capDepth ≤ (cfg.lv lvl).depth) :
    OsCapOk (cfg.lv lvl).depth (cfg.lv lvl).capDepth rt ((osHQs cfg lvl xs p cv1).zip osp) := by
  subst hhd
  obtain ⟨os1, rfl, hl, -, hj⟩ := os_openAll_inv _ _ _ _ hoa
  have hql : (osHQs cfg lvl xs p cv1).length = (cfg.lv lvl).queries := by simp [osHQs]
  have hmem : ∀ a ∈ (osHQs cfg lvl xs p cv1).zip (os1 ++ osq), ∃ j, ∃ hj : j < os1.length,
      a = ((osHQs cfg lvl xs p cv1).getD j 0, os1[j]) := by
    intro a ha
    obtain ⟨j, hj1, rfl⟩ := List.getElem_of_mem ha
    simp only [List.length_zip, List.length_append] at hj1
    refine ⟨j, by omega, ?_⟩
    simp only [List.getElem_zip, List.getElem_append_left (show j < os1.length by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  refine ⟨hag, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, ?_, hcd1, hcd2⟩
  · obtain ⟨j, hj', rfl⟩ := hmem a ha
    simp only [osHQs]
    rw [os_getD_map_range _ (by omega), osPosOf]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  · obtain ⟨j, hj', rfl⟩ := hmem a ha
    exact (hj j hj').2.1
  · obtain ⟨j, hj', rfl⟩ := hmem a ha
    exact (hj j hj').2.2
  · intro h0
    have := congrArg List.length h0
    simp only [List.length_zip, List.length_append, List.length_nil] at this
    omega

end
end LeanVM.Guest.B1
