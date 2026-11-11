/-
  LeanVM.Guest.B1.Whir.Flatness

  The template's body is flat (atoms and calls) up to its final `ret`.
-/

module

public import LeanVM.Guest.B1.Whir.Finish
public import LeanVM.Guest.B1.Whir.Squeezes

/-!
# The body is flat

`osBody c = osBodyA c ++ [ret …]` (`osBody_split`) with `osBodyA c` flat (`osBodyA_flat`): every
block of the template is atoms, calls, conditional calls and dispatches.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1

@[expose] public section

/-- A list of statements is flat. -/
abbrev Flat (l : List Stmt) : Prop := l.all Stmt.flat = true

theorem flat_append {a b : List Stmt} (ha : Flat a) (hb : Flat b) : Flat (a ++ b) := by
  simp only [Flat, List.all_append, ha, hb, Bool.and_self]

theorem flat_cons {s : Stmt} {a : List Stmt} (hs : Stmt.flat s = true) (ha : Flat a) :
    Flat (s :: a) := by
  simp only [Flat, List.all_cons, hs, ha, Bool.true_and]

theorem flat_map {α : Type} (l : List α) (f : α → Stmt) (h : ∀ a, Stmt.flat (f a) = true) :
    Flat (l.map f) := by
  simp only [Flat, List.all_map, List.all_eq_true, Function.comp_apply]
  exact fun a _ ↦ h a

theorem flat_flatten {l : List (List Stmt)} (h : ∀ a ∈ l, Flat a) : Flat l.flatten := by
  simp only [Flat, List.all_flatten, List.all_eq_true] at h ⊢
  exact h

theorem osMat_flat (b o k : ℕ) : Flat (osMat b o k).1 := by unfold osMat; split_ifs <;> rfl

theorem osHeap_flat (e k : ℕ) : Flat (osHeap e k) := rfl

theorem osLoopCall_flat (name : String) (n : ℕ) (args : List ℕ) (k : ℕ) :
    Flat (osLoopCall name n args k) := rfl

theorem osFoldCall_flat (fr : Option (List String)) (args rets : List V) :
    Stmt.flat (osFoldCall fr args rets) = true := by
  cases fr <;> rfl

theorem osFolds_flat (fr : Option (List String)) (p : ℕ) : ∀ n off s, Flat (osFolds fr p off n s).1
  | 0, _, _ => rfl
  | n + 1, off, _ => flat_append (flat_append (osMat_flat _ _ _)
      (flat_cons (osFoldCall_flat _ _ _) rfl)) (osFolds_flat fr p n (off + 1) _)

theorem osPad_flat (pad : Option ℕ) (k : ℕ) : Flat (osPad pad k).1 := by
  cases pad <;> rfl

theorem osPowSteps_flat (x : ℕ) : ∀ ds acc k, Flat (osPowSteps x ds acc k).1
  | [], _, _ => rfl
  | d :: ds, acc, k => by
    cases d
    · exact flat_cons rfl (osPowSteps_flat x ds _ _)
    · exact flat_cons rfl (flat_cons rfl (osPowSteps_flat x ds _ _))

theorem osMu_flat (lvl lam k : ℕ) : Flat (osMu lvl lam k).1 := rfl

theorem osMatP_flat (P : List (ℕ × ℕ × ℕ)) (m : List OsMat) (b o k : ℕ) :
    Flat (osMatP P m b o k).1 := by
  unfold osMatP; split_ifs <;> rfl

theorem osPositions_flat (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    Flat (osPositions c lvl lv s).1 := by
  simp only [osPositions]
  refine flat_append (flat_append (flat_append (flat_append (flat_append
    (osMatP_flat _ _ _ _ _) (osMatP_flat _ _ _ _ _)) rfl) (flat_map _ _ fun _ ↦ rfl))
    (osPad_flat _ _)) rfl

theorem osQueries_flat (c : OsCfg) (lvl : ℕ) (lv : OsLv) (lam : ℕ) (s : OsSt) :
    Flat (osQueries c lvl lv lam s).1 := by
  simp only [osQueries]
  refine flat_append (flat_append (flat_append (flat_append
    (osHeap_flat _ _) (osMatP_flat _ _ _ _ _)) rfl) (osMatP_flat _ _ _ _ _)) rfl

theorem osCommit_flat (P : List (ℕ × ℕ × ℕ)) (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    Flat (osCommit P lvl lv s).1 := by
  simp only [osCommit]
  repeat (first | refine flat_append ?_ ?_ | exact osMatP_flat _ _ _ _ _ |
    exact flat_map _ _ fun _ ↦ rfl | rfl)

theorem osWinTabs_flat : Flat osWinTabs := flat_flatten fun a ha ↦ by
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
  rfl

theorem osHead_flat (c : OsCfg) : Flat (osHead c).1 := by
  have H := osHeap_flat
  exact flat_append (flat_append (flat_append (flat_append (flat_append (flat_append (flat_append
    (flat_append (flat_append (flat_append (flat_append (flat_append rfl (H _ _)) (H _ _)) rfl)
    (H _ _)) (H _ _)) (H _ _)) (H _ _)) (H _ _)) (H _ _)) osWinTabs_flat) (H _ _)) (H _ _)

theorem osFinal_flat (c : OsCfg) (s : OsSt) : Flat (osFinal c s).1 :=
  flat_append (osMat_flat _ _ _) rfl

theorem osLevel_flat (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : Flat (osLevel c lvl lv s).1 := by
  simp only [osLevel]
  refine flat_append (flat_append (flat_append (flat_append (flat_append (flat_append
    (flat_append (flat_append (osFolds_flat _ _ _ _ _) ?_) rfl) (osPositions_flat _ _ _ _))
    (osMu_flat _ _ _)) (osQueries_flat _ _ _ _ _)) ?_) rfl) rfl
  · split
    · exact osFinal_flat _ _
    · exact osCommit_flat _ _ _ _
  · split
    · rfl
    · rfl

theorem osLevels_flat (c : OsCfg) : ∀ lvl lvs s, Flat (osLevels c lvl lvs s).1
  | _, [], _ => rfl
  | lvl, _ :: rest, _ => flat_append (osLevel_flat _ _ _ _) (osLevels_flat c (lvl + 1) rest _)

theorem osTail_flat (c : OsCfg) (s : OsSt) : Flat (osTail c s).1 := by
  simp only [osTail]
  refine flat_append (flat_append (flat_append (flat_append (flat_append (flat_append
    (flat_append (osHeap_flat _ _) (osFolds_flat _ _ _ _ _)) (flat_map _ _ fun _ ↦ rfl)) rfl) rfl)
    rfl) rfl) (flat_flatten fun a ha ↦ ?_)
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
  rfl

theorem osPtBlks_flat (c : OsCfg) (pt pt1 tch : ℕ) : ∀ i n k, Flat (osPtBlks c pt pt1 tch i n k).1
  | _, 0, _ => rfl
  | i, n + 1, k => flat_append (by
      unfold osPtBlk; split <;> rfl) (osPtBlks_flat c pt pt1 tch (i + 1) n _)

theorem osBasisRow_flat (bd : ℕ) : ∀ cs sc k, Flat (osBasisRow bd cs sc k).1
  | [], _, _ => rfl
  | (_, _, _) :: rest, _, _ => flat_append (by
      unfold osBasisBlk; split <;> rfl) (osBasisRow_flat bd rest _ _)

theorem osBases_flat (c : OsCfg) (tch bd ls : ℕ) : ∀ lvl lvs k, Flat (osBases c tch bd ls lvl lvs k).1
  | _, [], _ => rfl
  | lvl, _ :: rest, _ => flat_append (flat_append (flat_cons rfl (osBasisRow_flat _ _ _ _)) rfl)
      (osBases_flat c tch bd ls (lvl + 1) rest _)

theorem osResidual_flat (c : OsCfg) (ich bd ls lvl : ℕ) (lv : OsLv) (mats : List OsMat) (k : ℕ) :
    Flat (osResidual c ich bd ls lvl lv mats k).1 := by
  simp only [osResidual]
  exact flat_append (flat_append (osMatP_flat _ _ _ _ _) (osMatP_flat _ _ _ _ _)) rfl

theorem osResiduals_flat (c : OsCfg) (ich bd ls : ℕ) :
    ∀ lvl lvs mats k, Flat (osResiduals c ich bd ls lvl lvs mats k).1
  | _, [], _, _ => rfl
  | lvl, _ :: rest, _, _ => flat_append (osResidual_flat _ _ _ _ _ _ _ _)
      (osResiduals_flat c ich bd ls (lvl + 1) rest _ _)

theorem osOodFacs_flat (sc : ℕ) : ∀ cs k, Flat (osOodFacs sc cs k).1
  | [], _ => rfl
  | (_, _) :: rest, _ => flat_append rfl (osOodFacs_flat _ rest _)

theorem osOodWeights_flat (c : OsCfg) (tch : ℕ) :
    ∀ prevCols ol lvs acc k, Flat (osOodWeights c tch prevCols ol lvs acc k).1
  | _, _, [], _, _ => rfl
  | _, _, _ :: rest, acc, _ => by
    simp only [osOodWeights]
    refine flat_append (flat_append (flat_cons rfl (osOodFacs_flat _ _ _)) ?_)
      (osOodWeights_flat c tch _ _ rest _ _)
    split <;> rfl

theorem osFinishA_flat (c : OsCfg) (st : OsSt) (tch : ℕ) : Flat (osFinishA c st tch) := by
  simp only [osFinishA]
  have h1 := flat_append (rfl : Flat [Stmt.call ("fold_final_msg__L" ++ natStr c.yrLog)
    [.n osFmsg, .n tch] [.n st.k], .atom (.hint (.alloc (.n (st.k + 1)) pointCap)),
    .atom (.hint (.alloc (.n (st.k + 1 + 1)) pointCap))]) (osPtBlks_flat c (st.k + 1) (st.k + 1 + 1)
      tch 0 pointCap (st.k + 1 + 2))
  refine flat_append (flat_append (flat_append (flat_append (flat_append (flat_append
    (flat_append (flat_append h1 (osHeap_flat _ _)) (osHeap_flat _ _))
    (osBases_flat _ _ _ _ _ _ _)) (osHeap_flat _ _)) rfl) (osResiduals_flat _ _ _ _ _ _ _ _))
    (osOodWeights_flat _ _ _ _ _ _ _)) rfl

/-- The body before its `ret`. -/
def osBodyA (c : OsCfg) : List Stmt :=
  (osHead c).1 ++ (osLevels c 0 c.levels (osHead c).2).1 ++
    (osTail c (osLevels c 0 c.levels (osHead c).2).2).1 ++
    osFinishA c (osTail c (osLevels c 0 c.levels (osHead c).2).2).2.1
      (osTail c (osLevels c 0 c.levels (osHead c).2).2).2.2

theorem osBody_split (c : OsCfg) :
    osBody c = osBodyA c ++ [.ret (osFinishRet c (osTail c (osLevels c 0 c.levels (osHead c).2).2).2.1
      (osTail c (osLevels c 0 c.levels (osHead c).2).2).2.2)] := by
  simp only [osBody, osBodyA, osFinish_split, List.append_assoc]

theorem osBodyA_flat (c : OsCfg) : Flat (osBodyA c) :=
  flat_append (flat_append (flat_append (osHead_flat c) (osLevels_flat _ _ _ _)) (osTail_flat _ _))
    (osFinishA_flat _ _ _)

end
end LeanVM.Guest.B1.Whir
