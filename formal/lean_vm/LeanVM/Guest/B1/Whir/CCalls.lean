/-
  LeanVM.Guest.B1.Whir.CCalls

  The call statements of open_stacked's blocks and their values: what the placed lift takes of
  the body's calls, fixed before the memory.
-/

module

public import LeanVM.Guest.B1.Whir.Flatness

/-!
# The blocks' calls

`callVs s`: a call statement's condition, selector, arguments and returns (`Stmt.callVarsS` of
`Place/OsProtoSpec`). `cvOf ss σ`: the values of a block's call statements' variables under `σ`,
in order. `*_calls`: the blocks without calls (atoms, `level_rate`'s `match`es) and the call
statements of the others.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1

@[expose] public section

/-- A call statement's condition, selector, arguments and returns. -/
def callVs : Stmt → Option (List V)
  | .call _ a r => some (a ++ r)
  | .callIf cv _ a => some (cv :: a)
  | .dispatch x _ a r => some (x :: a ++ r)
  | _ => none

/-- **The values of a block's call statements' variables**, in order. -/
def cvOf (ss : List Stmt) (σ : Val) : List (List E) := (ss.filterMap callVs).map (·.map σ)

theorem cvOf_append (a b : List Stmt) (σ : Val) : cvOf (a ++ b) σ = cvOf a σ ++ cvOf b σ := by
  simp [cvOf, List.filterMap_append]

theorem cvOf_of_calls {ss : List Stmt} {vs : List (List V)} (h : ss.filterMap callVs = vs) (σ : Val) :
    cvOf ss σ = vs.map (·.map σ) := by
  rw [cvOf, h]

theorem calls_append (a b : List Stmt) :
    (a ++ b).filterMap callVs = a.filterMap callVs ++ b.filterMap callVs := List.filterMap_append

theorem calls_of_isAtom : ∀ (ss : List Stmt), ss.all Stmt.isAtom = true → ss.filterMap callVs = []
  | [], _ => rfl
  | s :: ss, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    match s, h.1 with
    | .atom _, _ => simp only [List.filterMap_cons, callVs]; exact calls_of_isAtom ss h.2

theorem calls_flatten (L : List (List Stmt)) (h : ∀ a ∈ L, a.filterMap callVs = []) :
    L.flatten.filterMap callVs = [] := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.flatten_cons, calls_append, h a List.mem_cons_self,
      ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb)]
    rfl

/-! ## Blocks without calls -/

theorem osHeap_calls (e k : ℕ) : (osHeap e k).filterMap callVs = [] := rfl

theorem osMatP_calls (P : List (ℕ × ℕ × ℕ)) (m : List OsMat) (b o k : ℕ) :
    (osMatP P m b o k).1.filterMap callVs = [] := by
  unfold osMatP; split_ifs <;> rfl

theorem osMatS_calls (P : List (ℕ × ℕ × ℕ)) (b o : ℕ) (s : OsSt) : (osMatS P b o s).1.filterMap callVs = [] :=
  osMatP_calls _ _ _ _ _

theorem osMat_calls (b o k : ℕ) : (osMat b o k).1.filterMap callVs = [] := by
  unfold osMat; split_ifs <;> rfl

theorem osCurS_calls (s : OsSt) : (osCurS s).1.filterMap callVs = [] := osMat_calls _ _ _

theorem osPad_calls (pad : Option ℕ) (k : ℕ) : (osPad pad k).1.filterMap callVs = [] := by
  cases pad <;> rfl

theorem gcInlineT_calls (b o : ℕ) (w tabs : V) : (gcInlineT b o w tabs).filterMap callVs = [] :=
  calls_of_isAtom _ (renameList_isAtom _ _ (gcPre_isAtom b))

theorem osRoundCore_calls (b p cb co claim i : ℕ) (cap : List ℕ) :
    (osRoundCore b p cb co claim i cap).filterMap callVs = [] := by
  unfold osRoundCore
  rw [calls_append, calls_append, calls_append, gcInlineT_calls, calls_flatten]
  · rfl
  · intro a ha
    simp only [List.mem_map, List.mem_range] at ha
    obtain ⟨t, -, rfl⟩ := ha
    rfl

theorem osRound_calls (cp last : Bool) (i : ℕ) (s : OsSt) : (osRound cp last i s).1.filterMap callVs = [] := by
  unfold osRound
  dsimp only
  rw [calls_append, calls_append, osRoundCore_calls]
  split_ifs <;> simp [callVs, osCp]

theorem osRounds_calls : ∀ cp i n s, (osRounds cp i n s).1.filterMap callVs = []
  | _, _, 0, _ => rfl
  | _, i, n + 1, _ => by
    show ((osRound _ _ _ _).1 ++ (osRounds false (i + 1) n _).1).filterMap callVs = []
    rw [calls_append, osRound_calls, osRounds_calls false (i + 1) n]
    rfl

theorem osRates_calls (c : OsCfg) (lvl : ℕ) (s : OsSt) : (osRates c lvl s).1.filterMap callVs = [] := by
  simp [osRates, callVs, osCst, osMul]

theorem osQGrind_calls (s : OsSt) : (osQGrind s).1.filterMap callVs = [] := gcInlineT_calls _ _ _ _

theorem osHsCoefs_calls (src dst : ℕ) (sc : ℕ → ℕ) (si di : ℕ) :
    ∀ n i k, (osHsCoefs src dst sc si di n i k).1.filterMap callVs = []
  | 0, _, _ => rfl
  | n + 1, i, k => by
    show ((osHsCoef _ _ _ _ _ _).1 ++ (osHsCoefs src dst sc si di n (i + 1) _).1).filterMap callVs = []
    rw [calls_append, osHsCoefs_calls src dst sc si di n (i + 1)]
    unfold osHsCoef; split_ifs <;> rfl

theorem osHsMid_calls (lvl : ℕ) (lv : OsLv) (s : OsSt) : (osHsMid lvl lv s).1.filterMap callVs = [] :=
  osHsCoefs_calls _ _ _ _ _ _ _ _

theorem osHsFinal_calls (c : OsCfg) (lv : OsLv) (s : OsSt) : (osHsFinal c lv s).1.filterMap callVs = [] := by
  show (osHeap _ _ ++ _).filterMap callVs = []
  rw [calls_append, osHeap_calls, osHsCoefs_calls]
  rfl

theorem osGlue_calls (lvl : ℕ) (s : OsSt) : (osGlue lvl s).1.filterMap callVs = [] := rfl

theorem osHead_calls (c : OsCfg) : (osHead c).1.filterMap callVs = [] := by
  unfold osHead
  dsimp only
  simp only [calls_append, osHeap_calls, osPad_calls, List.nil_append, List.append_nil]
  rw [calls_flatten]
  · rfl
  · intro a ha
    simp only [List.mem_map, List.mem_range] at ha
    obtain ⟨t, -, rfl⟩ := ha
    rfl

/-! ## Single calls -/

theorem cvOf_call (f : String) (a r : List V) (σ : Val) : cvOf [.call f a r] σ = [(a ++ r).map σ] := rfl

/-- A run of values from `r`, read off its cells. -/
theorem osRun_vals {σ : Val} {r n : ℕ} {rets : List E} (hl : rets.length = n)
    (h : ∀ j < n, σ (.n (r + j)) = rets.getD j 0) : (osRun r n).map σ = rets := by
  refine List.ext_getElem (by simp [osRun, hl]) fun j h1 h2 ↦ ?_
  simp only [osRun, List.length_map, List.length_range] at h1
  simp only [osRun, List.getElem_map, List.getElem_range]
  rw [h j h1, List.getD_eq_getElem _ _ h2]

end
end LeanVM.Guest.B1.Whir
