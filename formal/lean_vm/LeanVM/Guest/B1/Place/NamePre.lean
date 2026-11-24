/-
  LeanVM.Guest.B1.Place.NamePre

  The specializations' families by their names' prefixes: names of two families differ, with no
  string compared.
-/

module

public import LeanVM.Guest.B1.Whir.TableKeys

/-!
# Names apart by their prefixes

A specialization's name starts with its family's base (`level_positions__L`, `level_residual__L`,
`level_residual_slow__L`, `level_queries__L`; `HasPre`). Two bases neither of which starts the
other (`Apart`, decided once on the two literals) start no common name (`ne_of_hasPre`), so a name
of one family is in no table of another (`not_mem_of_hasPre`) and the kernel never compares the
names themselves.
-/

namespace LeanVM.Guest.B1.Whir

@[expose] public section

/-- A string's UTF-8 bytes, which the kernel reads off a literal without decoding it. -/
abbrev bytesL (s : String) : List UInt8 := s.toByteArray.data.toList

theorem bytesL_append (s t : String) : bytesL (s ++ t) = bytesL s ++ bytesL t := by
  simp only [bytesL, String.toByteArray_append, ByteArray.toList_data_append]

/-- `s` starts with `p`, byte for byte. -/
abbrev HasPre (p s : String) : Prop := bytesL p <+: bytesL s

/-- Neither of `p` and `q` starts the other. -/
abbrev Apart (p q : String) : Prop := ¬ bytesL p <+: bytesL q ∧ ¬ bytesL q <+: bytesL p

/-- **Names starting with apart prefixes differ.** -/
theorem ne_of_hasPre {p q s t : String} (hpq : Apart p q) (hs : HasPre p s) (ht : HasPre q t) : s ≠ t := by
  rintro rfl
  exact (List.prefix_or_prefix_of_prefix hs ht).elim hpq.1 hpq.2

/-- A name starting with `p` is no entry of a table whose names start with `q`. -/
theorem not_mem_of_hasPre {α : Type} {p q s : String} {T : List (String × α)} (hpq : Apart p q)
    (hs : HasPre p s) (hT : ∀ e ∈ T, HasPre q e.1) : ∀ e ∈ T, e.1 ≠ s :=
  fun e he h ↦ ne_of_hasPre hpq hs (h ▸ hT e he) rfl

/-- A table whose names start with `q` has no entry named `s` starting with `p`. -/
theorem any_name_eq_false {α : Type} {p q s : String} {T : List (String × α)} (hpq : Apart p q)
    (hs : HasPre p s) (hT : ∀ e ∈ T, HasPre q e.1) : T.any (·.1 == s) = false :=
  List.any_eq_false.mpr fun e he h ↦ not_mem_of_hasPre hpq hs hT e he (beq_iff_eq.mp h)

theorem hasPre_append (p s t : String) : HasPre p (p ++ s ++ t) := by
  simp only [HasPre, bytesL_append, List.append_assoc]
  exact List.prefix_append _ _

theorem hasPre_foldl (f : String → ℕ → String) (hf : ∀ s m, HasPre s (f s m)) :
    ∀ (ns : List ℕ) (x : String), HasPre x (ns.foldl f x)
  | [], _ => List.prefix_refl _
  | m :: ms, x => (hf x m).trans (hasPre_foldl f hf ms (f x m))

theorem keyStr_hasPre (p : String) : ∀ ns : List ℕ, HasPre p (keyStr p ns)
  | [] => List.prefix_refl _
  | n :: ns => by
    have h : HasPre p (p ++ natStr n) := by
      simp only [HasPre, bytesL_append]
      exact List.prefix_append _ _
    simp only [keyStr]
    exact h.trans (hasPre_foldl _ (fun s m ↦ hasPre_append s "_L" (natStr m)) ns _)

/-! ## The families -/

theorem osPositionsName_hasPre (lv : OsLv) : HasPre "level_positions__L" (osPositionsName lv) := by
  rw [osPositionsName_eq]; exact keyStr_hasPre _ _

theorem osResidualName_hasPre (lv : OsLv) : HasPre "level_residual__L" (osResidualName lv) := by
  rw [osResidualName_eq]; exact keyStr_hasPre _ _

theorem osQueriesName_hasPre (c : OsCfg) (lvl : ℕ) (lv : OsLv) :
    HasPre "level_queries__L" (osQueriesName c lvl lv) := by
  rw [osQueriesName_eq]; exact keyStr_hasPre _ _

theorem osSlowName_hasPre (c : OsCfg) (lv : OsLv) : HasPre "level_residual_slow__L" (osSlowName c lv) := by
  simp only [HasPre, osSlowName, bytesL_append, List.append_assoc]
  exact List.prefix_append _ _

theorem lpTable_hasPre : ∀ e ∈ lpTable, HasPre "level_positions__L" e.1 :=
  fun e he ↦ by rw [lp_names e he]; exact keyStr_hasPre _ _

theorem lqTable_hasPre : ∀ e ∈ lqTable, HasPre "level_queries__L" e.1 :=
  fun e he ↦ by rw [lq_names e he]; exact keyStr_hasPre _ _

theorem lrTable_hasPre : ∀ e ∈ lrTable, HasPre "level_residual__L" e.1 :=
  fun e he ↦ by rw [lr_names e he]; exact keyStr_hasPre _ _

/-! ## The bases apart -/

theorem apart_pos_res : Apart "level_positions__L" "level_residual__L" := by decide +kernel
theorem apart_pos_queries : Apart "level_positions__L" "level_queries__L" := by decide +kernel
theorem apart_res_queries : Apart "level_residual__L" "level_queries__L" := by decide +kernel
theorem apart_slow_pos : Apart "level_residual_slow__L" "level_positions__L" := by decide +kernel
theorem apart_slow_res : Apart "level_residual_slow__L" "level_residual__L" := by decide +kernel
theorem apart_slow_queries : Apart "level_residual_slow__L" "level_queries__L" := by decide +kernel

end
end LeanVM.Guest.B1.Whir
