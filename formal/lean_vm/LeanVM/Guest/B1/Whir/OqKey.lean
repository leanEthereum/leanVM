/-
  LeanVM.Guest.B1.Whir.OqKey

  `opening_queries`' specializations looked up by their numbers.
-/

module

public import LeanVM.Guest.B1.Whir.NameNums
public import LeanVM.Guest.B1.Whir.Witness

/-!
# `opening_queries`' entries by numbers

A specialization's name is `opening_queries__L` and its shape's eleven numbers (`oqName_eq`), and
so is every entry's of `openingQueriesLoops` (`oq_names`, by the kernel, once). So the entry of
a name (`oqEntry`) is the entry of its numbers (`oqEntry_oqName`, by `find_name_key`): the
decided facts look entries up by numbers and build no string.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.B1

@[expose] public section

/-- A shape's numbers, as its name writes them. -/
def _root_.LeanVM.Guest.B1.OqShape.key (s : OqShape) : List ℕ :=
  [s.odd, s.base, s.folds, s.leafCells, s.depth, s.cd, s.mu, s.vanish, s.nHs, s.hsBits, s.final]

/-- The numbers `oqName` writes. -/
def oqKey (q base folds leaf d cd mu nhs hbits fin : ℕ) : List ℕ :=
  [q % 2 * base, base, folds, leaf, d, cd, mu, mu * (mu + 1) / 2, nhs, hbits, fin]

theorem oqName_eq (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    oqName q base folds leaf d cd mu nhs hbits fin =
      keyStr "opening_queries__L" (oqKey q base folds leaf d cd mu nhs hbits fin) := rfl

set_option maxRecDepth 100000 in
/-- Every entry's name is its shape's numbers. -/
theorem oq_names : ∀ e ∈ openingQueriesLoops, e.1 = keyStr "opening_queries__L" e.2.2.key := by
  decide +kernel

/-- The entry of the numbers `k`. -/
def oqEntryK (k : List ℕ) : Option (String × String × OqShape) :=
  openingQueriesLoops.find? fun e => e.2.2.key == k

theorem oqEntry_oqName (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    oqEntry (oqName q base folds leaf d cd mu nhs hbits fin) =
      oqEntryK (oqKey q base folds leaf d cd mu nhs hbits fin) := by
  rw [oqName_eq]
  exact find_name_key openingQueriesLoops _ keyStr_inj (fun x => x.2.key) oq_names _

/-- The numbers of level `lvl`'s `opening_queries` specialization (`osOqName`). -/
def osOqKey (c : OsCfg) (lvl : ℕ) (lv : OsLv) : List ℕ :=
  let fin := lvl = c.yrLevel
  oqKey lv.queries (lvBase lvl) lv.folds lv.leafCells lv.depth lv.capDepth
    (if fin then lv.logCols else 0) (if fin then c.yrLen + lv.folds else 0)
    (if fin then c.yrLog + 1 else 0) (if fin then 1 else 0)

theorem oqEntry_osOqName (c : OsCfg) (lvl : ℕ) (lv : OsLv) :
    oqEntry (osOqName c lvl lv) = oqEntryK (osOqKey c lvl lv) :=
  oqEntry_oqName ..

/-- The shape of the numbers `k`. -/
def oqShapeK (k : List ℕ) : OqShape := ((oqEntryK k).map (·.2.2)).getD oqShapeZero

theorem oqShapeOf_osOqName (c : OsCfg) (lvl : ℕ) (lv : OsLv) :
    oqShapeOf (osOqName c lvl lv) = oqShapeK (osOqKey c lvl lv) := by
  unfold oqShapeOf oqShapeK
  rw [oqEntry_osOqName]

theorem oqShapeOf_oqName (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    oqShapeOf (oqName q base folds leaf d cd mu nhs hbits fin) =
      oqShapeK (oqKey q base folds leaf d cd mu nhs hbits fin) := by
  unfold oqShapeOf oqShapeK
  rw [oqEntry_oqName]

/-- The entry of a name's numbers, when there is one, is the entry of the name. -/
theorem oqEntry_name_iff' (q base folds leaf d cd mu nhs hbits fin : ℕ) :
    (oqEntry (oqName q base folds leaf d cd mu nhs hbits fin)).map (·.1) =
        some (oqName q base folds leaf d cd mu nhs hbits fin) ↔
      (oqEntryK (oqKey q base folds leaf d cd mu nhs hbits fin)).isSome := by
  rw [oqEntry_oqName]
  constructor
  · intro h
    cases he : oqEntryK (oqKey q base folds leaf d cd mu nhs hbits fin) <;> simp_all
  · intro h
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp h
    rw [he, Option.map_some]
    have he' : openingQueriesLoops.find?
        (fun e => e.2.2.key == oqKey q base folds leaf d cd mu nhs hbits fin) = some e := he
    have hk := List.find?_some he'
    have hm := List.mem_of_find?_eq_some he'
    simp only [beq_iff_eq] at hk
    rw [oq_names e hm, hk]
    rfl

theorem oqEntry_name_iff (c : OsCfg) (lvl : ℕ) (lv : OsLv) :
    (oqEntry (osOqName c lvl lv)).map (·.1) = some (osOqName c lvl lv) ↔
      (oqEntryK (osOqKey c lvl lv)).isSome :=
  oqEntry_name_iff' ..

end
end LeanVM.Guest.B1.Whir
