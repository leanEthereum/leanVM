/-
  LeanVM.Guest.B1.Link.Arith.TablesL

  The tables with their coefficients as words (`tablesL`), equal to `tables()`, the coefficients'
  limbs checked by the kernel table by table and, for `KECCAK`, access by access.
-/

module

public import LeanVM.Guest.B1.Link.Arith.Lits
import Mathlib.Tactic.IntervalCases

/-!
# `tables()`, its coefficients as words

`tablesLits`: each table's coefficients' limbs (`linksLits`), written out; `tablesL`: the tables,
each coefficient replaced by its word (`litTable`). `tablesL_eq`: `tablesL = tables`, from
`litTable_self` and the limbs, which the kernel checks against the tables' own coefficients one
table, or one `KECCAK` access, at a time (`lits_t*`, `kec_*`): the coefficients are products in `E`
that the kernel evaluates slowly, so the normal forms read `tablesL` instead.
-/

namespace LeanVM.Guest.B1.Link.Arith

open LeanVM.Parameters LeanVM.Guest LeanVM.Protocol.Verifier

@[expose] public section

/-- `KECCAK`'s accesses' coefficients' limbs. -/
def kecLits : List AccessLits :=
  [⟨[], [(1, 0), (1, 1), (1, 0), (0, 1), (0, 1)], []⟩,
    ⟨[], [(1, 0), (1, 1), (1, 0), (0, 1), (0, 1)], []⟩,
    ⟨[], [(1, 0), (1, 1), (1, 0), (0, 1), (0, 1)], []⟩,
    ⟨[], [(1, 0), (1, 1), (1, 0), (0, 1), (0, 1)], []⟩,
    ⟨[], [(1, 0), (1, 1), (1, 0), (0, 1), (0, 1)], []⟩,
    ⟨[], [(1, 0), (1, 1), (1, 0), (0, 1), (0, 1)], []⟩,
    ⟨[], [(1, 0), (1, 1), (1, 0), (0, 1), (0, 1)], []⟩,
    ⟨[], [(1, 0), (1, 1), (1, 0), (0, 1), (0, 1)], []⟩,
    ⟨[], [(1, 0), (1, 1), (1, 0), (0, 1), (0, 1)], []⟩,
    ⟨[], [(1, 0), (0, 1)], []⟩,
    ⟨[], [(1, 0), (0, 1)], []⟩,
    ⟨[], [(1, 0), (0, 1)], []⟩,
    ⟨[], [(1, 0), (0, 1)], []⟩,
    ⟨[(1, 0)], [(1, 0), (1, 1), (0, 1), (0, 1)], []⟩,
    ⟨[(2, 0)], [(1, 0), (1, 1), (1, 0), (0, 1), (0, 1)], []⟩,
    ⟨[(4, 0)], [(1, 0), (1, 1), (1, 0), (0, 1), (0, 1)], []⟩,
    ⟨[(8, 0)], [(1, 0), (1, 1), (1, 0), (0, 1), (0, 1)], []⟩,
    ⟨[(16, 0)], [(1, 0), (1, 1), (1, 0), (0, 1), (0, 1)], []⟩,
    ⟨[(32, 0)], [(1, 0), (1, 1), (1, 0), (0, 1), (0, 1)], []⟩,
    ⟨[(64, 0)], [(1, 0), (1, 1), (1, 0), (0, 1), (0, 1)], []⟩,
    ⟨[(128, 0)], [(1, 0), (1, 1), (1, 0), (0, 1), (0, 1)], []⟩,
    ⟨[(256, 0)], [(1, 0), (1, 1), (1, 0)], []⟩,
    ⟨[(512, 0)], [(1, 0), (0, 1)], []⟩,
    ⟨[(1024, 0)], [(1, 0), (0, 1)], []⟩,
    ⟨[(2048, 0)], [(1, 0), (0, 1)], []⟩,
    ⟨[(4096, 0)], [(1, 0), (0, 1)], []⟩]

/-- Each table's coefficients' limbs, `linksLits` of its links. -/
def tablesLits : List LinksLits :=
  [⟨([(2, 0)], [(1, 0)]), [],
    [⟨[], [], [[(1, 0)]]⟩,
     ⟨[], [], [[(1, 0)]]⟩,
     ⟨[], [], [[(1, 0)], [(1, 0)]]⟩]⟩,
  ⟨([(2, 0)], [(1, 0)]), [],
    [⟨[], [(1, 0), (0, 1)], []⟩,
     ⟨[], [], [[(1, 0)]]⟩,
     ⟨[], [], [[(1, 0), (0, 1)]]⟩]⟩,
  ⟨([(2, 0)], [(1, 0)]), [],
    [⟨[], [], [[(1, 0)], [(0, 1)]]⟩]⟩,
  ⟨([(2, 0)], [(1, 0)]), [[(1, 0)], [(1, 0)]],
    [⟨[], [(1, 0)], []⟩,
     ⟨[(1, 0)], [], [[(1, 0), (1, 0)], [(4, 0)], [(1, 0)]]⟩,
     ⟨[], [], [[(1, 0)]]⟩]⟩,
  ⟨([(1, 0)], [(1, 0)]), [],
    [⟨[], [(1, 0)], []⟩,
     ⟨[], [(1, 0)], []⟩,
     ⟨[], [(1, 0)], []⟩]⟩,
  ⟨([(2, 0)], [(1, 0)]), [[(1, 0)], [(1, 0)], [(1, 0)], [(1, 0)], [(1, 0)]], kecLits⟩]

/-- The tables, each coefficient the word of its limbs. -/
def tablesL : List Table := (tables.zip tablesLits).map fun (tb, l) ↦ litTable tb l

theorem getElem_eq_getD' {α : Type} [Inhabited α] (l : List α) {n : ℕ} (h : n < l.length) :
    l[n] = l.getD n default := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- `KECCAK`'s accesses. -/
abbrev kecMem : List Access := (tables.getD 5 default).links.memory

theorem kec_0 : (kecMem.map accessLits).getD 0 default = kecLits.getD 0 default := by
  decide +kernel
theorem kec_1 : (kecMem.map accessLits).getD 1 default = kecLits.getD 1 default := by
  decide +kernel
theorem kec_2 : (kecMem.map accessLits).getD 2 default = kecLits.getD 2 default := by
  decide +kernel
theorem kec_3 : (kecMem.map accessLits).getD 3 default = kecLits.getD 3 default := by
  decide +kernel
theorem kec_4 : (kecMem.map accessLits).getD 4 default = kecLits.getD 4 default := by
  decide +kernel
theorem kec_5 : (kecMem.map accessLits).getD 5 default = kecLits.getD 5 default := by
  decide +kernel
theorem kec_6 : (kecMem.map accessLits).getD 6 default = kecLits.getD 6 default := by
  decide +kernel
theorem kec_7 : (kecMem.map accessLits).getD 7 default = kecLits.getD 7 default := by
  decide +kernel
theorem kec_8 : (kecMem.map accessLits).getD 8 default = kecLits.getD 8 default := by
  decide +kernel
theorem kec_9 : (kecMem.map accessLits).getD 9 default = kecLits.getD 9 default := by
  decide +kernel
theorem kec_10 : (kecMem.map accessLits).getD 10 default = kecLits.getD 10 default := by
  decide +kernel
theorem kec_11 : (kecMem.map accessLits).getD 11 default = kecLits.getD 11 default := by
  decide +kernel
theorem kec_12 : (kecMem.map accessLits).getD 12 default = kecLits.getD 12 default := by
  decide +kernel
theorem kec_13 : (kecMem.map accessLits).getD 13 default = kecLits.getD 13 default := by
  decide +kernel
theorem kec_14 : (kecMem.map accessLits).getD 14 default = kecLits.getD 14 default := by
  decide +kernel
theorem kec_15 : (kecMem.map accessLits).getD 15 default = kecLits.getD 15 default := by
  decide +kernel
theorem kec_16 : (kecMem.map accessLits).getD 16 default = kecLits.getD 16 default := by
  decide +kernel
theorem kec_17 : (kecMem.map accessLits).getD 17 default = kecLits.getD 17 default := by
  decide +kernel
theorem kec_18 : (kecMem.map accessLits).getD 18 default = kecLits.getD 18 default := by
  decide +kernel
theorem kec_19 : (kecMem.map accessLits).getD 19 default = kecLits.getD 19 default := by
  decide +kernel
theorem kec_20 : (kecMem.map accessLits).getD 20 default = kecLits.getD 20 default := by
  decide +kernel
theorem kec_21 : (kecMem.map accessLits).getD 21 default = kecLits.getD 21 default := by
  decide +kernel
theorem kec_22 : (kecMem.map accessLits).getD 22 default = kecLits.getD 22 default := by
  decide +kernel
theorem kec_23 : (kecMem.map accessLits).getD 23 default = kecLits.getD 23 default := by
  decide +kernel
theorem kec_24 : (kecMem.map accessLits).getD 24 default = kecLits.getD 24 default := by
  decide +kernel
theorem kec_25 : (kecMem.map accessLits).getD 25 default = kecLits.getD 25 default := by
  decide +kernel
theorem kecMem_length : kecMem.length = 26 := by decide +kernel

theorem kec_lits : kecMem.map accessLits = kecLits := by
  refine List.ext_getElem (by rw [List.length_map, kecMem_length]; rfl) fun j h1 h2 ↦ ?_
  have hj : j < 26 := by simpa [kecLits] using h2
  rw [getElem_eq_getD' _ h1, getElem_eq_getD' _ h2]
  interval_cases j
  exacts [kec_0, kec_1, kec_2, kec_3, kec_4, kec_5, kec_6, kec_7, kec_8, kec_9, kec_10, kec_11, kec_12, kec_13, kec_14, kec_15, kec_16, kec_17, kec_18, kec_19, kec_20, kec_21, kec_22, kec_23, kec_24, kec_25]
theorem lits_t0 : linksLits (tables.getD 0 default).links = tablesLits.getD 0 default := by
  decide +kernel
theorem lits_t1 : linksLits (tables.getD 1 default).links = tablesLits.getD 1 default := by
  decide +kernel
theorem lits_t2 : linksLits (tables.getD 2 default).links = tablesLits.getD 2 default := by
  decide +kernel
theorem lits_t3 : linksLits (tables.getD 3 default).links = tablesLits.getD 3 default := by
  decide +kernel
theorem lits_t4 : linksLits (tables.getD 4 default).links = tablesLits.getD 4 default := by
  decide +kernel
theorem lits_t5_head : (linksLits (tables.getD 5 default).links).next = (tablesLits.getD 5 default).next ∧
    (linksLits (tables.getD 5 default).links).operands = (tablesLits.getD 5 default).operands := by
  decide +kernel

theorem lits_t5 : linksLits (tables.getD 5 default).links = tablesLits.getD 5 default := by
  have h := lits_t5_head
  have hm : (linksLits (tables.getD 5 default).links).memory = (tablesLits.getD 5 default).memory :=
    kec_lits
  revert h hm
  generalize linksLits (tables.getD 5 default).links = a
  generalize tablesLits.getD 5 default = b
  intro h hm
  cases a; cases b
  simp_all

theorem tables_length : tables.length = 6 := by decide +kernel

theorem tables_lits : tables.map (fun tb ↦ linksLits tb.links) = tablesLits := by
  refine List.ext_getElem (by rw [List.length_map, tables_length]; rfl) fun t h1 h2 ↦ ?_
  have ht : t < 6 := by simpa [tablesLits] using h2
  rw [List.getElem_map, getElem_eq_getD' tables (by simpa using h1), getElem_eq_getD' _ h2]
  interval_cases t
  exacts [lits_t0, lits_t1, lits_t2, lits_t3, lits_t4, lits_t5]

/-- **`tablesL` is `tables()`.** -/
theorem tablesL_eq : tablesL = tables := by
  rw [tablesL, ← tables_lits, zip_map_self]
  simp only [litTable_self, List.map_id']

end

end LeanVM.Guest.B1.Link.Arith
