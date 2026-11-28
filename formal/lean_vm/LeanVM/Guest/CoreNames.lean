/-
  LeanVM.Guest.CoreNames

  The names of the core program's functions are distinct, so a function is found by its name.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.CompiledNames

/-!
# Distinct function names

Strings are compared slowly in the kernel, so names are never compared with each other: each is
encoded once as a number (`encS`, `NameIx.lean`), reduced modulo `namesMod`, and the residues are checked
pairwise distinct in one pass through a bit set on the compiled function table
(`CompiledNames.lean`), whose names are the core program's (`names_eq`, `coreProgram_codes_nodup`);
equal names would give equal residues (`coreProgram_names_nodup`). `namesMod` is the smallest modulus
under which the residues differ (`CoreNamesMod.lean`, written by `scripts/core-names-modulus` when the guest's
names change).
-/

namespace LeanVM.Guest

open Core

@[expose] public section

/-- **The names' residues are distinct**: they are the compiled functions' (`names_eq`). -/
theorem coreProgram_codes_nodup : (coreProgram.map fun f ↦ encS f.name % namesMod).Nodup := by
  have h := compiled_codes_nodup
  rw [← names_eq, List.map_map] at h
  exact h

theorem coreProgram_names_nodup : (coreProgram.map (·.name)).Nodup := by
  have h : ((coreProgram.map (·.name)).map fun s ↦ encS s % namesMod).Nodup := by
    rw [List.map_map]
    exact coreProgram_codes_nodup
  exact h.of_map _

private theorem find_getElem_of_nodup :
    ∀ {l : List Fn}, (l.map (·.name)).Nodup → ∀ {j : ℕ} (h : j < l.length),
      l.find? (fun g ↦ g.name == l[j].name) = some l[j]
  | [], _, j, h => absurd h (Nat.not_lt_zero _)
  | g :: l, hn, j, h => by
    rw [List.map_cons, List.nodup_cons] at hn
    cases j with
    | zero => simp
    | succ j =>
      have hj : j < l.length := Nat.lt_of_succ_lt_succ h
      have hne : g.name ≠ (l[j]'hj).name := fun e ↦
        hn.1 (List.mem_map.mpr ⟨l[j], List.getElem_mem hj, e.symm⟩)
      have hb : (g.name == (l[j]'hj).name) = false := by simpa using hne
      rw [List.getElem_cons_succ, List.find?_cons, hb]
      exact find_getElem_of_nodup hn.2 hj

theorem coreProgram_find_getElem {j : ℕ} (h : j < coreProgram.length) :
    coreProgram.find? coreProgram[j].name = some coreProgram[j] :=
  find_getElem_of_nodup coreProgram_names_nodup h

end
end LeanVM.Guest
