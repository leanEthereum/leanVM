/-
  LeanVM.Guest.CoreNames

  The names of the core program's functions are distinct, so a function is found by its name.
-/

module

public import LeanVM.Guest.CoreData

/-!
# Distinct function names

Strings are compared slowly in the kernel, so names are never compared with each other: each is
encoded once as a number (`encS`), reduced modulo `namesMod`, and the residues are checked
pairwise distinct in one pass through a bit set (`nodupBits`, `coreProgram_codes_nodup`); equal
names would give equal residues (`coreProgram_names_nodup`). `namesMod` is the smallest modulus
under which the residues differ, from `scripts/core-names-modulus`, rerun when the guest's names
change.
-/

namespace LeanVM.Guest

open Core

@[expose] public section

/-- The bytes of a name as digits in base `2^9`, each shifted by one. -/
def encL : List UInt8 → ℕ
  | [] => 0
  | c :: cs => (c.toNat + 1) + 2 ^ 9 * encL cs

/-- The encoding of a name. -/
def encS (s : String) : ℕ := encL s.toByteArray.data.toList

/-- The modulus under which the names' encodings differ (`scripts/core-names-modulus`). -/
def namesMod : ℕ := 108082

/-- Pairwise distinctness through the bit set `seen`: each entry's bit is clear, then set. -/
def nodupBits : List ℕ → ℕ → Bool
  | [], _ => true
  | x :: xs, seen => !seen.testBit x && nodupBits xs (seen ||| 2 ^ x)

theorem nodup_of_nodupBits : ∀ {l : List ℕ} {seen : ℕ}, nodupBits l seen = true →
    l.Nodup ∧ ∀ x ∈ l, seen.testBit x = false
  | [], _, _ => ⟨List.nodup_nil, by simp⟩
  | x :: xs, seen, h => by
    simp only [nodupBits, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hn, hb⟩ := nodup_of_nodupBits h.2
    refine ⟨List.nodup_cons.mpr ⟨fun hm ↦ ?_, hn⟩, fun y hy ↦ ?_⟩
    · simpa [Nat.testBit_or, Nat.testBit_two_pow_self] using hb x hm
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact h.1
      · have := hb y hy
        simp only [Nat.testBit_or, Bool.or_eq_false_iff] at this
        exact this.1

set_option maxRecDepth 100000 in
/-- **The names' residues are distinct**, by one kernel evaluation. -/
theorem coreProgram_codes_nodup : (coreProgram.map fun f ↦ encS f.name % namesMod).Nodup :=
  (nodup_of_nodupBits (seen := 0) (by decide +kernel)).1

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
