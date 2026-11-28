/-
  LeanVM.Guest.CompiledNames

  The compiled functions' names are distinct, by their codes' residues (`CoreNames.lean` transfers it
  to the core program, whose names are theirs).
-/

module

public import LeanVM.Guest.Data.Functions
import all LeanVM.Guest.Data.Functions
public import LeanVM.Guest.CoreNamesMod
public import LeanVM.Guest.NameIx

/-!
# Distinct compiled names

Strings are compared slowly in the kernel, so names are never compared with each other: each is
encoded once as a number (`encS`, `NameIx.lean`), reduced modulo `namesMod`, and the residues are
checked pairwise distinct in one pass through a bit set (`nodupBits`). The check reads the compiled
function table alone, not the core IR, so it runs beside the core IR's modules, not after them.
-/

namespace LeanVM.Guest

@[expose] public section

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
/-- **The compiled functions' names' residues are distinct**, after `__jump_tables`, by one kernel
evaluation. -/
theorem compiled_codes_nodup :
    ((Data.functions.tail.map CompiledFunction.name).map fun s ↦ encS s % namesMod).Nodup :=
  (nodup_of_nodupBits (seen := 0) (by decide +kernel)).1

end
end LeanVM.Guest
