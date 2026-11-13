/-
  LeanVM.Guest.CoreFind

  Finding a function of a core program by its name, for any program: `Program.indexOf?`, and
  `Finds P name fn`, the hypothesis a proof about one function takes in place of the guest's data.
-/

module

public import LeanVM.Guest.Core

/-!
# Functions found by name

A proof about one core function `fn` states it for every program that finds `fn` under its name
(`Finds P name fn`), so it imports the core module holding that function (its pack,
`Guest/Pack/P<k>/Core.lean`, or its own, `Guest/Pack/<key>/Core.lean`) and no other data; the glue (`CoreData.lean` and the instantiations beside the proofs) gives the
instance for the guest's `coreProgram`.
-/

namespace LeanVM.Guest

open Core

@[expose] public section

/-- The index of the first function of a name. -/
def Core.Program.indexOf? (P : Program) (n : String) : Option Nat := P.findIdx? (·.name == n)

/-- A function found by its index. -/
theorem Core.Program.find?_of_indexOf? {n : String} :
    ∀ {P : Program} {j : Nat} {f : Fn}, P.indexOf? n = some j → P[j]? = some f →
      P.find? n = some f
  | [], _, _, h, _ => by simp [Program.indexOf?] at h
  | g :: P, j, f, h, hj => by
      unfold Program.indexOf? at h
      unfold Program.find?
      by_cases hg : (g.name == n) = true
      · simp only [List.findIdx?_cons, hg, ↓reduceIte, Option.some.injEq] at h
        subst h
        simpa [List.find?_cons, hg] using hj
      · simp only [List.findIdx?_cons, hg] at h
        obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [List.getElem?_cons_succ] at hj
        simpa [List.find?_cons, hg, Program.find?] using find?_of_indexOf? hk hj

/-- **The program `P` finds `fn` under `name`.** -/
class Finds (P : Program) (name : String) (fn : Fn) : Prop where
  find : P.find? name = some fn

end
end LeanVM.Guest
