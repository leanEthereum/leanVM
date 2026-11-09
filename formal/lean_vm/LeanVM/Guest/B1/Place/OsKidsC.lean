/-
  LeanVM.Guest.B1.Place.OsKidsC

  The callee relation of a placed body: every call complete on the caller's words. After mumbai's
  `B1/Whir/OsKidsA.lean`.
-/

module

public import LeanVM.Guest.B1.Place.OsPlace
public import LeanVM.Guest.B1.Place.OsKids
public import LeanVM.Guest.B1.Whir.Flat

/-!
# The callees of a placed body, from its `Rel`-level walk

`osKC fs cert κ Lk`: the relation "the callee is `CompleteAtD` on the words `Lk`, returning the
frame's words". A flat block proved at that relation (`AllOk`, as `open_stacked`'s blocks are,
generic in the relation) gives every taken call's placed completeness (`kids_of_allOk`), what
`os_kids_block` takes. `osKC_of`: a callee's `CompleteRelD` on a meaning holding on every memory
holding `Lk`. `os_readsAt_shift`, `os_reads_noLow`: reading the caller's words.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir (AllOk StmtOk)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- A callee complete on the words `Lk`, returning its frame's words. -/
def osKC (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (Lk : Layout) : CallRel :=
  fun f a r => CompleteAtD fs cert κ f Lk a (Returns r)

theorem os_readsAt_shift {rd : Reader} {cur : E} {xs : List E} (h : ReadsAt rd cur xs) {p n : ℕ}
    (hp : p + n ≤ xs.length) : ReadsAt rd (cur * gen ^ p) ((xs.drop p).take n) := by
  intro k hk
  simp only [List.length_take, List.length_drop] at hk
  rw [loadHolds_mul_gen_pow, List.getElem_take, List.getElem_drop]
  exact h (p + k) (by omega)

end
end LeanVM.Guest.B1
