/-
  LeanVM.Guest.B1.Main.L5Pops

  The entries every valid tree of `main`'s children loop (`main_loop4`) of the honest shape pops: per child, its counts (`child_meta`), its two claim lists' digests', its deferred claim (`child_defer`) and DA digest (`child_da`) as the memory holds them, `verify_sub`'s.
-/

module

public import LeanVM.Guest.B1.Main.MainGoalsHL5T
public import LeanVM.Guest.B1.Main.MainPops
public import LeanVM.Guest.B1.Main.MainNoWit
public import LeanVM.Guest.B1.Digest.ClaimListPops
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main_loop4»

/-!
# The children loop's pops

* `l5Seg`: child `c`'s entries, its callees' given;
* `l5_popS`, `l5_chk`: `main_loop4`'s body's skeleton of entries and the products its proof reads, by the kernel.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest (valid_holds words_heap monoIs monoIs_sound genMulOk genMul_sound isAddAt add_sound
  atomsIn atoms_of_flat holdsList_flat)

@[expose] public section

variable {rd : Reader}

/-- **Child `c`'s entries in `main_loop4`**: its counts, its claim lists' digests' `px`, `ps`, its deferred claim and DA
digest, `verify_sub`'s `pv`. -/
def l5Seg (ex es : ℕ) (px ps : List Pop) (defer : List E) (da : E × E) (pv : List Pop) : List Pop :=
  ("child_meta", [gen ^ ex, gen ^ es]) :: (px ++ ps ++ [("child_defer", defer), ("child_da", [da.1, da.2])] ++ pv)

theorem l5_popS : (l5Pre ++ [l5Tail]).filterMap Stmt.popS = [some ("child_meta", .stack [.n (val% «main_loop4» "child_meta[0]"), .n (val% «main_loop4» "child_meta[1]")]), none, none,
    some ("child_defer", .heap (.n (val% «main_loop4» "carried")) 0 24), some ("child_da", .heap (.n (val% «main_loop4» "child_da")) 0 2), none, none, none] := by
  decide +kernel

theorem l5_chk : l5Pre.all Digest.Stmt.flat = true ∧ monoIs (atomsIn l5Pre) (.n (val% «main_loop4» "carried")) (.n (val% «main_loop4» "child_carried")) (.n (val% «main_loop4» "xc")) 24 = true ∧
    monoIs (atomsIn l5Pre) (.n (val% «main_loop4» "child_da")) (.n (val% «main_loop4» "da_digests")) (.n (val% «main_loop4» "xc")) 2 = true ∧ genMulOk (atomsIn l5Pre) (.n (val% «main_loop4» "s21#4")) (.n (val% «main_loop4» "xc")) = true ∧
    genMulOk (atomsIn l5Pre) (.n (val% «main_loop4» "s21#1")) (.n (val% «main_loop4» "xc")) = true ∧ (atomsIn l5Pre).any (isAddAt (.n (val% «main_loop4» "s21#2")) (.n (val% «main_loop4» "s21#1")) (.n (val% «main_loop4» "bound"))) = true := by
  decide +kernel

/-- A heap destination through `g^a` of a run the memory holds reads the run. -/
theorem l5_words_of_reads (σ : Val) {p : V} {a : ℕ} (hp : σ p = gen ^ a) {L : List E} (h : ReadsAt rd (gen ^ a) L) :
    Dest.words rd σ (.heap p 0 L.length) = L := by
  rw [words_heap σ hp]
  refine List.ext_getElem (by simp) fun k h1 h2 => ?_
  rw [List.getElem_map, List.getElem_range, Nat.zero_add]
  obtain ⟨-, hl⟩ := h k h2
  rw [gen_pow_eq_ofK, addr_ofK] at hl
  rw [hl]
  rfl

theorem l5_tail_args (σ : Val) : ([V.n (val% «main_loop4» "s21#4"), .n (val% «main_loop4» "bound"), .n (val% «main_loop4» "written"), .n (val% «main_loop4» "lx_table"), .n (val% «main_loop4» "cover"), .n (val% «main_loop4» "lx_slots_g"), .n (val% «main_loop4» "lean_sphincs_table"), .n (val% «main_loop4» "sp_cover"), .n (val% «main_loop4» "lean_sphincs_slots_g"), .n (val% «main_loop4» "child_carried"), .n (val% «main_loop4» "da_digests"), .n (val% «main_loop4» "seed_0"), .n (val% «main_loop4» "seed_1"),
    .n (val% «main_loop4» "child_pi"), .n (val% «main_loop4» "g_squares"), .n (val% «main_loop4» "child_fresh")] : List V).map σ = σ (.n (val% «main_loop4» "s21#4")) :: ((List.range 16).map V.n).tail.map σ := rfl

end
end LeanVM.Guest.B1.Main
