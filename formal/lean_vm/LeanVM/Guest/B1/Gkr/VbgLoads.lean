/-
  LeanVM.Guest.B1.Gkr.VbgLoads

  `verify_bus_gkr`'s honest valuation: its allocations, pointers and sizes, and every load inside
  one of its buffers.
-/

module

public import LeanVM.Guest.B1.Gkr.VbgMem
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_bus_gkr»

/-!
# Pointers and loads

On the honest valuation (`Fwd.ev` of `vbgEvL` with the allocations answered by `vbgW`):
`vbg_ptrs` gives the allocations' pointers, `layers`' size `g^(10·(depth + 2))`, the three
tables and `gkr_sizes` shifted by `depth`. `vbg_loadOk`: every load of `vbgEvL` (a kernel check lists them by
pointer and offset) lands inside the cursor's words, the root-most slot, the point rows, a table,
the last slot, the values' buffer or `gkr_sizes`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

theorem vbg_mem {s : Stmt} (h : vbgEvL.any (fun t ↦ tbStmtsEqb [s] [t]) = true) : s ∈ vbgEvL := by
  obtain ⟨t, ht, he⟩ := List.any_eq_true.mp h
  have := tbStmtsEqb_sound he
  simp only [List.cons.injEq, and_true] at this
  rw [this]; exact ht

/-- The pointer and offset classes of `vbgEvL`'s loads. -/
def vbgLoadOk : Stmt → Bool
  | .atom (.load _ (.n p) off) =>
      (p == (val% «verify_bus_gkr» "cursor@1") && decide (off < 14)) || ((p == (val% «verify_bus_gkr» "nxt") && decide (off < 10)) ||
        ((p == (val% «verify_bus_gkr» "gkr_pts") && decide (off < 42)) ||
        (((p == (val% «verify_bus_gkr» "depth_odd") || p == (val% «verify_bus_gkr» "four_bounds") || p == (val% «verify_bus_gkr» "four_rem")) && decide (off < 33)) ||
        (((p == (val% «verify_bus_gkr» "odd_g~0") || p == (val% «verify_bus_gkr» "n_four~0") || p == (val% «verify_bus_gkr» "rem_g~0")) && off == 0) ||
        ((p == (val% «verify_bus_gkr» "last") && decide (off < 10)) || ((p == (val% «verify_bus_gkr» "leaves") && decide (off < 3)) ||
        ((p == (val% «verify_bus_gkr» "gkr_sizes") && decide (off < 66)) || ((p == (val% «verify_bus_gkr» "rounds~0") && off == 0) ||
        (p == (val% «verify_bus_gkr» "gkr_pts~0") && off == 33)))))))))
  | .atom (.load ..) => false
  | _ => true

theorem vbg_loadOk : vbgEvL.all vbgLoadOk = true := by decide +kernel

section
variable {rd : Reader} {W : ℕ → E} {args : List E} {σ : Val}

/-- **The pointers** of the honest valuation. -/
theorem vbg_ptrs (hσ : σ = B1.Val.ofArgs (ev rd W args vbgEvL))
    (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS W σ s) {depth : ℕ} {cap0 : List E} {cur zeta tabs stream : E}
    (hcl : cap0.length = 5) (hargs : args = cap0 ++ [cur, gen ^ depth, zeta, tabs, stream])
    {layers sizes rounds rows odd bnd rem vals : E}
    (hW : W = vbgW layers sizes rounds rows odd bnd rem vals) :
    σ (.n (val% «verify_bus_gkr» "cursor@1")) = cur ∧ σ (.n (val% «verify_bus_gkr» "g_bus_mu")) = gen ^ depth ∧ σ (.n (val% «verify_bus_gkr» "layers~5")) = gen ^ (10 * (depth + 2)) ∧
      σ (.n (val% «verify_bus_gkr» "layers")) = layers ∧ σ (.n (val% «verify_bus_gkr» "rounds")) = rounds ∧ σ (.n (val% «verify_bus_gkr» "gkr_pts")) = rows ∧ σ (.n (val% «verify_bus_gkr» "depth_odd")) = odd ∧
      σ (.n (val% «verify_bus_gkr» "four_bounds")) = bnd ∧ σ (.n (val% «verify_bus_gkr» "four_rem")) = rem ∧ σ (.n (val% «verify_bus_gkr» "odd_g~0")) = odd * gen ^ depth ∧
      σ (.n (val% «verify_bus_gkr» "n_four~0")) = bnd * gen ^ depth ∧ σ (.n (val% «verify_bus_gkr» "rem_g~0")) = rem * gen ^ depth ∧ σ (.n (val% «verify_bus_gkr» "leaves")) = vals ∧
      σ (.n (val% «verify_bus_gkr» "gkr_sizes")) = sizes ∧ σ (.n (val% «verify_bus_gkr» "rounds~0")) = sizes * gen ^ depth ∧
      σ (.n (val% «verify_bus_gkr» "gkr_pts~0")) = sizes * gen ^ depth := by
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp vb_chk
  have hl : args.length = 10 := by rw [hargs]; simp [hcl]
  have par : ∀ i < (val% «verify_bus_gkr» "layers~0"), σ (.n i) = args.getD i 0 := fun i hi ↦ by
    rw [hσ]; exact ev_params rd W (by rw [hl]; exact hc') (by rw [hl]; exact hi)
  have e5 : σ (.n (val% «verify_bus_gkr» "cursor@1")) = cur := by rw [par 5 (by omega), hargs]; simp [hcl]
  have e6 : σ (.n (val% «verify_bus_gkr» "g_bus_mu")) = gen ^ depth := by rw [par 6 (by omega), hargs]; simp [hcl]
  have g : ∀ a : Atom, vbgEvL.any (fun t ↦ tbStmtsEqb [.atom a] [t]) = true → Good rd vbgS W σ a :=
    fun a h ↦ hG _ (vbg_mem h)
  have mul : ∀ d x y : ℕ, vbgEvL.any (fun t ↦ tbStmtsEqb [.atom (.mul (.n d) (.n x) (.n y))] [t])
      = true → x < d → y < d → σ (.n d) = σ (.n x) * σ (.n y) :=
    fun d x y h hx hy ↦ good_mul (g _ h) hx hy
  have c10 : σ (.n (val% «verify_bus_gkr» "layers~0")) = gen ^ 2 := by
    rw [← tb_word_four]; exact g (.const (.n (val% «verify_bus_gkr» "layers~0")) (word 4 0)) (by decide +kernel)
  have m11 := mul 11 6 10 (by decide +kernel) (by omega) (by omega)
  have m12 := mul 12 11 11 (by decide +kernel) (by omega) (by omega)
  have m13 := mul 13 12 12 (by decide +kernel) (by omega) (by omega)
  have m14 := mul 14 13 11 (by decide +kernel) (by omega) (by omega)
  have m15 := mul 15 14 14 (by decide +kernel) (by omega) (by omega)
  have al : ∀ (a : Atom) (d : ℕ), vbgEvL.any (fun t ↦ tbStmtsEqb [.atom a] [t]) = true →
      Good rd vbgS W σ a = (σ (.n d) = W d) → σ (.n d) = W d :=
    fun a d h e ↦ e ▸ g a h
  have e16 : σ (.n (val% «verify_bus_gkr» "layers")) = layers := by
    rw [al (.hint (.allocDyn (.n (val% «verify_bus_gkr» "layers")) (.n (val% «verify_bus_gkr» "layers~5")))) (val% «verify_bus_gkr» "layers") (by decide +kernel) rfl, hW]; simp [vbgW]
  have e17 : σ (.n (val% «verify_bus_gkr» "gkr_sizes")) = sizes := by
    rw [al (.hint (.alloc (.n (val% «verify_bus_gkr» "gkr_sizes")) 66)) (val% «verify_bus_gkr» "gkr_sizes") (by decide +kernel) rfl, hW]; simp [vbgW]
  have e90 : σ (.n (val% «verify_bus_gkr» "rounds")) = rounds := by
    rw [al (.hint (.allocDyn (.n (val% «verify_bus_gkr» "rounds")) (.n (val% «verify_bus_gkr» "rounds~1")))) (val% «verify_bus_gkr» "rounds") (by decide +kernel) rfl, hW]; simp [vbgW]
  have e93 : σ (.n (val% «verify_bus_gkr» "gkr_pts")) = rows := by
    rw [al (.hint (.allocDyn (.n (val% «verify_bus_gkr» "gkr_pts")) (.n (val% «verify_bus_gkr» "gkr_pts~1")))) (val% «verify_bus_gkr» "gkr_pts") (by decide +kernel) rfl, hW]; simp [vbgW]
  have e134 : σ (.n (val% «verify_bus_gkr» "depth_odd")) = odd := by
    rw [al (.hint (.alloc (.n (val% «verify_bus_gkr» "depth_odd")) 33)) (val% «verify_bus_gkr» "depth_odd") (by decide +kernel) rfl, hW]; simp [vbgW]
  have e136 : σ (.n (val% «verify_bus_gkr» "four_bounds")) = bnd := by
    rw [al (.hint (.alloc (.n (val% «verify_bus_gkr» "four_bounds")) 33)) (val% «verify_bus_gkr» "four_bounds") (by decide +kernel) rfl, hW]; simp [vbgW]
  have e137 : σ (.n (val% «verify_bus_gkr» "four_rem")) = rem := by
    rw [al (.hint (.alloc (.n (val% «verify_bus_gkr» "four_rem")) 33)) (val% «verify_bus_gkr» "four_rem") (by decide +kernel) rfl, hW]; simp [vbgW]
  have e494 : σ (.n (val% «verify_bus_gkr» "leaves")) = vals := by
    rw [al (.hint (.alloc (.n (val% «verify_bus_gkr» "leaves")) 3)) (val% «verify_bus_gkr» "leaves") (by decide +kernel) rfl, hW]; simp [vbgW]
  have m236 := mul (val% «verify_bus_gkr» "odd_g~0") (val% «verify_bus_gkr» "depth_odd") 6 (by decide +kernel) (by omega) (by omega)
  have m466 := mul (val% «verify_bus_gkr» "n_four~0") (val% «verify_bus_gkr» "four_bounds") 6 (by decide +kernel) (by omega) (by omega)
  have m468 := mul (val% «verify_bus_gkr» "rem_g~0") (val% «verify_bus_gkr» "four_rem") 6 (by decide +kernel) (by omega) (by omega)
  have m88 := mul (val% «verify_bus_gkr» "rounds~0") (val% «verify_bus_gkr» "gkr_sizes") 6 (by decide +kernel) (by omega) (by omega)
  have m91 := mul (val% «verify_bus_gkr» "gkr_pts~0") (val% «verify_bus_gkr» "gkr_sizes") 6 (by decide +kernel) (by omega) (by omega)
  refine ⟨e5, e6, ?_, e16, e90, e93, e134, e136, e137, by rw [m236, e134, e6], by rw [m466, e136, e6],
    by rw [m468, e137, e6], e494, e17, by rw [m88, e17, e6], by rw [m91, e17, e6]⟩
  rw [m15, m14, m13, m12, m11, e6, c10, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
  ring_nf

end

end
end LeanVM.Guest.B1.Tables
