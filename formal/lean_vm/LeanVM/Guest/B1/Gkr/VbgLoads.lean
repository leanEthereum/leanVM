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
`vbg_ptrs` gives the allocations' pointers, `layers`' size `g^(10·(depth + 2))` and the three
tables shifted by `depth`. `vbg_loadOk`: every load of `vbgEvL` (a kernel check lists them by
pointer and offset) lands inside the cursor's words, the root-most slot, the point rows, a table,
the last slot or the values' buffer.
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
      (p == 5 && decide (off < 14)) || ((p == 173 && decide (off < 10)) ||
        ((p == 18 && decide (off < 42)) ||
        (((p == 63 || p == 65 || p == 66) && decide (off < 33)) ||
        (((p == 165 || p == 395 || p == 397) && off == 0) ||
        ((p == 409 && decide (off < 10)) || (p == 423 && decide (off < 3)))))))
  | .atom (.load ..) => false
  | _ => true

theorem vbg_loadOk : vbgEvL.all vbgLoadOk = true := by decide +kernel

section
variable {rd : Reader} {W : ℕ → E} {args : List E} {σ : Val}

/-- **The pointers** of the honest valuation. -/
theorem vbg_ptrs (hσ : σ = B1.Val.ofArgs (ev rd W args vbgEvL))
    (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS W σ s) {depth : ℕ} {cap0 : List E} {cur zeta tabs stream : E}
    (hcl : cap0.length = 5) (hargs : args = cap0 ++ [cur, gen ^ depth, zeta, tabs, stream])
    {layers rounds rows odd bnd rem vals : E}
    (hW : W = vbgW layers rounds rows odd bnd rem vals) :
    σ (.n (val% «verify_bus_gkr» "cursor@1")) = cur ∧ σ (.n (val% «verify_bus_gkr» "g_bus_mu")) = gen ^ depth ∧ σ (.n (val% «verify_bus_gkr» "layers~5")) = gen ^ (10 * (depth + 2)) ∧
      σ (.n (val% «verify_bus_gkr» "layers")) = layers ∧ σ (.n (val% «verify_bus_gkr» "rounds")) = rounds ∧ σ (.n (val% «verify_bus_gkr» "gkr_pts")) = rows ∧ σ (.n (val% «verify_bus_gkr» "depth_odd")) = odd ∧
      σ (.n (val% «verify_bus_gkr» "four_bounds")) = bnd ∧ σ (.n (val% «verify_bus_gkr» "four_rem")) = rem ∧ σ (.n (val% «verify_bus_gkr» "odd_g~0")) = odd * gen ^ depth ∧
      σ (.n (val% «verify_bus_gkr» "n_four~0")) = bnd * gen ^ depth ∧ σ (.n (val% «verify_bus_gkr» "rem_g~0")) = rem * gen ^ depth ∧ σ (.n (val% «verify_bus_gkr» "leaves")) = vals := by
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
    rw [al (.hint (.allocDyn (.n (val% «verify_bus_gkr» "layers")) (.n (val% «verify_bus_gkr» "layers~5")))) 16 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e17 : σ (.n (val% «verify_bus_gkr» "rounds")) = rounds := by
    rw [al (.hint (.alloc (.n (val% «verify_bus_gkr» "rounds")) 6034)) 17 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e18 : σ (.n (val% «verify_bus_gkr» "gkr_pts")) = rows := by
    rw [al (.hint (.alloc (.n (val% «verify_bus_gkr» "gkr_pts")) 1640)) 18 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e64 : σ (.n (val% «verify_bus_gkr» "depth_odd")) = odd := by
    rw [al (.hint (.alloc (.n (val% «verify_bus_gkr» "depth_odd")) 33)) 63 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e66 : σ (.n (val% «verify_bus_gkr» "four_bounds")) = bnd := by
    rw [al (.hint (.alloc (.n (val% «verify_bus_gkr» "four_bounds")) 33)) 65 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e67 : σ (.n (val% «verify_bus_gkr» "four_rem")) = rem := by
    rw [al (.hint (.alloc (.n (val% «verify_bus_gkr» "four_rem")) 33)) 66 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e427 : σ (.n (val% «verify_bus_gkr» "leaves")) = vals := by
    rw [al (.hint (.alloc (.n (val% «verify_bus_gkr» "leaves")) 3)) 423 (by decide +kernel) rfl, hW]; simp [vbgW]
  have m166 := mul 165 63 6 (by decide +kernel) (by omega) (by omega)
  have m399 := mul 395 65 6 (by decide +kernel) (by omega) (by omega)
  have m401 := mul 397 66 6 (by decide +kernel) (by omega) (by omega)
  refine ⟨e5, e6, ?_, e16, e17, e18, e64, e66, e67, by rw [m166, e64, e6], by rw [m399, e66, e6],
    by rw [m401, e67, e6], e427⟩
  rw [m15, m14, m13, m12, m11, e6, c10, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
  ring_nf

end

end
end LeanVM.Guest.B1.Tables
