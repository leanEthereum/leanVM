/-
  LeanVM.Guest.B1.Gkr.VbgLoads

  `verify_bus_gkr`'s honest valuation: its allocations, pointers and sizes, and every load inside
  one of its buffers.
-/

module

public import LeanVM.Guest.B1.Gkr.VbgMem

/-!
# Pointers and loads

On the honest valuation (`Fwd.ev` of `vbgEvL` with the allocations answered by `vbgW`):
`vbg_ptrs` gives the allocations' pointers, `layers`' size `g^(13·(depth + 2))` and every pointer
a load goes through (the cursor, `layers`, the rows, the tables shifted by `depth`, `layers`
shifted to the last slot, the values' buffer). `vbg_loadOk`: every load of `vbgEvL` (a kernel
check lists them by pointer and offset) lands inside the cursor's words, `layers`, the point rows,
a table or the values' buffer.
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
      (p == 5 && decide (off < 14)) || ((p == 16 && decide (off < 39)) ||
        ((p == 18 && decide (off < 42)) || ((p == 64 && decide (off < 8)) ||
        (((p == 73 || p == 74) && decide (off < 33)) ||
        (((p == 141 || p == 377 || p == 381) && off == 0) ||
        ((p == 388 && decide (off < 10)) || (p == 394 && decide (off < 3))))))))
  | .atom (.load ..) => false
  | _ => true

theorem vbg_loadOk : vbgEvL.all vbgLoadOk = true := by decide +kernel

section
variable {rd : Reader} {W : ℕ → E} {args : List E} {σ : Val}

/-- **The pointers** of the honest valuation. -/
theorem vbg_ptrs (hσ : σ = B1.Val.ofArgs (ev rd W args vbgEvL))
    (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS W σ s) {depth : ℕ} {cap0 : List E} {cur zeta tabs : E}
    (hcl : cap0.length = 5) (hargs : args = cap0 ++ [cur, gen ^ depth, zeta, tabs])
    {layers rounds rows kmn bnd odd vals : E} (hW : W = vbgW layers rounds rows kmn bnd odd vals) :
    σ (.n 5) = cur ∧ σ (.n 6) = gen ^ depth ∧ σ (.n 15) = gen ^ (13 * (depth + 2)) ∧
      σ (.n 16) = layers ∧ σ (.n 17) = rounds ∧ σ (.n 18) = rows ∧ σ (.n 64) = kmn ∧
      σ (.n 73) = bnd ∧ σ (.n 74) = odd ∧ σ (.n 141) = odd * gen ^ depth ∧
      σ (.n 377) = bnd * gen ^ depth ∧ σ (.n 381) = bnd * gen ^ depth ∧
      σ (.n 388) = layers * gen ^ (13 * depth) ∧ σ (.n 394) = vals := by
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp vb_chk
  have hl : args.length = 9 := by rw [hargs]; simp [hcl]
  have par : ∀ i < 9, σ (.n i) = args.getD i 0 := fun i hi ↦ by
    rw [hσ]; exact ev_params rd W (by rw [hl]; exact hc') (by rw [hl]; exact hi)
  have e5 : σ (.n 5) = cur := by rw [par 5 (by omega), hargs]; simp [hcl]
  have e6 : σ (.n 6) = gen ^ depth := by rw [par 6 (by omega), hargs]; simp [hcl]
  have g : ∀ a : Atom, vbgEvL.any (fun t ↦ tbStmtsEqb [.atom a] [t]) = true → Good rd vbgS W σ a :=
    fun a h ↦ hG _ (vbg_mem h)
  have mul : ∀ d x y : ℕ, vbgEvL.any (fun t ↦ tbStmtsEqb [.atom (.mul (.n d) (.n x) (.n y))] [t])
      = true → x < d → y < d → σ (.n d) = σ (.n x) * σ (.n y) :=
    fun d x y h hx hy ↦ good_mul (g _ h) hx hy
  have c9 : σ (.n 9) = gen ^ 2 := by
    rw [← tb_word_four]; exact g (.const (.n 9) (word 4 0)) (by decide +kernel)
  have m10 := mul 10 6 9 (by decide +kernel) (by omega) (by omega)
  have m11 := mul 11 10 10 (by decide +kernel) (by omega) (by omega)
  have m12 := mul 12 11 10 (by decide +kernel) (by omega) (by omega)
  have m13 := mul 13 12 12 (by decide +kernel) (by omega) (by omega)
  have m14 := mul 14 13 13 (by decide +kernel) (by omega) (by omega)
  have m15 := mul 15 14 10 (by decide +kernel) (by omega) (by omega)
  have al : ∀ (a : Atom) (d : ℕ), vbgEvL.any (fun t ↦ tbStmtsEqb [.atom a] [t]) = true →
      Good rd vbgS W σ a = (σ (.n d) = W d) → σ (.n d) = W d :=
    fun a d h e ↦ e ▸ g a h
  have e16 : σ (.n 16) = layers := by
    rw [al (.hint (.allocDyn (.n 16) (.n 15))) 16 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e17 : σ (.n 17) = rounds := by
    rw [al (.hint (.alloc (.n 17) 6034)) 17 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e18 : σ (.n 18) = rows := by
    rw [al (.hint (.alloc (.n 18) 1640)) 18 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e64 : σ (.n 64) = kmn := by
    rw [al (.hint (.alloc (.n 64) 8)) 64 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e73 : σ (.n 73) = bnd := by
    rw [al (.hint (.alloc (.n 73) 33)) 73 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e74 : σ (.n 74) = odd := by
    rw [al (.hint (.alloc (.n 74) 33)) 74 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e394 : σ (.n 394) = vals := by
    rw [al (.hint (.alloc (.n 394) 3)) 394 (by decide +kernel) rfl, hW]; simp [vbgW]
  have m141 := mul 141 74 6 (by decide +kernel) (by omega) (by omega)
  have m377 := mul 377 73 6 (by decide +kernel) (by omega) (by omega)
  have m381 := mul 381 73 6 (by decide +kernel) (by omega) (by omega)
  have m383 := mul 383 6 6 (by decide +kernel) (by omega) (by omega)
  have m384 := mul 384 383 6 (by decide +kernel) (by omega) (by omega)
  have m385 := mul 385 384 384 (by decide +kernel) (by omega) (by omega)
  have m386 := mul 386 385 385 (by decide +kernel) (by omega) (by omega)
  have m387 := mul 387 386 6 (by decide +kernel) (by omega) (by omega)
  have m388 := mul 388 16 387 (by decide +kernel) (by omega) (by omega)
  refine ⟨e5, e6, ?_, e16, e17, e18, e64, e73, e74, by rw [m141, e74, e6], by rw [m377, e73, e6],
    by rw [m381, e73, e6], ?_, e394⟩
  · rw [m15, m14, m13, m12, m11, m10, e6, c9, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add, ← pow_add]
    ring_nf
  · rw [m388, m387, m386, m385, m384, m383, e16, e6, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add]
    ring_nf

end

end
end LeanVM.Guest.B1.Tables
