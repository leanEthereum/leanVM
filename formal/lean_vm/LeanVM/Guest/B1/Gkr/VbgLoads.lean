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
`vbg_ptrs` gives the allocations' pointers, every pointer a load goes through (the cursor, the
tables, the tables shifted by `depth`, `layers`, the rows, `layers` shifted to the last record, the
values' buffer) and, from `loop_bounds[depth] = g^n`, the sizes of `layers` (`g^(13·(n + 1))`)
and of the rows (`g^(40·(n + 2))`). `vbg_loadOk`: every load of `vbgEvL` (a kernel check lists
them by pointer and offset) lands inside the cursor's words, a table, `layers`, the point rows or
the values' buffer.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Guest.Value LeanVM.Guest.B1
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
      (p == 5 && decide (off < 14)) || ((p == 53 && decide (off < 8)) ||
        (((p == 62 || p == 63 || p == 130) && decide (off < 33)) ||
        (((p == 164 || p == 174 || p == 186) && off == 0) ||
        ((p == 173 && decide (off < 13)) || ((p == 185 && decide (off < 42)) ||
        ((p == 426 && decide (off < 10)) || (p == 432 && decide (off < 3))))))))
  | .atom (.load ..) => false
  | _ => true

theorem vbg_loadOk : vbgEvL.all vbgLoadOk = true := by decide +kernel

section
variable {rd : Reader} {W : ℕ → E} {args : List E} {σ : Val}

/-- **The pointers** of the honest valuation, and the sizes from `loop_bounds[depth] = g^n`. -/
theorem vbg_ptrs (hσ : σ = B1.Val.ofArgs (ev rd W args vbgEvL))
    (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS W σ s) {depth : ℕ} {cap0 : List E} {cur zeta tabs : E}
    (hcl : cap0.length = 5) (hargs : args = cap0 ++ [cur, gen ^ depth, zeta, tabs])
    {layers rounds rows kmn bnd odd rlen vals : E}
    (hW : W = vbgW layers rounds rows kmn bnd odd rlen vals) :
    σ (.n 5) = cur ∧ σ (.n 6) = gen ^ depth ∧ σ (.n 53) = kmn ∧ σ (.n 62) = bnd ∧
      σ (.n 63) = odd ∧ σ (.n 130) = rlen ∧ σ (.n 173) = layers ∧ σ (.n 176) = rounds ∧
      σ (.n 185) = rows ∧ σ (.n 432) = vals ∧ σ (.n 164) = bnd * gen ^ depth ∧
      σ (.n 174) = rlen * gen ^ depth ∧ σ (.n 186) = odd * gen ^ depth ∧
      ∀ n : ℕ, σ (.n 165) = gen ^ n → σ (.n 172) = gen ^ (13 * (n + 1)) ∧
        σ (.n 184) = gen ^ (40 * (n + 2)) ∧ σ (.n 426) = layers * gen ^ (13 * n) := by
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
  have al : ∀ (a : Atom) (d : ℕ), vbgEvL.any (fun t ↦ tbStmtsEqb [.atom a] [t]) = true →
      Good rd vbgS W σ a = (σ (.n d) = W d) → σ (.n d) = W d :=
    fun a d h e ↦ e ▸ g a h
  have e53 : σ (.n 53) = kmn := by
    rw [al (.hint (.alloc (.n 53) 8)) 53 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e62 : σ (.n 62) = bnd := by
    rw [al (.hint (.alloc (.n 62) 33)) 62 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e63 : σ (.n 63) = odd := by
    rw [al (.hint (.alloc (.n 63) 33)) 63 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e130 : σ (.n 130) = rlen := by
    rw [al (.hint (.alloc (.n 130) 33)) 130 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e173 : σ (.n 173) = layers := by
    rw [al (.hint (.allocDyn (.n 173) (.n 172))) 173 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e176 : σ (.n 176) = rounds := by
    rw [al (.hint (.allocDyn (.n 176) (.n 175))) 176 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e185 : σ (.n 185) = rows := by
    rw [al (.hint (.allocDyn (.n 185) (.n 184))) 185 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e432 : σ (.n 432) = vals := by
    rw [al (.hint (.alloc (.n 432) 3)) 432 (by decide +kernel) rfl, hW]; simp [vbgW]
  have m164 := mul 164 62 6 (by decide +kernel) (by omega) (by omega)
  have m174 := mul 174 130 6 (by decide +kernel) (by omega) (by omega)
  have m186 := mul 186 63 6 (by decide +kernel) (by omega) (by omega)
  refine ⟨e5, e6, e53, e62, e63, e130, e173, e176, e185, e432, by rw [m164, e62, e6],
    by rw [m174, e130, e6], by rw [m186, e63, e6], fun n h165 ↦ ?_⟩
  have c166 : σ (.n 166) = gen := by
    rw [← tb_word_gen]; exact g (.const (.n 166) (word 2 0)) (by decide +kernel)
  have c177 : σ (.n 177) = gen ^ 2 := by
    rw [← tb_word_four]; exact g (.const (.n 177) (word 4 0)) (by decide +kernel)
  have m167 := mul 167 165 166 (by decide +kernel) (by omega) (by omega)
  have m168 := mul 168 167 167 (by decide +kernel) (by omega) (by omega)
  have m169 := mul 169 168 167 (by decide +kernel) (by omega) (by omega)
  have m170 := mul 170 169 169 (by decide +kernel) (by omega) (by omega)
  have m171 := mul 171 170 170 (by decide +kernel) (by omega) (by omega)
  have m172 := mul 172 171 167 (by decide +kernel) (by omega) (by omega)
  have m178 := mul 178 165 177 (by decide +kernel) (by omega) (by omega)
  have m179 := mul 179 178 178 (by decide +kernel) (by omega) (by omega)
  have m180 := mul 180 179 179 (by decide +kernel) (by omega) (by omega)
  have m181 := mul 181 180 178 (by decide +kernel) (by omega) (by omega)
  have m182 := mul 182 181 181 (by decide +kernel) (by omega) (by omega)
  have m183 := mul 183 182 182 (by decide +kernel) (by omega) (by omega)
  have m184 := mul 184 183 183 (by decide +kernel) (by omega) (by omega)
  have m421 := mul 421 165 165 (by decide +kernel) (by omega) (by omega)
  have m422 := mul 422 421 165 (by decide +kernel) (by omega) (by omega)
  have m423 := mul 423 422 422 (by decide +kernel) (by omega) (by omega)
  have m424 := mul 424 423 423 (by decide +kernel) (by omega) (by omega)
  have m425 := mul 425 424 165 (by decide +kernel) (by omega) (by omega)
  have m426 := mul 426 173 425 (by decide +kernel) (by omega) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [m172, m171, m170, m169, m168, m167, h165, c166]
    ring
  · rw [m184, m183, m182, m181, m180, m179, m178, h165, c177]
    ring
  · rw [m426, m425, m424, m423, m422, m421, h165, e173]
    ring

end

end
end LeanVM.Guest.B1.Tables
