/-
  LeanVM.Guest.B1.Gkr.VbgLoads

  `verify_bus_gkr`'s honest valuation: its allocations, pointers and sizes, and every load inside
  one of its buffers.
-/

module

public import LeanVM.Guest.B1.Gkr.VbgMem

/-!
# Pointers and loads

On the honest valuation (`Fwd.ev` of `vbgEvL` with the allocations answered by `vbgW`), on a
memory holding `layers`' level-0 slot: `vbg_ptrs` gives the allocations' pointers, `layers`'
size `g^(17·(depth + 2))` and every pointer a load goes through (the cursor, `layers`, the tables
shifted by `depth`, the cursor two words on and the second point row, read from the level-0
slot, `layers` shifted to the last slot). `vbg_loads`: every load of `vbgEvL` (a kernel check
lists them by pointer and offset) lands inside the cursor's words, `layers`, the point rows or a
table.
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
      (p == 5 && decide (off < 2)) || ((p == 15 && decide (off < 34)) ||
        ((p == 56 && decide (off < 8)) ||
        (((p == 65 || p == 66) && decide (off < 33)) || ((p == 133 && off == 0) ||
        ((p == 171 && decide (off < 6)) || ((p == 181 && off == 0) ||
        (((p == 310 || p == 314) && off == 0) || (p == 321 && decide (off < 10)))))))))
  | .atom (.load ..) => false
  | _ => true

theorem vbg_loadOk : vbgEvL.all vbgLoadOk = true := by decide +kernel

theorem tb_word_g40 : word 1099511627776 0 0 = gen ^ 40 := by
  rw [show (1099511627776 : ℕ) = 2 ^ 40 by norm_num, tb_word_two_pow (by norm_num)]

theorem gkSlotWords_getD5 {s : Fs} {cur : E} {st : GkrState} {row pos half par : E}
    (hcl : s.cap.length = 5) : (gkSlotWords s cur st row pos half par).getD 5 0 = cur := by
  obtain ⟨c0, c1, c2, c3, c4, hc⟩ := tb_list5_eq hcl
  simp [gkSlotWords, hc]

theorem gkSlotWords_getD9 {s : Fs} {cur : E} {st : GkrState} {row pos half par : E}
    (hcl : s.cap.length = 5) (hvl : st.values.length = 3) :
    (gkSlotWords s cur st row pos half par).getD 9 0 = row := by
  obtain ⟨c0, c1, c2, c3, c4, hc⟩ := tb_list5_eq hcl
  obtain ⟨v0, v1, v2, hv⟩ := tb_list3_eq hvl
  simp [gkSlotWords, hc, hv]

section
variable {depth : ℕ} {cap0 xs : List E} {cur : E} {eP : ℕ}

/-- `layers`' level-0 slot's cursor and row. -/
theorem vbgLayBlock0 (hcl : cap0.length = 5) (hcan : AllCanonical cap0) :
    (vbgLayBlock depth cap0 xs cur eP 0).getD 5 0 = cur * gen ^ 2 ∧
      (vbgLayBlock depth cap0 xs cur eP 0).getD 9 0 = ofK (addressOfIndex eP) := by
  have inv := gkSl_inv (xs := xs) (sh := depth % 2) hcl hcan 0
  unfold vbgLayBlock
  by_cases h : 0 % 2 = depth % 2 ∧ 0 ≤ depth
  · simp only [h, and_self, ↓reduceIte]
    have hsh : depth % 2 ≠ 1 := by omega
    have hoff := gkSl0_off cap0 xs (depth % 2)
    simp only [hsh, ↓reduceIte] at hoff
    simp only [Nat.zero_sub, Nat.zero_div, vbgSlotW]
    refine ⟨by rw [gkSlotWords_getD5 inv.1, hoff], ?_⟩
    rw [gkSlotWords_getD9 inv.1 inv.2.2.2]
    simp [show depth % 2 = 0 by omega]
  · simp only [h, ↓reduceIte]
    exact ⟨gkSlotWords_getD5 hcl, gkSlotWords_getD9 hcl (by simp [gkRootSt])⟩

end

section
variable {rd : Reader} {W : ℕ → E} {args : List E} {σ : Val}

/-- **The pointers** of the honest valuation. -/
theorem vbg_ptrs (hσ : σ = B1.Val.ofArgs (ev rd W args vbgEvL))
    (hG : ∀ s ∈ vbgEvL, GoodS rd vbgS W σ s) {depth : ℕ} {cap0 : List E} {cur zeta : E}
    (hcl : cap0.length = 5) (hargs : args = cap0 ++ [cur, gen ^ depth, zeta])
    {layers rounds rows kmn pairs dsh : E} (hW : W = vbgW layers rounds rows kmn pairs dsh)
    (h5 : LoadHolds rd layers 5 (cur * gen ^ 2)) (h9 : LoadHolds rd layers 9 rows) :
    σ (.n 5) = cur ∧ σ (.n 6) = gen ^ depth ∧ σ (.n 14) = gen ^ (17 * (depth + 2)) ∧
      σ (.n 15) = layers ∧ σ (.n 16) = rounds ∧ σ (.n 17) = rows ∧ σ (.n 56) = kmn ∧
      σ (.n 65) = pairs ∧
      σ (.n 66) = dsh ∧ σ (.n 133) = dsh * gen ^ depth ∧ σ (.n 171) = cur * gen ^ 2 ∧
      σ (.n 181) = rows * gen ^ 40 ∧ σ (.n 310) = pairs * gen ^ depth ∧
      σ (.n 314) = pairs * gen ^ depth ∧ σ (.n 321) = layers * gen ^ (17 * depth) := by
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp vb_chk
  have hl : args.length = 8 := by rw [hargs]; simp [hcl]
  have par : ∀ i < 8, σ (.n i) = args.getD i 0 := fun i hi ↦ by
    rw [hσ]; exact ev_params rd W (by rw [hl]; exact hc') (by rw [hl]; exact hi)
  have e5 : σ (.n 5) = cur := by rw [par 5 (by omega), hargs]; simp [hcl]
  have e6 : σ (.n 6) = gen ^ depth := by rw [par 6 (by omega), hargs]; simp [hcl]
  have g : ∀ a : Atom, vbgEvL.any (fun t ↦ tbStmtsEqb [.atom a] [t]) = true → Good rd vbgS W σ a :=
    fun a h ↦ hG _ (vbg_mem h)
  have mul : ∀ d x y : ℕ, vbgEvL.any (fun t ↦ tbStmtsEqb [.atom (.mul (.n d) (.n x) (.n y))] [t])
      = true → x < d → y < d → σ (.n d) = σ (.n x) * σ (.n y) :=
    fun d x y h hx hy ↦ good_mul (g _ h) hx hy
  have c8 : σ (.n 8) = gen ^ 2 := by
    rw [← tb_word_four]; exact g (.const (.n 8) (word 4 0 0)) (by decide +kernel)
  have m9 := mul 9 6 8 (by decide +kernel) (by omega) (by omega)
  have m10 := mul 10 9 9 (by decide +kernel) (by omega) (by omega)
  have m11 := mul 11 10 10 (by decide +kernel) (by omega) (by omega)
  have m12 := mul 12 11 11 (by decide +kernel) (by omega) (by omega)
  have m13 := mul 13 12 12 (by decide +kernel) (by omega) (by omega)
  have m14 := mul 14 13 9 (by decide +kernel) (by omega) (by omega)
  have al : ∀ (a : Atom) (d : ℕ), vbgEvL.any (fun t ↦ tbStmtsEqb [.atom a] [t]) = true →
      Good rd vbgS W σ a = (σ (.n d) = W d) → σ (.n d) = W d :=
    fun a d h e ↦ e ▸ g a h
  have e15 : σ (.n 15) = layers := by
    rw [al (.hint (.allocDyn (.n 15) (.n 14))) 15 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e16 : σ (.n 16) = rounds := by
    rw [al (.hint (.alloc (.n 16) 6034)) 16 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e17 : σ (.n 17) = rows := by
    rw [al (.hint (.alloc (.n 17) 1640)) 17 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e56 : σ (.n 56) = kmn := by
    rw [al (.hint (.alloc (.n 56) 8)) 56 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e65 : σ (.n 65) = pairs := by
    rw [al (.hint (.alloc (.n 65) 33)) 65 (by decide +kernel) rfl, hW]; simp [vbgW]
  have e66 : σ (.n 66) = dsh := by
    rw [al (.hint (.alloc (.n 66) 33)) 66 (by decide +kernel) rfl, hW]; simp [vbgW]
  have m133 := mul 133 66 6 (by decide +kernel) (by omega) (by omega)
  have m310 := mul 310 65 6 (by decide +kernel) (by omega) (by omega)
  have m314 := mul 314 65 6 (by decide +kernel) (by omega) (by omega)
  have m316 := mul 316 6 6 (by decide +kernel) (by omega) (by omega)
  have m317 := mul 317 316 316 (by decide +kernel) (by omega) (by omega)
  have m318 := mul 318 317 317 (by decide +kernel) (by omega) (by omega)
  have m319 := mul 319 318 318 (by decide +kernel) (by omega) (by omega)
  have m320 := mul 320 319 6 (by decide +kernel) (by omega) (by omega)
  have m321 := mul 321 15 320 (by decide +kernel) (by omega) (by omega)
  have r171 := good_read (g (.load (.n 171) (.n 15) 5) (by decide +kernel)) (by decide +kernel)
    (v := cur * gen ^ 2) (by rw [e15]; exact h5)
  have r179 := good_read (g (.load (.n 179) (.n 15) 9) (by decide +kernel)) (by decide +kernel)
    (v := rows) (by rw [e15]; exact h9)
  have c180 : σ (.n 180) = gen ^ 40 := by
    rw [← tb_word_g40]; exact g (.const (.n 180) (word 1099511627776 0 0)) (by decide +kernel)
  have m181 := mul 181 179 180 (by decide +kernel) (by omega) (by omega)
  refine ⟨e5, e6, ?_, e15, e16, e17, e56, e65, e66, by rw [m133, e66, e6], r171.1,
    by rw [m181, r179.1, c180], by rw [m310, e65, e6], by rw [m314, e65, e6], ?_⟩
  · rw [m14, m13, m12, m11, m10, m9, e6, c8, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add, ← pow_add]
    ring_nf
  · rw [m321, m320, m319, m318, m317, m316, e15, e6, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add]
    ring_nf

end

end
end LeanVM.Guest.B1.Tables
