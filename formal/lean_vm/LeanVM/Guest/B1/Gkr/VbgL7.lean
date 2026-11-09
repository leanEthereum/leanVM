/-
  LeanVM.Guest.B1.Gkr.VbgL7

  `verify_bus_gkr`'s layer loop `__loop6` loads from a region holding its buffers and the cursor's
  words, on a memory holding the buffers' honest words.
-/

module

public import LeanVM.Guest.B1.Gkr.Loop7In
public import LeanVM.Guest.B1.Gkr.VbgComplete

/-!
# `__loop6` in `verify_bus_gkr`, loading from its buffers

`vbg_loop7_relIn`: on a memory holding the buffers' honest words (`vbgLay`), the call of
`__loop6` from `1` below `g^(depth/2)` loads from any region holding the cursor's words and the
buffers `layers`, `rounds`, the rows and `depth_shift`: iteration `j`'s slot, row, records and
cursor (`Ly7In`) are the honest slot's (`GkSlotC`) and records' (`RecsAt`), inside the buffers.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem gkPos_closed (sh : ℕ) : ∀ j, gkPos sh j = sh + j * j + j * sh
  | 0 => by simp [gkPos]
  | j + 1 => by rw [gkPos, gkPos_closed sh j]; ring

/-- **`__loop6` loads from the buffers** (TRIAGE G #43): at `2 ≤ depth ≤ 32`, an accepting run of
`gkrPhase depth`, the buffers' honest words in memory (`vbgLay`), `__loop6`'s relation from `1`
below `g^(depth/2)` loads from any region holding the cursor's words and the buffers. -/
theorem vbg_loop7_relIn {depth : ℕ} (hd : depth ≤ 32) {cap0 xs : List E}
    {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) {ec eL eR eP eK ePa eD : ℕ} {rd : Reader}
    {R : ℕ → Prop}
    (hm : MemLay rd (vbgLay depth cap0 xs (ofK (addressOfIndex ec)) eL eR eP eK ePa eD))
    (hRx : ∀ i < xs.length, R (ec + i)) (hRL : ∀ i < 17 * (depth + 2), R (eL + i))
    (hRR : ∀ i < 6034, R (eR + i)) (hRr : ∀ i < 1640, R (eP + i)) (hRK : ∀ i < 8, R (eK + i))
    (hRD : ∀ i < 33, R (eD + i)) (hm0 : 0 < depth / 2)
    (h : coreProgram.Rel rd "__loop6" [1, gen ^ (depth / 2), ofK (addressOfIndex eD), gen ^ depth,
      ofK (addressOfIndex eL), ofK (addressOfIndex eR), ofK (addressOfIndex eK)] []) :
    coreProgram.RelIn rd R "__loop6" [1, gen ^ (depth / 2), ofK (addressOfIndex eD), gen ^ depth,
      ofK (addressOfIndex eL), ofK (addressOfIndex eR), ofK (addressOfIndex eK)] [] := by
  obtain ⟨-, -, -, hsteps, -, -, -, -⟩ := gk_walk hrun hc
  obtain ⟨sp, hsp⟩ := hc
  have hsc : capOf sp.state = cap0 := hsp.1
  have hcl : cap0.length = 5 := by rw [← hsc]; simp [capOf]
  have hcan : AllCanonical cap0 := by rw [← hsc]; exact tb_capOf_canonical _
  unfold vbgLay at hm
  rw [memLay_append, memLay_append, memLay_append, memLay_append] at hm
  obtain ⟨⟨⟨⟨-, hmS⟩, hmP⟩, hmC⟩, hmT⟩ := hm
  set sh := depth % 2 with hsh
  set m := depth / 2 with hmm
  have hsh2 : sh < 2 := by omega
  have inv := gkSl_inv (xs := xs) (sh := sh) hcl hcan
  have hpl : ∀ j ≤ m, (gkSl cap0 xs sh j).2.1.point.length = 2 * j + sh :=
    gkSl_point_len (gkSl0_point_len cap0 xs sh hsh2) fun j hj => (hsteps j hj).1
  have SL : ∀ j ≤ m, GkSlotC rd (ofK (addressOfIndex eL)) (2 * j + sh) (gkSl cap0 xs sh j).1
      (ofK (addressOfIndex ec) * gen ^ (gkSl cap0 xs sh j).2.2) (gkSl cap0 xs sh j).2.1
      (ofK (addressOfIndex eP) * gen ^ (40 * (j + sh))) (gen ^ gkPos sh j) (gen ^ (j / 4))
      (gen ^ (j % 4)) := fun j hj =>
    gkSlotC_of (inv j).1 (inv j).2.1 (inv j).2.2.1 (inv j).2.2.2 (hpl j hj)
      (by rw [tb_ofK_gpow_mul]
          have := hmP _ (List.mem_map.mpr ⟨j, List.mem_range.mpr (show j < m + 1 by omega), rfl⟩)
          exact this)
      (by have := hmS _ (List.mem_map.mpr ⟨j, List.mem_range.mpr (show j < m + 1 by omega), rfl⟩)
          exact this)
  -- `depth_shift[depth]`
  have hD := hmT _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hsh' : LoadHolds rd (ofK (addressOfIndex eD) * gen ^ depth) 0 (gen ^ sh) := by
    rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]
    have := hD depth (by simp; omega)
    simpa [hsh] using this
  have hshR : PtrIn R (ofK (addressOfIndex eD) * gen ^ depth) 1 := by
    rw [tb_ofK_gpow_mul]
    exact ptrIn_ofK fun i hi ↦ by rw [Nat.add_assoc]; exact hRD _ (by omega)
  -- the iterations
  have hit : ∀ j < m, Ly7In rd R (ofK (addressOfIndex eL)) (ofK (addressOfIndex eR)) sh j := by
    intro j hj
    obtain ⟨hok, hdr⟩ := hsteps j hj
    obtain ⟨-, -, -, -, -, -, -, -, hrow, -, -, hpos, hhalf, hpar⟩ := SL j (by omega)
    have hcs : (gkD cap0 xs sh j).cs.length = 2 * j + sh := hok.1.trans (hpl j (by omega))
    have hR := recsAt_of (fun q hq => hmC q (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨j,
      List.mem_range.mpr hj, rfl⟩, hq⟩)) hcs
    have hO : (gkSl cap0 xs sh (j + 1)).2.2 = (gkSl cap0 xs sh j).2.2 + 4 * (2 * j + sh) + 12 :=
      rfl
    have h12 : (3 : ℕ) * 2 ^ 2 = 12 := by norm_num
    have hO1 : (gkSl cap0 xs sh (j + 1)).2.2 ≤ xs.length := by
      refine tb_drop_le hdr ?_ (by rw [hO]; omega)
      rw [gkStepD_xs_length hok, hpl j (by omega), hO]
      omega
    have hp := gkPos_closed sh j
    have hjj : j * j ≤ 15 * 15 := Nat.mul_le_mul (by omega) (by omega)
    have hjs : j * sh ≤ 15 * 1 := Nat.mul_le_mul (by omega) (by omega)
    refine ⟨ofK (addressOfIndex eP) * gen ^ (40 * (j + sh)), gen ^ gkPos sh j,
      ofK (addressOfIndex ec) * gen ^ (gkSl cap0 xs sh j).2.2, ?_, hrow, hpos, hhalf, hpar, ?_,
          ?_, ?_,
      fun r hr ↦ ?_⟩
    · rw [tb_ofK_gpow_mul]
      exact ptrIn_ofK fun i hi ↦ by rw [Nat.add_assoc]; exact hRL _ (by omega)
    · rw [tb_ofK_gpow_mul]
      exact ptrIn_ofK fun i hi ↦ by rw [Nat.add_assoc]; exact hRr _ (by omega)
    · rw [tb_ofK_gpow_mul]
      exact ptrIn_ofK fun i hi ↦ by rw [Nat.add_assoc]; exact hRR _ (by omega)
    · rw [tb_ofK_gpow_mul]
      exact ptrIn_ofK fun i hi ↦ by rw [Nat.add_assoc]; exact hRx _ (by omega)
    · exact (hR r (by omega)).2.1
  obtain ⟨d, hd'⟩ := h
  rw [show (1 : E) = gen ^ 0 from (pow_zero _).symm] at hd' ⊢
  exact loop7_relIn hsh' hshR (ptrIn_ofK hRK) hit d 0 hm0 hd'

end
end LeanVM.Guest.B1.Tables
