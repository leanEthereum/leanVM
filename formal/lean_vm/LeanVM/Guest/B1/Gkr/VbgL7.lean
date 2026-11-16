/-
  LeanVM.Guest.B1.Gkr.VbgL7

  `verify_bus_gkr`'s layer loop `verify_bus_gkr_loop0` loads from a region holding its buffers and
  the cursor's words, on a memory holding the buffers' honest words.
-/

module

public import LeanVM.Guest.B1.Gkr.Loop7In
public import LeanVM.Guest.B1.Gkr.VbgComplete
public import LeanVM.Guest.Data.NameStrings

/-!
# `verify_bus_gkr_loop0` in `verify_bus_gkr`, loading from its buffers

`vbg_loop7_relIn`: on a memory holding the buffers' honest words (`vbgLay`), the call of
`verify_bus_gkr_loop0` from `1` below `g^((depth - 1)/2)` loads from any region holding the cursor's
words and the buffers `layers`, `rounds` and the rows: iteration `j`'s slot, row, records and
cursor (`Ly7In`) are the honest slot's (`GkSlot`, layer index `j + 1 - sh`) and records'
(`LyRecs`), inside the buffers.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem gkPos_closed (sh : ℕ) : ∀ k, 2 * gkPos sh k = 2 * sh + k * k + k + 2 * (k * sh)
  | 0 => by simp [gkPos]
  | k + 1 => by rw [gkPos, mul_add, mul_add, mul_add, gkPos_closed sh k]; ring

/-- **`verify_bus_gkr_loop0` loads from the buffers** (TRIAGE G #43): at `3 ≤ depth ≤ 32`, an
accepting run of `gkrPhase depth`, the buffers' honest words in memory (`vbgLay`),
`verify_bus_gkr_loop0`'s relation from `1` below `g^((depth - 1)/2)` loads from any region holding
the cursor's words and the buffers. -/
theorem vbg_loop7_relIn {depth : ℕ} (hd : depth ≤ 32) {cap0 xs : List E}
    {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) {ec eL eR eP eB eO eV : ℕ} {rd : Reader}
    {R : ℕ → Prop}
    (hm : MemLay rd (vbgLay depth cap0 xs (ofK (addressOfIndex ec)) eL eR eP eB eO eV))
    (hRx : ∀ i < xs.length, R (ec + i)) (hRL : ∀ i < 10 * (depth + 2), R (eL + i))
    (hRR : ∀ i < 6034, R (eR + i)) (hRr : ∀ i < 1640, R (eP + i))
    (hm0 : 0 < (depth - 1) / 2) {tabs claim stream : E}
    (h : coreProgram.Rel rd name% «verify_bus_gkr_loop0» [1, gen ^ ((depth - 1) / 2),
        gen ^ (2 - depth % 2), ofK (addressOfIndex eL), tabs, ofK (addressOfIndex eP),
        ofK (addressOfIndex eR), claim, gen ^ (depth % 2), stream, gen ^ depth] []) :
    coreProgram.RelIn rd R name% «verify_bus_gkr_loop0» [1, gen ^ ((depth - 1) / 2),
        gen ^ (2 - depth % 2), ofK (addressOfIndex eL), tabs, ofK (addressOfIndex eP),
        ofK (addressOfIndex eR), claim, gen ^ (depth % 2), stream, gen ^ depth] [] := by
  obtain ⟨-, -, -, hsteps, -, -, -, -⟩ := gk_walk hrun hc
  obtain ⟨sp, hsp⟩ := hc
  have hsc : capOf sp.state = cap0 := hsp.1
  have hcl : cap0.length = 5 := by rw [← hsc]; simp [capOf]
  unfold vbgLay at hm
  rw [memLay_append, memLay_append, memLay_append] at hm
  obtain ⟨⟨⟨hmS, -⟩, hmC⟩, -⟩ := hm
  set sh := depth % 2 with hsh
  set M := depth / 2 with hM
  have hsh2 : sh < 2 := by omega
  have hpl : ∀ j ≤ M, (gkSl cap0 xs sh j).2.1.point.length = 2 * j + sh :=
    gkSl_point_len (gkSl0_point_len cap0 xs sh hsh2) fun j hj => (hsteps j hj).1
  -- the iterations
  have hit : ∀ j < (depth - 1) / 2, Ly7In rd R (ofK (addressOfIndex eL))
      (ofK (addressOfIndex eP)) (ofK (addressOfIndex eR)) sh j := by
    intro j hj
    set k := j + 1 - sh with hk
    have hkM : k < M := by omega
    obtain ⟨hok, hdr⟩ := hsteps k hkM
    have hLk : 2 * j + 2 - sh = 2 * k + sh := by omega
    have hi : k + sh - 1 < M + sh := by omega
    have hik : k + sh - 1 + 1 - sh = k := by omega
    have hS := hmS _ (List.mem_map.mpr ⟨k + sh - 1, List.mem_range.mpr hi, rfl⟩)
    simp only [hik] at hS
    have hpos : LoadHolds rd (ofK (addressOfIndex eL)) (10 * (2 * k + sh) + 9) (gen ^ gkPos sh k) := by
      have h := tb_reads_load hS (k := 9) (by simp [gkSlotWords, (gkSl_inv (xs := xs) (sh := sh) hcl k).1,
        (gkSl_inv (xs := xs) (sh := sh) hcl k).2.1])
      simpa [gkSlotWords, (gkSl_inv (xs := xs) (sh := sh) hcl k).1,
        (gkSl_inv (xs := xs) (sh := sh) hcl k).2.1, List.getD_eq_getElem?_getD] using h
    have hcs : (gkD cap0 xs sh k).cs.length = 2 * k + sh := hok.1.trans (hpl k (by omega))
    have hR := lyRecs_of (fun q hq => hmC q (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨j,
      List.mem_range.mpr hj, rfl⟩, hq⟩)) hcs (by omega) hsh2
    rw [show k + sh - 1 = j by omega] at hR
    have hO : (gkSl cap0 xs sh (k + 1)).2.2 = (gkSl cap0 xs sh k).2.2 + 4 * (2 * k + sh) + 12 :=
      rfl
    have h12 : (3 : ℕ) * 2 ^ 2 = 12 := by norm_num
    have hO1 : (gkSl cap0 xs sh (k + 1)).2.2 ≤ xs.length := by
      refine tb_drop_le hdr ?_ (by rw [hO]; omega)
      rw [gkStepD_xs_length hok, hpl k (by omega), hO]
      omega
    have hp := gkPos_closed sh k
    have hkk : k * k ≤ 15 * 15 := Nat.mul_le_mul (by omega) (by omega)
    have hks : k * sh ≤ 15 * 1 := Nat.mul_le_mul (by omega) (by omega)
    refine ⟨gen ^ gkPos sh k, ofK (addressOfIndex ec) * gen ^ (gkSl cap0 xs sh k).2.2, ?_,
      by rw [hLk]; exact hpos, ?_, ?_, ?_, fun y hy ↦ ?_, ?_⟩
    · rw [hLk, tb_ofK_gpow_mul]
      exact ptrIn_ofK fun i hi ↦ by rw [Nat.add_assoc]; exact hRL _ (by omega)
    · rw [hLk, tb_ofK_gpow_mul]
      exact ptrIn_ofK fun i hi ↦ by rw [Nat.add_assoc]; exact hRr _ (by omega)
    · rw [tb_ofK_gpow_mul]
      exact ptrIn_ofK fun i hi ↦ by rw [Nat.add_assoc]; exact hRR _ (by omega)
    · rw [hLk, tb_ofK_gpow_mul]
      exact ptrIn_ofK fun i hi ↦ by rw [Nat.add_assoc]; exact hRx _ (by omega)
    · have h := (hR.1 y hy).2.1
      rwa [show 4 * (2 * y) = 8 * y by ring] at h
    · have h := hR.2.2.1
      rwa [hcs, ← hLk] at h
  obtain ⟨d, hd'⟩ := h
  rw [show (1 : E) = gen ^ 0 from (pow_zero _).symm] at hd' ⊢
  exact loop7_relIn hsh2 hit d 0 hm0 hd'

end
end LeanVM.Guest.B1.Tables
