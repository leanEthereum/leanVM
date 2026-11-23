/-
  LeanVM.Guest.B1.Gkr.GlCInVbg

  `verify_bus_gkr`'s radix-four layers (`gkr_layers__L{o}`) load from a region holding its buffers
  and the cursor's words, on a memory holding the buffers' honest words.
-/

module

public import LeanVM.Guest.B1.Gkr.GlCIn
public import LeanVM.Guest.B1.Gkr.GlCInLs
public import LeanVM.Guest.B1.Gkr.VbgComplete
public import LeanVM.Guest.Data.NameStrings

/-!
# `gkr_layers__L{o}` in `verify_bus_gkr`, loading from its buffers

`vbg_layers_relIn`: on a memory holding the buffers' honest words (`vbgLay`), the call of
`gkr_layers__L{depth % 2}` at `n_four = g^((depth - 1)/8)`, `rem_g = g^(((depth - 1)/2) % 4)`
loads from any region holding the cursor's words and the buffers `layers`, `rounds` and the rows:
layer `j`'s slot and cursor (`GlIn`) are the honest slot's (layer index `j + 1 - sh`), its records
inside the round records.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The layers' first records and their counts fit a field of the round records. -/
theorem gkPos_fits : ∀ d < 33, ∀ j < (d - 1) / 2, gkPos (d % 2) (j + 1 - d % 2) + j / 4 ≤ 860 := by
  decide

/-- **`gkr_layers__L{o}` loads from the buffers**: at `depth ≤ 32`, an accepting run of
`gkrPhase depth`, the buffers' honest words in memory (`vbgLay`), its relation loads from any
region holding the cursor's words and the buffers. -/
theorem vbg_layers_relIn {depth : ℕ} (hd : depth ≤ 32) {cap0 xs : List E}
    {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) {ec eL eR eP eO eB eM eV : ℕ} {rd : Reader}
    {R : ℕ → Prop}
    (hm : MemLay rd (vbgLay depth cap0 xs (ofK (addressOfIndex ec)) eL eR eP eO eB eM eV))
    (hRx : ∀ i < xs.length, R (ec + i)) (hRL : ∀ i < 10 * (depth + 2), R (eL + i))
    (hRR : ∀ i < 6034, R (eR + i)) (hRr : ∀ i < 1640, R (eP + i)) {gmu tabs stream : E}
    {rets : List E}
    (h : coreProgram.Rel rd (glcLsN (depth % 2)) [ofK (addressOfIndex eL),
      ofK (addressOfIndex eR), ofK (addressOfIndex eP), gen ^ ((depth - 1) / 8),
      gen ^ ((depth - 1) / 2 % 4), gen ^ (2 - depth % 2), gmu, tabs, stream] rets) :
    coreProgram.RelIn rd R (glcLsN (depth % 2)) [ofK (addressOfIndex eL),
      ofK (addressOfIndex eR), ofK (addressOfIndex eP), gen ^ ((depth - 1) / 8),
      gen ^ ((depth - 1) / 2 % 4), gen ^ (2 - depth % 2), gmu, tabs, stream] rets := by
  obtain ⟨-, -, -, hsteps, -, -, -, -⟩ := gk_walk hrun hc
  obtain ⟨sp, hsp⟩ := hc
  have hsc : capOf sp.state = cap0 := hsp.1
  have hcl : cap0.length = 5 := by rw [← hsc]; simp [capOf]
  unfold vbgLay at hm
  rw [memLay_append, memLay_append, memLay_append] at hm
  obtain ⟨⟨⟨hmS, -⟩, -⟩, -⟩ := hm
  set sh := depth % 2 with hsh
  set M := depth / 2 with hM
  have hsh2 : sh < 2 := by omega
  have hpl : ∀ j ≤ M, (gkSl cap0 xs sh j).2.1.point.length = 2 * j + sh :=
    gkSl_point_len (gkSl0_point_len cap0 xs sh hsh2) fun j hj => (hsteps j hj).1
  -- the layers' words
  have hit : ∀ j < (depth - 1) / 2, GlIn rd R (ofK (addressOfIndex eL))
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
    have inv := gkSl_inv (xs := xs) (sh := sh) hcl k
    have hword : ∀ i < 10, LoadHolds rd (ofK (addressOfIndex eL)) (10 * (2 * k + sh) + i)
        ((gkSlotWords (gkSl cap0 xs sh k).1
          (ofK (addressOfIndex ec) * gen ^ (gkSl cap0 xs sh k).2.2) (gkSl cap0 xs sh k).2.1
          (gen ^ gkPos sh k)).getD i 0) := fun i hi ↦
      tb_reads_load hS (k := i) (by simp [gkSlotWords, inv.1, inv.2.1]; omega)
    have hpos := hword 9 (by omega)
    have hcur := hword 5 (by omega)
    simp [gkSlotWords, inv.1, inv.2.1, List.getD_eq_getElem?_getD] at hpos
    simp [gkSlotWords, inv.1, inv.2.1, List.getD_eq_getElem?_getD] at hcur
    have hO : (gkSl cap0 xs sh (k + 1)).2.2 = (gkSl cap0 xs sh k).2.2 + 4 * (2 * k + sh) + 12 :=
      rfl
    have hO1 : (gkSl cap0 xs sh (k + 1)).2.2 ≤ xs.length := by
      refine tb_drop_le hdr ?_ (by rw [hO]; omega)
      rw [gkStepD_xs_length hok, hpl k (by omega), hO]
      omega
    have hpb : gkPos sh k + j / 4 ≤ 860 := gkPos_fits depth (by omega) j hj
    refine ⟨gen ^ gkPos sh k, ofK (addressOfIndex ec) * gen ^ (gkSl cap0 xs sh k).2.2, ?_,
      by rw [hLk]; exact hpos, by rw [hLk]; exact hcur, ?_, ?_, ?_⟩
    · rw [hLk, tb_ofK_gpow_mul]
      exact ptrIn_ofK fun i hi ↦ by rw [Nat.add_assoc]; exact hRL _ (by omega)
    · rw [hLk, tb_ofK_gpow_mul]
      exact ptrIn_ofK fun i hi ↦ by rw [Nat.add_assoc]; exact hRr _ (by omega)
    · rw [tb_ofK_gpow_mul]
      exact ptrIn_ofK fun i hi ↦ by rw [Nat.add_assoc]; exact hRR _ (by omega)
    · rw [hLk, tb_ofK_gpow_mul]
      exact ptrIn_ofK fun i hi ↦ by rw [Nat.add_assoc]; exact hRx _ (by omega)
  refine gls_relIn (by omega) (by omega) (fun j hj hgl ↦ ?_) h
  obtain ⟨m, p, hp, rfl⟩ : ∃ m p, p < 4 ∧ j = 4 * m + p :=
    ⟨j / 4, j % 4, Nat.mod_lt _ (by omega), by omega⟩
  unfold GlLay at hgl
  unfold GlLayIn
  rw [show (4 * m + p) % 4 = p by omega, show (4 * m + p) / 4 = m by omega] at hgl ⊢
  exact gl_relIn hp hsh2 (by omega) (hit _ (by omega)) hgl

end
end LeanVM.Guest.B1.Tables
