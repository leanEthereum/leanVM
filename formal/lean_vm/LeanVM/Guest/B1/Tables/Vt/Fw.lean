/-
  LeanVM.Guest.B1.Tables.Vt.Fw

  `verify_tables`' framework claims: the memory and bytecode index extensions, the four column
  values stored in the claim pool with their `g^|point|`, and the pull side's reloads of them.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Fresh
public import LeanVM.Guest.B1.Tables.Vt.SelFw
public import LeanVM.Guest.B1.Selectors.Glue
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# The framework's claims

`vt_fw`: `index_mle` at `kb[1] = g^log_mem` and at `kb[0]·g^19` (the bytecode's log-size) give the index extensions
of the point's prefixes; the memory's two values, the final memory count and the final bytecode
count are `claim_pool[0 .. 3]`; the
pull side reloads the index values and the memory values from where the push side left them.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem vt_index_arm {rd : Reader} {σ : Val} {v r : ℕ} {point : List E} {κ : ℕ}
    (hz : ReadsAt rd (σ (.n (val% «verify_tables» "zeta"))) point) (hκ : κ ≤ point.length) (hκ34 : κ < 34)
    (hv : σ (.n v) = gen ^ κ)
    (hd : ∃ (j : ℕ) (h : j < vtImNames.length), σ (.n v) = ofK (Parameters.addressOfIndex j) ∧
      coreProgram.Rel rd vtImNames[j] ([V.n (val% «verify_tables» "zeta")].map σ) ([V.n r].map σ)) :
    σ (.n r) = indexMle (point.take κ) := by
  obtain ⟨j, hj, hjv, hrel⟩ := hd
  have hj34 : j < 34 := by simpa [vtImNames] using hj
  rw [hv, ← gen_pow_eq_ofK] at hjv
  obtain rfl := gen_pow_inj (by omega) (by omega) hjv
  simp only [vtImNames, List.getElem_map, List.getElem_range, List.map_cons, List.map_nil] at hrel
  obtain ⟨zs, hzl, hzr, hval⟩ := index_mle_holds κ hκ34 _ _ _ hrel
  rw [hval, tbReadsAt_unique hzr (tbReadsAt_take hz κ) (by simp; omega)]

/-- **The framework's claims.** -/
theorem vt_fw {rd : Reader} {σ : Val} (h : VtH rd σ) {point : List E}
    (hz : ReadsAt rd (σ (.n (val% «verify_tables» "zeta"))) point) {lm : ℕ} (hlm : lm ≤ point.length) (hlm34 : lm < 34)
    (h19 : 19 ≤ point.length) (hk1 : σ (.n (val% «verify_tables» "kb[1]")) = gen ^ lm) (hk2 : σ (.n (val% «verify_tables» "kappa_g@2")) = gen ^ 19) :
    σ (.n (val% «verify_tables» "coord_val@1")) = indexMle (point.take lm) ∧ σ (.n (val% «verify_tables» "coord_vals[302]")) = σ (.n (val% «verify_tables» "coord_val@1")) ∧
      σ (.n (val% «verify_tables» "coord_val@2")) = indexMle (point.take 19) ∧ σ (.n (val% «verify_tables» "coord_vals[307]")) = σ (.n (val% «verify_tables» "coord_val@2")) ∧
      σ (.n (val% «verify_tables» "coord_val@3")) = σ (.n (val% «verify_tables» "x@1")) ∧ σ (.n (val% «verify_tables» "coord_val@4")) = σ (.n (val% «verify_tables» "x@2")) ∧
      LoadHolds rd (σ (.n (val% «verify_tables» "claim_pool"))) 0 (σ (.n (val% «verify_tables» "x@1"))) ∧ LoadHolds rd (σ (.n (val% «verify_tables» "claim_pool"))) 1 (σ (.n (val% «verify_tables» "x@2"))) ∧
      LoadHolds rd (σ (.n (val% «verify_tables» "claim_pool"))) 2 (σ (.n (val% «verify_tables» "x@3"))) ∧ LoadHolds rd (σ (.n (val% «verify_tables» "claim_pool"))) 3 (σ (.n (val% «verify_tables» "x@4"))) := by
  have d1 := h.dispatchAt 839 (.n (val% «verify_tables» "kb[1]")) vtImNames [.n (val% «verify_tables» "zeta")] [.n (val% «verify_tables» "coord_val@1")] (by decide +kernel)
  have d2 := h.dispatchAt 869 (.n (val% «verify_tables» "kappa_g@2")) vtImNames [.n (val% «verify_tables» "zeta")] [.n (val% «verify_tables» "coord_val@2")] (by decide +kernel)
  have s1 := h.atomAt 841 (.load (.n (val% «verify_tables» "coord_val@1")) (.n (val% «verify_tables» "block_index_mle")) 1) (by decide +kernel)
  have s2 := h.atomAt 871 (.load (.n (val% «verify_tables» "coord_val@2")) (.n (val% «verify_tables» "block_index_mle")) 2) (by decide +kernel)
  have r1 := h.atomAt 1201 (.load (.n (val% «verify_tables» "coord_vals[302]")) (.n (val% «verify_tables» "block_index_mle")) 1) (by decide +kernel)
  have r2 := h.atomAt 1216 (.load (.n (val% «verify_tables» "coord_vals[307]")) (.n (val% «verify_tables» "block_index_mle")) 2) (by decide +kernel)
  have p0 := h.atomAt 846 (.load (.n (val% «verify_tables» "x@1")) (.n (val% «verify_tables» "claim_pool")) 0) (by decide +kernel)
  have p1 := h.atomAt 851 (.load (.n (val% «verify_tables» "x@2")) (.n (val% «verify_tables» "claim_pool")) 1) (by decide +kernel)
  have p2 := h.atomAt 1205 (.load (.n (val% «verify_tables» "x@3")) (.n (val% «verify_tables» "claim_pool")) 2) (by decide +kernel)
  have p3 := h.atomAt 1220 (.load (.n (val% «verify_tables» "x@4")) (.n (val% «verify_tables» "claim_pool")) 3) (by decide +kernel)
  have q0 := h.atomAt 1207 (.load (.n (val% «verify_tables» "coord_val@3")) (.n (val% «verify_tables» "claim_pool")) 0) (by decide +kernel)
  have q1 := h.atomAt 1209 (.load (.n (val% «verify_tables» "coord_val@4")) (.n (val% «verify_tables» "claim_pool")) 1) (by decide +kernel)
  simp only [Atom.Holds] at s1 s2 r1 r2 p0 p1 p2 p3 q0 q1
  exact ⟨vt_index_arm hz hlm hlm34 hk1 d1, loadHolds_unique r1 s1,
    vt_index_arm hz h19 (by norm_num) hk2 d2, loadHolds_unique r2 s2,
    loadHolds_unique q0 p0, loadHolds_unique q1 p1, p0, p1, p2, p3⟩

end
end LeanVM.Guest.B1.Tables
