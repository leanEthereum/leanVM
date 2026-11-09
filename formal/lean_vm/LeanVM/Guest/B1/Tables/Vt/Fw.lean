/-
  LeanVM.Guest.B1.Tables.Vt.Fw

  `verify_tables`' framework claims: the memory and bytecode index extensions, the five column
  values stored in the claim pool with their `g^|point|`, and the pull side's reloads of them.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Fresh
public import LeanVM.Guest.B1.Selectors.IndexMle

/-!
# The framework's claims (G:2269-2303)

`vt_fw`: `index_mle` at `kb[1] = g^log_mem` and at `kb[0]·g^19` (the bytecode's log-size) give the index extensions
of the point's prefixes; the memory's three values, the final memory count and the final bytecode
count are `claim_pool[0 .. 4]`; the
pull side reloads the index values and the memory values from where the push side left them.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem vt_index_arm {rd : Reader} {σ : Val} {v r : ℕ} {point : List E} {κ : ℕ}
    (hz : TbReadsAt rd (σ (.n 8)) point) (hκ : κ ≤ point.length) (hκ34 : κ < 34)
    (hv : σ (.n v) = gen ^ κ)
    (hd : ∃ (j : ℕ) (h : j < vtImNames.length), σ (.n v) = ofK (Parameters.addressOfIndex j) ∧
      coreProgram.Rel rd vtImNames[j] ([V.n 8].map σ) ([V.n r].map σ)) :
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
    (hz : TbReadsAt rd (σ (.n 8)) point) {lm : ℕ} (hlm : lm ≤ point.length) (hlm34 : lm < 34)
    (h19 : 19 ≤ point.length) (hk1 : σ (.n 29) = gen ^ lm) (hk2 : σ (.n 876) = gen ^ 19) :
    σ (.n 824) = indexMle (point.take lm) ∧ σ (.n 1839) = σ (.n 824) ∧
      σ (.n 894) = indexMle (point.take 19) ∧ σ (.n 1881) = σ (.n 894) ∧
      σ (.n 1856) = σ (.n 830) ∧ σ (.n 1860) = σ (.n 843) ∧ σ (.n 1864) = σ (.n 856) ∧
      LoadHolds rd (σ (.n 15)) 0 (σ (.n 830)) ∧ LoadHolds rd (σ (.n 15)) 1 (σ (.n 843)) ∧
      LoadHolds rd (σ (.n 15)) 2 (σ (.n 856)) ∧ LoadHolds rd (σ (.n 15)) 3 (σ (.n 1843)) ∧
      LoadHolds rd (σ (.n 15)) 4 (σ (.n 1898)) := by
  have d1 := h.dispatchAt 810 (.n 29) vtImNames [.n 8] [.n 824] (by decide +kernel)
  have d2 := h.dispatchAt 880 (.n 876) vtImNames [.n 8] [.n 894] (by decide +kernel)
  have s1 := h.atomAt 811 (.load (.n 824) (.n 781) 1) (by decide +kernel)
  have s2 := h.atomAt 881 (.load (.n 894) (.n 781) 2) (by decide +kernel)
  have r1 := h.atomAt 1877 (.load (.n 1839) (.n 781) 1) (by decide +kernel)
  have r2 := h.atomAt 1919 (.load (.n 1881) (.n 781) 2) (by decide +kernel)
  have p0 := h.atomAt 826 (.load (.n 830) (.n 15) 0) (by decide +kernel)
  have p1 := h.atomAt 839 (.load (.n 843) (.n 15) 1) (by decide +kernel)
  have p2 := h.atomAt 852 (.load (.n 856) (.n 15) 2) (by decide +kernel)
  have p3 := h.atomAt 1890 (.load (.n 1843) (.n 15) 3) (by decide +kernel)
  have p4 := h.atomAt 1933 (.load (.n 1898) (.n 15) 4) (by decide +kernel)
  have q0 := h.atomAt 1894 (.load (.n 1856) (.n 15) 0) (by decide +kernel)
  have q1 := h.atomAt 1898 (.load (.n 1860) (.n 15) 1) (by decide +kernel)
  have q2 := h.atomAt 1902 (.load (.n 1864) (.n 15) 2) (by decide +kernel)
  simp only [Atom.Holds] at s1 s2 r1 r2 p0 p1 p2 p3 p4 q0 q1 q2
  exact ⟨vt_index_arm hz hlm hlm34 hk1 d1, tb_loadHolds_unique r1 s1,
    vt_index_arm hz h19 (by norm_num) hk2 d2, tb_loadHolds_unique r2 s2,
    tb_loadHolds_unique q0 p0, tb_loadHolds_unique q1 p1, tb_loadHolds_unique q2 p2,
    p0, p1, p2, p3, p4⟩

end
end LeanVM.Guest.B1.Tables
