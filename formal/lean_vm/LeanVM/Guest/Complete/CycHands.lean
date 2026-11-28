/-
  LeanVM.Guest.Complete.CycHands

  The cycle hand facts of the hand functions whose virtual values their own paths fix (`Budget/HandVals.lean`).
-/

module

public import LeanVM.Guest.Complete.Cycles
public import LeanVM.Guest.Budget.HandVals
import LeanVM.Guest.CoreRef

/-!
# The cycle hand facts from the virtual values

`handFact_ch_of`: a hand function's cycle hand fact (`HandFact` at `chCertAt`, `chHandAt`, `chOut`) is, at opcode
`op`, its inner preconditions and its inner bound's coordinate within its outer certificate's, both read off the
generated data at its index. Then each function's fact is its `HandVals` lemma and linear arithmetic, opcode by
opcode.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Budget
open LeanVM.Guest.B1
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- **A hand function's cycle hand fact from its coordinates**: at its index `j` (not `main`'s, `da_verify`'s or the
loop's), its hand `hv` and outer certificate `.stat [] b []`, the inner preconditions and the inner bound's coordinate
within the outer one's. -/
theorem handFact_ch_of (op : Opcode) (C₁ C₂ : ℕ) {f : String} {j : ℕ} {hv : HandV} {b : AffV} {σ : Val}
    (hj : coreIdx f = j) (hm : j ≠ Data.chidxMain) (hd : j ≠ Data.chidxDa) (hl : f ≠ "__loop4_main")
    (hh : Data.chhandJ j = some hv) (hc : Data.chcertJ j = .stat [] b [])
    (hfact : ∀ fn, coreProgram.find? f = some fn → ArgsPre hv.pre (fn.params.map σ ++ hv.vps.map σ) ∧
      (hv.b.proj (B2C.opIdx op)).eval (fn.params.map σ ++ hv.vps.map σ) ≤
        (b.proj (B2C.opIdx op)).eval (fn.params.map σ)) :
    HandFact coreProgram (chCertAt op C₁ C₂) (chHandAt op C₁ C₂) (chOut op) f σ := by
  refine ⟨not_chOut op hl, fun h hH fn hfn => ?_⟩
  have hjl : j ≠ Data.chidxLoop := fun e => hl (coreIdx_eq_loop (hj.trans e))
  unfold chHandAt handAt handP at hH
  rw [hj, ite_eq_right hm, hh, Option.map_some, Option.some.injEq] at hH
  subst hH
  refine ⟨σ, SameOnPath.refl, ?_⟩
  unfold chCertAt certAt certP
  rw [hj, ite_eq_right hd, ite_eq_right hjl, hc]
  intro _
  have := hfact fn hfn
  simpa [HandV.proj, CertV.proj, List.map_append] using this

/-- The exponent of a power of `g`, read as an argument. -/
theorem argExp_gpow {vs : List E} {k e : ℕ} {w : E} (hk : vs.getD k 0 = w) (h : GPow w e) : argExp vs k = e := by
  unfold argExp; rw [hk]; exact h.logG

/-- A power of `g` meets a precondition `(k, 2^64)`. -/
theorem argsPre_gT {vs : List E} {k e : ℕ} (hk : vs.getD k 0 = gen ^ e) (he : e < 2 ^ 64 - 1) :
    ArgsPre [(k, 18446744073709551616)] vs := by
  intro q hq
  simp only [List.mem_singleton] at hq
  subst hq
  refine ⟨e, by simp [preLt, gT], he, ?_⟩
  rw [hk]; exact LeanVM.Guest.Value.gen_pow_eq_ofK e

/-! ## `squeeze_packed` -/

theorem chhand_squeeze : Data.chhandJ (idx% «squeeze_packed») = some ⟨[.n 40], [(7, 18446744073709551616)],
    ⟨[7, 31, 15, 58, 4, 3], [(7, [1, 10, 8, 47, 2, 4])]⟩, [(.n 50, 0), (.n 52, 0), (.n 51, 1048577)]⟩ := by
  rfl

theorem chcert_squeeze : Data.chcertJ (idx% «squeeze_packed») = .stat [] ⟨[7, 31, 15, 58, 4, 3], [(6, [1, 3, 2, 12, 1, 1])]⟩ [] := by
  rfl

/-- **`squeeze_packed`'s cycle hand fact**, from its path. -/
theorem handFact_ch_squeeze (op : Opcode) (C₁ C₂ : ℕ) {rd : Reader} {σ : Val}
    (h : PathHolds coreProgram rd "squeeze_packed" σ) :
    HandFact coreProgram (chCertAt op C₁ C₂) (chHandAt op C₁ C₂) (chOut op) "squeeze_packed" σ := by
  obtain ⟨q, r, hq, hr, h40, h6⟩ := squeeze_packed_vals h
  refine handFact_ch_of op C₁ C₂ (coreIdx_of_name (j := idx% «squeeze_packed») rfl) (by decide) (by decide)
    (by decide) chhand_squeeze chcert_squeeze fun fn hfn => ?_
  have e := Option.some.inj (hfn.symm.trans (coreProgram_find?_at (j := idx% «squeeze_packed») rfl))
  subst e
  have hp : (fn% «squeeze_packed»).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] := rfl
  rw [hp]
  dsimp only
  set ps : List E := [V.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6].map σ with hps
  set vs : List E := ps ++ [V.n 40].map σ with hvs
  have a7 : argExp vs 7 = q := argExp_gpow rfl h40
  have a6 : argExp ps 6 = 4 * q + r := argExp_gpow rfl h6
  refine ⟨argsPre_gT (vs := vs) (k := 7) (e := q) h40.1 h40.2, ?_⟩
  cases op <;> simp only [AffV.proj, Aff.eval, B2C.opIdx, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.getD_cons_zero, List.getD_cons_succ, a7, a6] <;> omega

/-! ## `rs_eq_run` -/

theorem chhand_rs_eq_run : Data.chhandJ (idx% «rs_eq_run») = some ⟨[.n 37], [(4, 18446744073709551616)],
    ⟨[455, 924, 9, 285, 4, 0], [(4, [513, 1028, 7, 156, 4, 0])]⟩, [(.n 115, 0), (.n 117, 0), (.n 116, 1048577)]⟩ := by
  rfl

theorem chcert_rs_eq_run : Data.chcertJ (idx% «rs_eq_run») = .stat [] ⟨[455, 924, 9, 285, 4, 0], [(2, [65, 129, 1, 20, 1, 0])]⟩ [] := by
  rfl

/-- **`rs_eq_run`'s cycle hand fact**, from its path. -/
theorem handFact_ch_rs_eq_run (op : Opcode) (C₁ C₂ : ℕ) {rd : Reader} {σ : Val}
    (h : PathHolds coreProgram rd "rs_eq_run" σ) :
    HandFact coreProgram (chCertAt op C₁ C₂) (chHandAt op C₁ C₂) (chOut op) "rs_eq_run" σ := by
  obtain ⟨q, r, hq, hr, hv, hc⟩ := rs_eq_run_vals h
  refine handFact_ch_of op C₁ C₂ (coreIdx_of_name (j := idx% «rs_eq_run») rfl) (by decide) (by decide)
    (by decide) chhand_rs_eq_run chcert_rs_eq_run fun fn hfn => ?_
  have e := Option.some.inj (hfn.symm.trans (coreProgram_find?_at (j := idx% «rs_eq_run») rfl))
  subst e
  have hp : (fn% «rs_eq_run»).params = [.n 0, .n 1, .n 2, .n 3] := rfl
  rw [hp]
  dsimp only
  set ps : List E := [V.n 0, .n 1, .n 2, .n 3].map σ with hps
  set vs : List E := ps ++ [V.n 37].map σ with hvs
  have av : argExp vs 4 = q := argExp_gpow rfl hv
  have ac : argExp ps 2 = 8 * q + r := argExp_gpow rfl hc
  refine ⟨argsPre_gT (vs := vs) (k := 4) (e := q) hv.1 hv.2, ?_⟩
  cases op <;> simp only [AffV.proj, Aff.eval, B2C.opIdx, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.getD_cons_zero, List.getD_cons_succ, av, ac] <;> omega

/-! ## `ring_rows` -/

theorem chhand_ring_rows : Data.chhandJ (idx% «ring_rows») = some ⟨[.n 102], [(5, 18446744073709551616)],
    ⟨[455, 919, 8, 669, 4, 0], [(5, [513, 1030, 7, 604, 4, 0])]⟩, [(.n 107, 0), (.n 109, 0), (.n 108, 1048577)]⟩ := by
  rfl

theorem chcert_ring_rows : Data.chcertJ (idx% «ring_rows») = .stat [] ⟨[455, 919, 8, 669, 4, 0], [(4, [65, 129, 1, 76, 1, 0])]⟩ [] := by
  rfl

/-- **`ring_rows`'s cycle hand fact**, from its path. -/
theorem handFact_ch_ring_rows (op : Opcode) (C₁ C₂ : ℕ) {rd : Reader} {σ : Val}
    (h : PathHolds coreProgram rd "ring_rows" σ) :
    HandFact coreProgram (chCertAt op C₁ C₂) (chHandAt op C₁ C₂) (chOut op) "ring_rows" σ := by
  obtain ⟨q, r, hq, hr, hv, hc⟩ := ring_rows_vals h
  refine handFact_ch_of op C₁ C₂ (coreIdx_of_name (j := idx% «ring_rows») rfl) (by decide) (by decide)
    (by decide) chhand_ring_rows chcert_ring_rows fun fn hfn => ?_
  have e := Option.some.inj (hfn.symm.trans (coreProgram_find?_at (j := idx% «ring_rows») rfl))
  subst e
  have hp : (fn% «ring_rows»).params = [.n 0, .n 1, .n 2, .n 3, .n 4] := rfl
  rw [hp]
  dsimp only
  set ps : List E := [V.n 0, .n 1, .n 2, .n 3, .n 4].map σ with hps
  set vs : List E := ps ++ [V.n 102].map σ with hvs
  have av : argExp vs 5 = q := argExp_gpow rfl hv
  have ac : argExp ps 4 = 8 * q + r := argExp_gpow rfl hc
  refine ⟨argsPre_gT (vs := vs) (k := 5) (e := q) hv.1 hv.2, ?_⟩
  cases op <;> simp only [AffV.proj, Aff.eval, B2C.opIdx, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.getD_cons_zero, List.getD_cons_succ, av, ac] <;> omega

/-! ## `link_rounds__L1_L0` -/

theorem chhand_link_L1_L0 : Data.chhandJ (idx% «link_rounds__L1_L0») = some ⟨[.n 43], [(10, 18446744073709551616)],
    ⟨[16, 40, 23, 53, 4, 3], [(10, [13, 21, 18, 32, 2, 4])]⟩, [(.n 54, 0), (.n 56, 0), (.n 55, 1048577)]⟩ := by
  rfl

theorem chcert_link_L1_L0 : Data.chcertJ (idx% «link_rounds__L1_L0») = .stat [] ⟨[16, 40, 23, 53, 4, 3], [(8, [4, 6, 5, 8, 1, 1])]⟩ [] := by
  rfl

set_option maxRecDepth 100000 in
/-- **`link_rounds__L1_L0`'s cycle hand fact**, from its path. -/
theorem handFact_ch_link_L1_L0 (op : Opcode) (C₁ C₂ : ℕ) {rd : Reader} {σ : Val}
    (h : PathHolds coreProgram rd "link_rounds__L1_L0" σ) :
    HandFact coreProgram (chCertAt op C₁ C₂) (chHandAt op C₁ C₂) (chOut op) "link_rounds__L1_L0" σ := by
  obtain ⟨q, r, hq, hr, hv, hc⟩ := link_rounds_vals (Or.inl rfl) h
  refine handFact_ch_of op C₁ C₂ (coreIdx_of_name (j := idx% «link_rounds__L1_L0») rfl) (by decide) (by decide)
    (by decide) chhand_link_L1_L0 chcert_link_L1_L0 fun fn hfn => ?_
  have e := Option.some.inj (hfn.symm.trans (coreProgram_find?_at (j := idx% «link_rounds__L1_L0») rfl))
  subst e
  have hp : (fn% «link_rounds__L1_L0»).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] := rfl
  rw [hp]
  dsimp only
  set ps : List E := [V.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9].map σ with hps
  set vs : List E := ps ++ [V.n 43].map σ with hvs
  have av : argExp vs 10 = q := argExp_gpow rfl hv
  have ac : argExp ps 8 = 4 * q + r := argExp_gpow rfl hc
  refine ⟨argsPre_gT (vs := vs) (k := 10) (e := q) hv.1 hv.2, ?_⟩
  cases op <;> simp only [AffV.proj, Aff.eval, B2C.opIdx, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.getD_cons_zero, List.getD_cons_succ, av, ac] <;> omega

/-! ## `link_rounds__L7_L0` -/

theorem chhand_link_L7_L0 : Data.chhandJ (idx% «link_rounds__L7_L0») = some ⟨[.n 43], [(10, 18446744073709551616)],
    ⟨[52, 58, 36, 71, 4, 6], [(10, [61, 45, 37, 56, 2, 8])]⟩, [(.n 54, 0), (.n 56, 0), (.n 55, 1048577)]⟩ := by
  rfl

theorem chcert_link_L7_L0 : Data.chcertJ (idx% «link_rounds__L7_L0») = .stat [] ⟨[52, 58, 36, 71, 4, 6], [(8, [16, 12, 10, 14, 1, 2])]⟩ [] := by
  rfl

set_option maxRecDepth 100000 in
/-- **`link_rounds__L7_L0`'s cycle hand fact**, from its path. -/
theorem handFact_ch_link_L7_L0 (op : Opcode) (C₁ C₂ : ℕ) {rd : Reader} {σ : Val}
    (h : PathHolds coreProgram rd "link_rounds__L7_L0" σ) :
    HandFact coreProgram (chCertAt op C₁ C₂) (chHandAt op C₁ C₂) (chOut op) "link_rounds__L7_L0" σ := by
  obtain ⟨q, r, hq, hr, hv, hc⟩ := link_rounds_vals (Or.inr (Or.inr (Or.inl rfl))) h
  refine handFact_ch_of op C₁ C₂ (coreIdx_of_name (j := idx% «link_rounds__L7_L0») rfl) (by decide) (by decide)
    (by decide) chhand_link_L7_L0 chcert_link_L7_L0 fun fn hfn => ?_
  have e := Option.some.inj (hfn.symm.trans (coreProgram_find?_at (j := idx% «link_rounds__L7_L0») rfl))
  subst e
  have hp : (fn% «link_rounds__L7_L0»).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] := rfl
  rw [hp]
  dsimp only
  set ps : List E := [V.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9].map σ with hps
  set vs : List E := ps ++ [V.n 43].map σ with hvs
  have av : argExp vs 10 = q := argExp_gpow rfl hv
  have ac : argExp ps 8 = 4 * q + r := argExp_gpow rfl hc
  refine ⟨argsPre_gT (vs := vs) (k := 10) (e := q) hv.1 hv.2, ?_⟩
  cases op <;> simp only [AffV.proj, Aff.eval, B2C.opIdx, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.getD_cons_zero, List.getD_cons_succ, av, ac] <;> omega

/-! ## `link_rounds__L6_L0` -/

theorem chhand_link_L6_L0 : Data.chhandJ (idx% «link_rounds__L6_L0») = some ⟨[.n 43], [(10, 18446744073709551616)],
    ⟨[46, 55, 39, 68, 4, 6], [(10, [53, 41, 41, 52, 2, 8])]⟩, [(.n 54, 0), (.n 56, 0), (.n 55, 1048577)]⟩ := by
  rfl

theorem chcert_link_L6_L0 : Data.chcertJ (idx% «link_rounds__L6_L0») = .stat [] ⟨[46, 55, 39, 68, 4, 6], [(8, [14, 11, 11, 13, 1, 2])]⟩ [] := by
  rfl

set_option maxRecDepth 100000 in
/-- **`link_rounds__L6_L0`'s cycle hand fact**, from its path. -/
theorem handFact_ch_link_L6_L0 (op : Opcode) (C₁ C₂ : ℕ) {rd : Reader} {σ : Val}
    (h : PathHolds coreProgram rd "link_rounds__L6_L0" σ) :
    HandFact coreProgram (chCertAt op C₁ C₂) (chHandAt op C₁ C₂) (chOut op) "link_rounds__L6_L0" σ := by
  obtain ⟨q, r, hq, hr, hv, hc⟩ := link_rounds_vals (Or.inr (Or.inl rfl)) h
  refine handFact_ch_of op C₁ C₂ (coreIdx_of_name (j := idx% «link_rounds__L6_L0») rfl) (by decide) (by decide)
    (by decide) chhand_link_L6_L0 chcert_link_L6_L0 fun fn hfn => ?_
  have e := Option.some.inj (hfn.symm.trans (coreProgram_find?_at (j := idx% «link_rounds__L6_L0») rfl))
  subst e
  have hp : (fn% «link_rounds__L6_L0»).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] := rfl
  rw [hp]
  dsimp only
  set ps : List E := [V.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9].map σ with hps
  set vs : List E := ps ++ [V.n 43].map σ with hvs
  have av : argExp vs 10 = q := argExp_gpow rfl hv
  have ac : argExp ps 8 = 4 * q + r := argExp_gpow rfl hc
  refine ⟨argsPre_gT (vs := vs) (k := 10) (e := q) hv.1 hv.2, ?_⟩
  cases op <;> simp only [AffV.proj, Aff.eval, B2C.opIdx, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.getD_cons_zero, List.getD_cons_succ, av, ac] <;> omega

/-! ## `link_rounds__L8_L1` -/

theorem chhand_link_L8_L1 : Data.chhandJ (idx% «link_rounds__L8_L1») = some ⟨[.n 43], [(10, 18446744073709551616)],
    ⟨[76, 144, 52, 131, 7, 9], [(10, [93, 160, 54, 136, 6, 12])]⟩, [(.n 54, 0), (.n 56, 0), (.n 55, 1048577)]⟩ := by
  rfl

theorem chcert_link_L8_L1 : Data.chcertJ (idx% «link_rounds__L8_L1») = .stat [] ⟨[76, 144, 52, 131, 7, 9], [(8, [24, 40, 14, 34, 2, 3])]⟩ [] := by
  rfl

set_option maxRecDepth 100000 in
/-- **`link_rounds__L8_L1`'s cycle hand fact**, from its path. -/
theorem handFact_ch_link_L8_L1 (op : Opcode) (C₁ C₂ : ℕ) {rd : Reader} {σ : Val}
    (h : PathHolds coreProgram rd "link_rounds__L8_L1" σ) :
    HandFact coreProgram (chCertAt op C₁ C₂) (chHandAt op C₁ C₂) (chOut op) "link_rounds__L8_L1" σ := by
  obtain ⟨q, r, hq, hr, hv, hc⟩ := link_rounds_vals (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h
  refine handFact_ch_of op C₁ C₂ (coreIdx_of_name (j := idx% «link_rounds__L8_L1») rfl) (by decide) (by decide)
    (by decide) chhand_link_L8_L1 chcert_link_L8_L1 fun fn hfn => ?_
  have e := Option.some.inj (hfn.symm.trans (coreProgram_find?_at (j := idx% «link_rounds__L8_L1») rfl))
  subst e
  have hp : (fn% «link_rounds__L8_L1»).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] := rfl
  rw [hp]
  dsimp only
  set ps : List E := [V.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9].map σ with hps
  set vs : List E := ps ++ [V.n 43].map σ with hvs
  have av : argExp vs 10 = q := argExp_gpow rfl hv
  have ac : argExp ps 8 = 4 * q + r := argExp_gpow rfl hc
  refine ⟨argsPre_gT (vs := vs) (k := 10) (e := q) hv.1 hv.2, ?_⟩
  cases op <;> simp only [AffV.proj, Aff.eval, B2C.opIdx, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.getD_cons_zero, List.getD_cons_succ, av, ac] <;> omega

/-! ## `link_rounds__L9_L1` -/

theorem chhand_link_L9_L1 : Data.chhandJ (idx% «link_rounds__L9_L1») = some ⟨[.n 43], [(10, 18446744073709551616)],
    ⟨[82, 150, 56, 134, 7, 9], [(10, [101, 168, 61, 140, 6, 12])]⟩, [(.n 54, 0), (.n 56, 0), (.n 55, 1048577)]⟩ := by
  rfl

theorem chcert_link_L9_L1 : Data.chcertJ (idx% «link_rounds__L9_L1») = .stat [] ⟨[82, 150, 56, 134, 7, 9], [(8, [26, 42, 16, 35, 2, 3])]⟩ [] := by
  rfl

set_option maxRecDepth 100000 in
/-- **`link_rounds__L9_L1`'s cycle hand fact**, from its path. -/
theorem handFact_ch_link_L9_L1 (op : Opcode) (C₁ C₂ : ℕ) {rd : Reader} {σ : Val}
    (h : PathHolds coreProgram rd "link_rounds__L9_L1" σ) :
    HandFact coreProgram (chCertAt op C₁ C₂) (chHandAt op C₁ C₂) (chOut op) "link_rounds__L9_L1" σ := by
  obtain ⟨q, r, hq, hr, hv, hc⟩ := link_rounds_vals (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) h
  refine handFact_ch_of op C₁ C₂ (coreIdx_of_name (j := idx% «link_rounds__L9_L1») rfl) (by decide) (by decide)
    (by decide) chhand_link_L9_L1 chcert_link_L9_L1 fun fn hfn => ?_
  have e := Option.some.inj (hfn.symm.trans (coreProgram_find?_at (j := idx% «link_rounds__L9_L1») rfl))
  subst e
  have hp : (fn% «link_rounds__L9_L1»).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] := rfl
  rw [hp]
  dsimp only
  set ps : List E := [V.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9].map σ with hps
  set vs : List E := ps ++ [V.n 43].map σ with hvs
  have av : argExp vs 10 = q := argExp_gpow rfl hv
  have ac : argExp ps 8 = 4 * q + r := argExp_gpow rfl hc
  refine ⟨argsPre_gT (vs := vs) (k := 10) (e := q) hv.1 hv.2, ?_⟩
  cases op <;> simp only [AffV.proj, Aff.eval, B2C.opIdx, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.getD_cons_zero, List.getD_cons_succ, av, ac] <;> omega

/-! ## `link_rounds__L10_L1` -/

theorem chhand_link_L10_L1 : Data.chhandJ (idx% «link_rounds__L10_L1») = some ⟨[.n 43], [(10, 18446744073709551616)],
    ⟨[88, 156, 54, 137, 7, 9], [(10, [109, 176, 58, 144, 6, 12])]⟩, [(.n 54, 0), (.n 56, 0), (.n 55, 1048577)]⟩ := by
  rfl

theorem chcert_link_L10_L1 : Data.chcertJ (idx% «link_rounds__L10_L1») = .stat [] ⟨[88, 156, 54, 137, 7, 9], [(8, [28, 44, 15, 36, 2, 3])]⟩ [] := by
  rfl

set_option maxRecDepth 100000 in
/-- **`link_rounds__L10_L1`'s cycle hand fact**, from its path. -/
theorem handFact_ch_link_L10_L1 (op : Opcode) (C₁ C₂ : ℕ) {rd : Reader} {σ : Val}
    (h : PathHolds coreProgram rd "link_rounds__L10_L1" σ) :
    HandFact coreProgram (chCertAt op C₁ C₂) (chHandAt op C₁ C₂) (chOut op) "link_rounds__L10_L1" σ := by
  obtain ⟨q, r, hq, hr, hv, hc⟩ := link_rounds_vals (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) h
  refine handFact_ch_of op C₁ C₂ (coreIdx_of_name (j := idx% «link_rounds__L10_L1») rfl) (by decide) (by decide)
    (by decide) chhand_link_L10_L1 chcert_link_L10_L1 fun fn hfn => ?_
  have e := Option.some.inj (hfn.symm.trans (coreProgram_find?_at (j := idx% «link_rounds__L10_L1») rfl))
  subst e
  have hp : (fn% «link_rounds__L10_L1»).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] := rfl
  rw [hp]
  dsimp only
  set ps : List E := [V.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9].map σ with hps
  set vs : List E := ps ++ [V.n 43].map σ with hvs
  have av : argExp vs 10 = q := argExp_gpow rfl hv
  have ac : argExp ps 8 = 4 * q + r := argExp_gpow rfl hc
  refine ⟨argsPre_gT (vs := vs) (k := 10) (e := q) hv.1 hv.2, ?_⟩
  cases op <;> simp only [AffV.proj, Aff.eval, B2C.opIdx, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.getD_cons_zero, List.getD_cons_succ, av, ac] <;> omega

end
end LeanVM.Guest.Complete
