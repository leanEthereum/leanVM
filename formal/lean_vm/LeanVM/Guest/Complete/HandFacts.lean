/-
  LeanVM.Guest.Complete.HandFacts

  The hand facts of the functions whose virtual values their own path fixes: `squeeze_packed`,
  `rs_eq_run`, `ring_rows`, and the link's round functions, at the node's constants; a function with no inner check.
-/

module

public import LeanVM.Guest.Complete.HandMain

/-!
# Path-local hand facts

A hand fact (`HandFact`) at a function other than `main`, `da_verify` and the children's loop reads
the generated certificate and inner check of its index (`handFact_of`); their affine bounds are
compared with short forms by the kernel (`affEqB`, `aff_eq`), and the inequality follows from what
the path fixes of the values (`Budget/HandVals.lean`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest.Budget LeanVM.Guest.Value

@[expose] public section

/-! ## Affine bounds by their coefficients -/

theorem aff_eval_eq (b : Aff) (args : List E) (n : ℕ) (hlt : ∀ q ∈ b.cs, q.1 < n) :
    b.eval args = b.c + ∑ i ∈ Finset.range n, coefOf b.cs i * argExp args i := by
  unfold Aff.eval
  rw [sum_coef (argExp args) n _ hlt]

/-- Two affine bounds over arguments `0 ..< n` with the same constant and coefficients. -/
def affEqB (n : ℕ) (b b' : Aff) : Bool :=
  b.c == b'.c && b.cs.all (·.1 < n) && b'.cs.all (·.1 < n) &&
    (List.range n).all fun i => coefOf b.cs i == coefOf b'.cs i

theorem aff_eq {n : ℕ} {b b' : Aff} (h : affEqB n b b' = true) (args : List E) : b.eval args = b'.eval args := by
  simp only [affEqB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  obtain ⟨⟨⟨hc, h1⟩, h2⟩, h3⟩ := h
  rw [aff_eval_eq b args n h1, aff_eval_eq b' args n h2, hc]
  congr 1
  exact Finset.sum_congr rfl fun i hi => by rw [h3 i (Finset.mem_range.mp hi)]

/-! ## A hand fact from the generated data -/

/-- A certificate's preconditions and bound, if a bound. -/
def certStat : Cert → Option (List (ℕ × ℕ) × Aff)
  | .stat p b _ => some (p, b)
  | _ => none

/-- A hand's virtual parameters, preconditions and inner bound. -/
def handTriple (h : Hand) : List V × List (ℕ × ℕ) × Aff := (h.vps, h.pre, h.b)

theorem coreIdx_of_name {j : ℕ} {f : String} (h : (coreProgram[j]?).map Fn.name = some f) : coreIdx f = j := by
  obtain ⟨fn, hfn, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hfn
  exact coreIdx_getElem hj

theorem whabsJ_false (j : ℕ) : Data.whabsJ j = false := by
  have h : ∀ b ∈ Data.whabsL, b = false := by decide +kernel
  unfold Data.whabsJ
  rw [List.getD_eq_getElem?_getD]
  cases hb : Data.whabsL[j]? with
  | none => rfl
  | some b => exact h b (List.mem_of_getElem? hb)

/-- **Only the children's loop is left out of the check.** -/
theorem whOut_not {f : String} (h : coreIdx f ≠ Data.whidxLoop) : ¬ whOut f := by
  unfold whOut
  rintro (h1 | h2)
  · rw [whabsJ_false] at h1; exact Bool.false_ne_true h1
  · have : coreIdx f ≠ 39 := h
    simp [Data.whloopJ, this] at h2

/-- **A hand fact of function `j`** (not `main`, `da_verify` or the loop), its generated bounds compared
with the short forms `bS` (inner) and `bOS` (outer) over `n` arguments, from the inequality at those. -/
theorem handFact_of {f : String} {j n : ℕ} (hn : (coreProgram[j]?).map Fn.name = some f) (hd : j ≠ Data.whidxDa)
    (hl : j ≠ Data.whidxLoop) (hm : j ≠ Data.whidxMain) {preO : List (ℕ × ℕ)} {bO : Aff}
    (hc : certStat (Data.whcertJ j) = some (preO, bO)) {vps : List V} {pre : List (ℕ × ℕ)} {b : Aff}
    (hh : (Data.whhandJ j).map handTriple = some (vps, pre, b)) {bS bOS : Aff} (hb : affEqB n b bS = true)
    (hbO : affEqB n bO bOS = true) {C₁ C₂ : ℕ} {σ σ' : Val} (hsame : SameOnPath coreProgram f σ σ')
    (hfact : ∀ fn, coreProgram.find? f = some fn → ArgsPre preO (fn.params.map σ) →
      ArgsPre pre (fn.params.map σ ++ vps.map σ') ∧
        bS.eval (fn.params.map σ ++ vps.map σ') ≤ bOS.eval (fn.params.map σ)) :
    HandFact coreProgram (whCertAt C₁ C₂) (whHandAt C₁ C₂) whOut f σ := by
  have hj := coreIdx_of_name hn
  refine ⟨whOut_not (by rw [hj]; exact hl), fun h hh' fn hfn => ⟨σ', hsame, ?_⟩⟩
  have e1 : whHandAt C₁ C₂ f = Data.whhandJ j := by simp only [whHandAt, handAt, hj, hm, ↓reduceIte]
  rw [e1] at hh'
  rw [hh'] at hh
  simp only [Option.map_some, handTriple, Option.some.injEq, Prod.mk.injEq] at hh
  obtain ⟨rfl, rfl, rfl⟩ := hh
  have e2 : whCertAt C₁ C₂ f = Data.whcertJ j := by simp only [whCertAt, certAt, hj, hd, hl, ↓reduceIte]
  rw [e2]
  cases hcj : Data.whcertJ j with
  | stat p b' k =>
      rw [hcj] at hc
      simp only [certStat, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      intro hpre
      obtain ⟨h1, h2⟩ := hfact fn hfn hpre
      exact ⟨h1, by rw [aff_eq hb, aff_eq hbO]; exact h2⟩
  | none => rw [hcj] at hc; simp [certStat] at hc
  | loop _ _ _ _ => rw [hcj] at hc; simp [certStat] at hc

/-- **A function with no inner check** (not the loop) has its hand fact. -/
theorem handFact_of_none {f : String} {C₁ C₂ : ℕ} {σ : Val} (hl : coreIdx f ≠ Data.whidxLoop)
    (hh : whHandAt C₁ C₂ f = none) : HandFact coreProgram (whCertAt C₁ C₂) (whHandAt C₁ C₂) whOut f σ :=
  ⟨whOut_not hl, fun h hh' => by rw [hh] at hh'; exact absurd hh' (by simp)⟩

/-- A precondition `g^b` at the one virtual value `k`. -/
theorem argsPre_one {args : List E} {k e : ℕ} (h : GPow (args.getD k 0) e) : ArgsPre [(k, 2 ^ 64)] args :=
  argsPre_of (by simp) fun q hq => by
    rw [List.mem_singleton] at hq; subst hq; exact ⟨e, h⟩

/-! ## The functions -/

variable {rd : Reader} {σ : Val} {C₁ C₂ : ℕ}

theorem squeeze_packed_hand (h : PathHolds coreProgram rd "squeeze_packed" σ) :
    HandFact coreProgram (whCertAt C₁ C₂) (whHandAt C₁ C₂) whOut "squeeze_packed" σ := by
  obtain ⟨q, r, -, -, gq, gc⟩ := squeeze_packed_vals h
  refine handFact_of (j := 11) (n := 8) (bS := ⟨373, [(7, 116)]⟩) (bOS := ⟨373, [(6, 29)]⟩)
    (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide)
    (by decide) rfl rfl (by decide +kernel) (by decide +kernel) SameOnPath.refl ?_
  intro fn hfn _
  rw [coreProgram_find?_at (j := idx% «squeeze_packed») rfl] at hfn
  obtain rfl := Option.some.inj hfn
  have a7 : argExp ((fn% «squeeze_packed»).params.map σ ++ [σ (.n 40)]) 7 = q := gq.logG
  have a6 : argExp ((fn% «squeeze_packed»).params.map σ) 6 = 4 * q + r := gc.logG
  refine ⟨argsPre_one gq, ?_⟩
  simp only [Aff.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, a7, a6]
  omega

theorem rs_eq_run_hand (h : PathHolds coreProgram rd "rs_eq_run" σ) :
    HandFact coreProgram (whCertAt C₁ C₂) (whHandAt C₁ C₂) whOut "rs_eq_run" σ := by
  obtain ⟨q, r, -, -, gq, gc⟩ := rs_eq_run_vals h
  refine handFact_of (j := 6) (n := 5) (bS := ⟨1723, [(4, 1705)]⟩) (bOS := ⟨1723, [(2, 214)]⟩)
    (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide)
    (by decide) rfl rfl (by decide +kernel) (by decide +kernel) SameOnPath.refl ?_
  intro fn hfn _
  rw [coreProgram_find?_at (j := idx% «rs_eq_run») rfl] at hfn
  obtain rfl := Option.some.inj hfn
  have a4 : argExp ((fn% «rs_eq_run»).params.map σ ++ [σ (.n 37)]) 4 = q := gq.logG
  have a2 : argExp ((fn% «rs_eq_run»).params.map σ) 2 = 8 * q + r := gc.logG
  refine ⟨argsPre_one gq, ?_⟩
  simp only [Aff.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, a4, a2]
  omega

theorem ring_rows_hand (h : PathHolds coreProgram rd "ring_rows" σ) :
    HandFact coreProgram (whCertAt C₁ C₂) (whHandAt C₁ C₂) whOut "ring_rows" σ := by
  obtain ⟨q, r, -, -, gq, gc⟩ := ring_rows_vals h
  refine handFact_of (j := 12) (n := 6) (bS := ⟨1595, [(5, 1643)]⟩) (bOS := ⟨1595, [(4, 206)]⟩)
    (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide)
    (by decide) rfl rfl (by decide +kernel) (by decide +kernel) SameOnPath.refl ?_
  intro fn hfn _
  rw [coreProgram_find?_at (j := idx% «ring_rows») rfl] at hfn
  obtain rfl := Option.some.inj hfn
  have a5 : argExp ((fn% «ring_rows»).params.map σ ++ [σ (.n 102)]) 5 = q := gq.logG
  have a4 : argExp ((fn% «ring_rows»).params.map σ) 4 = 8 * q + r := gc.logG
  refine ⟨argsPre_one gq, ?_⟩
  simp only [Aff.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, a5, a4]
  omega

/-- A link round function's hand fact, at its index `j`, constant `c`, inner and outer coefficients
`d`, `d'` with `d ≤ 4 d'`. -/
theorem lr_hand {f : String} (hf : LinkRoundsName f) {j c d d' : ℕ}
    (hn : (coreProgram[j]?).map Fn.name = some f) (hd : j ≠ Data.whidxDa) (hl : j ≠ Data.whidxLoop)
    (hm : j ≠ Data.whidxMain) {preO : List (ℕ × ℕ)} {bO : Aff}
    (hc : certStat (Data.whcertJ j) = some (preO, bO)) {pre : List (ℕ × ℕ)} {b : Aff}
    (hh : (Data.whhandJ j).map handTriple = some ([.n 43], pre, b)) (hpre : pre = [(10, 2 ^ 64)])
    (hb : affEqB 11 b ⟨c, [(10, d)]⟩ = true) (hbO : affEqB 11 bO ⟨c, [(8, d')]⟩ = true) (hdd : d ≤ 4 * d')
    (hps : ∀ fn, coreProgram.find? f = some fn → fn.params = (List.range 10).map V.n)
    (h : PathHolds coreProgram rd f σ) :
    HandFact coreProgram (whCertAt C₁ C₂) (whHandAt C₁ C₂) whOut f σ := by
  obtain ⟨q, r, -, -, gq, gc⟩ := link_rounds_vals hf h
  refine handFact_of hn hd hl hm hc hh hb hbO SameOnPath.refl ?_
  intro fn hfn _
  rw [hps fn hfn]
  have a10 : argExp (((List.range 10).map V.n).map σ ++ [σ (.n 43)]) 10 = q := gq.logG
  have a8 : argExp (((List.range 10).map V.n).map σ) 8 = 4 * q + r := gc.logG
  subst hpre
  refine ⟨argsPre_one (e := q) gq, ?_⟩
  simp only [List.map_cons, List.map_nil, Aff.eval, List.sum_cons, List.sum_nil, a10, a8]
  have h1 : d * q ≤ 4 * (d' * q) := by rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right q hdd
  have h2 : d' * (4 * q + r) = 4 * (d' * q) + d' * r := by ring
  omega

/-- The link's round functions' parameters. -/
theorem lr_params {f : String} {fn0 : Fn} (hf : coreProgram.find? f = some fn0)
    (hp : fn0.params = (List.range 10).map V.n) :
    ∀ fn, coreProgram.find? f = some fn → fn.params = (List.range 10).map V.n := fun fn hfn => by
  rw [hf] at hfn; obtain rfl := Option.some.inj hfn; exact hp

set_option maxRecDepth 100000 in
theorem link_rounds_hand {f : String} (hf : LinkRoundsName f) (h : PathHolds coreProgram rd f σ) :
    HandFact coreProgram (whCertAt C₁ C₂) (whHandAt C₁ C₂) whOut f σ := by
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lr_hand (j := 175) (c := 475) (d := 150) (d' := 38) (Or.inl rfl)
      (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide)
      rfl rfl rfl (by decide +kernel) (by decide +kernel) (by norm_num)
      (lr_params (coreProgram_find?_at (j := idx% «link_rounds__L1_L0») rfl) rfl) h
  · exact lr_hand (j := 543) (c := 910) (d := 310) (d' := 78) (Or.inr (Or.inl rfl))
      (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide)
      rfl rfl rfl (by decide +kernel) (by decide +kernel) (by norm_num)
      (lr_params (coreProgram_find?_at (j := idx% «link_rounds__L6_L0») rfl) rfl) h
  · exact lr_hand (j := 542) (c := 951) (d := 326) (d' := 82) (Or.inr (Or.inr (Or.inl rfl)))
      (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide)
      rfl rfl rfl (by decide +kernel) (by decide +kernel) (by norm_num)
      (lr_params (coreProgram_find?_at (j := idx% «link_rounds__L7_L0») rfl) rfl) h
  · exact lr_hand (j := 544) (c := 1834) (d := 646) (d' := 162) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide)
      rfl rfl rfl (by decide +kernel) (by decide +kernel) (by norm_num)
      (lr_params (coreProgram_find?_at (j := idx% «link_rounds__L8_L1») rfl) rfl) h
  · exact lr_hand (j := 545) (c := 1885) (d := 662) (d' := 166) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide)
      rfl rfl rfl (by decide +kernel) (by decide +kernel) (by norm_num)
      (lr_params (coreProgram_find?_at (j := idx% «link_rounds__L9_L1») rfl) rfl) h
  · exact lr_hand (j := 546) (c := 1930) (d := 678) (d' := 170) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      (Data.nameT_spec (by rw [coreProgram_length]; decide) (by decide +kernel)) (by decide) (by decide) (by decide)
      rfl rfl rfl (by decide +kernel) (by decide +kernel) (by norm_num)
      (lr_params (coreProgram_find?_at (j := idx% «link_rounds__L10_L1») rfl) rfl) h

end
end LeanVM.Guest.Complete
