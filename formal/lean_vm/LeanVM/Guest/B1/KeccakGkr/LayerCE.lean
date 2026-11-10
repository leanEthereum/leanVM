/-
  LeanVM.Guest.B1.KeccakGkr.LayerCE

  `keccak_layer`'s `t`, lane weights and weight sections, completely.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCC
public import LeanVM.Guest.B1.KeccakGkr.LayerProof

/-!
# `t`, the lane weights and the claim's weights, completely

* `ldIn ps`: a load through one of the pointers `ps` below its bound; `side_ldIn`: with each
  pointer's words in memory and the load not a store, its side condition.
* `tReads_complete`: `t`'s three words read from memory.
* `eqf_complete`: the local point's lane weights, its five last coordinates read back.
* `weight_complete`: the weight section, the claim's lanes (and for a later claim its local
  point) and the local point read.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

/-- A load through one of the pointers `ps` below its bound. -/
def ldIn (ps : List (V × ℕ)) : Atom → Bool
  | .load _ p off => ps.any fun q ↦ q.1 == p && decide (off < q.2)
  | _ => false

theorem side_ldIn {ps : List (V × ℕ)}
    (hW : ∀ q ∈ ps, ∃ W : List E, ReadsAt rd (σ q.1) W ∧ q.2 ≤ W.length) {a : Atom}
    (ha : ldIn ps a = true) (hS : a ∉ S) : Side rd S σ a := by
  cases a with
  | load d p off =>
    simp only [ldIn, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ha
    obtain ⟨q, hq, rfl, hoff⟩ := ha
    obtain ⟨W, hr, hl⟩ := hW q hq
    exact side_loadVia hS hr (by omega)
  | _ => simp [ldIn] at ha

/-- The residual atoms of a block are loads through `ps`, none a store: they have their side
conditions. -/
theorem resid_ldIn {B : List Stmt} {ps : List (V × ℕ)}
    (hk : (resid (atomsL B)).all (ldIn ps) = true) (hS : ∀ a ∈ resid (atomsL B), a ∉ S)
    (hW : ∀ q ∈ ps, ∃ W : List E, ReadsAt rd (σ q.1) W ∧ q.2 ≤ W.length) :
    ∀ a ∈ resid (atomsL B), a.Holds rd σ ∨ Side rd S σ a :=
  fun a ha ↦ Or.inr (side_ldIn hW (List.all_eq_true.mp hk a ha) (hS a ha))

/-! ## `t` -/

/-- **`t`, completely.** -/
theorem tReads_complete {o : ℕ} (hg : ∀ s ∈ tReadsT o, GoodS rd S w σ s)
    (hS : ∀ d' off, Atom.load d' (.n (o + 745)) off ∉ S) {t0 t1 t2 : E}
    (h0 : LoadHolds rd (σ (.n (o + 745))) 33 t0) (h1 : LoadHolds rd (σ (.n (o + 745))) 34 t1)
    (h2 : LoadHolds rd (σ (.n (o + 745))) 35 t2) :
    σ (.n (o + 1112)) = t0 ∧ σ (.n (o + 1115)) = t1 ∧ σ (.n (o + 1118)) = t2 ∧
      ∀ {next : Prop} {kret : List E → Prop}, next → Stmt.HoldsList C rd σ (tReadsT o) next kret := by
  have g0 := fun s hs ↦ hg s (List.mem_append_left _ (List.mem_append_left _ hs))
  have g1 := fun s hs ↦ hg s (List.mem_append_left _ (List.mem_append_right _ hs))
  have g2 := fun s hs ↦ hg s (List.mem_append_right _ hs)
  obtain ⟨e0, -, f0⟩ := fsNext_complete (C := C) g0 (hS _ _) h0
  obtain ⟨e1, -, f1⟩ := fsNext_complete (C := C) g1 (hS _ _) h1
  obtain ⟨e2, -, f2⟩ := fsNext_complete (C := C) g2 (hS _ _) h2
  refine ⟨e0, e1, e2, fun hn ↦ ?_⟩
  rw [tReadsT, holdsList_append, holdsList_append]
  exact f0 (f1 (f2 hn))

/-! ## The lane weights -/

/-- The lane weights' section. -/
def eqfS (o : ℕ) : List Stmt := eqfT (.n (o + 748)) 6 5 25 (o + 1121)

theorem eqf_kernel {o : ℕ} (ho : LayOff o) :
    (eqfS o).all isAtom = true ∧ (resid (atomsL (eqfS o))).all (ldIn [(.n (o + 748), 11)]) = true := by
  rcases ho with rfl | rfl <;> exact ⟨by decide +kernel, by decide +kernel⟩

/-- **The lane weights, completely.** -/
theorem eqf_complete {o : ℕ} (ho : LayOff o) (hσ : ∀ v, σ v = σ (.n v.idx))
    (hg : ∀ s ∈ eqfS o, GoodS rd S w σ s)
    (hS : ∀ a ∈ resid (atomsL (eqfS o)), a ∉ S) {locPt : List E} (hl : locPt.length = 11)
    (hloc : ReadsAt rd (σ (.n (o + 748))) locPt) :
    ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (eqfS o) next kret := by
  obtain ⟨hall, hr⟩ := eqf_kernel ho
  exact block_holds hall hσ hg
    (resid_ldIn hr hS fun q hq ↦ by
      simp only [List.mem_singleton] at hq
      subst hq
      exact ⟨locPt, hloc, by omega⟩)

/-! ## The weights -/

/-- The pointers the weight section loads through. -/
def weightPs (first o : ℕ) : List (V × ℕ) :=
  [(.n 11, 22), (.n (o + 1190), 25), (.n (o + 748), 11)] ++
    if first = 1 then [] else [(.n (o + 1191), 11)]

theorem weight_kernel {first : ℕ} (hf : first < 2) :
    (weightT first (layOff first)).all isAtom = true ∧
      (resid (atomsL (weightT first (layOff first)))).all
        (ldIn (weightPs first (layOff first))) = true := by
  interval_cases first
  all_goals exact ⟨by decide +kernel, by decide +kernel⟩

/-- **The weight section, completely**: the claim's record (`22` words), its lanes at `lp` and,
for a later claim, its local point at `lc`, and the local point at `loc`. -/
theorem weight_complete {first : ℕ} (hf : first < 2)
    (hσ : ∀ v, σ v = σ (.n v.idx)) (hg : ∀ s ∈ weightT first (layOff first), GoodS rd S w σ s)
    (hS : ∀ a ∈ resid (atomsL (weightT first (layOff first))), a ∉ S)
    {cw : List E} (hcw : ReadsAt rd (σ (.n 11)) cw) (hcwl : 22 ≤ cw.length)
    {lanes : List E} (hll : lanes.length = 25) (hlanes : ReadsAt rd (cw.getD 3 0) lanes)
    {locPt : List E} (hl : locPt.length = 11) (hloc : ReadsAt rd (σ (.n (layOff first + 748))) locPt)
    {locC : List E} (hlc : first = 0 → locC.length = 11 ∧ ReadsAt rd (cw.getD 4 0) locC) :
    ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (weightT first (layOff first)) next kret := by
  obtain ⟨hall, hr⟩ := weight_kernel hf
  have hcw3 : LoadHolds rd (σ (.n 11)) 3 (cw.getD 3 0) := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hcw 3 (by omega)
  have hcw4 : LoadHolds rd (σ (.n 11)) 4 (cw.getD 4 0) := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hcw 4 (by omega)
  have g85 : Good rd S w σ (.load (.n (layOff first + 1190)) (.n 11) 3) := by
    have := hg (.atom (.load (.n (layOff first + 1190)) (.n 11) 3)) (by
      unfold weightT; split <;> simp)
    exact this
  have hS85 : Atom.load (.n (layOff first + 1190)) (.n 11) 3 ∉ S := hS _ (by
    interval_cases first <;> decide +kernel)
  have e85 := load_val (w := w) g85 hS85 hcw3
  intro next kret hn
  refine block_holds hall hσ hg (resid_ldIn hr hS fun q hq ↦ ?_) hn
  simp only [weightPs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with (rfl | rfl | rfl) | hq
  · exact ⟨cw, hcw, hcwl⟩
  · exact ⟨lanes, by rw [e85]; exact hlanes, by simp [hll]⟩
  · exact ⟨locPt, hloc, by simp [hl]⟩
  · split at hq
    · simp at hq
    · rename_i hf1
      have hf0 : first = 0 := by omega
      simp only [List.mem_singleton] at hq
      subst hq
      have g86 : Good rd S w σ (.load (.n (layOff first + 1191)) (.n 11) 4) := by
        have := hg (.atom (.load (.n (layOff first + 1191)) (.n 11) 4)) (by
          unfold weightT; simp [hf1])
        exact this
      have hS86 : Atom.load (.n (layOff first + 1191)) (.n 11) 4 ∉ S := hS _ (by
        subst hf0; decide +kernel)
      have e86 := load_val (w := w) g86 hS86 hcw4
      obtain ⟨hlcl, hlcr⟩ := hlc hf0
      exact ⟨locC, by rw [e86]; exact hlcr, by simp [hlcl]⟩

end
end LeanVM.Guest.B1.VerifySub
