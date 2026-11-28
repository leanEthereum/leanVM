/-
  LeanVM.Guest.B1.VsC.VsPh6

  `wC`'s windows `7 ..< 9`: the opening's grind, the link's packing check, `squeeze_packed`.
-/

module

public import LeanVM.Guest.B1.VsC.VsPh5

/-!
# `wC`'s windows `7 ..< 9`

`vsC_w7` (statements `488 ..< 574`): the opening message's grind `gcInlineOT 2 581 178 (.n 574) (.n 4)` (`vsC7_eq`, by
the kernel; its atoms by `gcO_atoms`), then the link's packing word `f4` read from the shape's buffer (`.n 9`'s word
`3`), `f4^8 / (g^n·c·g^w·g^chunkCount)` one of `1, 2, …, 128` (the product of its eight sums is `0`), the opening's
first word stored at `.n 10`, and the stream cursor `.n 10·g`. `vsC_w8` (statement `574`): `squeeze_packed`, at a
given end. `vsPh6_wins` from numeric hypotheses.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- Statements `488 ..< 537`: the opening's grind, `grind_check(.n 574, g_squares·g^178, 2)` from `.n 581`. -/
def vsOpG : List Stmt := gcInlineOT 2 581 178 (.n 574) (.n 4)

/-- The packing check's constant. -/
abbrev pkC : E := word 452984832 0

/-- Statements `537 ..< 574`. -/
def vsC7q : List Atom :=
  [.load (.n 645) (.n 9) 3, .mul (.n 646) (.n 645) (.n 645), .mul (.n 647) (.n 646) (.n 646),
    .mul (.n 648) (.n 647) (.n 647), .const (.n 649) pkC, .mul (.n 650) (.n 408) (.n 649),
    .mul (.n 651) (.n 650) (.n 409), .mul (.n 652) (.n 651) (.n 484), .mul (.n 648) (.n 653) (.n 652),
    .const (.n 654) (word 1 0), .add (.n 655) (.n 653) (.n 654), .const (.n 656) (word 2 0),
    .add (.n 657) (.n 653) (.n 656), .mul (.n 658) (.n 655) (.n 657), .const (.n 659) (word 4 0),
    .add (.n 660) (.n 653) (.n 659), .mul (.n 661) (.n 658) (.n 660), .const (.n 662) (word 8 0),
    .add (.n 663) (.n 653) (.n 662), .mul (.n 664) (.n 661) (.n 663), .const (.n 665) (word 16 0),
    .add (.n 666) (.n 653) (.n 665), .mul (.n 667) (.n 664) (.n 666), .const (.n 668) (word 32 0),
    .add (.n 669) (.n 653) (.n 668), .mul (.n 670) (.n 667) (.n 669), .const (.n 671) (word 64 0),
    .add (.n 672) (.n 653) (.n 671), .mul (.n 673) (.n 670) (.n 672), .const (.n 674) (word 128 0),
    .add (.n 675) (.n 653) (.n 674), .mul (.n 676) (.n 673) (.n 675), .const (.n 677) (word 0 0),
    .assertEq (.n 676) (.n 677), .load (.n 573) (.n 10) 0, .const (.n 678) (word 2 0),
    .mul (.n 679) (.n 10) (.n 678)]

/-- Statement `574`: `squeeze_packed`. -/
def vsC8s : Stmt :=
  .call "squeeze_packed" [.n 575, .n 576, .n 577, .n 578, .n 579, .n 679, .n 645] [.n 680, .n 681, .n 682, .n 683, .n 684]

set_option maxRecDepth 200000 in
theorem vsC7_eq : (vsC.drop 60).take 86 = vsOpG ++ vsC7q.map Stmt.atom := stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 200000 in
theorem vsC8_eq : (vsC.drop 146).take 1 = [vsC8s] := stmtsEqb_sound (by decide +kernel)

theorem vsC_w7_eq : vsC_w7 = .run (atomsOf vsOpG ++ vsC7q) := by
  rw [vsC_w7, vsC7_eq, atomsOf_append', atomsOf_map]

theorem vsC_w8_eq : vsC_w8 = .call vsC8s := by rw [vsC_w8, headD_of_take_one vsC8_eq]

set_option maxRecDepth 200000 in
/-- No store into the opening grind's values. -/
theorem vsOp_noStore : (storesOf 482 vsC).all (fun a => !loadInto 581 (581 + (gcLen 2 - 2)) a) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
/-- The packing word is first read here, the opening's first word stored. -/
theorem vsC7_stores : (storesOf 482 vsC).contains (.load (.n 645) (.n 9) 3) = false ∧
    (storesOf 482 vsC).contains (.load (.n 573) (.n 10) 0) = true := by decide +kernel

theorem vsC7q_pure : vsC7q.filter pureAsks = [.mul (.n 648) (.n 653) (.n 652), .assertEq (.n 676) (.n 677)] := by
  decide +kernel

theorem vsC7q_mem : vsC7q.filter memAsks = [.load (.n 645) (.n 9) 3, .load (.n 573) (.n 10) 0] := by
  decide +kernel

theorem pkC_ne : pkC ≠ 0 := by decide

/-- The product of `c + 2^i`, `i < 8`, as the packing check computes it. -/
def pkProd (c : E) : E :=
  (((((((c + word 1 0) * (c + word 2 0)) * (c + word 4 0)) * (c + word 8 0)) * (c + word 16 0)) *
    (c + word 32 0)) * (c + word 64 0)) * (c + word 128 0)

theorem pkProd_zero {j : ℕ} (hj : j < 8) : pkProd (word (2 ^ j) 0) = 0 := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [pkProd, Link.add_self_E]

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 : Reader} {w : ℕ → E}
  {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **`wC`'s windows `7 ..< 9`' hypotheses**: the opening grind's honest windows and proof of work on `w 574`, the
exponent table as in `vsPh5_wins`, the shape's buffer at `b9` (its word `3` the packing word `f4`, on the evaluation
memory and on every memory holding the words), `g^n`, `g^w`, `g^chunkCount w` at `.n 408`, `.n 409`, `.n 484`, the
packing check `f4^8 / (g^n·c·g^w·g^chunkCount w) = 2^j`, `j < 8`, the buffer `.n 10` at `b10` holding `w 573`,
`squeeze_packed`'s `CallAtA` on its arguments' values at a given end `ec`, its returns the oracle's; `K` at `ec`. -/
theorem vsPh6_wins (hk : 11 ≤ k) (ha : args.length = 6) {st : St} {K : St → Prop}
    {qt b9 b10 n wd cc jj : ℕ} {f4 : E} {sh : List E}
    (h4 : vsVal rd0 w args (.n 4) = ptrAt qt) (hl0 : LowDef k rd0) (rt : ExpWinTab rd0 (ptrAt qt))
    (hPt : ∀ rd, Pre rd → ExpWinTab rd (ptrAt qt)) (hRq : ∀ j < 2 ^ 11, R (qt + (j + 178)))
    (hwin : ∀ j ≤ gcW 2, w (581 + j) = gcWin 2 (w 574) j) (hlow : ((w 574).limb 0).lane.toNat % 2 ^ 2 = 0)
    (h9 : vsVal rd0 w args (.n 9) = ptrAt b9) (hsh : 3 < sh.length) (hf4 : sh[3] = f4)
    (r9 : ReadsAt rd0 (ptrAt b9) sh) (hO9 : ∀ rd, st.O rd → ReadsAt rd (ptrAt b9) sh) (hOwn9 : Own (b9 + 3))
    (h408 : vsVal rd0 w args (.n 408) = gen ^ n) (h409 : vsVal rd0 w args (.n 409) = gen ^ wd)
    (hw484 : w 484 = gen ^ cc) (hj : jj < 8)
    (hpk : f4 ^ 8 * (gen ^ n * pkC * gen ^ wd * gen ^ cc)⁻¹ = word (2 ^ jj) 0)
    (h10 : vsVal rd0 w args (.n 10) = ptrAt b10) (hOwn10 : Own (b10 + 0))
    (hO10 : ∀ rd, Pre rd → st.O rd → LoadHolds rd (ptrAt b10) 0 (w 573))
    {Rc Dc : ℕ → Prop} {Oc Pc : Reader → Prop} {Qc : Reader → Tree → Prop} {Bc ec : ℕ}
    (hc : CallAtA fs al cert k "squeeze_packed" [w 575, w 576, w 577, w 578, w 579, ptrAt (b10 + 1), f4]
      [w 680, w 681, w 682, w 683, w 684] Rc Dc Oc Pc Qc Bc (allocBase (al "squeeze_packed") st.kc)
      (allocBase (al "squeeze_packed") st.kc + Bc) ec)
    (hRc : ∀ i, Rc i → (R i ∨ Own i) ∨ st.D i) (hPc : ∀ rd, Pre rd ∧ st.O rd → Pc rd)
    (hK : K ⟨st.a, ec, fun rd => st.O rd ∧ Oc rd, fun i => st.D i ∨ Dc i, st.Qs ++ [Qc]⟩) :
    WinsHyp fs al cert k (vsVal rd0 w args) w Own R Pre [vsC_w7, vsC_w8] st K := by
  rw [vsC_w7_eq, vsC_w8_eq, WinsHyp]
  set σ := vsVal rd0 w args with hσ
  have hgC := vsVal_goodC (rd := rd0) (w := w) ha
  have memC7 : ∀ x ∈ vsOpG ++ vsC7q.map Stmt.atom, x ∈ vsC := fun x hx =>
    List.mem_of_mem_drop (List.mem_of_mem_take (by rw [vsC7_eq]; exact hx))
  have hg7 : ∀ a ∈ vsC7q, Good rd0 (storesOf 482 vsC) w σ a := fun a h =>
    hgC (.atom a) (memC7 _ (List.mem_append_right _ (List.mem_map_of_mem h)))
  have hgG : ∀ x ∈ vsOpG, GoodS rd0 (storesOf 482 vsC) w σ x := fun x h =>
    hgC x (memC7 _ (List.mem_append_left _ h))
  have r6 : ∀ v ∈ [V.n 573, .n 574, .n 575, .n 576, .n 577, .n 578, .n 579, .n 580], σ v = w v.idx :=
    vsVal_retC (rd0 := rd0) (w := w) ha vsC6_eq
  have e574 : σ (.n 574) = w 574 := r6 (.n 574) (by simp)
  -- the grind
  have wt : ∀ rd, ExpWinTab rd (ptrAt qt) → WinTabs rd (σ (.n 4) * gen ^ 178) := fun rd h n hn => by
    rw [h4, loadHolds_mul_gen_pow]; exact h n hn
  have hS : ∀ a ∈ storesOf 482 vsC, loadInto 581 (581 + (gcLen 2 - 2)) a = false := fun a h => by
    have := List.all_eq_true.mp vsOp_noStore a h
    simpa using this
  have gG := gcO_atoms (k := k) (b := 2) (o := 581) (off := 178) (wv := .n 574) (tabs := .n 4) hk (by decide)
    (by show 574 < 581; omega) (by show 4 < 581; omega) hgG hS hl0 (wt rd0 rt) (by rw [e574]; exact hwin)
    (by rw [e574]; exact hlow)
  -- the packing check
  have mf : ∀ d x y, Atom.mul (.n d) (.n x) (.n y) ∈ vsC7q → x < d → y < d → σ (.n d) = σ (.n x) * σ (.n y) :=
    fun d x y hm hx hy => good_mulF (hg7 _ hm) hx hy
  have cs : ∀ (d : ℕ) (e : E), Atom.const (.n d) e ∈ vsC7q → σ (.n d) = e := fun d e h => hg7 _ h
  have ad : ∀ d x y, Atom.add (.n d) (.n x) (.n y) ∈ vsC7q → σ (.n d) = σ (.n x) + σ (.n y) := fun d x y h => hg7 _ h
  have fr := vsC7_stores
  have e645 : σ (.n 645) = f4 := by
    rw [← hf4]
    exact good_loadAt (by intro h; rw [List.contains_iff_mem.mpr h] at fr; exact absurd fr.1 (by decide))
      (hg7 _ (by simp [vsC7q])) h9 hsh r9
  have e648 : σ (.n 648) = f4 ^ 8 := by
    rw [mf 648 647 647 (by simp [vsC7q]) (by omega) (by omega), mf 647 646 646 (by simp [vsC7q]) (by omega) (by omega),
      mf 646 645 645 (by simp [vsC7q]) (by omega) (by omega), e645]
    ring
  have e652 : σ (.n 652) = gen ^ n * pkC * gen ^ wd * gen ^ cc := by
    rw [mf 652 651 484 (by simp [vsC7q]) (by omega) (by omega), mf 651 650 409 (by simp [vsC7q]) (by omega) (by omega),
      mf 650 408 649 (by simp [vsC7q]) (by omega) (by omega), h408, h409, cs 649 pkC (by simp [vsC7q]),
      show σ (.n 484) = w 484 from (vsVal_retC (rd0 := rd0) (w := w) ha vsC1_eq (.n 484) (List.mem_singleton_self _)),
      hw484]
  have n652 : σ (.n 652) ≠ 0 := by
    rw [e652]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero pow_ne pkC_ne) pow_ne) pow_ne
  have e653 : σ (.n 653) = word (2 ^ jj) 0 := by
    rw [good_mulD (hg7 (.mul (.n 648) (.n 653) (.n 652)) (by simp [vsC7q])) (by omega), e648, e652, hpk]
  have e676 : σ (.n 676) = pkProd (σ (.n 653)) := by
    rw [mf 676 673 675 (by simp [vsC7q]) (by omega) (by omega), mf 673 670 672 (by simp [vsC7q]) (by omega) (by omega),
      mf 670 667 669 (by simp [vsC7q]) (by omega) (by omega), mf 667 664 666 (by simp [vsC7q]) (by omega) (by omega),
      mf 664 661 663 (by simp [vsC7q]) (by omega) (by omega), mf 661 658 660 (by simp [vsC7q]) (by omega) (by omega),
      mf 658 655 657 (by simp [vsC7q]) (by omega) (by omega),
      ad 655 653 654 (by simp [vsC7q]), ad 657 653 656 (by simp [vsC7q]), ad 660 653 659 (by simp [vsC7q]),
      ad 663 653 662 (by simp [vsC7q]), ad 666 653 665 (by simp [vsC7q]), ad 669 653 668 (by simp [vsC7q]),
      ad 672 653 671 (by simp [vsC7q]), ad 675 653 674 (by simp [vsC7q]),
      cs 654 (word 1 0) (by simp [vsC7q]), cs 656 (word 2 0) (by simp [vsC7q]), cs 659 (word 4 0) (by simp [vsC7q]), cs 662 (word 8 0) (by simp [vsC7q]),
      cs 665 (word 16 0) (by simp [vsC7q]), cs 668 (word 32 0) (by simp [vsC7q]), cs 671 (word 64 0) (by simp [vsC7q]), cs 674 (word 128 0) (by simp [vsC7q])]
    rfl
  have e677 : σ (.n 677) = 0 := (cs 677 _ (by simp [vsC7q])).trans zero_eq_word
  have e679 : σ (.n 679) = ptrAt (b10 + 1) := by
    rw [mf 679 10 678 (by simp [vsC7q]) (by omega) (by omega), h10,
      show σ (.n 678) = word 2 0 from cs 678 _ (by simp [vsC7q]), show word 2 0 = gen ^ 1 from wordG (j := 1) (by norm_num),
      ptrAt_add]
  have hh7 : heapHintAddrs σ ((atomsOf vsOpG ++ vsC7q).map Ev.atom) = [] := rfl
  refine ⟨RunHyp.of_asks rfl ?_ (fun A hA => by rw [hh7] at hA; simp at hA) ?_ ?_, ?_⟩
  · intro A hA
    obtain ⟨d, p, off, hm, rfl⟩ := mem_loadAddrs hA
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨rfl, e, he, hp⟩ := (gG _ hm).2.2 d p off rfl
      refine ⟨qt + (e + 178), ?_, Or.inr (Or.inl (hRq e he))⟩
      rw [hp, h4, ptrAt_add, ptrAt, B1.Main.addr_ofK, Nat.add_assoc]
    · have hm' : Atom.load d p off ∈ vsC7q.filter memAsks := List.mem_filter.mpr ⟨hm, rfl⟩
      rw [vsC7q_mem] at hm'
      simp only [List.mem_cons, List.not_mem_nil, or_false, Atom.load.injEq] at hm'
      rcases hm' with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
      · exact ⟨b9 + 3, by rw [h9, ptrAt, B1.Main.addr_ofK], Or.inl hOwn9⟩
      · exact ⟨b10 + 0, by rw [h10, ptrAt, B1.Main.addr_ofK], Or.inl hOwn10⟩
  · intro x hx
    obtain ⟨hx, hpa⟩ := List.mem_filter.mp hx
    rcases List.mem_append.mp hx with hx | hx
    · exact (gG x hx).1
    · have hx' : x ∈ vsC7q.filter pureAsks := List.mem_filter.mpr ⟨hx, hpa⟩
      rw [vsC7q_pure] at hx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
      rcases hx' with rfl | rfl
      · exact pureF_div n652
      · show σ (.n 676) + σ (.n 677) = 0
        rw [e676, e677, e653, pkProd_zero hj, add_zero]
  · intro rd _ hp ho x hx
    obtain ⟨hx, hma⟩ := List.mem_filter.mp hx
    rcases List.mem_append.mp hx with hx | hx
    · exact (gG x hx).2.1 rd (wt rd (hPt rd hp))
    · have hx' : x ∈ vsC7q.filter memAsks := List.mem_filter.mpr ⟨hx, hma⟩
      rw [vsC7q_mem] at hx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
      rcases hx' with rfl | rfl
      · show LoadHolds rd (σ (.n 9)) 3 (σ (.n 645))
        rw [h9, e645, ← hf4]; exact hO9 rd ho 3 hsh
      · show LoadHolds rd (σ (.n 10)) 0 (σ (.n 573))
        rw [h10, r6 (.n 573) (by simp)]; exact hO10 rd hp ho
  rw [show allocs σ ((atomsOf vsOpG ++ vsC7q).map Ev.atom) = [] from rfl, List.sum_nil, Nat.add_zero]
  -- `squeeze_packed`
  have hargs : (argsOf vsC8s).map σ = [w 575, w 576, w 577, w 578, w 579, ptrAt (b10 + 1), f4] := by
    show [σ (.n 575), σ (.n 576), σ (.n 577), σ (.n 578), σ (.n 579), σ (.n 679), σ (.n 645)] = _
    rw [r6 (.n 575) (by simp), r6 (.n 576) (by simp), r6 (.n 577) (by simp), r6 (.n 578) (by simp),
      r6 (.n 579) (by simp), e679, e645]
  have r8 : ∀ v ∈ [V.n 680, .n 681, .n 682, .n 683, .n 684], σ v = w v.idx :=
    vsVal_retC (rd0 := rd0) (w := w) ha vsC8_eq
  have hrets : (retsOf vsC8s).map σ = [w 680, w 681, w 682, w 683, w 684] := by
    show [σ (.n 680), σ (.n 681), σ (.n 682), σ (.n 683), σ (.n 684)] = _
    rw [r8 (.n 680) (by simp), r8 (.n 681) (by simp), r8 (.n 682) (by simp), r8 (.n 683) (by simp),
      r8 (.n 684) (by simp)]
  rw [← hargs, ← hrets] at hc
  exact winsHyp_call_at (g := "squeeze_packed") rfl hc (fun i hi => (hRc i hi).imp_right id)
    (fun rd hp => hPc rd hp) hK

end

end
end LeanVM.Guest.B1.VsC
