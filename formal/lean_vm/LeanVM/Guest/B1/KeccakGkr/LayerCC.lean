/-
  LeanVM.Guest.B1.KeccakGkr.LayerCC

  `keccak_layer`'s pack rounds' setup and last record, completely.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCB

/-!
# The pack rounds' setup and the last record, completely

* `packSetup_complete`: with the claim's point pointer in its record, the first round record in
  memory, and the eight-round and remainder loops' relations, the setup holds.
* `last_complete`: with the last record in memory, `lastT` reads it and holds.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

theorem capAt_get {rec : E} {k : ℕ} {cap : List E} (h : CapAt rd rec k krCap cap) {j : ℕ}
    (hj : j < 5) : LoadHolds rd rec (k + 16 * j) (cap.getD j 0) := by
  obtain ⟨hl, h⟩ := h
  have := h j (by omega)
  rw [List.getD_eq_getElem _ _ (by omega), show k + 16 * j = k + j * krCap by simp [krCap]; ring]
  exact this

theorem goodS_mul_lt {d x y : ℕ} (hx : x < d) (hy : y < d)
    (h : GoodS rd S w σ (.atom (.mul (.n d) (.n x) (.n y)))) : σ (.n d) = σ (.n x) * σ (.n y) := by
  simp only [GoodS, Good] at h
  rwa [ite_pos' ⟨hx, hy⟩] at h

/-- The setup's equations. -/
theorem packSetup_goods {o first : ℕ} (ho : LayOff o) (hg : ∀ s ∈ packSetupT o first, GoodS rd S w σ s) :
    Good rd S w σ (.load (.n (o + 718)) (.n 11) 2) ∧
    σ (.n (o + 721)) = word 281474976710656 0 ∧ σ (.n (o + 722)) = σ (.n 7) * σ (.n (o + 721)) ∧
    σ (.n (o + 723)) = word 1 0 ∧ σ (.n (o + 724)) = word 1 0 ∧
    σ (.n (o + 725)) = σ (.n (o + 724)) + σ (.n 9) ∧ σ (.n (o + 726)) = word 1 0 ∧
    σ (.n (o + 727)) = σ (.n (o + 720)) * σ (.n 9) ∧ σ (.n (o + 728)) = σ (.n 9) * σ (.n 9) ∧
    σ (.n (o + 729)) = σ (.n (o + 728)) * σ (.n (o + 728)) ∧
    σ (.n (o + 730)) = σ (.n (o + 729)) * σ (.n (o + 729)) ∧
    σ (.n (o + 731)) = σ (.n (o + 718)) * σ (.n (o + 730)) ∧
    σ (.n (o + 732)) = σ (.n 9) * σ (.n 9) ∧
    σ (.n (o + 733)) = σ (.n (o + 732)) * σ (.n (o + 732)) ∧
    σ (.n (o + 734)) = σ (.n (o + 733)) * σ (.n (o + 733)) ∧
    σ (.n (o + 735)) = σ (.n (o + 719)) * σ (.n (o + 734)) ∧ σ (.n (o + 736)) = word 1 0 ∧
    σ (.n (o + 737)) = σ (.n (o + 736)) + σ (.n 10) ∧ σ (.n (o + 738)) = word 1 0 := by
  rcases ho with rfl | rfl <;>
  · simp only [packSetupT, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true] at hg
    obtain ⟨g718, -, -, -, -, -, -, -, g721, g722, -, -, g723, -, g724, g725, g726, -, g727, g728,
      g729, g730, g731, g732, g733, g734, g735, g736, g737, g738, -⟩ := hg
    exact ⟨g718, g721, goodS_mul_lt (by omega) (by omega) g722, g723, g724, g725, g726,
      goodS_mul_lt (by omega) (by omega) g727, goodS_mul_lt (by omega) (by omega) g728,
      goodS_mul_lt (by omega) (by omega) g729, goodS_mul_lt (by omega) (by omega) g730,
      goodS_mul_lt (by omega) (by omega) g731, goodS_mul_lt (by omega) (by omega) g732,
      goodS_mul_lt (by omega) (by omega) g733, goodS_mul_lt (by omega) (by omega) g734,
      goodS_mul_lt (by omega) (by omega) g735, g736, g737, g738⟩

/-- **The setup's call arguments** on a valuation satisfying its equations. -/
theorem packSetup_vals {o first : ℕ} (ho : LayOff o) (hg : ∀ s ∈ packSetupT o first, GoodS rd S w σ s) :
    σ (.n (o + 725)) = 1 + σ (.n 9) ∧ σ (.n (o + 726)) = 1 ∧ σ (.n (o + 727)) = σ (.n (o + 720)) * σ (.n 9) ∧
      σ (.n (o + 731)) = σ (.n (o + 718)) * σ (.n 9) ^ 8 ∧ σ (.n (o + 735)) = σ (.n (o + 719)) * σ (.n 9) ^ 8 ∧
      σ (.n (o + 737)) = 1 + σ (.n 10) ∧ σ (.n (o + 738)) = 1 := by
  obtain ⟨g718, e721, e722, e723, e724, e725, e726, e727, e728, e729, e730, e731, e732, e733,
    e734, e735, e736, e737, e738⟩ := packSetup_goods ho hg
  refine ⟨by rw [e725, e724, word_one], by rw [e726, word_one], e727,
    by rw [e731, gen_pow_eight_of _ _ _ _ e728 e729 e730],
    by rw [e735, gen_pow_eight_of _ _ _ _ e732 e733 e734], by rw [e737, e736, word_one],
    by rw [e738, word_one]⟩

/-- **The pack rounds' setup, completely**: with the claim's point pointer in its record, the
first round record in memory, and the two loops' relations, the setup holds. -/
theorem packSetup_complete {o first : ℕ} (ho : LayOff o) (hg : ∀ s ∈ packSetupT o first, GoodS rd S w σ s)
    (hS : Atom.load (.n (o + 718)) (.n 11) 2 ∉ S) {pp : E} (hpp : LoadHolds rd (σ (.n 11)) 2 pp)
    (hrec : RoundRec rd (σ (.n (o + 720))) 0 ((cap5 (o + 539)).map σ) (σ (.n 7) * gen ^ 48) (σ (.n (o + 717))) 1)
    (hik : IsInK (1 + σ (.n 9)))
    (hcall : 1 + σ (.n 9) ≠ 0 →
      C (packLoopName first) [1, σ (.n 9), σ (.n (o + 720)), pp, σ (.n (o + 719)), σ (.n 14)] [])
    (hik' : IsInK (1 + σ (.n 10)))
    (hcall' : 1 + σ (.n 10) ≠ 0 →
      C (remLoopName first) [1, σ (.n 10), σ (.n (o + 720)) * σ (.n 9), pp * σ (.n 9) ^ 8,
        σ (.n 14), σ (.n (o + 719)) * σ (.n 9) ^ 8] []) :
    σ (.n (o + 718)) = pp ∧ σ (.n (o + 727)) = σ (.n (o + 720)) * σ (.n 9) ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList C rd σ (packSetupT o first) next kret := by
  obtain ⟨g718, e721, e722, e723, e724, e725, e726, e727, e728, e729, e730, e731, e732, e733,
    e734, e735, e736, e737, e738⟩ := packSetup_goods ho hg
  have epp := load_val (w := w) g718 hS hpp
  obtain ⟨hcap, lcur, lcl, lsc⟩ := hrec
  have c : ∀ j < 5, LoadHolds rd (σ (.n (o + 720))) (16 * j) (σ (.n (o + 539 + j))) := by
    intro j hj
    have := capAt_get hcap hj
    rw [zero_add] at this
    interval_cases j <;> simpa [cap5] using this
  have e725' : σ (.n (o + 725)) = 1 + σ (.n 9) := by rw [e725, e724, word_one]
  have e737' : σ (.n (o + 737)) = 1 + σ (.n 10) := by rw [e737, e736, word_one]
  refine ⟨epp, e727, fun {next kret} hn ↦ ?_⟩
  simp only [packSetupT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  refine ⟨by rw [epp]; exact hpp, trivial, trivial, c 0 (by norm_num), c 1 (by norm_num),
    c 2 (by norm_num), c 3 (by norm_num), c 4 (by norm_num), e721, e722, ?_, ?_, e723, ?_,
    e724, e725, e726, by rw [e725']; exact hik, fun hne ↦ ?_, e727, e728, e729, e730,
    e731, e732, e733, e734, e735, e736, e737, e738, by rw [e737']; exact hik',
    fun hne ↦ ?_, hn⟩
  · simpa [krCap, e722, e721, gen48] using lcur
  · simpa [krCap] using lcl
  · simpa [krCap, e723, word_one] using lsc
  · rw [e726, word_one, epp]
    exact hcall (by rw [← e725']; exact hne)
  · have h8 : σ (.n (o + 730)) = σ (.n 9) ^ 8 := gen_pow_eight_of _ _ _ _ e728 e729 e730
    have h8' : σ (.n (o + 734)) = σ (.n 9) ^ 8 := gen_pow_eight_of _ _ _ _ e732 e733 e734
    rw [e738, word_one, e727, e731, e735, h8, h8', epp]
    exact hcall' (by rw [← e737']; exact hne)

theorem last_kernel {o : ℕ} (ho : LayOff o) :
    (lastT o).all isAtom = true ∧
      resid (atomsL (lastT o)) =
        (List.range 8).map (fun j ↦ .load (.n (o + 740 + j)) (.n (o + 739)) (16 * j)) := by
  rcases ho with rfl | rfl <;> exact ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 20000 in
/-- **The last record, completely**: with the record `rounds·step_g·rem_g` in memory, its
capacity, cursor, claim and scale are read, and `lastT` holds. -/
theorem last_complete {o : ℕ} (ho : LayOff o) (hσ : ∀ v, σ v = σ (.n v.idx))
    (hg : ∀ s ∈ lastT o, GoodS rd S w σ s)
    (hS : ∀ d off, Atom.load d (.n (o + 739)) off ∉ S) {capL : List E} {curL vL scL : E}
    (hrec : RoundRec rd (σ (.n (o + 727)) * σ (.n 10)) 0 capL curL vL scL) :
    σ (.n (o + 739)) = σ (.n (o + 727)) * σ (.n 10) ∧ (cap5 (o + 740)).map σ = capL ∧ σ (.n (o + 745)) = curL ∧
      σ (.n (o + 746)) = vL ∧ σ (.n (o + 747)) = scL ∧ ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList C rd σ (lastT o) next kret := by
  obtain ⟨hall, hr⟩ := last_kernel ho
  have g72 : σ (.n (o + 739)) = σ (.n (o + 727)) * σ (.n 10) :=
    good_mul ⟨idx_lt (by omega), idx_lt (by omega)⟩ (show Good rd S w σ (.mul (.n (o + 739)) (.n (o + 727)) (.n 10)) from
      hg (.atom (.mul (.n (o + 739)) (.n (o + 727)) (.n 10))) (by simp [lastT]))
  obtain ⟨⟨hcl, hcap⟩, lcur, lv, lsc⟩ := hrec
  rw [← g72] at hcap lcur lv lsc
  have gl : ∀ j < 8, Good rd S w σ (.load (.n (o + 740 + j)) (.n (o + 739)) (16 * j)) :=
    fun j hj ↦ hg (.atom (.load _ _ _))
      (by
        unfold lastT
        exact List.mem_append_left _ (List.mem_append_right _
          (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
  have hcapj : ∀ j (hj : j < 5), LoadHolds rd (σ (.n (o + 739))) (16 * j)
      (capL[j]'(by omega)) := fun j hj ↦ by
    have := hcap j (by omega)
    rwa [zero_add, show j * krCap = 16 * j by simp [krCap]; ring] at this
  have ecap : ∀ j (hj : j < 5), σ (.n (o + 740 + j)) = capL[j]'(by omega) :=
    fun j hj ↦ load_val (w := w) (gl j (by omega)) (hS _ _) (hcapj j hj)
  have lcur' : LoadHolds rd (σ (.n (o + 739))) (16 * 5) curL := by simpa [krCap] using lcur
  have lv' : LoadHolds rd (σ (.n (o + 739))) (16 * 6) vL := by simpa [krCap] using lv
  have lsc' : LoadHolds rd (σ (.n (o + 739))) (16 * 7) scL := by simpa [krCap] using lsc
  refine ⟨g72, ?_, load_val (gl 5 (by norm_num)) (hS _ _) lcur',
    load_val (w := w) (gl 6 (by norm_num)) (hS _ _) lv', load_val (w := w) (gl 7 (by norm_num)) (hS _ _) lsc', ?_⟩
  · obtain ⟨c0, c1, c2, c3, c4, rfl⟩ : ∃ c0 c1 c2 c3 c4, capL = [c0, c1, c2, c3, c4] := by
      match capL, hcl with
      | [c0, c1, c2, c3, c4], _ => exact ⟨c0, c1, c2, c3, c4, rfl⟩
    have e0 := ecap 0 (by norm_num)
    have e1 := ecap 1 (by norm_num)
    have e2 := ecap 2 (by norm_num)
    have e3 := ecap 3 (by norm_num)
    have e4 := ecap 4 (by norm_num)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at e0 e1 e2 e3 e4
    simp only [cap5, List.map_cons, List.map_nil, e0, e1, e2, e3, e4]
  · refine block_holds hall hσ hg ?_
    rw [hr]
    intro a ha
    right
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    have hj' := List.mem_range.mp hj
    rcases (show j < 5 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with hj5 | rfl | rfl | rfl
    · exact side_load (hS _ _) (hcapj j hj5)
    · exact side_load (hS _ _) lcur'
    · exact side_load (hS _ _) lv'
    · exact side_load (hS _ _) lsc'

end
end LeanVM.Guest.B1.VerifySub
