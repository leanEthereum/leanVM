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

/-- **The setup's call arguments** on a valuation satisfying its equations. -/
theorem packSetup_vals {first : ℕ} (hg : ∀ s ∈ packSetupT first, GoodS rd S w σ s) :
    σ (.n 1058) = 1 + σ (.n 9) ∧ σ (.n 1059) = 1 ∧ σ (.n 1060) = σ (.n 1053) * σ (.n 9) ∧
      σ (.n 1064) = σ (.n 1051) * σ (.n 9) ^ 8 ∧ σ (.n 1068) = σ (.n 1052) * σ (.n 9) ^ 8 ∧
      σ (.n 1070) = 1 + σ (.n 10) ∧ σ (.n 1071) = 1 := by
  have gs : ∀ a, Stmt.atom a ∈ packSetupT first → Good rd S w σ a := fun a ha ↦ hg _ ha
  have e1057 : σ (.n 1057) = word 1 0 0 := gs (.const (.n 1057) _) (by simp [packSetupT])
  have e1058 : σ (.n 1058) = σ (.n 1057) + σ (.n 9) := gs (.add (.n 1058) _ _) (by simp [packSetupT])
  have e1059 : σ (.n 1059) = word 1 0 0 := gs (.const (.n 1059) _) (by simp [packSetupT])
  have e1060 : σ (.n 1060) = σ (.n 1053) * σ (.n 9) := good_mul (by decide) (gs _ (by simp [packSetupT]))
  have e1061 : σ (.n 1061) = σ (.n 9) * σ (.n 9) := good_mul (by decide) (gs _ (by simp [packSetupT]))
  have e1062 : σ (.n 1062) = σ (.n 1061) * σ (.n 1061) := good_mul (by decide) (gs _ (by simp [packSetupT]))
  have e1063 : σ (.n 1063) = σ (.n 1062) * σ (.n 1062) := good_mul (by decide) (gs _ (by simp [packSetupT]))
  have e1064 : σ (.n 1064) = σ (.n 1051) * σ (.n 1063) := good_mul (by decide) (gs _ (by simp [packSetupT]))
  have e1065 : σ (.n 1065) = σ (.n 9) * σ (.n 9) := good_mul (by decide) (gs _ (by simp [packSetupT]))
  have e1066 : σ (.n 1066) = σ (.n 1065) * σ (.n 1065) := good_mul (by decide) (gs _ (by simp [packSetupT]))
  have e1067 : σ (.n 1067) = σ (.n 1066) * σ (.n 1066) := good_mul (by decide) (gs _ (by simp [packSetupT]))
  have e1068 : σ (.n 1068) = σ (.n 1052) * σ (.n 1067) := good_mul (by decide) (gs _ (by simp [packSetupT]))
  have e1069 : σ (.n 1069) = word 1 0 0 := gs (.const (.n 1069) _) (by simp [packSetupT])
  have e1070 : σ (.n 1070) = σ (.n 1069) + σ (.n 10) := gs (.add (.n 1070) _ _) (by simp [packSetupT])
  have e1071 : σ (.n 1071) = word 1 0 0 := gs (.const (.n 1071) _) (by simp [packSetupT])
  refine ⟨by rw [e1058, e1057, word_one], by rw [e1059, word_one], e1060,
    by rw [e1064, gen_pow_eight_of _ _ _ _ e1061 e1062 e1063],
    by rw [e1068, gen_pow_eight_of _ _ _ _ e1065 e1066 e1067], by rw [e1070, e1069, word_one],
    by rw [e1071, word_one]⟩

/-- **The pack rounds' setup, completely**: with the claim's point pointer in its record, the
first round record in memory, and the two loops' relations, the setup holds. -/
theorem packSetup_complete {first : ℕ} (hg : ∀ s ∈ packSetupT first, GoodS rd S w σ s)
    (hS : Atom.load (.n 1051) (.n 11) 2 ∉ S) {pp : E} (hpp : LoadHolds rd (σ (.n 11)) 2 pp)
    (hrec : RoundRec rd (σ (.n 1053)) 0 ((cap5 866).map σ) (σ (.n 7) * gen ^ 47) (σ (.n 1050)) 1)
    (hik : IsInK (1 + σ (.n 9)))
    (hcall : 1 + σ (.n 9) ≠ 0 →
      C (packLoopName first) [1, σ (.n 9), σ (.n 1053), pp, σ (.n 1052)] [])
    (hik' : IsInK (1 + σ (.n 10)))
    (hcall' : 1 + σ (.n 10) ≠ 0 →
      C (remLoopName first) [1, σ (.n 10), σ (.n 1053) * σ (.n 9), pp * σ (.n 9) ^ 8,
        σ (.n 1052) * σ (.n 9) ^ 8] []) :
    σ (.n 1051) = pp ∧ σ (.n 1060) = σ (.n 1053) * σ (.n 9) ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList C rd σ (packSetupT first) next kret := by
  have gs : ∀ a, Stmt.atom a ∈ packSetupT first → Good rd S w σ a := fun a ha ↦ hg _ ha
  have epp := load_val (w := w) (gs _ (by simp [packSetupT])) hS hpp
  have e1054 : σ (.n 1054) = word 140737488355328 0 0 := gs (.const (.n 1054) _) (by simp [packSetupT])
  have e1055 : σ (.n 1055) = σ (.n 7) * σ (.n 1054) := good_mul (by decide) (gs _ (by simp [packSetupT]))
  have e1056 : σ (.n 1056) = word 1 0 0 := gs (.const (.n 1056) _) (by simp [packSetupT])
  have e1057 : σ (.n 1057) = word 1 0 0 := gs (.const (.n 1057) _) (by simp [packSetupT])
  have e1058 : σ (.n 1058) = σ (.n 1057) + σ (.n 9) := gs (.add (.n 1058) _ _) (by simp [packSetupT])
  have e1059 : σ (.n 1059) = word 1 0 0 := gs (.const (.n 1059) _) (by simp [packSetupT])
  have e1060 : σ (.n 1060) = σ (.n 1053) * σ (.n 9) := good_mul (by decide) (gs _ (by simp [packSetupT]))
  have e1061 : σ (.n 1061) = σ (.n 9) * σ (.n 9) := good_mul (by decide) (gs _ (by simp [packSetupT]))
  have e1062 : σ (.n 1062) = σ (.n 1061) * σ (.n 1061) := good_mul (by decide) (gs _ (by simp [packSetupT]))
  have e1063 : σ (.n 1063) = σ (.n 1062) * σ (.n 1062) := good_mul (by decide) (gs _ (by simp [packSetupT]))
  have e1064 : σ (.n 1064) = σ (.n 1051) * σ (.n 1063) := good_mul (by decide) (gs _ (by simp [packSetupT]))
  have e1065 : σ (.n 1065) = σ (.n 9) * σ (.n 9) := good_mul (by decide) (gs _ (by simp [packSetupT]))
  have e1066 : σ (.n 1066) = σ (.n 1065) * σ (.n 1065) := good_mul (by decide) (gs _ (by simp [packSetupT]))
  have e1067 : σ (.n 1067) = σ (.n 1066) * σ (.n 1066) := good_mul (by decide) (gs _ (by simp [packSetupT]))
  have e1068 : σ (.n 1068) = σ (.n 1052) * σ (.n 1067) := good_mul (by decide) (gs _ (by simp [packSetupT]))
  have e1069 : σ (.n 1069) = word 1 0 0 := gs (.const (.n 1069) _) (by simp [packSetupT])
  have e1070 : σ (.n 1070) = σ (.n 1069) + σ (.n 10) := gs (.add (.n 1070) _ _) (by simp [packSetupT])
  have e1071 : σ (.n 1071) = word 1 0 0 := gs (.const (.n 1071) _) (by simp [packSetupT])
  obtain ⟨hcap, lcur, lcl, lsc⟩ := hrec
  have c : ∀ j < 5, LoadHolds rd (σ (.n 1053)) (16 * j) (σ (.n (866 + j))) := by
    intro j hj
    have := capAt_get hcap hj
    rw [zero_add] at this
    interval_cases j <;> simpa [cap5] using this
  have e1058' : σ (.n 1058) = 1 + σ (.n 9) := by rw [e1058, e1057, word_one]
  have e1070' : σ (.n 1070) = 1 + σ (.n 10) := by rw [e1070, e1069, word_one]
  refine ⟨epp, e1060, fun {next kret} hn ↦ ?_⟩
  simp only [packSetupT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
  refine ⟨by rw [epp]; exact hpp, trivial, trivial, c 0 (by norm_num), c 1 (by norm_num),
    c 2 (by norm_num), c 3 (by norm_num), c 4 (by norm_num), e1054, e1055, ?_, ?_, e1056, ?_,
    e1057, e1058, e1059, by rw [e1058']; exact hik, fun hne ↦ ?_, e1060, e1061, e1062, e1063,
    e1064, e1065, e1066, e1067, e1068, e1069, e1070, e1071, by rw [e1070']; exact hik',
    fun hne ↦ ?_, hn⟩
  · simpa [krCap, e1055, e1054, gen47] using lcur
  · simpa [krCap] using lcl
  · simpa [krCap, e1056, word_one] using lsc
  · rw [e1059, word_one, epp]
    exact hcall (by rw [← e1058']; exact hne)
  · have h8 : σ (.n 1063) = σ (.n 9) ^ 8 := gen_pow_eight_of _ _ _ _ e1061 e1062 e1063
    have h8' : σ (.n 1067) = σ (.n 9) ^ 8 := gen_pow_eight_of _ _ _ _ e1065 e1066 e1067
    rw [e1071, word_one, e1060, e1064, e1068, h8, h8', epp]
    exact hcall' (by rw [← e1070']; exact hne)

theorem last_kernel :
    lastT.all isAtom = true ∧ canonChk [] (atomsL ([] ++ lastT)) = true ∧
      resid (atomsL lastT) = (List.range 8).map (fun j ↦ .load (.n (1073 + j)) (.n 1072) (16 * j)) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 20000 in
/-- **The last record, completely**: with the record `rounds·step_g·rem_g` in memory, its
capacity, cursor, claim and scale are read, and `lastT` holds. -/
theorem last_complete (hσ : ∀ v, σ v = σ (.n v.idx)) (hg : ∀ s ∈ lastT, GoodS rd S w σ s)
    (hS : ∀ d off, Atom.load d (.n 1072) off ∉ S) {capL : List E} {curL vL scL : E}
    (hrec : RoundRec rd (σ (.n 1060) * σ (.n 10)) 0 capL curL vL scL) :
    σ (.n 1072) = σ (.n 1060) * σ (.n 10) ∧ (cap5 1073).map σ = capL ∧ σ (.n 1078) = curL ∧
      σ (.n 1079) = vL ∧ σ (.n 1080) = scL ∧ ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList C rd σ lastT next kret := by
  obtain ⟨hall, hk, hr⟩ := last_kernel
  have g72 : σ (.n 1072) = σ (.n 1060) * σ (.n 10) :=
    good_mul (by decide) (show Good rd S w σ (.mul (.n 1072) (.n 1060) (.n 10)) from
      hg (.atom (.mul (.n 1072) (.n 1060) (.n 10))) (by simp [lastT]))
  obtain ⟨⟨hcl, hcap⟩, lcur, lv, lsc⟩ := hrec
  rw [← g72] at hcap lcur lv lsc
  have gl : ∀ j < 8, Good rd S w σ (.load (.n (1073 + j)) (.n 1072) (16 * j)) :=
    fun j hj ↦ hg (.atom (.load _ _ _))
      (by
        unfold lastT
        exact List.mem_append_left _ (List.mem_append_right _
          (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)))
  have hcapj : ∀ j (hj : j < 5), LoadHolds rd (σ (.n 1072)) (16 * j)
      (capL[j]'(by omega)) := fun j hj ↦ by
    have := hcap j (by omega)
    rwa [zero_add, show j * krCap = 16 * j by simp [krCap]; ring] at this
  have ecap : ∀ j (hj : j < 5), σ (.n (1073 + j)) = capL[j]'(by omega) :=
    fun j hj ↦ load_val (gl j (by omega)) (hS _ _) (hcapj j hj)
  have lcur' : LoadHolds rd (σ (.n 1072)) (16 * 5) curL := by simpa [krCap] using lcur
  have lv' : LoadHolds rd (σ (.n 1072)) (16 * 6) vL := by simpa [krCap] using lv
  have lsc' : LoadHolds rd (σ (.n 1072)) (16 * 7) scL := by simpa [krCap] using lsc
  refine ⟨g72, ?_, load_val (gl 5 (by norm_num)) (hS _ _) lcur',
    load_val (gl 6 (by norm_num)) (hS _ _) lv', load_val (gl 7 (by norm_num)) (hS _ _) lsc', ?_⟩
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
  · refine block_holdsP (P := []) hall hσ hk (by simpa using hg) (A := []) (by simp) ?_
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
