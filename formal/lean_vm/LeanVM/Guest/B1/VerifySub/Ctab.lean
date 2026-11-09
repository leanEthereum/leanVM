/-
  LeanVM.Guest.B1.VerifySub.Ctab

  Two sections of `verify_sub`: the bus challenges' equality weights `fp_w` (G:3419-3421) and the
  ring map's Frobenius coefficients `c_table` (G:3445-3462).
-/

module

public import LeanVM.Guest.B1.VerifySub.Template
public import LeanVM.Protocol.Keccak.Multilinear
public import LeanVM.Guest.B1.VerifySub.CtabCheck

/-!
# `fp_w` and `c_table`

* `vsFpwT_holds`: `fp_w[x] = eq_weight(bus_alpha, 4, x, 0)`, bit `t` of `x` choosing `α_t`
  (else `1 + α_t`), is `eqKernel alphas` (`eqKernel`'s first coordinate is its index's lowest
  bit, as `eq_weight`'s).
* `vsCtabT_holds`: `c_table` is `ringCoefficients` of the six challenges. Every value of the
  section is a monomial in the challenges: `ctRun`, evaluated by the kernel, records each value's
  and each table cell's exponents (`ctRun_sound`), and the table's are `ringCoefficients`'
  (`ct_final`, `ringCoefficients_getD`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {next : Prop} {kret : List E → Prop}

/-! ## `fp_w` -/

theorem vsEqwFactor_holds {x t v : ℕ} {a : E} (ha : LoadHolds rd (σ (.n 346)) t a)
    (h : Stmt.HoldsList C rd σ (vsEqwFactor x t v).1 next kret) :
    σ (.n (vsEqwFactor x t v).2.1) = (if x.testBit t then a else 1 + a) ∧ next := by
  unfold vsEqwFactor at h ⊢
  by_cases hb : x.testBit t
  · simp only [hb, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, vsLd] at h ⊢
    exact ⟨loadHolds_unique h.1 ha, h.2⟩
  · simp only [hb, Bool.false_eq_true, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, vsLd,
      vsConst, vsAdd] at h ⊢
    obtain ⟨l, c, s, n⟩ := h
    refine ⟨?_, n⟩
    rw [s, c, loadHolds_unique l ha, word_one]

theorem testBit_eqAt (x : ℕ) (a0 a1 a2 a3 : E) :
    eqAt [a0, a1, a2, a3] x =
      (if x.testBit 0 then a0 else 1 + a0) * (if x.testBit 1 then a1 else 1 + a1) *
        (if x.testBit 2 then a2 else 1 + a2) * (if x.testBit 3 then a3 else 1 + a3) := by
  simp only [eqAt_cons, eqAt_nil, Nat.testBit_eq_decide_div_mod_eq, Nat.div_div_eq_div_mul,
    decide_eq_true_eq, mul_one]
  norm_num
  ring_nf

theorem vsEqwT_holds {x v : ℕ} {a0 a1 a2 a3 : E}
    (ha : ReadsAt rd (σ (.n 346)) [a0, a1, a2, a3])
    (h : Stmt.HoldsList C rd σ (vsEqwT x v).1 next kret) :
    σ (.n (vsEqwT x v).2.1) = eqAt [a0, a1, a2, a3] x ∧ next := by
  have l0 : LoadHolds rd (σ (.n 346)) 0 a0 := ha 0 (by simp)
  have l1 : LoadHolds rd (σ (.n 346)) 1 a1 := ha 1 (by simp)
  have l2 : LoadHolds rd (σ (.n 346)) 2 a2 := ha 2 (by simp)
  have l3 : LoadHolds rd (σ (.n 346)) 3 a3 := ha 3 (by simp)
  unfold vsEqwT at h ⊢
  simp only [holdsList_append] at h
  obtain ⟨e0, h⟩ := vsEqwFactor_holds l0 h
  obtain ⟨e1, h⟩ := vsEqwFactor_holds l1 h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, vsMul] at h
  obtain ⟨m1, h⟩ := h
  obtain ⟨e2, h⟩ := vsEqwFactor_holds l2 h
  obtain ⟨m2, h⟩ := h
  obtain ⟨e3, h⟩ := vsEqwFactor_holds l3 h
  obtain ⟨m3, h⟩ := h
  refine ⟨?_, h⟩
  rw [m3, m2, m1, e0, e1, e2, e3, testBit_eqAt]

theorem fpw_loop {a0 a1 a2 a3 : E} (ha : ReadsAt rd (σ (.n 346)) [a0, a1, a2, a3]) :
    ∀ (l : List ℕ) {next : Prop}, Stmt.HoldsList C rd σ (l.flatMap fun x ↦
      (vsEqwT x (vsFpwStart x)).1 ++ [vsLd (vsEqwT x (vsFpwStart x)).2.1 427 x]) next kret →
      (∀ x ∈ l, LoadHolds rd (σ (.n 427)) x (eqAt [a0, a1, a2, a3] x)) ∧ next
  | [], _, h => ⟨fun _ hx ↦ absurd hx (by simp), h⟩
  | x :: l, _, h => by
    rw [List.flatMap_cons, holdsList_append, holdsList_append] at h
    obtain ⟨e, h⟩ := vsEqwT_holds ha h
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, vsLd] at h
    obtain ⟨lx, h⟩ := h
    obtain ⟨hl, hn⟩ := fpw_loop ha l h
    refine ⟨fun y hy ↦ ?_, hn⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · rw [← e]; exact lx
    · exact hl y hy

/-- **`fp_w`** (G:3419-3422): the bus challenges' equality weights, then `β`'s squeeze. -/
theorem vsFpwT_holds {alphas : List E} (hl : alphas.length = 4)
    (ha : ReadsAt rd (σ (.n 346)) alphas) (h : Stmt.HoldsList C rd σ vsFpwT next kret) :
    ReadsAt rd (σ (.n 427)) (eqKernel alphas) ∧ Stmt.HoldsList C rd σ (vsSqzT 415 604) next kret := by
  match alphas, hl with
  | [a0, a1, a2, a3], _ =>
    unfold vsFpwT at h
    rw [holdsList_append] at h
    simp only [Stmt.HoldsList, Stmt.Holds, vsAlloc, Atom.Holds, true_and] at h
    obtain ⟨hw, hn⟩ := fpw_loop ha (List.range 16) h
    refine ⟨fun k hk ↦ ?_, hn⟩
    have hk' : k < 16 := by rw [eqKernel_length] at hk; simpa using hk
    have e := eqKernel_getD [a0, a1, a2, a3] k
    rw [List.getD_eq_getElem _ _ hk, ite_eq_left_of_eq_true _ _ (eq_true (by simpa using hk'))] at e
    rw [e]
    exact hw k (List.mem_range.2 hk')

/-! ## `c_table` -/

theorem foldl_filter_mul {α : Type} (F : E → α → E) (hF : ∀ acc x, F acc x = acc * F 1 x)
    (p : α → Bool) : ∀ (L : List α) (acc : E),
      (L.filter p).foldl F acc = acc * (L.map fun x ↦ if p x then F 1 x else 1).prod
  | [], acc => by simp
  | x :: L, acc => by
    rw [List.filter_cons, List.map_cons, List.prod_cons]
    by_cases hp : p x
    · simp only [hp, ↓reduceIte, List.foldl_cons]
      rw [foldl_filter_mul F hF p L, hF acc x, mul_assoc]
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, one_mul]
      exact foldl_filter_mul F hF p L acc

theorem specEV_getD {k i : ℕ} (hi : i < 6) : (specEV k).getD i 0 =
    if k &&& ringMapShifts.getD i 0 ≠ 0 then 2 ^ (k % ringMapShifts.getD i 0) else 0 := by
  rw [specEV, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

/-- `ringCoefficients`' `k`-th product is the monomial `specEV k`. -/
theorem ringCoefficients_getElem {chs : List E} (hl : chs.length = 6) {k : ℕ} (hk : k < 64) :
    (ringCoefficients chs)[k]'(by simp [ringCoefficients, kBits]; exact hk) =
      evVal chs (specEV k) := by
  match chs, hl with
  | [c0, c1, c2, c3, c4, c5], _ =>
    simp only [ringCoefficients, List.getElem_map, List.getElem_range]
    rw [foldl_filter_mul _ (fun acc x ↦ by rcases x with ⟨f, s⟩; simp)]
    rw [show evVal [c0, c1, c2, c3, c4, c5] (specEV k) = ∏ i ∈ range 6,
        (if k &&& ringMapShifts.getD i 0 ≠ 0 then
          [c0, c1, c2, c3, c4, c5].getD i 0 ^ (2 ^ (k % ringMapShifts.getD i 0)) else 1) from
      Finset.prod_congr rfl fun i hi ↦ by
        rw [specEV_getD (mem_range.1 hi)]
        split_ifs <;> simp]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, ringMapShifts, List.zip_cons_cons,
      List.zip_nil_right, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      List.getD_cons_zero, List.getD_cons_succ, one_mul, mul_one, decide_eq_true_eq]
    ring

/-- **`c_table`** (G:3439-3448): the ring map's Frobenius coefficients are `ringCoefficients` of
its six challenges, then `ring_switch_target` is called. -/
theorem vsCtabT_holds {chs : List E} (hl : chs.length = 6) (hc : ReadsAt rd (σ (.n 664)) chs)
    (h : Stmt.HoldsList C rd σ vsCtabT next kret) :
    ReadsAt rd (σ (.n 665)) (ringCoefficients chs) ∧
      C "ring_switch_target" [σ (.n 648), σ (.n 664)] [σ (.n 1091)] ∧ next := by
  rw [vsCtabT_eq, holdsList_append] at h
  have hc0 := ct_check
  generalize hr : ctRun ⟨[], []⟩ ctPre = r at hc0
  rcases r with _ | st
  · cases hc0
  simp only [Option.map_some, Option.some.injEq, List.all_eq_true, List.mem_range, beq_iff_eq]
    at hc0
  obtain ⟨⟨-, hm⟩, h⟩ := ctRun_sound hl hc hr ⟨fun _ hp ↦ absurd hp (by simp),
    fun _ hp ↦ absurd hp (by simp)⟩ h
  simp only [Stmt.HoldsList, Stmt.Holds, vsCall, List.map_cons, List.map_nil] at h
  refine ⟨fun k hk ↦ ?_, h⟩
  have hk' : k < 64 := by simpa [ringCoefficients, kBits] using hk
  rw [ringCoefficients_getElem hl hk']
  exact (hm _ (lookup_mem (hc0 k hk'))).1

end
end LeanVM.Guest.B1.VerifySub
