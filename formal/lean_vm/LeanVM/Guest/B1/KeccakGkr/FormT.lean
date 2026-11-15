/-
  LeanVM.Guest.B1.KeccakGkr.FormT

  `keccak_form`'s statements (`formAll`) compute `formVal`.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerT
public import LeanVM.Guest.B1.KeccakGkr.KFormMath

/-!
# `keccak_form`

The statements run three sums per column and a total over the lanes (`formEnt`, `formEnts`,
`formCols`), then the final loop (`formFin`). `formAll_holds`: with the lanes read at `lp`, the
total is `formVal` of the lane weights `f`, the lanes at `π`, and the shifts `sh`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

theorem addOpt_holds (o : Option ℕ) (v b : ℕ) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (addOpt o v b).1 next kret) :
    σ (.n (addOpt o v b).2.2) = ov σ o + σ (.n v) ∧ next := by
  cases o with
  | none => simp only [addOpt, Stmt.HoldsList] at h ⊢; exact ⟨by simp [ov], h⟩
  | some t =>
    simp only [addOpt, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h ⊢
    exact ⟨h.1, h.2⟩

/-- **One lane** of `keccak_form`. -/
theorem formEnt_holds {lp : V} {sh f : ℕ → ℕ} {lane b : ℕ} {st : FAcc} {lanes : List E}
    (hlanes : ReadsAt rd (σ lp) lanes) (hlen : lanes.length = 25) (hl : lane < 25)
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (formEnt lp sh f lane b st).1 next kret) :
    ov σ (formEnt lp sh f lane b st).2.2.tot = ov σ st.tot +
        σ (.n (f lane)) * (kLane lanes lane * σ (.n (sh (kRho lane)))) ∧
      ov σ (formEnt lp sh f lane b st).2.2.acc = ov σ st.acc +
        kLane lanes lane * σ (.n (sh (kRho lane))) ∧
      ov σ (formEnt lp sh f lane b st).2.2.accn = ov σ st.accn +
        kLane lanes lane * σ (.n (sh ((kRho lane + 1) % 64))) ∧
      ov σ (formEnt lp sh f lane b st).2.2.facc = ov σ st.facc + σ (.n (f lane)) ∧ next := by
  simp only [formEnt, holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨hld, e1, e2, h⟩ := h
  obtain ⟨r1, h⟩ := addOpt_holds _ _ _ h
  obtain ⟨r2, h⟩ := addOpt_holds _ _ _ h
  obtain ⟨enx, h⟩ := h
  obtain ⟨r3, h⟩ := addOpt_holds _ _ _ h
  obtain ⟨r4, hn⟩ := addOpt_holds _ _ _ h
  have hpi := keccakPi_lt lane hl
  have hlw : σ (.n b) = kLane lanes lane := by
    rw [kLane, List.getD_eq_getElem _ _ (by omega)]
    exact loadHolds_unique hld (hlanes _ (by omega))
  refine ⟨?_, ?_, ?_, ?_, hn⟩
  · show σ (.n _) = _
    rw [r1, e2, e1, hlw, kRho]
  · show σ (.n _) = _
    rw [r2, e1, hlw, kRho]
  · show σ (.n _) = _
    rw [r3, enx, hlw, kRho]
  · show σ (.n _) = _
    rw [r4]

theorem listSum_range (g : ℕ → E) : ∀ n, ((List.range n).map g).sum = ∑ i ∈ range n, g i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, listSum_range g n,
      Finset.sum_range_succ]; simp

theorem ov_of_isSome {o : Option ℕ} (h : o.isSome = true) : ov σ o = σ (.n (o.getD 0)) := by
  cases o with
  | none => simp at h
  | some v => rfl

theorem formEnts_isSome {lp : V} {sh f : ℕ → ℕ} {x : ℕ} :
    ∀ (ys : List ℕ) (b : ℕ) (st : FAcc), ys ≠ [] →
      (formEnts lp sh f x ys b st).2.2.tot.isSome = true ∧
      (formEnts lp sh f x ys b st).2.2.acc.isSome = true ∧
      (formEnts lp sh f x ys b st).2.2.accn.isSome = true ∧
      (formEnts lp sh f x ys b st).2.2.facc.isSome = true
  | [], _, _, h => absurd rfl h
  | [y], b, st, _ => by simp [formEnts, formEnt]
  | y :: y' :: ys, b, st, _ => formEnts_isSome (y' :: ys) _ _ (by simp)

/-- **A column's lanes.** -/
theorem formEnts_holds {lp : V} {sh f : ℕ → ℕ} {x : ℕ} {lanes : List E}
    (hlanes : ReadsAt rd (σ lp) lanes) (hlen : lanes.length = 25) :
    ∀ (ys : List ℕ) (b : ℕ) (st : FAcc), (∀ y ∈ ys, x + 5 * y < 25) → ∀ {next : Prop}
      {kret : List E → Prop}, Stmt.HoldsList C rd σ (formEnts lp sh f x ys b st).1 next kret →
      ov σ (formEnts lp sh f x ys b st).2.2.tot = ov σ st.tot + (ys.map fun y ↦
        σ (.n (f (x + 5 * y))) * (kLane lanes (x + 5 * y) * σ (.n (sh (kRho (x + 5 * y)))))).sum ∧
      ov σ (formEnts lp sh f x ys b st).2.2.acc = ov σ st.acc + (ys.map fun y ↦
        kLane lanes (x + 5 * y) * σ (.n (sh (kRho (x + 5 * y))))).sum ∧
      ov σ (formEnts lp sh f x ys b st).2.2.accn = ov σ st.accn + (ys.map fun y ↦
        kLane lanes (x + 5 * y) * σ (.n (sh ((kRho (x + 5 * y) + 1) % 64)))).sum ∧
      ov σ (formEnts lp sh f x ys b st).2.2.facc = ov σ st.facc + (ys.map fun y ↦
        σ (.n (f (x + 5 * y)))).sum ∧ next
  | [], b, st, _, next, kret, h => by simp only [formEnts, Stmt.HoldsList] at h ⊢; simp [h]
  | y :: ys, b, st, hy, next, kret, h => by
    simp only [formEnts, holdsList_append] at h ⊢
    obtain ⟨t1, a1, n1, f1, h⟩ := formEnt_holds hlanes hlen (hy y (by simp)) h
    obtain ⟨t2, a2, n2, f2, hn⟩ := formEnts_holds hlanes hlen ys _ _
      (fun y' hy' ↦ hy y' (by simp [hy'])) h
    refine ⟨?_, ?_, ?_, ?_, hn⟩
    · rw [t2, t1, List.map_cons, List.sum_cons, add_assoc]
    · rw [a2, a1, List.map_cons, List.sum_cons, add_assoc]
    · rw [n2, n1, List.map_cons, List.sum_cons, add_assoc]
    · rw [f2, f1, List.map_cons, List.sum_cons, add_assoc]

/-- `keccak_form`'s three sums of lane `l` (`M`, `N`, `F`). -/
def fM (lanes : List E) (σ : Val) (sh : ℕ → ℕ) (l : ℕ) : E := kLane lanes l * σ (.n (sh (kRho l)))
def fN (lanes : List E) (σ : Val) (sh : ℕ → ℕ) (l : ℕ) : E :=
  kLane lanes l * σ (.n (sh ((kRho l + 1) % 64)))

/-- **The columns.** -/
theorem formCols_holds {lp : V} {sh f : ℕ → ℕ} {lanes : List E}
    (hlanes : ReadsAt rd (σ lp) lanes) (hlen : lanes.length = 25) :
    ∀ (xs : List ℕ) (b : ℕ) (tot : Option ℕ), (∀ x ∈ xs, x < 5) → ∀ {next : Prop}
      {kret : List E → Prop}, Stmt.HoldsList C rd σ (formCols lp sh f xs b tot).1 next kret →
      ov σ (formCols lp sh f xs b tot).2.2.1 = ov σ tot + (xs.map fun x ↦ ([0, 1, 2, 3, 4].map
        fun y ↦ σ (.n (f (x + 5 * y))) * fM lanes σ sh (x + 5 * y)).sum).sum ∧
      (formCols lp sh f xs b tot).2.2.2.length = xs.length ∧
      (∀ i (hi : i < xs.length),
        σ (.n ((formCols lp sh f xs b tot).2.2.2.getD i default).1) =
          ([0, 1, 2, 3, 4].map fun y ↦ fM lanes σ sh (xs[i] + 5 * y)).sum ∧
        σ (.n ((formCols lp sh f xs b tot).2.2.2.getD i default).2.1) =
          ([0, 1, 2, 3, 4].map fun y ↦ fN lanes σ sh (xs[i] + 5 * y)).sum ∧
        σ (.n ((formCols lp sh f xs b tot).2.2.2.getD i default).2.2) =
          ([0, 1, 2, 3, 4].map fun y ↦ σ (.n (f (xs[i] + 5 * y)))).sum) ∧ next
  | [], b, tot, _, next, kret, h => by
    simp only [formCols, Stmt.HoldsList] at h ⊢
    simp [h]
  | x :: xs, b, tot, hx, next, kret, h => by
    have hx5 : x < 5 := hx x (by simp)
    simp only [formCols, holdsList_append] at h
    obtain ⟨t1, a1, n1, f1, h⟩ := formEnts_holds (x := x) hlanes hlen [0, 1, 2, 3, 4] b
      ⟨tot, none, none, none⟩ (fun y hy ↦ by simp at hy; omega) h
    obtain ⟨-, sa, sn, sf⟩ := formEnts_isSome (lp := lp) (sh := sh) (f := f) (x := x)
      [0, 1, 2, 3, 4] b ⟨tot, none, none, none⟩ (by simp)
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
    obtain ⟨c0, c1, c2, h⟩ := h
    obtain ⟨tr, hlenr, hcr, hn⟩ := formCols_holds hlanes hlen xs _ _
      (fun x' hx' ↦ hx x' (by simp [hx'])) h
    have hov0 : ov σ none = 0 := rfl
    simp only [hov0, zero_add] at a1 n1 f1
    rw [ov_of_isSome sa] at a1
    rw [ov_of_isSome sn] at n1
    rw [ov_of_isSome sf] at f1
    refine ⟨?_, ?_, fun i hi ↦ ?_, hn⟩
    · simp only [formCols]
      rw [tr, t1, List.map_cons, List.sum_cons, add_assoc]
      rfl
    · simp only [formCols, List.length_cons, hlenr]
    · rcases i with _ | i
      · simp only [formCols, List.getD_cons_zero, List.getElem_cons_zero]
        refine ⟨?_, ?_, ?_⟩
        · rw [c0, a1]; rfl
        · rw [c1, n1]; rfl
        · rw [c2, f1]
      · simp only [formCols, List.getD_cons_succ, List.getElem_cons_succ]
        exact hcr i (by simpa using hi)

/-- **The final loop.** -/
theorem formFin_holds (cols : List (ℕ × ℕ × ℕ)) :
    ∀ (xs : List ℕ) (b tot : ℕ) {next : Prop} {kret : List E → Prop},
      Stmt.HoldsList C rd σ (formFin cols xs b tot).1 next kret →
      σ (.n (formFin cols xs b tot).2.2) = σ (.n tot) + (xs.map fun x ↦
        σ (.n (cols.getD x default).2.2) * (σ (.n (cols.getD ((x + 1) % 5) default).1) +
          σ (.n (cols.getD ((x + 4) % 5) default).2.1))).sum ∧ next
  | [], b, tot, next, kret, h => by
    simp only [formFin, Stmt.HoldsList] at h ⊢
    simp [h]
  | x :: xs, b, tot, next, kret, h => by
    simp only [formFin, holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h ⊢
    obtain ⟨e0, e1, e2, h⟩ := h
    obtain ⟨ih, hn⟩ := formFin_holds cols xs _ _ h
    refine ⟨?_, hn⟩
    rw [ih, e2, e1, e0, List.map_cons, List.sum_cons, add_assoc]

theorem sum5 (g : ℕ → E) : ([0, 1, 2, 3, 4].map g).sum = ∑ i ∈ range 5, g i := listSum_range g 5

theorem formCols_isSome {lp : V} {sh f : ℕ → ℕ} :
    ∀ (xs : List ℕ) (b : ℕ) (tot : Option ℕ), xs ≠ [] →
      (formCols lp sh f xs b tot).2.2.1.isSome = true
  | [], _, _, h => absurd rfl h
  | [x], b, tot, _ => by
    simp only [formCols]
    exact (formEnts_isSome [0, 1, 2, 3, 4] b _ (by simp)).1
  | x :: x' :: xs, b, tot, _ => by
    simp only [formCols]
    exact formCols_isSome (x' :: xs) _ _ (by simp)

theorem sum_xy (G : ℕ → E) : ∑ x ∈ range 5, ∑ y ∈ range 5, G (x + 5 * y) = ∑ l ∈ range 25, G l := by
  rw [show (25 : ℕ) = 5 * 5 from rfl, sum_range_mul, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
  rw [add_comm]

/-- **`keccak_form`**: the total is `formVal` of the lane weights, the lanes at `π`
and the shifts. -/
theorem formAll_holds {lp : V} {sh f : ℕ → ℕ} {B : ℕ} {lanes : List E}
    (hlanes : ReadsAt rd (σ lp) lanes) (hlen : lanes.length = 25) {next : Prop}
    {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (formAll lp sh f B).1 next kret) :
    σ (.n (formAll lp sh f B).2.2) =
      formVal (fun l ↦ σ (.n (f l))) (kLane lanes) (fun r ↦ σ (.n (sh r))) ∧ next := by
  simp only [formAll, holdsList_append] at h ⊢
  obtain ⟨tc, -, hcols, h⟩ := formCols_holds (sh := sh) (f := f) hlanes hlen [0, 1, 2, 3, 4] B
    none (fun x hx ↦ by simp at hx; omega) h
  obtain ⟨tf, hn⟩ := formFin_holds _ _ _ _ h
  refine ⟨?_, hn⟩
  rw [tf, ← ov_of_isSome (σ := σ) (formCols_isSome (lp := lp) (sh := sh) (f := f) [0, 1, 2, 3, 4] B none
    (by simp)), tc, formVal]
  have hov0 : ov σ none = 0 := rfl
  rw [hov0, zero_add, sum5, sum5]
  refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun x hx ↦ ?_)
  · rw [← sum_xy]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [sum5]
    rfl
  · have hx5 := Finset.mem_range.1 hx
    obtain ⟨-, -, e2⟩ := hcols x (by simpa using hx5)
    obtain ⟨e1, -, -⟩ := hcols ((x + 1) % 5) (by simp; omega)
    obtain ⟨-, e3, -⟩ := hcols ((x + 4) % 5) (by simp; omega)
    rw [e1, e2, e3]
    have hg : ∀ k (hk : k < [0, 1, 2, 3, 4].length), [0, 1, 2, 3, 4][k] = k := by
      intro k hk; simp at hk; interval_cases k <;> rfl
    rw [hg _ (by simpa using hx5), hg _ (by simp; omega), hg _ (by simp; omega), sum5, sum5, sum5]
    rfl

end
end LeanVM.Guest.B1.VerifySub
