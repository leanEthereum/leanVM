/-
  LeanVM.Guest.EndExecRExp

  The families of a product's factors (`Res.expFamB`), sound at the honest frames.
-/

module

public import LeanVM.Guest.EndExecRF
public import LeanVM.Guest.Res.ExpDefs

/-!
# Runs bounded by a product's factors, sound

`kVal_top`, `pw0_top`, `pw_top`: the cells the checks name hold the powers of `g` they claim, read
through the frame's values of the witness's atoms (`TopAt.cell`); `eqX_top`: the cells hold one word;
`mulX_top`: the product. `expShift_top`, `expFac_top`, `expPt_top`: with `[p] = [u]·[v]`,
`[u] = g^eu`, `[v] = g^ev`, `[p]`'s exponent is `eu + ev` (no wrap: both below `2^40`), which bounds
the run's points.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (fsN cellJ namedOf)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (Wit witOk powOf powOf1 cellLt holdsBase inFr frEx kVal1 kVal pw0 pw mulAt eqX mulX
  expHi expShiftB expFacB expPtB expFamB)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

theorem powOf1_sound {c : E} {z : ℕ} (h : powOf1 c = some z) : c = ofK (Parameters.g ^ z) := by
  unfold powOf1 at h
  split_ifs at h with h1
  · obtain rfl := (Option.some.inj h).symm
    rw [eq_ofK_limb h1.1, h1.2, pow_zero]
  · exact powOf_sound h

section

variable {M : ℕ → E} {fp : ℕ}

/-- A product with a larger offset and the same bases: its word is the other's times `g^z`. -/
theorem rmono_k {a b : Mono} (hfp : a.fp = b.fp) (hbs : a.bs = b.bs) (hk : b.k ≤ a.k) {va vb : E}
    (ha : RMono M fp a va) (hb : RMono M fp b vb) : va = vb * ofK (Parameters.g ^ (a.k - b.k)) := by
  obtain ⟨w, hw, rfl⟩ := ha
  obtain ⟨w', hw', rfl⟩ := hb
  rw [hbs] at hw
  rw [rbs_uniq hw hw', hfp, show a.k = b.k + (a.k - b.k) by omega, pow_add, ofK_mul,
    show b.k + (a.k - b.k) - b.k = a.k - b.k by omega]
  ring

/-- **A run scaled by `g^ev`** inside the run up to an exponent `ec + ev` past it. -/
theorem rsub_scaled {a b : Rng} {ec ev : ℕ} (hal : a.lo = .num 0) (hbl : b.lo = .num 0) (haS : a.S = 1)
    (hbS : b.S = 1) (hd : a.d = b.d) (hah : RIdx M fp a.hi ec)
    (hq : ∀ vq vb, RMono M fp a.q vq → RMono M fp b.q vb → vq = vb * ofK (Parameters.g ^ ev))
    (hhi : ∀ y, RIdx M fp b.hi y → ec + ev ≤ y) : RSub M fp a [b] := by
  refine ⟨0, ec, by rw [hal]; rfl, hah, fun vq hvq jj _ hjj ↦
    ⟨b, List.mem_singleton_self _, fun vb ylo yhi hvb hlo hy ↦ ?_⟩⟩
  rw [hbl] at hlo
  have := hhi yhi hy
  refine ⟨ev + jj, by simp only [RIdx] at hlo; omega, by omega, ?_⟩
  rw [hq vq vb hvq hvb, haS, hbS, hd]
  simp only [one_mul, ofK_gpow]
  rw [show ev + jj + b.d = ev + (jj + b.d) by omega, pow_add]
  ring

end

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ} {w : Wit}

/-- A witness atom's cell holds its value. -/
theorem wit_cell (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {a : Atom} (ha : a ∈ w.as)
    {v : V} (hv : v ∈ atomUses a) (hin : inFr j (cellJ j v) = true) :
    refMem r.img (e.I.fp + cellJ j v) = e.σ v := by
  obtain ⟨vs, -, hF, -, hwa, -⟩ := t.wit hr hW
  simp only [inFr, Bool.and_eq_true, decide_eq_true_eq] at hin
  exact t.cell hr hF (namedOf_atom (hwa _ ha) hv) hin.1 hin.2

/-- A witness atom holds. -/
theorem wit_holds (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {a : Atom} (ha : a ∈ w.as) :
    a.Holds r.img.read e.σ := by
  obtain ⟨vs, -, -, hev, hwa, -⟩ := t.wit hr hW
  exact hev _ (hwa _ ha)

theorem kVal1_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {o z : ℕ}
    (h : kVal1 j w.as o = some z) :
    inFr j o = true ∧ refMem r.img (e.I.fp + o) = ofK (Parameters.g ^ z) := by
  unfold kVal1 at h
  obtain ⟨a, ha, hf⟩ := List.exists_of_findSome?_eq_some h
  cases a with
  | const d c =>
    simp only at hf
    split_ifs at hf with hd
    simp only [Bool.and_eq_true, beq_iff_eq] at hd
    obtain ⟨rfl, hin⟩ := hd
    refine ⟨hin, ?_⟩
    have hc : e.σ d = c := wit_holds t hr hW ha
    rw [wit_cell t hr hW ha (by simp [atomUses]) hin, hc, powOf1_sound hf]
  | _ => simp at hf

/-- **A constant cell** holds its `g^z`. -/
theorem kVal_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {o z : ℕ}
    (h : kVal j w.as o = some z) :
    inFr j o = true ∧ refMem r.img (e.I.fp + o) = ofK (Parameters.g ^ z) := by
  unfold kVal at h
  cases h1 : kVal1 j w.as o with
  | some z' =>
    rw [h1, Option.some_or] at h
    obtain rfl := Option.some.inj h
    exact kVal1_top t hr hW h1
  | none =>
    rw [h1, Option.none_or] at h
    obtain ⟨a, ha, hf⟩ := List.exists_of_findSome?_eq_some h
    cases a with
    | mul d x y =>
      simp only at hf
      split_ifs at hf with hd
      simp only [Bool.and_eq_true, beq_iff_eq] at hd
      obtain ⟨rfl, hin⟩ := hd
      obtain ⟨zx, hx, hf⟩ := Option.bind_eq_some_iff.mp hf
      obtain ⟨zy, hy, rfl⟩ := Option.map_eq_some_iff.mp hf
      obtain ⟨hix, ex⟩ := kVal1_top t hr hW hx
      obtain ⟨hiy, ey⟩ := kVal1_top t hr hW hy
      refine ⟨hin, ?_⟩
      have hm : e.σ d = e.σ x * e.σ y := wit_holds t hr hW ha
      rw [wit_cell t hr hW ha (by simp [atomUses]) hin, hm,
        ← wit_cell t hr hW ha (by simp [atomUses]) hix, ← wit_cell t hr hW ha (by simp [atomUses]) hiy,
        ex, ey, ← ofK_mul, ← pow_add]
    | _ => simp at hf

theorem pw0_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {o : ℕ} (h : pw0 j w o = true) :
    inFr j o = true ∧ ∃ x < 2 ^ 39, refMem r.img (e.I.fp + o) = ofK (Parameters.g ^ x) := by
  unfold pw0 at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · obtain ⟨h2, hlt⟩ := cellLt_bounds h
    exact ⟨by simp [inFr, h2, hlt], cellLt_top t hr hW h⟩
  · cases hk : kVal j w.as o with
    | none => rw [hk] at h; cases h
    | some z =>
      rw [hk] at h
      obtain ⟨hin, hv⟩ := kVal_top t hr hW hk
      exact ⟨hin, z, by simpa using h, hv⟩

/-- **A product of the witness's** at an honest frame. -/
theorem mulAt_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {m : Atom} (hm : m ∈ w.as)
    {P X Y : ℕ} (h : mulAt j m = some (P, X, Y)) :
    inFr j P = true ∧ inFr j X = true ∧ inFr j Y = true ∧
      refMem r.img (e.I.fp + P) = refMem r.img (e.I.fp + X) * refMem r.img (e.I.fp + Y) := by
  cases m with
  | mul d x y =>
    simp only [mulAt] at h
    split_ifs at h with hin
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [Bool.and_eq_true] at hin
    obtain ⟨⟨hd, hx⟩, hy⟩ := hin
    have hmh : e.σ d = e.σ x * e.σ y := wit_holds t hr hW hm
    refine ⟨hd, hx, hy, ?_⟩
    rw [wit_cell t hr hW hm (by simp [atomUses]) hd, wit_cell t hr hW hm (by simp [atomUses]) hx,
      wit_cell t hr hW hm (by simp [atomUses]) hy, hmh]
  | _ => simp [mulAt] at h

/-- **A cell `pw` takes** holds `g^x`, `x < 2^40`. -/
theorem pw_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {o : ℕ} (h : pw j w o = true) :
    inFr j o = true ∧ ∃ x < 2 ^ 40, refMem r.img (e.I.fp + o) = ofK (Parameters.g ^ x) := by
  unfold pw at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · obtain ⟨hin, x, hx, hv⟩ := pw0_top t hr hW h
    exact ⟨hin, x, by omega, hv⟩
  obtain ⟨hin, h⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨hin, ?_⟩
  obtain ⟨m, hm, h⟩ := List.any_eq_true.mp h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · cases m with
    | copy d s =>
      have hcs : e.σ d = e.σ s := wit_holds t hr hW hm
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨⟨rfl, his⟩, hp⟩ | ⟨⟨rfl, hid⟩, hp⟩
      · obtain ⟨-, x, hx, hv⟩ := pw0_top t hr hW hp
        refine ⟨x, by omega, ?_⟩
        rw [wit_cell t hr hW hm (by simp [atomUses]) hin, hcs,
          ← wit_cell t hr hW hm (by simp [atomUses]) his, hv]
      · obtain ⟨-, x, hx, hv⟩ := pw0_top t hr hW hp
        refine ⟨x, by omega, ?_⟩
        rw [wit_cell t hr hW hm (by simp [atomUses]) hin, ← hcs,
          ← wit_cell t hr hW hm (by simp [atomUses]) hid, hv]
    | _ => simp at h
  · cases hc : mulAt j m with
    | none => rw [hc] at h; cases h
    | some c =>
      obtain ⟨P, X, Y⟩ := c
      rw [hc] at h
      obtain ⟨-, -, -, hv⟩ := mulAt_top t hr hW hm hc
      simp only at h
      rcases Bool.or_eq_true_iff.mp h with h | h
      · simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨rfl, h1⟩, h2⟩ := h
        obtain ⟨-, x, hx, ex⟩ := pw0_top t hr hW h1
        obtain ⟨-, y, hy, ey⟩ := pw0_top t hr hW h2
        exact ⟨x + y, by omega, by rw [hv, ex, ey, ← ofK_mul, ← pow_add]⟩
      · obtain ⟨⟨hX, h1⟩, h2⟩ := Bool.and_eq_true_iff.mp h |>.imp_left Bool.and_eq_true_iff.mp
        simp only [beq_iff_eq] at hX
        subst hX
        obtain ⟨m', hm', h2⟩ := List.any_eq_true.mp h2
        cases hc' : mulAt j m' with
        | none => rw [hc'] at h2; cases h2
        | some c' =>
          obtain ⟨P', X', Y'⟩ := c'
          rw [hc'] at h2
          simp only [Bool.and_eq_true, beq_iff_eq] at h2
          obtain ⟨⟨rfl, rfl⟩, h3⟩ := h2
          obtain ⟨-, -, -, hv'⟩ := mulAt_top t hr hW hm' hc'
          obtain ⟨-, y, -, ey⟩ := pw0_top t hr hW h1
          obtain ⟨-, x, hx, ex⟩ := pw0_top t hr hW h3
          refine ⟨x, by omega, ?_⟩
          have hne : refMem r.img (e.I.fp + Y') ≠ 0 := by rw [ey]; exact Mode.ofK_gpow_ne_zero _
          rw [← ex]
          exact mul_right_cancel₀ hne (hv.symm.trans hv')

/-- **Cells `eqX` ties hold one word.** -/
theorem eqX_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {a b : ℕ} (h : eqX j w a b = true) :
    refMem r.img (e.I.fp + a) = refMem r.img (e.I.fp + b) := by
  unfold eqX at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rw [beq_iff_eq.mp h]
  obtain ⟨hab, h⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hab
  obtain ⟨m, hm, h⟩ := List.any_eq_true.mp h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · cases m with
    | copy d s =>
      have hcs : e.σ d = e.σ s := wit_holds t hr hW hm
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [wit_cell t hr hW hm (by simp [atomUses]) ha, wit_cell t hr hW hm (by simp [atomUses]) hb, hcs]
      · rw [wit_cell t hr hW hm (by simp [atomUses]) ha, wit_cell t hr hW hm (by simp [atomUses]) hb, hcs]
    | _ => simp at h
  · cases hc : mulAt j m with
    | none => rw [hc] at h; cases h
    | some c =>
      obtain ⟨P, X, Y⟩ := c
      rw [hc] at h
      obtain ⟨-, -, -, hv⟩ := mulAt_top t hr hW hm hc
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hk, h⟩ := h
      obtain ⟨-, h1⟩ := kVal_top t hr hW hk
      rw [h1, pow_zero, Value.ofK_one, mul_one] at hv
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hv
      · exact hv.symm

/-- **A product `mulX` takes.** -/
theorem mulX_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {okP okU okV : ℕ → Bool}
    (h : mulX j w okP okU okV = true) :
    ∃ P u v, okP P = true ∧ okU u = true ∧ okV v = true ∧
      refMem r.img (e.I.fp + P) = refMem r.img (e.I.fp + u) * refMem r.img (e.I.fp + v) := by
  obtain ⟨m, hm, h⟩ := List.any_eq_true.mp h
  cases hc : mulAt j m with
  | none => rw [hc] at h; cases h
  | some c =>
    obtain ⟨P, X, Y⟩ := c
    rw [hc] at h
    obtain ⟨-, -, -, hv⟩ := mulAt_top t hr hW hm hc
    simp only [Bool.and_eq_true, Bool.or_eq_true] at h
    rcases h with ⟨hP, ⟨hu, hv'⟩ | ⟨hu, hv'⟩⟩
    · exact ⟨P, X, Y, hP, hu, hv', hv⟩
    · exact ⟨P, Y, X, hP, hu, hv', by rw [hv, mul_comm]⟩

/-- **A run's bound `expHi` takes**: at least the exponent of the product it names. -/
theorem expHi_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {hi : Mode.Idx} {okP : ℕ → Bool}
    (hh : expHi j w hi = some okP) {P n : ℕ} (hP : okP P = true)
    (hv : refMem r.img (e.I.fp + P) = ofK (Parameters.g ^ n)) (hn : n < 2 ^ 62) {y : ℕ}
    (hy : RIdx (refMem r.img) e.I.fp hi y) : n ≤ y := by
  unfold expHi at hh
  split at hh
  · rename_i p
    obtain rfl := Option.some.inj hh
    obtain ⟨vp, ep, hvp, hvp', hep, hyy⟩ := hy
    change refMem r.img (e.I.fp + p) = vp at hvp
    have := ofK_gpow_inj (by omega) (by omega) (hv.symm.trans ((eqX_top t hr hW hP).trans (hvp.trans hvp')))
    omega
  · rename_i H
    obtain rfl := Option.some.inj hh
    change y = H at hy
    have hN : H + 1 ≤ 2 ^ 62 := by
      simp only [cellLt, Bool.and_eq_true, decide_eq_true_eq] at hP; exact hP.1.2
    obtain ⟨eP, heP, hvP⟩ := cellLt_top t hr hW hP
    rw [ofK_gpow_inj (by omega) (by omega) (hv.symm.trans hvP)]
    omega
  · cases hh

/-- **A run scaled by a factor** at an honest frame. -/
theorem expShift_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {x : Mode.Res}
    (hx : expShiftB j w x = true) : RRes (refMem r.img) e.I.fp x := by
  match x, hx with
  | .sub a [b], hx =>
    simp only [expShiftB] at hx
    cases hc : frEx a.hi with
    | none => simp [hc] at hx
    | some c =>
      cases hh : expHi j w b.hi with
      | none => simp [hc, hh] at hx
      | some okP =>
        rw [hc, hh] at hx
        have hah := frEx_eq hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hx
        obtain ⟨⟨⟨⟨⟨⟨⟨hal, hbl⟩, haS⟩, hbS⟩, hd⟩, hfp⟩, hpc⟩, hq⟩ := hx
        obtain ⟨-, ec, hec, hcv⟩ := pw_top t hr hW hpc
        have hahi : RIdx (refMem r.img) e.I.fp a.hi ec := by
          rw [hah]; exact ⟨_, ec, hcv, rfl, by omega, rfl⟩
        -- the product and its bound
        have fin : ∀ P u v ev, okP P = true → eqX j w u c = true → ev < 2 ^ 40 →
            refMem r.img (e.I.fp + P) = refMem r.img (e.I.fp + u) * refMem r.img (e.I.fp + v) →
            refMem r.img (e.I.fp + v) = ofK (Parameters.g ^ ev) →
            ∀ y, RIdx (refMem r.img) e.I.fp b.hi y → ec + ev ≤ y := by
          intro P u v ev hP hu hev hp hvv y hy
          refine expHi_top t hr hW hh hP ?_ (by omega) hy
          rw [hp, eqX_top t hr hW hu, hcv, hvv, ← ofK_mul, ← pow_add]
        rcases Bool.or_eq_true_iff.mp hq with hq | hq
        · obtain ⟨hk, hq⟩ := Bool.and_eq_true_iff.mp hq
          obtain ⟨⟨B, eB⟩, -, hB⟩ := List.any_eq_true.mp hq
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hB hk
          obtain ⟨⟨rfl, hbs⟩, hm⟩ := hB
          obtain ⟨P, u, v, hP, hu, hvB, hp⟩ := mulX_top t hr hW hm
          obtain ⟨hob, hopw⟩ := Bool.and_eq_true_iff.mp hvB
          obtain ⟨hin, ev, hev, hvv⟩ := pw_top t hr hW hopw
          simp only [inFr, Bool.and_eq_true, decide_eq_true_eq] at hin
          have hu' := holdsBase_top t hr hW hin.1 hin.2 hob
          exact rsub_scaled hal hbl haS hbS hd hahi
            (fun vq vb hvq hvb ↦ by rw [rmono_insert hfp hk hbs hu' hvq hvb, hvv])
            (fin P u v ev hP hu hev hp hvv)
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
          obtain ⟨⟨⟨hbs, hk⟩, hz⟩, hm⟩ := hq
          obtain ⟨P, u, v, hP, hu, hvk, hp⟩ := mulX_top t hr hW hm
          obtain ⟨-, hvv⟩ := kVal_top t hr hW (beq_iff_eq.mp hvk)
          exact rsub_scaled hal hbl haS hbS hd hahi
            (fun vq vb hvq hvb ↦ rmono_k hfp hbs hk hvq hvb)
            (fin P u v _ hP hu (by omega) hp hvv)
  | .sub _ [], hx => simp [expShiftB] at hx
  | .sub _ (_ :: _ :: _), hx => simp [expShiftB] at hx
  | .lt _ _, hx => simp [expShiftB] at hx
  | .nz _, hx => simp [expShiftB] at hx
  | .name _, hx => simp [expShiftB] at hx

/-- **A run up to a factor's exponent** at an honest frame. -/
theorem expFac_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {x : Mode.Res}
    (hx : expFacB j w x = true) : RRes (refMem r.img) e.I.fp x := by
  match x, hx with
  | .sub a [b], hx =>
    simp only [expFacB] at hx
    split at hx
    · rename_i X p l hah hbh hal
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
      obtain ⟨⟨⟨⟨hq, hlo⟩, hS⟩, hd⟩, hm⟩ := hx
      obtain ⟨P, u, v, hP, hu, hv, hp⟩ := mulX_top t hr hW hm
      obtain ⟨hob, hupw⟩ := Bool.and_eq_true_iff.mp hu
      obtain ⟨hin, ex, hex, hux⟩ := pw_top t hr hW hupw
      obtain ⟨-, ev, hev, hvv⟩ := pw_top t hr hW hv
      simp only [inFr, Bool.and_eq_true, decide_eq_true_eq] at hin
      have hB := holdsBase_top t hr hW hin.1 hin.2 hob
      refine ⟨l, ex, by rw [hal]; rfl, by rw [hah]; exact ⟨_, ex, hB, hux, by omega, rfl⟩,
        fun vq hvq jj hj1 hj2 ↦ ⟨b, List.mem_singleton_self _, fun vb ylo yhi hvb hylo hy ↦ ?_⟩⟩
      rw [← hlo, hal] at hylo
      change ylo = l at hylo
      rw [hbh] at hy
      obtain ⟨vp, ep, hvp, hvp', hep, hyy⟩ := hy
      change refMem r.img (e.I.fp + p) = vp at hvp
      have hpe : ofK (Parameters.g ^ (ex + ev)) = ofK (Parameters.g ^ ep) := by
        rw [pow_add, ofK_mul, ← hux, ← hvv, ← hp, eqX_top t hr hW hP, hvp, hvp']
      have := ofK_gpow_inj (by omega) (by omega) hpe
      refine ⟨jj, by omega, by omega, ?_⟩
      rw [hq] at hvq
      rw [rmono_uniq hvq hvb, hS, hd]
    · simp at hx
  | .sub _ [], hx => simp [expFacB] at hx
  | .sub _ (_ :: _ :: _), hx => simp [expFacB] at hx
  | .lt _ _, hx => simp [expFacB] at hx
  | .nz _, hx => simp [expFacB] at hx
  | .name _, hx => simp [expFacB] at hx

/-- **A point at a factor** at an honest frame. -/
theorem expPt_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {x : Mode.Res}
    (hx : expPtB j w x = true) : RRes (refMem r.img) e.I.fp x := by
  match x, hx with
  | .sub a [b], hx =>
    simp only [expPtB] at hx
    split at hx
    · rename_i p c hbh
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨hal, hah⟩, hbl⟩, hbS⟩, hd⟩, hc⟩, hfp⟩, hk⟩, hany⟩ := hx
      obtain ⟨⟨B, eB⟩, -, hB⟩ := List.any_eq_true.mp hany
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hB
      obtain ⟨⟨rfl, hbs⟩, hm⟩ := hB
      obtain ⟨P, u, v, hP, hu, hv, hp⟩ := mulX_top t hr hW hm
      obtain ⟨hob, hupw⟩ := Bool.and_eq_true_iff.mp hu
      obtain ⟨hin, ex, hex, hux⟩ := pw_top t hr hW hupw
      obtain ⟨-, ev, hev, hvv⟩ := pw_top t hr hW hv
      simp only [inFr, Bool.and_eq_true, decide_eq_true_eq] at hin
      have hB := holdsBase_top t hr hW hin.1 hin.2 hob
      refine ⟨0, 1, by rw [hal]; rfl, by rw [hah]; rfl,
        fun vq hvq jj hj1 hj2 ↦ ⟨b, List.mem_singleton_self _, fun vb ylo yhi hvb hylo hy ↦ ?_⟩⟩
      rw [hbl] at hylo
      change ylo = 0 at hylo
      rw [hbh] at hy
      obtain ⟨vp, ep, hvp, hvp', hep, hyy⟩ := hy
      change refMem r.img (e.I.fp + p) = vp at hvp
      have hpe : ofK (Parameters.g ^ (ex + ev)) = ofK (Parameters.g ^ ep) := by
        rw [pow_add, ofK_mul, ← hux, ← hvv, ← hp, eqX_top t hr hW hP, hvp, hvp']
      have := ofK_gpow_inj (by omega) (by omega) hpe
      have hj : jj = 0 := by change 0 ≤ jj at hj1; change jj < 1 at hj2; omega
      subst hj
      refine ⟨ex, by omega, by omega, ?_⟩
      rw [rmono_insert hfp hk hbs hB hvq hvb, hux, hbS, hd]
      simp only [mul_zero, zero_add, one_mul, ofK_gpow]
      rw [pow_add]
      ring
    · simp at hx
  | .sub _ [], hx => simp [expPtB] at hx
  | .sub _ (_ :: _ :: _), hx => simp [expPtB] at hx
  | .lt _ _, hx => simp [expPtB] at hx
  | .nz _, hx => simp [expPtB] at hx
  | .name _, hx => simp [expPtB] at hx

/-- **The families of a product's factors at an honest frame.** -/
theorem expFam_top (t : TopAt A r K i e j) (hr : r.Ok) (hW : witOk j w = true) {x : Mode.Res}
    (hx : expFamB j w x = true) : RRes (refMem r.img) e.I.fp x := by
  simp only [expFamB, Bool.or_eq_true] at hx
  rcases hx with (hx | hx) | hx
  · exact expShift_top t hr hW hx
  · exact expFac_top t hr hW hx
  · exact expPt_top t hr hW hx

end

end

end LeanVM.Guest.EndExec
