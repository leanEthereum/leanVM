/-
  LeanVM.Guest.B1.RowWeights

  B1 for `opening_row_weights`: the equality kernel of the fold challenges, at both
  specializations, one generic argument.
-/

module

public import LeanVM.Guest.B1.EqWeight

/-!
# `opening_row_weights` (TRIAGE #34)

`opening_row_weights(point, out, folds, reverse)` (G:952-959) stores, for `i < 2^folds`, the
`eq_weight` of the slot `i` (or `2^folds - 1 - i` when `reverse = 1`) over `point`: entry
`slot i` of `eqKernel point` (V:676). Its expansion is one `eqWeightT` block and a store per
`i`, threaded through `orwGo`, equal to both specializations (`__L4_L0`, `__L6_L1`) by kernel
evaluation.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The slot of row `i`. -/
def orwSlot (folds rev i : ℕ) : ℕ := if rev = 1 then 2 ^ folds - 1 - i else i

/-- Rows `i .. i + n - 1` from the value `b`. -/
def orwGo (folds rev : ℕ) : ℕ → ℕ → ℕ → List Stmt
  | _, 0, _ => [.ret []]
  | i, n + 1, b =>
    (eqWeightT (.n 0) folds (orwSlot folds rev i) 0 b).1 ++
      [.atom (.load ((eqWeightT (.n 0) folds (orwSlot folds rev i) 0 b).2.2.getD (.n 0)) (.n 1) i)] ++
      orwGo folds rev (i + 1) n (eqWeightT (.n 0) folds (orwSlot folds rev i) 0 b).2.1

theorem core582_body : Fn.body Data.core582 = orwGo 4 0 0 (2 ^ 4) 2 :=
  stmtsEqb_sound (by decide +kernel)

theorem core578_body : Fn.body Data.core578 = orwGo 6 1 0 (2 ^ 6) 2 :=
  stmtsEqb_sound (by decide +kernel)

/-! ## The rows -/

/-- The first value of row `i + k`. -/
def orwStart (folds rev : ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, b, 0 => b
  | i, b, k + 1 => orwStart folds rev (i + 1) (eqWeightT (.n 0) folds (orwSlot folds rev i) 0 b).2.1 k

/-- What row `i` from the value `b` asks. -/
def RowOk (rd : Reader) (σ : Val) (folds rev i b : ℕ) : Prop :=
  EwOk rd σ (.n 0) (ewBit (orwSlot folds rev i) 0) 0 folds b none ∧
    LoadHolds rd (σ (.n 1)) i (σ ((eqWeightT (.n 0) folds (orwSlot folds rev i) 0 b).2.2.getD (.n 0)))

theorem holds_orwGo {C : CallRel} {rd : Reader} {σ : Val} (folds rev : ℕ) (rets : List E) :
    ∀ n i b, Stmt.HoldsList C rd σ (orwGo folds rev i n b) False (fun rs => rs = rets) ↔
      (∀ k < n, RowOk rd σ folds rev (i + k) (orwStart folds rev i b k)) ∧ rets = []
  | 0, _, _ => by simp [orwGo, Stmt.HoldsList, Stmt.Holds, eq_comm]
  | n + 1, i, b => by
    rw [orwGo, holdsList_append, holdsList_append, eqWeightT, holds_ewGo, ← eqWeightT,
      holds_orwGo folds rev rets n (i + 1)]
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
    constructor
    · rintro ⟨hew, hst, hall, hr⟩
      refine ⟨fun k hk => ?_, hr⟩
      cases k with
      | zero => exact ⟨hew, hst⟩
      | succ k =>
        have := hall k (by omega)
        rwa [show i + 1 + k = i + (k + 1) by omega] at this
    · rintro ⟨hall, hr⟩
      obtain ⟨hew, hst⟩ := hall 0 (by omega)
      refine ⟨hew, hst, fun k hk => ?_, hr⟩
      have := hall (k + 1) (by omega)
      rwa [show i + (k + 1) = i + 1 + k by omega] at this

/-! ## The meaning -/

/-- **`opening_row_weights(point, out, folds, reverse)`** (G:952-959; TRIAGE #34): the `folds`
words at `point` are `rs`, and row `i < 2^folds` of `out` is entry `slot i` of `eqKernel rs`
(V:676), the slot reversed at `reverse = 1`. -/
def MeaningOpeningRowWeights (folds rev : ℕ) (rd : Reader) : List E → List E → Prop
  | [point, out], rets =>
      rets = [] ∧ ∃ rs : List E, rs.length = folds ∧ ReadsAt rd point rs ∧
        ∀ i < 2 ^ folds, LoadHolds rd out i ((eqKernel rs).getD (orwSlot folds rev i) 0)
  | _, _ => False

theorem orwSlot_lt (folds rev i : ℕ) (hi : i < 2 ^ folds) : orwSlot folds rev i < 2 ^ folds := by
  unfold orwSlot; split <;> omega

/-- Row `i`'s product over the words `r`, the entry of the kernel. -/
theorem row_value {rd : Reader} {σ : Val} {folds rev i b : ℕ} (hf : 0 < folds) {rs : List E}
    (hrs : rs.length = folds) (hi : i < 2 ^ folds)
    (hl : ∀ c < folds, LoadHolds rd (σ (.n 0)) c (rs.getD c 0))
    (hew : EwOk rd σ (.n 0) (ewBit (orwSlot folds rev i) 0) 0 folds b none) :
    σ ((eqWeightT (.n 0) folds (orwSlot folds rev i) 0 b).2.2.getD (.n 0)) =
      (eqKernel rs).getD (orwSlot folds rev i) 0 := by
  have hv := ewOk_value (.n 0) (ewBit (orwSlot folds rev i) 0) (fun c => rs.getD c 0) folds 0 b
    none (fun k hk => by simpa using hl k hk) hew
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp
    (ewGo_isSome (.n 0) (ewBit (orwSlot folds rev i) 0) folds 0 b none hf)
  rw [eqWeightT, hres, Option.getD_some]
  rw [hres] at hv
  rw [eqKernel_getD rs _ (by rw [hrs]; exact orwSlot_lt folds rev i hi), hrs]
  simpa [wvOf, ewBit] using hv

/-- The honest value at `k` of rows `i ..` from the value `b`, over the words `r`. -/
def orwEval (r : ℕ → E) (folds rev : ℕ) : ℕ → ℕ → ℕ → ℕ → E
  | _, 0, _, _ => 0
  | i, n + 1, b, k =>
    if k < ewEnd (ewBit (orwSlot folds rev i) 0) 0 folds b false then
      ewEval r (ewBit (orwSlot folds rev i) 0) 0 folds b none k
    else orwEval r folds rev (i + 1) n (ewEnd (ewBit (orwSlot folds rev i) 0) 0 folds b false) k

theorem eqWeightT_next (folds idx b : ℕ) :
    (eqWeightT (.n 0) folds idx 0 b).2.1 = ewEnd (ewBit idx 0) 0 folds b false :=
  ewGo_next _ _ _ _ _ _

theorem orw_complete {rd : Reader} {σ : Val} {folds rev : ℕ} (hf : 0 < folds) {rs : List E}
    (hrs : rs.length = folds) (hl : ∀ c < folds, LoadHolds rd (σ (.n 0)) c (rs.getD c 0))
    (hout : ∀ i < 2 ^ folds, LoadHolds rd (σ (.n 1)) i ((eqKernel rs).getD (orwSlot folds rev i) 0)) :
    ∀ n i b, i + n ≤ 2 ^ folds →
      (∀ k, b ≤ k → σ (.n k) = orwEval (fun c => rs.getD c 0) folds rev i n b k) →
      ∀ k < n, RowOk rd σ folds rev (i + k) (orwStart folds rev i b k)
  | 0, _, _, _, _, k, hk => absurd hk (by omega)
  | n + 1, i, b, hn, hv, k, hk => by
    have hew : EwOk rd σ (.n 0) (ewBit (orwSlot folds rev i) 0) 0 folds b none :=
      ewOk_of_eval (.n 0) _ (fun c => rs.getD c 0) folds 0 b none none rfl (fun _ h => by simp at h)
        (fun c hc => by simpa using hl c hc) (fun k hk1 hk2 => by
          rw [hv k hk1, orwEval, ite_pos' (by simpa using hk2)])
    cases k with
    | zero =>
      simp only [Nat.add_zero, orwStart]
      exact ⟨hew, by rw [row_value hf hrs (by omega) hl hew]; exact hout i (by omega)⟩
    | succ k =>
      have := orw_complete hf hrs hl hout n (i + 1)
        (eqWeightT (.n 0) folds (orwSlot folds rev i) 0 b).2.1 (by omega) (fun k' hk' => by
        rw [eqWeightT_next] at hk'
        rw [hv k' (le_trans (le_ewEnd _ _ _ _ _) hk'), orwEval, ite_neg' (by omega), eqWeightT_next])
        k (by omega)
      rwa [show i + 1 + k = i + (k + 1) by omega] at this

/-- **`opening_row_weights` at `0 < folds`**, for a compiled function whose body is
`orwGo folds rev 0 (2^folds) 2`. -/
theorem opening_row_weights_iff {name : String} {f : Fn} (folds rev : ℕ) (hf : 0 < folds)
    (hfind : coreProgram.find? name = some f) (hparams : f.params = [.n 0, .n 1])
    (hbody : f.body = orwGo folds rev 0 (2 ^ folds) 2) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd name args rets ↔ MeaningOpeningRowWeights folds rev rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams]
  simp only [holds_orwGo, List.map_cons, List.map_nil, Nat.zero_add]
  constructor
  · rintro ⟨σ, hp, hrows, hret⟩
    subst hp
    obtain ⟨rs, hrs, hR⟩ := exists_list_of_forall (P := fun c v => LoadHolds rd (σ (.n 0)) c v)
      fun c hc => by simpa using ewOk_loads _ _ _ _ _ _ (hrows 0 (Nat.two_pow_pos _)).1 c hc
    have hl : ∀ c < folds, LoadHolds rd (σ (.n 0)) c (rs.getD c 0) := fun c hc => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact hR c (by omega)
    refine ⟨hret, rs, hrs, fun c hc => ?_, fun i hi => ?_⟩
    · have := hl c (by omega)
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some] at this
    · obtain ⟨hew, hst⟩ := hrows i hi
      rw [← row_value hf hrs hi hl hew]
      exact hst
  · intro hm
    obtain ⟨point, out, rfl⟩ : ∃ point out, args = [point, out] := by
      match args, hm with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    obtain ⟨rfl, rs, hrs, hR, hout⟩ := hm
    let τ : Val := fun v => if v.idx < 2 then [point, out].getD v.idx 0 else
      orwEval (fun c => rs.getD c 0) folds rev 0 (2 ^ folds) 2 v.idx
    have hl : ∀ c < folds, LoadHolds rd (τ (.n 0)) c (rs.getD c 0) := fun c hc => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact hR c (by omega)
    refine ⟨τ, rfl, fun k hk => ?_, rfl⟩
    have := orw_complete hf hrs hl hout (2 ^ folds) 0 2 (by omega) (fun k hk => by
      change (if k < 2 then _ else _) = _
      rw [ite_neg' (by omega)]) k hk
    rwa [Nat.zero_add] at this

set_option maxRecDepth 100000 in
theorem opening_row_weights_L4_L0_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_row_weights__L4_L0" args rets ↔
      MeaningOpeningRowWeights 4 0 rd args rets :=
  opening_row_weights_iff 4 0 (by decide) (Program.find?_of_indexOf? (j := 582) (by decide +kernel)
    rfl) rfl core582_body rd args rets

set_option maxRecDepth 100000 in
theorem opening_row_weights_L6_L1_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_row_weights__L6_L1" args rets ↔
      MeaningOpeningRowWeights 6 1 rd args rets :=
  opening_row_weights_iff 6 1 (by decide) (Program.find?_of_indexOf? (j := 578) (by decide +kernel)
    rfl) rfl core578_body rd args rets

end
end LeanVM.Guest.B1
