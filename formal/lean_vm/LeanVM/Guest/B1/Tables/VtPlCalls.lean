/-
  LeanVM.Guest.B1.Tables.VtPlCalls

  `verify_tables`' placed form: its dispatches, its frames against `vtKids`.
-/

module

public import LeanVM.Guest.B1.Tables.VtPlLoads

/-!
# The frames, placed

`verify_tables` sets up six dispatched padding weights and 69 loops (`vt_calls`); each matches
its `vtKids` entry: a padding weight at its table's log-height `g^τ` on its row count and the
bus point, returning its weight; a selector on its block's `g^κ` and the buffers; the two index
chains, `__loop79` and `__loop80` on the sum-check's buffers.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

theorem vt_callsMatch_append {σ : Val} : ∀ (cs1 cs2 : List Call) (ks1 ks2 : List Kid)
    (o1 o2 : List (List E × Main.Layout)), CallsMatch σ cs1 ks1 o1 → CallsMatch σ cs2 ks2 o2 →
    CallsMatch σ (cs1 ++ cs2) (ks1 ++ ks2) (o1 ++ o2)
  | [], _, [], _, [], _, _, h => h
  | _ :: cs1, cs2, _ :: ks1, ks2, _ :: o1, o2, ⟨a, b, c, h⟩, h2 =>
      ⟨a, b, c, vt_callsMatch_append cs1 cs2 ks1 ks2 o1 o2 h h2⟩
  | [], _, _ :: _, _, _, _, h, _ => h.elim
  | _ :: _, _, [], _, _, _, h, _ => h.elim
  | [], _, [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, _ :: _, _, [], _, h, _ => h.elim

theorem vt_outsOk_append : ∀ (ks1 ks2 : List Kid) (outs : List (List E × Main.Layout)),
    OutsOk (ks1 ++ ks2) outs → ∃ o1 o2, outs = o1 ++ o2 ∧ OutsOk ks1 o1 ∧ OutsOk ks2 o2
  | [], _, outs, h => ⟨[], outs, rfl, trivial, h⟩
  | _ :: ks1, ks2, o :: outs, ⟨h1, h⟩ =>
    let ⟨o1, o2, he, h1', h2'⟩ := vt_outsOk_append ks1 ks2 outs h
    ⟨o :: o1, o2, by rw [he]; rfl, ⟨h1, h1'⟩, h2'⟩
  | _ :: _, _, [], h => h.elim

/-- A frame matching its callee, given the callee's result. -/
def CallOk (σ : Val) (c : Call) (k : Kid) (o : List E × Main.Layout) : Prop :=
  c.f = k.f ∧ c.taken = k.taken ∧ (k.taken = true → c.args.map σ = k.args ∧ c.rets.map σ = o.1)

theorem vt_callsMatch_map {α : Type} {σ : Val} (f : α → Call) (g : α → Kid) :
    ∀ (l : List α) (outs : List (List E × Main.Layout)), OutsOk (l.map g) outs →
      (∀ a ∈ l, ∀ o : List E × Main.Layout, ((g a).taken = true → (g a).Out o.1 o.2) → CallOk σ (f a) (g a) o) →
      CallsMatch σ (l.map f) (l.map g) outs
  | [], [], _, _ => trivial
  | a :: l, o :: os, ⟨ho, hos⟩, h => by
    obtain ⟨h1, h2, h3⟩ := h a (by simp) o ho
    exact ⟨h1, h2, h3, vt_callsMatch_map f g l os hos fun a' ha' => h a' (by simp [ha'])⟩
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

theorem vt_callsMatch_one {σ : Val} {c : Call} {k : Kid} :
    ∀ (outs : List (List E × Main.Layout)), OutsOk [k] outs →
      (∀ o : List E × Main.Layout, (k.taken = true → k.Out o.1 o.2) → CallOk σ c k o) →
      CallsMatch σ [c] [k] outs
  | [o], ⟨ho, _⟩, h => ⟨(h o ho).1, (h o ho).2.1, (h o ho).2.2, trivial⟩
  | [], h, _ => h.elim
  | _ :: _ :: _, ⟨_, h⟩, _ => h.elim

theorem one_add_gen_pow_dec' {k : ℕ} (hk : k < 2 ^ 63) :
    decide (1 + gen ^ k ≠ 0) = decide (k ≠ 0) := by
  rw [decide_eq_decide]
  constructor
  · intro h h0; exact h (by rw [h0, pow_zero]; exact e_add_self 1)
  · intro h h0
    have h1 : gen ^ k = gen ^ 0 := by rw [pow_zero]; exact (e_add_eq_zero_iff.mp h0).symm
    exact h (gen_pow_inj (by omega) (by norm_num) h1)

/-! ## The frames -/

/-- Selector `i`'s frame. -/
def vtSelCall (i : ℕ) : Option V × String × List V × List V :=
  (some (.n (selVal.getD i 0 + 20)), selNames.getD i "",
    [.n (selVal.getD i 0 + 21), .n (selVal.getD i 0 + 5), .n (selVal.getD i 0 + 14),
      .n (selVal.getD i 0 + 15), .n (selVal.getD i 0 + 10), .n (selVal.getD i 0 + 16), .n 10,
      .n (selVal.getD i 0)], [])

/-- The loops' frames. -/
def vtRestCalls : List (Option V × String × List V × List V) :=
  [vtSelCall 0, vtSelCall 1, (some (.n 1928), "__loop14", [.n 1929, .n 1893, .n 1925, .n 5, .n 1817], []),
    vtSelCall 2, (some (.n 2032), "__loop16", [.n 2033, .n 1997, .n 2029, .n 5, .n 1817], [])] ++
  (List.range 62).map (fun i => vtSelCall (i + 3)) ++
  [(some (.n 4644), "__loop79", [.n 4645, .n 4554, .n 4636, .n 15, .n 4554, .n 4639], []),
    (some (.n 4658), "__loop80", [.n 4659, .n 4554, .n 4655, .n 5, .n 15], [])]

/-- Table `t`'s padding weight's frame. -/
noncomputable def vtPadCall (σ : Val) (t : ℕ) : Option V × String × List V × List V :=
  (none, pwNames.getD (logG (σ (.n (1733 + 14 * t)))) "", [.n (1733 + 14 * t + 5), .n 5],
    [.n (1733 + 14 * t + 6), .n (1733 + 14 * t + 7), .n (1733 + 14 * t + 8)])

set_option maxRecDepth 100000 in
theorem vt_pre_split : vtPre = vtPre.take 1439 ++ ((List.range 6).flatMap vtPad ++ vtPre.drop 1505) := by
  have h1 : (vtPre.drop 1439).take 66 = (List.range 6).flatMap vtPad :=
    (stmtsEqb_sound (by decide +kernel)).symm
  rw [← h1, show vtPre.drop 1505 = (vtPre.drop 1439).drop 66 by rw [List.drop_drop],
    List.take_append_drop, List.take_append_drop]

set_option maxRecDepth 100000 in
theorem vt_pre_lo : (vtPre.take 1439).all (fun s => (Stmt.dispX s).isNone) = true ∧
    (vtPre.take 1439).filterMap Main.Stmt.callS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem vt_pre_hi : (vtPre.drop 1505).all (fun s => (Stmt.dispX s).isNone) = true ∧
    (vtPre.drop 1505).filterMap Main.Stmt.callS = vtRestCalls := by decide +kernel

theorem vtPad_calls (σ : Val) (t : ℕ) : (vtPad t).filterMap (Stmt.callSF σ) = [vtPadCall σ t] := rfl

theorem vtPad_disp (t : ℕ) : (vtPad t).filterMap Stmt.dispX = [(.n (1733 + 14 * t), pwNames)] := rfl

theorem vtPads_calls (σ : Val) : ∀ m, ((List.range m).flatMap vtPad).filterMap (Stmt.callSF σ) =
    (List.range m).map (vtPadCall σ)
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.flatMap_append, List.filterMap_append, vtPads_calls σ m, List.map_append]
    simp [vtPad_calls]

/-- **`verify_tables`' frames.** -/
theorem vt_calls (σ : Val) :
    vtPre.filterMap (Stmt.callSF σ) = (List.range 6).map (vtPadCall σ) ++ vtRestCalls := by
  rw [vt_pre_split, List.filterMap_append, List.filterMap_append, callSF_nodisp σ _ vt_pre_lo.1,
    vt_pre_lo.2, callSF_nodisp σ _ vt_pre_hi.1, vt_pre_hi.2, vtPads_calls, List.nil_append]

theorem vt_disps : vtPre.filterMap Stmt.dispX = (List.range 6).map fun t => (.n (1733 + 14 * t), pwNames) := by
  rw [vt_pre_split, List.filterMap_append, List.filterMap_append]
  have h1 : (vtPre.take 1439).filterMap Stmt.dispX = [] := by
    have := vt_pre_lo.1
    rw [List.filterMap_eq_nil_iff]
    intro s hs
    simpa using List.all_eq_true.mp this s hs
  have h2 : (vtPre.drop 1505).filterMap Stmt.dispX = [] := by
    have := vt_pre_hi.1
    rw [List.filterMap_eq_nil_iff]
    intro s hs
    simpa using List.all_eq_true.mp this s hs
  rw [h1, h2, List.nil_append, List.append_nil]
  have : ∀ m, ((List.range m).flatMap vtPad).filterMap Stmt.dispX =
      (List.range m).map fun t => (.n (1733 + 14 * t), pwNames) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ, List.flatMap_append, List.filterMap_append, ih, List.map_append]
      simp [vtPad_disp]
  exact this 6

end
end LeanVM.Guest.B1.VerifySub
