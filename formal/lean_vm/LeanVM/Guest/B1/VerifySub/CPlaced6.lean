/-
  LeanVM.Guest.B1.VerifySub.CPlaced6

  `verify_sub` placed: the path's frames match its callees, batch by batch.
-/

module

public import LeanVM.Guest.B1.VerifySub.CPlaced5

/-!
# `verify_sub`'s frames match its callees

A frame's words among the honest calls (`vs_calls`) are the honest ones of its callee: each callee
but `g_power_of_word` and `assert_canonical` is called once, those two at arguments the valuation
fixes. `match1`, `matchOpen`, `matchTerm`: `CallsMatch` for the calls before the dispatch, the
opening and the terminal.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig

@[expose] public section

/-! ## Names -/

theorem ne_getD {s : String} (h : (openNames.all (· != s) && s != "") = true) (j : ℕ) :
    s ≠ openNames.getD j "" := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  intro he
  by_cases hl : j < openNames.length
  · rw [List.getD_eq_getElem _ _ hl] at he
    have := List.all_eq_true.mp h.1 _ (List.getElem_mem hl)
    rw [← he] at this
    simp at this
  · rw [List.getD_eq_default _ _ (by omega)] at he
    exact h.2 he

theorem lit_ne_open {s : String} {μ r : ℕ} (h : (openNames.all (· != s) && s != "") = true) :
    (s = openName μ r) = False := eq_false (ne_getD h _)

theorem open_ne_lit {s : String} {μ r : ℕ} (h : (openNames.all (· != s) && s != "") = true) :
    (openName μ r = s) = False := eq_false fun e => ne_getD h _ e.symm

theorem getD_ne_lit {s : String} {j : ℕ} (h : (openNames.all (· != s) && s != "") = true) :
    (openNames.getD j "" = s) = False := eq_false fun e => ne_getD h _ e.symm

/-- Read a call's words off the honest calls. -/
macro "vs_dec" h:ident : tactic => `(tactic| simp (config := { decide := true })
  [vsTriples, lit_ne_open, open_ne_lit, getD_ne_lit] at $h:ident)

/-! ## The calls before the dispatch -/

variable {fs : String → ℕ} {cert : String → V → ℕ} {bytecode : List K} {D : VsData}
  {fp lpA sqA outA : ℕ} {off kap pt : E}

theorem list12 {α : Type} {l : List α} (h : l.length = 12) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11, l = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] := by
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8,
    _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, l⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at h
  subst h
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- **The calls before the dispatch match their callees.** -/
theorem match1 (hok : D.Ok bytecode) {σ : Val}
    (hfix : Fixes σ (vsG11 D (vsPtrsAt fs fp D off kap pt) (ofK (Parameters.gpow lpA))
      (ofK (Parameters.gpow sqA)) (ofK (Parameters.gpow outA))))
    (hT : ∀ c ∈ (vsPre1.filterMap Main.Stmt.callS).map (Main.mkCall σ), c.taken = true →
      (c.f, c.args.map σ, c.rets.map σ) ∈ vsTriples bytecode D (vsPtrsAt fs fp D off kap pt)
        (ofK (Parameters.gpow lpA)) (ofK (Parameters.gpow sqA)))
    {outs : List (List E × Main.Layout)} (ho : OutsOk (vsKids1 fs D fp lpA sqA outA) outs)
    (hpl : (outs.getD 10 ([], [])).1 = [gen ^ D.stackTot, off, kap]) :
    CallsMatch σ ((vsPre1.filterMap Main.Stmt.callS).map (Main.mkCall σ))
      (vsKids1 fs D fp lpA sqA outA) outs := by
  obtain ⟨o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, rfl⟩ :=
    list12 (ho.length.trans (by simp [vsKids1]))
  simp only [OutsOk, vsKids1, Returns, forall_const] at ho
  obtain ⟨⟨r0, -⟩, ⟨r1, -⟩, ⟨r2, -⟩, ⟨r3, -⟩, ⟨r4, -⟩, ⟨r5, -⟩, ⟨r6, -⟩, ⟨r7, -⟩, ⟨r8, -⟩, h9, -,
    ⟨r11, -⟩, -⟩ := ho
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hpl
  rw [vsPre1_calls] at hT ⊢
  simp only [List.map_cons, List.map_nil, Main.mkCall, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, forall_const] at hT
  simp only [List.map_cons, List.map_nil, Main.mkCall, CallsMatch, vsKids1]
  have e121 : σ (.n 121) = eOfNat D.rate := hfix.get (by vs_mem)
  have e15 : σ (.n 15) = eOfNat D.logMem := hfix.get (by vs_mem)
  have e5 : σ (.n 5) = ofK (Parameters.gpow sqA) := hfix.get (by vs_mem)
  have e419 : σ (.n 419) = D.x0 := hfix.get (by vs_mem)
  have e434 : σ (.n 434) = D.x1 := hfix.get (by vs_mem)
  have e1160 : σ (.n 1160) = word 1 0 0 + gen ^ D.tau := hfix.get (by vs_mem)
  have hne : (eOfNat D.rate = eOfNat D.logMem) = False := eq_false fun h => by
    have := eOfNat_inj (by have := hok.rate_le; omega) (by have := hok.logMem_le; omega) h
    have := hok.rate_le; have := hok.logMem_ge; omega
  have hne' : (eOfNat D.logMem = eOfNat D.rate) = False := eq_false fun h => of_eq_false hne h.symm
  clear hfix
  rw [e121, e5] at hT
  rw [e15, e419, e434, e1160] at hT
  obtain ⟨hT0, hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8, hT9, hT10, hT11⟩ := hT
  vs_dec hT0; vs_dec hT1; vs_dec hT2; vs_dec hT3; vs_dec hT4; vs_dec hT5; vs_dec hT6; vs_dec hT7
  vs_dec hT8; vs_dec hT9; vs_dec hT10; vs_dec hT11
  simp only [hne, hne', false_and, or_false] at hT0 hT1
  replace hT3 : σ (.n 449) = 0 := Or.elim hT3 id And.right
  replace hT4 : σ (.n 450) = 0 := Or.elim hT4 And.right id
  simp only [vsPtrsAt, curG, curT, curF, curW] at *
  simp_all

/-- **The opening matches its callee.** -/
theorem matchOpen {σ : Val} {sel : ℕ}
    (hT : (openNames.getD sel "", [σ (.n 1171), σ (.n 1172), σ (.n 1627), σ (.n 419), σ (.n 434),
      σ (.n 726)], [σ (.n 1648), σ (.n 1649), σ (.n 1650), σ (.n 1651)]) ∈
        vsTriples bytecode D (vsPtrsAt fs fp D off kap pt) (ofK (Parameters.gpow lpA))
          (ofK (Parameters.gpow sqA)))
    {o : List E × Main.Layout} (hpt : o.1 = [D.w.target, pt, D.w.inner, D.w.residual]) :
    CallsMatch σ [⟨openNames.getD sel "", [.n 1171, .n 1172, .n 1627, .n 419, .n 434, .n 726],
      [.n 1648, .n 1649, .n 1650, .n 1651], true⟩] [vsOpenKid fs bytecode D fp lpA sqA outA] [o] := by
  vs_dec hT
  simp only [vsPtrsAt, curG, curT, curF, curW] at *
  simp only [CallsMatch, vsOpenKid, vsPtrsAt, curG, curT, curF, curW, List.map_cons, List.map_nil]
  simp_all

/-- **The terminal matches its callee.** -/
theorem matchTerm {σ : Val} {Lc Lo : Main.Layout}
    (hT : ("check_opening_terminal", [σ (.n 418), σ (.n 709), σ (.n 715), σ (.n 417), σ (.n 713),
      σ (.n 144), σ (.n 718), σ (.n 8), σ (.n 1180), σ (.n 1630), σ (.n 1631), σ (.n 734), σ (.n 733),
      σ (.n 1649), σ (.n 1650), σ (.n 1651), σ (.n 1648)], []) ∈
        vsTriples bytecode D (vsPtrsAt fs fp D off kap pt) (ofK (Parameters.gpow lpA))
          (ofK (Parameters.gpow sqA)))
    {o : List E × Main.Layout} (hr : o.1 = []) :
    CallsMatch σ [⟨"check_opening_terminal", [.n 418, .n 709, .n 715, .n 417, .n 713, .n 144, .n 718,
      .n 8, .n 1180, .n 1630, .n 1631, .n 734, .n 733, .n 1649, .n 1650, .n 1651, .n 1648], [], true⟩]
      [vsTermKid fs D fp lpA sqA outA off kap pt Lc Lo] [o] := by
  vs_dec hT
  simp only [vsPtrsAt] at *
  simp only [CallsMatch, vsTermKid, vsPtrsAt, List.map_cons, List.map_nil]
  simp_all

end
end LeanVM.Guest.B1.VerifySub
