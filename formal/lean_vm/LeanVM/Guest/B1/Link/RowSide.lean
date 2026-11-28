/-
  LeanVM.Guest.B1.Link.RowSide

  B1 for `link_row_side` (chunk counts `6` to `9`): the row rounds, then the pointer-column rounds.
-/

module

public import LeanVM.Guest.B1.Link.RoundsMain
import LeanVM.Guest.CoreRef

/-!
# `link_row_side`

`link_row_side(fs0..fs4, cursor, claim, chi, q_point, g_n, tabs, d)` (G) runs `link_rounds` over
the rows (`n_rows = log g_n` rounds of `d + 1` tail coefficients, the challenges at `chi`), then
over the pointer columns (`LINK_Q_VARS = 6` rounds of `d`, at `q_point`), and returns the state
after them (`MeaningLRS`): two chains of rounds.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **`link_row_side`**: the rows' count `g^n`, `n < 64`; when the rounds grind, with `tabs` the
windows table, a chain of `n` row rounds then of `6` pointer-column rounds. -/
def MeaningLRS (nt1 b1 nt2 b2 : ℕ) (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, cur, cl, chi, qp, gn, tabs], rets => ∃ n < 64, gn = gen ^ n ∧
      ((b1 ≠ 0 ∨ b2 ≠ 0 → WinTabs rd tabs) → ∃ l1 l2 : List (E × RSt), l1.length = n ∧ l2.length = 6 ∧
        RoundChain rd nt1 b1 ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1 ∧
        RoundChain rd nt2 b2 (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1) l2 ∧
        ReadsAt rd chi (l1.map Prod.fst) ∧ ReadsAt rd qp (l2.map Prod.fst) ∧
        rets = (chainLast (chainLast ⟨[f0, f1, f2, f3, f4], cur, cl⟩ l1) l2).cells)
  | _, _ => False

/-- `link_row_side`'s body, its two `link_rounds` named. -/
def lrsBody (rows cols : String) : List Stmt :=
  [.call rows [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 9, .n 10]
      [.n 11, .n 12, .n 13, .n 14, .n 15, .n 16, .n 17],
    .atom (.const (.n 18) (word 64 0)),
    .call cols [.n 11, .n 12, .n 13, .n 14, .n 15, .n 16, .n 17, .n 8, .n 18, .n 10]
      [.n 19, .n 20, .n 21, .n 22, .n 23, .n 24, .n 25],
    .atom (.copy (.n 26) (.n 19)), .atom (.copy (.n 27) (.n 20)), .atom (.copy (.n 28) (.n 21)),
    .atom (.copy (.n 29) (.n 22)), .atom (.copy (.n 30) (.n 23)), .atom (.copy (.n 31) (.n 24)),
    .atom (.copy (.n 32) (.n 25)), .ret [.n 26, .n 27, .n 28, .n 29, .n 30, .n 31, .n 32]]

theorem cells_eq_seven {st : RSt} (h : st.cap.length = 5) :
    ∃ a b c d e u v, st.cells = [a, b, c, d, e, u, v] ∧ st = ⟨[a, b, c, d, e], u, v⟩ := by
  obtain ⟨cap, u, v⟩ := st
  match cap, h with
  | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, u, v, rfl, rfl⟩

/-- **The template's relation implies its meaning.** -/
theorem lrs_sound {rd : Reader} {nt1 b1 nt2 b2 : ℕ} {rows cols : String}
    (hrows : ∀ args rets, coreProgram.Rel rd rows args rets → MeaningLR nt1 b1 rd args rets)
    (hcols : ∀ args rets, coreProgram.Rel rd cols args rets → MeaningLR nt2 b2 rd args rets)
    {name : String} {f : Fn} (hfind : coreProgram.find? name = some f)
    (hparams : f.params = (List.range 11).map V.n) (hbody : f.body = lrsBody rows cols) (args rets : List E) :
    coreProgram.Rel rd name args rets → MeaningLRS nt1 b1 nt2 b2 rd args rets := by
  rw [rel_iff_sem hfind, hbody, hparams]
  simp only [lrsBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, List.range_succ,
    List.range_zero, List.nil_append, List.cons_append]
  rintro ⟨σ, rfl, hr, c18, hc, e26, e27, e28, e29, e30, e31, e32, hret⟩
  obtain ⟨n, hn, hgn, hm1⟩ := hrows _ _ hr
  obtain ⟨n2, hn2, hg6, hm2⟩ := hcols _ _ hc
  refine ⟨n, hn, hgn, fun hw ↦ ?_⟩
  obtain ⟨l1, hl1, hc1, hp1, hr1⟩ := hm1 fun h ↦ hw (Or.inl h)
  have h1len : (chainLast ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], σ (.n 5), σ (.n 6)⟩ l1).cap.length = 5 :=
    chainLast_cap_length rfl hc1
  obtain ⟨a, b, c, d, e, u, v, hcells, hst⟩ := cells_eq_seven h1len
  rw [hcells] at hr1
  simp only [List.cons.injEq, and_true] at hr1
  obtain ⟨h11, h12, h13, h14, h15, h16, h17⟩ := hr1
  rw [h11, h12, h13, h14, h15, h16, h17] at hm2
  obtain ⟨l2, hl2, hc2, hp2, hr2⟩ := hm2 fun h ↦ hw (Or.inr h)
  have h6 : n2 = 6 := by
    rw [c18, show (64 : ℕ) = 2 ^ 6 from rfl, word_two_pow (by norm_num)] at hg6
    exact (gen_pow_inj (by omega) (by omega) hg6).symm
  rw [← hst] at hc2 hr2
  refine ⟨l1, l2, hl1, by rw [hl2, h6], hc1, hc2, hp1, hp2, ?_⟩
  rw [← hret, e26, e27, e28, e29, e30, e31, e32, ← hr2]

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem link_row_side_L6_sound (rd : Reader) (hgc : GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_row_side__L6" args rets → MeaningLRS 7 0 6 0 rd args rets :=
  lrs_sound (fun _ _ ↦ link_rounds_L7_L0_sound rd (fun _ ↦ hgc) _ _)
    (fun _ _ ↦ link_rounds_L6_L0_sound rd (fun _ ↦ hgc) _ _)
    (coreProgram_find?_at (j := idx% «link_row_side__L6») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem link_row_side_L7_sound (rd : Reader) (hgc : GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_row_side__L7" args rets → MeaningLRS 8 1 7 0 rd args rets :=
  lrs_sound (fun _ _ ↦ link_rounds_L8_L1_sound rd (fun _ ↦ hgc) _ _)
    (fun _ _ ↦ link_rounds_L7_L0_sound rd (fun _ ↦ hgc) _ _)
    (coreProgram_find?_at (j := idx% «link_row_side__L7») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem link_row_side_L8_sound (rd : Reader) (hgc : GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_row_side__L8" args rets → MeaningLRS 9 1 8 1 rd args rets :=
  lrs_sound (fun _ _ ↦ link_rounds_L9_L1_sound rd (fun _ ↦ hgc) _ _)
    (fun _ _ ↦ link_rounds_L8_L1_sound rd (fun _ ↦ hgc) _ _)
    (coreProgram_find?_at (j := idx% «link_row_side__L8») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

set_option maxRecDepth 100000 in
theorem link_row_side_L9_sound (rd : Reader) (hgc : GcSound1 rd) (args rets : List E) :
    coreProgram.Rel rd "link_row_side__L9" args rets → MeaningLRS 10 1 9 1 rd args rets :=
  lrs_sound (fun _ _ ↦ link_rounds_L10_L1_sound rd (fun _ ↦ hgc) _ _)
    (fun _ _ ↦ link_rounds_L9_L1_sound rd (fun _ ↦ hgc) _ _)
    (coreProgram_find?_at (j := idx% «link_row_side__L9») rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) args rets

end
end LeanVM.Guest.B1.Link
