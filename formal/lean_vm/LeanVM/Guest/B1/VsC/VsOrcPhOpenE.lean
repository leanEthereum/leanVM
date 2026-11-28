/-
  LeanVM.Guest.B1.VsC.VsOrcPhOpenE

  `PhOpen` at the honest values with `check_stack_terminal`'s end bounded.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcPhOpen
public import LeanVM.Guest.B1.VsC.CalleesB
public import LeanVM.Guest.Complete.FsSmall

/-!
# `PhOpen` with the stack terminal's end bounded

**`phOpenOk_inE`**: `phOpenOk_in` from `CheckStackTerminalCompleteAE … Bd` (vsbnd's statement with an end bound
`Bd`), the continuation also given `Bd` at `check_stack_terminal`'s cursor, so `verify_sub`'s end state, whose
callees' cursor is that callee's end, is bounded.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Stack LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 rd1 : Reader}
  {args : List E} {cur p : ℕ} {ret : ℕ → (ℕ → E) → E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **`PhOpen` at the honest values, `check_stack_terminal`'s end bounded**: `phOpenOk_in` from
`CheckStackTerminalCompleteAE … Bd`, its continuation also given `Bd` at the callee's cursor. -/
theorem phOpenOk_inE {Bd : ℕ → ℕ → Prop} (hC : CheckStackTerminalCompleteAE fs al cert k Bd) (ha : args.length = 6) (hr : CausalRule ret)
    {st : St} {K : St → Prop} {b23 bm : ℕ} {xs23 xm : List E} {sl ic0 qt : ℕ} {a96 h1 h2 : E} {fsv : List E}
    {Ro Do : ℕ → Prop} {Oo Po : Reader → Prop} {Qo : Reader → Tree → Prop} {Bo eo : ℕ} {s0 c pp : ℕ}
    {wE : WhirEnd} {bp bp1 nx : ℕ} {layout : Layout} {link : LinkEnd} {chi r qPoint kOut kIn f g x z : List E}
    {rho lam rm : E} {outputs : List ColumnClaim} {keccakSlices : List E} {oodValue v0 v1 : E}
    {claims : List StackClaim} {carr : List (ℕ × ℕ)}
    (H : PhOpenIn fs al cert k rd0 rd1 args cur p ret Own R Pre st b23 bm xs23 xm sl ic0 qt a96 h1 h2 fsv Ro Do Oo Po
      Qo Bo eo s0 c pp wE bp bp1 nx layout link chi r qPoint kOut kIn f g x z rho lam rm outputs keccakSlices oodValue
      v0 v1 claims carr)
    (hK : ∀ ec : ℕ, st.kc ≤ ec →
      Bd (allocBase (al "check_stack_terminal") eo + fs "check_stack_terminal") ec → K ⟨st.a, ec, fun rd => (st.O rd ∧ Oo rd) ∧ True, fun i => (st.D i ∨ Do i) ∨ False,
      st.Qs ++ [Qo, PostQuiet]⟩) :
    PhOpenOk fs al cert k rd0 (vsW rd1 args cur p ret) args Own R Pre st K := by
  have hl : (osRets wE bp bp1 (ic0 + 1 + nx)).length = 6 := rfl
  have e := vsW_rets (rd1 := rd1) (cur := cur) (p := p) ha hr (i0 := 3991) (cs := osRets wE bp bp1 (ic0 + 1 + nx))
    (fun j hj => by rw [hl] at hj; interval_cases j <;> decide)
    (fun j hj σ => H.ro j (by rw [hl] at hj; exact hj) σ)
  have hrets : osRets wE bp bp1 (ic0 + 1 + nx) =
      [vsW rd1 args cur p ret 3991, vsW rd1 args cur p ret 3992, vsW rd1 args cur p ret 3993,
        vsW rd1 args cur p ret 3994, vsW rd1 args cur p ret 3995, vsW rd1 args cur p ret 3996] := by
    rw [← e, hl]; rfl
  have hos := H.hos
  rw [hrets] at hos
  have h3996 : vsW rd1 args cur p ret 3996 = ptrAt (s0 + c) := by
    have := congrArg (fun l => l.getD 5 0) hrets
    simp only [osRets, List.getD_cons_succ, List.getD_cons_zero] at this
    rw [← this, H.hie]
  obtain ⟨ec, hB, hcs⟩ := hC (cstArgsOf (vsVal rd0 (vsW rd1 args cur p ret) args) (vsW rd1 args cur p ret)) layout link
    chi r qPoint kOut kIn f g x z rho lam rm outputs keccakSlices oodValue v0 v1 claims
    (allocBase (al "check_stack_terminal") eo) H.hcl H.hsl H.hid
    (by rw [H.hcarr]; exact ptrsBelow_idx fun q hq => le_trans (H.hfc q hq) (le_allocBase _ _))
  rw [H.hcarr] at hcs
  have hcs := CallAtA.idxR hcs
  obtain ⟨_, _, hoe, _⟩ := id hos
  obtain ⟨_, _, hce, _⟩ := id hcs
  have hke : st.kc ≤ ec := le_trans (le_allocBase _ _) (le_trans (Nat.le_add_right _ _) (le_trans hoe
    (le_trans (le_allocBase _ _) (le_trans (Nat.le_add_right _ _) hce))))
  refine ⟨b23, bm, xs23, xm, sl, ic0, qt, a96, h1, h2, fsv, Ro, Do, Oo, Po, Qo, Bo, eo, s0, c, pp, _, _, _, _, _, _,
    ec, ⟨H.h23, H.hl23, H.r23, H.hO23, H.hc23, H.h1076, H.hlm, H.rm', H.hOm, H.hcm, H.h16, H.h30, H.h489, H.h96,
    H.hfsv, H.h134, H.h137, H.h2920, H.h4, hos, H.hRo, H.hPo, H.hc, H.hpk, h3996, H.h55, H.h42, hcs, ?_,
    fun rd hrd => H.hPc rd hrd⟩, hK ec hke hB⟩
  rintro i ⟨q, hq, t, ht, rfl⟩
  exact H.hcc q hq t ht

end

end
end LeanVM.Guest.B1.VsC
