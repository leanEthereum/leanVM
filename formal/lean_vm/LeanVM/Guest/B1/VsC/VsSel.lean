/-
  LeanVM.Guest.B1.VsC.VsSel

  `verify_sub`'s window `18` of `wA` and the least-height branch's selector.
-/

module

public import LeanVM.Guest.B1.VsC.VsPh1
import LeanVM.Guest.B1.Link.Forms

/-!
# The least-height selector

Statements `174 ..< 180` (`vsA_w18`): the `KECCAK` table's log height `g^h` (`.n 120`, `h` at least its
floor `9`, at most `24`) divided by `g^9`, range checked below `g^24`, then the selector
`.n 234 = g^h + g^9`. `vsW18_runHyp`: the window's hypotheses. `vs_sel234`: the selector is in `K`, and
zero exactly when `h = 9`, the case the branch skips the height's least-ness checks
(`IteHyp`'s first conjunct, and which arm is taken).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

/-- Statements `174 ..< 180`. -/
def vsW18 : List Atom := [
    .const (.n 227) (word 16777216 0),
    .const (.n 228) (word 512 0),
    .mul (.n 120) (.n 229) (.n 228),
    .rangeCheck (.n 229) (.n 230) (.n 231) (.n 232) (.n 227),
    .const (.n 233) (word 512 0),
    .add (.n 234) (.n 120) (.n 233)]

set_option maxRecDepth 100000 in
theorem vsW18_eq : (vsA.drop 174).take 6 = vsW18.map Stmt.atom := stmtsEqb_sound (by decide +kernel)

theorem vsA_w18_eq : vsA_w18 = .run vsW18 := by rw [vsA_w18, vsW18_eq, atomsOf_map]

theorem vsW18_ne : vsW18.all neB = true := by decide +kernel

theorem vsW18_pure : vsW18.filter pureAsks =
    [.mul (.n 120) (.n 229) (.n 228), .rangeCheck (.n 229) (.n 230) (.n 231) (.n 232) (.n 227)] := by decide +kernel

theorem vsW18_mem : vsW18.filter memAsks = [] := by decide +kernel

section
variable {rd0 : Reader} {w : ℕ → E} {args : List E}

theorem vsW18_vals (ha : args.length = 6) {h : ℕ} (h9 : 9 ≤ h) (h120 : vsVal rd0 w args (.n 120) = gen ^ h) :
    vsVal rd0 w args (.n 227) = gen ^ 24 ∧ vsVal rd0 w args (.n 228) = gen ^ 9 ∧
      vsVal rd0 w args (.n 229) = gen ^ (h - 9) ∧ vsVal rd0 w args (.n 234) = gen ^ h + gen ^ 9 := by
  have hg := vsA_run_good (rd0 := rd0) (w := w) ha vsW18_eq vsW18_ne
  have h227 : vsVal rd0 w args (.n 227) = gen ^ 24 :=
    (hg (.const (.n 227) _) (by simp [vsW18])).trans (wordG (j := 24) (by norm_num))
  have h228 : vsVal rd0 w args (.n 228) = gen ^ 9 :=
    (hg (.const (.n 228) _) (by simp [vsW18])).trans (wordG (j := 9) (by norm_num))
  have h233 : vsVal rd0 w args (.n 233) = gen ^ 9 :=
    (hg (.const (.n 233) _) (by simp [vsW18])).trans (wordG (j := 9) (by norm_num))
  have h229 : vsVal rd0 w args (.n 229) = gen ^ (h - 9) := by
    have := hg (.mul (.n 120) (.n 229) (.n 228)) (by simp [vsW18])
    simp only [Good, show ¬ ((V.n 229).idx < (V.n 120).idx ∧ (V.n 228).idx < (V.n 120).idx) from by decide,
      ↓reduceIte] at this
    rw [this, h120, h228, gen_div h9]
  have h234 : vsVal rd0 w args (.n 234) = gen ^ h + gen ^ 9 := by
    have := hg (.add (.n 234) (.n 120) (.n 233)) (by simp [vsW18])
    simp only [Good] at this
    rw [this, h120, h233]
  exact ⟨h227, h228, h229, h234⟩

/-- **The least-height selector**: in `K`, zero exactly when the height is its floor `9`. -/
theorem vs_sel234 (ha : args.length = 6) {h : ℕ} (h9 : 9 ≤ h) (h24 : h ≤ 24)
    (h120 : vsVal rd0 w args (.n 120) = gen ^ h) :
    IsInK (vsVal rd0 w args (.n 234)) ∧ (vsVal rd0 w args (.n 234) = 0 ↔ h = 9) := by
  obtain ⟨-, -, -, h234⟩ := vsW18_vals ha h9 h120
  rw [h234]
  refine ⟨isInK_add (by rw [Value.gen_pow_eq_ofK]; exact Value.ofK_isInK _)
    (by rw [Value.gen_pow_eq_ofK]; exact Value.ofK_isInK _), ⟨fun h0 => ?_, fun e => by rw [e]; exact Link.add_self_E _⟩⟩
  have e : gen ^ h = gen ^ 9 := by
    have := congrArg (· + gen ^ 9) h0
    simpa only [add_assoc, Link.add_self_E, add_zero, zero_add] using this
  exact Value.gen_pow_inj (by omega) (by norm_num) e

end

section
variable {k : ℕ} {rd0 : Reader} {w : ℕ → E} {args : List E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **Window `18`'s hypotheses.** -/
theorem vsW18_runHyp (hk : 6 ≤ k) (ha : args.length = 6) {h a : ℕ} (h9 : 9 ≤ h) (h24 : h ≤ 24)
    (h120 : vsVal rd0 w args (.n 120) = gen ^ h) {D : ℕ → Prop} {O : Reader → Prop} :
    RunHyp k (vsVal rd0 w args) w a Own R D Pre O vsW18 := by
  obtain ⟨h227, h228, h229, -⟩ := vsW18_vals ha h9 h120
  have hg := vsA_run_good (rd0 := rd0) (w := w) ha vsW18_eq vsW18_ne
  have h230 : vsVal rd0 w args (.n 230) = gen ^ (24 - (h - 9)) := by
    have := (hg (.rangeCheck (.n 229) (.n 230) (.n 231) (.n 232) (.n 227)) (by simp [vsW18])).2.2
    have hl : (V.n 227).idx < (V.n 230).idx := by decide
    simp only [hl, ↓reduceIte] at this
    rw [this, h227, h229, gen_div (by omega)]
  refine RunHyp.of_asks rfl (by intro A hA; simp [loadAddrs, vsW18, Ev.loadAddr?] at hA)
    (by intro A hA; simp [heapHintAddrs, vsW18, Ev.hintAddrs] at hA) ?_
    (by intro rd _ _ _ x hx; rw [vsW18_mem] at hx; simp at hx)
  intro x hx
  rw [vsW18_pure] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · show (if (V.n 229).idx < (V.n 120).idx ∧ (V.n 228).idx < (V.n 120).idx then True
      else vsVal rd0 w args (.n 228) ≠ 0)
    simp only [show ¬ ((V.n 229).idx < (V.n 120).idx ∧ (V.n 228).idx < (V.n 120).idx) from by decide,
      ↓reduceIte, h228]
    exact pow_ne_zero _ Value.gen_ne_zero
  · exact ⟨by rw [h229]; exact lowW_pow (lt_two_pow_k hk (by omega)),
      by rw [h230]; exact lowW_pow (lt_two_pow_k hk (by omega))⟩

end

end
end LeanVM.Guest.B1.VsC
