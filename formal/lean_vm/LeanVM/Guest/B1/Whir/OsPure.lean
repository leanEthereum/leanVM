/-
  LeanVM.Guest.B1.Whir.OsPure

  The trees' sizes of `open_stacked`'s pure callees, from the guest's static certificates.
-/

module

public import LeanVM.Guest.Memory.GuestSize
public import LeanVM.Guest.Value.Bits

/-!
# The pure callees' sizes (TRIAGE #36)

`os_selfLoop_tot`: a loop helper calling only itself, its certificate a loop to its second
argument, entered at `[1, g^q, …]`, allocates at most `q` times its frame and its path's words.
`os_capLoop_tot`: a function calling only a loop helper that calls only itself, its certificate a
constant `B`, allocates at most its frame and words and `(B - ω f) / ω g` of the helper's.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier

@[expose] public section

theorem os_take_two {args : List E} {x y : E} (h : args.take 2 = [x, y]) : args.getD 0 0 = x ∧ args.getD 1 0 = y := by
  match args, h with
  | a :: b :: _, h => simp only [List.take_succ_cons, List.take_zero, List.cons.injEq] at h; exact ⟨h.1, h.2.1⟩

/-- **A self-calling loop helper from `1` to `g^q`.** -/
theorem os_selfLoop_tot (fs : String → ℕ) {j : ℕ} (hj : j < coreProgram.length) {f : String}
    (hn : coreProgram[j].name = f) (hc : (Stmt.blockCallees coreProgram[j].body).all (· == f) = true)
    {w : ℕ × List String} (hw : Stmt.blockWords coreProgram[j].body = some w) {c : ℕ}
    (hcf : staticCertOf f = .loop none [] ⟨c, []⟩ []) (hω : omegaOf f = c) (hc0 : 0 < c) {q : ℕ} (hq : 0 < q)
    (hq64 : q < 2 ^ 64 - 1) :
    ∀ rd (t : Tree) (args rets : List E), t.name = f → args.take 2 = [1, gen ^ q] →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram → t.total fs ≤ q * (fs f + wordsVal fs w) := by
  intro rd t args rets htn ha hv hb
  obtain ⟨hl, hcl⟩ := self_hyps (fs := fs) hj hn hc hw
  obtain ⟨h0, h1⟩ := os_take_two ha
  have ha0 : args.getD 0 0 = ofK (Parameters.gpow 0) := by rw [h0]; simp [Parameters.gpow]
  have he : endOf none args = ofK (Parameters.gpow q) := by
    rw [show endOf none args = args.getD 1 0 from rfl, h1, gen_pow_eq_ofK]
  have hwt := weight_le_of_loop coreProgram_checked hcf htn hv hb ha0 he hq hq64 (fun _ h => (List.not_mem_nil h).elim)
  have := total_le_self (ω := omegaOf) (n := q - 0) hl hcl htn hv hb (by rw [hω]; exact hc0)
    (by rw [hω]; simpa [Aff.eval] using hwt)
  simpa using this

/-- **A function calling only a self-calling loop helper**, its certificate constant. -/
theorem os_capLoop_tot (fs : String → ℕ) {j jl : ℕ} (hj : j < coreProgram.length) (hjl : jl < coreProgram.length)
    {f g : String} (hn : coreProgram[j].name = f) (hnl : coreProgram[jl].name = g) (hfg : f ≠ g)
    (hc : (Stmt.blockCallees coreProgram[j].body).all (· == g) = true)
    (hcl : (Stmt.blockCallees coreProgram[jl].body).all (· == g) = true)
    {w wl : ℕ × List String} (hw : Stmt.blockWords coreProgram[j].body = some w)
    (hwl : Stmt.blockWords coreProgram[jl].body = some wl)
    {B : ℕ} {ks : List (V × ℕ)} (hcf : staticCertOf f = .stat [] ⟨B, []⟩ ks) {cf cl : ℕ} (hωf : omegaOf f = cf)
    (hωl : omegaOf g = cl) (hcl0 : 0 < cl) :
    TotalLe coreProgram fs f fun _ => fs f + wordsVal fs w + (B - cf) / cl * (fs g + wordsVal fs wl) := by
  have hf := core_find hj hn
  have hg := core_find hjl hnl
  obtain ⟨-, hcg⟩ := self_hyps (fs := fs) hjl hnl hcl hwl
  let ω' : String → ℕ := fun h => if h = f then fs f + wordsVal fs w else fs g + wordsVal fs wl
  have hloc : LocLe coreProgram fs ω' (fun h => h = f ∨ h = g) := locLe_of_words fun h hh fn hfn => by
    rcases hh with rfl | rfl
    · rw [hf, Option.some.injEq] at hfn; subst hfn; exact ⟨w, hw, by simp [ω']⟩
    · rw [hg, Option.some.injEq] at hfn; subst hfn; exact ⟨wl, hwl, by simp [ω', Ne.symm hfg]⟩
  have hcin : CallsIn coreProgram (fun h => h = f ∨ h = g) := callsIn_of_callees fun h hh fn hfn h' hh' => by
    rcases hh with rfl | rfl
    · rw [hf, Option.some.injEq] at hfn; subst hfn; exact Or.inr (by simpa using List.all_eq_true.mp hc h' hh')
    · rw [hg, Option.some.injEq] at hfn; subst hfn; exact Or.inr (by simpa using List.all_eq_true.mp hcl h' hh')
  intro rd t args rets htn hv hb
  have htot := total_le_weight hloc hcin t (Or.inl htn) hv hb
  have hwB : t.weight omegaOf ≤ B := weightLe_of_stat coreProgram_checked hcf rd t args rets htn hv hb
  match t, hv with
  | .node f' σ bufs kids, hv' =>
    simp only [Tree.name] at htn
    subst f'
    obtain ⟨fn, hfn, -, es, vs, hwk, -, -, hk⟩ := hv'
    rw [hf, Option.some.injEq] at hfn
    subst hfn
    have hcs : ∀ c ∈ calls es, c.f = g := fun c hc' => by
      have := walk_callees (σ := σ) coreProgram[j].body (c := c) (by rw [hwk]; exact hc')
      simpa using List.all_eq_true.mp hc _ this
    rw [Tree.weight, weightKids_self hcg kids hk hcs, hωf, hωl] at hwB
    rw [Tree.weight, weightKids_self hcg kids hk hcs] at htot
    have hn' : Tree.weightKids (fun _ => 1) kids ≤ (B - cf) / cl :=
      (Nat.le_div_iff_mul_le hcl0).mpr (by rw [Nat.mul_comm]; omega)
    have e1 : ω' f = fs f + wordsVal fs w := by simp [ω']
    have e2 : ω' g = fs g + wordsVal fs wl := by simp [ω', Ne.symm hfg]
    rw [e1, e2] at htot
    exact htot.trans (Nat.add_le_add_left (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hn') _)

end
end LeanVM.Guest.B1
