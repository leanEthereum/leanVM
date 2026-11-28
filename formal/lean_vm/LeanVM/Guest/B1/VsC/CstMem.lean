/-
  LeanVM.Guest.B1.VsC.CstMem

  `check_stack_terminal`'s forward valuation on a memory: its oracle, its facts.
-/

module

public import LeanVM.Guest.B1.VsC.CstVals

/-!
# `check_stack_terminal`'s forward valuation

`cstOrc`: the oracle, its buffers at the cursor `c`, the selectors at `csel`, `q_keccak`'s ring row
at `crow`, each `ring_cols` return its table's sum. `cst_fwdG`: on every memory where `StackCtxAt`
holds of the arguments, the forward valuation is a `CstG` and keeps the arguments, its calls'
returns the oracle's. `cst_hyp`: on a memory also holding the node's own words, the selectors and
the row, it is a `CstHyp`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Complete LeanVM.Guest.B1.Stack LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link
open LeanVM.Guest.B1.Whir LeanVM.Guest.Value LeanVM.Guest.B1.VerifySub LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **`check_stack_terminal`'s oracle.** -/
def cstOrc (layout : Layout) (chi x f g qPoint : List E) (rho : E) (c csel crow : ℕ) (i : ℕ) : E :=
  if 31 ≤ i ∧ i < 41 then ptrAtV (cstBase chi.length c (i - 31))
  else if i = 43 then ptrAtV csel else if i = 59 then ptrAtV crow
  else if i = 471 then rcSum layout chi x f g qPoint rho 0 0 5
  else if i = 488 then rcSum layout chi x f g qPoint rho 1 5 5
  else if i = 504 then rcSum layout chi x f g qPoint rho 2 10 3
  else if i = 522 then rcSum layout chi x f g qPoint rho 3 13 5
  else if i = 540 then rcSum layout chi x f g qPoint rho 4 18 5
  else if i = 569 then rcSum layout chi x f g qPoint rho 5 23 10 else 0

theorem cstOrc_buf {layout : Layout} {chi x f g qPoint : List E} {rho : E} {c csel crow : ℕ} :
    ∀ i < 10, cstOrc layout chi x f g qPoint rho c csel crow (31 + i) = ptrAtV (cstBase chi.length c i) := by
  intro i hi
  simp only [cstOrc, show 31 ≤ 31 + i ∧ 31 + i < 41 from ⟨by omega, by omega⟩, and_self, ↓reduceIte,
    Nat.add_sub_cancel_left]

theorem cstOrc_rc {layout : Layout} {chi x f g qPoint : List E} {rho : E} {c csel crow : ℕ} :
    ∀ p ∈ rcTab, cstOrc layout chi x f g qPoint rho c csel crow p.2.2.2 =
      rcSum layout chi x f g qPoint rho p.1 p.2.1 p.2.2.1 := by
  intro p hp
  simp only [rcTab, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [cstOrc]

theorem cstArgsOf_eq (σ : Val) : cstValArgs σ = ((List.range 23).map V.n).map σ := rfl

theorem cst_chk' : ∃ c', chk 23 cstBody = some c' := Option.isSome_iff_exists.mp cst_chk

theorem mem_cstBody_head {s : Stmt} (h : s ∈ cstHead) : s ∈ cstBody := mem_cstBody_of_B (memB_head h)

theorem mem_cstBody_rest {s : Stmt} (h : s ∈ cstRest) : s ∈ cstBody := by
  rw [cstBody_split]; simp [h]

section
variable {rd : Reader} {τ : Val} {layout : Layout} {link : LinkEnd} {chi r qPoint kOut kIn f g x z : List E}
  {rho lam rm : E} {outputs : List ColumnClaim} {c csel crow : ℕ}

/-- **The forward valuation on a memory where `StackCtxAt` holds**: a `CstG`, keeping the
arguments, its dispatch's and calls' returns the oracle's. -/
theorem cst_fwdG (hP : StackCtxAt rd (cstValArgs τ) layout link chi r qPoint kOut kIn f g x z rho lam rm outputs)
    (hL : layout.stackLog ≤ 30) :
    let w := cstOrc layout chi x f g qPoint rho c csel crow
    let σ := fwdVal rd w (cstValArgs τ) cstBody
    CstG rd w σ layout link chi r qPoint kOut kIn f g x z rho lam rm outputs c ∧ cstValArgs σ = cstValArgs τ ∧
      σ (.n 43) = ptrAtV csel ∧ (∀ cl ∈ cstRestCalls, ∀ v ∈ cl.rets, σ v = w v.idx) ∧
      ∀ s ∈ cstBody, GoodS rd cstS w σ s := by
  intro w σ
  obtain ⟨c', hc⟩ := cst_chk'
  have hchk : chk (cstValArgs τ).length cstBody = some c' := hc
  have hgs : ∀ s ∈ cstBody, GoodS rd cstS w σ s := fun s hs => (ev_spec rd w cstBody (cstValArgs τ) hchk).2.2 s hs
  have hargs : cstValArgs σ = cstValArgs τ := by
    rw [cstArgsOf_eq σ]; exact fwd_params hchk
  have hbuf : ∀ i < 10, σ (.n (31 + i)) = ptrAtV (cstBase chi.length c i) := by
    intro i hi
    rw [← cstOrc_buf (layout := layout) (x := x) (f := f) (g := g) (qPoint := qPoint) (rho := rho) (csel := csel)
      (crow := crow) i hi]
    have hm : ∃ sz, Stmt.atom (.hint (.alloc (.n (31 + i)) sz)) ∈ cstHead ∨
        Stmt.atom (.hint (.allocDyn (.n (31 + i)) (.n 30))) ∈ cstHead := by
      interval_cases i
      · exact ⟨0, Or.inr (by simp [cstHead])⟩
      · exact ⟨33, Or.inl (by simp [cstHead])⟩
      · exact ⟨33, Or.inl (by simp [cstHead])⟩
      · exact ⟨42, Or.inl (by simp [cstHead])⟩
      · exact ⟨42, Or.inl (by simp [cstHead])⟩
      · exact ⟨42, Or.inl (by simp [cstHead])⟩
      · exact ⟨42, Or.inl (by simp [cstHead])⟩
      · exact ⟨31, Or.inl (by simp [cstHead])⟩
      · exact ⟨126, Or.inl (by simp [cstHead])⟩
      · exact ⟨31, Or.inl (by simp [cstHead])⟩
    obtain ⟨sz, hm | hm⟩ := hm
    · exact hgs _ (mem_cstBody_head hm)
    · exact hgs _ (mem_cstBody_head hm)
  refine ⟨⟨fun a ha => hgs _ (mem_cstBody_of_B (mem_of_mem_atomsOf ha)), hbuf, by rw [hargs]; exact hP, hL⟩, hargs,
    ?_, fun cl hcl v hv => ?_, hgs⟩
  · have hd : Stmt.dispatch (.n 42) cstArms cstArgsV [.n 43] ∈ cstBody := by rw [cstBody_split]; simp
    have := hgs _ hd (.n 43) (by simp)
    rw [this]; simp [w, cstOrc]
  · have hm : Stmt.call cl.f cl.args cl.rets ∈ cstRest := mem_callsOfB (by rw [cstRest_calls]; exact hcl)
    exact hgs _ (mem_cstBody_rest hm) v hv

end

end
end LeanVM.Guest.B1.VsC
