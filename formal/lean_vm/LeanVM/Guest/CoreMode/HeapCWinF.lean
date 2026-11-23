/-
  LeanVM.Guest.CoreMode.HeapCWinF

  The heap check of a function that is not a loop helper in windows: the pass over consecutive slices of the
  body, each from a stated state to a stated state, then the rest of the body from the last one.
-/

module

public import LeanVM.Guest.CoreMode.HeapCWin

/-!
# The heap check of a function body in windows

`HeapCWin` splits a loop helper's pass; this is the same for a function with `term = []`, whose check is
`(chkC X f.body S₀).isSome`. The body splits at cut points `a₀ = 0 < … < aₙ = N`: each window (`winOkF`) decides
that the statements `aᵢ` to `aᵢ₊₁ - 1` have no top-level `ret` (a `ret` inside an arm is fine: the pass returns
`st.nextT` there and joins), name no ghost value, and take the pass from `Sᵢ` to `Sᵢ₊₁` (`chkC_append`). The head
(`headOkF`) decides the parameters, the entry state `S₀`, no `term`, the frame run cells; the last part
(`lastOkF`), the statements from `N` on, the `ret` among them, from `Sₙ`. `heapOkC_of_winsF` assembles them.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec (Trie PowTree natSeq)

@[expose] public section

/-- **A window of a body**: the statements `ss` have no top-level `ret` and name no ghost value, and the pass
over them goes from `st` to `st'`. -/
noncomputable def winOkF (pows : PowTree) (sigOf : String → HSig) (f : Fn) (H : HCert) (ss : List Stmt)
    (st st' : CSt) : Bool :=
  !endsRet ss && ngL ss && withCx pows sigOf f H fun X ↦ decide (chkC X ss st = some st')

theorem winOkF_spec {pows : PowTree} {sigOf : String → HSig} {f : Fn} {H : HCert} {ss : List Stmt} {st st' : CSt}
    (h : winOkF pows sigOf f H ss st st' = true) :
    endsRet ss = false ∧ noGhostL ss = true ∧ chkC (cxOf pows sigOf f H) ss st = some st' := by
  simp only [winOkF, withCx_eq, Bool.and_eq_true, decide_eq_true_eq, ngL_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **Consecutive windows** of the block `L`, as `winsOk`, by `winOkF`. -/
def winsOkF (pows : PowTree) (sigOf : String → HSig) (f : Fn) (H : HCert) (L : List Stmt) :
    List (ℕ × CSt) → Prop
  | (a, S) :: (b, S') :: l => winOkF pows sigOf f H ((L.drop a).take (b - a)) S S' = true ∧ a ≤ b ∧
      winsOkF pows sigOf f H L ((b, S') :: l)
  | _ => True

/-- **Windows chained**: from the first cut point to the last, the pass goes from the first state to the last,
and the statements between name no ghost value. -/
theorem winsOkF_chain {pows : PowTree} {sigOf : String → HSig} {f : Fn} {H : HCert} {L : List Stmt} :
    ∀ (l : List (ℕ × CSt)) (a : ℕ) (S : CSt), winsOkF pows sigOf f H L ((a, S) :: l) →
      chkC (cxOf pows sigOf f H) (L.drop a) S =
          chkC (cxOf pows sigOf f H) (L.drop (lastW l (a, S)).1) (lastW l (a, S)).2 ∧
        noGhostL ((L.drop a).take ((lastW l (a, S)).1 - a)) = true ∧ a ≤ (lastW l (a, S)).1
  | [], a, S, _ => by simp [lastW, noGhostL, Stmt.usesList, Stmt.tmpsList]
  | (b, S') :: l, a, S, h => by
    obtain ⟨hw, hab, hr⟩ := h
    obtain ⟨hc, hg, hb⟩ := winsOkF_chain l b S' hr
    obtain ⟨hwr, hwg, hwc⟩ := winOkF_spec hw
    simp only [lastW] at hc hg hb ⊢
    have hsplit : L.drop a = (L.drop a).take (b - a) ++ L.drop b := by
      conv_lhs => rw [← List.take_append_drop (b - a) (L.drop a)]
      rw [List.drop_drop]; congr 2; omega
    have htake : (L.drop a).take ((lastW l (b, S')).1 - a) =
        (L.drop a).take (b - a) ++ (L.drop b).take ((lastW l (b, S')).1 - b) := by
      rw [show (lastW l (b, S')).1 - a = (b - a) + ((lastW l (b, S')).1 - b) by omega, List.take_add,
        List.drop_drop]
      congr 3; omega
    refine ⟨?_, ?_, by omega⟩
    · rw [hsplit, chkC_append _ _ _ _ hwr, hwc, Option.bind_some, hc]
    · rw [htake, noGhostL_append, hwg, hg]; rfl

/-- **The head of a body's check**: the parameters, the preconditions over them, no termination fact, the
parameters naming no ghost, the frame run cells at return (`faOk`), and the entry state `S₀`. -/
noncomputable def headOkF (pows : PowTree) (sigOf : String → HSig) (f : Fn) (H : HCert) (S0 : CSt) : Bool :=
  paramsN f.params 0 && preOver f.params.length H.sig.pre && H.sig.term.isEmpty && f.params.all okV &&
    faOk (topAtoms f.body) (dstKeys (topAtoms f.body)) H.fas && H.dups.isEmpty &&
    withCx pows sigOf f H fun X ↦ decide (initC X = some S0)

/-- **The last part of a body's check**: the statements from `N` on name no ghost value, and the pass over them
from `Sn` succeeds (it ends at a `ret`, or at the end of the body). -/
noncomputable def lastOkF (pows : PowTree) (sigOf : String → HSig) (f : Fn) (H : HCert) (N : ℕ) (Sn : CSt) :
    Bool :=
  ngL (f.body.drop N) && withCx pows sigOf f H fun X ↦ (chkC X (f.body.drop N) Sn).isSome

/-- **A body's heap check from windows**: the head, consecutive windows from `(0, S₀)` to `(N, Sₙ)`, and the
statements from `N` on. -/
theorem heapOkC1_of_winsF {pows : PowTree} {sigOf : String → HSig} {f : Fn} {H : HCert} {N : ℕ}
    {S0 Sn : CSt} {l : List (ℕ × CSt)} (hh : headOkF pows sigOf f H S0 = true)
    (hw : winsOkF pows sigOf f H f.body ((0, S0) :: l)) (hl : lastW l (0, S0) = (N, Sn))
    (ht : lastOkF pows sigOf f H N Sn = true) : heapOkC1 pows sigOf f H = true := by
  simp only [headOkF, Bool.and_eq_true, decide_eq_true_eq, withCx_eq, List.isEmpty_iff] at hh
  obtain ⟨⟨⟨⟨⟨⟨hpar, hpov⟩, hterm⟩, hpok⟩, hfa⟩, hdups⟩, hinit⟩ := hh
  simp only [lastOkF, Bool.and_eq_true, withCx_eq, ngL_eq] at ht
  obtain ⟨hng2, hlast⟩ := ht
  obtain ⟨hc, hng, -⟩ := winsOkF_chain l 0 S0 hw
  rw [hl] at hc hng
  simp only [List.drop_zero, Nat.sub_zero] at hc hng
  have hghost : noGhost f = true := by
    have h1 := noGhostL_append (f.body.take N) (f.body.drop N)
    rw [List.take_append_drop, hng, hng2] at h1
    simp only [noGhostL, List.all_append, Bool.and_true, Bool.and_eq_true] at h1
    simp only [noGhost, List.all_append, Bool.and_eq_true]
    exact ⟨⟨h1.1, h1.2⟩, hpok⟩
  unfold heapOkC1
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨hpar, hpov⟩, by simp [hterm]⟩, hghost⟩, hfa⟩, ?_⟩
  simp only [Trie.seq_eq]
  have hX : (⟨pows, H.readT, trieFrom H.sig.pre 0 .nil, trieFrom H.calls 0 .nil, trieFrom H.rets 0 .nil,
      trieFrom H.res 0 .nil, keysT H.divs .nil, keysT H.hvs .nil, H.gargs, sigOf, H.sig, f.params, [],
      keysT H.eqs .nil, H.fas, H.ders⟩ : CX) = cxOf pows sigOf f H := rfl
  rw [hX, hinit, hterm]
  simp only [bodyC, hdups, List.isEmpty_nil, Bool.cond_true]
  rw [hc]
  exact hlast

/-- `heapOkC1_of_winsF` for a certificate with no split. -/
theorem heapOkC_of_winsF {pows : PowTree} {sigOf : String → HSig} {f : Fn} {H : HCert} {N : ℕ}
    {S0 Sn : CSt} {l : List (ℕ × CSt)} (hh : headOkF pows sigOf f H S0 = true)
    (hw : winsOkF pows sigOf f H f.body ((0, S0) :: l)) (hl : lastW l (0, S0) = (N, Sn))
    (ht : lastOkF pows sigOf f H N Sn = true) (ha : H.arms = [] := by rfl) : heapOkC pows sigOf f H = true :=
  heapOkC_of1 ha (heapOkC1_of_winsF hh hw hl ht)

end

end LeanVM.Guest.CoreMode
