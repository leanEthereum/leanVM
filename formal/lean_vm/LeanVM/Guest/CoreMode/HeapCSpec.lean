/-
  LeanVM.Guest.CoreMode.HeapCSpec

  What the core route takes of a function's heap check with calls and loops, whichever checker decided it.
-/

module

public import LeanVM.Guest.CoreMode.HeapCSig

/-!
# The heap check's interface

`HeapCSpec pows sigOf f H`: what the route's proofs (`CoreFacts.lean`, `CoreLoopC.lean`) take of a function's heap
check with calls and loops, at its callees' signatures `sigOf` and its certificate `H`: its parameters are `V.n 0`,
`V.n 1`, …; a loop helper (`term = [(.val 0, ei)]`) names no returned word, word at return, equation or run at a word;
and on every returning path whose events hold, given its entry facts, residuals, words at cells and parameter words,
every event's needs are written before it and, every call having its callee's returned words, its guarantees at return
(`heapOkC_soundP`'s conclusion). The kernel-checked checkers prove it: `heapOkC` (`HeapCSound.lean`, `heapOkC_spec`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **The heap check with calls and loops, as the route takes it.** -/
structure HeapCSpec (pows : Exec.PowTree) (sigOf : String → HSig) (f : Fn) (H : HCert) : Prop where
  params : f.params = (List.range f.params.length).map V.n
  loop : ∀ ei, H.sig.term = [(.val 0, ei)] →
    H.sig.retM = [] ∧ H.sig.postV = [] ∧ H.sig.retEq = [] ∧ H.sig.postQ = []
  sound : pows.Ok → sigOf f.name = H.sig → ∀ {σ : Val} {rd : Reader} {es : List Ev} {vs : List V},
    walk σ f.body = .ret es vs → (∀ e ∈ es, e.Holds rd σ) → EntryF H (f.params.map σ) → ResF H σ →
    DerOk H rd σ → GwOk H.sig rd σ →
    ReadsOkP sigOf H rd σ (f.params.map σ) es ∧ ((∀ e ∈ es, EvM sigOf rd σ e) →
      (PostOkC sigOf H rd σ (f.params.map σ) es vs ∧ (H.fas = [] → PostOkW sigOf H rd σ (f.params.map σ) es vs)) ∧
      RetMOk H.sig (f.params.map σ) (vs.map σ) ∧ RetVOk rd H.sig (f.params.map σ ++ vs.map σ) ∧
      RetEqOk H.sig (f.params.map σ ++ vs.map σ))

namespace HeapCSpec

variable {pows : Exec.PowTree} {sigOf : String → HSig} {f : Fn} {H : HCert}

/-- `heapOkC_sound`'s conclusion. -/
theorem sound_all (h : HeapCSpec pows sigOf f H) (hp : pows.Ok) (hself : sigOf f.name = H.sig) {σ : Val}
    {rd : Reader} {es : List Ev} {vs : List V} (hw : walk σ f.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ)
    (hM : ∀ e ∈ es, EvM sigOf rd σ e) (hE : EntryF H (f.params.map σ)) (hR : ResF H σ) (hD : DerOk H rd σ)
    (hG : GwOk H.sig rd σ) :
    ReadsOkC sigOf H rd σ (f.params.map σ) es ∧ PostOkC sigOf H rd σ (f.params.map σ) es vs ∧
      RetMOk H.sig (f.params.map σ) (vs.map σ) ∧ RetVOk rd H.sig (f.params.map σ ++ vs.map σ) ∧
      RetEqOk H.sig (f.params.map σ ++ vs.map σ) :=
  have h := h.sound hp hself hw hh hE hR hD hG
  ⟨readsOkC_of_P h.1 hM, (h.2 hM).1.1, (h.2 hM).2⟩

/-- `heapOkC_soundW`'s conclusion: no frame run cell guaranteed, the guarantees written by the events. -/
theorem soundW (h : HeapCSpec pows sigOf f H) (hp : pows.Ok) (hself : sigOf f.name = H.sig) {σ : Val}
    {rd : Reader} {es : List Ev} {vs : List V} (hw : walk σ f.body = .ret es vs) (hh : ∀ e ∈ es, e.Holds rd σ)
    (hM : ∀ e ∈ es, EvM sigOf rd σ e) (hE : EntryF H (f.params.map σ)) (hR : ResF H σ) (hD : DerOk H rd σ)
    (hG : GwOk H.sig rd σ) (hn : H.fas = []) : PostOkW sigOf H rd σ (f.params.map σ) es vs :=
  ((h.sound hp hself hw hh hE hR hD hG).2 hM).1.2 hn

end HeapCSpec

end

end LeanVM.Guest.CoreMode
