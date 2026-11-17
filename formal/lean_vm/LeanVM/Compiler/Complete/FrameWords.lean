/-
  LeanVM.Compiler.Complete.FrameWords

  The frame side's statement from the walk's: one frame for each class of valuations agreeing off
  the temporaries, patched at the temporaries' cells.
-/

module

public import LeanVM.Compiler.Complete.FrameWalk
public import LeanVM.Compiler.Complete.FrameOp

/-!
# `FrameWordsStmt` from `WalkWordsStmt`

The frame family takes, for a valuation `σ`, the walk's frame words `Ψ` and headers `kh` of the
class of `σ` (chosen at `zeroTmps σ`, the class's representative), patched at the temporaries'
cells with `σ`'s words (`patchT`). Two valuations agreeing off the temporaries have one
representative, so the family is blind to the temporaries' words (`FrameCongr`). The path of `σ`
is its representative's (`walk_congr`: the temporaries are named by no statement), its events'
relations without the temporaries' loads agree (`evNT_of_holds`), so the walk's statement at the
representative gives `σ` its clauses and its path's words.
-/

namespace LeanVM.Compiler.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

theorem zeroTmps_zeroTmps (ts : List V) (σ : Val) : zeroTmps ts (zeroTmps ts σ) = zeroTmps ts σ := by
  funext v
  unfold zeroTmps
  split <;> rfl

theorem zeroTmps_congr {ts : List V} {σ σ' : Val} (h : ∀ v, v ∉ ts → σ' v = σ v) :
    zeroTmps ts σ' = zeroTmps ts σ := by
  funext v
  unfold zeroTmps
  split
  · rfl
  · next hv => exact h v hv

theorem zeroTmps_off {ts : List V} {σ : Val} {v : V} (hv : v ∉ ts) : zeroTmps ts σ v = σ v := by
  simp [zeroTmps, hv]

theorem instOf_zeroTmps {κ₀ : ℕ} (W : World κ₀) (tf : TracedFn) (pf : Placed) (fp : ℕ)
    (hdr : E × E) (σ : Val) (es : List Ev) :
    instOf W tf pf fp hdr (zeroTmps (Stmt.tmpsList tf.core.body) σ) es = instOf W tf pf fp hdr σ es := by
  simp only [instOf, zeroTmps_zeroTmps]

/-- `patchT` reads of the instance only its temporaries and places. -/
theorem patchT_instOf {κ₀ : ℕ} (W : World κ₀) (tf : TracedFn) (pf : Placed) (fp : ℕ)
    (hdr : E × E) (σ₁ σ₂ : Val) (es₁ es₂ : List Ev) :
    patchT (instOf W tf pf fp hdr σ₁ es₁) = patchT (instOf W tf pf fp hdr σ₂ es₂) := rfl

/-- **The frame side's statement from the walk's.** -/
theorem frameWords_of_walk (hWW : WalkWordsStmt) : FrameWordsStmt := by
  intro κ₀ W hc tf htf hsc pf hpl hta hns fp hfp kfps hdr
  classical
  set T := Stmt.tmpsList tf.core.body with hT
  have hfresh := hta.fresh
  have hX : ∀ σ₀ : Val, ∃ p : (ℕ → E) × (ℕ → E × E), ∀ es vs,
      walk σ₀ tf.core.body = .ret es vs →
      (∀ q ∈ addrs es, σ₀ q.1 = ofK (addressOfIndex (fp + (cellP pf.locs q.2).getD 0))) →
      (∃ rd, (instOf W tf pf fp hdr σ₀ es).Rd rd) →
      ∀ σ', (instOf W tf pf fp hdr σ₀ es).Same σ' →
        (∀ rd : Reader, (∀ e ∈ es, e.Holds rd σ') →
          FrameClauses (loopTable W.p) tf pf fp σ' es vs hdr
            ⟨patchT (instOf W tf pf fp hdr σ₀ es) p.1 σ', p.2⟩) ∧
        (kfps.length = (calls es).length →
          (isLoopName tf.core.name = true → ∀ kfp, kfps.getLast? = some kfp →
            kfp = fp + pf.fn.frameSize) →
          (tf.core.name ≠ "main" → IsInK hdr.1 ∧ IsInK hdr.2) →
          (∃ rd : Reader, ∀ e ∈ es, e.Holds rd σ') →
          PathWords W tf pf fp σ' es kfps hdr ⟨patchT (instOf W tf pf fp hdr σ₀ es) p.1 σ', p.2⟩) := by
    intro σ₀
    rcases hwk : walk σ₀ tf.core.body with es | ⟨es, vs⟩ | _
    · exact ⟨(fun _ => 0, fun _ => (0, 0)), fun _ _ h => nomatch h⟩
    · by_cases hpre : (∀ q ∈ addrs es, σ₀ q.1 = ofK (addressOfIndex (fp + (cellP pf.locs q.2).getD 0)))
          ∧ ∃ rd, (instOf W tf pf fp hdr σ₀ es).Rd rd
      · obtain ⟨Ψ, kh, h⟩ :=
          hWW W hc tf htf hsc pf hpl hta hns fp hfp kfps hdr σ₀ es vs hwk hpre.1 hpre.2
        refine ⟨(Ψ, kh), fun es' vs' h' _ _ => ?_⟩
        simp only [Out.ret.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        exact h
      · refine ⟨(fun _ => 0, fun _ => (0, 0)), fun es' vs' h' ha hr => ?_⟩
        simp only [Out.ret.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        exact absurd ⟨ha, hr⟩ hpre
    · exact ⟨(fun _ => 0, fun _ => (0, 0)), fun _ _ h => nomatch h⟩
  let pick : Val → (ℕ → E) × (ℕ → E × E) := fun σ₀ => Classical.choose (hX σ₀)
  refine ⟨fun σ => ⟨patchT (instOf W tf pf fp hdr σ []) (pick (zeroTmps T σ)).1 σ,
    (pick (zeroTmps T σ)).2⟩, ?_, ?_⟩
  · intro σ σ' hσ
    have hz : zeroTmps T σ' = zeroTmps T σ := zeroTmps_congr hσ
    refine ⟨fun n hn => ?_, by simp only [hz]⟩
    have hnt : ¬ (instOf W tf pf fp hdr σ' []).tc n := fun ⟨t, ht, hc'⟩ => hn t ht hc'
    have hnt' : ¬ (instOf W tf pf fp hdr σ []).tc n := fun ⟨t, ht, hc'⟩ => hn t ht hc'
    simp [patchT, hnt, hnt', hz]
  · intro σ es vs hw ha
    set σ₀ := zeroTmps T σ with hσ₀
    have hwi := walk_within (σ := σ) tf.core.body
    rw [hw] at hwi
    have huse : ∀ e ∈ es, ∀ v ∈ e.uses, σ v = σ₀ v := fun e he v hv =>
      (zeroTmps_off fun ht => (hfresh.2 v ht).1 (hwi.1 e he v hv)).symm
    have hw₀ : walk σ₀ tf.core.body = .ret es vs := by
      rw [← hw]
      exact walk_congr tf.core.body fun v hv => zeroTmps_off fun ht => (hfresh.2 v ht).1 hv
    have ha₀ : ∀ q ∈ addrs es, σ₀ q.1 = ofK (addressOfIndex (fp + (cellP pf.locs q.2).getD 0)) := by
      intro q hq
      rw [← ha q hq]
      obtain ⟨e, he, hq'⟩ : ∃ e ∈ es, Ev.addr? e = some q := by
        simpa [addrs, List.mem_filterMap] using hq
      have hu : q.1 ∈ e.uses := by
        match e, hq' with
        | .atom (.frameAddr p (r :: rs)), hq' =>
          simp only [Ev.addr?, Option.some.injEq] at hq'
          subst hq'
          simp [Ev.uses, atomUses]
      exact (huse e he q.1 hu).symm
    have hSame : (instOf W tf pf fp hdr σ₀ es).Same σ := fun v hv => by
      have hv' : v ∉ T := hv
      show σ v = zeroTmps T σ₀ v
      rw [hσ₀, zeroTmps_zeroTmps, zeroTmps_off hv']
    have hRd : ∀ rd : Reader, (∀ e ∈ es, e.Holds rd σ) → (instOf W tf pf fp hdr σ₀ es).Rd rd :=
      fun rd hrd e he => by
        show evNT rd (zeroTmps T σ₀) e
        rw [hσ₀, zeroTmps_zeroTmps]
        exact evNT_of_holds (huse e he) (hrd e he)
    have hp := Classical.choose_spec (hX σ₀)
    refine ⟨fun rd hrd => (hp es vs hw₀ ha₀ ⟨rd, hRd rd hrd⟩ σ hSame).1 rd hrd,
      fun hl htl hhk ⟨rd, hrd⟩ =>
        (hp es vs hw₀ ha₀ ⟨rd, hRd rd hrd⟩ σ hSame).2 hl htl hhk ⟨rd, hrd⟩⟩

/-- info: 'LeanVM.Compiler.Complete.frameWords_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms frameWords_of_walk

end
end LeanVM.Compiler.Complete
