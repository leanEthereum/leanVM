/-
  LeanVM.Guest.B1.Common.Phase

  One phase of openings at Keccak-256: `openPhaseWithHash` is `openAllWithHash` on a phase of the
  verifier's shape whose positions are the queries.
-/

module

public import LeanVM.Protocol.WithHash

/-!
# A phase of openings

A query step consumes one phase (`Compile.openPhaseWithHash`, `Transcript::merkle`): every opening
of the commitment's shape, the phase's positions the sampled queries, then every path climbing to
the root (`openAllWithHash`).

* `openOne_shape`: an opening `openOne` accepts has the commitment's shape.
* `openPhase_of_openAll`: a phase of the queries' positions that `openAll` opens entirely is
  opened by `openPhase`, with the same leaves; `openPhase_eq_leaves`: one whose every opening
  `openOne` accepts at its query gives its leaves.
* `openPhase_some`: what an accepted phase is: of the shape, at the queries' positions, opened by
  `openAll` with nothing left.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile

@[expose] public section

variable (H : Bytes → Id Digest)

/-- **An opening `openOne` accepts has the commitment's shape.** -/
theorem openOne_shape {root : Digest} {height width q : ℕ} {o : Opening}
    (h : Id.run (openOneWithHash (m := Id) H root height width q o) = true) :
    o.leaf.length = width ∧ o.path.length = height := by
  by_contra hs
  simp only [Id.run, openOneWithHash, hs, ↓reduceIte, pure] at h
  exact Bool.false_ne_true h

/-- `openAll` consumes one opening per position. -/
theorem openAll_length {root : Digest} {height width : ℕ} :
    ∀ (ps : List ℕ) (os : List Opening) (rows : List (List K)) (rest : List Opening),
      Id.run (openAllWithHash (m := Id) H root height width ps os) = some (rows, rest) →
        os.length = ps.length + rest.length ∧ rows = (os.take ps.length).map (·.leaf)
  | [], os, rows, rest, h => by
    simp only [Id.run, openAllWithHash, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | _ :: _, [], _, _, h => by simp [Id.run, openAllWithHash, pure] at h
  | q :: qs, o :: os, rows, rest, h => by
    simp only [Id.run, openAllWithHash, bind] at h
    split at h
    · cases hr : openAllWithHash (m := Id) H root height width qs os with
      | none => simp [hr, pure] at h
      | some v =>
        obtain ⟨rows', rest'⟩ := v
        rw [hr] at h
        simp only [pure, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := openAll_length qs os rows' rest' hr
        refine ⟨by simp [h1]; omega, by simp [h2]⟩
    · simp [pure] at h

/-- `openAll` accepts at each position the opening at the same index. -/
theorem openAll_openOne {root : Digest} {height width : ℕ} :
    ∀ (ps : List ℕ) (os : List Opening) (rows : List (List K)) (rest : List Opening),
      Id.run (openAllWithHash (m := Id) H root height width ps os) = some (rows, rest) →
        ∀ k (hk : k < ps.length) (ho : k < os.length),
          Id.run (openOneWithHash (m := Id) H root height width ps[k] os[k]) = true
  | [], _, _, _, _, k, hk, _ => by simp at hk
  | _ :: _, [], _, _, h, _, _, _ => by simp [Id.run, openAllWithHash, pure] at h
  | q :: qs, o :: os, rows, rest, h, k, hk, ho => by
    simp only [Id.run, openAllWithHash, bind] at h
    split at h
    · rename_i hok
      cases hr : openAllWithHash (m := Id) H root height width qs os with
      | none => simp [hr, pure] at h
      | some v =>
        obtain ⟨rows', rest'⟩ := v
        rcases k with _ | k
        · exact hok
        · exact openAll_openOne qs os rows' rest' hr k (by simpa using hk) (by simpa using ho)
    · simp [pure] at h

/-- **A phase `openAll` opens entirely, of the shape and at the queries' positions, is opened by
`openPhase`**, with the same leaves. -/
theorem openPhase_of_openAll {root : Digest} {height width : ℕ} {ps : List ℕ}
    {phase : List Opening} {rows : List (List K)} {rest : List Opening}
    (hshape : ∀ o ∈ phase, o.leaf.length = width ∧ o.path.length = height)
    (hidx : phase.map Opening.leafIndex = ps)
    (h : Id.run (openAllWithHash (m := Id) H root height width ps phase) = some (rows, rest)) :
    Id.run (openPhaseWithHash (m := Id) H root height width ps phase) = some rows := by
  simp only [Id.run] at h
  have hc : (∀ o ∈ phase, o.leaf.length = width ∧ o.path.length = height) ∧
      phase.map Opening.leafIndex = ps := ⟨hshape, hidx⟩
  simp only [Id.run, openPhaseWithHash]
  split_ifs
  simp only [bind, h, pure]

/-- **A phase at the queries' positions whose every opening `openOne` accepts at its query** gives
its leaves. -/
theorem openPhase_eq_leaves {root : Digest} {height width : ℕ} {ps : List ℕ}
    {phase : List Opening} (hl : phase.length = ps.length)
    (hok : ∀ k (hk : k < ps.length) (ho : k < phase.length),
      Id.run (openOneWithHash (m := Id) H root height width ps[k] phase[k]) = true)
    (hidx : phase.map Opening.leafIndex = ps) :
    Id.run (openPhaseWithHash (m := Id) H root height width ps phase) = some (phase.map (·.leaf)) := by
  have hall : ∀ (qs : List ℕ) (os : List Opening), os.length = qs.length →
      (∀ k (hk : k < qs.length) (ho : k < os.length),
        Id.run (openOneWithHash (m := Id) H root height width qs[k] os[k]) = true) →
      Id.run (openAllWithHash (m := Id) H root height width qs os) = some (os.map (·.leaf), []) := by
    intro qs
    induction qs with
    | nil => intro os hl _; cases os <;> simp_all [Id.run, openAllWithHash, pure]
    | cons q qs ih =>
      intro os hl hok
      cases os with
      | nil => simp at hl
      | cons o os =>
        have h0 := hok 0 (by simp) (by simp)
        have ih' := ih os (by simpa using hl)
          (fun k hk ho ↦ hok (k + 1) (by simpa using hk) (by simpa using ho))
        simp only [List.getElem_cons_zero, Id.run] at h0 ih'
        simp only [Id.run, openAllWithHash, bind, h0, ↓reduceIte, ih', pure, Option.map_some,
          List.map_cons]
  refine openPhase_of_openAll H (fun o ho ↦ ?_) hidx (hall ps phase hl hok)
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ho
  exact openOne_shape H (hok k (by omega) hk)

/-- **What an accepted phase is**: of the shape, at the queries' positions, opened by `openAll`
with nothing left. -/
theorem openPhase_some {root : Digest} {height width : ℕ} {ps : List ℕ} {phase : List Opening}
    {rows : List (List K)}
    (h : Id.run (openPhaseWithHash (m := Id) H root height width ps phase) = some rows) :
    (∀ o ∈ phase, o.leaf.length = width ∧ o.path.length = height) ∧
      phase.map Opening.leafIndex = ps ∧
      Id.run (openAllWithHash (m := Id) H root height width ps phase) = some (rows, []) := by
  simp only [Id.run, openPhaseWithHash, bind, pure] at h
  split_ifs at h with hc
  · obtain ⟨hshape, hidx⟩ := hc
    refine ⟨hshape, hidx, ?_⟩
    split at h
    · rename_i rows' rest hr
      simp only [Option.some.injEq] at h
      subst h
      have hl := (openAll_length H ps phase rows' rest hr).1
      have : phase.length = ps.length := by rw [← hidx, List.length_map]
      have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hrest
      exact hr
    · simp at h

end
end LeanVM.Guest.B1
