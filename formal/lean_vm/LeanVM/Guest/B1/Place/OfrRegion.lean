/-
  LeanVM.Guest.B1.Place.OfrRegion

  The cursor words of open_stacked's `opening_fold_round` calls lie in the callees' words.
-/

module

public import LeanVM.Guest.B1.Place.OsCallsOk

/-!
# The fold rounds' words, in the callees' words

A round's meaning at `b > 0` bits reads its nonce, which the returns do not fix, so the memory
facts alone do not place it. Instead the body runs on the memory restricted to the callees' words
(`restrictL rd M`, undefined elsewhere): a round's reads succeed there only inside `M`.
`ofrC M`: the call relation recording that; `osCallsOk_ofr`: the body's calls hold at it on the
restricted memory, so `osBodyA_honest` there gives each round's region.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- The memory `rd` restricted to the region of `M`. -/
noncomputable def restrictL (rd : Reader) (M : Layout) : Reader := fun A ↦
  open Classical in if ∃ i, A = addressOfIndex i ∧ RegionL M i then rd A else none

theorem memL_restrictL {rd : Reader} {M : Layout} (h : MemL rd M) : MemL (restrictL rd M) M := by
  intro q hq k hk
  refine ⟨(h q hq k hk).1, ?_⟩
  have e : (ofK (addressOfIndex q.1)).limb 0 * addressOfIndex k = addressOfIndex (q.1 + k) :=
    Main.addr_ofK _ _
  rw [e]
  have := (h q hq k hk).2
  rw [e] at this
  simp only [restrictL]
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨q.1 + k, rfl, q, hq, by omega, by omega⟩)]
  exact this

theorem readsAt_restrictL {rd : Reader} {M : Layout} {p : E} {ws : List E}
    (h : ReadsAt (restrictL rd M) p ws) : ∀ t < ws.length, ∃ i,
      p.limb 0 * addressOfIndex t = addressOfIndex i ∧ RegionL M i := by
  intro t ht
  have h2 := (h t ht).2
  simp only [restrictL] at h2
  split at h2
  · next hx => exact hx
  · exact absurd h2 (by simp)

theorem readsAt_restrictL_of {rd : Reader} {M : Layout} {p : E} {ws : List E}
    (h : ReadsAt rd p ws) (hreg : ∀ t < ws.length, ∃ i,
      p.limb 0 * addressOfIndex t = addressOfIndex i ∧ RegionL M i) :
    ReadsAt (restrictL rd M) p ws := fun t ht ↦ by
  refine ⟨(h t ht).1, ?_⟩
  simp only [restrictL]
  rw [ite_eq_left_of_eq_true _ _ (eq_true (hreg t ht))]
  exact (h t ht).2

/-- The call relation recording the rounds' regions. -/
def ofrC (M : Layout) : CallRel := fun f a _ ↦
  ∀ b, osKindOf f = some (.ofr b) → RegPtrs [(7, roundLen b)] a (RegionL M)

theorem ofrC_of_kind {M : Layout} {f : String} {K : OsKind} (hK : osKindOf f = some K)
    (hne : ∀ b, K ≠ .ofr b) (a r : List E) : ofrC M f a r := fun b hb ↦
  absurd (hK.symm.trans hb) (by simpa using hne b)

theorem ofrC_of_none {M : Layout} {f : String} (hK : osKindOf f = none) (a r : List E) :
    ofrC M f a r := fun b hb ↦ absurd (hK.symm.trans hb) (by simp)

theorem dispC_none {M : Layout} {rd : Reader} {c : OsCfg} {ri l : ℕ} (hN : OsNames c ri)
    (hl : l < c.levels.length) (f : OsLv → String) (hf : osKindOf (f (lvAt c l)) = none)
    (a r : List E) : DispC (ofrC M) rd (ofK (addressOfIndex ri)) ((c.lvAt l).map f) a r :=
  dispC_rate (hN.rate l hl) hN.ri4 f (ofrC_of_none hf a r)

/-- **The body's calls at `ofrC M`** on a memory restricted to `M`. -/
theorem osCallsOk_ofr {c : OsCfg} {tr : OsTr} {ri : ℕ} (hN : OsNames c ri) (A : OsAt)
    (M : Layout) (rd : Reader) :
    OsCallsOk (ofrC M) (restrictL rd M) (ofK (addressOfIndex ri)) A c tr := by
  have hfold0 : FoldCallC (ofrC M) (restrictL rd M) none 0 (ofK (addressOfIndex ri)) :=
    fun σ _ args rets _ _ ↦ ofrC_of_kind osKindOf_fold (by simp) (args.map σ) (rets.map σ)
  refine ⟨hfold0, fun i hi ↦ ⟨?_, fun _ _ _ ↦ ofrC_of_kind osKindOf_can (by simp) _ _,
    fun hne _ _ _ ↦ ofrC_of_kind (hN.ood i hi hne) (by simp) _ _,
    fun _ _ _ ↦ ofrC_of_kind (hN.grind i hi) (by simp) _ _,
    fun _ _ _ _ _ ↦ ofrC_of_kind hN.fm (by simp) _ _, dispC_none hN hi _ (hN.pos i hi) _ _,
    ofrC_of_kind (hN.rw i hi) (by simp) _ _, dispC_none hN hi _ (hN.q i hi) _ _⟩,
    fun i hi ↦ dispC_none hN hi _ (hN.res i hi) _ _, ofrC_of_kind hN.ffm (by simp) _ _⟩
  unfold osFoldNames
  split
  · next hg => rw [hN.fold0 i hi hg]; exact hfold0
  · next hg =>
    intro σ hR args rets _ hmf
    have hl : ri < ((c.lvAt i).map fun l ↦ osFoldRoundName l.foldGrind).length := by
      rw [List.length_map, (hN.rate i hi).1]; exact hN.ri4
    refine ⟨ri, hl, hR, ?_⟩
    rw [List.getElem_map, ← List.getD_eq_getElem _ default (by simpa using hl), (hN.rate i hi).2]
    intro b hb
    rw [hN.ofr i hi hg] at hb
    cases hb
    match h : args.map σ, hmf with
    | [f0, f1, f2, f3, f4, w0, w1, cur, c0, c1, c2], ⟨nonce, d0, d2, hrd, _⟩ =>
      intro q hq t ht
      simp only [List.mem_singleton] at hq
      subst hq
      have := readsAt_restrictL hrd t (by rw [roundWords_length]; exact ht)
      simpa using this

end
end LeanVM.Guest.B1
