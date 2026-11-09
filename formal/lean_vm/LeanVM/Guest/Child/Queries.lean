/-
  LeanVM.Guest.Child.Queries

  The query steps of the verifier's run on an honest proof, with Keccak: each opens one committed
  word's tree, at positions below its leaf count, with the honest paths.
-/

module

public import LeanVM.Guest.Child.Range
public import LeanVM.Protocol.WithHashBridge
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.AcceptableChild

/-!
# The honest proof's query steps

`queriesOf_proveFrom`: `run_proveFrom`'s simulation, for the query steps `Limits.queryStepsOf`
lists. From a history whose strategy wins, the verifier's run on the honest prover's output opens,
at each query step, the tree of one committed word of height `ht` at positions `ps` with the
openings `openingAt keccak256 ht word` of those positions; with `InRange`, every position is below
`2^ht`.
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash

@[expose] public section

/-- A query step of honest openings: one tree of height `ht`, positions below `2^ht`. -/
def HonestBatch (b : ℕ × List (ℕ × Opening)) : Prop :=
  ∃ (ht : ℕ) (word : Word) (ps : List ℕ), b = (ht, ps.zip (ps.map (openingAt keccak256 ht word))) ∧ ∀ q ∈ ps, q < 2 ^ ht

theorem zip_map_append {β γ : Type} (ps : List β) (f : β → γ) (rest : List γ) :
    ps.zip (ps.map f ++ rest) = ps.zip (ps.map f) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih]

/-- **The honest proof's query steps are honest batches.** -/
theorem queriesOf_proveFrom (S : Strategy) (fuel : ℕ) :
    ∀ (p : VerifierProgram Bool) (h : List Ev) (sp : Sponge) (xs : List E) (os : List (List Opening))
      (restS : List E) (restO : List (List Opening)),
      S.AcceptsFrom p h → (∀ c ∈ commits h, WellShaped c.2.1 c.2.2) →
      InRange p ((commits h).map (·.1)) (fun _ _ ↦ True) →
      proveFrom keccak256 keccakF1600 S fuel p sp h = some (xs, os) →
      ∀ b ∈ Limits.queryStepsOf p ⟨sp, xs ++ restS, os ++ restO, rootsOf keccak256 (commits h)⟩,
        HonestBatch b := by
  intro p
  induction p with
  | ret b =>
    intro h sp xs os restS restO _ _ _ _ b hb
    simp [Limits.queryStepsOf] at hb
  | fail =>
    intro h sp xs os restS restO hacc
    exact absurd hacc id
  | read k ih =>
    intro h sp xs os restS restO hacc hws hir hp b hb
    simp only [proveFrom] at hp
    obtain ⟨t, ht, he⟩ := Option.map_eq_some_iff.mp hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hws' : ∀ c ∈ commits (h ++ [Ev.read (S.msg h)]), WellShaped c.2.1 c.2.2 := by
      simpa [commits_append, commits] using hws
    have hc : commits (h ++ [Ev.read (S.msg h)]) = commits h := by
      simp [commits_append, commits]
    simp only [List.cons_append, Limits.queryStepsOf] at hb
    refine ih _ _ _ t.1 t.2 restS restO hacc hws' (hc ▸ hir _) ht b ?_
    rw [hc]
    exact hb
  | sample k ih =>
    intro h sp xs os restS restO hacc hws hir hp b hb
    simp only [proveFrom] at hp
    have hc : commits (h ++ [Ev.sample (squeezeI keccakF1600 sp).1]) = commits h := by
      simp [commits_append, commits]
    have hws' : ∀ c ∈ commits (h ++ [Ev.sample (squeezeI keccakF1600 sp).1]),
        WellShaped c.2.1 c.2.2 := by
      rw [hc]; exact hws
    simp only [Limits.queryStepsOf] at hb
    refine ih _ _ _ xs os restS restO (hacc _) hws' (hc ▸ hir _) hp b ?_
    rw [hc]
    exact hb
  | grind bits k ih =>
    intro h sp xs os restS restO hacc hws hir hp b hb
    simp only [proveFrom] at hp
    split at hp
    · exact absurd hp (by simp)
    · rename_i n hn
      obtain ⟨t, ht, he⟩ := Option.map_eq_some_iff.mp hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hc : commits (h ++ [Ev.grind bits]) = commits h := by
        simp [commits_append, commits]
      have hws' : ∀ c ∈ commits (h ++ [Ev.grind bits]), WellShaped c.2.1 c.2.2 := by
        rw [hc]; exact hws
      have hpow := powOk_of_findNonce keccakF1600 hn
      simp only [List.cons_append, Limits.queryStepsOf] at hb
      rw [show powOk bits n (Id.run (squeeze keccakF1600 (Id.run (absorb keccakF1600 sp n dsPowNonce)))).1
        = true from hpow] at hb
      simp only [↓reduceIte] at hb
      refine ih _ _ t.1 t.2 restS restO hacc hws' (hc ▸ hir) ht b ?_
      rw [hc]
      exact hb
  | commit ht w k ih =>
    intro h sp xs os restS restO hacc hws hir hp b hb
    obtain ⟨hw, hacc⟩ := hacc
    simp only [proveFrom] at hp
    obtain ⟨t, htt, he⟩ := Option.map_eq_some_iff.mp hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hws' : ∀ c ∈ commits (h ++ [Ev.commit ht w (S.word h)]), WellShaped c.2.1 c.2.2 := by
      simp only [commits_append, commits, List.mem_append, List.mem_singleton]
      rintro c (hc | rfl)
      · exact hws c hc
      · exact hw
    have hdec : digestFromHalves ((digestHalves (treeRoot keccak256 ht (S.word h))).1,
        (digestHalves (treeRoot keccak256 ht (S.word h))).2) =
          some (treeRoot keccak256 ht (S.word h)) :=
      digestOfScalars_digestScalars _
    have hroots : rootsOf keccak256 (commits (h ++ [Ev.commit ht w (S.word h)])) =
        rootsOf keccak256 (commits h) ++ [(treeRoot keccak256 ht (S.word h), ht, w)] := by
      simp [rootsOf, commits_append, commits]
    have hcm : (commits (h ++ [Ev.commit ht w (S.word h)])).map (·.1) =
        (commits h).map (·.1) ++ [ht] := by
      simp [commits_append, commits]
    simp only [List.cons_append, Limits.queryStepsOf, hdec] at hb
    refine ih _ _ t.1 t.2 restS restO hacc hws' (hcm ▸ hir) htt b ?_
    rw [hroots]
    exact hb
  | query i ps k ih =>
    intro h sp xs os restS restO hacc hws hir hp b hb
    obtain ⟨rows, hans, hacc⟩ := hacc
    simp only [proveFrom] at hp
    split at hp
    · rename_i hc
      simp [answer, hc] at hans
    · rename_i ht w word hc
      obtain ⟨t, htt, he⟩ := Option.map_eq_some_iff.mp hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hrows : rows = ps.map fun q ↦ word (q % 2 ^ ht) := by
        simp only [answer, hc, Option.map_some, Option.some.injEq] at hans
        exact hans.symm
      subst hrows
      have hcq : commits (h ++ [Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))]) = commits h := by
        simp [commits_append, commits]
      have hws' : ∀ c ∈ commits (h ++ [Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))]),
          WellShaped c.2.1 c.2.2 := by
        rw [hcq]; exact hws
      have hw : WellShaped w word := hws _ (List.mem_of_getElem? hc)
      have hroot : (rootsOf keccak256 (commits h))[i]? = some (treeRoot keccak256 ht word, ht, w) := by
        simp [rootsOf, hc]
      have hopen := openPhase_openingAt keccak256 hw (height := ht) ps
      have hgi : ((commits h).map (·.1)).getD i 0 = ht := by
        simp [List.getD_eq_getElem?_getD, hc]
      simp only [Limits.queryStepsOf, hroot, List.cons_append, openPhase_eq_withHash,
        keccak256With_keccakF1600] at hb
      rw [show Id.run (openPhaseWithHash (m := Id) keccak256 (treeRoot keccak256 ht word) ht w ps
        (ps.map (openingAt keccak256 ht word))) =
          some (ps.map fun q ↦ word (q % 2 ^ ht)) from hopen] at hb
      simp only at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨ht, word, ps, rfl, fun q hq ↦ hgi ▸ hir.1 q hq⟩
      · refine ih _ _ _ t.1 t.2 restS restO hacc hws' (hcq ▸ hir.2 _) htt b ?_
        rw [hcq]
        exact hb

end
end LeanVM.Guest.Child
