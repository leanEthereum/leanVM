/-
  LeanVM.Guest.B1.Whir.Tail

  The template's tail rounds run the Spec's `tailRounds`.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Whir.TailSpec
public import LeanVM.Guest.B1.Whir.Level

/-!
# The tail rounds (G:1648-1666)

The last level's tail: `yrLog - 1` `opening_fold` rounds (`osFolds_sound`) then the closing
squeeze on the two waiting scalars, its challenge stored at `tail_challenges[yrLog - 1]`, the
final claim the quadratic at it; the unused entries zeroed. In the Spec that is `tailRounds yrLog`
(`tailRounds_eq`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- **The tail rounds** (G:1648-1666): from the guest's claim and quadratic, the `2(yrLog - 1)`
words at the cursor read, they run `tailRounds yrLog`; its challenges are stored at
`tail_challenges` (the returned pointer), the entries past them zero, its claim the state's. -/
theorem osTail_sound (hC : ∀ args rets, C "opening_fold" args rets → MeaningOpeningFold rd args rets)
    {c : OsCfg} {st : OsSt} (hy : 1 ≤ c.yrLog) (hfs : st.fs.length = 5) (hco : st.co < u128Bound)
    (hpad : PadOk σ (some (st.pad.getD 0))) (ws : WhirStateT) (hq : ws.quad = st.quad σ)
    (ht : ws.target = σ (.n st.t)) (hok : AllOk C rd σ (osTail c st).1) :
    ∃ (xs chs : List E) (F' : Fs), xs.length = 2 * (c.yrLog - 1) ∧ chs.length = c.yrLog ∧
      ReadsAt rd (st.cur σ) xs ∧
      RunsTo ((tailRoundsT c.yrLog ws.target ws.quad).bind fun r ↦ VerifierProgram.ret ([] ++
          r.1, r.2))
        (st.F σ) xs (chs, σ (.n (osTail c st).2.1.t)) F' ∧
      (∀ i (hi : i < chs.length), LoadHolds rd (σ (.n (osTail c st).2.2)) i chs[i]) ∧
      (∀ i, i < yrLogCap - c.yrLog → LoadHolds rd (σ (.n (osTail c st).2.2)) (c.yrLog + i) 0) := by
  obtain ⟨n, hn⟩ : ∃ n, c.yrLog = n + 1 := ⟨c.yrLog - 1, by omega⟩
  have hn1 : c.yrLog - 1 = n := by omega
  simp only [osTail, hn1] at hok ⊢
  simp only [allOk_append] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hF⟩, hCp⟩, hP0⟩, hP1⟩, hK⟩, hL⟩, hZ⟩ := hok
  obtain ⟨xs, chs, hxl, hcl, hrd, hrun, -, hfs2, -, hld⟩ :=
    osFolds_sound hC (st.k + 1) n 0 { st with k := st.k + 2 } ws [] hfs hco hq ht hF
  have hpad2 := (osFolds_state (st.k + 1) n 0 { st with k := st.k + 2 }).1
  rw [hpad2] at hK
  set f2 := (osFolds (st.k + 1) 0 n { st with k := st.k + 2 }).2 with hf2
  set j := f2.k
  set p := st.pad.getD 0
  obtain ⟨g0, g1, g2, g3, g4, hg⟩ := fold_args f2 hfs2
  obtain ⟨z1, z2, z3, z4⟩ := hpad
  simp only [hg, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, allOk_cons,
    allOk_nil, and_true, StmtOk, Atom.Holds, allOk_fsPackT, allOk_challengeT, Nat.zero_add,
    Nat.add_zero, Nat.reduceAdd] at hCp hP0 hP1 hK hL
  obtain ⟨e0, e1, e2, e3, e4⟩ := hCp
  obtain ⟨hKk, hch⟩ := hK
  obtain ⟨L42, m43, a44, m45, m46, a47⟩ := hL
  obtain ⟨-, -, hcanK, hout⟩ := keccakA_perm (rd := rd) hKk
  have cn0 := packed_cells hP0 (hcanK _ (by simp))
  have cn1 := packed_cells hP1 (hcanK _ (by simp))
  simp only [Nat.add_assoc, Nat.reduceAdd] at cn0 cn1
  have hS : permOf (List.map σ [V.n (j + 11), V.n (j + 13), V.n (j + 20), V.n (j + 22), V.n (p + 1),
      V.n (p + 2), V.n (p + 3), V.n (p + 4), V.n j, V.n (j + 1), V.n (j + 2), V.n (j + 3),
      V.n (j + 4)]) = (f2.F σ).perm := by
    rw [perm_eq_cells _ (by simp [OsSt.F])]
    simp [OsSt.F, OsSt.fsv, hg, pendCells, cn0.1, cn0.2, cn1.1, cn1.2, z1, z2, z3, z4, e0, e1, e2,
      e3, e4, dsObserve]
  rw [hS] at hout
  have o0 : σ (.n (j + 23)) = cellsOfState (f2.F σ).perm false 0 := by
    simpa [osRun] using outs_eq hout 0 (by simp [osRun])
  have o1 : σ (.n (j + 24)) = cellsOfState (f2.F σ).perm false 1 := by
    simpa [osRun] using outs_eq hout 1 (by simp [osRun])
  have hchv : σ (.n (j + 42)) = (f2.F σ).squeeze.1 := challengeT_value hch o0 o1
  have hclaim : σ (.n (j + 47)) = polyEval (f2.quad σ) (f2.F σ).squeeze.1 := by
    rw [a47, m46, m45, a44, m43, ← hchv]
    simp only [OsSt.quad, polyEval, List.foldr_cons, List.foldr_nil]
    ring
  -- the Spec's side
  have h2 : RunsTo (VerifierProgram.sampleChallenge.bind fun cc ↦ VerifierProgram.ret (([] ++ chs)
      ++ [cc],
      polyEval (f2.quad σ) cc)) (f2.F σ) ([] ++ []) (([] ++ chs) ++ [σ (.n (j + 42))],
      σ (.n (j + 47))) (f2.F σ).squeeze.2 := by
    rw [hchv, hclaim]
    exact RunsTo.bind' (runsTo_sampleE _) (runsTo_ret _ _)
  have h3 := RunsTo.bind' (f := fun pp : WhirStateT × List E ↦ VerifierProgram.sampleChallenge.bind
      fun cc ↦
    VerifierProgram.ret (pp.2 ++ [cc], polyEval pp.1.quad cc)) hrun h2
  have e := tailRounds_eq n ws.target ws.quad ws.folds ws.glued []
  refine ⟨xs, chs ++ [σ (.n (j + 42))], (f2.F σ).squeeze.2, by rw [hxl], by simp [hcl, hn], hrd, ?_, ?_, ?_⟩
  · rw [hn, e]
    exact RunsTo.of_eq h3 rfl (by simp) (by simp) rfl
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases h : i < chs.length
    · rw [List.getElem_append_left h]
      simpa using hld i h
    · have hi' : i = chs.length := by omega
      subst hi'
      rw [List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_singleton]
      rw [hcl]
      exact L42
  · intro i hi
    rw [allOk_flatten] at hZ
    have := hZ _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds] at this
    obtain ⟨hz, hl⟩ := this
    rw [hz, word_zero] at hl
    exact hl

end
end LeanVM.Guest.B1.Whir
