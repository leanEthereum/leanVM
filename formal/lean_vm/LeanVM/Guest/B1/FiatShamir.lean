/-
  LeanVM.Guest.B1.FiatShamir

  B1 for the guest's compiled Fiat-Shamir functions: each relation is the run of the
  specification's program on the chain.
-/

module

public import LeanVM.Guest.B1.FsBlocks

/-!
# The compiled Fiat-Shamir functions

| function | meaning |
|---|---|
| `sumcheck_round4` (TRIAGE #25) | `sumcheckRoundPoly 4 claim none`, then a sample (V:1313) |
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `sumcheck_round4` -/

/-- A plain sumcheck round of `count` coefficients: read the round polynomial, sample the
challenge, and fold the claim to the polynomial at it (one round of `sumcheck`, V:1324). -/
def roundPoly (count : ℕ) (claim : E) (eq : Option E) : Prog (E × E) := do
  let message ← sumcheckRoundPoly count claim eq
  let challenge ← Prog.sampleE
  return (polyEval message challenge, challenge)

/-- **`sumcheck_round4`** (G:845-857; TRIAGE #25): from the state of `cv`, the three words at the
cursor are the round polynomial's `c0, c2, c3` (`sumcheckRoundPoly 4 claim none`, V:1313), the
run of the round returns the next claim and the challenge, and the function returns the new
state's cells, the cursor three words on, the claim and the challenge. -/
def MeaningSumcheckRound4 (rd : Reader) : List E → List E → Prop
  | [s0, s1, cur, claim], rets =>
      ∃ cv c0 c2 c3 claim' r cv', (s0, s1) = digestScalars cv ∧ ReadsAt rd cur [c0, c2, c3] ∧
        RunsTo (roundPoly 4 claim none) cv [c0, c2, c3] (claim', r) cv' ∧
        rets = [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ 3, claim', r]
  | _, _ => False

theorem runsTo_roundPoly4 (cv : Digest) (claim c0 c2 c3 : E) :
    RunsTo (roundPoly 4 claim none) cv [c0, c2, c3]
      (polyEval [c0, claim + (c2 + c3), c2, c3] (challengeOf (sqCv (obsAll cv [c0, c2, c3]))),
        challengeOf (sqCv (obsAll cv [c0, c2, c3]))) (sqCv (obsAll cv [c0, c2, c3])) := by
  have h1 := runsTo_readE cv c0
  have h2 := runsTo_readN (obsCv cv c0) [c2, c3]
  have h := (h1.bind (f := fun constant => do
      let tail ← Prog.readN 2
      return constant :: (claim + sumE tail) :: tail)
    (h2.bind (f := fun tail => (pure (c0 :: (claim + sumE tail) :: tail) : Prog (List E)))
      (runsTo_ret _ _))).bind (f := fun message => do
        let challenge ← Prog.sampleE
        return (polyEval message challenge, challenge))
    ((runsTo_sampleE _).bind (f := fun challenge => (pure (polyEval
      (c0 :: (claim + sumE [c2, c3]) :: [c2, c3]) challenge, challenge) : Prog (E × E)))
      (runsTo_ret _ _))
  refine h.of_eq rfl ?_ rfl
  simp only [sumE, List.foldl, zero_add]
  rfl

theorem find_sumcheck_round4 : coreProgram.find? "sumcheck_round4" = some Data.core6 :=
  Program.find?_of_indexOf? (j := 6) (by decide +kernel) rfl

theorem core6_body : Fn.body Data.core6 =
    [.atom (.copy (.n 4) (.n 0)), .atom (.copy (.n 5) (.n 1))] ++
    fsNextT (.n 4) (.n 5) (.n 2) 0 6 ++ fsNextT (.n 19) (.n 20) (.n 2) 1 21 ++
    fsNextT (.n 34) (.n 35) (.n 2) 2 36 ++
    [.atom (.add (.n 51) (.n 3) (.n 21)), .atom (.add (.n 52) (.n 51) (.n 36))] ++
    squeezeT (.n 49) (.n 50) 53 ++
    [.atom (.copy (.n 67) (.n 58)), .atom (.copy (.n 68) (.n 59)),
      .atom (.const (.n 69) (word 8 0 0)), .atom (.mul (.n 70) (.n 2) (.n 69)),
      .atom (.copy (.n 71) (.n 70)), .atom (.mul (.n 72) (.n 66) (.n 36)),
      .atom (.add (.n 73) (.n 21) (.n 72)), .atom (.mul (.n 74) (.n 66) (.n 73)),
      .atom (.add (.n 75) (.n 52) (.n 74)), .atom (.mul (.n 76) (.n 66) (.n 75)),
      .atom (.add (.n 77) (.n 6) (.n 76)), .atom (.copy (.n 78) (.n 66)),
      .ret [.n 67, .n 68, .n 71, .n 77, .n 78]] := rfl

theorem core6_params : Fn.params Data.core6 = [.n 0, .n 1, .n 2, .n 3] := rfl

theorem word_eight : word 8 0 0 = gen ^ 3 := word_two_pow (a := 3) (by decide)

theorem sumcheck_round4_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "sumcheck_round4" args rets ↔ MeaningSumcheckRound4 rd args rets := by
  rw [rel_iff_sem find_sumcheck_round4, core6_body, core6_params]
  simp only [holdsList_append, holds_fsNextT, holds_squeezeT, Stmt.HoldsList, Stmt.Holds,
    Atom.Holds, List.map_cons, List.map_nil]
  constructor
  · rintro ⟨σ, hp, h4, h5, ⟨hl0, cv, hcv, e0⟩, ⟨hl1, cv1, hcv1, e1⟩, ⟨hl2, cv2, hcv2, e2⟩, h51,
      h52, ⟨cv3, hcv3, e3⟩, h67, h68, h69, h70, h71, h72, h73, h74, h75, h76, h77, h78, hret⟩
    subst hp
    have f19 : σ (.n 19) = (digestScalars (absorbCv cv (σ (.n 6)) 1)).1 := e0 12 (by omega) (by omega)
    have f20 : σ (.n 20) = (digestScalars (absorbCv cv (σ (.n 6)) 1)).2 := e0 13 (by omega) (by omega)
    have f34 : σ (.n 34) = (digestScalars (absorbCv cv1 (σ (.n 21)) 1)).1 := e1 12 (by omega) (by omega)
    have f35 : σ (.n 35) = (digestScalars (absorbCv cv1 (σ (.n 21)) 1)).2 := e1 13 (by omega) (by omega)
    have f49 : σ (.n 49) = (digestScalars (absorbCv cv2 (σ (.n 36)) 1)).1 := e2 12 (by omega) (by omega)
    have f50 : σ (.n 50) = (digestScalars (absorbCv cv2 (σ (.n 36)) 1)).2 := e2 13 (by omega) (by omega)
    have f58 : σ (.n 58) = (digestScalars (absorbCv cv3 0 2)).1 := e3 5 (by omega)
    have f59 : σ (.n 59) = (digestScalars (absorbCv cv3 0 2)).2 := e3 6 (by omega)
    have f66 : σ (.n 66) = challengeOf (sqCv cv3) := e3 13 (by omega)
    have g1 : cv1 = obsCv cv (σ (.n 6)) :=
      digestScalars_injective (by rw [← hcv1, f19, f20]; rfl)
    have g2 : cv2 = obsCv cv1 (σ (.n 21)) :=
      digestScalars_injective (by rw [← hcv2, f34, f35]; rfl)
    have g3 : cv3 = obsCv cv2 (σ (.n 36)) :=
      digestScalars_injective (by rw [← hcv3, f49, f50]; rfl)
    rw [h4, h5] at hcv
    refine ⟨cv, σ (.n 6), σ (.n 21), σ (.n 36), _, _, _, hcv, ?_,
      runsTo_roundPoly4 cv (σ (.n 3)) _ _ _, ?_⟩
    · intro k hk
      simp only [List.length_cons, List.length_nil] at hk
      interval_cases k
      · exact hl0
      · exact hl1
      · exact hl2
    · rw [← hret, h67, h68, h71, h70, h69, word_eight, h77, h76, h75, h74, h73, h72, h52, h51,
        h78, f66, f58, f59, g3, g2, g1]
      simp only [obsAll, List.foldl, polyEval, List.foldr, zero_mul, zero_add, List.cons.injEq,
        and_true, absorbCv_sq, true_and]
      ring
  · intro hm
    obtain ⟨s0, s1, cur, claim, rfl⟩ : ∃ s0 s1 cur claim, args = [s0, s1, cur, claim] := by
      match args, hm with
      | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
    obtain ⟨cv, c0, c2, c3, claim', r, cv', hcv, hrd, hrun, hret⟩ := hm
    obtain ⟨hcl, hcv'⟩ := (runsTo_roundPoly4 cv claim c0 c2 c3).iff.mp hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hcl
    subst hcv' hret
    have hl : ∀ k (hk : k < 3), LoadHolds rd cur k [c0, c2, c3][k] := hrd
    set cv1 := obsCv cv c0
    set cv2 := obsCv cv1 c2
    set cv3 := obsCv cv2 c3
    set r := challengeOf (sqCv cv3)
    refine ⟨setl (setv (setl (setv (setl (setv (setl (setv (setl (Val.ofArgs [s0, s1, cur, claim])
      4 [s0, s1, c0]) 7 14 (fsVals c0 cv 1)) 21 [c2]) 22 14 (fsVals c2 cv1 1)) 36 [c3]) 37 14
      (fsVals c3 cv2 1)) 51 [claim + c2, claim + c2 + c3]) 53 14 (sqVals cv3)) 67
      [sqVals cv3 5, sqVals cv3 6, word 8 0 0, cur * word 8 0 0, cur * word 8 0 0, r * c3,
        c2 + r * c3, r * (c2 + r * c3), claim + c2 + c3 + r * (c2 + r * c3),
        r * (claim + c2 + c3 + r * (c2 + r * c3)), c0 + r * (claim + c2 + c3 + r * (c2 + r * c3)),
        r], ?_, ?_, ?_, ⟨?_, cv, ?_, ?_⟩, ⟨?_, cv1, ?_, ?_⟩, ⟨?_, cv2, ?_, ?_⟩, ?_, ?_,
      ⟨cv3, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try (intro k hk1 hk2)
    all_goals try (intro k hk1)
    all_goals (try b1_look)
    · exact hl 0 (by decide)
    · exact hcv
    · exact hl 1 (by decide)
    · show ((digestScalars (absorbCv cv c0 1)).1, (digestScalars (absorbCv cv c0 1)).2) = _
      rw [Prod.mk.eta]; rfl
    · exact hl 2 (by decide)
    · show ((digestScalars (absorbCv cv1 c2 1)).1, (digestScalars (absorbCv cv1 c2 1)).2) = _
      rw [Prod.mk.eta]; rfl
    · show ((digestScalars (absorbCv cv2 c3 1)).1, (digestScalars (absorbCv cv2 c3 1)).2) = _
      rw [Prod.mk.eta]; rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp only [sqVals, sqStateVals, absorbCv_sq, word_eight, obsAll, List.foldl, polyEval,
        List.foldr, zero_mul, zero_add, List.cons.injEq, and_true, true_and, r, cv3, cv2, cv1]
      ring


/-! ## `sumcheck_round5` -/

/-- **`sumcheck_round5`** (G:860-872; TRIAGE #26): an equality-mode round over the previous
challenge `e`: the four words at the cursor are `c1 .. c4` (`sumcheckRoundPoly 5 claim (some e)`,
V:1313), and the function returns the new state's cells, the cursor four words on, the next
claim and the challenge. -/
def MeaningSumcheckRound5 (rd : Reader) : List E → List E → Prop
  | [s0, s1, cur, claim, e], rets =>
      ∃ cv c1 c2 c3 c4 claim' r cv', (s0, s1) = digestScalars cv ∧
        ReadsAt rd cur [c1, c2, c3, c4] ∧
        RunsTo (roundPoly 5 claim (some e)) cv [c1, c2, c3, c4] (claim', r) cv' ∧
        rets = [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ 4, claim', r]
  | _, _ => False

theorem runsTo_roundPoly5 (cv : Digest) (claim e c1 c2 c3 c4 : E) :
    RunsTo (roundPoly 5 claim (some e)) cv [c1, c2, c3, c4]
      (polyEval [claim + e * (c1 + c2 + c3 + c4), c1, c2, c3, c4]
        (challengeOf (sqCv (obsAll cv [c1, c2, c3, c4]))),
        challengeOf (sqCv (obsAll cv [c1, c2, c3, c4]))) (sqCv (obsAll cv [c1, c2, c3, c4])) := by
  have h2 := runsTo_readN cv [c1, c2, c3, c4]
  have h := (h2.bind (f := fun tail => (pure ((claim + e * sumE tail) :: tail) : Prog (List E)))
      (runsTo_ret _ _)).bind (f := fun message => do
        let challenge ← Prog.sampleE
        return (polyEval message challenge, challenge))
    ((runsTo_sampleE _).bind (f := fun challenge => (pure (polyEval
      ((claim + e * sumE [c1, c2, c3, c4]) :: [c1, c2, c3, c4]) challenge, challenge) :
        Prog (E × E))) (runsTo_ret _ _))
  refine h.of_eq rfl ?_ rfl
  simp only [sumE, List.foldl, zero_add]

theorem find_sumcheck_round5 : coreProgram.find? "sumcheck_round5" = some Data.core7 :=
  Program.find?_of_indexOf? (j := 7) (by decide +kernel) rfl

theorem core7_params : Fn.params Data.core7 = [.n 0, .n 1, .n 2, .n 3, .n 4] := rfl

theorem core7_body : Fn.body Data.core7 =
    [.atom (.copy (.n 5) (.n 0)), .atom (.copy (.n 6) (.n 1))] ++
    fsNextT (.n 5) (.n 6) (.n 2) 0 7 ++ fsNextT (.n 20) (.n 21) (.n 2) 1 22 ++
    fsNextT (.n 35) (.n 36) (.n 2) 2 37 ++ fsNextT (.n 50) (.n 51) (.n 2) 3 52 ++
    squeezeT (.n 65) (.n 66) 67 ++
    [.atom (.add (.n 81) (.n 7) (.n 22)), .atom (.add (.n 82) (.n 81) (.n 37)),
      .atom (.add (.n 83) (.n 82) (.n 52)), .atom (.mul (.n 84) (.n 4) (.n 83)),
      .atom (.add (.n 85) (.n 3) (.n 84)), .atom (.copy (.n 86) (.n 72)),
      .atom (.copy (.n 87) (.n 73)), .atom (.const (.n 88) (word 16 0 0)),
      .atom (.mul (.n 89) (.n 2) (.n 88)), .atom (.copy (.n 90) (.n 89)),
      .atom (.mul (.n 91) (.n 80) (.n 52)), .atom (.add (.n 92) (.n 37) (.n 91)),
      .atom (.mul (.n 93) (.n 80) (.n 92)), .atom (.add (.n 94) (.n 22) (.n 93)),
      .atom (.mul (.n 95) (.n 80) (.n 94)), .atom (.add (.n 96) (.n 7) (.n 95)),
      .atom (.mul (.n 97) (.n 80) (.n 96)), .atom (.add (.n 98) (.n 85) (.n 97)),
      .atom (.copy (.n 99) (.n 80)), .ret [.n 86, .n 87, .n 90, .n 98, .n 99]] := rfl

theorem word_sixteen : word 16 0 0 = gen ^ 4 := word_two_pow (a := 4) (by decide)

theorem sumcheck_round5_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "sumcheck_round5" args rets ↔ MeaningSumcheckRound5 rd args rets := by
  rw [rel_iff_sem find_sumcheck_round5, core7_body, core7_params]
  simp only [holdsList_append, holds_fsNextT, holds_squeezeT, Stmt.HoldsList, Stmt.Holds,
    Atom.Holds, List.map_cons, List.map_nil]
  constructor
  · rintro ⟨σ, hp, h5, h6, ⟨hl0, cv, hcv, e0⟩, ⟨hl1, cv1, hcv1, e1⟩, ⟨hl2, cv2, hcv2, e2⟩,
      ⟨hl3, cv3, hcv3, e3⟩, ⟨cv4, hcv4, e4⟩, h81, h82, h83, h84, h85, h86, h87, h88, h89, h90,
      h91, h92, h93, h94, h95, h96, h97, h98, h99, hret⟩
    subst hp
    have f20 : σ (.n 20) = (digestScalars (absorbCv cv (σ (.n 7)) 1)).1 := e0 12 (by omega) (by omega)
    have f21 : σ (.n 21) = (digestScalars (absorbCv cv (σ (.n 7)) 1)).2 := e0 13 (by omega) (by omega)
    have f35 : σ (.n 35) = (digestScalars (absorbCv cv1 (σ (.n 22)) 1)).1 := e1 12 (by omega) (by omega)
    have f36 : σ (.n 36) = (digestScalars (absorbCv cv1 (σ (.n 22)) 1)).2 := e1 13 (by omega) (by omega)
    have f50 : σ (.n 50) = (digestScalars (absorbCv cv2 (σ (.n 37)) 1)).1 := e2 12 (by omega) (by omega)
    have f51 : σ (.n 51) = (digestScalars (absorbCv cv2 (σ (.n 37)) 1)).2 := e2 13 (by omega) (by omega)
    have f65 : σ (.n 65) = (digestScalars (absorbCv cv3 (σ (.n 52)) 1)).1 := e3 12 (by omega) (by omega)
    have f66 : σ (.n 66) = (digestScalars (absorbCv cv3 (σ (.n 52)) 1)).2 := e3 13 (by omega) (by omega)
    have f72 : σ (.n 72) = (digestScalars (absorbCv cv4 0 2)).1 := e4 5 (by omega)
    have f73 : σ (.n 73) = (digestScalars (absorbCv cv4 0 2)).2 := e4 6 (by omega)
    have f80 : σ (.n 80) = challengeOf (sqCv cv4) := e4 13 (by omega)
    have g1 : cv1 = obsCv cv (σ (.n 7)) := digestScalars_injective (by rw [← hcv1, f20, f21]; rfl)
    have g2 : cv2 = obsCv cv1 (σ (.n 22)) := digestScalars_injective (by rw [← hcv2, f35, f36]; rfl)
    have g3 : cv3 = obsCv cv2 (σ (.n 37)) := digestScalars_injective (by rw [← hcv3, f50, f51]; rfl)
    have g4 : cv4 = obsCv cv3 (σ (.n 52)) := digestScalars_injective (by rw [← hcv4, f65, f66]; rfl)
    rw [h5, h6] at hcv
    refine ⟨cv, σ (.n 7), σ (.n 22), σ (.n 37), σ (.n 52), _, _, _, hcv, ?_,
      runsTo_roundPoly5 cv (σ (.n 3)) (σ (.n 4)) _ _ _ _, ?_⟩
    · intro k hk
      simp only [List.length_cons, List.length_nil] at hk
      interval_cases k
      · exact hl0
      · exact hl1
      · exact hl2
      · exact hl3
    · rw [← hret, h86, h87, h90, h89, h88, word_sixteen, h98, h97, h96, h95, h94, h93, h92, h91,
        h85, h84, h83, h82, h81, h99, f80, f72, f73, g4, g3, g2, g1]
      simp only [obsAll, List.foldl, polyEval, List.foldr, zero_mul, zero_add, List.cons.injEq,
        and_true, absorbCv_sq, true_and]
      ring
  · intro hm
    obtain ⟨s0, s1, cur, claim, e, rfl⟩ : ∃ s0 s1 cur claim e,
        args = [s0, s1, cur, claim, e] := by
      match args, hm with
      | [a, b, c, d, f], _ => exact ⟨a, b, c, d, f, rfl⟩
    obtain ⟨cv, c1, c2, c3, c4, claim', r, cv', hcv, hrd, hrun, hret⟩ := hm
    obtain ⟨hcl, hcv'⟩ := (runsTo_roundPoly5 cv claim e c1 c2 c3 c4).iff.mp hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hcl
    subst hcv' hret
    have hl : ∀ k (hk : k < 4), LoadHolds rd cur k [c1, c2, c3, c4][k] := hrd
    set cv1 := obsCv cv c1
    set cv2 := obsCv cv1 c2
    set cv3 := obsCv cv2 c3
    set cv4 := obsCv cv3 c4
    set r := challengeOf (sqCv cv4)
    set c0 := claim + e * (c1 + c2 + c3 + c4)
    refine ⟨setl (setv (setv (setl (setv (setl (setv (setl (setv (setl
      (Val.ofArgs [s0, s1, cur, claim, e]) 5 [s0, s1, c1]) 8 14 (fsVals c1 cv 1)) 22 [c2]) 23 14
      (fsVals c2 cv1 1)) 37 [c3]) 38 14 (fsVals c3 cv2 1)) 52 [c4]) 53 14 (fsVals c4 cv3 1)) 67
      14 (sqVals cv4)) 81
      [c1 + c2, c1 + c2 + c3, c1 + c2 + c3 + c4, e * (c1 + c2 + c3 + c4), c0, sqVals cv4 5,
        sqVals cv4 6, word 16 0 0, cur * word 16 0 0, cur * word 16 0 0, r * c4, c3 + r * c4,
        r * (c3 + r * c4), c2 + r * (c3 + r * c4), r * (c2 + r * (c3 + r * c4)),
        c1 + r * (c2 + r * (c3 + r * c4)), r * (c1 + r * (c2 + r * (c3 + r * c4))),
        c0 + r * (c1 + r * (c2 + r * (c3 + r * c4))), r], ?_, ?_⟩
    · b1_look
    refine ⟨?_, ?_, ⟨?_, cv, ?_, ?_⟩, ⟨?_, cv1, ?_, ?_⟩, ⟨?_, cv2, ?_, ?_⟩, ⟨?_, cv3, ?_, ?_⟩,
      ⟨cv4, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try (intro k hk1 hk2)
    all_goals try (intro k hk1)
    all_goals (try b1_look)
    · exact hl 0 (by decide)
    · exact hcv
    · exact hl 1 (by decide)
    · show ((digestScalars (absorbCv cv c1 1)).1, (digestScalars (absorbCv cv c1 1)).2) = _
      rw [Prod.mk.eta]; rfl
    · exact hl 2 (by decide)
    · show ((digestScalars (absorbCv cv1 c2 1)).1, (digestScalars (absorbCv cv1 c2 1)).2) = _
      rw [Prod.mk.eta]; rfl
    · exact hl 3 (by decide)
    · show ((digestScalars (absorbCv cv2 c3 1)).1, (digestScalars (absorbCv cv2 c3 1)).2) = _
      rw [Prod.mk.eta]; rfl
    · show ((digestScalars (absorbCv cv3 c4 1)).1, (digestScalars (absorbCv cv3 c4 1)).2) = _
      rw [Prod.mk.eta]; rfl
    iterate 6 (· rfl)
    simp only [sqVals, sqStateVals, absorbCv_sq, word_sixteen, obsAll, List.foldl, polyEval,
      List.foldr, zero_mul, zero_add, List.cons.injEq, and_true, true_and, r, cv4, cv3, cv2, cv1, c0]
    ring

/-! ## `opening_fold` -/

/-- One fold round of a WHIR level (`foldRounds`, V:1678): sample the challenge, fold the
running quadratic `quad` at it, read the next quadratic (`sumcheckRoundPoly 3 _ none`). The
challenge, the folded claim and the next quadratic. -/
def foldStep (quad : List E) : Prog (E × E × List E) := do
  let challenge ← Prog.sampleE
  let target := polyEval quad challenge
  let next ← sumcheckRoundPoly 3 target none
  return (challenge, target, next)

/-- `foldRounds` is `foldStep` round after round. -/
theorem foldRounds_succ (n : ℕ) (s : WhirState) (levelFolds : List E) :
    foldRounds (n + 1) s levelFolds = (do
      let (c, target, quad) ← foldStep s.quad
      foldRounds n { s with target, quad, folds := s.folds ++ [c] } (levelFolds ++ [c])) := by
  simp only [foldRounds, foldStep, prog_bind_eq, prog_pure_eq]
  rfl

theorem runsTo_foldStep (cv : Digest) (c0 c1 c2 d0 d2 : E) :
    RunsTo (foldStep [c0, c1, c2]) cv [d0, d2]
      (challengeOf (sqCv cv), polyEval [c0, c1, c2] (challengeOf (sqCv cv)),
        [d0, polyEval [c0, c1, c2] (challengeOf (sqCv cv)) + d2, d2])
      (obsAll (sqCv cv) [d0, d2]) := by
  have h := (runsTo_sampleE cv).bind (f := fun challenge => do
      let target := polyEval [c0, c1, c2] challenge
      let next ← sumcheckRoundPoly 3 target none
      return (challenge, target, next))
    (((runsTo_readE (sqCv cv) d0).bind (f := fun constant => do
        let tail ← Prog.readN 1
        return constant :: (polyEval [c0, c1, c2] (challengeOf (sqCv cv)) + sumE tail) :: tail)
      ((runsTo_readN (obsCv (sqCv cv) d0) [d2]).bind
        (f := fun tail => (pure (d0 :: (polyEval [c0, c1, c2] (challengeOf (sqCv cv)) + sumE tail)
          :: tail) : Prog (List E))) (runsTo_ret _ _))).bind
      (f := fun next => (pure (challengeOf (sqCv cv), polyEval [c0, c1, c2] (challengeOf (sqCv cv)),
        next) : Prog (E × E × List E))) (runsTo_ret _ _))
  refine h.of_eq rfl ?_ rfl
  simp only [sumE, List.foldl, zero_add]

/-- **`opening_fold`** (G:917-924; TRIAGE #31): one fold round (`foldStep`) from the state of
`cv` over the quadratic `c0, c1, c2`, the next quadratic's `c0, c2` read at the cursor; the
function returns the new state's cells, the cursor two words on, the folded claim, the two
words read and the challenge. -/
def MeaningOpeningFold (rd : Reader) : List E → List E → Prop
  | [s0, s1, cur, c0, c1, c2], rets =>
      ∃ cv d0 d2 r t q cv', (s0, s1) = digestScalars cv ∧ ReadsAt rd cur [d0, d2] ∧
        RunsTo (foldStep [c0, c1, c2]) cv [d0, d2] (r, t, q) cv' ∧
        rets = [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ 2, t, d0, d2, r]
  | _, _ => False

theorem find_opening_fold : coreProgram.find? "opening_fold" = some Data.core8 :=
  Program.find?_of_indexOf? (j := 8) (by decide +kernel) rfl

theorem core8_params : Fn.params Data.core8 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] := rfl

theorem core8_body : Fn.body Data.core8 =
    [.atom (.copy (.n 6) (.n 0)), .atom (.copy (.n 7) (.n 1))] ++
    squeezeT (.n 6) (.n 7) 8 ++
    [.atom (.mul (.n 22) (.n 5) (.n 21)), .atom (.add (.n 23) (.n 22) (.n 4)),
      .atom (.mul (.n 24) (.n 23) (.n 21)), .atom (.add (.n 25) (.n 24) (.n 3))] ++
    fsNextT (.n 13) (.n 14) (.n 2) 0 26 ++ fsNextT (.n 39) (.n 40) (.n 2) 1 41 ++
    [.atom (.copy (.n 56) (.n 54)), .atom (.copy (.n 57) (.n 55)),
      .atom (.const (.n 58) (word 4 0 0)), .atom (.mul (.n 59) (.n 2) (.n 58)),
      .atom (.copy (.n 60) (.n 59)), .atom (.copy (.n 61) (.n 25)), .atom (.copy (.n 62) (.n 26)),
      .atom (.copy (.n 63) (.n 41)), .atom (.copy (.n 64) (.n 21)),
      .ret [.n 56, .n 57, .n 60, .n 61, .n 62, .n 63, .n 64]] := rfl

theorem word_four : word 4 0 0 = gen ^ 2 := word_two_pow (a := 2) (by decide)

theorem opening_fold_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "opening_fold" args rets ↔ MeaningOpeningFold rd args rets := by
  rw [rel_iff_sem find_opening_fold, core8_body, core8_params]
  simp only [holdsList_append, holds_fsNextT, holds_squeezeT, Stmt.HoldsList, Stmt.Holds,
    Atom.Holds, List.map_cons, List.map_nil]
  constructor
  · rintro ⟨σ, hp, h6, h7, ⟨cv, hcv, e0⟩, h22, h23, h24, h25, ⟨hl0, cv1, hcv1, e1⟩,
      ⟨hl1, cv2, hcv2, e2⟩, h56, h57, h58, h59, h60, h61, h62, h63, h64, hret⟩
    subst hp
    have f13 : σ (.n 13) = (digestScalars (absorbCv cv 0 2)).1 := e0 5 (by omega)
    have f14 : σ (.n 14) = (digestScalars (absorbCv cv 0 2)).2 := e0 6 (by omega)
    have f21 : σ (.n 21) = challengeOf (sqCv cv) := e0 13 (by omega)
    have f39 : σ (.n 39) = (digestScalars (absorbCv cv1 (σ (.n 26)) 1)).1 := e1 12 (by omega) (by omega)
    have f40 : σ (.n 40) = (digestScalars (absorbCv cv1 (σ (.n 26)) 1)).2 := e1 13 (by omega) (by omega)
    have f54 : σ (.n 54) = (digestScalars (absorbCv cv2 (σ (.n 41)) 1)).1 := e2 12 (by omega) (by omega)
    have f55 : σ (.n 55) = (digestScalars (absorbCv cv2 (σ (.n 41)) 1)).2 := e2 13 (by omega) (by omega)
    have g1 : cv1 = sqCv cv := digestScalars_injective (by rw [← hcv1, f13, f14]; rfl)
    have g2 : cv2 = obsCv cv1 (σ (.n 26)) := digestScalars_injective (by rw [← hcv2, f39, f40]; rfl)
    rw [h6, h7] at hcv
    refine ⟨cv, σ (.n 26), σ (.n 41), _, _, _, _, hcv, ?_,
      runsTo_foldStep cv (σ (.n 3)) (σ (.n 4)) (σ (.n 5)) _ _, ?_⟩
    · intro k hk
      simp only [List.length_cons, List.length_nil] at hk
      interval_cases k
      · exact hl0
      · exact hl1
    · rw [← hret, h56, h57, h60, h59, h58, word_four, h61, h25, h24, h23, h22, h62, h63, h64,
        f21, f54, f55, g2, g1, absorbCv_one]
      simp only [obsAll, List.foldl, polyEval, List.foldr, zero_mul, zero_add]
  · intro hm
    obtain ⟨s0, s1, cur, c0, c1, c2, rfl⟩ : ∃ s0 s1 cur c0 c1 c2,
        args = [s0, s1, cur, c0, c1, c2] := by
      match args, hm with
      | [a, b, c, d, f, g], _ => exact ⟨a, b, c, d, f, g, rfl⟩
    obtain ⟨cv, d0, d2, r, t, q, cv', hcv, hrd, hrun, hret⟩ := hm
    obtain ⟨hcl, hcv'⟩ := (runsTo_foldStep cv c0 c1 c2 d0 d2).iff.mp hrun
    simp only [Prod.mk.injEq] at hcl
    obtain ⟨rfl, rfl, rfl⟩ := hcl
    subst hcv' hret
    have hl : ∀ k (hk : k < 2), LoadHolds rd cur k [d0, d2][k] := hrd
    set cv1 := sqCv cv
    set r := challengeOf cv1
    set cv2 := obsCv cv1 d0
    refine ⟨setl (setv (setl (setv (setl (setv (setl (Val.ofArgs [s0, s1, cur, c0, c1, c2]) 6
      [s0, s1]) 8 14 (sqVals cv)) 22 [c2 * r, c2 * r + c1, (c2 * r + c1) * r,
        (c2 * r + c1) * r + c0, d0]) 27 14 (fsVals d0 cv1 1)) 41 [d2]) 42 14 (fsVals d2 cv2 1)) 56
      [fsVals d2 cv2 1 12, fsVals d2 cv2 1 13, word 4 0 0, cur * word 4 0 0, cur * word 4 0 0,
        (c2 * r + c1) * r + c0, d0, d2, r], ?_, ?_⟩
    · b1_look
    refine ⟨?_, ?_, ⟨cv, ?_, ?_⟩, ?_, ?_, ?_, ?_, ⟨?_, cv1, ?_, ?_⟩, ⟨?_, cv2, ?_, ?_⟩, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try (intro k hk1 hk2)
    all_goals try (intro k hk1)
    all_goals (try b1_look)
    · exact hcv
    · rfl
    · rfl
    · exact hl 0 (by decide)
    · show ((digestScalars (absorbCv cv 0 2)).1, (digestScalars (absorbCv cv 0 2)).2) = _
      rw [Prod.mk.eta]; rfl
    · exact hl 1 (by decide)
    · show ((digestScalars (absorbCv cv1 d0 1)).1, (digestScalars (absorbCv cv1 d0 1)).2) = _
      rw [Prod.mk.eta]; rfl
    · rfl
    · simp only [fsVals, absorbCv_one, word_four, obsAll, List.foldl, polyEval, List.foldr,
        zero_mul, zero_add, r, cv2, cv1]

/-! ## `assert_canonical` -/

/-- **`assert_canonical`** (G:451-457; TRIAGE #2): the word is canonical (`IsCanonical128`),
and the function returns `0`. -/
def MeaningAssertCanonical : List E → List E → Prop
  | [w], rets => IsCanonical128 w ∧ rets = [0]
  | _, _ => False

theorem find_assert_canonical : coreProgram.find? "assert_canonical" = some Data.core1 :=
  Program.find?_of_indexOf? (j := 1) (by decide +kernel) rfl

theorem core1_body : Fn.body Data.core1 =
    canonicalLimbsT (.n 0) 1 ++ [.atom (.const (.n 5) (word 0 0 0)), .ret [.n 5]] := rfl

theorem assert_canonical_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "assert_canonical" args rets ↔ MeaningAssertCanonical args rets := by
  rw [rel_iff_sem find_assert_canonical, core1_body, show Fn.params Data.core1 = [.n 0] from rfl]
  simp only [holdsList_append, holds_canonicalLimbsT, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    List.map_cons, List.map_nil, word_zero]
  constructor
  · rintro ⟨σ, rfl, ⟨hc, -⟩, h5, hret⟩
    exact ⟨hc, by rw [← hret, h5]⟩
  · intro hm
    obtain ⟨w, rfl⟩ : ∃ w, args = [w] := by
      match args, hm with
      | [a], _ => exact ⟨a, rfl⟩
    obtain ⟨hc, rfl⟩ := hm
    refine ⟨setl (Val.ofArgs [w]) 1 [ofK (w.limb 0), w + ofK (w.limb 0), word 1 0 1,
      ofK (w.limb 1), 0], ?_, ⟨hc, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    all_goals b1_look

end
end LeanVM.Guest.B1
