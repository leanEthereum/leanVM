/-
  LeanVM.Guest.B1.Tables.FlockLoops

  `verify_flock`'s two loops: `__loop81` squeezes the zerocheck's sampled challenges, `__loop82`
  runs its sampled rounds; each iteration's meaning, and the loop's.
-/

module

public import LeanVM.Guest.B1.Tables.FlockBody

/-!
# `__loop81` and `__loop82`

`fsNext_chain` and `squeeze_chain` read the Fiat-Shamir blocks as steps of the chain: from the
state `cv`, `fs_next` absorbs its word (`obsCv`), `squeeze` moves to `sqCv cv` and gives
`challengeOf (sqCv cv)`. `scStep` is one round of the zerocheck's equality-mode sumcheck
(`sumcheckRoundPoly 3 claim (some e)`, then the challenge, V:1313-1335).

`__loop81` at `x` (`L81Body`): row `x` of `flock_pts` holds the state, its squeeze's challenge is
at `zerocheck_r[x]` and the new state in row `x·g`. `__loop82` at `x` (`L82Body`): row `x` of
`flock_rounds` holds the state, the cursor and the claim, the round reads the cursor's two words
and takes its equality factor from `zerocheck_r[x·g^6]`, its challenge goes to
`zerocheck_chis[x]`, and row `x·g` holds what `scStep` gives and the cursor moved by two.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The Fiat-Shamir blocks as steps -/

section
variable {C : CallRel} {rd : Reader} {σ : Val}

theorem fsNext_chain {s0 s1 cur : V} {j b : ℕ} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (fsNextT s0 s1 cur j b) True kret) {cv : Digest}
    (hcv : (σ s0, σ s1) = digestScalars cv) :
    LoadHolds rd (σ cur) j (σ (.n b)) ∧
      (σ (.n (b + 13)), σ (.n (b + 14))) = digestScalars (obsCv cv (σ (.n b))) := by
  obtain ⟨⟨hl, cv', hcv', e⟩, -⟩ := (holds_fsNextT s0 s1 cur j b True kret).mp h
  obtain rfl := digestScalars_injective (hcv'.symm.trans hcv)
  have e12 := e 12 (by omega) (by omega)
  have e13 := e 13 (by omega) (by omega)
  rw [show b + 1 + 12 = b + 13 by omega] at e12
  rw [show b + 1 + 13 = b + 14 by omega] at e13
  exact ⟨hl, by rw [e12, e13]; rfl⟩

theorem squeeze_chain {s0 s1 : V} {b : ℕ} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (squeezeT s0 s1 b) True kret) {cv : Digest}
    (hcv : (σ s0, σ s1) = digestScalars cv) :
    (σ (.n (b + 5)), σ (.n (b + 6))) = digestScalars (sqCv cv) ∧
      σ (.n (b + 13)) = challengeOf (sqCv cv) := by
  obtain ⟨⟨cv', hcv', e⟩, -⟩ := (holds_squeezeT s0 s1 b True kret).mp h
  obtain rfl := digestScalars_injective (hcv'.symm.trans hcv)
  exact ⟨by rw [e 5 (by omega), e 6 (by omega)]; rfl, e 13 (by omega)⟩

end

/-- One round of the equality-mode sumcheck from the claim `s.1` and the state `s.2`: the
coefficients `g = (g₁, g₂)` read, the constant one `claim + e·(g₁ + g₂)`, the challenge, the next
claim and the state. -/
def scStep (e : E) (g : E × E) (s : E × Digest) : E × E × Digest :=
  let cv := obsCv (obsCv s.2 g.1) g.2
  let chi := challengeOf (sqCv cv)
  (chi, s.1 + e * (g.1 + g.2) + chi * (g.1 + chi * g.2), sqCv cv)

/-- One round of the plain-mode sumcheck: the coefficients `(c₀, c₂)` read, the linear one
`claim + c₂`. -/
def lcStep (g : E × E) (s : E × Digest) : E × E × Digest :=
  let cv := obsCv (obsCv s.2 g.1) g.2
  let r := challengeOf (sqCv cv)
  (r, g.1 + r * (s.1 + g.2 + r * g.2), sqCv cv)

/-! ## `__loop81` -/

/-- `__loop81` at `x`: row `x` of `pts` holds a state, the squeeze's challenge is at `zr[x]`, and
row `x·g` the new state. -/
def L81Body (rd : Reader) (pts zr x : E) : Prop :=
  ∃ cv : Digest, LoadHolds rd (pts * (x * x)) 0 (digestScalars cv).1 ∧
    LoadHolds rd (pts * (x * x)) 1 (digestScalars cv).2 ∧
    LoadHolds rd (zr * x) 0 (challengeOf (sqCv cv)) ∧
    LoadHolds rd (pts * (x * x)) 2 (digestScalars (sqCv cv)).1 ∧
    LoadHolds rd (pts * (x * x)) 3 (digestScalars (sqCv cv)).2

theorem loop81_step (rd : Reader) (N pts zr : E) (d : ℕ) (x : E) :
    coreProgram.relN rd (d + 1) "__loop81" (x :: [N, pts, zr]) [] ↔
      L81Body rd pts zr x ∧ IsInK (x * gen + N) ∧
        (x * gen + N ≠ 0 → coreProgram.relN rd d "__loop81" (x * gen :: [N, pts, zr]) []) := by
  rw [relN_succ_iff find_loop81, show Fn.params Data.core140 = [.n 0, .n 1, .n 2, .n 3] from rfl,
    core140_body, l81Body]
  simp only [holdsList_append, holds_squeezeT, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    List.map_cons, List.map_nil, and_true, word_gen]
  constructor
  · rintro ⟨σ, hp, h4, h5, l6, l7, ⟨cv, hcv, e⟩, h22, l21, l13, l14, h23, h24, h25, h26, h27,
      hK, hcall⟩
    simp only [List.cons.injEq] at hp
    obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hp
    have e5 : σ (.n 13) = (digestScalars (sqCv cv)).1 := e 5 (by omega)
    have e6 : σ (.n 14) = (digestScalars (sqCv cv)).2 := e 6 (by omega)
    have e13 : σ (.n 21) = challengeOf (sqCv cv) := e 13 (by omega)
    rw [h4] at h5
    rw [h5] at l6 l7 l13 l14
    rw [h22, e13] at l21
    rw [e5] at l13
    rw [e6] at l14
    refine ⟨⟨cv, ?_, ?_, l21, l13, l14⟩, by rwa [h25, h24, h23] at hK, fun hne => ?_⟩
    · rw [show σ (.n 6) = (digestScalars cv).1 from congrArg Prod.fst hcv] at l6; exact l6
    · rw [show σ (.n 7) = (digestScalars cv).2 from congrArg Prod.snd hcv] at l7; exact l7
    · have := hcall (by rwa [h25, h24, h23])
      rwa [h27, h26] at this
  · rintro ⟨⟨cv, l6, l7, l21, l13, l14⟩, hK, hcall⟩
    refine ⟨setl (Val.ofArgs [x, N, pts, zr]) 4 [x * x, pts * (x * x), (digestScalars cv).1,
      (digestScalars cv).2, sqVals cv 0, sqVals cv 1, sqVals cv 2, sqVals cv 3, sqVals cv 4,
      sqVals cv 5, sqVals cv 6, sqVals cv 7, sqVals cv 8, sqVals cv 9, sqVals cv 10, sqVals cv 11,
      sqVals cv 12, sqVals cv 13, zr * x, gen, x * gen, x * gen + N, gen, x * gen], ?_, ?_⟩
    · b1_look
    · refine ⟨?_, ?_, ?_, ?_, ⟨cv, ?_, fun k hk => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_⟩
      all_goals (try b1_look)
      · exact l6
      · exact l7
      · interval_cases k <;> b1_look
      · exact l21
      · exact l13
      · exact l14
      · exact hK
      · exact hcall

/-! ## `__loop82` -/

/-- `__loop82` at `x`: row `x` of `rnd` holds the state, the cursor and the claim, the round's
words are at the cursor, its equality factor at `zr[x·g^6]`, its challenge goes to `chis[x]`, and
row `x·g` holds `scStep`'s claim and state and the cursor two words on. -/
def L82Body (rd : Reader) (rnd zr chis x : E) : Prop :=
  ∃ (cv : Digest) (cur claim e g1 g2 : E),
    LoadHolds rd (rnd * (x * x * (x * x))) 0 (digestScalars cv).1 ∧
    LoadHolds rd (rnd * (x * x * (x * x))) 1 (digestScalars cv).2 ∧
    LoadHolds rd (rnd * (x * x * (x * x))) 2 cur ∧ LoadHolds rd (rnd * (x * x * (x * x))) 3 claim ∧
    LoadHolds rd (zr * x) 6 e ∧ LoadHolds rd cur 0 g1 ∧ LoadHolds rd cur 1 g2 ∧
    LoadHolds rd (chis * x) 0 (scStep e (g1, g2) (claim, cv)).1 ∧
    LoadHolds rd (rnd * (x * x * (x * x))) 4 (digestScalars (scStep e (g1, g2) (claim, cv)).2.2).1 ∧
    LoadHolds rd (rnd * (x * x * (x * x))) 5 (digestScalars (scStep e (g1, g2) (claim, cv)).2.2).2 ∧
    LoadHolds rd (rnd * (x * x * (x * x))) 6 (cur * gen ^ 2) ∧
    LoadHolds rd (rnd * (x * x * (x * x))) 7 (scStep e (g1, g2) (claim, cv)).2.1

theorem word_four' : word 4 0 0 = gen ^ 2 := word_two_pow (a := 2) (by decide)

set_option maxHeartbeats 1000000 in
theorem loop82_step (rd : Reader) (N rnd zr chis : E) (d : ℕ) (x : E) :
    coreProgram.relN rd (d + 1) "__loop82" (x :: [N, rnd, zr, chis]) [] ↔
      L82Body rd rnd zr chis x ∧ IsInK (x * gen + N) ∧
        (x * gen + N ≠ 0 →
          coreProgram.relN rd d "__loop82" (x * gen :: [N, rnd, zr, chis]) []) := by
  rw [relN_succ_iff find_loop82,
    show Fn.params Data.core141 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl, core141_body, l82Body]
  simp only [holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    and_true, word_gen, word_four']
  constructor
  · rintro ⟨σ, hp, h5, h6, h7, l8, l9, h10, l11, l12, hb⟩
    simp only [List.cons.injEq] at hp
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hp
    rw [holds_fsNextT] at hb
    obtain ⟨⟨l13, cv, hcv, e1⟩, hb⟩ := hb
    rw [holds_fsNextT] at hb
    obtain ⟨⟨l28, cv2, hcv2, e2⟩, hb⟩ := hb
    obtain ⟨l43, h44, h45, h46, hb⟩ := hb
    rw [holds_squeezeT] at hb
    obtain ⟨⟨cv3, hcv3, e3⟩, h61, l60, l52, l53, h62, h63, l63, h64, h65, h66, h67, l67, h68, h69,
      h70, h71, h72, hK, hcall⟩ := hb
    -- the chain
    have c2 : cv2 = obsCv cv (σ (.n 13)) := by
      have a12 : σ (.n 26) = _ := e1 12 (by omega) (by omega)
      have a13 : σ (.n 27) = _ := e1 13 (by omega) (by omega)
      exact digestScalars_injective (hcv2.symm.trans (by rw [a12, a13]; rfl))
    have c3 : cv3 = obsCv cv2 (σ (.n 28)) := by
      have a12 : σ (.n 41) = _ := e2 12 (by omega) (by omega)
      have a13 : σ (.n 42) = _ := e2 13 (by omega) (by omega)
      exact digestScalars_injective (hcv3.symm.trans (by rw [a12, a13]; rfl))
    have s5 : σ (.n 52) = (digestScalars (sqCv cv3)).1 := e3 5 (by omega)
    have s6 : σ (.n 53) = (digestScalars (sqCv cv3)).2 := e3 6 (by omega)
    have s13 : σ (.n 60) = challengeOf (sqCv cv3) := e3 13 (by omega)
    rw [h6, h5] at h7
    rw [h7] at l8 l9 l12 l43 l52 l53 l63 l67
    rw [h10] at l11
    rw [h61] at l60
    have hst : scStep (σ (.n 11)) (σ (.n 13), σ (.n 28)) (σ (.n 43), cv) =
        (σ (.n 60), σ (.n 67), sqCv cv3) := by
      subst c3 c2
      refine Prod.ext s13.symm (Prod.ext ?_ rfl)
      show σ (.n 43) + σ (.n 11) * (σ (.n 13) + σ (.n 28)) +
          challengeOf (sqCv (obsCv (obsCv cv (σ (.n 13))) (σ (.n 28)))) *
            (σ (.n 13) + challengeOf (sqCv (obsCv (obsCv cv (σ (.n 13))) (σ (.n 28)))) *
              σ (.n 28)) = σ (.n 67)
      rw [h67, h66, h65, h64, h46, h45, h44, s13]
    refine ⟨⟨cv, σ (.n 12), σ (.n 43), σ (.n 11), σ (.n 13), σ (.n 28), ?_, ?_, l12, l43, l11, l13,
      l28, ?_, ?_, ?_, ?_, ?_⟩, by rwa [h70, h69, h68] at hK, fun hne => ?_⟩
    · rw [show σ (.n 8) = (digestScalars cv).1 from congrArg Prod.fst hcv] at l8; exact l8
    · rw [show σ (.n 9) = (digestScalars cv).2 from congrArg Prod.snd hcv] at l9; exact l9
    · rw [hst]; exact l60
    · rw [hst, ← s5]; exact l52
    · rw [hst, ← s6]; exact l53
    · rw [h63, h62] at l63; exact l63
    · rw [hst]; exact l67
    · have := hcall (by rwa [h70, h69, h68])
      rwa [h72, h71] at this
  · rintro ⟨⟨cv, cur, claim, e, g1, g2, l8, l9, l12, l43, l11, l13, l28, l60, l52, l53, l63, l67⟩,
      hK, hcall⟩
    set cv2 := obsCv cv g1
    set cv3 := obsCv cv2 g2
    have hst := (show scStep e (g1, g2) (claim, cv) = (challengeOf (sqCv cv3),
      claim + e * (g1 + g2) + challengeOf (sqCv cv3) * (g1 + challengeOf (sqCv cv3) * g2),
      sqCv cv3) from rfl)
    rw [hst] at l60 l52 l53 l67
    refine ⟨setl (Val.ofArgs [x, N, rnd, zr, chis]) 5 ([x * x, x * x * (x * x),
      rnd * (x * x * (x * x)),
      (digestScalars cv).1, (digestScalars cv).2, zr * x, e, cur, g1] ++
      ((List.range 14).map fun k => fsVals g1 cv 1 k) ++ [g2] ++
      ((List.range 14).map fun k => fsVals g2 cv2 1 k) ++
      [claim, g1 + g2, e * (g1 + g2), claim + e * (g1 + g2)] ++
      ((List.range 14).map fun k => sqVals cv3 k) ++
      [chis * x, gen ^ 2, cur * gen ^ 2, challengeOf (sqCv cv3) * g2,
        g1 + challengeOf (sqCv cv3) * g2,
        challengeOf (sqCv cv3) * (g1 + challengeOf (sqCv cv3) * g2),
        claim + e * (g1 + g2) + challengeOf (sqCv cv3) * (g1 + challengeOf (sqCv cv3) * g2),
        gen, x * gen, x * gen + N, gen, x * gen]), ?_, ?_⟩
    · simp only [List.cons_append, List.map_cons, List.range_succ, List.range_zero, List.map_nil,
        List.nil_append]
      b1_look
    · simp only [List.cons_append, List.map_cons, List.range_succ, List.range_zero, List.map_nil,
        List.nil_append]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals (try b1_look)
      · exact l8
      · exact l9
      · exact l11
      · exact l12
      · rw [holds_fsNextT]
        refine ⟨⟨?_, cv, ?_, fun k hk1 hk2 => ?_⟩, ?_⟩
        · b1_look; exact l13
        · b1_look
        · interval_cases k <;> b1_look
        rw [holds_fsNextT]
        refine ⟨⟨?_, cv2, ?_, fun k hk1 hk2 => ?_⟩, ?_⟩
        · b1_look; exact l28
        · b1_look; rfl
        · interval_cases k <;> b1_look
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        all_goals (try b1_look)
        · exact l43
        rw [holds_squeezeT]
        refine ⟨⟨cv3, ?_, fun k hk => ?_⟩, ?_⟩
        · b1_look; rfl
        · interval_cases k <;> b1_look
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        all_goals (try b1_look)
        all_goals (try rfl)
        · exact l60
        · exact l52
        · exact l53
        · exact l63
        · exact l67
        · exact hK
        · exact hcall

end
end LeanVM.Guest.B1
