/-
  LeanVM.Guest.B1.Tables.VtC.ZTail

  `verify_tables`' statements `6353 ..< 6398`, completely: the public input's binding and the
  return.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ZSetup

/-!
# The public input's binding, completely (G:2522-2535)

`vtZt_complete`: from the sponge `S2` after the table evaluations (its three waiting words'
cells, evaluations `156 ..< 159`, and its capacity), on canonical public words `pi_0, pi_1` and a
pool holding the three binding claims at `164 ..< 167`, the statements hold; `rm` is `S2`'s
squeeze and the function returns the sponge after it, the cursor `159` words past the rounds',
`g^n`, the bytecode value and `rm`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The tail's statements evaluation alone does not settle. -/
noncomputable def zTRest : List Stmt := [
    .atom (.keccak [.n 5712, .n 5714, .n 5723, .n 5725, .n 5734, .n 5736, .n 6922, .n 6923, .n 5700, .n 5701, .n 5702, .n 5703, .n 5704] [.n 6924, .n 6925, .n 6926, .n 6927, .n 6928, .n 6929, .n 6930, .n 6931, .n 6932, .n 6933, .n 6934, .n 6935, .n 6936] false false),
    .atom (.assertInK (.n 6937) (.n 6940)),
    .atom (.assertInK (.n 6944) (.n 6947)),
    .atom (.assertInK (.n 6949) (.n 6952)),
    .atom (.load (.n 6956) (.n 15) 164),
    .atom (.load (.n 6959) (.n 15) 165),
    .atom (.load (.n 6960) (.n 15) 166)]

/-- What the tail gives: `rm`, the returned capacity, cursor, `g^n`, bytecode value, `rm` and
`col_eval_words` (the rounds' cursor). -/
def ZtOut (σ : Val) (S2 : Fs) : Prop :=
  σ (.n 6943) = S2.squeeze.1 ∧
    [σ (.n 6961), σ (.n 6962), σ (.n 6963), σ (.n 6964), σ (.n 6965)] = S2.squeeze.2.cap ∧
    σ (.n 6968) = σ (.n 2625) * gen ^ 159 ∧ σ (.n 6969) = σ (.n 2516) ∧
    σ (.n 6970) = σ (.n 581) ∧ σ (.n 6971) = S2.squeeze.1 ∧ σ (.n 6972) = σ (.n 2625)

set_option maxRecDepth 100000 in
/-- **Statements `6353 ..< 6398`, completely.** -/
theorem vtZt_complete {rd : Reader} {w : ℕ → E} {args : List E} (hl : args.length = 20) {S2 : Fs}
    (hSr : rateOf S2.pend =
      [vtσ rd w args (.n 5712), vtσ rd w args (.n 5714), vtσ rd w args (.n 5723),
        vtσ rd w args (.n 5725), vtσ rd w args (.n 5734), vtσ rd w args (.n 5736), 0, 0])
    (hSc : S2.cap = [vtσ rd w args (.n 5700), vtσ rd w args (.n 5701), vtσ rd w args (.n 5702),
      vtσ rd w args (.n 5703), vtσ rd w args (.n 5704)])
    (hcan : AllCanonical (rateOf S2.pend ++ S2.cap))
    (hc6 : IsCanonical128 (vtσ rd w args (.n 6))) (hc7 : IsCanonical128 (vtσ rd w args (.n 7)))
    (hp0 : LoadHolds rd (vtσ rd w args (.n 15)) 164 (multilinearEval
      [ofK ((vtσ rd w args (.n 6)).limb 0), ofK ((vtσ rd w args (.n 7)).limb 0)] [S2.squeeze.1]))
    (hp1 : LoadHolds rd (vtσ rd w args (.n 15)) 165 (multilinearEval
      [ofK ((vtσ rd w args (.n 6)).limb 1), ofK ((vtσ rd w args (.n 7)).limb 1)] [S2.squeeze.1]))
    (hp2 : LoadHolds rd (vtσ rd w args (.n 15)) 166 0) :
    (∀ s ∈ (vtPre.drop 6353).take 45, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      ZtOut (vtσ rd w args) S2 := by
  have g : GoodL rd w (vtσ rd w args) zTail := vt_goodL hl 6353 zTail zTail_at
  have gk : Good rd vtSL w (vtσ rd w args) (.keccak [.n 5712, .n 5714, .n 5723, .n 5725, .n 5734, .n 5736, .n 6922, .n 6923, .n 5700, .n 5701, .n 5702, .n 5703, .n 5704] (lyOuts 6924) false
      false) := (vt_goodL (rd := rd) (w := w) hl 6355 [.atom (.keccak [.n 5712, .n 5714, .n 5723, .n 5725, .n 5734, .n 5736, .n 6922, .n 6923, .n 5700, .n 5701, .n 5702, .n 5703, .n 5704]
      (lyOuts 6924) false false)] (by decide +kernel)).1
  have gch : GoodL rd w (vtσ rd w args) (challengeT (.n 6924) (.n 6925) 6937) :=
    vt_goodL hl 6356 _ (by decide +kernel)
  have e := tbStmtsEqb_sound zTail_at
  have hlen42 : zTail.length = 45 := rfl
  suffices H : (∀ s ∈ zTRest, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      ZtOut (vtσ rd w args) S2 by
    refine ⟨fun s hs => ?_, H.2⟩
    rw [← hlen42, ← e] at hs
    exact vt_block hl 6353 zTail zTail_at zTRest (by decide +kernel) H.1 s hs
  generalize vtσ rd w args = σ at *
  simp only [zTail, GoodL, GoodS, Good, fixNe, Nat.reduceLT, and_true, ↓reduceIte] at g
  obtain ⟨g6353, g6354, g6355, g6356, g6357, g6358, g6359, g6360, g6361, g6362, g6363, g6364, g6365, g6366, g6367, g6368, g6369, g6370, g6371, g6372, g6373, g6374, g6375, g6376, g6377, g6378, g6379, g6380, g6381, g6382, g6383, g6384, g6385, g6386, g6387, g6388, g6389, g6390, g6391, g6392, g6393, g6394, g6395, g6396, g6397⟩ := g
  rw [tb_word_zero] at g6353 g6354
  -- the squeeze
  have hin : ([.n 5712, .n 5714, .n 5723, .n 5725, .n 5734, .n 5736, .n 6922, .n 6923, .n 5700,
      .n 5701, .n 5702, .n 5703, .n 5704] : List V).map σ = rateOf S2.pend ++ S2.cap := by
    rw [hSr, hSc]; simp [g6353, g6354]
  have k6355 : (Atom.keccak [.n 5712, .n 5714, .n 5723, .n 5725, .n 5734, .n 5736, .n 6922, .n 6923, .n 5700, .n 5701, .n 5702, .n 5703, .n 5704] (lyOuts 6924) false false).Holds rd σ :=
    z_keccak gk (by rw [hin]; exact hcan)
  obtain ⟨-, hPk, -⟩ := ly_keccak k6355
  rw [hin] at hPk
  have hch : ChallengeOk σ (.n 6924) (.n 6925) 6937 :=
    z_challenge gch
      (by rw [hPk 1 (by norm_num)]; exact cellsOfState_canonical _ _ _)
  have vrm : σ (.n 6943) = S2.squeeze.1 :=
    challengeT_value hch (hPk 0 (by norm_num)) (hPk 1 (by norm_num))
  -- the public words' limbs
  have l6 : σ (.n 6944) = ofK ((σ (.n 6)).limb 0) := by
    have := g6364 0 (by simp); simpa [limbAt] using this
  have l7 : σ (.n 6949) = ofK ((σ (.n 7)).limb 0) := by
    have := g6370 0 (by simp); simpa [limbAt] using this
  have h6 : σ (.n 6947) = ofK ((σ (.n 6)).limb 1) := by
    rw [g6367, g6365, g6366, word_y_inv, l6]; exact split_hi hc6
  have h7 : σ (.n 6952) = ofK ((σ (.n 7)).limb 1) := by
    rw [g6373, g6371, g6372, word_y_inv, l7]; exact split_hi hc7
  have i6360 : (Atom.assertInK (.n 6937) (.n 6940)).Holds rd σ := ⟨hch.2.2.2.1, hch.2.2.2.2.1⟩
  have i6368 : (Atom.assertInK (.n 6944) (.n 6947)).Holds rd σ := by
    rw [Atom.Holds, l6, h6]; exact ⟨ofK_isInK _, ofK_isInK _⟩
  have i6374 : (Atom.assertInK (.n 6949) (.n 6952)).Holds rd σ := by
    rw [Atom.Holds, l7, h7]; exact ⟨ofK_isInK _, ofK_isInK _⟩
  have s6379 : (Atom.load (.n 6956) (.n 15) 164).Holds rd σ := by
    show LoadHolds rd _ _ _
    have e : multilinearEval [ofK ((σ (.n 6)).limb 0), ofK ((σ (.n 7)).limb 0)] [S2.squeeze.1] =
        σ (.n 6956) := by
      rw [g6378, g6377, g6376, g6375, g6369, l6, l7, vrm]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [← e]; exact hp0
  have s6383 : (Atom.load (.n 6959) (.n 15) 165).Holds rd σ := by
    show LoadHolds rd _ _ _
    have e : multilinearEval [ofK ((σ (.n 6)).limb 1), ofK ((σ (.n 7)).limb 1)] [S2.squeeze.1] =
        σ (.n 6959) := by
      rw [g6382, g6381, g6380, h6, h7, vrm]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [← e]; exact hp1
  have s6385 : (Atom.load (.n 6960) (.n 15) 166).Holds rd σ := by
    show LoadHolds rd _ _ _
    rw [g6384, tb_word_zero]; exact hp2
  have hrest : ∀ s ∈ zTRest, VSH (coreProgram.Rel rd) rd σ s := by
    intro s hs
    simp only [zTRest, List.mem_cons, List.not_mem_nil, or_false] at hs
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl := hs
    · exact k6355
    · exact i6360
    · exact i6368
    · exact i6374
    · exact s6379
    · exact s6383
    · exact s6385
  refine ⟨hrest, vrm, ?_, ?_, g6394, g6395, by rw [g6396, vrm], g6397⟩
  · rw [g6386, g6387, g6388, g6389, g6390, hPk 8 (by norm_num), hPk 9 (by norm_num),
      hPk 10 (by norm_num), hPk 11 (by norm_num), hPk 12 (by norm_num)]
    rfl
  · rw [g6393, g6392, g6391, vtW159]

end
end LeanVM.Guest.B1.Tables
