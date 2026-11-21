/-
  LeanVM.Guest.B1.Tables.VtC.ZTail

  `verify_tables`' statements `5225 ..< 5256`, completely: the public input's binding and the
  return.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ZSetup

/-!
# The public input's binding, completely

`vtZt_complete`: from the sponge `S2` after the table evaluations (its waiting word's two cells,
evaluation `152`, and its capacity), on a pool holding the two binding claims at `157`, `158`, the
statements hold; `rm` is `S2`'s squeeze and the function returns the sponge after it, the cursor
`153` words past the rounds', `g^n`, the bytecode value and `rm`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The tail's statements evaluation alone does not settle. -/
noncomputable def zTRest : List Stmt := [
    .atom (.keccak [.n 4388, .n 4389, .n 2294, .n 2294, .n 2294, .n 2295, .n 2296, .n 2297, .n 4382, .n 4383, .n 4384, .n 4385, .n 4386] [.n 5648, .n 5649, .n 5650, .n 5651, .n 5652, .n 5653, .n 5654, .n 5655, .n 5656, .n 5657, .n 5658, .n 5659, .n 5660] false false),
    .atom (.assertInK (.n 5661) (.n 5664)),
    .atom (.assertInK (.n 5665) (.n 5668)),
    .atom (.load (.n 5671) (.n 15) 157),
    .atom (.load (.n 5674) (.n 15) 158)]

/-- What the tail gives: `rm`, the returned capacity, cursor, `g^n`, bytecode value, `rm` and
`col_eval_words` (the rounds' cursor). -/
def ZtOut (σ : Val) (S2 : Fs) : Prop :=
  σ (.n 5648) = S2.squeeze.1 ∧
    [σ (.n 5675), σ (.n 5676), σ (.n 5677), σ (.n 5678), σ (.n 5679)] = S2.squeeze.2.cap ∧
    σ (.n 5682) = σ (.n 2347) * gen ^ 153 ∧ σ (.n 5683) = σ (.n 2245) ∧
    σ (.n 5684) = σ (.n 1606) ∧ σ (.n 5685) = S2.squeeze.1 ∧ σ (.n 5686) = σ (.n 2347)

theorem vtW153C : word 10905190400 0 = gen ^ 153 := by
  rw [tb_word_eOfNat]
  show ofK (K.ofBits 10905190400) = gen ^ 153
  rw [gen_pow_eq_ofK, show K.ofBits 10905190400 = Parameters.addressOfIndex 153 by decide +kernel]

set_option maxRecDepth 100000 in
/-- **Statements `5225 ..< 5256`, completely.** -/
theorem vtZt_complete {rd : Reader} {w : ℕ → E} {args : List E} (hl : args.length = 20) {S2 : Fs}
    (hSr : rateOf S2.pend =
      [vtσ rd w args (.n 4388), vtσ rd w args (.n 4389), 0, 0, 0, 0, 0, 0])
    (hSc : S2.cap = [vtσ rd w args (.n 4382), vtσ rd w args (.n 4383), vtσ rd w args (.n 4384),
      vtσ rd w args (.n 4385), vtσ rd w args (.n 4386)])
    (hp0 : LoadHolds rd (vtσ rd w args (.n 15)) 157 (multilinearEval
      [ofK ((vtσ rd w args (.n 6)).limb 0), ofK ((vtσ rd w args (.n 7)).limb 0)] [S2.squeeze.1]))
    (hp1 : LoadHolds rd (vtσ rd w args (.n 15)) 158 (multilinearEval
      [ofK ((vtσ rd w args (.n 6)).limb 1), ofK ((vtσ rd w args (.n 7)).limb 1)] [S2.squeeze.1])) :
    (∀ s ∈ (vtPre.drop 5225).take 31, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      ZtOut (vtσ rd w args) S2 := by
  have g : GoodL rd w (vtσ rd w args) zTail := vt_goodL hl 5225 zTail zTail_at
  have gz : GoodL rd w (vtσ rd w args) [.atom (.const (.n 2294) (word 0 0)),
      .atom (.const (.n 2295) (word 0 0)), .atom (.const (.n 2296) (word 0 0)),
      .atom (.const (.n 2297) (word 0 0))] := vt_goodL hl 2328 _ (by decide +kernel)
  have gk : Good rd vtSL w (vtσ rd w args) (.keccak [.n 4388, .n 4389, .n 2294, .n 2294, .n 2294,
      .n 2295, .n 2296, .n 2297, .n 4382, .n 4383, .n 4384, .n 4385, .n 4386] (lyOuts 5648) false
      false) := (vt_goodL (rd := rd) (w := w) hl 5225 [.atom (.keccak [.n 4388, .n 4389, .n 2294,
      .n 2294, .n 2294, .n 2295, .n 2296, .n 2297, .n 4382, .n 4383, .n 4384, .n 4385, .n 4386]
      (lyOuts 5648) false false)] (by decide +kernel)).1
  have e := tbStmtsEqb_sound zTail_at
  have hlen31 : zTail.length = 31 := rfl
  suffices H : (∀ s ∈ zTRest, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      ZtOut (vtσ rd w args) S2 by
    refine ⟨fun s hs => ?_, H.2⟩
    rw [← hlen31, ← e] at hs
    exact vt_block hl 5225 zTail zTail_at zTRest (by decide +kernel) H.1 s hs
  generalize vtσ rd w args = σ at *
  simp only [zTail, GoodL, GoodS, Good, fixNe, Nat.reduceLT, and_true, ↓reduceIte] at g
  simp only [GoodL, GoodS, Good, fixNe, and_true] at gz
  obtain ⟨z0, z1, z2, z3⟩ := gz
  rw [tb_word_zero] at z0 z1 z2 z3
  obtain ⟨g5523, g5524, g5525, g5526, g5527, g5528, g5529, g5530, g5531, g5532, g5533, g5534, g5535,
    g5536, g5537, g5538, g5539, g5540, g5541, g5542, g5543, g5544, g5545, g5546, g5547, g5548,
    g5549, g5550, g5551, g5552, g5553⟩ := g
  -- the squeeze
  have hin : ([.n 4388, .n 4389, .n 2294, .n 2294, .n 2294, .n 2295, .n 2296, .n 2297, .n 4382,
      .n 4383, .n 4384, .n 4385, .n 4386] : List V).map σ = rateOf S2.pend ++ S2.cap := by
    rw [hSr, hSc]; simp [z0, z1, z2, z3]
  have k5523 : (Atom.keccak [.n 4388, .n 4389, .n 2294, .n 2294, .n 2294, .n 2295, .n 2296,
      .n 2297, .n 4382, .n 4383, .n 4384, .n 4385, .n 4386] (lyOuts 5648) false false).Holds rd σ :=
    z_keccak gk
  obtain ⟨hPk, -⟩ := ly_keccak k5523
  rw [hin] at hPk
  have vrm : σ (.n 5648) = S2.squeeze.1 := challengeT_value (s0 := .n 5648) (b := 5648) rfl (hPk 0 (by norm_num))
  -- the public words' limbs
  have l6 : σ (.n 5661) = ofK ((σ (.n 6)).limb 0) := by
    have := g5524 0 (by simp); simpa [limbAt] using this
  have l7 : σ (.n 5665) = ofK ((σ (.n 7)).limb 0) := by
    have := g5529 0 (by simp); simpa [limbAt] using this
  have h6 : σ (.n 5664) = ofK ((σ (.n 6)).limb 1) := by
    rw [g5527, g5525, g5526, word_y_inv, l6]; exact split_hi _
  have h7 : σ (.n 5668) = ofK ((σ (.n 7)).limb 1) := by
    rw [g5532, g5530, g5531, word_y_inv, l7]; exact split_hi _
  have i5528 : (Atom.assertInK (.n 5661) (.n 5664)).Holds rd σ := by
    rw [Atom.Holds, l6, h6]; exact ⟨ofK_isInK _, ofK_isInK _⟩
  have i5533 : (Atom.assertInK (.n 5665) (.n 5668)).Holds rd σ := by
    rw [Atom.Holds, l7, h7]; exact ⟨ofK_isInK _, ofK_isInK _⟩
  have s5537 : (Atom.load (.n 5671) (.n 15) 157).Holds rd σ := by
    show LoadHolds rd _ _ _
    have e : multilinearEval [ofK ((σ (.n 6)).limb 0), ofK ((σ (.n 7)).limb 0)] [S2.squeeze.1] =
        σ (.n 5671) := by
      rw [g5536, g5535, g5534, l6, l7, vrm]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [← e]; exact hp0
  have s5541 : (Atom.load (.n 5674) (.n 15) 158).Holds rd σ := by
    show LoadHolds rd _ _ _
    have e : multilinearEval [ofK ((σ (.n 6)).limb 1), ofK ((σ (.n 7)).limb 1)] [S2.squeeze.1] =
        σ (.n 5674) := by
      rw [g5540, g5539, g5538, h6, h7, vrm]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [← e]; exact hp1
  have hrest : ∀ s ∈ zTRest, VSH (coreProgram.Rel rd) rd σ s := by
    intro s hs
    simp only [zTRest, List.mem_cons, List.not_mem_nil, or_false] at hs
    obtain rfl | rfl | rfl | rfl | rfl := hs
    · exact k5523
    · exact i5528
    · exact i5533
    · exact s5537
    · exact s5541
  refine ⟨hrest, vrm, ?_, ?_, g5550, g5551, by rw [g5552, vrm], g5553⟩
  · rw [g5542, g5543, g5544, g5545, g5546, hPk 8 (by norm_num), hPk 9 (by norm_num),
      hPk 10 (by norm_num), hPk 11 (by norm_num), hPk 12 (by norm_num)]
    rfl
  · rw [g5549, g5548, g5547, vtW153C]

end
end LeanVM.Guest.B1.Tables
