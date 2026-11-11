/-
  LeanVM.Guest.B1.Tables.VtC.ZTail

  `verify_tables`' statements `5525 ..< 5559`, completely: the public input's binding and the
  return.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ZSetup

/-!
# The public input's binding, completely (G:2703-2719)

`vtZt_complete`: from the sponge `S2` after the table evaluations (its waiting word's two cells,
evaluation `152`, and its capacity), on a pool holding the two binding claims at `157`, `158`, the
statements hold; `rm` is `S2`'s squeeze and the function returns the sponge after it, the cursor
`153` words past the rounds', `g^n`, the bytecode value and `rm`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The tail's statements evaluation alone does not settle. -/
noncomputable def zTRest : List Stmt := [
    .atom (.keccak [.n 4688, .n 4689, .n 2593, .n 2593, .n 2593, .n 2594, .n 2595, .n 2596, .n 4682, .n 4683, .n 4684, .n 4685, .n 4686] [.n 5948, .n 5949, .n 5950, .n 5951, .n 5952, .n 5953, .n 5954, .n 5955, .n 5956, .n 5957, .n 5958, .n 5959, .n 5960] false false),
    .atom (.assertInK (.n 5962) (.n 5965)),
    .atom (.assertInK (.n 5967) (.n 5970)),
    .atom (.load (.n 5974) (.n 15) 157),
    .atom (.load (.n 5977) (.n 15) 158)]

/-- What the tail gives: `rm`, the returned capacity, cursor, `g^n`, bytecode value, `rm` and
`col_eval_words` (the rounds' cursor). -/
def ZtOut (σ : Val) (S2 : Fs) : Prop :=
  σ (.n 5961) = S2.squeeze.1 ∧
    [σ (.n 5978), σ (.n 5979), σ (.n 5980), σ (.n 5981), σ (.n 5982)] = S2.squeeze.2.cap ∧
    σ (.n 5985) = σ (.n 2647) * gen ^ 153 ∧ σ (.n 5986) = σ (.n 2544) ∧
    σ (.n 5987) = σ (.n 1905) ∧ σ (.n 5988) = S2.squeeze.1 ∧ σ (.n 5989) = σ (.n 2647)

theorem vtW153C : word 10905190400 0 = gen ^ 153 := by
  rw [tb_word_eOfNat]
  show ofK (K.ofBits 10905190400) = gen ^ 153
  rw [gen_pow_eq_ofK, show K.ofBits 10905190400 = Parameters.addressOfIndex 153 by decide +kernel]

set_option maxRecDepth 100000 in
/-- **Statements `5525 ..< 5559`, completely.** -/
theorem vtZt_complete {rd : Reader} {w : ℕ → E} {args : List E} (hl : args.length = 20) {S2 : Fs}
    (hSr : rateOf S2.pend =
      [vtσ rd w args (.n 4688), vtσ rd w args (.n 4689), 0, 0, 0, 0, 0, 0])
    (hSc : S2.cap = [vtσ rd w args (.n 4682), vtσ rd w args (.n 4683), vtσ rd w args (.n 4684),
      vtσ rd w args (.n 4685), vtσ rd w args (.n 4686)])
    (hp0 : LoadHolds rd (vtσ rd w args (.n 15)) 157 (multilinearEval
      [ofK ((vtσ rd w args (.n 6)).limb 0), ofK ((vtσ rd w args (.n 7)).limb 0)] [S2.squeeze.1]))
    (hp1 : LoadHolds rd (vtσ rd w args (.n 15)) 158 (multilinearEval
      [ofK ((vtσ rd w args (.n 6)).limb 1), ofK ((vtσ rd w args (.n 7)).limb 1)] [S2.squeeze.1])) :
    (∀ s ∈ (vtPre.drop 5525).take 34, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      ZtOut (vtσ rd w args) S2 := by
  have g : GoodL rd w (vtσ rd w args) zTail := vt_goodL hl 5525 zTail zTail_at
  have gz : GoodL rd w (vtσ rd w args) [.atom (.const (.n 2593) (word 0 0)),
      .atom (.const (.n 2594) (word 0 0)), .atom (.const (.n 2595) (word 0 0)),
      .atom (.const (.n 2596) (word 0 0))] := vt_goodL hl 2627 _ (by decide +kernel)
  have gk : Good rd vtSL w (vtσ rd w args) (.keccak [.n 4688, .n 4689, .n 2593, .n 2593, .n 2593,
      .n 2594, .n 2595, .n 2596, .n 4682, .n 4683, .n 4684, .n 4685, .n 4686] (lyOuts 5948) false
      false) := (vt_goodL (rd := rd) (w := w) hl 5525 [.atom (.keccak [.n 4688, .n 4689, .n 2593,
      .n 2593, .n 2593, .n 2594, .n 2595, .n 2596, .n 4682, .n 4683, .n 4684, .n 4685, .n 4686]
      (lyOuts 5948) false false)] (by decide +kernel)).1
  have e := tbStmtsEqb_sound zTail_at
  have hlen34 : zTail.length = 34 := rfl
  suffices H : (∀ s ∈ zTRest, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      ZtOut (vtσ rd w args) S2 by
    refine ⟨fun s hs => ?_, H.2⟩
    rw [← hlen34, ← e] at hs
    exact vt_block hl 5525 zTail zTail_at zTRest (by decide +kernel) H.1 s hs
  generalize vtσ rd w args = σ at *
  simp only [zTail, GoodL, GoodS, Good, fixNe, Nat.reduceLT, and_true, ↓reduceIte] at g
  simp only [GoodL, GoodS, Good, fixNe, and_true] at gz
  obtain ⟨z0, z1, z2, z3⟩ := gz
  rw [tb_word_zero] at z0 z1 z2 z3
  obtain ⟨g5525, g5526, g5527, g5528, g5529, g5530, g5531, g5532, g5533, g5534, g5535, g5536,
    g5537, g5538, g5539, g5540, g5541, g5542, g5543, g5544, g5545, g5546, g5547, g5548, g5549,
    g5550, g5551, g5552, g5553, g5554, g5555, g5556, g5557, g5558⟩ := g
  -- the squeeze
  have hin : ([.n 4688, .n 4689, .n 2593, .n 2593, .n 2593, .n 2594, .n 2595, .n 2596, .n 4682,
      .n 4683, .n 4684, .n 4685, .n 4686] : List V).map σ = rateOf S2.pend ++ S2.cap := by
    rw [hSr, hSc]; simp [z0, z1, z2, z3]
  have k5525 : (Atom.keccak [.n 4688, .n 4689, .n 2593, .n 2593, .n 2593, .n 2594, .n 2595,
      .n 2596, .n 4682, .n 4683, .n 4684, .n 4685, .n 4686] (lyOuts 5948) false false).Holds rd σ :=
    z_keccak gk
  obtain ⟨hPk, -⟩ := ly_keccak k5525
  rw [hin] at hPk
  have vrm : σ (.n 5961) = S2.squeeze.1 := challengeT_value (b := 5961) g5526 (hPk 0 (by norm_num))
  -- the public words' limbs
  have l6 : σ (.n 5962) = ofK ((σ (.n 6)).limb 0) := by
    have := g5527 0 (by simp); simpa [limbAt] using this
  have l7 : σ (.n 5967) = ofK ((σ (.n 7)).limb 0) := by
    have := g5533 0 (by simp); simpa [limbAt] using this
  have h6 : σ (.n 5965) = ofK ((σ (.n 6)).limb 1) := by
    rw [g5530, g5528, g5529, word_y_inv, l6]; exact split_hi _
  have h7 : σ (.n 5970) = ofK ((σ (.n 7)).limb 1) := by
    rw [g5536, g5534, g5535, word_y_inv, l7]; exact split_hi _
  have i5531 : (Atom.assertInK (.n 5962) (.n 5965)).Holds rd σ := by
    rw [Atom.Holds, l6, h6]; exact ⟨ofK_isInK _, ofK_isInK _⟩
  have i5537 : (Atom.assertInK (.n 5967) (.n 5970)).Holds rd σ := by
    rw [Atom.Holds, l7, h7]; exact ⟨ofK_isInK _, ofK_isInK _⟩
  have s5542 : (Atom.load (.n 5974) (.n 15) 157).Holds rd σ := by
    show LoadHolds rd _ _ _
    have e : multilinearEval [ofK ((σ (.n 6)).limb 0), ofK ((σ (.n 7)).limb 0)] [S2.squeeze.1] =
        σ (.n 5974) := by
      rw [g5541, g5540, g5539, g5538, g5532, l6, l7, vrm]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [← e]; exact hp0
  have s5546 : (Atom.load (.n 5977) (.n 15) 158).Holds rd σ := by
    show LoadHolds rd _ _ _
    have e : multilinearEval [ofK ((σ (.n 6)).limb 1), ofK ((σ (.n 7)).limb 1)] [S2.squeeze.1] =
        σ (.n 5977) := by
      rw [g5545, g5544, g5543, h6, h7, vrm]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [← e]; exact hp1
  have hrest : ∀ s ∈ zTRest, VSH (coreProgram.Rel rd) rd σ s := by
    intro s hs
    simp only [zTRest, List.mem_cons, List.not_mem_nil, or_false] at hs
    obtain rfl | rfl | rfl | rfl | rfl := hs
    · exact k5525
    · exact i5531
    · exact i5537
    · exact s5542
    · exact s5546
  refine ⟨hrest, vrm, ?_, ?_, g5555, g5556, by rw [g5557, vrm], g5558⟩
  · rw [g5547, g5548, g5549, g5550, g5551, hPk 8 (by norm_num), hPk 9 (by norm_num),
      hPk 10 (by norm_num), hPk 11 (by norm_num), hPk 12 (by norm_num)]
    rfl
  · rw [g5554, g5553, g5552, vtW153C]

end
end LeanVM.Guest.B1.Tables
