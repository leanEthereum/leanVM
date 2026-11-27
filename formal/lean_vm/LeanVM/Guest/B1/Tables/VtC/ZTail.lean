/-
  LeanVM.Guest.B1.Tables.VtC.ZTail

  `verify_tables`' statements `nxt[0]@42 ..< ret`, completely: the public input's binding and the
  return.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ZSetup
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# The public input's binding, completely

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
    .atom (.keccak [.n (val% «verify_tables» "rate[0]@42"), .n (val% «verify_tables» "rate[1]@42"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[2]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[3]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[4]"), .n (val% «verify_tables» "nxt[8]@41"), .n (val% «verify_tables» "nxt[9]@41"), .n (val% «verify_tables» "nxt[10]@41"), .n (val% «verify_tables» "nxt[11]@41"), .n (val% «verify_tables» "nxt[12]@41")] [.n (val% «verify_tables» "nxt[0]@42"), .n (val% «verify_tables» "nxt[1]@42"), .n (val% «verify_tables» "nxt[2]@42"), .n (val% «verify_tables» "nxt[3]@42"), .n (val% «verify_tables» "nxt[4]@42"), .n (val% «verify_tables» "nxt[5]@42"), .n (val% «verify_tables» "nxt[6]@42"), .n (val% «verify_tables» "nxt[7]@42"), .n (val% «verify_tables» "nxt[8]@42"), .n (val% «verify_tables» "nxt[9]@42"), .n (val% «verify_tables» "nxt[10]@42"), .n (val% «verify_tables» "nxt[11]@42"), .n (val% «verify_tables» "nxt[12]@42")] false false),
    .atom (.assertInK (.n (val% «verify_tables» "lo[0]@1")) (.n (val% «verify_tables» "hi@1"))),
    .atom (.assertInK (.n (val% «verify_tables» "lo[0]@2")) (.n (val% «verify_tables» "hi@2"))),
    .atom (.load (.n (val% «verify_tables» "s88#2")) (.n (val% «verify_tables» "claim_pool")) 157),
    .atom (.load (.n (val% «verify_tables» "s90#2")) (.n (val% «verify_tables» "claim_pool")) 158)]

/-- What the tail gives: `rm`, the returned capacity, cursor, `g^n`, bytecode value, `rm` and
`col_eval_words` (the rounds' cursor). -/
def ZtOut (σ : Val) (S2 : Fs) : Prop :=
  σ (.n (val% «verify_tables» "nxt[0]@42")) = S2.squeeze.1 ∧
    [σ (.n (val% «verify_tables» "s92#0")), σ (.n (val% «verify_tables» "s92#0[1]")), σ (.n (val% «verify_tables» "s92#0[2]")), σ (.n (val% «verify_tables» "s92#0[3]")), σ (.n (val% «verify_tables» "s92#0[4]"))] = S2.squeeze.2.cap ∧
    σ (.n (val% «verify_tables» "s92#0[5]")) = σ (.n (val% «verify_tables» "cursor@5")) * gen ^ 153 ∧ σ (.n (val% «verify_tables» "s92#0[6]")) = σ (.n (val% «verify_tables» "g_zc_n")) ∧
    σ (.n (val% «verify_tables» "s92#0[7]")) = σ (.n (val% «verify_tables» "x@8")) ∧ σ (.n (val% «verify_tables» "s92#0[8]")) = S2.squeeze.1 ∧ σ (.n (val% «verify_tables» "s92#0[9]")) = σ (.n (val% «verify_tables» "cursor@5"))

set_option maxRecDepth 100000 in
/-- **Statements `nxt[0]@42 ..< ret`, completely.** -/
theorem vtZt_complete {rd : Reader} {w : ℕ → E} {args : List E} (hl : args.length = 21) {S2 : Fs}
    (hSr : rateOf S2.pend =
      [vtσ rd w args (.n (val% «verify_tables» "rate[0]@42")), vtσ rd w args (.n (val% «verify_tables» "rate[1]@42")), 0, 0, 0, 0, 0, 0])
    (hSc : S2.cap = [vtσ rd w args (.n (val% «verify_tables» "nxt[8]@41")), vtσ rd w args (.n (val% «verify_tables» "nxt[9]@41")), vtσ rd w args (.n (val% «verify_tables» "nxt[10]@41")),
      vtσ rd w args (.n (val% «verify_tables» "nxt[11]@41")), vtσ rd w args (.n (val% «verify_tables» "nxt[12]@41"))])
    (hp0 : LoadHolds rd (vtσ rd w args (.n (val% «verify_tables» "claim_pool"))) 157 (multilinearEval
      [ofK ((vtσ rd w args (.n (val% «verify_tables» "pi_0"))).limb 0), ofK ((vtσ rd w args (.n (val% «verify_tables» "pi_1"))).limb 0)] [S2.squeeze.1]))
    (hp1 : LoadHolds rd (vtσ rd w args (.n (val% «verify_tables» "claim_pool"))) 158 (multilinearEval
      [ofK ((vtσ rd w args (.n (val% «verify_tables» "pi_0"))).limb 1), ofK ((vtσ rd w args (.n (val% «verify_tables» "pi_1"))).limb 1)] [S2.squeeze.1])) :
    (∀ s ∈ (vtPre.drop (pos% «verify_tables» "nxt[0]@42")).take (span% «verify_tables» "nxt[0]@42" "ret"), VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      ZtOut (vtσ rd w args) S2 := by
  have g : GoodL rd w (vtσ rd w args) zTail := vt_goodL hl 5209 zTail zTail_at
  have gz : GoodL rd w (vtσ rd w args) [.atom (.const (.n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]")) (word 0 0)),
      .atom (.const (.n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[2]")) (word 0 0)), .atom (.const (.n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[3]")) (word 0 0)),
      .atom (.const (.n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[4]")) (word 0 0))] := vt_goodL hl 2322 _ (by decide +kernel)
  have gk : Good rd vtSL w (vtσ rd w args) (.keccak [.n (val% «verify_tables» "rate[0]@42"), .n (val% «verify_tables» "rate[1]@42"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"),
      .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[2]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[3]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[4]"), .n (val% «verify_tables» "nxt[8]@41"), .n (val% «verify_tables» "nxt[9]@41"), .n (val% «verify_tables» "nxt[10]@41"), .n (val% «verify_tables» "nxt[11]@41"), .n (val% «verify_tables» "nxt[12]@41")] (lyOuts (val% «verify_tables» "nxt[0]@42")) false
      false) := (vt_goodL (rd := rd) (w := w) hl 5209 [.atom (.keccak [.n (val% «verify_tables» "rate[0]@42"), .n (val% «verify_tables» "rate[1]@42"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"),
      .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[2]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[3]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[4]"), .n (val% «verify_tables» "nxt[8]@41"), .n (val% «verify_tables» "nxt[9]@41"), .n (val% «verify_tables» "nxt[10]@41"), .n (val% «verify_tables» "nxt[11]@41"), .n (val% «verify_tables» "nxt[12]@41")]
      (lyOuts (val% «verify_tables» "nxt[0]@42")) false false)] (by decide +kernel)).1
  have e := stmtsEqb_sound zTail_at
  have hlen31 : zTail.length = 31 := rfl
  suffices H : (∀ s ∈ zTRest, VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      ZtOut (vtσ rd w args) S2 by
    refine ⟨fun s hs => ?_, H.2⟩
    rw [← hlen31, ← e] at hs
    exact vt_block hl 5209 zTail zTail_at zTRest (by decide +kernel) H.1 s hs
  generalize vtσ rd w args = σ at *
  simp only [zTail, GoodL, GoodS, Good, fixNe, Nat.reduceLT, and_true, ↓reduceIte] at g
  simp only [GoodL, GoodS, Good, fixNe, and_true] at gz
  obtain ⟨z0, z1, z2, z3⟩ := gz
  rw [word_zero] at z0 z1 z2 z3
  obtain ⟨g5523, g5524, g5525, g5526, g5527, g5528, g5529, g5530, g5531, g5532, g5533, g5534, g5535,
    g5536, g5537, g5538, g5539, g5540, g5541, g5542, g5543, g5544, g5545, g5546, g5547, g5548,
    g5549, g5550, g5551, g5552, g5553⟩ := g
  -- the squeeze
  have hin : ([.n (val% «verify_tables» "rate[0]@42"), .n (val% «verify_tables» "rate[1]@42"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[2]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[3]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[4]"), .n (val% «verify_tables» "nxt[8]@41"),
      .n (val% «verify_tables» "nxt[9]@41"), .n (val% «verify_tables» "nxt[10]@41"), .n (val% «verify_tables» "nxt[11]@41"), .n (val% «verify_tables» "nxt[12]@41")] : List V).map σ = rateOf S2.pend ++ S2.cap := by
    rw [hSr, hSc]; simp [z0, z1, z2, z3]
  have k5523 : (Atom.keccak [.n (val% «verify_tables» "rate[0]@42"), .n (val% «verify_tables» "rate[1]@42"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[2]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[3]"),
      .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[4]"), .n (val% «verify_tables» "nxt[8]@41"), .n (val% «verify_tables» "nxt[9]@41"), .n (val% «verify_tables» "nxt[10]@41"), .n (val% «verify_tables» "nxt[11]@41"), .n (val% «verify_tables» "nxt[12]@41")] (lyOuts (val% «verify_tables» "nxt[0]@42")) false false).Holds rd σ :=
    z_keccak gk
  obtain ⟨hPk, -⟩ := ly_keccak k5523
  rw [hin] at hPk
  have vrm : σ (.n (val% «verify_tables» "nxt[0]@42")) = S2.squeeze.1 := challengeT_value (s0 := .n (val% «verify_tables» "nxt[0]@42")) (b := 5633) rfl (hPk 0 (by norm_num))
  -- the public words' limbs
  have l6 : σ (.n (val% «verify_tables» "lo[0]@1")) = ofK ((σ (.n (val% «verify_tables» "pi_0"))).limb 0) := by
    have := g5524 0 (by simp); simpa [limbAt] using this
  have l7 : σ (.n (val% «verify_tables» "lo[0]@2")) = ofK ((σ (.n (val% «verify_tables» "pi_1"))).limb 0) := by
    have := g5529 0 (by simp); simpa [limbAt] using this
  have h6 : σ (.n (val% «verify_tables» "hi@1")) = ofK ((σ (.n (val% «verify_tables» "pi_0"))).limb 1) := by
    rw [g5527, g5525, g5526, word_y_inv, l6]; exact split_hi _
  have h7 : σ (.n (val% «verify_tables» "hi@2")) = ofK ((σ (.n (val% «verify_tables» "pi_1"))).limb 1) := by
    rw [g5532, g5530, g5531, word_y_inv, l7]; exact split_hi _
  have i5528 : (Atom.assertInK (.n (val% «verify_tables» "lo[0]@1")) (.n (val% «verify_tables» "hi@1"))).Holds rd σ := by
    rw [Atom.Holds, l6, h6]; exact ⟨ofK_isInK _, ofK_isInK _⟩
  have i5533 : (Atom.assertInK (.n (val% «verify_tables» "lo[0]@2")) (.n (val% «verify_tables» "hi@2"))).Holds rd σ := by
    rw [Atom.Holds, l7, h7]; exact ⟨ofK_isInK _, ofK_isInK _⟩
  have s5537 : (Atom.load (.n (val% «verify_tables» "s88#2")) (.n (val% «verify_tables» "claim_pool")) 157).Holds rd σ := by
    show LoadHolds rd _ _ _
    have e : multilinearEval [ofK ((σ (.n (val% «verify_tables» "pi_0"))).limb 0), ofK ((σ (.n (val% «verify_tables» "pi_1"))).limb 0)] [S2.squeeze.1] =
        σ (.n (val% «verify_tables» "s88#2")) := by
      rw [g5536, g5535, g5534, l6, l7, vrm]
      simp only [multilinearEval, List.foldl, foldPairs, List.headD]
      ring
    rw [← e]; exact hp0
  have s5541 : (Atom.load (.n (val% «verify_tables» "s90#2")) (.n (val% «verify_tables» "claim_pool")) 158).Holds rd σ := by
    show LoadHolds rd _ _ _
    have e : multilinearEval [ofK ((σ (.n (val% «verify_tables» "pi_0"))).limb 1), ofK ((σ (.n (val% «verify_tables» "pi_1"))).limb 1)] [S2.squeeze.1] =
        σ (.n (val% «verify_tables» "s90#2")) := by
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
  · rw [g5549, g5548, g5547, vtW153]

end
end LeanVM.Guest.B1.Tables
