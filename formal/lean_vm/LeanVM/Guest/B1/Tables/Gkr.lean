/-
  LeanVM.Guest.B1.Tables.Gkr

  B1 for `verify_bus_gkr`: its soundness, `SoundGkr`.
-/

module

public import LeanVM.Guest.B1.Tables.GkrLayer

/-!
# `verify_bus_gkr` (TRIAGE #37)

`verify_bus_gkr(fs0, fs1, cursor, g_bus_mu, zeta)` (G:1320-1438) range-checks
`g_bus_mu = g^depth`, `depth < 33`, reads the shared root and the count root (asserted nonzero),
fills the slot of the empty point, runs a binary layer when `depth` is odd (`odd_layer`,
`gkrStep 1`), then `depth / 2` layers of two levels (`loop10_step`, `gkrStep 2`), copies the
final point into `zeta` (`loop11_sound`) and returns the final state, cursor and values. Along
the slots, the stream runs `gkrLayers depth` (`gkrLayers_even`, `gkrLayers_odd`), so the whole is
`gkrPhase depth` (`verify_bus_gkr_sound`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The binary layer -/

theorem s191_noRet : Stmt.noRetList Data.core10.s191_e = true := by decide +kernel

/-- The first state cell before the `i`-th child's `fs_next` in the binary layer. -/
def oddS (i : ℕ) : ℕ := if i = 0 then 135 else 152 + 16 * i

theorem odd_fs_blocks : ∀ i < 6, stmtsEqb (fsNextT (.n (oddS i)) (.n (oddS i + 1)) (.n 144) i
    (155 + 16 * i)) ((Data.core10.s191_e.drop (27 + 14 * i)).take 13) = true := by decide +kernel

theorem odd_copy_blocks : ∀ i < 6, stmtsEqb [.atom (.copy (.n (170 + 16 * i)) (.n (155 + 16 * i)))]
    ((Data.core10.s191_e.drop (40 + 14 * i)).take 1) = true := by decide +kernel

theorem multilinearEval_two (e0 e1 y0 : E) :
    multilinearEval [e0, e1] [y0] = e0 * (1 + y0) + e1 * y0 := by
  simp [multilinearEval, foldPairs]

theorem prodE_two (e0 e1 : E) : prodE [e0, e1] = e0 * e1 := by simp [prodE]

theorem word_g6 : word 64 0 0 = gen ^ 6 := word_two_pow (a := 6) (by decide)

/-- **The binary layer** (G:1354-1377), run when `depth` is odd: from the slot of the empty
point, `gkrStep 1` to the slot of length `1`, the row `MU_CAP` cells on. -/
theorem odd_layer {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}
    (hb : Stmt.HoldsList C rd σ Data.core10.s191_e True kret) {cv : Digest} {cur row : E}
    {s : GkrState} (hL : GkrLayer rd (σ (.n 10)) 0 cv cur s row) :
    ∃ ys s' cv', RunsTo (gkrStep 1 s) cv ys s' cv' ∧ ReadsAt rd cur ys ∧
      GkrLayer rd (σ (.n 10)) 1 cv' (cur * gen ^ ys.length) s' (row * gen ^ 40) := by
  have hnr := s191_noRet
  obtain ⟨g0, g1, g2, gv, g3, g4, g5, g6, gpl, -⟩ := hL
  have l128 := holds_atom hnr hb 0 (.load (.n 128) (.n 10) 0) (by decide +kernel)
  have l129 := holds_atom hnr hb 1 (.load (.n 129) (.n 10) 1) (by decide +kernel)
  have sq1 := holds_squeezeAt hnr hb 2 (.n 128) (.n 129) 130 (by decide +kernel)
  have l144 := holds_atom hnr hb 16 (.load (.n 144) (.n 10) 2) (by decide +kernel)
  have l145 := holds_atom hnr hb 17 (.load (.n 145) (.n 10) 3) (by decide +kernel)
  have l146 := holds_atom hnr hb 18 (.load (.n 146) (.n 10) 4) (by decide +kernel)
  have l147 := holds_atom hnr hb 19 (.load (.n 147) (.n 10) 5) (by decide +kernel)
  have a148 := holds_atom hnr hb 20 (.mul (.n 148) (.n 143) (.n 147)) (by decide +kernel)
  have a149 := holds_atom hnr hb 21 (.add (.n 149) (.n 146) (.n 148)) (by decide +kernel)
  have a150 := holds_atom hnr hb 22 (.mul (.n 150) (.n 143) (.n 149)) (by decide +kernel)
  have a151 := holds_atom hnr hb 23 (.add (.n 151) (.n 145) (.n 150)) (by decide +kernel)
  have l152 := holds_atom hnr hb 24 (.load (.n 152) (.n 10) 6) (by decide +kernel)
  have a153 := holds_atom hnr hb 25 (.const (.n 153) (word 1099511627776 0 0)) (by decide +kernel)
  have a154 := holds_atom hnr hb 26 (.mul (.n 154) (.n 152) (.n 153)) (by decide +kernel)
  have fsb := fun i hi => holds_fsNextAt hnr hb (27 + 14 * i) _ _ _ i _ (odd_fs_blocks i hi)
  have cpb := fun i hi => holds_atom hnr hb (40 + 14 * i) _ (odd_copy_blocks i hi)
  have a251 := holds_atom hnr hb 111 (.mul (.n 251) (.n 234) (.n 250)) (by decide +kernel)
  have a252 := holds_atom hnr hb 112 (.const (.n 252) (word 0 0 0)) (by decide +kernel)
  have a253 := holds_atom hnr hb 113 (.mul (.n 253) (.n 143) (.n 252)) (by decide +kernel)
  have a254 := holds_atom hnr hb 114 (.add (.n 254) (.n 251) (.n 253)) (by decide +kernel)
  have a255 := holds_atom hnr hb 115 (.mul (.n 255) (.n 202) (.n 218)) (by decide +kernel)
  have a256 := holds_atom hnr hb 116 (.mul (.n 256) (.n 143) (.n 254)) (by decide +kernel)
  have a257 := holds_atom hnr hb 117 (.add (.n 257) (.n 255) (.n 256)) (by decide +kernel)
  have a258 := holds_atom hnr hb 118 (.mul (.n 258) (.n 170) (.n 186)) (by decide +kernel)
  have a259 := holds_atom hnr hb 119 (.mul (.n 259) (.n 143) (.n 257)) (by decide +kernel)
  have a260 := holds_atom hnr hb 120 (.add (.n 260) (.n 258) (.n 259)) (by decide +kernel)
  have ae := holds_atom hnr hb 121 (.assertEq (.n 151) (.n 260)) (by decide +kernel)
  have sq2 := holds_squeezeAt hnr hb 122 (.n 248) (.n 249) 261 (by decide +kernel)
  have t274 := holds_atom hnr hb 136 (.load (.n 274) (.n 154) 0) (by decide +kernel)
  have t266 := holds_atom hnr hb 137 (.load (.n 266) (.n 10) 8) (by decide +kernel)
  have t267 := holds_atom hnr hb 138 (.load (.n 267) (.n 10) 9) (by decide +kernel)
  have a275 := holds_atom hnr hb 139 (.const (.n 275) (word 64 0 0)) (by decide +kernel)
  have a276 := holds_atom hnr hb 140 (.mul (.n 276) (.n 144) (.n 275)) (by decide +kernel)
  have t276 := holds_atom hnr hb 141 (.load (.n 276) (.n 10) 10) (by decide +kernel)
  have a277 := holds_atom hnr hb 142 (.add (.n 277) (.n 170) (.n 186)) (by decide +kernel)
  have a278 := holds_atom hnr hb 143 (.mul (.n 278) (.n 274) (.n 277)) (by decide +kernel)
  have a279 := holds_atom hnr hb 144 (.add (.n 279) (.n 170) (.n 278)) (by decide +kernel)
  have t279 := holds_atom hnr hb 145 (.load (.n 279) (.n 10) 11) (by decide +kernel)
  have a280 := holds_atom hnr hb 146 (.add (.n 280) (.n 202) (.n 218)) (by decide +kernel)
  have a281 := holds_atom hnr hb 147 (.mul (.n 281) (.n 274) (.n 280)) (by decide +kernel)
  have a282 := holds_atom hnr hb 148 (.add (.n 282) (.n 202) (.n 281)) (by decide +kernel)
  have t282 := holds_atom hnr hb 149 (.load (.n 282) (.n 10) 12) (by decide +kernel)
  have a283 := holds_atom hnr hb 150 (.add (.n 283) (.n 234) (.n 250)) (by decide +kernel)
  have a284 := holds_atom hnr hb 151 (.mul (.n 284) (.n 274) (.n 283)) (by decide +kernel)
  have a285 := holds_atom hnr hb 152 (.add (.n 285) (.n 234) (.n 284)) (by decide +kernel)
  have t285 := holds_atom hnr hb 153 (.load (.n 285) (.n 10) 13) (by decide +kernel)
  have t154 := holds_atom hnr hb 154 (.load (.n 154) (.n 10) 14) (by decide +kernel)
  simp only [Atom.Holds, word_zero, word_g40, word_g6] at *
  have e128 : σ (.n 128) = (digestScalars cv).1 := loadHolds_unique l128 g0
  have e129 : σ (.n 129) = (digestScalars cv).2 := loadHolds_unique l129 g1
  have e144 : σ (.n 144) = cur := loadHolds_unique l144 g2
  have e145 : σ (.n 145) = s.values.getD 0 0 := loadHolds_unique l145 g3
  have e146 : σ (.n 146) = s.values.getD 1 0 := loadHolds_unique l146 g4
  have e147 : σ (.n 147) = s.values.getD 2 0 := loadHolds_unique l147 g5
  have e152 : σ (.n 152) = row := loadHolds_unique l152 g6
  obtain ⟨cv0, hcv0, hsq, h143⟩ := sq1
  have ecv : cv0 = cv := digestScalars_injective (by rw [← hcv0, e128, e129])
  subst ecv
  have f0 := (fsb 0 (by decide)).2
  have c0 := cpb 0 (by decide)
  have f1 := (fsb 1 (by decide)).2
  have c1 := cpb 1 (by decide)
  have f2 := (fsb 2 (by decide)).2
  have c2 := cpb 2 (by decide)
  have f3 := (fsb 3 (by decide)).2
  have c3 := cpb 3 (by decide)
  have f4 := (fsb 4 (by decide)).2
  have c4 := cpb 4 (by decide)
  have f5 := (fsb 5 (by decide)).2
  have c5 := cpb 5 (by decide)
  simp only [oddS, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, OfNat.ofNat_ne_zero,
    Nat.succ_ne_zero] at f0 f1 f2 f3 f4 f5 c0 c1 c2 c3 c4 c5
  have k0 := fs_chain hsq f0
  have k1 := fs_chain k0 f1
  have k2 := fs_chain k1 f2
  have k3 := fs_chain k2 f3
  have k4 := fs_chain k3 f4
  have k5 := fs_chain k4 f5
  have hE : (σ (.n 248), σ (.n 249)) = digestScalars (obsAll (obsAll (obsAll (sqCv cv0)
      [σ (.n 155), σ (.n 171)]) [σ (.n 187), σ (.n 203)]) [σ (.n 219), σ (.n 235)]) := k5
  obtain ⟨cvA, hA, hA', h274⟩ := sq2
  rw [hA] at hE
  have ecA := digestScalars_injective hE
  subst ecA
  have hpt0 : s.point = [] := List.length_eq_zero_iff.mp gpl
  have hsc : RunsTo (sumcheck (polyEval s.values (challengeOf (sqCv cv0))) (2 ^ 1 + 1)
      (s.point.map some)) (sqCv cv0) [] ([], polyEval s.values (challengeOf (sqCv cv0)))
      (sqCv cv0) := by
    rw [hpt0]; exact runsTo_ret _ _
  have hreq : polyEval s.values (challengeOf (sqCv cv0)) = polyEval [prodE [σ (.n 155), σ (.n 171)],
      prodE [σ (.n 187), σ (.n 203)], prodE [σ (.n 219), σ (.n 235)]] (challengeOf (sqCv cv0)) := by
    have hc := e_add_eq_zero_iff.mp ae
    rw [a151, a150, a149, a148, a260, a259, a258, a257, a256, a255, a254, a253, a252, a251, c0, c1,
      c2, c3, c4, c5, e145, e146, e147, h143] at hc
    rw [values_three gv, polyEval_three, polyEval_three, prodE_two, prodE_two, prodE_two, hc]
    ring
  have hrun := runsTo_gkrStep 1 hsc rfl rfl rfl hreq
  simp only [sqAll] at hrun
  rw [← h274] at hrun
  refine ⟨_, _, _, hrun, ?_, ?_⟩
  · rw [List.nil_append, ← e144]
    intro k hk
    have hk' : k < 6 := by simpa using hk
    obtain ⟨hl, -⟩ := fsb k hk'
    interval_cases k <;> exact hl
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · rw [← (congrArg Prod.fst hA')]; exact t266
  · rw [← (congrArg Prod.snd hA')]; exact t267
  · have : cur * gen ^ ([] ++ ([σ (.n 155), σ (.n 171)] ++ ([σ (.n 187), σ (.n 203)] ++
        [σ (.n 219), σ (.n 235)]))).length = σ (.n 276) := by
      rw [a276, a275, e144]; rfl
    rw [this]; exact t276
  · have : σ (.n 279) = multilinearEval [σ (.n 155), σ (.n 171)] [σ (.n 274)] := by
      rw [multilinearEval_two, a279, a278, a277, c0, c1]; ring
    simp only [List.map_cons, List.map_nil, List.getD_cons_zero]
    rw [← this]; exact t279
  · have : σ (.n 282) = multilinearEval [σ (.n 187), σ (.n 203)] [σ (.n 274)] := by
      rw [multilinearEval_two, a282, a281, a280, c2, c3]; ring
    simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
    rw [← this]; exact t282
  · have : σ (.n 285) = multilinearEval [σ (.n 219), σ (.n 235)] [σ (.n 274)] := by
      rw [multilinearEval_two, a285, a284, a283, c4, c5]; ring
    simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
    rw [← this]; exact t285
  · rw [a154, a153, e152] at t154; exact t154
  · rw [a154, a153, e152] at t274
    intro k hk
    have hk' : k < 1 := by simpa using hk
    interval_cases k
    exact t274

/-! ## `verify_bus_gkr` -/

theorem find_verify_bus_gkr : coreProgram.find? "verify_bus_gkr" = some Data.core10 :=
  Program.find?_of_indexOf? (j := 10) (by decide +kernel) rfl

/-- `verify_bus_gkr`'s statements before its `ret`. -/
noncomputable def gkrPre : List Stmt := (Fn.body Data.core10).take 218

theorem core10_body :
    Fn.body Data.core10 = gkrPre ++ [.ret [.n 305, .n 306, .n 307, .n 308, .n 309, .n 310]] :=
  stmtsEqb_sound (by decide +kernel)

theorem gkrPre_noRet : Stmt.noRetList gkrPre = true := by decide +kernel

/-- The stores of `pair_bounds[g^d] = g^(d/2)` and `depth_shift[g^d] = g^(d % 2)`. -/
theorem gkr_table_blocks : ∀ d < 33, stmtsEqb
    [.atom (.const (.n (58 + 2 * d)) (word (2 ^ (d / 2)) 0 0)),
      .atom (.load (.n (58 + 2 * d)) (.n 56) d),
      .atom (.const (.n (59 + 2 * d)) (word (2 ^ (d % 2)) 0 0)),
      .atom (.load (.n (59 + 2 * d)) (.n 57) d)]
    ((gkrPre.drop (55 + 4 * d)).take 4) = true := by decide +kernel

theorem word_g32 : word 4294967296 0 0 = gen ^ 32 := word_two_pow (a := 32) (by decide)

theorem gen_add_one_ne_zero : gen + 1 ≠ 0 := by
  intro h
  have h1 : gen ^ 1 = gen ^ 0 := by rw [pow_one, pow_zero]; exact e_add_eq_zero_iff.mp h
  exact absurd (gen_pow_inj (by decide) (by decide) h1) (by decide)

/-- **`verify_bus_gkr` is sound** on a memory of at most `2^32` words. -/
theorem verify_bus_gkr_sound {κ : ℕ} (hκ : κ ≤ 32) (Lm : MemImage κ) : SoundGkr Lm.read := by
  intro fs0 fs1 cur gmu zeta rets h
  obtain ⟨σ, hp, hb, hret⟩ := rel_pre find_verify_bus_gkr core10_body gkrPre_noRet h
  simp only [show Fn.params Data.core10 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq] at hp hret
  obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hp
  have hnr := gkrPre_noRet
  have a13 := holds_atom hnr hb 8 (.const (.n 13) (word 4294967296 0 0)) (by decide +kernel)
  have rc := holds_atom hnr hb 9 (.rangeCheck (.n 3) (.n 14) (.n 15) (.n 16) (.n 13))
    (by decide +kernel)
  have a17 := holds_atom hnr hb 10 (.copy (.n 17) (.n 0)) (by decide +kernel)
  have a18 := holds_atom hnr hb 11 (.copy (.n 18) (.n 1)) (by decide +kernel)
  have fs1b := holds_fsNextAt hnr hb 12 (.n 17) (.n 18) (.n 2) 0 19 (by decide +kernel)
  have fs2b := holds_fsNextAt hnr hb 25 (.n 32) (.n 33) (.n 2) 1 34 (by decide +kernel)
  have a49 := holds_atom hnr hb 38 (.const (.n 49) (word 0 0 0)) (by decide +kernel)
  have a50 := holds_atom hnr hb 39 (.add (.n 50) (.n 34) (.n 49)) (by decide +kernel)
  have ne := holds_atom hnr hb 41 (.assertNe (.n 50) (.n 51) (.n 52)) (by decide +kernel)
  have s47 := holds_atom hnr hb 42 (.load (.n 47) (.n 10) 0) (by decide +kernel)
  have s48 := holds_atom hnr hb 43 (.load (.n 48) (.n 10) 1) (by decide +kernel)
  have a53 := holds_atom hnr hb 44 (.const (.n 53) (word 4 0 0)) (by decide +kernel)
  have a54 := holds_atom hnr hb 45 (.mul (.n 54) (.n 2) (.n 53)) (by decide +kernel)
  have s54 := holds_atom hnr hb 46 (.load (.n 54) (.n 10) 2) (by decide +kernel)
  have s19 := holds_atom hnr hb 47 (.load (.n 19) (.n 10) 3) (by decide +kernel)
  have s19' := holds_atom hnr hb 48 (.load (.n 19) (.n 10) 4) (by decide +kernel)
  have s34 := holds_atom hnr hb 49 (.load (.n 34) (.n 10) 5) (by decide +kernel)
  have s12 := holds_atom hnr hb 50 (.load (.n 12) (.n 10) 6) (by decide +kernel)
  have tb := fun d hd => holds_slice hnr hb (55 + 4 * d) _ (gkr_table_blocks d hd)
  have a124 := holds_atom hnr hb 187 (.mul (.n 124) (.n 57) (.n 3)) (by decide +kernel)
  have l125 := holds_atom hnr hb 188 (.load (.n 125) (.n 124) 0) (by decide +kernel)
  have a126 := holds_atom hnr hb 189 (.const (.n 126) (word 1 0 0)) (by decide +kernel)
  have a127 := holds_atom hnr hb 190 (.add (.n 127) (.n 125) (.n 126)) (by decide +kernel)
  have hite := holds_slice hnr hb 191 [.ite (.n 127) Data.core10.s191_t Data.core10.s191_e]
    (by decide +kernel)
  have a287 := holds_atom hnr hb 192 (.const (.n 287) (word 1 0 0)) (by decide +kernel)
  have a288 := holds_atom hnr hb 193 (.mul (.n 288) (.n 56) (.n 3)) (by decide +kernel)
  have l289 := holds_atom hnr hb 194 (.load (.n 289) (.n 288) 0) (by decide +kernel)
  have a290 := holds_atom hnr hb 195 (.add (.n 290) (.n 287) (.n 289)) (by decide +kernel)
  have a291 := holds_atom hnr hb 196 (.const (.n 291) (word 1 0 0)) (by decide +kernel)
  have a292 := holds_atom hnr hb 197 (.mul (.n 292) (.n 56) (.n 3)) (by decide +kernel)
  have l293 := holds_atom hnr hb 198 (.load (.n 293) (.n 292) 0) (by decide +kernel)
  have c10 := holds_callIf hnr hb 199 (.n 290) "__loop10"
    [.n 291, .n 293, .n 57, .n 3, .n 10, .n 11]
    (by decide +kernel)
  have a294 := holds_atom hnr hb 200 (.mul (.n 294) (.n 3) (.n 3)) (by decide +kernel)
  have a295 := holds_atom hnr hb 201 (.mul (.n 295) (.n 294) (.n 294)) (by decide +kernel)
  have a296 := holds_atom hnr hb 202 (.mul (.n 296) (.n 295) (.n 295)) (by decide +kernel)
  have a297 := holds_atom hnr hb 203 (.mul (.n 297) (.n 10) (.n 296)) (by decide +kernel)
  have l298 := holds_atom hnr hb 204 (.load (.n 298) (.n 297) 0) (by decide +kernel)
  have l299 := holds_atom hnr hb 205 (.load (.n 299) (.n 297) 1) (by decide +kernel)
  have l300 := holds_atom hnr hb 206 (.load (.n 300) (.n 297) 2) (by decide +kernel)
  have l301 := holds_atom hnr hb 207 (.load (.n 301) (.n 297) 6) (by decide +kernel)
  have a302 := holds_atom hnr hb 208 (.const (.n 302) (word 1 0 0)) (by decide +kernel)
  have a303 := holds_atom hnr hb 209 (.add (.n 303) (.n 302) (.n 3)) (by decide +kernel)
  have a304 := holds_atom hnr hb 210 (.const (.n 304) (word 1 0 0)) (by decide +kernel)
  have c11 := holds_callIf hnr hb 211 (.n 303) "__loop11" [.n 304, .n 3, .n 4, .n 301]
    (by decide +kernel)
  have a305 := holds_atom hnr hb 212 (.copy (.n 305) (.n 298)) (by decide +kernel)
  have a306 := holds_atom hnr hb 213 (.copy (.n 306) (.n 299)) (by decide +kernel)
  have a307 := holds_atom hnr hb 214 (.copy (.n 307) (.n 300)) (by decide +kernel)
  have l308 := holds_atom hnr hb 215 (.load (.n 308) (.n 297) 3) (by decide +kernel)
  have l309 := holds_atom hnr hb 216 (.load (.n 309) (.n 297) 4) (by decide +kernel)
  have l310 := holds_atom hnr hb 217 (.load (.n 310) (.n 297) 5) (by decide +kernel)
  simp only [Atom.Holds, word_one, word_zero, word_four, word_g32, List.map_cons,
    List.map_nil] at *
  -- the depth
  obtain ⟨d, hd, hgmu⟩ := rc_sound' hκ Lm (K := 33) (by norm_num) (by norm_num)
    (by rw [a13, gen_pow_eq_ofK]) rc.1 rc.2.1 rc.2.2
  have hord : d < ordG := by unfold ordG; omega
  -- the roots
  obtain ⟨l19, cvq, hcvq, h32⟩ := fs1b
  obtain ⟨l34, h47⟩ := fs2b
  rw [a17, a18] at hcvq
  have k1 := fs_chain h32 h47
  have hne34 : σ (.n 34) ≠ 0 := by
    intro h0
    rw [a50, a49, h0, add_zero, zero_mul] at ne
    exact zero_ne_one (ne.1.symm.trans ne.2)
  -- the slot of the empty point
  have hL0 : GkrLayer Lm.read (σ (.n 10)) 0 (obsCv (obsCv cvq (σ (.n 19))) (σ (.n 34)))
      (σ (.n 2) * gen ^ 2) ⟨[σ (.n 19), σ (.n 19), σ (.n 34)], []⟩ (σ (.n 12)) := by
    refine ⟨?_, ?_, ?_, rfl, s19, s19', s34, s12, rfl, readsAt_nil _ _⟩
    · rw [← congrArg Prod.fst k1]; exact s47
    · rw [← congrArg Prod.snd k1]; exact s48
    · rw [← a53, ← a54]; exact s54
  -- the tables
  have htab : ∀ e < 33, LoadHolds Lm.read (σ (.n 56)) e (gen ^ (e / 2)) ∧
      LoadHolds Lm.read (σ (.n 57)) e (gen ^ (e % 2)) := by
    intro e he
    have := tb e he
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
    obtain ⟨c1, l1, c2, l2⟩ := this
    rw [c1, word_two_pow (by omega)] at l1
    rw [c2, word_two_pow (by omega)] at l2
    exact ⟨l1, l2⟩
  have hsh : LoadHolds Lm.read (σ (.n 57) * σ (.n 3)) 0 (gen ^ (d % 2)) := by
    rw [hgmu, loadHolds_gen_pow_mul]; exact (htab d hd).2
  rw [a124] at l125
  have e125 : σ (.n 125) = gen ^ (d % 2) := loadHolds_unique l125 hsh
  -- the binary layer
  have hstart : ∃ (ys : List E) (s : GkrState) (cv' : Digest) (row : E),
      ReadsAt Lm.read (σ (.n 2) * gen ^ 2) ys ∧
      RunsTo (if d % 2 = 1 then gkrStep 1 ⟨[σ (.n 19), σ (.n 19), σ (.n 34)], []⟩
        else pure ⟨[σ (.n 19), σ (.n 19), σ (.n 34)], []⟩)
        (obsCv (obsCv cvq (σ (.n 19))) (σ (.n 34))) ys s cv' ∧
      GkrLayer Lm.read (σ (.n 10)) (d % 2) cv' (σ (.n 2) * gen ^ 2 * gen ^ ys.length) s row := by
    simp only [Stmt.HoldsList] at hite
    obtain ⟨⟨-, -, hodd⟩, -⟩ := (holds_ite_noRet _ _ _ rfl s191_noRet _ _).mp hite
    rcases Nat.mod_two_eq_zero_or_one d with h0 | h1
    · refine ⟨[], ⟨[σ (.n 19), σ (.n 19), σ (.n 34)], []⟩,
        obsCv (obsCv cvq (σ (.n 19))) (σ (.n 34)),
        σ (.n 12), readsAt_nil _ _, ?_, ?_⟩
      · simp only [h0, zero_ne_one, ↓reduceIte]; exact runsTo_ret _ _
      · rw [h0, List.length_nil, pow_zero, mul_one]; exact hL0
    · have hn : σ (.n 127) ≠ 0 := by
        rw [a127, e125, a126, h1, pow_one]; exact gen_add_one_ne_zero
      obtain ⟨ys, s', cv', hrun, hrd, hl⟩ := odd_layer (hodd hn) hL0
      refine ⟨ys, s', cv', σ (.n 12) * gen ^ 40, hrd, ?_, ?_⟩
      · simp only [h1, ↓reduceIte]; exact hrun
      · rw [h1]; exact hl
  -- the layers of two levels
  rw [a288, hgmu, loadHolds_gen_pow_mul, Nat.add_zero] at l289
  rw [a292, hgmu, loadHolds_gen_pow_mul, Nat.add_zero] at l293
  have e289 : σ (.n 289) = gen ^ (d / 2) := loadHolds_unique l289 (htab d hd).1
  have e293 : σ (.n 293) = gen ^ (d / 2) := loadHolds_unique l293 (htab d hd).1
  have hP : ∀ j < d / 2, GkrPairStep Lm.read (σ (.n 10)) (σ (.n 57)) (σ (.n 3)) (gen ^ j) :=
    Main.loop_sound (ps := [σ (.n 293), σ (.n 57), σ (.n 3), σ (.n 10), σ (.n 11)])
      (N := σ (.n 293)) (by unfold ordG; omega) e293 (fun x hx => (loop10_step hx))
      (fun hne => by
        have := c10 (by rw [a290, a287, e289, ← e293]; exact hne)
        rw [a291] at this
        exact this)
  have hit : ∀ i ≤ d / 2, ∃ (ys : List E) (s : GkrState) (cv' : Digest) (row : E),
      ReadsAt Lm.read (σ (.n 2) * gen ^ 2) ys ∧
      RunsTo ((if d % 2 = 1 then gkrStep 1 ⟨[σ (.n 19), σ (.n 19), σ (.n 34)], []⟩
        else pure ⟨[σ (.n 19), σ (.n 19), σ (.n 34)], []⟩) >>= gkrPairs i)
        (obsCv (obsCv cvq (σ (.n 19))) (σ (.n 34))) ys s cv' ∧
      GkrLayer Lm.read (σ (.n 10)) (2 * i + d % 2) cv' (σ (.n 2) * gen ^ 2 * gen ^ ys.length) s
        row := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨ys, s, cv', row, hrd, hrun, hl⟩ := hstart
      refine ⟨ys, s, cv', row, hrd, ?_, by rw [Nat.mul_zero, Nat.zero_add]; exact hl⟩
      rw [show gkrPairs 0 = pure from rfl, bind_pure]
      exact hrun
    | succ i ih =>
      intro hi
      obtain ⟨ys, s, cv', row, hrd, hrun, hl⟩ := ih (by omega)
      obtain ⟨ys2, s2, cv2, hrun2, hrd2, hl2⟩ := hP i (by omega) i (d % 2) rfl hsh (by omega)
        (Nat.mod_lt _ (by decide)) cv' _ s row hl
      refine ⟨ys ++ ys2, s2, cv2, row * gen ^ 40, readsAt_append_pow hrd hrd2, ?_, ?_⟩
      · rw [show gkrPairs (i + 1) = fun t => gkrPairs i t >>= gkrStep 2 from rfl, ← bind_assoc]
        exact hrun.bind hrun2
      · rw [show 2 * (i + 1) + d % 2 = 2 * i + d % 2 + 2 by ring, List.length_append, pow_add,
          ← mul_assoc]
        exact hl2
  obtain ⟨ys, sF, cvF, row, hrd, hrun, hl⟩ := hit (d / 2) le_rfl
  rw [Nat.div_add_mod] at hl
  have hlay : RunsTo (gkrLayers d ⟨[σ (.n 19), σ (.n 19), σ (.n 34)], []⟩)
      (obsCv (obsCv cvq (σ (.n 19))) (σ (.n 34))) ys sF cvF := by
    rcases Nat.mod_two_eq_zero_or_one d with h0 | h1
    · rw [show d = 2 * (d / 2) by omega, gkrLayers_even]
      simp only [h0, zero_ne_one, ↓reduceIte, pure_bind] at hrun
      exact hrun
    · rw [show d = 2 * (d / 2) + 1 by omega, gkrLayers_odd]
      simp only [h1, ↓reduceIte] at hrun
      exact hrun
  -- the last slot
  obtain ⟨g0, g1, g2, gv, g3, g4, g5, g6, gpl, gpt⟩ := hl
  have hF : ∀ k w, LoadHolds Lm.read (σ (.n 297)) k w ↔
      LoadHolds Lm.read (σ (.n 10)) (8 * d + k) w := by
    intro k w
    rw [show σ (.n 297) = σ (.n 10) * gen ^ (8 * d) by
      rw [a297, a296, a295, a294, hgmu]; ring, loadHolds_gen_pow_mul]
  have e298 := loadHolds_unique ((hF 0 _).mp l298) g0
  have e299 := loadHolds_unique ((hF 1 _).mp l299) g1
  have e300 := loadHolds_unique ((hF 2 _).mp l300) g2
  have e301 := loadHolds_unique ((hF 6 _).mp l301) g6
  have e308 := loadHolds_unique ((hF 3 _).mp l308) g3
  have e309 := loadHolds_unique ((hF 4 _).mp l309) g4
  have e310 := loadHolds_unique ((hF 5 _).mp l310) g5
  have hz : ReadsAt Lm.read (σ (.n 4)) sF.point := by
    refine loop11_sound (zeta := σ (.n 4)) (row := σ (.n 301)) (m := d) hord
      (by rw [e301]; exact gpt) gpl (fun hne => ?_)
    have := c11 (by rw [a303, a302, hgmu]; exact hne)
    rw [a304, hgmu] at this
    exact this
  have hv : RunsTo (verifyGkrGrandProducts d) cvq ([σ (.n 19)] ++ ([σ (.n 34)] ++ (ys ++ [])))
      (σ (.n 34), sF.point, sF.values) cvF := by
    unfold verifyGkrGrandProducts
    refine (runsTo_readE cvq _).bind ?_
    refine (runsTo_readE _ _).bind ?_
    refine hlay.bind ?_
    exact runsTo_ret _ _
  refine ⟨cvq, d, [σ (.n 19), σ (.n 34)] ++ ys, (σ (.n 34), sF.point, sF.values), cvF, hcvq, hgmu,
    hd, ?_, ?_, gpl, gv, hz, ?_⟩
  · refine readsAt_append_pow ?_
      (by simp only [List.length_cons, List.length_nil, Nat.reduceAdd]; exact hrd)
    intro k hk
    have hk' : k < 2 := by simpa using hk
    interval_cases k
    · exact l19
    · exact l34
  · unfold gkrPhase
    exact (hv.bind (RunsTo.bind (f := fun (_ : Unit) =>
      (pure (σ (.n 34), sF.point, sF.values) : Prog (E × List E × List E)))
      (runsTo_require hne34 _) (runsTo_ret _ _))).of_eq (by simp) rfl rfl
  · rw [← hret, a305, a306, a307, e298, e299, e300, values_three gv, ← e308, ← e309, ← e310]
    simp only [List.length_cons, List.cons_append, List.nil_append, List.cons.injEq, and_true,
      true_and]
    rw [mul_assoc, ← pow_add]
    exact congrArg (fun n => σ (.n 2) * gen ^ n) (by omega)

end
end LeanVM.Guest.B1.VerifySub
