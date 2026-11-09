/-
  LeanVM.Guest.B1.Ring.Target

  B1 of `ring_switch_target`: its core IR computes `Σ_i g^i Φ(s_i)`.
-/

module

public import LeanVM.Guest.B1.Ring.Weight

/-!
# `ring_switch_target` (TRIAGE G #64, #65)

`ring_switch_target(slices, map_challenges)` (G:3102-3119, `Data.core13`) seeds a two-slot chain
`(x^0, 0)` and runs `__loop13` (`Data.core269`) for `x = g^j`, `j < 8`: the loop body evaluates
`Φ` (`ring_map`, G:3092-3098, inline: six stages, each `lin + f_p · lin^(2^shift)` by `shift`
squarings, `stageT`) on the eight slices `8j .. 8j + 7` and combines them in Horner form by `g`
(the chunk `Σ_i g^i Φ(s_(8j+i))`), then extends the chain: `x^0 ← x^0·g^8`,
`sum ← sum + x^0·chunk`. The chain's last sum is `polyEval (s.map Φ) g`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## One stage of `ring_map` -/

/-- The value squaring `i` reads: `lin`, then the previous square. -/
def sqSrc (lin : V) (b : ℕ) : ℕ → V
  | 0 => lin
  | i + 1 => .n (b + i)

/-- `d` squarings of `lin` into `b .. b + d - 1`. -/
def sqChainT (lin : V) (b d : ℕ) : List Stmt :=
  ((List.range d).map fun i ↦ [.atom (.mul (.n (b + i)) (sqSrc lin b i) (sqSrc lin b i))]).flatten

/-- One stage (`d ≥ 1` squarings): `lin^(2^d)` into `b + d - 1`, the challenge `map[s]` into
`b + d`, the product into `b + d + 1`, `lin + f·lin^(2^d)` into `b + d + 2`. -/
def stageT (lin : V) (b d s : ℕ) : List Stmt :=
  sqChainT lin b d ++
    [.atom (.load (.n (b + d)) (.n 2) s), .atom (.mul (.n (b + d + 1)) (.n (b + d)) (.n (b + d - 1))),
      .atom (.add (.n (b + d + 2)) lin (.n (b + d + 1)))]

/-- `ring_map` on `lin`, its values from `b`: six stages of `32, 16, 8, 4, 2, 1` squarings; the
result at `b + 80`. -/
def rmapT (lin : V) (b : ℕ) : List Stmt :=
  stageT lin b 32 0 ++ stageT (.n (b + 34)) (b + 35) 16 1 ++ stageT (.n (b + 53)) (b + 54) 8 2 ++
    stageT (.n (b + 64)) (b + 65) 4 3 ++ stageT (.n (b + 71)) (b + 72) 2 4 ++
    stageT (.n (b + 76)) (b + 77) 1 5

theorem holds_sqChainT {lin : V} {b d : ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (sqChainT lin b d) next kret) :
    (∀ i < d, σ (.n (b + i)) = σ lin ^ 2 ^ (i + 1)) ∧ next := by
  obtain ⟨hall, hn⟩ := (holdsList_range_flatten d _ (fun _ ↦ rfl) next kret).mp h
  refine ⟨fun i hi => ?_, hn⟩
  have hsq : ∀ j < d, σ (.n (b + j)) = σ (sqSrc lin b j) * σ (sqSrc lin b j) := by
    intro j hj
    simpa [Stmt.HoldsList, Stmt.Holds, Atom.Holds] using hall j hj
  induction i with
  | zero => rw [hsq 0 hi]; simp [sqSrc, pow_two]
  | succ i ih =>
    rw [hsq (i + 1) hi, sqSrc, ih (by omega), ← pow_two, ← pow_mul, ← pow_succ]

theorem sqChainT_noRet (lin : V) (b d : ℕ) : Stmt.noRetList (sqChainT lin b d) = true :=
  noRetList_flatten_map _ (fun _ ↦ rfl) _

theorem stageT_noRet (lin : V) (b d s : ℕ) : Stmt.noRetList (stageT lin b d s) = true := by
  rw [stageT, noRetList_append, sqChainT_noRet]; rfl

/-- **One stage**: with the challenge `f = map[s]` (`d ≥ 1`), `b + d + 2` holds
`lin + f·lin^(2^d)`. -/
theorem holds_stageT {lin : V} {b d s : ℕ} (hd : 1 ≤ d) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (stageT lin b d s) next kret) :
    (LoadHolds rd (σ (.n 2)) s (σ (.n (b + d))) ∧
      σ (.n (b + d + 2)) = σ lin + σ (.n (b + d)) * σ lin ^ 2 ^ d) ∧ next := by
  rw [stageT, holdsList_append] at h
  obtain ⟨hsq, h⟩ := holds_sqChainT h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨hl, hm, ha, hn⟩ := h
  refine ⟨⟨hl, ?_⟩, hn⟩
  rw [ha, hm, show b + d - 1 = b + (d - 1) by omega, hsq (d - 1) (by omega),
    show d - 1 + 1 = d by omega]

theorem rmapT_noRet (lin : V) (b : ℕ) : Stmt.noRetList (rmapT lin b) = true := by
  simp only [rmapT, noRetList_append, stageT_noRet]; rfl

/-- **`ring_map`** (G:3093-3099): the six challenges it loads from `map_challenges` (value `2`),
and `Φ` of `lin` at them (`phiMap`, V:2103) at `b + 80`. -/
theorem holds_rmapT {lin : V} {b : ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (rmapT lin b) next kret) :
    (ReadsAt rd (σ (.n 2)) [σ (.n (b + 32)), σ (.n (b + 51)), σ (.n (b + 62)), σ (.n (b + 69)),
        σ (.n (b + 74)), σ (.n (b + 78))] ∧
      σ (.n (b + 80)) = phiMap (σ lin) [σ (.n (b + 32)), σ (.n (b + 51)), σ (.n (b + 62)),
        σ (.n (b + 69)), σ (.n (b + 74)), σ (.n (b + 78))]) ∧ next := by
  simp only [rmapT, holdsList_append] at h
  obtain ⟨⟨l0, e0⟩, h⟩ := holds_stageT (by decide) h
  obtain ⟨⟨l1, e1⟩, h⟩ := holds_stageT (by decide) h
  obtain ⟨⟨l2, e2⟩, h⟩ := holds_stageT (by decide) h
  obtain ⟨⟨l3, e3⟩, h⟩ := holds_stageT (by decide) h
  obtain ⟨⟨l4, e4⟩, h⟩ := holds_stageT (by decide) h
  obtain ⟨⟨l5, e5⟩, h⟩ := holds_stageT (by decide) h
  refine ⟨⟨?_, ?_⟩, h⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact l0
    · exact l1
    · exact l2
    · exact l3
    · exact l4
    · exact l5
  · simp only [Nat.add_assoc, Nat.reduceAdd] at e0 e1 e2 e3 e4 e5 ⊢
    rw [e5, e4, e3, e2, e1, e0]
    rfl

/-! ## The loop body (`__loop13`) -/

/-- The first value of row `r ≥ 1` of a chunk: `5 + 85r`. -/
abbrev ltBase (r : ℕ) : ℕ := 5 + 85 * r

/-- Row `r ∈ 1..7` of a chunk: `chunk·g` (the constant `2 = g` at `ltBase r`), the slice
`7 - r` of the chunk read, `Φ` of it, the sum at `ltBase r + 84`. -/
def ltRow (r : ℕ) : List Stmt :=
  [.atom (.const (.n (ltBase r)) (word 2 0 0)),
    .atom (.mul (.n (ltBase r + 1)) (.n (if r = 1 then 89 else ltBase r - 1)) (.n (ltBase r))),
    .atom (.load (.n (ltBase r + 2)) (.n 7) (7 - r))] ++ rmapT (.n (ltBase r + 2)) (ltBase r + 3) ++
  [.atom (.add (.n (ltBase r + 84)) (.n (ltBase r + 1)) (.n (ltBase r + 83)))]

/-- `__loop13`'s body. -/
def loop14T : List Stmt :=
  [.atom (.mul (.n 4) (.n 0) (.n 0)), .atom (.mul (.n 5) (.n 4) (.n 4)),
    .atom (.mul (.n 6) (.n 5) (.n 5)), .atom (.mul (.n 7) (.n 1) (.n 6)),
    .atom (.load (.n 8) (.n 7) 7)] ++ rmapT (.n 8) 9 ++
  ((List.range 7).map fun r ↦ ltRow (r + 1)).flatten ++
  [.atom (.mul (.n 685) (.n 0) (.n 0)), .atom (.mul (.n 686) (.n 3) (.n 685)),
    .atom (.load (.n 687) (.n 686) 0), .atom (.const (.n 688) (word 256 0 0)),
    .atom (.mul (.n 689) (.n 687) (.n 688)), .atom (.load (.n 689) (.n 686) 2),
    .atom (.load (.n 690) (.n 686) 1), .atom (.mul (.n 691) (.n 687) (.n 684)),
    .atom (.add (.n 692) (.n 690) (.n 691)), .atom (.load (.n 692) (.n 686) 3),
    .atom (.const (.n 693) (word 2 0 0)), .atom (.mul (.n 694) (.n 0) (.n 693)),
    .atom (.const (.n 695) (word 256 0 0)), .atom (.add (.n 696) (.n 694) (.n 695)),
    .atom (.const (.n 697) (word 2 0 0)), .atom (.mul (.n 698) (.n 0) (.n 697)),
    .callIf (.n 696) "__loop13" [.n 698, .n 1, .n 2, .n 3], .ret []]

theorem loop14_body : Data.core269.body = loop14T := stmtsEqb_sound (by decide +kernel)

theorem find_loop14 : coreProgram.find? "__loop13" = some Data.core269 :=
  Program.find?_of_indexOf? (j := 269) (by decide +kernel) rfl

theorem ltRow_noRet (r : ℕ) : Stmt.noRetList (ltRow r) = true := by
  simp only [ltRow, noRetList_append, rmapT_noRet]; rfl

/-- What row `r` of a chunk asks of a valuation. -/
theorem holds_ltRow {r : ℕ} {kret : List E → Prop} (h : Stmt.HoldsList C rd σ (ltRow r) True kret) :
    σ (.n (ltBase r + 1)) = σ (.n (if r = 1 then 89 else ltBase r - 1)) * gen ∧
      LoadHolds rd (σ (.n 7)) (7 - r) (σ (.n (ltBase r + 2))) ∧
      ReadsAt rd (σ (.n 2)) [σ (.n (ltBase r + 3 + 32)), σ (.n (ltBase r + 3 + 51)),
        σ (.n (ltBase r + 3 + 62)), σ (.n (ltBase r + 3 + 69)), σ (.n (ltBase r + 3 + 74)),
        σ (.n (ltBase r + 3 + 78))] ∧
      σ (.n (ltBase r + 84)) = σ (.n (ltBase r + 1)) +
        phiMap (σ (.n (ltBase r + 2))) [σ (.n (ltBase r + 3 + 32)), σ (.n (ltBase r + 3 + 51)),
          σ (.n (ltBase r + 3 + 62)), σ (.n (ltBase r + 3 + 69)), σ (.n (ltBase r + 3 + 74)),
          σ (.n (ltBase r + 3 + 78))] := by
  rw [ltRow, holdsList_append, holdsList_append] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨e0, e1, l2, h⟩ := h
  obtain ⟨⟨rl, rv⟩, h⟩ := holds_rmapT h
  simp only [and_true] at h
  refine ⟨by rw [e1, e0, word_gen], l2, rl, ?_⟩
  rw [h, ← rv, show ltBase r + 3 + 80 = ltBase r + 83 by omega]

/-- The chunk of slices `vs` (eight): `Σ_i g^i Φ(vs_i)`. -/
def rsChunk (vs chs : List E) : E := ∑ i ∈ Finset.range 8, gen ^ i * phiMap (vs.getD i 0) chs

/-- **The loop body's meaning at `x`**: the eight slices at `slices·x^8`, the chain's row at
`chain·x^2` holds `(x₀, run)` and the next row `(x₀·g^8, run + x₀·chunk)`. -/
def RowOk (rd : Reader) (sl mc ch x : E) : Prop :=
  ∃ (vs : List E) (xp run : E), vs.length = 8 ∧ ReadsAt rd (sl * x ^ 8) vs ∧
    LoadHolds rd (ch * x ^ 2) 0 xp ∧ LoadHolds rd (ch * x ^ 2) 1 run ∧
    LoadHolds rd (ch * x ^ 2) 2 (xp * gen ^ 8) ∧
    (∃ chs : List E, chs.length = 6 ∧ ReadsAt rd mc chs) ∧
    ∀ chs : List E, chs.length = 6 → ReadsAt rd mc chs →
      LoadHolds rd (ch * x ^ 2) 3 (run + xp * rsChunk vs chs)

theorem readsAt_six_unique {p : E} {a b c d e f : E} {chs : List E} (hl : chs.length = 6)
    (h : ReadsAt rd p chs) (h' : ReadsAt rd p [a, b, c, d, e, f]) : [a, b, c, d, e, f] = chs := by
  apply List.ext_getElem (by simp [hl])
  intro k hk _
  exact loadHolds_unique (h' k hk) (h k (by simp at hk; omega))

/-- **`__loop13`'s step**: at depth `d + 1` and `x`, the body's meaning, and the call at `x·g`
one level shallower unless `x·g = g^8`. -/
theorem loop14_step (d : ℕ) (x sl mc ch : E)
    (h : coreProgram.relN rd (d + 1) "__loop13" [x, sl, mc, ch] []) :
    RowOk rd sl mc ch x ∧
      (x * gen + gen ^ 8 ≠ 0 → coreProgram.relN rd d "__loop13" [x * gen, sl, mc, ch] []) := by
  obtain ⟨fn, hf, σ, hpar, hb⟩ := h
  rw [find_loop14] at hf
  cases hf
  simp only [Data.core269, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar hb
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hpar
  rw [loop14_body] at hb
  simp only [loop14T, holdsList_append] at hb
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hb
  obtain ⟨e4, e5, e6, e7, l8, hb⟩ := hb
  obtain ⟨⟨rl0, rv0⟩, hb⟩ := holds_rmapT hb
  obtain ⟨hrows, e685, e686, l687, e688, e689, l689, l690, e691, e692, l692, e693, e694, e695,
    e696, e697, e698, -, hcall, -⟩ :=
    (holdsList_range_flatten 7 (fun r ↦ ltRow (r + 1)) (fun r ↦ ltRow_noRet (r + 1)) _ _).mp hb
  have w1 := holds_ltRow (hrows 0 (by decide))
  have w2 := holds_ltRow (hrows 1 (by decide))
  have w3 := holds_ltRow (hrows 2 (by decide))
  have w4 := holds_ltRow (hrows 3 (by decide))
  have w5 := holds_ltRow (hrows 4 (by decide))
  have w6 := holds_ltRow (hrows 5 (by decide))
  have w7 := holds_ltRow (hrows 6 (by decide))
  simp only [ltBase, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, ↓reduceIte,
    show ¬ (2 : ℕ) = 1 by decide, show ¬ (3 : ℕ) = 1 by decide, show ¬ (4 : ℕ) = 1 by decide,
    show ¬ (5 : ℕ) = 1 by decide, show ¬ (6 : ℕ) = 1 by decide, show ¬ (7 : ℕ) = 1 by decide]
    at w1 w2 w3 w4 w5 w6 w7
  simp only [Nat.reduceAdd] at rl0 rv0
  have hx8 : σ (.n 6) = σ (.n 0) ^ 8 := by rw [e6, e5, e4]; ring
  have hx2 : σ (.n 686) = σ (.n 3) * σ (.n 0) ^ 2 := by rw [e686, e685]; ring
  refine ⟨⟨[σ (.n 602), σ (.n 517), σ (.n 432), σ (.n 347), σ (.n 262), σ (.n 177), σ (.n 92),
    σ (.n 8)], σ (.n 687), σ (.n 690), rfl, ?_, ?_, ?_, ?_, ⟨_, rfl, rl0⟩, fun chs hl hchs => ?_⟩,
    ?_⟩
  · rw [← hx8, ← e7]
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact w7.2.1
    · exact w6.2.1
    · exact w5.2.1
    · exact w4.2.1
    · exact w3.2.1
    · exact w2.2.1
    · exact w1.2.1
    · exact l8
  · rw [← hx2]; exact l687
  · rw [← hx2]; exact l690
  · rw [← hx2, ← word_two_pow (by decide : 8 < 64)]
    rw [e689, e688] at l689
    exact l689
  · rw [← hx2]
    rw [e692, e691] at l692
    rw [readsAt_six_unique hl hchs rl0] at rv0
    rw [readsAt_six_unique hl hchs w1.2.2.1] at w1
    rw [readsAt_six_unique hl hchs w2.2.2.1] at w2
    rw [readsAt_six_unique hl hchs w3.2.2.1] at w3
    rw [readsAt_six_unique hl hchs w4.2.2.1] at w4
    rw [readsAt_six_unique hl hchs w5.2.2.1] at w5
    rw [readsAt_six_unique hl hchs w6.2.2.1] at w6
    rw [readsAt_six_unique hl hchs w7.2.2.1] at w7
    convert l692 using 3
    rw [w7.2.2.2, w7.1, w6.2.2.2, w6.1, w5.2.2.2, w5.1, w4.2.2.2, w4.1, w3.2.2.2, w3.1, w2.2.2.2,
      w2.1, w1.2.2.2, w1.1, rv0]
    simp only [rsChunk, Finset.sum_range_succ, Finset.sum_range_zero, List.getD_cons_zero,
      List.getD_cons_succ, pow_zero, pow_one, one_mul, zero_add]
    ring
  · intro hne
    have e : σ (.n 696) = σ (.n 0) * gen + gen ^ 8 := by
      rw [e696, e694, e693, e695, word_gen, ← word_two_pow (by decide : 8 < 64)]; rfl
    have e' : σ (.n 698) = σ (.n 0) * gen := by rw [e698, e697, word_gen]
    have := hcall (by rw [e]; exact hne)
    simpa [e'] using this

/-! ## `ring_switch_target` -/

/-- `ring_switch_target`'s body. -/
def rstT : List Stmt :=
  [.atom (.hint (.alloc (.n 2) 18)), .atom (.const (.n 3) (word 1 0 0)),
    .atom (.load (.n 3) (.n 2) 0), .atom (.const (.n 4) (word 0 0 0)),
    .atom (.load (.n 4) (.n 2) 1), .atom (.const (.n 5) (word 1 0 0)),
    .call "__loop13" [.n 5, .n 0, .n 1, .n 2] [], .atom (.const (.n 6) (word 65536 0 0)),
    .atom (.mul (.n 7) (.n 2) (.n 6)), .atom (.load (.n 8) (.n 7) 1), .ret [.n 8]]

theorem rst_body : Data.core13.body = rstT := stmtsEqb_sound (by decide +kernel)

theorem find_rst : coreProgram.find? "ring_switch_target" = some Data.core13 :=
  Program.find?_of_indexOf? (j := 13) (by decide +kernel) rfl

/-- `polyEval` as a sum (`Σ_t l_t·x^t`). -/
theorem polyEval_eq_sum (x : E) :
    ∀ l : List E, polyEval l x = ∑ t ∈ Finset.range l.length, l.getD t 0 * x ^ t
  | [] => by simp [polyEval]
  | c :: l => by
    rw [show polyEval (c :: l) x = polyEval l x * x + c from rfl, polyEval_eq_sum x l,
      List.length_cons, Finset.sum_range_succ', Finset.sum_mul]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ, mul_assoc]

theorem loadHolds_sq {p x : E} {j k : ℕ} {w : E} (hx : x = gen ^ j) :
    LoadHolds rd (p * x ^ 2) k w ↔ LoadHolds rd p (2 * j + k) w := by
  rw [hx, ← pow_mul, show j * 2 = 2 * j by ring, loadHolds_mul_gen_pow]

/-- **`ring_switch_target` computes `Σ_i g^i Φ(s_i)`.** -/
theorem ring_switch_target_holds : ring_switch_target_Spec := by
  intro rd args rets h
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem find_rst args rets).mp h
  simp only [Data.core13, List.map_cons, List.map_nil] at hpar hb
  subst hpar
  rw [rst_body] at hb
  simp only [rstT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨-, e3, l3, e4, l4, e5, hloop, e6, e7, l8, hret⟩ := hb
  have hrows : ∀ j, j < 8 → RowOk rd (σ (.n 0)) (σ (.n 1)) (σ (.n 2)) (gen ^ j) := by
    have := loop_sound (P := coreProgram) (f := "__loop13") (ps := [σ (.n 0), σ (.n 1), σ (.n 2)])
      (N := gen ^ 8) (m := 8) (B := RowOk rd (σ (.n 0)) (σ (.n 1)) (σ (.n 2)))
      (fun d x h => loop14_step d x _ _ _ h) rfl (by decide) 0
      (by rw [pow_zero, ← word_one, ← e5]; exact hloop)
    exact fun j hj => this j (Nat.zero_le j) hj
  choose vs xp run hvl hvs hxp hrun hnext hch hval using hrows
  obtain ⟨chs, hcl, hchs⟩ := hch 0 (by decide)
  let sOf : ℕ → E := fun t ↦ if h : t / 8 < 8 then (vs (t / 8) h).getD (t % 8) 0 else 0
  let S : ℕ → E := fun j ↦ ∑ t ∈ Finset.range (8 * j), gen ^ t * phiMap (sOf t) chs
  have hchain : ∀ j ≤ 8, LoadHolds rd (σ (.n 2)) (2 * j) (gen ^ (8 * j)) ∧
      LoadHolds rd (σ (.n 2)) (2 * j + 1) (S j) := by
    intro j hj
    induction j with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [e3, word_one] at l3; simpa using l3
      · rw [e4, word_zero] at l4; simpa [S] using l4
    | succ j ih =>
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hj8 : j < 8 := by omega
      have x0 := (loadHolds_sq rfl).mp (hxp j hj8)
      have r0 := (loadHolds_sq rfl).mp (hrun j hj8)
      have n2 := (loadHolds_sq rfl).mp (hnext j hj8)
      have n3 := (loadHolds_sq rfl).mp (hval j hj8 chs hcl hchs)
      simp only [Nat.add_zero] at x0
      rw [loadHolds_unique x0 ih1] at n2 n3
      rw [loadHolds_unique r0 ih2] at n3
      refine ⟨?_, ?_⟩
      · rw [show 2 * (j + 1) = 2 * j + 2 by ring, show 8 * (j + 1) = 8 * j + 8 by ring, pow_add]
        exact n2
      · rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring]
        convert n3 using 1
        simp only [S, rsChunk, show 8 * (j + 1) = 8 * j + 8 by ring, Finset.sum_range_add,
          Finset.mul_sum]
        refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i hi => ?_)
        have hi8 : i < 8 := Finset.mem_range.mp hi
        have hd : (8 * j + i) / 8 = j := by omega
        have hm : (8 * j + i) % 8 = i := by omega
        simp only [sOf, hd, hm, hj8, ↓reduceDIte, pow_add, mul_assoc]
  refine ⟨(List.range 64).map sOf, chs, by simp [kBits], by simpa [ringMapShifts] using hcl, ?_,
    hchs, ?_⟩
  · intro t ht
    simp only [List.length_map, List.length_range] at ht
    simp only [List.getElem_map, List.getElem_range]
    have h8 : t / 8 < 8 := by omega
    have hrd := hvs (t / 8) h8 (t % 8) (by rw [hvl]; omega)
    rw [← pow_mul, loadHolds_mul_gen_pow, show t / 8 * 8 + t % 8 = t by omega] at hrd
    simp only [sOf, h8, ↓reduceDIte]
    rw [List.getD_eq_getElem _ _ (by rw [hvl]; omega)]
    exact hrd
  · rw [← hret]
    simp only [List.cons.injEq, and_true]
    have h17 := (hchain 8 le_rfl).2
    rw [e7, e6, show (65536 : ℕ) = 2 ^ 16 from rfl, word_two_pow (by decide),
      loadHolds_mul_gen_pow] at l8
    rw [loadHolds_unique l8 h17, polyEval_eq_sum]
    simp only [S, List.length_map, List.length_range, Nat.reduceMul]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' : t < 64 := Finset.mem_range.mp ht
    rw [List.getD_eq_getElem _ _ (by simpa using ht')]
    simp only [List.getElem_map, List.getElem_range]
    ring

end
end LeanVM.Guest.B1.VerifySub
