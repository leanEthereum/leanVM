/-
  LeanVM.Guest.B1.VerifySub.Loops

  `verify_sub`'s two `mul_range` loops: the ring switch's target, and Flock's point copied into
  `z_vals`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Ring
public import LeanVM.Guest.B1.VerifySub.Run

/-!
# `__loop84`, `__loop85` (G:2192-2210)

* `__loop84(x, z_partial, map_challenges, rs_chain)`, for `x = g^0 .. g^63`: the slice
  `z_partial[x]` through the ring map (`phiMap`, V:2005), and the chain `rs_chain`'s row `x`
  (`g^i`, the running sum) advanced to row `x·g`. `loop84_step` is its body (soundness);
  `loop84_sound` its run from `g^0` to the end at `g^64`.
* `__loop85(x, g^τ, zv_lo, zr_hi)`, for `x = g^0 .. g^(τ-1)`: `zv_lo[x] = zr_hi[x]`.

`loop_sound` is `loop_iff`'s forward direction, from the body's soundness alone.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `loop_iff`'s forward direction, from the body's soundness. -/
theorem loop_sound {P : Core.Program} {rd : Reader} {f : String} {ps : List E} {N : E}
    {B : E → Prop}
    (hstep : ∀ d x, P.relN rd (d + 1) f (x :: ps) [] →
      B x ∧ (x * gen + N ≠ 0 → P.relN rd d f (x * gen :: ps) []))
    (k : ℕ) (h : P.Rel rd f (gen ^ k :: ps) []) :
    ∃ m, k < m ∧ N = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ N) ∧
      ∀ j, k ≤ j → j < m → B (gen ^ j) := by
  obtain ⟨d, hd⟩ := h
  induction d generalizing k with
  | zero => exact hd.elim
  | succ d ih =>
    obtain ⟨hB, hnext⟩ := hstep d _ hd
    by_cases h0 : gen ^ k * gen + N = 0
    · refine ⟨k + 1, by omega, (gen_pow_add_eq_zero_iff k).mp h0, fun j h1 h2 => by omega,
        fun j h1 h2 => ?_⟩
      rwa [show j = k by omega]
    · have := hnext h0
      rw [gen_pow_mul_gen] at this
      obtain ⟨m, hm, hN, hfirst, hall⟩ := ih (k + 1) this
      refine ⟨m, by omega, hN, fun j h1 h2 => ?_, fun j h1 h2 => ?_⟩
      · rcases Nat.lt_or_ge (k + 1) j with h | h
        · exact hfirst j h h2
        · rw [show j = k + 1 by omega]
          intro he
          exact h0 ((gen_pow_add_eq_zero_iff k).mpr he.symm)
      · rcases Nat.lt_or_ge k j with h | h
        · exact hall j (by omega) h2
        · rwa [show j = k by omega]

/-- A loop from `g^0` that ends at `g^n`, `n` below the order of `g`, runs its body at every
`g^j`, `j < n`. -/
theorem loop_to {P : Core.Program} {rd : Reader} {f : String} {ps : List E} {n : ℕ}
    {B : E → Prop}
    (hstep : ∀ d x, P.relN rd (d + 1) f (x :: ps) [] →
      B x ∧ (x * gen + gen ^ n ≠ 0 → P.relN rd d f (x * gen :: ps) []))
    (hn : n < ordG) (h : P.Rel rd f (gen ^ 0 :: ps) []) : ∀ j < n, B (gen ^ j) := by
  rcases Nat.eq_zero_or_pos n with rfl | hp
  · exact fun j hj => absurd hj (Nat.not_lt_zero j)
  have hn' : n < 2 ^ 64 - 1 := hn
  obtain ⟨m, hm, hN, hfirst, hall⟩ := loop_sound hstep 0 h
  have hmn : m = n := by
    rcases Nat.lt_trichotomy m n with hlt | heq | hgt
    · exact absurd (gen_pow_inj (by omega) (by omega) hN) (by omega)
    · exact heq
    · exact absurd rfl (hfirst n hp hgt)
  exact fun j hj => hall j (Nat.zero_le j) (by omega)

/-! ## `__loop84` -/

/-- A stage of the ring map at the slice value `w`: `d` squarings, the stage's challenge
`mc[st]`, `w + mc·w^(2^d)` at `w + d + 3`. -/
def l84Stage (w d st : ℕ) : List Stmt :=
  sqChain w d ++ [.atom (.load (.n (w + d + 1)) (.n 2) st),
    .atom (.mul (.n (w + d + 2)) (.n (w + d + 1)) (.n (w + d))),
    .atom (.add (.n (w + d + 3)) (.n w) (.n (w + d + 2)))]

/-- The expansion of `__loop84`. -/
def l84Body : List Stmt :=
  [.atom (.mul (.n 4) (.n 1) (.n 0)), .atom (.load (.n 5) (.n 4) 0)] ++ l84Stage 5 32 0 ++
    l84Stage 40 16 1 ++ l84Stage 59 8 2 ++ l84Stage 70 4 3 ++ l84Stage 77 2 4 ++ l84Stage 82 1 5 ++
    [.atom (.mul (.n 87) (.n 0) (.n 0)), .atom (.mul (.n 88) (.n 3) (.n 87)),
      .atom (.load (.n 89) (.n 88) 0), .atom (.const (.n 90) (word 2 0 0)),
      .atom (.mul (.n 91) (.n 89) (.n 90)), .atom (.load (.n 91) (.n 88) 2),
      .atom (.load (.n 92) (.n 88) 1), .atom (.mul (.n 93) (.n 89) (.n 86)),
      .atom (.add (.n 94) (.n 92) (.n 93)), .atom (.load (.n 94) (.n 88) 3),
      .atom (.const (.n 95) (word 2 0 0)), .atom (.mul (.n 96) (.n 0) (.n 95)),
      .atom (.const (.n 97) (word 27 0 0)), .atom (.add (.n 98) (.n 96) (.n 97)),
      .atom (.const (.n 99) (word 2 0 0)), .atom (.mul (.n 100) (.n 0) (.n 99)),
      .callIf (.n 98) "__loop84" [.n 100, .n 1, .n 2, .n 3], .ret []]

theorem core174_body : Fn.body Data.core174 = l84Body := stmtsEqb_sound (by decide +kernel)

theorem find_loop84 : coreProgram.find? "__loop84" = some Data.core174 :=
  Program.find?_of_indexOf? (j := 174) (by decide +kernel) rfl

theorem l84Stage_noRet (w d st : ℕ) : Stmt.noRetList (l84Stage w d st) = true := by
  rw [l84Stage, noRetList_append, sqChain_noRet]; rfl

theorem holds_l84Stage {C : CallRel} {rd : Reader} {σ : Val} {k : List E → Prop} (w d st : ℕ)
    (next : Prop) (h : Stmt.HoldsList C rd σ (l84Stage w d st) next k) :
    LoadHolds rd (σ (.n 2)) st (σ (.n (w + d + 1))) ∧
      σ (.n (w + d + 3)) = σ (.n w) + σ (.n (w + d + 1)) * σ (.n w) ^ 2 ^ d ∧ next := by
  rw [holdsList_noRet _ (l84Stage_noRet w d st)] at h
  obtain ⟨h, hn⟩ := h
  rw [l84Stage, holdsList_append, holdsList_noRet _ (sqChain_noRet _ _)] at h
  obtain ⟨hc, h⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h
  obtain ⟨l, hm, ha⟩ := h
  rw [ha, hm, holds_sqChain _ _ hc]
  exact ⟨l, rfl, hn⟩

/-- `__loop84`'s body at `x`: the slice `z_partial[x]` through the map of the challenges `cs` at
`map_challenges`, and `rs_chain`'s row `x` (the power `xp`, the sum `sm`) advanced. -/
def Loop84Body (rd : Reader) (zp mc rs x : E) : Prop :=
  ∃ (lin xp sm : E) (cs : List E), cs.length = 6 ∧ ReadsAt rd mc cs ∧ LoadHolds rd (zp * x) 0 lin ∧
    LoadHolds rd (rs * (x * x)) 0 xp ∧ LoadHolds rd (rs * (x * x)) 1 sm ∧
    LoadHolds rd (rs * (x * x)) 2 (xp * gen) ∧
    LoadHolds rd (rs * (x * x)) 3 (sm + xp * phiMap lin cs)

theorem word27 : word 27 0 0 = gen ^ 64 := by
  rw [word_eOfNat, show (27 : ℕ) = gSquaresBits.getD 6 0 from rfl, eOfNat_gSquaresBits 6 (by decide)]
  norm_num

theorem loop84_step (rd : Reader) (zp mc rs : E) (d : ℕ) (x : E) :
    coreProgram.relN rd (d + 1) "__loop84" (x :: [zp, mc, rs]) [] →
      Loop84Body rd zp mc rs x ∧
        (x * gen + gen ^ 64 ≠ 0 → coreProgram.relN rd d "__loop84" (x * gen :: [zp, mc, rs]) []) := by
  rw [relN_succ_iff find_loop84, show Fn.params Data.core174 = [.n 0, .n 1, .n 2, .n 3] from rfl,
    core174_body, l84Body]
  rintro ⟨σ, hp, h⟩
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hp
  simp only [holdsList_append] at h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨h4, l5, h⟩ := h
  obtain ⟨m0, s0, h⟩ := holds_l84Stage _ _ _ _ h
  obtain ⟨m1, s1, h⟩ := holds_l84Stage _ _ _ _ h
  obtain ⟨m2, s2, h⟩ := holds_l84Stage _ _ _ _ h
  obtain ⟨m3, s3, h⟩ := holds_l84Stage _ _ _ _ h
  obtain ⟨m4, s4, h⟩ := holds_l84Stage _ _ _ _ h
  obtain ⟨m5, s5, h⟩ := holds_l84Stage _ _ _ _ h
  simp only [List.map_cons, List.map_nil, word_gen, word27] at h
  obtain ⟨h87, h88, l89, h90, h91, l91, l92, h93, h94, l94, h95, h96, h97, h98, h99, h100,
    ⟨-, hcall, -⟩⟩ := h
  refine ⟨⟨σ (.n 5), σ (.n 89), σ (.n 92), [σ (.n 38), σ (.n 57), σ (.n 68), σ (.n 75), σ (.n 80),
    σ (.n 84)], rfl, ?_, by rw [← h4]; exact l5, by rw [← h87, ← h88]; exact l89,
    by rw [← h87, ← h88]; exact l92, by rw [← h87, ← h88, ← h90, ← h91]; exact l91, ?_⟩, ?_⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    match k, hk with
    | 0, _ => exact m0
    | 1, _ => exact m1
    | 2, _ => exact m2
    | 3, _ => exact m3
    | 4, _ => exact m4
    | 5, _ => exact m5
  · rw [← h87, ← h88]
    have hphi : σ (.n 86) = phiMap (σ (.n 5)) [σ (.n 38), σ (.n 57), σ (.n 68), σ (.n 75),
        σ (.n 80), σ (.n 84)] := by
      rw [s5, s4, s3, s2, s1, s0]
      rfl
    rw [← hphi, ← h93, ← h94]
    exact l94
  · intro hne
    have := hcall (by rw [h98, h96, h95, h97]; exact hne)
    rwa [h100, h99] at this

theorem polyEval_eq_sum (l : List E) (x : E) :
    polyEval l x = ((List.range l.length).map fun i ↦ l.getD i 0 * x ^ i).sum := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [polyEval, List.foldr_cons, ← polyEval, ih, List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Function.comp_def, List.getD_cons_zero,
      List.getD_cons_succ, pow_zero, mul_one, List.sum_cons, pow_succ]
    rw [add_comm, ← List.sum_map_mul_right]
    exact congrArg (c + ·) (congrArg List.sum (List.map_congr_left fun i _ => by ring))

theorem gen_pow_two_mul (j : ℕ) : gen ^ j * gen ^ j = gen ^ (2 * j) := by rw [← pow_add, two_mul]

variable {rd : Reader} {σ : Val}

/-- **The ring switch's target** (G:2190-2203): `__loop84` from `g^0` over `rs_chain`, whose row
`64` holds `Σ_i g^i Φ(s_i)` (`ringTarget`, V:2031). -/
theorem vs_transposed (h : VsHolds rd σ) {zs cs : List E} (hzl : zs.length = 64)
    (hz : ReadsAt rd (σ (.n 723)) zs) (hcl : cs.length = 6) (hc : ReadsAt rd (σ (.n 732)) cs) :
    σ (.n 1150) = ringTarget zs cs := by
  have hi := h.slice 1305 [.atom (.const (.n 1145) (word 1 0 0)), .atom (.load (.n 1145) (.n 1144) 0),
    .atom (.const (.n 1146) (word 0 0 0)), .atom (.load (.n 1146) (.n 1144) 1),
    .atom (.const (.n 1147) (word 1 0 0))] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one, word_zero] at hi
  obtain ⟨e1145, i0, e1146, i1, e1147⟩ := hi
  rw [e1145] at i0
  rw [e1146] at i1
  have hcall := h.call 1310 "__loop84" [.n 1147, .n 723, .n 732, .n 1144] [] (by decide +kernel)
  simp only [List.map_cons, List.map_nil, e1147] at hcall
  rw [← pow_zero gen] at hcall
  have hb := loop_to (fun d x => loop84_step rd _ _ _ d x) (by decide) hcall
  -- the slices and the challenges, through every body
  have hrow : ∀ j ≤ 64, LoadHolds rd (σ (.n 1144)) (2 * j) (gen ^ j) ∧
      LoadHolds rd (σ (.n 1144)) (2 * j + 1)
        ((List.range j).map fun i ↦ phiMap (zs.getD i 0) cs * gen ^ i).sum := by
    intro j hj
    induction j with
    | zero => exact ⟨by simpa using i0, by simpa using i1⟩
    | succ j ih =>
      obtain ⟨ih0, ih1⟩ := ih (by omega)
      obtain ⟨lin, xp, sm, cs', hcs', hc', hlin, l0, l1, l2, l3⟩ := hb j (by omega)
      rw [gen_pow_two_mul, loadHolds_mul_gen_pow, Nat.add_zero] at l0
      rw [gen_pow_two_mul, loadHolds_mul_gen_pow] at l1 l2 l3
      have hxp := loadHolds_unique l0 ih0
      have hsm := loadHolds_unique l1 ih1
      have hcs : cs' = cs := List.ext_getElem (by rw [hcs', hcl]) fun k h1 h2 =>
        loadHolds_unique (hc' k h1) (hc k h2)
      have hlz : lin = zs.getD j 0 := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        rw [loadHolds_mul_gen_pow, Nat.add_zero] at hlin
        exact loadHolds_unique hlin (hz j (by omega))
      rw [hxp] at l2 l3
      rw [hsm, hcs, hlz] at l3
      refine ⟨by rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_succ]; exact l2, ?_⟩
      rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring, List.range_succ, List.map_append,
        List.sum_append]
      simpa [mul_comm] using l3
  have ht := h.slice 1311 [.atom (.const (.n 1148) (word 325 0 0)),
    .atom (.mul (.n 1149) (.n 1144) (.n 1148)), .atom (.load (.n 1150) (.n 1149) 1)]
    (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at ht
  obtain ⟨e1148, e1149, l1150⟩ := ht
  have w325 : word 325 0 0 = gen ^ 128 := by
    rw [word_eOfNat, show (325 : ℕ) = gSquaresBits.getD 7 0 from rfl,
      eOfNat_gSquaresBits 7 (by decide)]
    norm_num
  rw [e1149, e1148, w325, loadHolds_mul_gen_pow] at l1150
  rw [loadHolds_unique l1150 (hrow 64 le_rfl).2, ringTarget, polyEval_eq_sum, List.length_map, hzl]
  refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
  have hi' : i < 64 := by simpa using hi
  rw [List.getD_eq_getElem _ _ (by simpa [hzl] using hi'),
    List.getD_eq_getElem _ _ (by simpa [hzl] using hi'), List.getElem_map]

/-! ## `__loop85` and `z_vals` -/

theorem find_loop85 : coreProgram.find? "__loop85" = some Data.core175 :=
  Program.find?_of_indexOf? (j := 175) (by decide +kernel) rfl

theorem loop85_step (rd : Reader) (N zv zr : E) (d : ℕ) (x : E) :
    coreProgram.relN rd (d + 1) "__loop85" (x :: [N, zv, zr]) [] →
      (∃ v, LoadHolds rd (zr * x) 0 v ∧ LoadHolds rd (zv * x) 0 v) ∧
        (x * gen + N ≠ 0 → coreProgram.relN rd d "__loop85" (x * gen :: [N, zv, zr]) []) := by
  rw [relN_succ_iff find_loop85, show Fn.params Data.core175 = [.n 0, .n 1, .n 2, .n 3] from rfl,
    show Fn.body Data.core175 = Data.core175.body from rfl, Data.core175.body]
  rintro ⟨σ, hp, h⟩
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hp
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen] at h
  obtain ⟨h4, l5, h6, l6, h7, h8, h9, h10, h11, ⟨-, hcall, -⟩⟩ := h
  refine ⟨⟨σ (.n 5), by rw [← h4]; exact l5, by rw [← h6]; exact l6⟩, fun hne => ?_⟩
  have := hcall (by rw [h9, h8, h7]; exact hne)
  rwa [h11, h10] at this

/-- **`z_vals`** (G:2204-2210): Flock's point, the lincheck's challenges reversed then the
zerocheck's beyond its first eight. -/
theorem vs_zvals (h : VsHolds rd σ) {τ : ℕ} (hτ : τ < 29) (htau : σ (.n 718) = gen ^ τ)
    {chi rcs : List E} (hcl : chi.length = 8 + τ) (hrl : rcs.length = 8)
    (hchi : ReadsAt rd (σ (.n 721)) chi) (hrcs : ReadsAt rd (σ (.n 722)) rcs) :
    ReadsAt rd (σ (.n 734)) (rcs.reverse ++ chi.drop 8) := by
  have hcp := fun t (ht : t < 8) => h.slice (1314 + 2 * t)
    [.atom (.load (.n (1151 + t)) (.n 722) (7 - t)), .atom (.load (.n (1151 + t)) (.n 734) t)]
    (by revert t ht; decide +kernel)
  have hg := h.slice 1330 [.atom (.const (.n 1159) (word 1 0 0)),
    .atom (.add (.n 1160) (.n 1159) (.n 718)), .atom (.const (.n 1161) (word 1 0 0)),
    .atom (.const (.n 1162) (word 256 0 0)), .atom (.mul (.n 1163) (.n 734) (.n 1162)),
    .atom (.const (.n 1164) (word 256 0 0)), .atom (.mul (.n 1165) (.n 721) (.n 1164)),
    .callIf (.n 1160) "__loop85" [.n 1161, .n 718, .n 1163, .n 1165]] (by decide +kernel)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true, word_one, List.map_cons,
    List.map_nil] at hg
  obtain ⟨e1159, e1160, e1161, e1162, e1163, e1164, e1165, -, hcall⟩ := hg
  have w8 : word 256 0 0 = gen ^ 8 := word_two_pow (a := 8) (by decide)
  have hloop : ∀ j < τ, ∃ v, LoadHolds rd (σ (.n 721)) (8 + j) v ∧ LoadHolds rd (σ (.n 734)) (8 + j) v := by
    rcases Nat.eq_zero_or_pos τ with rfl | hp
    · exact fun j hj => absurd hj (Nat.not_lt_zero j)
    have hne : σ (.n 1160) ≠ 0 := by
      rw [e1160, e1159, htau]
      intro he
      have := gen_pow_inj (a := 0) (b := τ) (by decide) (by omega)
        (by rw [pow_zero]; exact (e_add_eq_zero_iff.mp he))
      omega
    have hc := hcall hne
    rw [e1161, e1163, e1165, e1162, e1164, w8, htau, ← pow_zero gen] at hc
    have hb := loop_to (fun d x => loop85_step rd _ _ _ d x) (by unfold ordG; omega) hc
    intro j hj
    obtain ⟨v, l1, l2⟩ := hb j hj
    rw [mul_assoc, ← pow_add, loadHolds_mul_gen_pow, Nat.add_zero] at l1 l2
    exact ⟨v, l1, l2⟩
  intro k hk
  simp only [List.length_append, List.length_reverse, List.length_drop, hrl, hcl] at hk
  rcases Nat.lt_or_ge k 8 with hk8 | hk8
  · rw [List.getElem_append_left (by simp [hrl]; omega), List.getElem_reverse]
    have := hcp k hk8
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
    have e1 := loadHolds_unique this.1 (hrcs (7 - k) (by omega))
    have e2 : rcs[rcs.length - 1 - k] = rcs[7 - k] := by simp only [hrl]
    rw [e2, ← e1]
    exact this.2
  · rw [List.getElem_append_right (by simp [hrl]; omega), List.getElem_drop]
    obtain ⟨v, l1, l2⟩ := hloop (k - 8) (by omega)
    rw [show 8 + (k - 8) = k by omega] at l1 l2
    simp only [List.length_reverse, hrl, show 8 + (k - 8) = k by omega]
    rw [← loadHolds_unique l1 (hchi k (by omega))]
    exact l2

end
end LeanVM.Guest.B1.VerifySub
