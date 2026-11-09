/-
  LeanVM.Guest.B1.Gkr.Holds

  `verify_bus_gkr` (TRIAGE G #43) computes the specification's bus GKR walk: `verify_bus_gkr_holds`.
-/

module

public import LeanVM.Guest.B1.Gkr.Walk
public import LeanVM.Guest.B1.Gkr.Loop8
public import LeanVM.Guest.B1.Gkr.RoundsHolds
public import LeanVM.Guest.B1.Placement.Common

/-!
# `verify_bus_gkr` is sound (G:1768-1940)

The body (`vbgPre`, checked against the core IR by kernel evaluation): the range check of
`g_bus_mu = g^depth` (`depth ≤ 32`), the two roots read and the count asserted nonzero, the root
slot, the tables `pairs[d] = g^(d/2)` and `depth_shift[d] = g^(d % 2)`, the binary layer at an
odd depth (`od_step`), the layer loop `__loop6` (`ly_step`, `ly_chain`), the final slot, the
point's copy to `zeta` (`__loop7`), and the return.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `verify_bus_gkr`'s statements before its `ret`. -/
def vbgPre : List Stmt :=
  [.atom (.const (.n 8) (word 4 0 0)), .atom (.mul (.n 9) (.n 6) (.n 8)),
    .atom (.mul (.n 10) (.n 9) (.n 9)), .atom (.mul (.n 11) (.n 10) (.n 10)),
    .atom (.mul (.n 12) (.n 11) (.n 11)), .atom (.mul (.n 13) (.n 12) (.n 12)),
    .atom (.mul (.n 14) (.n 13) (.n 9)), .atom (.hint (.allocDyn (.n 15) (.n 14))),
    .atom (.hint (.alloc (.n 16) 6034)), .atom (.hint (.alloc (.n 17) 1640)),
    .atom (.const (.n 18) (word 4294967296 0 0)),
    .atom (.rangeCheck (.n 6) (.n 19) (.n 20) (.n 21) (.n 18)),
    .atom (.copy (.n 22) (.n 0)), .atom (.copy (.n 23) (.n 1)), .atom (.copy (.n 24) (.n 2)),
    .atom (.copy (.n 25) (.n 3)), .atom (.copy (.n 26) (.n 4))] ++
  fsNextT (.n 5) 0 27 ++ fsNextT (.n 5) 1 37 ++
  [.atom (.const (.n 47) (word 0 0 0)), .atom (.add (.n 48) (.n 37) (.n 47)),
    .atom (.hint (.inverse (.n 48) (.n 49))), .atom (.assertNe (.n 48) (.n 49) (.n 50)),
    .atom (.load (.n 22) (.n 15) 0), .atom (.load (.n 23) (.n 15) 1),
    .atom (.load (.n 24) (.n 15) 2), .atom (.load (.n 25) (.n 15) 3),
    .atom (.load (.n 26) (.n 15) 4), .atom (.load (.n 34) (.n 15) 13),
    .atom (.load (.n 36) (.n 15) 14), .atom (.load (.n 44) (.n 15) 15),
    .atom (.load (.n 46) (.n 15) 16), .atom (.const (.n 51) (word 4 0 0)),
    .atom (.mul (.n 52) (.n 5) (.n 51)), .atom (.load (.n 52) (.n 15) 5),
    .atom (.load (.n 27) (.n 15) 6), .atom (.load (.n 27) (.n 15) 7),
    .atom (.load (.n 37) (.n 15) 8), .atom (.load (.n 17) (.n 15) 9),
    .atom (.const (.n 53) (word 1 0 0)), .atom (.load (.n 53) (.n 15) 10),
    .atom (.const (.n 54) (word 1 0 0)), .atom (.load (.n 54) (.n 15) 11),
    .atom (.const (.n 55) (word 1 0 0)), .atom (.load (.n 55) (.n 15) 12),
    .atom (.hint (.alloc (.n 56) 8))] ++
  ((List.range 4).map fun r ↦
    [.atom (.const (.n (57 + 2 * r)) (word (2 ^ ((r + 1) % 4)) 0 0)),
      .atom (.load (.n (57 + 2 * r)) (.n 56) r),
      .atom (.const (.n (58 + 2 * r)) (word (2 ^ ((r + 1) / 4)) 0 0)),
      .atom (.load (.n (58 + 2 * r)) (.n 56) (4 + r))]).flatten ++
  [
    .atom (.hint (.alloc (.n 65) 33)), .atom (.hint (.alloc (.n 66) 33))] ++
  ((List.range 33).map fun k ↦
    [.atom (.const (.n (67 + 2 * k)) (word (2 ^ (k / 2)) 0 0)),
      .atom (.load (.n (67 + 2 * k)) (.n 65) k),
      .atom (.const (.n (68 + 2 * k)) (word (2 ^ (k % 2)) 0 0)),
      .atom (.load (.n (68 + 2 * k)) (.n 66) k)]).flatten ++
  [.atom (.mul (.n 133) (.n 66) (.n 6)), .atom (.load (.n 134) (.n 133) 0),
    .atom (.const (.n 135) (word 1 0 0)), .atom (.add (.n 136) (.n 134) (.n 135)),
    .ite (.n 136) [] odBody,
    .atom (.const (.n 309) (word 1 0 0)), .atom (.mul (.n 310) (.n 65) (.n 6)),
    .atom (.load (.n 311) (.n 310) 0), .atom (.add (.n 312) (.n 309) (.n 311)),
    .atom (.const (.n 313) (word 1 0 0)), .atom (.mul (.n 314) (.n 65) (.n 6)),
    .atom (.load (.n 315) (.n 314) 0),
    .callIf (.n 312) "__loop6" [.n 313, .n 315, .n 66, .n 6, .n 15, .n 16, .n 56],
    .atom (.mul (.n 316) (.n 6) (.n 6)), .atom (.mul (.n 317) (.n 316) (.n 316)),
    .atom (.mul (.n 318) (.n 317) (.n 317)), .atom (.mul (.n 319) (.n 318) (.n 318)),
    .atom (.mul (.n 320) (.n 319) (.n 6)), .atom (.mul (.n 321) (.n 15) (.n 320)),
    .atom (.load (.n 322) (.n 321) 5), .atom (.load (.n 323) (.n 321) 9),
    .atom (.const (.n 324) (word 1 0 0)), .atom (.add (.n 325) (.n 324) (.n 6)),
    .atom (.const (.n 326) (word 1 0 0)),
    .callIf (.n 325) "__loop7" [.n 326, .n 6, .n 7, .n 323],
    .atom (.load (.n 327) (.n 321) 0), .atom (.load (.n 328) (.n 321) 1),
    .atom (.load (.n 329) (.n 321) 2), .atom (.load (.n 330) (.n 321) 3),
    .atom (.load (.n 331) (.n 321) 4), .atom (.copy (.n 332) (.n 322)),
    .atom (.load (.n 333) (.n 321) 6), .atom (.load (.n 334) (.n 321) 7),
    .atom (.load (.n 335) (.n 321) 8)]

/-- `verify_bus_gkr`'s returned values. -/
def vbgRets : List V := (List.range 9).map fun k ↦ .n (327 + k)

noncomputable def vbgCheck : Bool :=
  match coreProgram.find? "verify_bus_gkr" with
  | some fn => decide (fn.params = (List.range 8).map V.n) &&
      tbStmtsEqb fn.body (vbgPre ++ [.ret vbgRets])
  | none => false

theorem vbgCheck_eq : vbgCheck = true := by decide +kernel

theorem vbgFound : ∃ fn : Fn, coreProgram.find? "verify_bus_gkr" = some fn ∧
    fn.params = (List.range 8).map V.n ∧ fn.body = vbgPre ++ [.ret vbgRets] := by
  have h := vbgCheck_eq
  unfold vbgCheck at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

theorem vbgPre_noRet : Stmt.noRetList vbgPre = true := by decide +kernel

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **The root slot**: the two roots read at the cursor, the count nonzero, and the slot of
`L = 0` with the carried capacity, the two roots waiting, the values `[root, root, count]`. -/
theorem vbg_root (h : Stmt.HoldsList C rd σ vbgPre True kret) :
    LoadHolds rd (σ (.n 5)) 0 (σ (.n 27)) ∧ LoadHolds rd (σ (.n 5)) 1 (σ (.n 37)) ∧
      σ (.n 37) ≠ 0 ∧
      GkSlot rd (σ (.n 15)) 0 ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)],
        [(σ (.n 27), dsObserve), (σ (.n 37), dsObserve)]⟩ (σ (.n 5) * gen ^ 2)
        ⟨[σ (.n 27), σ (.n 27), σ (.n 37)], []⟩ (σ (.n 17)) 1 1 1 := by
  have hnr := vbgPre_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have r0 := tb_holds_slice hnr h 17 (fsNextT (.n 5) 0 27) (by decide +kernel)
  have r1 := tb_holds_slice hnr h 26 (fsNextT (.n 5) 1 37) (by decide +kernel)
  rw [holds_fsNextT] at r0 r1
  obtain ⟨⟨l27, p27⟩, -⟩ := r0
  obtain ⟨⟨l37, p37⟩, -⟩ := r1
  have cp : ∀ k < 5, σ (.n (22 + k)) = σ (.n k) := by
    intro k hk
    have := tb_holds_slice hnr h 12 ((List.range 5).map fun k ↦
      Stmt.atom (.copy (.n (22 + k)) (.n k))) (by decide +kernel)
    rw [tb_holdsList_mapAtoms] at this
    exact this k hk
  have lc : ∀ k < 5, LoadHolds rd (σ (.n 15)) k (σ (.n (22 + k))) := by
    intro k hk
    have := tb_holds_slice hnr h 39 ((List.range 5).map fun k ↦
      Stmt.atom (.load (.n (22 + k)) (.n 15) k)) (by decide +kernel)
    rw [tb_holdsList_mapAtoms] at this
    exact this k hk
  have c47 := a 35 (.const (.n 47) (word 0 0 0)) (by decide +kernel)
  have a48 := a 36 (.add (.n 48) (.n 37) (.n 47)) (by decide +kernel)
  have n48 := a 38 (.assertNe (.n 48) (.n 49) (.n 50)) (by decide +kernel)
  have l34 := a 44 (.load (.n 34) (.n 15) 13) (by decide +kernel)
  have l36 := a 45 (.load (.n 36) (.n 15) 14) (by decide +kernel)
  have l44 := a 46 (.load (.n 44) (.n 15) 15) (by decide +kernel)
  have l46 := a 47 (.load (.n 46) (.n 15) 16) (by decide +kernel)
  have c51 := a 48 (.const (.n 51) (word 4 0 0)) (by decide +kernel)
  have m52 := a 49 (.mul (.n 52) (.n 5) (.n 51)) (by decide +kernel)
  have l52 := a 50 (.load (.n 52) (.n 15) 5) (by decide +kernel)
  have v0 := a 51 (.load (.n 27) (.n 15) 6) (by decide +kernel)
  have v1 := a 52 (.load (.n 27) (.n 15) 7) (by decide +kernel)
  have v2 := a 53 (.load (.n 37) (.n 15) 8) (by decide +kernel)
  have l17 := a 54 (.load (.n 17) (.n 15) 9) (by decide +kernel)
  have c53 := a 55 (.const (.n 53) (word 1 0 0)) (by decide +kernel)
  have l53 := a 56 (.load (.n 53) (.n 15) 10) (by decide +kernel)
  have c54 := a 57 (.const (.n 54) (word 1 0 0)) (by decide +kernel)
  have l54 := a 58 (.load (.n 54) (.n 15) 11) (by decide +kernel)
  have c55 := a 59 (.const (.n 55) (word 1 0 0)) (by decide +kernel)
  have l55 := a 60 (.load (.n 55) (.n 15) 12) (by decide +kernel)
  simp only [Atom.Holds] at c47 a48 n48 l34 l36 l44 l46 c51 m52 l52 v0 v1 v2 l17 c53 l53 c54 l54
  simp only [Atom.Holds] at c55 l55
  rw [tb_word_zero] at c47
  rw [tb_word_one] at c55
  rw [tb_word_one] at c53 c54
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, tb_word_two_pow (by norm_num)] at c51
  refine ⟨l27, l37, fun h0 => ?_, rfl, fun j hj => ?_, by simp, fun c hc hcan j hj => ?_, ?_,
    rfl, fun t ht => ?_, l17, rfl, tbReadsAt_nil _ _, ?_, ?_, ?_⟩
  · obtain ⟨e50, e1⟩ := n48
    rw [a48, c47, h0, zero_add, zero_mul] at e50
    exact zero_ne_one (e50.symm.trans e1)
  · rw [show 17 * 0 + j = j by ring]
    have := lc j hj
    rw [cp j hj] at this
    interval_cases j <;> exact this
  · have hc' : ∀ j < 4, LoadHolds rd (σ (.n 15)) (13 + j) (c j) := fun j hj => by
      have := hc j hj; rwa [show 17 * 0 + 13 + j = 13 + j by ring] at this
    have e0 := tb_loadHolds_unique (hc' 0 (by omega)) l34
    have e1 := tb_loadHolds_unique (hc' 1 (by omega)) l36
    have e2 := tb_loadHolds_unique (hc' 2 (by omega)) l44
    have e3 := tb_loadHolds_unique (hc' 3 (by omega)) l46
    have k27 := tb_pack_cells p27 (by rw [show 27 + 7 = 34 from rfl, ← e0]; exact hcan 0 (by omega))
    have k37 := tb_pack_cells p37 (by rw [show 37 + 7 = 44 from rfl, ← e2]; exact hcan 2 (by omega))
    rw [rateOf_eq_cells _ (by simp)]
    interval_cases j
    · rw [e0]; exact k27.1
    · rw [e1]; exact k27.2
    · rw [e2]; exact k37.1
    · rw [e3]; exact k37.2
  · rw [m52, c51] at l52
    exact l52
  · rw [show 17 * 0 + 6 + t = 6 + t by ring]
    interval_cases t
    · exact v0
    · exact v1
    · exact v2
  · rw [c53] at l53; exact l53
  · rw [c54] at l54; exact l54
  · rw [c55] at l55; exact l55

/-- **The tables** at `g_bus_mu = g^depth`: `depth_shift[depth] = g^(depth % 2)` and
`pairs[depth] = g^(depth / 2)`. -/
theorem vbg_tables (h : Stmt.HoldsList C rd σ vbgPre True kret) {depth : ℕ}
    (hg : σ (.n 6) = gen ^ depth) (hd : depth < 33) :
    LoadHolds rd (σ (.n 66) * σ (.n 6)) 0 (gen ^ (depth % 2)) ∧
      σ (.n 134) = gen ^ (depth % 2) ∧ σ (.n 311) = gen ^ (depth / 2) ∧
      σ (.n 315) = gen ^ (depth / 2) := by
  have hnr := vbgPre_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have ht := tb_holds_slice hnr h 80 (((List.range 33).map fun k ↦
    [Stmt.atom (.const (.n (67 + 2 * k)) (word (2 ^ (k / 2)) 0 0)),
      .atom (.load (.n (67 + 2 * k)) (.n 65) k),
      .atom (.const (.n (68 + 2 * k)) (word (2 ^ (k % 2)) 0 0)),
      .atom (.load (.n (68 + 2 * k)) (.n 66) k)]).flatten) (by decide +kernel)
  rw [tb_holdsList_flatten_range _ _ (fun _ => rfl)] at ht
  have hk := ht depth hd
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hk
  obtain ⟨c0, l0, c1, l1⟩ := hk
  rw [c0, tb_word_two_pow (by omega)] at l0
  rw [c1, tb_word_two_pow (by omega)] at l1
  have m124 := a 212 (.mul (.n 133) (.n 66) (.n 6)) (by decide +kernel)
  have l125 := a 213 (.load (.n 134) (.n 133) 0) (by decide +kernel)
  have m301 := a 218 (.mul (.n 310) (.n 65) (.n 6)) (by decide +kernel)
  have l302 := a 219 (.load (.n 311) (.n 310) 0) (by decide +kernel)
  have m305 := a 222 (.mul (.n 314) (.n 65) (.n 6)) (by decide +kernel)
  have l306 := a 223 (.load (.n 315) (.n 314) 0) (by decide +kernel)
  simp only [Atom.Holds] at m124 l125 m301 l302 m305 l306
  have hsh : LoadHolds rd (σ (.n 66) * σ (.n 6)) 0 (gen ^ (depth % 2)) := by
    rw [hg, tb_loadHolds_mul_gen_pow]; exact l1
  rw [m124] at l125
  rw [m301, hg, tb_loadHolds_mul_gen_pow, Nat.add_zero] at l302
  rw [m305, hg, tb_loadHolds_mul_gen_pow, Nat.add_zero] at l306
  exact ⟨hsh, tb_loadHolds_unique l125 hsh, tb_loadHolds_unique l302 l0,
    tb_loadHolds_unique l306 l0⟩

end Sem

/-- **The table `k_mod_next`** (G:1802-1805) at `σ 56`. -/
theorem vbg_kmn {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ vbgPre True kret) : KModNext rd (σ (.n 56)) := by
  have hs := tb_holds_slice vbgPre_noRet h 62 ((List.range 4).map fun r ↦
    [Stmt.atom (.const (.n (57 + 2 * r)) (word (2 ^ ((r + 1) % 4)) 0 0)),
      .atom (.load (.n (57 + 2 * r)) (.n 56) r),
      .atom (.const (.n (58 + 2 * r)) (word (2 ^ ((r + 1) / 4)) 0 0)),
      .atom (.load (.n (58 + 2 * r)) (.n 56) (4 + r))]).flatten (by decide +kernel)
  rw [tb_holdsList_flatten_range _ _ (fun _ => rfl)] at hs
  intro r hr
  have := hs r hr
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
  obtain ⟨c0, l0, c1, l1⟩ := this
  rw [c0, tb_word_two_pow (by omega)] at l0
  rw [c1, tb_word_two_pow (by omega)] at l1
  exact ⟨l1, l0⟩

/-- **The walk**: from the root slot, the binary layer at an odd depth and the layer loop run
`gkrLayers depth` to the slot of `L = depth`, nothing waiting. -/
theorem vbg_walk {rd : Reader} {σ : Val} {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbgPre True kret) {depth : ℕ}
    (hg : σ (.n 6) = gen ^ depth) (hd : depth < 33) (hd0 : depth ≠ 0) {s0 : Fs} {c0 : E}
    {st0 : GkrState} {row0 pos0 : E}
    (hslot0 : GkSlot rd (σ (.n 15)) 0 s0 c0 st0 row0 pos0 1 1) :
    ∃ (xs : List E) (st : GkrState) (s : Fs) (row pos half par : E),
      RunsTo (gkrLayers depth st0) s0 xs st s ∧ TbReadsAt rd c0 xs ∧ s.pend = [] ∧
      GkSlot rd (σ (.n 15)) depth s (c0 * gen ^ xs.length) st row pos half par := by
  have hnr := vbgPre_noRet
  have a := fun n a heq => tb_holds_atom hnr h n a heq
  obtain ⟨hsh, e125, e302, e306⟩ := vbg_tables h hg hd
  -- the layer loop's iterations
  have c300 := a 217 (.const (.n 309) (word 1 0 0)) (by decide +kernel)
  have a303 := a 220 (.add (.n 312) (.n 309) (.n 311)) (by decide +kernel)
  have c304 := a 221 (.const (.n 313) (word 1 0 0)) (by decide +kernel)
  simp only [Atom.Holds, tb_word_one] at c300 a303 c304
  obtain ⟨-, h7⟩ := tb_holds_callIf hnr h 224 (.n 312) "__loop6"
    [.n 313, .n 315, .n 66, .n 6, .n 15, .n 16, .n 56] (by decide +kernel)
  have hk := vbg_kmn h
  have hB : ∀ j < depth / 2, LyB rd (σ (.n 66)) (σ (.n 6)) (σ (.n 15)) (σ (.n 56)) (gen ^ j) := by
    intro j hj
    have hne7 : σ (.n 312) ≠ 0 := by
      rw [a303, c300, e302]
      intro h0
      have := gen_pow_inj (by omega) (by omega)
        ((e_add_eq_zero_iff.mp h0).symm.trans (pow_zero gen).symm)
      omega
    have hrel7 := h7 hne7
    simp only [List.map_cons, List.map_nil, c304] at hrel7
    rw [← pow_zero gen] at hrel7
    obtain ⟨m', -, hN, hall⟩ := tb_loop_sound
      (B := LyB rd (σ (.n 66)) (σ (.n 6)) (σ (.n 15)) (σ (.n 56)))
      (fun d x hx => ly_step tb_gkr_rounds_holds d x hx) 0 hrel7
    have hm : depth / 2 ≤ m' := by
      by_contra hc
      have := gen_pow_inj (by omega) (by omega) (e306.symm.trans hN)
      omega
    exact hall j (by omega) (by omega)
  rcases Nat.mod_two_eq_zero_or_one depth with h2 | h2
  · -- an even depth: the layers from the root slot
    rw [h2] at hsh
    obtain ⟨xs, st, s, pos, hrun, hrd, hp, hsl⟩ := ly_chain hk hsh (by omega) (by omega) hB hslot0
      (depth / 2) le_rfl
    have hrun' : RunsTo (gkrLayers depth st0) s0 xs st s := by
      rw [show depth = 2 * (depth / 2) by omega, gkrLayers_even]
      exact hrun
    rw [show 2 * (depth / 2) + 0 = depth by omega] at hsl
    exact ⟨xs, st, s, _, _, _, _, hrun', hrd, hp (Or.inr (by omega)), hsl⟩
  · -- an odd depth: the binary layer, then the layers
    rw [h2] at hsh e125
    have hi := tb_holds_slice hnr h 216 [.ite (.n 136) [] odBody] (by decide +kernel)
    simp only [Stmt.HoldsList] at hi
    rw [tb_holds_ite_noRet _ _ _ rfl odBody_noRet] at hi
    obtain ⟨⟨-, -, hodd⟩, -⟩ := hi
    have c126 := a 214 (.const (.n 135) (word 1 0 0)) (by decide +kernel)
    have a127 := a 215 (.add (.n 136) (.n 134) (.n 135)) (by decide +kernel)
    simp only [Atom.Holds, tb_word_one] at c126 a127
    have hne : σ (.n 136) ≠ 0 := by
      rw [a127, c126, e125]
      intro h0
      have := gen_pow_inj (by omega) (by omega)
        ((e_add_eq_zero_iff.mp h0).trans (pow_zero gen).symm)
      omega
    obtain ⟨xs1, st1, s1, hrun1, hrd1, hp1, hsl1⟩ := od_step (hodd hne) hslot0
    obtain ⟨xs, st, s, pos, hrun, hrd, hp, hsl⟩ := ly_chain hk hsh (by omega) (by omega) hB
      (by simpa using hsl1) (depth / 2) le_rfl
    have hrun' : RunsTo (gkrLayers depth st0) s0 (xs1 ++ xs) st s := by
      rw [show depth = 2 * (depth / 2) + 1 by omega, gkrLayers_odd]
      exact hrun1.bind hrun
    have hrd' : TbReadsAt rd c0 (xs1 ++ xs) := by
      rw [tbReadsAt_append]
      exact ⟨hrd1, hrd⟩
    rw [show 2 * (depth / 2) + 1 = depth by omega] at hsl
    rw [mul_assoc c0, ← pow_add, ← List.length_append] at hsl
    exact ⟨xs1 ++ xs, st, s, _, _, _, _, hrun', hrd', hp (Or.inl hp1), hsl⟩


/-- **`verify_bus_gkr` is sound** (TRIAGE G #43): on any memory of at most `2^32` words, at a depth
other than `0`, it runs the specification's GKR walk and count check (`gkrPhase`) on the words it
reads, writes the point to `zeta` and returns the sponge's capacity, the cursor past the words
and the three values. -/
theorem verify_bus_gkr_holds {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) :
    verify_bus_gkr_Spec Lm.read := by
  intro args rets hne hrel
  obtain ⟨fn, hf, hp, hb⟩ := vbgFound
  obtain ⟨σ, hpar, h, hret⟩ := (tb_rel_pre hf hb vbgPre_noRet args rets).mp hrel
  rw [hp] at hpar
  have hargs : args = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6),
      σ (.n 7)] := by rw [← hpar]; rfl
  have hrets : rets = [σ (.n 327), σ (.n 328), σ (.n 329), σ (.n 330), σ (.n 331), σ (.n 332),
      σ (.n 333), σ (.n 334), σ (.n 335)] := by rw [← hret]; rfl
  subst hargs hrets
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hne
  have hnr := vbgPre_noRet
  have a := fun n a heq => tb_holds_atom hnr h n a heq
  -- the depth
  have c18 := a 10 (.const (.n 18) (word 4294967296 0 0)) (by decide +kernel)
  have rc := a 11 (.rangeCheck (.n 6) (.n 19) (.n 20) (.n 21) (.n 18)) (by decide +kernel)
  simp only [Atom.Holds] at c18 rc
  obtain ⟨depth, hd, hg⟩ := tb_rc_sound' hμ Lm (K := 33) (by omega) (by norm_num)
    (by rw [c18, show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num),
      gen_pow_eq_ofK]) rc.1 rc.2.1 rc.2.2
  have hd0 : depth ≠ 0 := by rintro rfl; exact hne (by rw [hg, pow_zero])
  -- the root slot and the walk
  obtain ⟨l27, l37, hcnt, hslot0⟩ := vbg_root h
  obtain ⟨xs, st, s, row, pos, half, par, hrun, hrd, hpe, hsl⟩ := vbg_walk h hg hd hd0 hslot0
  obtain ⟨hcl, hcap, -, -, hcur, hvl, hval, hrow, hpl, hpt, -, -, -⟩ := hsl
  -- the final slot
  have m307 := a 225 (.mul (.n 316) (.n 6) (.n 6)) (by decide +kernel)
  have m308 := a 226 (.mul (.n 317) (.n 316) (.n 316)) (by decide +kernel)
  have m309 := a 227 (.mul (.n 318) (.n 317) (.n 317)) (by decide +kernel)
  have m310 := a 228 (.mul (.n 319) (.n 318) (.n 318)) (by decide +kernel)
  have m311 := a 229 (.mul (.n 320) (.n 319) (.n 6)) (by decide +kernel)
  have m312 := a 230 (.mul (.n 321) (.n 15) (.n 320)) (by decide +kernel)
  have l313 := a 231 (.load (.n 322) (.n 321) 5) (by decide +kernel)
  have l314 := a 232 (.load (.n 323) (.n 321) 9) (by decide +kernel)
  have c315 := a 233 (.const (.n 324) (word 1 0 0)) (by decide +kernel)
  have a316 := a 234 (.add (.n 325) (.n 324) (.n 6)) (by decide +kernel)
  have c317 := a 235 (.const (.n 326) (word 1 0 0)) (by decide +kernel)
  have q323 := a 242 (.copy (.n 332) (.n 322)) (by decide +kernel)
  simp only [Atom.Holds] at m307 m308 m309 m310 m311 m312 l313 l314 c315 a316 c317 q323
  rw [tb_word_one] at c315 c317
  have e312 : σ (.n 321) = σ (.n 15) * gen ^ (17 * depth) := by
    rw [m312, m311, m310, m309, m308, m307, hg, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add]
    ring_nf
  have ld : ∀ k w, LoadHolds Lm.read (σ (.n 321)) k w →
      LoadHolds Lm.read (σ (.n 15)) (17 * depth + k) w := fun k w hw => by
    rw [e312, tb_loadHolds_mul_gen_pow] at hw; exact hw
  have hcs := tb_holds_slice hnr h 237 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (327 + k)) (.n 321) k)) (by decide +kernel)
  have hvs := tb_holds_slice hnr h 243 ((List.range 3).map fun k ↦
    Stmt.atom (.load (.n (333 + k)) (.n 321) (6 + k))) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hcs hvs
  simp only [Atom.Holds] at hcs hvs
  have ecap : ∀ k < 5, σ (.n (327 + k)) = s.cap.getD k 0 := fun k hk =>
    tb_loadHolds_unique (ld _ _ (hcs k hk)) (hcap k hk)
  have eval : ∀ k < 3, σ (.n (333 + k)) = st.values.getD k 0 := fun k hk =>
    tb_loadHolds_unique (by have := ld _ _ (hvs k hk); rwa [← Nat.add_assoc] at this) (hval k hk)
  have e313 := tb_loadHolds_unique (ld _ _ l313) hcur
  have e314 := tb_loadHolds_unique (ld _ _ l314) hrow
  -- the point's copy
  obtain ⟨-, h8⟩ := tb_holds_callIf hnr h 236 (.n 325) "__loop7" [.n 326, .n 6, .n 7, .n 323]
    (by decide +kernel)
  have hne8 : σ (.n 325) ≠ 0 := by
    rw [a316, c315, hg]
    intro h0
    have := gen_pow_inj (by omega) (by omega)
      ((e_add_eq_zero_iff.mp h0).symm.trans (pow_zero gen).symm)
    omega
  have hrel8 := h8 hne8
  simp only [List.map_cons, List.map_nil, c317, e314] at hrel8
  have hz := l8_loop hg (by omega) (by omega) hrel8 hpl hpt
  -- the specification's run
  have hs : s = ⟨s.cap, []⟩ := by cases s; simp only at hpe; rw [hpe]
  have r1 := runsTo_readE ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ (σ (.n 27))
  have r2 := runsTo_readE ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)],
    [(σ (.n 27), dsObserve)]⟩ (σ (.n 37))
  have ea1 : (⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).absorb (σ (.n 27))
      dsObserve = ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], [(σ (.n 27), dsObserve)]⟩ := by
    simp [Fs.absorb, rateScalars]
  have ea2 : (⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], [(σ (.n 27), dsObserve)]⟩ :
      Fs).absorb (σ (.n 37)) dsObserve = ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)],
        [(σ (.n 27), dsObserve), (σ (.n 37), dsObserve)]⟩ := by
    simp [Fs.absorb, rateScalars]
  rw [ea1] at r1
  rw [ea2] at r2
  have hv : RunsTo (verifyGkrGrandProducts depth)
      ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩
      ([σ (.n 27)] ++ ([σ (.n 37)] ++ (xs ++ []))) (σ (.n 37), st.point, st.values) s :=
    r1.bind (r2.bind (hrun.bind (runsTo_ret _ _)))
  have hph : RunsTo (gkrPhase depth) ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩
      ([σ (.n 27)] ++ ([σ (.n 37)] ++ (xs ++ [])) ++ ([] ++ []))
      (σ (.n 37), st.point, st.values) s :=
    hv.bind ((tb_runsTo_require hcnt s).bind (runsTo_ret _ _))
  rw [hs] at hph
  refine ⟨depth, _, _, s.cap, hg, hd, ?_, hph, hpl, hvl, hz, ?_⟩
  · simp only [List.append_nil, List.singleton_append]
    rw [tbReadsAt_cons, tbReadsAt_cons]
    have l37' := (tb_loadHolds_mul_gen_pow Lm.read (σ (.n 5)) 1 0 (σ (.n 37))).mpr l37
    rw [pow_one] at l37'
    refine ⟨l27, l37', ?_⟩
    rw [mul_assoc, ← pow_two]
    exact hrd
  · rw [tb_eq_map_getD hcl, tb_eq_map_getD hvl]
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, List.length_append, List.length_cons,
      List.length_nil, List.cons.injEq, and_true]
    refine ⟨ecap 0 (by omega), ecap 1 (by omega), ecap 2 (by omega), ecap 3 (by omega),
      ecap 4 (by omega), ?_, eval 0 (by omega), eval 1 (by omega), eval 2 (by omega)⟩
    rw [q323, e313]
    ring

end
end LeanVM.Guest.B1.Tables
