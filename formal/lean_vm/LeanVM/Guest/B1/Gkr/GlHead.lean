/-
  LeanVM.Guest.B1.Gkr.GlHead

  The head of a radix-four layer (`glPre`) and the pieces between its rounds (`glHeadStore`,
  `glLoopCall`, `glTailSetup`), soundly.
-/

module

public import LeanVM.Guest.B1.Gkr.GlRounds
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«gkr_layer__L»

/-!
# A layer's head and middle, soundly

* `gl_pre`: at `x_j = g^j` and `start_g = g^(2 - sh)`, the slot is at `layers·g^(10 L)`,
  `L = 2j + 2 - sh`, the cursor and the round position are the slot's, the combiner is its
  sponge's challenge with the capacity after it at `35 ..`, the point row is
  `gkr_pts·g^(40(j + 1))`, the head record `rounds·pos`, and the claim the trees' values combined;
* `gl_headStore`: the head record gets the state after the head rounds;
* `gl_loopCall`: the loop's call on `qrow = pt·g^(2p)` and `nqrow = qrow·g^42`;
* `gl_tailSetup`: the last record `head·x_m`, its loads, and `tpt = qrow·x_m^8`,
  `ntpt = tpt·g^42`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem glPre_noRet : Stmt.noRetList glPre = true := by decide

theorem glD_pos {p : ℕ} (hp : p ≠ 0) : glD p = 78 * p + 6 := by simp [glD, hp]

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **The layer's head.** -/
theorem gl_pre (h : Stmt.HoldsList C rd σ glPre True kret) {j sh : ℕ} (hx : σ (.n (valf% «gkr_layer» "x_j")) = gen ^ j)
    (hsg : σ (.n (valf% «gkr_layer» "start_g")) = gen ^ (2 - sh)) (hsh : sh < 2) {s : Fs} {cur : E} {st : GkrState}
    {row pos : E} (hslot : GkSlot rd (σ (.n (valf% «gkr_layer» "layers"))) (2 * j + 2 - sh) s cur st row pos) :
    σ (.n (valf% «gkr_layer» "layer")) = σ (.n (valf% «gkr_layer» "layers")) * gen ^ (10 * (2 * j + 2 - sh)) ∧ σ (.n (valf% «gkr_layer» "s4#0")) = cur ∧
      σ (.n (valf% «gkr_layer» "nxt[0]@1")) = s.squeeze.1 ∧ (glCap (valf% «gkr_layer» "nxt[8]@1")).map σ = s.squeeze.2.cap ∧ σ (.n (valf% «gkr_layer» "round_pos")) = pos ∧
      σ (.n (valf% «gkr_layer» "point_row")) = σ (.n (valf% «gkr_layer» "gkr_pts")) * gen ^ (40 * (j + 1)) ∧ σ (.n (valf% «gkr_layer» "head")) = σ (.n (valf% «gkr_layer» "rounds")) * pos ∧
      σ (.n (valf% «gkr_layer» "claim@2")) = polyEval st.values s.squeeze.1 ∧
      σ (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]")) = 0 ∧ σ (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[2]")) = 0 ∧ σ (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[3]")) = 0 ∧ σ (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[4]")) = 0 := by
  have hnr := glPre_noRet
  obtain ⟨hcl, hcap, hpe, hcur, hvl, hval, -, -, hpos⟩ := hslot
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have m9 := a 0 (.mul (.n (valf% «gkr_layer» "x_layer~0")) (.n (valf% «gkr_layer» "x_j")) (.n (valf% «gkr_layer» "x_j"))) (by decide +kernel)
  have m10 := a 1 (.mul (.n (valf% «gkr_layer» "x_layer")) (.n (valf% «gkr_layer» "x_layer~0")) (.n (valf% «gkr_layer» "start_g"))) (by decide +kernel)
  have m11 := a 2 (.mul (.n (valf% «gkr_layer» "layer~0")) (.n (valf% «gkr_layer» "x_layer")) (.n (valf% «gkr_layer» "x_layer"))) (by decide +kernel)
  have m12 := a 3 (.mul (.n (valf% «gkr_layer» "layer~1")) (.n (valf% «gkr_layer» "layer~0")) (.n (valf% «gkr_layer» "layer~0"))) (by decide +kernel)
  have m13 := a 4 (.mul (.n (valf% «gkr_layer» "layer~2")) (.n (valf% «gkr_layer» "layer~1")) (.n (valf% «gkr_layer» "x_layer"))) (by decide +kernel)
  have m14 := a 5 (.mul (.n (valf% «gkr_layer» "layer~3")) (.n (valf% «gkr_layer» "layer~2")) (.n (valf% «gkr_layer» "layer~2"))) (by decide +kernel)
  have m15 := a 6 (.mul (.n (valf% «gkr_layer» "layer")) (.n (valf% «gkr_layer» "layers")) (.n (valf% «gkr_layer» "layer~3"))) (by decide +kernel)
  simp only [Atom.Holds] at m9 m10 m11 m12 m13 m14 m15
  set L := 2 * j + 2 - sh with hL
  have e10 : σ (.n (valf% «gkr_layer» "x_layer")) = gen ^ L := by
    rw [m10, m9, hx, hsg, ← pow_add, ← pow_add, show j + j + (2 - sh) = L by omega]
  have e15 : σ (.n (valf% «gkr_layer» "layer")) = σ (.n (valf% «gkr_layer» "layers")) * gen ^ (10 * L) := by
    rw [m15, m14, m13, m12, m11, e10, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    ring_nf
  have ld : ∀ k w, LoadHolds rd (σ (.n (valf% «gkr_layer» "layer"))) k w ↔ LoadHolds rd (σ (.n (valf% «gkr_layer» "layers"))) (10 * L + k) w := by
    intro k w; rw [e15, tb_loadHolds_mul_gen_pow]
  -- the slot's capacity, the combiner's permutation
  have hcapL := tb_holds_slice hnr h 7 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n ((valf% «gkr_layer» "sp[0]@1") + k)) (.n (valf% «gkr_layer» "layer")) k)) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hcapL
  simp only [Atom.Holds] at hcapL
  have ecap : ∀ k < 5, σ (.n ((valf% «gkr_layer» "sp[0]@1") + k)) = s.cap.getD k 0 := fun k hk =>
    tb_loadHolds_unique ((ld k _).mp (hcapL k hk)) (hcap k hk)
  have l21 := a 12 (.load (.n (valf% «gkr_layer» "s4#0")) (.n (valf% «gkr_layer» "layer")) 5) (by decide +kernel)
  have c23 := a 14 (.const (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]")) (word 0 0)) (by decide +kernel)
  have c24 := a 15 (.const (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[2]")) (word 0 0)) (by decide +kernel)
  have c25 := a 16 (.const (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[3]")) (word 0 0)) (by decide +kernel)
  have c26 := a 17 (.const (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[4]")) (word 0 0)) (by decide +kernel)
  have k1 := a 18 (.keccak ([.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[2]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[3]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[4]")] ++
      (List.range 5).map fun k ↦ .n ((valf% «gkr_layer» "sp[0]@1") + k)) (lyOuts (valf% «gkr_layer» "nxt[0]@1")) false false) (by decide +kernel)
  simp only [Atom.Holds, tb_word_zero] at l21 c23 c24 c25 c26
  obtain ⟨hP, hB⟩ := ly_keccak k1
  have hcapE : ((List.range 5).map fun k ↦ V.n ((valf% «gkr_layer» "sp[0]@1") + k)).map σ = s.cap := by
    rw [tb_eq_map_getD hcl, List.map_map]
    exact List.map_congr_left fun k hk => ecap k (List.mem_range.mp hk)
  have hins : (([.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[2]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[3]"), .n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[4]")] ++
      (List.range 5).map fun k ↦ V.n ((valf% «gkr_layer» "sp[0]@1") + k)) : List V).map σ = rateOf s.pend ++ s.cap := by
    rw [ly_zero_rate c23 c24 c25 c26, hpe, hcapE]
  rw [hins] at hP hB
  have e40 : σ (.n (valf% «gkr_layer» "nxt[0]@1")) = s.squeeze.1 := by
    rw [hP 0 (by omega)]
    exact (Keccak.challengeOf_cells _).symm
  -- the values, the position, the point row, the head record, the claim
  have l41 := a 19 (.load (.n (valf% «gkr_layer» "layer_vals[0]")) (.n (valf% «gkr_layer» "layer")) 6) (by decide +kernel)
  have l42 := a 20 (.load (.n (valf% «gkr_layer» "layer_vals[1]")) (.n (valf% «gkr_layer» "layer")) 7) (by decide +kernel)
  have l43 := a 21 (.load (.n (valf% «gkr_layer» "layer_vals[2]")) (.n (valf% «gkr_layer» "layer")) 8) (by decide +kernel)
  have l44 := a 22 (.load (.n (valf% «gkr_layer» "round_pos")) (.n (valf% «gkr_layer» "layer")) 9) (by decide +kernel)
  have c45 := a 23 (.const (.n (valf% «gkr_layer» "point_row~0")) (word 2 0)) (by decide +kernel)
  have m46 := a 24 (.mul (.n (valf% «gkr_layer» "point_row~1")) (.n (valf% «gkr_layer» "x_j")) (.n (valf% «gkr_layer» "point_row~0"))) (by decide +kernel)
  have m47 := a 25 (.mul (.n (valf% «gkr_layer» "point_row~2")) (.n (valf% «gkr_layer» "point_row~1")) (.n (valf% «gkr_layer» "point_row~1"))) (by decide +kernel)
  have m48 := a 26 (.mul (.n (valf% «gkr_layer» "point_row~3")) (.n (valf% «gkr_layer» "point_row~2")) (.n (valf% «gkr_layer» "point_row~2"))) (by decide +kernel)
  have m49 := a 27 (.mul (.n (valf% «gkr_layer» "point_row~4")) (.n (valf% «gkr_layer» "point_row~3")) (.n (valf% «gkr_layer» "point_row~1"))) (by decide +kernel)
  have m50 := a 28 (.mul (.n (valf% «gkr_layer» "point_row~5")) (.n (valf% «gkr_layer» "point_row~4")) (.n (valf% «gkr_layer» "point_row~4"))) (by decide +kernel)
  have m51 := a 29 (.mul (.n (valf% «gkr_layer» "point_row~6")) (.n (valf% «gkr_layer» "point_row~5")) (.n (valf% «gkr_layer» "point_row~5"))) (by decide +kernel)
  have m52 := a 30 (.mul (.n (valf% «gkr_layer» "point_row~7")) (.n (valf% «gkr_layer» "point_row~6")) (.n (valf% «gkr_layer» "point_row~6"))) (by decide +kernel)
  have m53 := a 31 (.mul (.n (valf% «gkr_layer» "point_row")) (.n (valf% «gkr_layer» "gkr_pts")) (.n (valf% «gkr_layer» "point_row~7"))) (by decide +kernel)
  have m54 := a 32 (.mul (.n (valf% «gkr_layer» "head")) (.n (valf% «gkr_layer» "rounds")) (.n (valf% «gkr_layer» "round_pos"))) (by decide +kernel)
  have m55 := a 33 (.mul (.n (valf% «gkr_layer» "claim@1~0")) (.n (valf% «gkr_layer» "nxt[0]@1")) (.n (valf% «gkr_layer» "layer_vals[2]"))) (by decide +kernel)
  have a56 := a 34 (.add (.n (valf% «gkr_layer» "claim@1")) (.n (valf% «gkr_layer» "layer_vals[1]")) (.n (valf% «gkr_layer» "claim@1~0"))) (by decide +kernel)
  have m57 := a 35 (.mul (.n (valf% «gkr_layer» "claim@2~0")) (.n (valf% «gkr_layer» "nxt[0]@1")) (.n (valf% «gkr_layer» "claim@1"))) (by decide +kernel)
  have a58 := a 36 (.add (.n (valf% «gkr_layer» "claim@2")) (.n (valf% «gkr_layer» "layer_vals[0]")) (.n (valf% «gkr_layer» "claim@2~0"))) (by decide +kernel)
  simp only [Atom.Holds] at l41 l42 l43 l44 c45 m46 m47 m48 m49 m50 m51 m52 m53 m54 m55 a56 m57 a58
  rw [tb_word_gen] at c45
  have e41 := tb_loadHolds_unique ((ld _ _).mp l41) (hval 0 (by omega))
  have e42 := tb_loadHolds_unique ((ld _ _).mp l42) (hval 1 (by omega))
  have e43 := tb_loadHolds_unique ((ld _ _).mp l43) (hval 2 (by omega))
  have e44 := tb_loadHolds_unique ((ld _ _).mp l44) hpos
  have e21 := tb_loadHolds_unique ((ld _ _).mp l21) hcur
  have e53 : σ (.n (valf% «gkr_layer» "point_row")) = σ (.n (valf% «gkr_layer» "gkr_pts")) * gen ^ (40 * (j + 1)) := by
    rw [m53, m52, m51, m50, m49, m48, m47, m46, c45, hx, ← pow_succ]
    ring
  refine ⟨e15, e21, e40, ?_, e44, e53, by rw [m54, e44], ?_, c23, c24, c25, c26⟩
  · rw [show glCap (valf% «gkr_layer» "nxt[8]@1") = lyCap (valf% «gkr_layer» "nxt[0]@1") by simp [glCap, lyCap], hB]
    rfl
  · obtain ⟨v0, v1, v2, hv3⟩ : ∃ v0 v1 v2, st.values = [v0, v1, v2] := by
      match st.values, hvl with
      | [v0, v1, v2], _ => exact ⟨v0, v1, v2, rfl⟩
    rw [a58, m57, a56, m55, e41, e42, e43, e40, hv3]
    simp only [polyEval, List.foldr, List.getD_cons_zero, List.getD_cons_succ]
    ring

/-- **The head record's stores**: the state after the head rounds. -/
theorem gl_headStore {p : ℕ} (hp4 : p < 4) (h : Stmt.HoldsList C rd σ (glHeadStore p) True kret) :
    TbCapAt rd (σ (.n (valf% «gkr_layer» "head"))) 0 gkCap ((glCapAfter 58 (2 * p) (glCap (valf% «gkr_layer» "nxt[8]@1"))).map σ) ∧
      LoadHolds rd (σ (.n (valf% «gkr_layer» "head"))) (5 * gkCap) (σ (.n (valf% «gkr_layer» "s4#0")) * gen ^ (4 * (2 * p))) ∧
      LoadHolds rd (σ (.n (valf% «gkr_layer» "head"))) (6 * gkCap) (σ (glClaimAfter 58 (2 * p) (.n (valf% «gkr_layer» "claim@2")))) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp only [glHeadStore, ↓reduceIte, glHeadStore0, tb_holdsList_append_noRet
      (tb_noRetList_mapAtoms 5 _), tb_holdsList_mapAtoms] at h
    obtain ⟨hc, hr⟩ := h
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hr hc
    simp only [glCapAfter, glClaimAfter, Nat.mul_zero, ↓reduceIte, pow_zero, mul_one]
    exact ⟨tbCapAt_glCap (off := 0) (fun k hk => by simpa using hc k hk), hr.1, hr.2⟩
  · have hp0 : p ≠ 0 := by omega
    simp only [glHeadStore, hp0, ↓reduceIte, glHeadStoreP, tb_holdsList_append_noRet
      (tb_noRetList_mapAtoms 5 _), tb_holdsList_mapAtoms] at h
    obtain ⟨hc, hr⟩ := h
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hr hc
    obtain ⟨c, m, l1, l2⟩ := hr
    rw [tb_word_two_pow (by omega)] at c
    have e1 : glCapAfter 58 (2 * p) (glCap (valf% «gkr_layer» "nxt[8]@1")) = glCap (39 + 78 * p) := by
      simp only [glCapAfter, show 2 * p ≠ 0 by omega, ↓reduceIte]
      rw [show 58 + 39 * (2 * p) - 19 = 39 + 78 * p by omega]
    have e2 : glClaimAfter 58 (2 * p) (.n (valf% «gkr_layer» "claim@2")) = .n (57 + 78 * p) := by
      simp only [glClaimAfter, show 2 * p ≠ 0 by omega, ↓reduceIte]
      rw [show 58 + 39 * (2 * p) - 1 = 57 + 78 * p by omega]
    rw [e1, e2, show 4 * (2 * p) = 8 * p by ring, ← c, ← m]
    exact ⟨tbCapAt_glCap (off := 0) (fun k hk => by simpa using hc k hk), l1, l2⟩

/-- **The loop's call**, on `qrow = pt·g^(2p)` and `nqrow = qrow·g^42`. -/
theorem gl_loopCall {p : ℕ} (hp : p < 4) {nm : String}
    (h : Stmt.HoldsList C rd σ (glLoopCall p nm) True kret) :
    1 + σ (.n (valf% «gkr_layer» "x_m")) ≠ 0 → C nm [1, σ (.n (valf% «gkr_layer» "x_m")), σ (.n (valf% «gkr_layer» "head")), σ (.n (valf% «gkr_layer» "point_row")) * gen ^ (2 * p),
      σ (.n (valf% «gkr_layer» "point_row")) * gen ^ (2 * p) * gen ^ 42, σ (.n (valf% «gkr_layer» "tabs"))] [] := by
  rcases Nat.eq_zero_or_pos p with rfl | hp1
  · simp only [glLoopCall, ↓reduceIte, glLoopCall0, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
      List.map_cons, List.map_nil] at h
    obtain ⟨c59, a60, c61, c62, m63, -, hc, -⟩ := h
    rw [tb_word_one] at c59 c61
    rw [tb_word_two_pow (by norm_num)] at c62
    intro hne
    have := hc (by rw [a60, c59]; exact hne)
    rw [c61, m63, c62] at this
    simpa using this
  · have hp0 : p ≠ 0 := by omega
    simp only [glLoopCall, hp0, ↓reduceIte, glLoopCallP, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
      List.map_cons, List.map_nil] at h
    obtain ⟨c1, a2, c3, c4, m5, c6, m7, -, hc, -⟩ := h
    rw [tb_word_one] at c1 c3
    rw [tb_word_two_pow (by omega)] at c4 c6
    intro hne
    have := hc (by rw [a2, c1]; exact hne)
    rw [c3, m5, m7, c4, c6] at this
    rwa [mul_assoc, ← pow_add, Nat.add_comm (2 * p) 42]

/-- **The tail's pointers** and the last record's loads. -/
theorem gl_tailSetup {p : ℕ} (hp4 : p < 4) (h : Stmt.HoldsList C rd σ (glTailSetup p) True kret) :
    σ (.n (67 + glD p)) = σ (.n (valf% «gkr_layer» "point_row")) * gen ^ (2 * p) * σ (.n (valf% «gkr_layer» "x_m")) ^ 8 ∧
      σ (.n (70 + glD p)) = σ (.n (67 + glD p)) * gen ^ 42 ∧
      TbCapAt rd (σ (.n (valf% «gkr_layer» "head")) * σ (.n (valf% «gkr_layer» "x_m"))) 0 gkCap ((glCap (71 + glD p)).map σ) ∧
      LoadHolds rd (σ (.n (valf% «gkr_layer» "head")) * σ (.n (valf% «gkr_layer» "x_m"))) (5 * gkCap) (σ (.n (76 + glD p))) ∧
      LoadHolds rd (σ (.n (valf% «gkr_layer» "head")) * σ (.n (valf% «gkr_layer» "x_m"))) (6 * gkCap) (σ (.n (77 + glD p))) := by
  have hloads : ∀ w, Stmt.HoldsList C rd σ (glTailLoads p w) True kret → σ (.n w) = σ (.n (valf% «gkr_layer» "head")) * σ (.n (valf% «gkr_layer» "x_m")) →
      TbCapAt rd (σ (.n (valf% «gkr_layer» "head")) * σ (.n (valf% «gkr_layer» "x_m"))) 0 gkCap ((glCap (71 + glD p)).map σ) ∧
      LoadHolds rd (σ (.n (valf% «gkr_layer» "head")) * σ (.n (valf% «gkr_layer» "x_m"))) (5 * gkCap) (σ (.n (76 + glD p))) ∧
      LoadHolds rd (σ (.n (valf% «gkr_layer» "head")) * σ (.n (valf% «gkr_layer» "x_m"))) (6 * gkCap) (σ (.n (77 + glD p))) := by
    intro w hl hw
    simp only [glTailLoads, tb_holdsList_append_noRet (tb_noRetList_mapAtoms 5 _),
      tb_holdsList_mapAtoms] at hl
    obtain ⟨hc, hr⟩ := hl
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hr hc
    rw [← hw]
    exact ⟨tbCapAt_glCap (off := 0) (fun k hk => by simpa [Nat.add_assoc] using hc k hk), hr.1,
      hr.2⟩
  rcases Nat.eq_zero_or_pos p with rfl | hp1
  · simp only [glTailSetup, ↓reduceIte, glTailSetup0, holdsList_append, Stmt.HoldsList,
      Stmt.Holds, Atom.Holds] at h
    obtain ⟨m64, m65, m66, m67, m68, c69, m70, m71, hl⟩ := h
    rw [tb_word_two_pow (by norm_num)] at c69
    have hD : glD 0 = 0 := rfl
    simp only [hD, Nat.add_zero, Nat.mul_zero, pow_zero, mul_one]
    refine ⟨by rw [m68, m67, m66, m65]; ring, by rw [m71, m70, c69, m68, m67]; ring,
      hloads 63 hl m64⟩
  · have hp0 : p ≠ 0 := by omega
    simp only [glTailSetup, hp0, ↓reduceIte, glTailSetupP, holdsList_append, Stmt.HoldsList,
      Stmt.Holds, Atom.Holds] at h
    obtain ⟨m0, m1, m2, m3, c4, m5, m6, c7, m8, m9, hl⟩ := h
    rw [tb_word_two_pow (by omega)] at c4 c7
    obtain ⟨hcap, hcur, hcl⟩ := hloads _ hl m0
    rw [glD_pos hp0] at hcap hcur hcl ⊢
    rw [show 67 + (78 * p + 6) = 73 + 78 * p by omega, show 70 + (78 * p + 6) = 76 + 78 * p by omega]
    refine ⟨?_, ?_, hcap, hcur, hcl⟩
    · rw [m6, m5, c4, m3, m2, m1]; ring
    · rw [m9, m8, c7, m6, m5, c4, m3, m2, m1, pow_add]
      ring

end Sem

end
end LeanVM.Guest.B1.Tables
