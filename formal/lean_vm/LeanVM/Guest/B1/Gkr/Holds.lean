/-
  LeanVM.Guest.B1.Gkr.Holds

  `verify_bus_gkr` computes the specification's bus GKR walk: `verify_bus_gkr_holds`.
-/

module

public import LeanVM.Guest.B1.Gkr.Interface
public import LeanVM.Guest.B1.Gkr.Walk
public import LeanVM.Guest.B1.Gkr.Loop8
public import LeanVM.Guest.B1.Placement.Common
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.CoreData

/-!
# `verify_bus_gkr` is sound (G:1866-2047)

The body (`vbgPre`, the core IR's): the range check of `g_bus_mu = g^depth` (`depth ≤ 32`), the
two roots read and the count asserted nonzero, the combiner drawn from the two roots waiting
(a grind of `0` bits) and the batched claim (`gkr_combine`), the tables `k_mod_next`,
`loop_bounds[d] = g^((d - 1) / 2)` and `depth_odd[d] = g^(d % 2)`, the root-most layer
(`rt_two` at an odd depth, `rt_four` at an even one), the layer loop `verify_bus_gkr_loop0`
(`ly_step`, `ly_chain`), the final slot, the point's copy to `zeta` (`verify_bus_gkr_loop1`), the
trees' values into a buffer of three, and the return.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `verify_bus_gkr`'s parameters. -/
def vbgParams : List V := (List.range 9).map V.n

/-- `verify_bus_gkr`'s body, the core IR's. -/
noncomputable def vbgBody : List Stmt := (fn% «verify_bus_gkr»).body

/-- `verify_bus_gkr`'s statements before its `ret`. -/
noncomputable def vbgPre : List Stmt := vbgBody.take 233

/-- `verify_bus_gkr`'s returned values. -/
def vbgRets : List V := (List.range 7).map fun k ↦ .n (398 + k)

noncomputable def vbgCheck : Bool :=
  match coreProgram.find? name% «verify_bus_gkr» with
  | some fn => decide (fn.params = vbgParams) && tbStmtsEqb fn.body (vbgPre ++ [.ret vbgRets])
  | none => false

theorem vbgCheck_eq : vbgCheck = true := by decide +kernel

theorem vbgFound : ∃ fn : Fn, coreProgram.find? name% «verify_bus_gkr» = some fn ∧
    fn.params = vbgParams ∧ fn.body = vbgPre ++ [.ret vbgRets] := by
  have h := vbgCheck_eq
  unfold vbgCheck at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

theorem vbgPre_noRet : Stmt.noRetList vbgPre = true := by decide +kernel

/-- The sponge after the two roots: the carried capacity, both waiting. -/
def vbgS1 (σ : Val) : Fs :=
  ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)],
    [(σ (.n 28), dsObserve), (σ (.n 33), dsObserve)]⟩

/-- The trees' roots: push and pull share one, then the count's. -/
def vbgSt0 (σ : Val) : GkrState := ⟨[σ (.n 28), σ (.n 28), σ (.n 33)], []⟩

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **The roots and the combiner**: the two roots read at the cursor, the count nonzero, the
combiner the sponge's challenge with both waiting, the batched claim, the capacity after it, and
the zeros the layers' empty rates read. -/
theorem vbg_root (h : Stmt.HoldsList C rd σ vbgPre True kret) :
    LoadHolds rd (σ (.n 5)) 0 (σ (.n 28)) ∧ LoadHolds rd (σ (.n 5)) 1 (σ (.n 33)) ∧
      σ (.n 33) ≠ 0 ∧ σ (.n 59) = (vbgS1 σ).squeeze.1 ∧
      σ (.n 63) = polyEval (vbgSt0 σ).values (vbgS1 σ).squeeze.1 ∧
      (lyCap 46).map σ = capOf (vbgS1 σ).perm ∧
      σ (.n 42) = 0 ∧ σ (.n 43) = 0 ∧ σ (.n 44) = 0 ∧ σ (.n 45) = 0 := by
  have hnr := vbgPre_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have r0 := tb_holds_slice hnr h 17 (fsNextT (.n 5) 0 28) (by decide +kernel)
  have r1 := tb_holds_slice hnr h 22 (fsNextT (.n 5) 1 33) (by decide +kernel)
  rw [holds_fsNextT] at r0 r1
  obtain ⟨⟨l28, p28⟩, -⟩ := r0
  obtain ⟨⟨l33, p33⟩, -⟩ := r1
  have cp : ∀ k < 5, σ (.n (23 + k)) = σ (.n k) := by
    intro k hk
    have := tb_holds_slice hnr h 12 ((List.range 5).map fun k ↦
      Stmt.atom (.copy (.n (23 + k)) (.n k))) (by decide +kernel)
    rw [tb_holdsList_mapAtoms] at this
    exact this k hk
  have q31 := a 20 (.copy (.n 31) (.n 28)) (by decide +kernel)
  have q32 := a 21 (.copy (.n 32) (.n 28)) (by decide +kernel)
  have q36 := a 25 (.copy (.n 36) (.n 33)) (by decide +kernel)
  have c37 := a 26 (.const (.n 37) (word 0 0)) (by decide +kernel)
  have a38 := a 27 (.add (.n 38) (.n 33) (.n 37)) (by decide +kernel)
  have n38 := a 29 (.assertNe (.n 38) (.n 39) (.n 40)) (by decide +kernel)
  have c42 := a 31 (.const (.n 42) (word 0 0)) (by decide +kernel)
  have c43 := a 32 (.const (.n 43) (word 0 0)) (by decide +kernel)
  have c44 := a 33 (.const (.n 44) (word 0 0)) (by decide +kernel)
  have c45 := a 34 (.const (.n 45) (word 0 0)) (by decide +kernel)
  have k1 := a 35 (.keccak ([.n 29, .n 30, .n 34, .n 35, .n 42, .n 43, .n 44, .n 45] ++
    (List.range 5).map fun k ↦ .n (23 + k)) (lyOuts 46) false false) (by decide +kernel)
  have c59 := a 36 (.copy (.n 59) (.n 46)) (by decide +kernel)
  have m60 := a 37 (.mul (.n 60) (.n 59) (.n 36)) (by decide +kernel)
  have a61 := a 38 (.add (.n 61) (.n 32) (.n 60)) (by decide +kernel)
  have m62 := a 39 (.mul (.n 62) (.n 59) (.n 61)) (by decide +kernel)
  have a63 := a 40 (.add (.n 63) (.n 31) (.n 62)) (by decide +kernel)
  simp only [Atom.Holds, tb_word_zero] at q31 q32 q36 c37 a38 n38 c42 c43 c44 c45 c59 m60 a61 m62 a63
  obtain ⟨P, B⟩ := ly_keccak k1
  have hins : (([.n 29, .n 30, .n 34, .n 35, .n 42, .n 43, .n 44, .n 45] ++
      (List.range 5).map fun k ↦ V.n (23 + k)) : List V).map σ =
      rateOf (vbgS1 σ).pend ++ (vbgS1 σ).cap := by
    obtain ⟨e29, e30⟩ := Prod.ext_iff.mp (fsPackT_cells p28)
    obtain ⟨e34, e35⟩ := Prod.ext_iff.mp (fsPackT_cells p33)
    have hcapE : ((List.range 5).map fun k ↦ V.n (23 + k)).map σ =
        [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] := by
      rw [List.map_map, show [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] =
        (List.range 5).map (fun k ↦ σ (.n k)) from rfl]
      exact List.map_congr_left fun k hk => cp k (List.mem_range.mp hk)
    rw [List.map_append, hcapE, rateOf_eq_cells _ (by simp [vbgS1])]
    norm_num at e29 e30 e34 e35
    simp [vbgS1, pendCells, e29, e30, e34, e35, c42, c43, c44, c45]
  rw [hins] at P B
  have e59 : σ (.n 59) = (vbgS1 σ).squeeze.1 := by
    rw [c59, P 0 (by omega)]; exact (Keccak.challengeOf_cells _).symm
  refine ⟨l28, l33, fun h0 => ?_, e59, ?_, B, c42, c43, c44, c45⟩
  · obtain ⟨e40, e1⟩ := n38
    rw [a38, c37, h0, zero_add, zero_mul] at e40
    exact zero_ne_one (e40.symm.trans e1)
  · rw [a63, m62, a61, m60, q31, q32, q36, ← e59]
    simp only [vbgSt0, polyEval, List.foldr]
    ring

/-- **The tables** at `g_bus_mu = g^depth`: `k_mod_next`, `depth_odd[depth] = g^(depth % 2)` and
`loop_bounds[depth] = g^((depth - 1) / 2)`, and the loop's `start_g = g^(2 - depth % 2)`. -/
theorem vbg_tables (h : Stmt.HoldsList C rd σ vbgPre True kret) {depth : ℕ}
    (hg : σ (.n 6) = gen ^ depth) (hd : depth < 33) :
    KModNext rd (σ (.n 64)) ∧ σ (.n 142) = gen ^ (depth % 2) ∧
      σ (.n 378) = gen ^ ((depth - 1) / 2) ∧ σ (.n 382) = gen ^ ((depth - 1) / 2) ∧
      σ (.n 375) = gen ^ (2 - depth % 2) := by
  have hnr := vbgPre_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have hk := tb_holds_slice hnr h 42 ((List.range 4).map fun r ↦
    [Stmt.atom (.const (.n (65 + 2 * r)) (word (2 ^ ((r + 1) % 4)) 0)),
      .atom (.load (.n (65 + 2 * r)) (.n 64) r),
      .atom (.const (.n (66 + 2 * r)) (word (2 ^ ((r + 1) / 4)) 0)),
      .atom (.load (.n (66 + 2 * r)) (.n 64) (4 + r))]).flatten (by decide +kernel)
  rw [tb_holdsList_flatten_range _ _ (fun _ => rfl)] at hk
  have ht := tb_holds_slice hnr h 60 (((List.range 33).map fun d ↦
    [Stmt.atom (.const (.n (75 + 2 * d)) (word (2 ^ ((d - 1) / 2)) 0)),
      .atom (.load (.n (75 + 2 * d)) (.n 73) d),
      .atom (.const (.n (76 + 2 * d)) (word (2 ^ (d % 2)) 0)),
      .atom (.load (.n (76 + 2 * d)) (.n 74) d)]).flatten) (by decide +kernel)
  rw [tb_holdsList_flatten_range _ _ (fun _ => rfl)] at ht
  have hdt := ht depth hd
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hdt
  obtain ⟨c0, l0, c1, l1⟩ := hdt
  rw [c0, tb_word_two_pow (by omega)] at l0
  rw [c1, tb_word_two_pow (by omega)] at l1
  have m141 := a 192 (.mul (.n 141) (.n 74) (.n 6)) (by decide +kernel)
  have l142 := a 193 (.load (.n 142) (.n 141) 0) (by decide +kernel)
  have c374 := a 197 (.const (.n 374) (word 4 0)) (by decide +kernel)
  have m374 := a 198 (.mul (.n 374) (.n 375) (.n 142)) (by decide +kernel)
  have m377 := a 200 (.mul (.n 377) (.n 73) (.n 6)) (by decide +kernel)
  have l378 := a 201 (.load (.n 378) (.n 377) 0) (by decide +kernel)
  have m381 := a 204 (.mul (.n 381) (.n 73) (.n 6)) (by decide +kernel)
  have l382 := a 205 (.load (.n 382) (.n 381) 0) (by decide +kernel)
  simp only [Atom.Holds] at m141 l142 c374 m374 m377 l378 m381 l382
  rw [m141, hg, tb_loadHolds_mul_gen_pow, Nat.add_zero] at l142
  rw [m377, hg, tb_loadHolds_mul_gen_pow, Nat.add_zero] at l378
  rw [m381, hg, tb_loadHolds_mul_gen_pow, Nat.add_zero] at l382
  have e142 := tb_loadHolds_unique l142 l1
  refine ⟨fun r hr => ?_, e142, tb_loadHolds_unique l378 l0, tb_loadHolds_unique l382 l0, ?_⟩
  · have := hk r hr
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
    obtain ⟨c0, l0, c1, l1⟩ := this
    rw [c0, tb_word_two_pow (by omega)] at l0
    rw [c1, tb_word_two_pow (by omega)] at l1
    exact ⟨l1, l0⟩
  · rw [show (4 : ℕ) = 2 ^ 2 by norm_num, tb_word_two_pow (by norm_num)] at c374
    rw [c374, e142] at m374
    have hsh : depth % 2 ≤ 2 := by omega
    have hne : (gen : E) ^ (depth % 2) ≠ 0 := pow_ne_zero _ gen_ne_zero
    apply mul_right_cancel₀ hne
    rw [← m374, ← pow_add, Nat.sub_add_cancel hsh]

end Sem

/-- **The walk**: from the sponge the roots wait in, the root-most layer and the layer loop run
`gkrLayers depth` to the slot of `L = depth`, nothing waiting. -/
theorem vbg_walk (hGR : tb_gkr_rounds_Spec) {rd : Reader} {σ : Val} {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbgPre True kret) {depth : ℕ}
    (hg : σ (.n 6) = gen ^ depth) (hd : depth < 33) (hd0 : depth ≠ 0) :
    ∃ (xs : List E) (st : GkrState) (s : Fs) (row pos half par : E),
      RunsTo (gkrLayers depth (vbgSt0 σ)) (vbgS1 σ) xs st s ∧
      TbReadsAt rd (σ (.n 5) * gen ^ 2) xs ∧
      GkSlot rd (σ (.n 16)) depth s (σ (.n 5) * gen ^ 2 * gen ^ xs.length) st row pos half par := by
  have hnr := vbgPre_noRet
  have a := fun n a heq => tb_holds_atom hnr h n a heq
  obtain ⟨-, -, -, h59, h63, hcap, z42, z43, z44, z45⟩ := vbg_root h
  obtain ⟨hk, e142, e378, e382, e375⟩ := vbg_tables h hg hd
  -- the layer loop's iterations
  have c376 := a 199 (.const (.n 376) (word 1 0)) (by decide +kernel)
  have a379 := a 202 (.add (.n 379) (.n 376) (.n 378)) (by decide +kernel)
  have c380 := a 203 (.const (.n 380) (word 1 0)) (by decide +kernel)
  simp only [Atom.Holds, tb_word_one] at c376 a379 c380
  obtain ⟨-, h6⟩ := tb_holds_callIf hnr h 206 (.n 379) name% «verify_bus_gkr_loop0»
    [.n 380, .n 382, .n 375, .n 16, .n 8, .n 17, .n 63, .n 142, .n 6, .n 64] (by decide +kernel)
  have hB : ∀ j < (depth - 1) / 2, LyB rd (σ (.n 375)) (σ (.n 142)) (σ (.n 16)) (σ (.n 64)) (gen ^ j) := by
    intro j hj
    have hne : σ (.n 379) ≠ 0 := by
      rw [a379, c376, e378]
      intro h0
      have := gen_pow_inj (by omega) (by omega)
        ((e_add_eq_zero_iff.mp h0).symm.trans (pow_zero gen).symm)
      omega
    have hrel := h6 hne
    simp only [List.map_cons, List.map_nil, c380] at hrel
    rw [← pow_zero gen] at hrel
    obtain ⟨m', -, hN, hall⟩ := tb_loop_sound
      (B := LyB rd (σ (.n 375)) (σ (.n 142)) (σ (.n 16)) (σ (.n 64)))
      (fun d x hx => ly_step hGR d x hx) 0 hrel
    have hm' : (depth - 1) / 2 ≤ m' := by
      by_contra hc
      have := gen_pow_inj (by omega) (by omega) (e382.symm.trans hN)
      omega
    exact hall j (by omega) (by omega)
  obtain ⟨v0, v1, v2, hv⟩ : ∃ v0 v1 v2, (vbgSt0 σ).values = [v0, v1, v2] := ⟨_, _, _, rfl⟩
  rcases Nat.mod_two_eq_zero_or_one depth with h2 | h2
  · -- an even depth: the radix-four root layer, then the layers
    have hi := tb_holds_slice hnr h 196 [.ite (.n 144) rtFour rtTwo] (by decide +kernel)
    simp only [Stmt.HoldsList] at hi
    rw [tb_holds_ite_noRet _ _ _ rtFour_noRet rtTwo_noRet] at hi
    obtain ⟨⟨-, hfour, -⟩, -⟩ := hi
    have c143 := a 194 (.const (.n 143) (word 1 0)) (by decide +kernel)
    have a144 := a 195 (.add (.n 144) (.n 142) (.n 143)) (by decide +kernel)
    simp only [Atom.Holds, tb_word_one] at c143 a144
    have h0 : σ (.n 144) = 0 := by rw [a144, c143, e142, h2, pow_zero, e_add_self]
    obtain ⟨xs1, st1, s1, hrun1, hrd1, hsl1⟩ := rt_four (hfour h0) rfl rfl h59 h63 hcap
      z42 z43 z44 z45
    have hsl1' : GkSlot rd (σ (.n 16)) (2 - depth % 2) s1 (σ (.n 5) * gen ^ 2 * gen ^ xs1.length)
        st1 (σ (.n 18) * gen ^ 40) gen (gen ^ ((1 - depth % 2) / 4))
        (gen ^ ((1 - depth % 2) % 4)) := by rw [h2]; simpa using hsl1
    obtain ⟨xs, st, s, pos, hrun, hrd, hsl⟩ := ly_chain hk (sh := depth % 2) e375 e142 (by omega)
      (by omega) hB hsl1' ((depth - 1) / 2) le_rfl
    have hrun' : RunsTo (gkrLayers depth (vbgSt0 σ)) (vbgS1 σ) (xs1 ++ xs) st s := by
      rw [show depth = 2 * ((depth - 1) / 2) + 2 by omega, gkrLayers_even]
      exact hrun1.bind hrun
    have hrd' : TbReadsAt rd (σ (.n 5) * gen ^ 2) (xs1 ++ xs) := by
      rw [tbReadsAt_append]
      exact ⟨hrd1, hrd⟩
    rw [show 2 * ((depth - 1) / 2) + 2 - depth % 2 = depth by omega,
      mul_assoc (σ (.n 5) * gen ^ 2), ← pow_add,
      ← List.length_append] at hsl
    exact ⟨xs1 ++ xs, st, s, _, _, _, _, hrun', hrd', hsl⟩
  · -- an odd depth: the binary root layer, then the layers
    have hi := tb_holds_slice hnr h 196 [.ite (.n 144) rtFour rtTwo] (by decide +kernel)
    simp only [Stmt.HoldsList] at hi
    rw [tb_holds_ite_noRet _ _ _ rtFour_noRet rtTwo_noRet] at hi
    obtain ⟨⟨-, -, htwo⟩, -⟩ := hi
    have c143 := a 194 (.const (.n 143) (word 1 0)) (by decide +kernel)
    have a144 := a 195 (.add (.n 144) (.n 142) (.n 143)) (by decide +kernel)
    simp only [Atom.Holds, tb_word_one] at c143 a144
    have hne : σ (.n 144) ≠ 0 := by
      rw [a144, c143, e142, h2, pow_one]
      intro h0
      have := gen_pow_inj (a := 1) (b := 0) (by omega) (by omega)
        ((pow_one gen).trans ((e_add_eq_zero_iff.mp h0).trans (pow_zero gen).symm))
      omega
    obtain ⟨xs1, st1, s1, hrun1, hrd1, hsl1⟩ := rt_two (htwo hne) rfl rfl h59 h63 hcap
      z42 z43 z44 z45
    have hsl1' : GkSlot rd (σ (.n 16)) (2 - depth % 2) s1 (σ (.n 5) * gen ^ 2 * gen ^ xs1.length)
        st1 (σ (.n 18) * gen ^ 40) gen (gen ^ ((1 - depth % 2) / 4))
        (gen ^ ((1 - depth % 2) % 4)) := by rw [h2]; simpa using hsl1
    obtain ⟨xs, st, s, pos, hrun, hrd, hsl⟩ := ly_chain hk (sh := depth % 2) e375 e142 (by omega)
      (by omega) hB hsl1' ((depth - 1) / 2) le_rfl
    have hrun' : RunsTo (gkrLayers depth (vbgSt0 σ)) (vbgS1 σ) (xs1 ++ xs) st s := by
      rw [show depth = 2 * ((depth - 1) / 2) + 1 by omega, gkrLayers_odd]
      exact hrun1.bind hrun
    have hrd' : TbReadsAt rd (σ (.n 5) * gen ^ 2) (xs1 ++ xs) := by
      rw [tbReadsAt_append]
      exact ⟨hrd1, hrd⟩
    rw [show 2 * ((depth - 1) / 2) + 2 - depth % 2 = depth by omega,
      mul_assoc (σ (.n 5) * gen ^ 2), ← pow_add,
      ← List.length_append] at hsl
    exact ⟨xs1 ++ xs, st, s, _, _, _, _, hrun', hrd', hsl⟩

/-- **`verify_bus_gkr` is sound**: on any memory of at most `2^32` words, at a depth other than
`0`, it runs the specification's GKR walk and count check (`gkrPhase`) on the words it reads,
writes the point to `zeta` and returns the sponge's capacity, the cursor past the words and a
buffer of the three values, given the rounds `gkr_rounds__L{n}` (`verify_bus_gkr_holds`,
`RoundsHolds`). -/
theorem verify_bus_gkr_holds_of (hGR : tb_gkr_rounds_Spec) {μ : ℕ} (hμ : μ ≤ 32)
    (Lm : MemoryImage μ) : verify_bus_gkr_Spec Lm.read := by
  intro args rets hne hrel
  obtain ⟨fn, hf, hp, hb⟩ := vbgFound
  obtain ⟨σ, hpar, h, hret⟩ := (tb_rel_pre hf hb vbgPre_noRet args rets).mp hrel
  rw [hp] at hpar
  have hargs : args = [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6),
      σ (.n 7), σ (.n 8)] := by rw [← hpar]; rfl
  have hrets : rets = [σ (.n 398), σ (.n 399), σ (.n 400), σ (.n 401), σ (.n 402), σ (.n 403),
      σ (.n 404)] := by rw [← hret]; rfl
  subst hargs hrets
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hne
  have hnr := vbgPre_noRet
  have a := fun n a heq => tb_holds_atom hnr h n a heq
  -- the depth
  have c19 := a 10 (.const (.n 19) (word 4294967296 0)) (by decide +kernel)
  have rc := a 11 (.rangeCheck (.n 6) (.n 20) (.n 21) (.n 22) (.n 19)) (by decide +kernel)
  simp only [Atom.Holds] at c19 rc
  obtain ⟨depth, hd, hg⟩ := tb_rc_sound' hμ Lm (K := 33) (by omega) (by norm_num)
    (by rw [c19, show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num),
      gen_pow_eq_ofK]) rc.1 rc.2.1 rc.2.2
  have hd0 : depth ≠ 0 := by rintro rfl; exact hne (by rw [hg, pow_zero])
  -- the roots and the walk
  obtain ⟨l28, l33, hcnt, -⟩ := vbg_root h
  obtain ⟨xs, st, s, row, pos, half, par, hrun, hrd, hsl⟩ := vbg_walk hGR h hg hd hd0
  obtain ⟨hcl, hcap, hpe, hcur, hvl, hval, hrow, hpl, hpt, -, -, -⟩ := hsl
  -- the final slot
  have m383 := a 207 (.mul (.n 383) (.n 6) (.n 6)) (by decide +kernel)
  have m384 := a 208 (.mul (.n 384) (.n 383) (.n 6)) (by decide +kernel)
  have m385 := a 209 (.mul (.n 385) (.n 384) (.n 384)) (by decide +kernel)
  have m386 := a 210 (.mul (.n 386) (.n 385) (.n 385)) (by decide +kernel)
  have m387 := a 211 (.mul (.n 387) (.n 386) (.n 6)) (by decide +kernel)
  have m388 := a 212 (.mul (.n 388) (.n 16) (.n 387)) (by decide +kernel)
  have l389 := a 213 (.load (.n 389) (.n 388) 5) (by decide +kernel)
  have l390 := a 214 (.load (.n 390) (.n 388) 9) (by decide +kernel)
  have c391 := a 215 (.const (.n 391) (word 1 0)) (by decide +kernel)
  have a392 := a 216 (.add (.n 392) (.n 391) (.n 6)) (by decide +kernel)
  have c393 := a 217 (.const (.n 393) (word 1 0)) (by decide +kernel)
  have q403 := a 231 (.copy (.n 403) (.n 389)) (by decide +kernel)
  have q404 := a 232 (.copy (.n 404) (.n 394)) (by decide +kernel)
  simp only [Atom.Holds] at m383 m384 m385 m386 m387 m388 l389 l390 c391 a392 c393 q403 q404
  rw [tb_word_one] at c391 c393
  have e388 : σ (.n 388) = σ (.n 16) * gen ^ (13 * depth) := by
    rw [m388, m387, m386, m385, m384, m383, hg, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add]
    ring_nf
  have ld : ∀ k w, LoadHolds Lm.read (σ (.n 388)) k w →
      LoadHolds Lm.read (σ (.n 16)) (13 * depth + k) w := fun k w hw => by
    rw [e388, tb_loadHolds_mul_gen_pow] at hw; exact hw
  have hcs := tb_holds_slice hnr h 226 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (398 + k)) (.n 388) k)) (by decide +kernel)
  have hvs := tb_holds_slice hnr h 220 ((List.range 3).map fun k ↦
    [Stmt.atom (.load (.n (395 + k)) (.n 388) (6 + k)),
      .atom (.load (.n (395 + k)) (.n 394) k)]).flatten (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hcs
  rw [tb_holdsList_flatten_range _ _ (fun _ => rfl)] at hvs
  simp only [Atom.Holds] at hcs
  have ecap : ∀ k < 5, σ (.n (398 + k)) = s.cap.getD k 0 := fun k hk =>
    tb_loadHolds_unique (ld _ _ (hcs k hk)) (hcap k hk)
  have eval : ∀ k < 3, LoadHolds Lm.read (σ (.n 394)) k (st.values.getD k 0) := by
    intro k hk
    have := hvs k hk
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
    obtain ⟨l1, l2⟩ := this
    have e := tb_loadHolds_unique (by have := ld _ _ l1; rwa [← Nat.add_assoc] at this) (hval k hk)
    rw [e] at l2
    exact l2
  have e389 := tb_loadHolds_unique (ld _ _ l389) hcur
  have e390 := tb_loadHolds_unique (ld _ _ l390) hrow
  -- the point's copy
  obtain ⟨-, h7⟩ := tb_holds_callIf hnr h 218 (.n 392) name% «verify_bus_gkr_loop1» [.n 393, .n 6,
      .n 7, .n 390]
    (by decide +kernel)
  have hne7 : σ (.n 392) ≠ 0 := by
    rw [a392, c391, hg]
    intro h0
    have := gen_pow_inj (by omega) (by omega)
      ((e_add_eq_zero_iff.mp h0).symm.trans (pow_zero gen).symm)
    omega
  have hrel7 := h7 hne7
  simp only [List.map_cons, List.map_nil, c393, e390] at hrel7
  have hz := l8_loop hg (by omega) (by omega) hrel7 hpl hpt
  -- the specification's run
  have hs : s = ⟨s.cap, []⟩ := by cases s; simp only at hpe; rw [hpe]
  have r1 := runsTo_readE ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ (σ (.n 28))
  have r2 := runsTo_readE ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)],
    [(σ (.n 28), dsObserve)]⟩ (σ (.n 33))
  have ea1 : (⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).absorb (σ (.n 28))
      dsObserve = ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], [(σ (.n 28), dsObserve)]⟩ := by
    simp [Fs.absorb, rateScalars]
  have ea2 : (⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], [(σ (.n 28), dsObserve)]⟩ :
      Fs).absorb (σ (.n 33)) dsObserve = vbgS1 σ := by
    simp [Fs.absorb, rateScalars, vbgS1]
  rw [ea1] at r1
  rw [ea2] at r2
  have hv : RunsTo (verifyGkrGrandProducts depth)
      ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩
      ([σ (.n 28)] ++ ([σ (.n 33)] ++ (xs ++ []))) (σ (.n 33), st.point, st.values) s :=
    r1.bind (r2.bind (hrun.bind (runsTo_ret _ _)))
  have hph : RunsTo (gkrPhase depth) ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩
      ([σ (.n 28)] ++ ([σ (.n 33)] ++ (xs ++ [])) ++ ([] ++ []))
      (σ (.n 33), st.point, st.values) s :=
    hv.bind ((tb_runsTo_require hcnt s).bind (runsTo_ret _ _))
  rw [hs] at hph
  refine ⟨depth, _, _, s.cap, σ (.n 394), hg, hd, ?_, hph, hpl, hvl, hz, ?_, ?_⟩
  · simp only [List.append_nil, List.singleton_append]
    rw [tbReadsAt_cons, tbReadsAt_cons]
    have l33' := (tb_loadHolds_mul_gen_pow Lm.read (σ (.n 5)) 1 0 (σ (.n 33))).mpr l33
    rw [pow_one] at l33'
    refine ⟨l28, l33', ?_⟩
    rw [mul_assoc, ← pow_two]
    exact hrd
  · intro k hk
    have := eval k (by simpa [hvl] using hk)
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] using this
  · rw [tb_eq_map_getD hcl]
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, List.length_append, List.length_cons,
      List.length_nil, List.cons.injEq, and_true]
    refine ⟨ecap 0 (by omega), ecap 1 (by omega), ecap 2 (by omega), ecap 3 (by omega),
      ecap 4 (by omega), ?_, q404⟩
    rw [q403, e389]
    ring

end
end LeanVM.Guest.B1.Tables
