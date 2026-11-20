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
# `verify_bus_gkr` is sound

The body (`vbgPre`, the core IR's): the range check of `g_bus_mu = g^depth` (`depth ≤ 32`), the
two roots read and the count asserted nonzero, the combiner drawn from the two roots waiting
(a grind of `0` bits) and the batched claim (`gkr_combine`), the tables `k_mod_next`,
`loop_bounds[d] = g^((d - 1) / 2)`, `depth_odd[d] = g^(d % 2)` and the round records' extent
`rounds_len`, the buffers sized by the depth (`n_quads = loop_bounds[depth]` layer records and
point rows), the root-most layer (`rt_two` at an odd depth, `rt_four` at an even one), the layer
loop `verify_bus_gkr_loop0` (`ly_step`, `ly_chain`), the last layer record (record `n_quads`),
the point's copy to `zeta` (`verify_bus_gkr_loop1`), the trees' values into a buffer of three, and
the return.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `verify_bus_gkr`'s parameters. -/
def vbgParams : List V := (List.range 9).map V.n

/-- `verify_bus_gkr`'s body, the core IR's. -/
noncomputable def vbgBody : List Stmt := (fn% «verify_bus_gkr»).body

/-- `verify_bus_gkr`'s statements before its `ret`. -/
noncomputable def vbgPre : List Stmt := vbgBody.take 307

/-- The radix-four layers' round records (`rounds_len[depth]`, in records of `7` words):
`n² + n + n (1 - depth % 2)` for `n = (depth - 1) / 2`, one at a depth of `0`. -/
def vbgRecs (depth : ℕ) : ℕ :=
  if depth = 0 then 1
  else (depth - 1) / 2 * ((depth - 1) / 2) + (depth - 1) / 2 + (depth - 1) / 2 * (1 - depth % 2)

/-- `verify_bus_gkr`'s returned values. -/
def vbgRets : List V := (List.range 7).map fun k ↦ .n (436 + k)

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
    [(σ (.n 18), dsObserve), (σ (.n 23), dsObserve)]⟩

/-- The trees' roots: push and pull share one, then the count's. -/
def vbgSt0 (σ : Val) : GkrState := ⟨[σ (.n 18), σ (.n 18), σ (.n 23)], []⟩

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **The roots and the combiner**: the two roots read at the cursor, the count nonzero, the
combiner the sponge's challenge with both waiting, the batched claim, the capacity after it, and
the zeros the layers' empty rates read. -/
theorem vbg_root (h : Stmt.HoldsList C rd σ vbgPre True kret) :
    LoadHolds rd (σ (.n 5)) 0 (σ (.n 18)) ∧ LoadHolds rd (σ (.n 5)) 1 (σ (.n 23)) ∧
      σ (.n 23) ≠ 0 ∧ σ (.n 36) = (vbgS1 σ).squeeze.1 ∧
      σ (.n 52) = polyEval (vbgSt0 σ).values (vbgS1 σ).squeeze.1 ∧
      (lyCap 36).map σ = capOf (vbgS1 σ).perm ∧
      σ (.n 32) = 0 ∧ σ (.n 33) = 0 ∧ σ (.n 34) = 0 ∧ σ (.n 35) = 0 := by
  have hnr := vbgPre_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have r0 := tb_holds_slice hnr h 7 (fsNextT (.n 5) 0 18) (by decide +kernel)
  have r1 := tb_holds_slice hnr h 12 (fsNextT (.n 5) 1 23) (by decide +kernel)
  rw [holds_fsNextT] at r0 r1
  obtain ⟨⟨l28, p28⟩, -⟩ := r0
  obtain ⟨⟨l33, p33⟩, -⟩ := r1
  have cp : ∀ k < 5, σ (.n (13 + k)) = σ (.n k) := by
    intro k hk
    have := tb_holds_slice hnr h 2 ((List.range 5).map fun k ↦
      Stmt.atom (.copy (.n (13 + k)) (.n k))) (by decide +kernel)
    rw [tb_holdsList_mapAtoms] at this
    exact this k hk
  have q31 := a 10 (.copy (.n 21) (.n 18)) (by decide +kernel)
  have q32 := a 11 (.copy (.n 22) (.n 18)) (by decide +kernel)
  have q36 := a 15 (.copy (.n 26) (.n 23)) (by decide +kernel)
  have c37 := a 16 (.const (.n 27) (word 0 0)) (by decide +kernel)
  have a38 := a 17 (.add (.n 28) (.n 23) (.n 27)) (by decide +kernel)
  have n38 := a 19 (.assertNe (.n 28) (.n 29) (.n 30)) (by decide +kernel)
  have c42 := a 21 (.const (.n 32) (word 0 0)) (by decide +kernel)
  have c43 := a 22 (.const (.n 33) (word 0 0)) (by decide +kernel)
  have c44 := a 23 (.const (.n 34) (word 0 0)) (by decide +kernel)
  have c45 := a 24 (.const (.n 35) (word 0 0)) (by decide +kernel)
  have k1 := a 25 (.keccak ([.n 19, .n 20, .n 24, .n 25, .n 32, .n 33, .n 34, .n 35] ++
    (List.range 5).map fun k ↦ .n (13 + k)) (lyOuts 36) false false) (by decide +kernel)
  have m59 := a 26 (.mul (.n 49) (.n 36) (.n 26)) (by decide +kernel)
  have a60 := a 27 (.add (.n 50) (.n 22) (.n 49)) (by decide +kernel)
  have m61 := a 28 (.mul (.n 51) (.n 36) (.n 50)) (by decide +kernel)
  have a62 := a 29 (.add (.n 52) (.n 21) (.n 51)) (by decide +kernel)
  simp only [Atom.Holds, tb_word_zero] at q31 q32 q36 c37 a38 n38 c42 c43 c44 c45 m59 a60 m61 a62
  obtain ⟨P, B⟩ := ly_keccak k1
  have hins : (([.n 19, .n 20, .n 24, .n 25, .n 32, .n 33, .n 34, .n 35] ++
      (List.range 5).map fun k ↦ V.n (13 + k)) : List V).map σ =
      rateOf (vbgS1 σ).pend ++ (vbgS1 σ).cap := by
    obtain ⟨e29, e30⟩ := Prod.ext_iff.mp (fsPackT_cells p28)
    obtain ⟨e34, e35⟩ := Prod.ext_iff.mp (fsPackT_cells p33)
    have hcapE : ((List.range 5).map fun k ↦ V.n (13 + k)).map σ =
        [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] := by
      rw [List.map_map, show [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] =
        (List.range 5).map (fun k ↦ σ (.n k)) from rfl]
      exact List.map_congr_left fun k hk => cp k (List.mem_range.mp hk)
    rw [List.map_append, hcapE, rateOf_eq_cells _ (by simp [vbgS1])]
    norm_num at e29 e30 e34 e35
    simp [vbgS1, pendCells, e29, e30, e34, e35, c42, c43, c44, c45]
  rw [hins] at P B
  have e59 : σ (.n 36) = (vbgS1 σ).squeeze.1 := by
    rw [P 0 (by omega)]; exact (Keccak.challengeOf_cells _).symm
  refine ⟨l28, l33, fun h0 => ?_, e59, ?_, B, c42, c43, c44, c45⟩
  · obtain ⟨e40, e1⟩ := n38
    rw [a38, c37, h0, zero_add, zero_mul] at e40
    exact zero_ne_one (e40.symm.trans e1)
  · rw [a62, m61, a60, m59, q31, q32, q36, ← e59]
    simp only [vbgSt0, polyEval, List.foldr]
    ring

/-- **The tables** at `g_bus_mu = g^depth`: `k_mod_next`, `depth_odd[depth] = g^(depth % 2)` and
`n_quads = loop_bounds[depth] = g^((depth - 1) / 2)`, and the loop's `start_g = g^(2 - depth % 2)`. -/
theorem vbg_tables (h : Stmt.HoldsList C rd σ vbgPre True kret) {depth : ℕ}
    (hg : σ (.n 6) = gen ^ depth) (hd : depth < 33) :
    KModNext rd (σ (.n 53)) ∧ σ (.n 187) = gen ^ (depth % 2) ∧
      σ (.n 165) = gen ^ ((depth - 1) / 2) ∧ σ (.n 417) = gen ^ (2 - depth % 2) := by
  have hnr := vbgPre_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have hk := tb_holds_slice hnr h 31 ((List.range 4).map fun r ↦
    [Stmt.atom (.const (.n (54 + 2 * r)) (word (2 ^ ((r + 1) % 4)) 0)),
      .atom (.load (.n (54 + 2 * r)) (.n 53) r),
      .atom (.const (.n (55 + 2 * r)) (word (2 ^ ((r + 1) / 4)) 0)),
      .atom (.load (.n (55 + 2 * r)) (.n 53) (4 + r))]).flatten (by decide +kernel)
  rw [tb_holdsList_flatten_range _ _ (fun _ => rfl)] at hk
  have ht := tb_holds_slice hnr h 49 (((List.range 33).map fun d ↦
    [Stmt.atom (.const (.n (64 + 2 * d)) (word (2 ^ ((d - 1) / 2)) 0)),
      .atom (.load (.n (64 + 2 * d)) (.n 62) d),
      .atom (.const (.n (65 + 2 * d)) (word (2 ^ (d % 2)) 0)),
      .atom (.load (.n (65 + 2 * d)) (.n 63) d)]).flatten) (by decide +kernel)
  rw [tb_holdsList_flatten_range _ _ (fun _ => rfl)] at ht
  have hdt := ht depth hd
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hdt
  obtain ⟨c0, l0, c1, l1⟩ := hdt
  rw [c0, tb_word_two_pow (by omega)] at l0
  rw [c1, tb_word_two_pow (by omega)] at l1
  have m164 := a 248 (.mul (.n 164) (.n 62) (.n 6)) (by decide +kernel)
  have l165 := a 249 (.load (.n 165) (.n 164) 0) (by decide +kernel)
  have m186 := a 270 (.mul (.n 186) (.n 63) (.n 6)) (by decide +kernel)
  have l187 := a 271 (.load (.n 187) (.n 186) 0) (by decide +kernel)
  have c416 := a 275 (.const (.n 416) (word 4 0)) (by decide +kernel)
  have m416 := a 276 (.mul (.n 416) (.n 417) (.n 187)) (by decide +kernel)
  simp only [Atom.Holds] at m164 l165 m186 l187 c416 m416
  rw [m164, hg, tb_loadHolds_mul_gen_pow, Nat.add_zero] at l165
  rw [m186, hg, tb_loadHolds_mul_gen_pow, Nat.add_zero] at l187
  have e187 := tb_loadHolds_unique l187 l1
  refine ⟨fun r hr => ?_, e187, tb_loadHolds_unique l165 l0, ?_⟩
  · have := hk r hr
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
    obtain ⟨c0, l0, c1, l1⟩ := this
    rw [c0, tb_word_two_pow (by omega)] at l0
    rw [c1, tb_word_two_pow (by omega)] at l1
    exact ⟨l1, l0⟩
  · rw [show (4 : ℕ) = 2 ^ 2 by norm_num, tb_word_two_pow (by norm_num)] at c416
    rw [c416, e187] at m416
    have hsh : depth % 2 ≤ 2 := by omega
    have hne : (gen : E) ^ (depth % 2) ≠ 0 := pow_ne_zero _ gen_ne_zero
    apply mul_right_cancel₀ hne
    rw [← m416, ← pow_add, Nat.sub_add_cancel hsh]

end Sem

/-- **The walk**: from the sponge the roots wait in, the root-most layer and the layer loop run
`gkrLayers depth` to the layer record of `L = depth` (record `(depth - 1) / 2`), nothing waiting. -/
theorem vbg_walk (hGR : tb_gkr_rounds_Spec) {rd : Reader} {σ : Val} {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbgPre True kret) {depth : ℕ}
    (hg : σ (.n 6) = gen ^ depth) (hd : depth < 33) (hd0 : depth ≠ 0) :
    ∃ (xs : List E) (st : GkrState) (s : Fs) (row pos half par : E),
      RunsTo (gkrLayers depth (vbgSt0 σ)) (vbgS1 σ) xs st s ∧
      TbReadsAt rd (σ (.n 5) * gen ^ 2) xs ∧
      GkSlot rd (σ (.n 173)) depth s (σ (.n 5) * gen ^ 2 * gen ^ xs.length) st row pos half par := by
  have hnr := vbgPre_noRet
  have a := fun n a heq => tb_holds_atom hnr h n a heq
  obtain ⟨-, -, -, h59, h63, hcap, z42, z43, z44, z45⟩ := vbg_root h
  obtain ⟨hk, e187, e165, e417⟩ := vbg_tables h hg hd
  -- the layer loop's iterations
  have c418 := a 277 (.const (.n 418) (word 1 0)) (by decide +kernel)
  have a419 := a 278 (.add (.n 419) (.n 418) (.n 165)) (by decide +kernel)
  have c420 := a 279 (.const (.n 420) (word 1 0)) (by decide +kernel)
  simp only [Atom.Holds, tb_word_one] at c418 a419 c420
  obtain ⟨-, h6⟩ := tb_holds_callIf hnr h 280 (.n 419) name% «verify_bus_gkr_loop0»
    [.n 420, .n 165, .n 417, .n 173, .n 8, .n 176, .n 52, .n 187, .n 6, .n 53] (by decide +kernel)
  have hB : ∀ j < (depth - 1) / 2,
      LyB rd (σ (.n 417)) (σ (.n 187)) (σ (.n 173)) (σ (.n 53)) (gen ^ j) := by
    intro j hj
    have hne : σ (.n 419) ≠ 0 := by
      rw [a419, c418, e165]
      intro h0
      have := gen_pow_inj (by omega) (by omega)
        ((e_add_eq_zero_iff.mp h0).symm.trans (pow_zero gen).symm)
      omega
    have hrel := h6 hne
    simp only [List.map_cons, List.map_nil, c420] at hrel
    rw [← pow_zero gen] at hrel
    obtain ⟨m', -, hN, hall⟩ := tb_loop_sound
      (B := LyB rd (σ (.n 417)) (σ (.n 187)) (σ (.n 173)) (σ (.n 53)))
      (fun d x hx => ly_step hGR d x hx) 0 hrel
    have hm' : (depth - 1) / 2 ≤ m' := by
      by_contra hc
      have := gen_pow_inj (by omega) (by omega) (e165.symm.trans hN)
      omega
    exact hall j (by omega) (by omega)
  obtain ⟨v0, v1, v2, hv⟩ : ∃ v0 v1 v2, (vbgSt0 σ).values = [v0, v1, v2] := ⟨_, _, _, rfl⟩
  have hi := tb_holds_slice hnr h 274 [.ite (.n 189) rtFour rtTwo] (by decide +kernel)
  simp only [Stmt.HoldsList] at hi
  rw [tb_holds_ite_noRet _ _ _ rtFour_noRet rtTwo_noRet] at hi
  have c188 := a 272 (.const (.n 188) (word 1 0)) (by decide +kernel)
  have a189 := a 273 (.add (.n 189) (.n 187) (.n 188)) (by decide +kernel)
  simp only [Atom.Holds, tb_word_one] at c188 a189
  rcases Nat.mod_two_eq_zero_or_one depth with h2 | h2
  · -- an even depth: the radix-four root layer, then the layers
    obtain ⟨⟨-, hfour, -⟩, -⟩ := hi
    have h0 : σ (.n 189) = 0 := by rw [a189, c188, e187, h2, pow_zero, e_add_self]
    obtain ⟨xs1, st1, s1, hrun1, hrd1, hsl1⟩ := rt_four (hfour h0) rfl rfl h59 h63 hcap
      z42 z43 z44 z45
    have hsl1' : GkSlot rd (σ (.n 173)) (2 - depth % 2) s1 (σ (.n 5) * gen ^ 2 * gen ^ xs1.length)
        st1 (σ (.n 185) * gen ^ 40) 1 (gen ^ ((1 - depth % 2) / 4))
        (gen ^ ((1 - depth % 2) % 4)) := by rw [h2]; simpa using hsl1
    obtain ⟨xs, st, s, pos, hrun, hrd, hsl⟩ := ly_chain hk (sh := depth % 2) e417 e187 (by omega)
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
    obtain ⟨⟨-, -, htwo⟩, -⟩ := hi
    have hne : σ (.n 189) ≠ 0 := by
      rw [a189, c188, e187, h2, pow_one]
      intro h0
      have := gen_pow_inj (a := 1) (b := 0) (by omega) (by omega)
        ((pow_one gen).trans ((e_add_eq_zero_iff.mp h0).trans (pow_zero gen).symm))
      omega
    obtain ⟨xs1, st1, s1, hrun1, hrd1, hsl1⟩ := rt_two (htwo hne) rfl rfl h59 h63 hcap
      z42 z43 z44 z45
    have hsl1' : GkSlot rd (σ (.n 173)) (2 - depth % 2) s1 (σ (.n 5) * gen ^ 2 * gen ^ xs1.length)
        st1 (σ (.n 185) * gen ^ 40) 1 (gen ^ ((1 - depth % 2) / 4))
        (gen ^ ((1 - depth % 2) % 4)) := by rw [h2]; simpa using hsl1
    obtain ⟨xs, st, s, pos, hrun, hrd, hsl⟩ := ly_chain hk (sh := depth % 2) e417 e187 (by omega)
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
  have hrets : rets = [σ (.n 436), σ (.n 437), σ (.n 438), σ (.n 439), σ (.n 440), σ (.n 441),
      σ (.n 442)] := by rw [← hret]; rfl
  subst hargs hrets
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hne
  have hnr := vbgPre_noRet
  have a := fun n a heq => tb_holds_atom hnr h n a heq
  -- the depth
  have c9 := a 0 (.const (.n 9) (word 4294967296 0)) (by decide +kernel)
  have rc := a 1 (.rangeCheck (.n 6) (.n 10) (.n 11) (.n 12) (.n 9)) (by decide +kernel)
  simp only [Atom.Holds] at c9 rc
  obtain ⟨depth, hd, hg⟩ := tb_rc_sound' hμ Lm (K := 33) (by omega) (by norm_num)
    (by rw [c9, show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num),
      gen_pow_eq_ofK]) rc.1 rc.2.1 rc.2.2
  have hd0 : depth ≠ 0 := by rintro rfl; exact hne (by rw [hg, pow_zero])
  -- the roots and the walk
  obtain ⟨l28, l33, hcnt, -⟩ := vbg_root h
  obtain ⟨-, -, e165, -⟩ := vbg_tables h hg hd
  obtain ⟨xs, st, s, row, pos, half, par, hrun, hrd, hsl⟩ := vbg_walk hGR h hg hd hd0
  obtain ⟨hcl, hcap, hpe, hcur, hvl, hval, hrow, hpl, hpt, -, -, -⟩ := hsl
  -- the final layer record
  have m421 := a 281 (.mul (.n 421) (.n 165) (.n 165)) (by decide +kernel)
  have m422 := a 282 (.mul (.n 422) (.n 421) (.n 165)) (by decide +kernel)
  have m423 := a 283 (.mul (.n 423) (.n 422) (.n 422)) (by decide +kernel)
  have m424 := a 284 (.mul (.n 424) (.n 423) (.n 423)) (by decide +kernel)
  have m425 := a 285 (.mul (.n 425) (.n 424) (.n 165)) (by decide +kernel)
  have m426 := a 286 (.mul (.n 426) (.n 173) (.n 425)) (by decide +kernel)
  have l427 := a 287 (.load (.n 427) (.n 426) 5) (by decide +kernel)
  have l428 := a 288 (.load (.n 428) (.n 426) 9) (by decide +kernel)
  have c429 := a 289 (.const (.n 429) (word 1 0)) (by decide +kernel)
  have a430 := a 290 (.add (.n 430) (.n 429) (.n 6)) (by decide +kernel)
  have c431 := a 291 (.const (.n 431) (word 1 0)) (by decide +kernel)
  have q441 := a 305 (.copy (.n 441) (.n 427)) (by decide +kernel)
  have q442 := a 306 (.copy (.n 442) (.n 432)) (by decide +kernel)
  simp only [Atom.Holds] at m421 m422 m423 m424 m425 m426 l427 l428 c429 a430 c431 q441 q442
  rw [tb_word_one] at c429 c431
  have e426 : σ (.n 426) = σ (.n 173) * gen ^ (13 * ((depth - 1) / 2)) := by
    rw [m426, m425, m424, m423, m422, m421, e165]
    ring
  have ld : ∀ k w, LoadHolds Lm.read (σ (.n 426)) k w →
      LoadHolds Lm.read (σ (.n 173)) (13 * ((depth - 1) / 2) + k) w := fun k w hw => by
    rw [e426, tb_loadHolds_mul_gen_pow] at hw; exact hw
  have hcs := tb_holds_slice hnr h 300 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (436 + k)) (.n 426) k)) (by decide +kernel)
  have hvs := tb_holds_slice hnr h 294 ((List.range 3).map fun k ↦
    [Stmt.atom (.load (.n (433 + k)) (.n 426) (6 + k)),
      .atom (.load (.n (433 + k)) (.n 432) k)]).flatten (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hcs
  rw [tb_holdsList_flatten_range _ _ (fun _ => rfl)] at hvs
  simp only [Atom.Holds] at hcs
  have ecap : ∀ k < 5, σ (.n (436 + k)) = s.cap.getD k 0 := fun k hk =>
    tb_loadHolds_unique (ld _ _ (hcs k hk)) (hcap k hk)
  have eval : ∀ k < 3, LoadHolds Lm.read (σ (.n 432)) k (st.values.getD k 0) := by
    intro k hk
    have := hvs k hk
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
    obtain ⟨l1, l2⟩ := this
    have e := tb_loadHolds_unique (by have := ld _ _ l1; rwa [← Nat.add_assoc] at this) (hval k hk)
    rw [e] at l2
    exact l2
  have e389 := tb_loadHolds_unique (ld _ _ l427) hcur
  have e390 := tb_loadHolds_unique (ld _ _ l428) hrow
  -- the point's copy
  obtain ⟨-, h7⟩ := tb_holds_callIf hnr h 292 (.n 430) name% «verify_bus_gkr_loop1» [.n 431, .n 6,
      .n 7, .n 428]
    (by decide +kernel)
  have hne7 : σ (.n 430) ≠ 0 := by
    rw [a430, c429, hg]
    intro h0
    have := gen_pow_inj (by omega) (by omega)
      ((e_add_eq_zero_iff.mp h0).symm.trans (pow_zero gen).symm)
    omega
  have hrel7 := h7 hne7
  simp only [List.map_cons, List.map_nil, c431, e390] at hrel7
  have hz := l8_loop hg (by omega) (by omega) hrel7 hpl hpt
  -- the specification's run
  have hs : s = ⟨s.cap, []⟩ := by cases s; simp only at hpe; rw [hpe]
  have r1 := runsTo_readE ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ (σ (.n 18))
  have r2 := runsTo_readE ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)],
    [(σ (.n 18), dsObserve)]⟩ (σ (.n 23))
  have ea1 : (⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).absorb (σ (.n 18))
      dsObserve = ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], [(σ (.n 18), dsObserve)]⟩ := by
    simp [Fs.absorb, rateScalars]
  have ea2 : (⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], [(σ (.n 18), dsObserve)]⟩ :
      Fs).absorb (σ (.n 23)) dsObserve = vbgS1 σ := by
    simp [Fs.absorb, rateScalars, vbgS1]
  rw [ea1] at r1
  rw [ea2] at r2
  have hv : RunsTo (verifyGkrGrandProducts depth)
      ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩
      ([σ (.n 18)] ++ ([σ (.n 23)] ++ (xs ++ []))) (σ (.n 23), st.point, st.values) s :=
    r1.bind (r2.bind (hrun.bind (runsTo_ret _ _)))
  have hph : RunsTo (gkrPhase depth) ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩
      ([σ (.n 18)] ++ ([σ (.n 23)] ++ (xs ++ [])) ++ ([] ++ []))
      (σ (.n 23), st.point, st.values) s :=
    hv.bind ((tb_runsTo_require hcnt s).bind (runsTo_ret _ _))
  rw [hs] at hph
  refine ⟨depth, _, _, s.cap, σ (.n 432), hg, hd, ?_, hph, hpl, hvl, hz, ?_, ?_⟩
  · simp only [List.append_nil, List.singleton_append]
    rw [tbReadsAt_cons, tbReadsAt_cons]
    have l33' := (tb_loadHolds_mul_gen_pow Lm.read (σ (.n 5)) 1 0 (σ (.n 23))).mpr l33
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
      ecap 4 (by omega), ?_, q442⟩
    rw [q441, e389]
    ring

end
end LeanVM.Guest.B1.Tables
