/-
  LeanVM.Guest.B1.Gkr.Root

  `verify_bus_gkr`'s root-most layer: one step of the specification's GKR walk from the roots,
  of one level at an odd depth and of two at an even one, to the layer slot of its point.
-/

module

public import LeanVM.Guest.B1.Gkr.LayerStep
public import LeanVM.Guest.B1.Sumcheck.Run

/-!
# The root-most layer (G:1985-2044)

The root-most layer has no rounds: the combiner, drawn from the two roots waiting in the sponge,
batches the three trees' roots into the claim the children's products check. `verify_bus_gkr`
runs it in its body, in the two arms of an `ite` on `odd_g = g^(depth % 2)`:

* `rt_two` (`Data.core9.s196_e`, an odd depth): two children a tree, `y` one coordinate (its
  grind of `0` bits a permutation of the two waiting), the slot of `L = 1`;
* `rt_four` (`Data.core9.s196_t`, an even depth): four children a tree, `y` two coordinates, the
  slot of `L = 2`.

Both start from the body's combiner `σ 59`, the claim `σ 63`, the sponge's capacity after the
combiner `σ 54 .. σ 58` and the zeros `σ 42 .. σ 45`, the cursor past the roots at `σ 5·g^2`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The binary root layer, the `ite`'s else arm. -/
noncomputable def rtTwo : List Stmt := Data.core9.s196_e

/-- The radix-four root layer, the `ite`'s then arm. -/
noncomputable def rtFour : List Stmt := Data.core9.s196_t

theorem rtTwo_noRet : Stmt.noRetList rtTwo = true := by decide +kernel

theorem rtFour_noRet : Stmt.noRetList rtFour = true := by decide +kernel

/-- Child `i`'s read's first statement in a root arm. -/
def rtPos (i : ℕ) : ℕ := 4 * i + i / 4

theorem rtTwo_check : ∀ i < 6,
    tbStmtsEqb (chT (.n 5) 2 297 i) ((rtTwo.drop (rtPos i)).take (chT (.n 5) 2 297 i).length) =
      true := by
  decide +kernel

theorem rtFour_check : ∀ i < 12,
    tbStmtsEqb (chT (.n 5) 2 145 i) ((rtFour.drop (rtPos i)).take (chT (.n 5) 2 145 i).length) =
      true := by
  decide +kernel

/-- Absorbing at a full queue: one permutation, then the scalars waiting. -/
theorem tb_absorbAll_full' (s : Fs) (hs : s.pend.length = 4) (xs : List E) (h1 : 0 < xs.length)
    (h4 : xs.length ≤ 4) (t : ℕ) : s.absorbAll xs t = ⟨capOf s.perm, xs.map (·, t)⟩ := by
  match xs, h1 with
  | x :: rest, _ =>
    simp only [Fs.absorbAll, List.foldl_cons]
    have e1 : s.absorb x t = ⟨capOf s.perm, [(x, t)]⟩ := by
      simp [Fs.absorb, hs, rateScalars]
    rw [e1]
    have := absorbAll_short ⟨capOf s.perm, [(x, t)]⟩ rest t (by simp at h4 ⊢; omega)
    simp only [Fs.absorbAll] at this
    rw [this]
    simp

/-- The root-most step's sumcheck: no rounds. -/
theorem rt_sumcheck {st : GkrState} (hpt : st.point = []) (claim : E) (step : ℕ) (s : Fs) :
    RunsTo (sumcheck claim (2 ^ step + 1) (st.point.map some)) s [] ([], claim) s := by
  rw [hpt]
  exact runsTo_ret _ _

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- A read at `p` past the roots is a read at `p·g^2`. -/
theorem rt_read {p w : E} {i : ℕ} (h : LoadHolds rd p (2 + i) w) :
    LoadHolds rd (p * gen ^ 2) i w := by
  rw [tb_loadHolds_mul_gen_pow]; exact h

/-- **The binary root layer** (an odd depth): from the sponge `s` the roots wait in, one step of
one level to the slot of `L = 1`, the cursor past the roots `σ 5·g^2`. -/
theorem rt_two (h : Stmt.HoldsList C rd σ rtTwo True kret) {s : Fs} {st : GkrState}
    (hpt : st.point = []) (hvl : st.values.length = 3)
    (h59 : σ (.n 59) = s.squeeze.1) (h63 : σ (.n 63) = polyEval st.values s.squeeze.1)
    (hcap : (lyCap 46).map σ = capOf s.perm)
    (z42 : σ (.n 42) = 0) (z43 : σ (.n 43) = 0) (z44 : σ (.n 44) = 0) (z45 : σ (.n 45) = 0) :
    ∃ (xs : List E) (st' : GkrState) (s' : Fs), RunsTo (gkrStep 1 false st) s xs st' s' ∧
      TbReadsAt rd (σ (.n 5) * gen ^ 2) xs ∧
      GkSlot rd (σ (.n 16)) 1 s' (σ (.n 5) * gen ^ 2 * gen ^ xs.length) st'
        (σ (.n 18) * gen ^ 40) gen 1 1 := by
  have hnr := rtTwo_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have EV : ∀ i < 6, _ := fun i hi => ch_ev (tb_holds_slice hnr h (rtPos i) (chT (.n 5) 2 297 i)
    (rtTwo_check i hi))
  have hp : ∀ i < 6, FsPackOk σ (.n (chB 297 i)) (chB 297 i + 1) dsObserve :=
    fun i hi => (EV i hi).2.1
  have cp : ∀ i < 6, σ (.n (chB 297 i + 3)) = σ (.n (chB 297 i)) := fun i hi => (EV i hi).2.2
  set w0 := σ (.n 297)
  set w1 := σ (.n 301)
  set w2 := σ (.n 305)
  set w3 := σ (.n 309)
  set w4 := σ (.n 326)
  set w5 := σ (.n 330)
  have q0 : σ (.n 300) = w0 := cp 0 (by omega)
  have q1 : σ (.n 304) = w1 := cp 1 (by omega)
  have q2 : σ (.n 308) = w2 := cp 2 (by omega)
  have q3 : σ (.n 312) = w3 := cp 3 (by omega)
  have q4 : σ (.n 329) = w4 := cp 4 (by omega)
  have q5 : σ (.n 333) = w5 := cp 5 (by omega)
  -- the sponge: four children, a permutation, two waiting, `y`'s permutation
  have k1 := a 16 (.keccak (chRate 297 0 ++ lyCap 46) (lyOuts 313) false false) (by decide +kernel)
  obtain ⟨-, B0⟩ := ch_perm_block (fun i hi => hp i (by omega)) k1
  rw [hcap] at B0
  have k2 := a 36 (.keccak ([.n 327, .n 328, .n 331, .n 332, .n 42, .n 43, .n 44, .n 45] ++
    lyCap 313) (lyOuts 344) false false) (by decide +kernel)
  obtain ⟨P2, B2⟩ := ly_keccak k2
  have hr2 : (([.n 327, .n 328, .n 331, .n 332, .n 42, .n 43, .n 44, .n 45] ++ lyCap 313 :
      List V).map σ) = rateOf [(w4, dsObserve), (w5, dsObserve)] ++ (lyCap 313).map σ := by
    have hr := ch_rate (n := 2) (ws := fun i ↦ chB 297 (4 + i)) (fun i hi => hp (4 + i) (by omega))
    simp only [List.range_succ, List.range_zero, List.flatMap_cons, List.flatMap_nil,
      List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_nil, chB] at hr
    rw [List.map_append, rateOf_eq_cells _ (by simp)]
    simp only [List.map_cons, List.map_nil, z42, z43, z44, z45, List.cons_append,
      List.nil_append] at hr ⊢
    rw [show [σ (.n 327), σ (.n 328), σ (.n 331), σ (.n 332)] = pendCells
      [(w4, dsObserve), (w5, dsObserve)] from hr]
    simp [pendCells]
  rw [hr2] at P2 B2
  have c357 := a 37 (.copy (.n 357) (.n 344)) (by decide +kernel)
  simp only [Atom.Holds] at c357
  -- the check
  obtain ⟨v0, v1, v2, hv3⟩ : ∃ v0 v1 v2, st.values = [v0, v1, v2] := by
    match st.values, hvl with
    | [v0, v1, v2], _ => exact ⟨v0, v1, v2, rfl⟩
  have hcheck : polyEval st.values s.squeeze.1 =
      polyEval [prodE [w0, w1], prodE [w2, w3], prodE [w4, w5]] s.squeeze.1 := by
    have m334 := a 25 (.mul (.n 334) (.n 329) (.n 333)) (by decide +kernel)
    have c335 := a 26 (.const (.n 335) (word 0 0)) (by decide +kernel)
    have m336 := a 27 (.mul (.n 336) (.n 59) (.n 335)) (by decide +kernel)
    have a337 := a 28 (.add (.n 337) (.n 334) (.n 336)) (by decide +kernel)
    have m338 := a 29 (.mul (.n 338) (.n 308) (.n 312)) (by decide +kernel)
    have m339 := a 30 (.mul (.n 339) (.n 59) (.n 337)) (by decide +kernel)
    have a340 := a 31 (.add (.n 340) (.n 338) (.n 339)) (by decide +kernel)
    have m341 := a 32 (.mul (.n 341) (.n 300) (.n 304)) (by decide +kernel)
    have m342 := a 33 (.mul (.n 342) (.n 59) (.n 340)) (by decide +kernel)
    have a343 := a 34 (.add (.n 343) (.n 341) (.n 342)) (by decide +kernel)
    have q := a 35 (.assertEq (.n 63) (.n 343)) (by decide +kernel)
    simp only [Atom.Holds, tb_word_zero] at m334 c335 m336 a337 m338 m339 a340 m341 m342 a343 q
    have q' := e_add_eq_zero_iff.mp q
    rw [h63, a343, m342, a340, m339, a337, m336, c335, m334, m338, m341, q0, q1, q2, q3, q4, q5,
      h59] at q'
    rw [q']
    simp only [polyEval, prodE, List.foldr, List.foldl]
    ring
  have hstep := gkrStep_run (step := 1) (by norm_num) false (ch0 := [w0, w1]) (ch1 := [w2, w3])
    (ch2 := [w4, w5]) (rt_sumcheck hpt _ 1 s.squeeze.2) rfl rfl rfl hcheck
  have hA0 : s.squeeze.2.absorbAll [w0, w1] dsObserve =
      ⟨capOf s.perm, [(w0, dsObserve), (w1, dsObserve)]⟩ := by
    rw [absorbAll_short _ _ _ (by simp [Fs.squeeze])]
    rfl
  have hA1 : (⟨capOf s.perm, [(w0, dsObserve), (w1, dsObserve)]⟩ : Fs).absorbAll [w2, w3]
      dsObserve = ⟨capOf s.perm, [(w0, dsObserve), (w1, dsObserve), (w2, dsObserve),
        (w3, dsObserve)]⟩ := by
    rw [absorbAll_short _ _ _ (by simp)]
    rfl
  have hB0 : (lyCap 313).map σ = capOf (Fs.perm ⟨capOf s.perm,
      [(w0, dsObserve), (w1, dsObserve), (w2, dsObserve), (w3, dsObserve)]⟩) := by
    rw [B0]; rfl
  have hA2 : (⟨capOf s.perm, [(w0, dsObserve), (w1, dsObserve), (w2, dsObserve),
      (w3, dsObserve)]⟩ : Fs).absorbAll [w4, w5] dsObserve =
      ⟨(lyCap 313).map σ, [(w4, dsObserve), (w5, dsObserve)]⟩ := by
    rw [tb_absorbAll_full' _ (by simp) _ (by simp) (by simp), hB0]
    rfl
  rw [hA0, hA1, hA2] at hstep
  have hsq1 : ((⟨(lyCap 313).map σ, [(w4, dsObserve), (w5, dsObserve)]⟩ : Fs).squeezeN 1).1 =
      [σ (.n 357)] := by
    rw [c357, P2 0 (by omega), ← challengeOf_cells]; rfl
  have hsq2 : ((⟨(lyCap 313).map σ, [(w4, dsObserve), (w5, dsObserve)]⟩ : Fs).squeezeN 1).2 =
      ⟨(lyCap 344).map σ, []⟩ := by rw [B2]; rfl
  rw [hsq1, hsq2] at hstep
  refine ⟨_, _, _, hstep, ?_, ?_⟩
  · intro k hk
    simp only [List.nil_append, List.cons_append, List.length_cons, List.length_nil] at hk
    apply rt_read
    interval_cases k
    · exact (EV 0 (by omega)).1
    · exact (EV 1 (by omega)).1
    · exact (EV 2 (by omega)).1
    · exact (EV 3 (by omega)).1
    · exact (EV 4 (by omega)).1
    · exact (EV 5 (by omega)).1
  -- the slot of `L = 1`
  have hcs := tb_holds_slice hnr h 39 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (352 + k)) (.n 16) (13 + k))) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hcs
  simp only [Atom.Holds] at hcs
  have l357 := a 38 (.load (.n 357) (.n 18) 40) (by decide +kernel)
  have c358 := a 44 (.const (.n 358) (word 256 0)) (by decide +kernel)
  have m359 := a 45 (.mul (.n 359) (.n 5) (.n 358)) (by decide +kernel)
  have l359 := a 46 (.load (.n 359) (.n 16) 18) (by decide +kernel)
  have c369 := a 59 (.const (.n 369) (word 1099511627776 0)) (by decide +kernel)
  have m370 := a 60 (.mul (.n 370) (.n 18) (.n 369)) (by decide +kernel)
  have l370 := a 61 (.load (.n 370) (.n 16) 22) (by decide +kernel)
  have c371 := a 62 (.const (.n 371) (word 2 0)) (by decide +kernel)
  have l371 := a 63 (.load (.n 371) (.n 16) 23) (by decide +kernel)
  have c372 := a 64 (.const (.n 372) (word 1 0)) (by decide +kernel)
  have l372 := a 65 (.load (.n 372) (.n 16) 24) (by decide +kernel)
  have c373 := a 66 (.const (.n 373) (word 1 0)) (by decide +kernel)
  have l373 := a 67 (.load (.n 373) (.n 16) 25) (by decide +kernel)
  simp only [Atom.Holds] at l357 c358 m359 l359 c369 m370 l370 c371 l371 c372 l372 c373 l373
  rw [tb_word_gen] at c371
  rw [tb_word_one] at c372 c373
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num, tb_word_two_pow (by norm_num)] at c358
  rw [show (1099511627776 : ℕ) = 2 ^ 40 by norm_num, tb_word_two_pow (by norm_num)] at c369
  have VAL : ∀ t < 3, ∀ b u v off : ℕ, Stmt.HoldsList C rd σ
      [.atom (.add (.n b) (.n u) (.n v)), .atom (.mul (.n (b + 1)) (.n 357) (.n b)),
        .atom (.add (.n (b + 2)) (.n u) (.n (b + 1))), .atom (.load (.n (b + 2)) (.n 16) off)]
      True kret → LoadHolds rd (σ (.n 16)) off (σ (.n u) + σ (.n 357) * (σ (.n u) + σ (.n v))) := by
    intro t _ b u v off hv
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hv
    obtain ⟨e0, e1, e2, l⟩ := hv
    rw [e2, e1, e0] at l
    exact l
  have V0 := VAL 0 (by omega) 360 300 304 19 (tb_holds_slice hnr h 47 _ (by decide +kernel))
  have V1 := VAL 1 (by omega) 363 308 312 20 (tb_holds_slice hnr h 51 _ (by decide +kernel))
  have V2 := VAL 2 (by omega) 366 329 333 21 (tb_holds_slice hnr h 55 _ (by decide +kernel))
  rw [q0, q1] at V0
  rw [q2, q3] at V1
  rw [q4, q5] at V2
  refine ⟨by simp [lyCap], fun k hk => ?_, rfl, ?_, by simp, fun t ht => ?_, ?_, by simp, ?_,
    ?_, ?_, ?_⟩
  · have hg : ((lyCap 344).map σ).getD k 0 = σ (.n (352 + k)) := by
      simp [lyCap, List.getD_eq_getElem?_getD, hk]
    rw [hg, show 13 * 1 + k = 13 + k by ring]
    exact hcs k hk
  · rw [m359, c358] at l359
    rw [show σ (.n 5) * gen ^ 2 * gen ^ (([w0, w1] ++ ([w2, w3] ++ [w4, w5])).length) =
      σ (.n 5) * gen ^ 8 by simp only [List.length_append, List.length_cons, List.length_nil]; ring]
    exact l359
  · rw [show 13 * 1 + 6 + t = 19 + t by ring]
    interval_cases t
    · convert V0 using 1; simp [multilinearEval, foldPairs]
    · convert V1 using 1; simp [multilinearEval, foldPairs]
    · convert V2 using 1; simp [multilinearEval, foldPairs]
  · rw [m370, c369] at l370
    exact l370
  · simp only [List.append_nil]
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    obtain rfl : k = 0 := by omega
    rw [tb_loadHolds_mul_gen_pow]
    exact l357
  · rw [c371] at l371; exact l371
  · rw [c372] at l372; exact l372
  · rw [c373] at l373; exact l373

/-- **The radix-four root layer** (an even depth): from the sponge `s` the roots wait in, one
step of two levels to the slot of `L = 2`, the cursor past the roots `σ 5·g^2`. -/
theorem rt_four (h : Stmt.HoldsList C rd σ rtFour True kret) {s : Fs} {st : GkrState}
    (hpt : st.point = []) (hvl : st.values.length = 3)
    (h59 : σ (.n 59) = s.squeeze.1) (h63 : σ (.n 63) = polyEval st.values s.squeeze.1)
    (hcap : (lyCap 46).map σ = capOf s.perm)
    (z42 : σ (.n 42) = 0) (z43 : σ (.n 43) = 0) (z44 : σ (.n 44) = 0) (z45 : σ (.n 45) = 0) :
    ∃ (xs : List E) (st' : GkrState) (s' : Fs), RunsTo (gkrStep 2 false st) s xs st' s' ∧
      TbReadsAt rd (σ (.n 5) * gen ^ 2) xs ∧
      GkSlot rd (σ (.n 16)) 2 s' (σ (.n 5) * gen ^ 2 * gen ^ xs.length) st'
        (σ (.n 18) * gen ^ 40) gen 1 gen := by
  have hnr := rtFour_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have EV : ∀ i < 12, _ := fun i hi => ch_ev (tb_holds_slice hnr h (rtPos i) (chT (.n 5) 2 145 i)
    (rtFour_check i hi))
  have hp : ∀ i < 12, FsPackOk σ (.n (chB 145 i)) (chB 145 i + 1) dsObserve :=
    fun i hi => (EV i hi).2.1
  have cp : ∀ i < 12, σ (.n (chB 145 i + 3)) = σ (.n (chB 145 i)) := fun i hi => (EV i hi).2.2
  set W := chWords σ 145 with hW
  -- the sponge: three blocks of four children, then `y`'s two permutations
  have k1 := a 16 (.keccak (chRate 145 0 ++ lyCap 46) (lyOuts 161) false false) (by decide +kernel)
  obtain ⟨-, B0⟩ := ch_perm_block (fun i hi => hp i (by omega)) k1
  rw [hcap] at B0
  have k2 := a 33 (.keccak (chRate 145 1 ++ lyCap 161) (lyOuts 190) false false) (by decide +kernel)
  obtain ⟨-, B1⟩ := ch_perm_block (fun i hi => hp (4 + i) (by omega)) k2
  have k3 := a 67 (.keccak (chRate 145 2 ++ lyCap 190) (lyOuts 235) false false) (by decide +kernel)
  obtain ⟨P2, B2⟩ := ch_perm_block (fun i hi => hp (8 + i) (by omega)) k3
  set sp : Fs := ((s.squeeze.2.absorbAll (W 0) dsObserve).absorbAll (W 1) dsObserve).absorbAll
    (W 2) dsObserve with hsp
  have hA : sp = ⟨(lyCap 190).map σ, (W 2).map (·, dsObserve)⟩ := by
    rw [hsp]
    have A0 : s.squeeze.2.absorbAll (W 0) dsObserve = ⟨capOf s.perm, (W 0).map (·, dsObserve)⟩ := by
      rw [absorbAll_short _ _ _ (by simp [Fs.squeeze, hW, chWords_length])]
      simp [Fs.squeeze]
    rw [A0, tb_absorbAll_full _ (by simp [hW, chWords_length]) _ (chWords_length σ 145 1),
      show capOf (Fs.perm ⟨capOf s.perm, (W 0).map (·, dsObserve)⟩) = (lyCap 161).map σ by
        rw [B0]; rfl,
      tb_absorbAll_full _ (by simp [hW, chWords_length]) _ (chWords_length σ 145 2), ← B1]
  rw [← hA] at P2 B2
  have c248 := a 68 (.copy (.n 248) (.n 235)) (by decide +kernel)
  simp only [Atom.Holds] at c248
  have k4 := a 69 (.keccak ([.n 42, .n 42, .n 42, .n 42, .n 42, .n 43, .n 44, .n 45] ++
    lyCap 235) (lyOuts 249) false false) (by decide +kernel)
  obtain ⟨P3, B3⟩ := ly_keccak k4
  rw [ly_zero_rate z42 z43 z44 z45, B2] at P3 B3
  have c262 := a 70 (.copy (.n 262) (.n 249)) (by decide +kernel)
  simp only [Atom.Holds] at c262
  have hsq1 : (sp.squeezeN 2).1 = [σ (.n 248), σ (.n 262)] := by
    rw [c248, c262, P2 0 (by omega), P3 0 (by omega), ← challengeOf_cells, ← challengeOf_cells]
    rfl
  have hsq2 : (sp.squeezeN 2).2 = ⟨(lyCap 249).map σ, []⟩ := by
    rw [B3]; rfl
  -- the check
  obtain ⟨v0, v1, v2, hv3⟩ : ∃ v0 v1 v2, st.values = [v0, v1, v2] := by
    match st.values, hvl with
    | [v0, v1, v2], _ => exact ⟨v0, v1, v2, rfl⟩
  have hcheck : polyEval st.values s.squeeze.1 =
      polyEval [prodE (W 0), prodE (W 1), prodE (W 2)] s.squeeze.1 := by
    have m219 := a 50 (.mul (.n 219) (.n 206) (.n 210)) (by decide +kernel)
    have m220 := a 51 (.mul (.n 220) (.n 219) (.n 214)) (by decide +kernel)
    have m221 := a 52 (.mul (.n 221) (.n 220) (.n 218)) (by decide +kernel)
    have c222 := a 53 (.const (.n 222) (word 0 0)) (by decide +kernel)
    have m223 := a 54 (.mul (.n 223) (.n 59) (.n 222)) (by decide +kernel)
    have a224 := a 55 (.add (.n 224) (.n 221) (.n 223)) (by decide +kernel)
    have m225 := a 56 (.mul (.n 225) (.n 177) (.n 181)) (by decide +kernel)
    have m226 := a 57 (.mul (.n 226) (.n 225) (.n 185)) (by decide +kernel)
    have m227 := a 58 (.mul (.n 227) (.n 226) (.n 189)) (by decide +kernel)
    have m228 := a 59 (.mul (.n 228) (.n 59) (.n 224)) (by decide +kernel)
    have a229 := a 60 (.add (.n 229) (.n 227) (.n 228)) (by decide +kernel)
    have m230 := a 61 (.mul (.n 230) (.n 148) (.n 152)) (by decide +kernel)
    have m231 := a 62 (.mul (.n 231) (.n 230) (.n 156)) (by decide +kernel)
    have m232 := a 63 (.mul (.n 232) (.n 231) (.n 160)) (by decide +kernel)
    have m233 := a 64 (.mul (.n 233) (.n 59) (.n 229)) (by decide +kernel)
    have a234 := a 65 (.add (.n 234) (.n 232) (.n 233)) (by decide +kernel)
    have q := a 66 (.assertEq (.n 63) (.n 234)) (by decide +kernel)
    simp only [Atom.Holds, tb_word_zero] at m219 m220 m221 c222 m223 a224 m225 m226 m227 m228
    simp only [Atom.Holds] at a229 m230 m231 m232 m233 a234 q
    have q' := e_add_eq_zero_iff.mp q
    rw [h63, a234, m233, a229, m228, a224, m223, c222, m221, m220, m219, m227, m226, m225, m232,
      m231, m230, h59,
      show σ (.n 148) = σ (.n 145) from cp 0 (by omega),
      show σ (.n 152) = σ (.n 149) from cp 1 (by omega),
      show σ (.n 156) = σ (.n 153) from cp 2 (by omega),
      show σ (.n 160) = σ (.n 157) from cp 3 (by omega),
      show σ (.n 177) = σ (.n 174) from cp 4 (by omega),
      show σ (.n 181) = σ (.n 178) from cp 5 (by omega),
      show σ (.n 185) = σ (.n 182) from cp 6 (by omega),
      show σ (.n 189) = σ (.n 186) from cp 7 (by omega),
      show σ (.n 206) = σ (.n 203) from cp 8 (by omega),
      show σ (.n 210) = σ (.n 207) from cp 9 (by omega),
      show σ (.n 214) = σ (.n 211) from cp 10 (by omega),
      show σ (.n 218) = σ (.n 215) from cp 11 (by omega)] at q'
    rw [q', hW, chWords_eq, chWords_eq, chWords_eq]
    simp only [chB, polyEval, prodE, List.foldr, List.foldl]
    ring
  have hstep := gkrStep_run (step := 2) le_rfl false (rt_sumcheck hpt _ 2 s.squeeze.2)
    (chWords_length σ 145 0) (chWords_length σ 145 1) (chWords_length σ 145 2) hcheck
  rw [show ((s.squeeze.2.absorbAll (chWords σ 145 0) dsObserve).absorbAll (chWords σ 145 1)
    dsObserve).absorbAll (chWords σ 145 2) dsObserve = sp from rfl, hsq1, hsq2] at hstep
  refine ⟨_, _, _, hstep, ?_, ?_⟩
  · intro k hk
    have hk12 : k < 12 := by simpa [chWords_length] using hk
    apply rt_read
    convert (EV k hk12).1 using 1
    simp only [List.nil_append, chWords_eq]
    interval_cases k <;> rfl
  -- the slot of `L = 2`
  have hcs := tb_holds_slice hnr h 73 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (257 + k)) (.n 16) (26 + k))) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hcs
  simp only [Atom.Holds] at hcs
  have l248 := a 71 (.load (.n 248) (.n 18) 40) (by decide +kernel)
  have l262 := a 72 (.load (.n 262) (.n 18) 41) (by decide +kernel)
  have c263 := a 78 (.const (.n 263) (word 16384 0)) (by decide +kernel)
  have m264 := a 79 (.mul (.n 264) (.n 5) (.n 263)) (by decide +kernel)
  have l264 := a 80 (.load (.n 264) (.n 16) 31) (by decide +kernel)
  have c292 := a 111 (.const (.n 292) (word 1099511627776 0)) (by decide +kernel)
  have m293 := a 112 (.mul (.n 293) (.n 18) (.n 292)) (by decide +kernel)
  have l293 := a 113 (.load (.n 293) (.n 16) 35) (by decide +kernel)
  have c294 := a 114 (.const (.n 294) (word 2 0)) (by decide +kernel)
  have l294 := a 115 (.load (.n 294) (.n 16) 36) (by decide +kernel)
  have c295 := a 116 (.const (.n 295) (word 1 0)) (by decide +kernel)
  have l295 := a 117 (.load (.n 295) (.n 16) 37) (by decide +kernel)
  have c296 := a 118 (.const (.n 296) (word 2 0)) (by decide +kernel)
  have l296 := a 119 (.load (.n 296) (.n 16) 38) (by decide +kernel)
  simp only [Atom.Holds] at l248 l262 c263 m264 l264 c292 m293 l293 c294 l294 c295 l295 c296 l296
  rw [tb_word_gen] at c294 c296
  rw [tb_word_one] at c295
  rw [show (16384 : ℕ) = 2 ^ 14 by norm_num, tb_word_two_pow (by norm_num)] at c263
  rw [show (1099511627776 : ℕ) = 2 ^ 40 by norm_num, tb_word_two_pow (by norm_num)] at c292
  have VAL : ∀ b off t, (b = 265 + 9 * t) → t < 3 →
      Stmt.HoldsList C rd σ (chValT 145 248 262 16 t b off) True kret →
      LoadHolds rd (σ (.n 16)) off (multilinearEval (W t) [σ (.n 248), σ (.n 262)]) := by
    intro b off t hb ht hv
    obtain ⟨ev, l⟩ := ch_val hv
    rw [ev] at l
    convert l using 1
    rw [hW, chWords_eq]
    interval_cases t <;>
    · simp only [chB, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv]
      rw [cp _ (by omega), cp _ (by omega), cp _ (by omega), cp _ (by omega)]
  refine ⟨by simp [lyCap], fun k hk => ?_, rfl, ?_, by simp, fun t ht => ?_, ?_, by simp, ?_,
    ?_, ?_, ?_⟩
  · have hg : ((lyCap 249).map σ).getD k 0 = σ (.n (257 + k)) := by
      simp [lyCap, List.getD_eq_getElem?_getD, hk]
    rw [hg, show 13 * 2 + k = 26 + k by ring]
    exact hcs k hk
  · rw [m264, c263] at l264
    rw [show σ (.n 5) * gen ^ 2 * gen ^ ([] ++ (W 0 ++ (W 1 ++ W 2))).length =
      σ (.n 5) * gen ^ 14 by
        simp only [List.nil_append, List.length_append, hW, chWords_length]; ring]
    exact l264
  · rw [show 13 * 2 + 6 + t = 32 + t by ring]
    have hv : ([W 0, W 1, W 2].map fun c ↦ multilinearEval c [σ (.n 248), σ (.n 262)]).getD t 0 =
        multilinearEval (W t) [σ (.n 248), σ (.n 262)] := by
      interval_cases t <;> rfl
    rw [hv]
    interval_cases t
    · exact VAL 265 32 0 rfl (by omega) (tb_holds_slice hnr h 81 _ (by decide +kernel))
    · exact VAL 274 33 1 rfl (by omega) (tb_holds_slice hnr h 91 _ (by decide +kernel))
    · exact VAL 283 34 2 rfl (by omega) (tb_holds_slice hnr h 101 _ (by decide +kernel))
  · rw [m293, c292] at l293
    exact l293
  · simp only [List.append_nil]
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    rw [tb_loadHolds_mul_gen_pow]
    interval_cases k
    · exact l248
    · exact l262
  · rw [c294] at l294; exact l294
  · rw [c295] at l295; exact l295
  · rw [c296] at l296; exact l296

end Sem

end
end LeanVM.Guest.B1.Tables
