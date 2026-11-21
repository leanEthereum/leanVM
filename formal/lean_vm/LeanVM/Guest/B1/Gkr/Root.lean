/-
  LeanVM.Guest.B1.Gkr.Root

  `verify_bus_gkr`'s root-most layer: one step of the specification's GKR walk from the roots,
  of one level at an odd depth and of two at an even one, to the layer slot of its point.
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.B1.Gkr.LayerStep
public import LeanVM.Guest.CoreData

/-!
# The root-most layer

The root-most layer has no rounds: the combiner, drawn from the two roots waiting in the sponge,
batches the three trees' roots into the claim the children's products check. `verify_bus_gkr`
runs it in its body, in the two arms of an `ite` on `odd_g = g^(depth % 2)`:

* `rt_two` (`core% «verify_bus_gkr» s274_e`, an odd depth): two children a tree, `y` one coordinate
  (its grind of `0` bits a permutation of the two waiting), the slot of `L = 1`;
* `rt_four` (`core% «verify_bus_gkr» s274_t`, an even depth): four children a tree, `y` two
  coordinates, the slot of `L = 2`.

Both start from the body's combiner `σ 36`, the claim `σ 52`, the sponge's capacity after the
combiner `σ 44 .. σ 48` and the zeros `σ 32 .. σ 35`, the cursor past the roots at `σ 5·g^2`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Core LeanVM.Core.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The binary root layer, the `ite`'s else arm. -/
noncomputable def rtTwo : List Stmt := (core% «verify_bus_gkr» s274_e)

/-- The radix-four root layer, the `ite`'s then arm. -/
noncomputable def rtFour : List Stmt := (core% «verify_bus_gkr» s274_t)

theorem rtTwo_noRet : Stmt.noRetList rtTwo = true := by decide +kernel

theorem rtFour_noRet : Stmt.noRetList rtFour = true := by decide +kernel

/-- Child `i`'s read's first statement in a root arm. -/
def rtPos (i : ℕ) : ℕ := 4 * i + i / 4

theorem rtTwo_check : ∀ i < 6,
    tbStmtsEqb (chT (.n 5) 2 340 i) ((rtTwo.drop (rtPos i)).take (chT (.n 5) 2 340 i).length) =
      true := by
  decide +kernel

theorem rtFour_check : ∀ i < 12,
    tbStmtsEqb (chT (.n 5) 2 190 i) ((rtFour.drop (rtPos i)).take (chT (.n 5) 2 190 i).length) =
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
one level to the layer record of `L = 1` (record `0`), the cursor past the roots `σ 5·g^2`. -/
theorem rt_two (h : Stmt.HoldsList C rd σ rtTwo True kret) {s : Fs} {st : GkrState}
    (hpt : st.point = []) (hvl : st.values.length = 3)
    (h59 : σ (.n 36) = s.squeeze.1) (h63 : σ (.n 52) = polyEval st.values s.squeeze.1)
    (hcap : (lyCap 36).map σ = capOf s.perm)
    (z42 : σ (.n 32) = 0) (z43 : σ (.n 33) = 0) (z44 : σ (.n 34) = 0) (z45 : σ (.n 35) = 0) :
    ∃ (xs : List E) (st' : GkrState) (s' : Fs), RunsTo (gkrStep 1 false st) s xs st' s' ∧
      TbReadsAt rd (σ (.n 5) * gen ^ 2) xs ∧
      GkSlot rd (σ (.n 173)) 1 s' (σ (.n 5) * gen ^ 2 * gen ^ xs.length) st'
        (σ (.n 185) * gen ^ 40) 1 1 1 := by
  have hnr := rtTwo_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have EV : ∀ i < 6, _ := fun i hi => ch_ev (tb_holds_slice hnr h (rtPos i) (chT (.n 5) 2 340 i)
    (rtTwo_check i hi))
  have hp : ∀ i < 6, FsPackOk σ (.n (chB 340 i)) (chB 340 i + 1) dsObserve :=
    fun i hi => (EV i hi).2.1
  have cp : ∀ i < 6, σ (.n (chB 340 i + 3)) = σ (.n (chB 340 i)) := fun i hi => (EV i hi).2.2
  set w0 := σ (.n 340)
  set w1 := σ (.n 344)
  set w2 := σ (.n 348)
  set w3 := σ (.n 352)
  set w4 := σ (.n 369)
  set w5 := σ (.n 373)
  have q0 : σ (.n 343) = w0 := cp 0 (by omega)
  have q1 : σ (.n 347) = w1 := cp 1 (by omega)
  have q2 : σ (.n 351) = w2 := cp 2 (by omega)
  have q3 : σ (.n 355) = w3 := cp 3 (by omega)
  have q4 : σ (.n 372) = w4 := cp 4 (by omega)
  have q5 : σ (.n 376) = w5 := cp 5 (by omega)
  -- the sponge: four children, a permutation, two waiting, `y`'s permutation
  have k1 := a 16 (.keccak (chRate 340 0 ++ lyCap 36) (lyOuts 356) false false) (by decide +kernel)
  obtain ⟨-, B0⟩ := ch_perm_block (fun i hi => hp (4 * 0 + i) (by omega)) k1
  rw [hcap] at B0
  have k2 := a 36 (.keccak ([.n 370, .n 371, .n 374, .n 375, .n 32, .n 33, .n 34, .n 35] ++
    lyCap 356) (lyOuts 387) false false) (by decide +kernel)
  obtain ⟨P2, B2⟩ := ly_keccak k2
  have hr2 : (([.n 370, .n 371, .n 374, .n 375, .n 32, .n 33, .n 34, .n 35] ++ lyCap 356 :
      List V).map σ) = rateOf [(w4, dsObserve), (w5, dsObserve)] ++ (lyCap 356).map σ := by
    obtain ⟨e327, e328⟩ := Prod.ext_iff.mp (fsPackT_cells (hp 4 (by omega)))
    obtain ⟨e331, e332⟩ := Prod.ext_iff.mp (fsPackT_cells (hp 5 (by omega)))
    norm_num [chB] at e327 e328 e331 e332
    rw [List.map_append, rateOf_eq_cells _ (by simp)]
    simp [pendCells, e327, e328, e331, e332, z42, z43, z44, z45, w4, w5]
  rw [hr2] at P2 B2
  -- the check
  obtain ⟨v0, v1, v2, hv3⟩ : ∃ v0 v1 v2, st.values = [v0, v1, v2] := by
    match st.values, hvl with
    | [v0, v1, v2], _ => exact ⟨v0, v1, v2, rfl⟩
  have hcheck : polyEval st.values s.squeeze.1 =
      polyEval [prodE [w0, w1], prodE [w2, w3], prodE [w4, w5]] s.squeeze.1 := by
    have m331 := a 25 (.mul (.n 377) (.n 372) (.n 376)) (by decide +kernel)
    have c332 := a 26 (.const (.n 378) (word 0 0)) (by decide +kernel)
    have m333 := a 27 (.mul (.n 379) (.n 36) (.n 378)) (by decide +kernel)
    have a334 := a 28 (.add (.n 380) (.n 377) (.n 379)) (by decide +kernel)
    have m335 := a 29 (.mul (.n 381) (.n 351) (.n 355)) (by decide +kernel)
    have m336 := a 30 (.mul (.n 382) (.n 36) (.n 380)) (by decide +kernel)
    have a337 := a 31 (.add (.n 383) (.n 381) (.n 382)) (by decide +kernel)
    have m338 := a 32 (.mul (.n 384) (.n 343) (.n 347)) (by decide +kernel)
    have m339 := a 33 (.mul (.n 385) (.n 36) (.n 383)) (by decide +kernel)
    have a340 := a 34 (.add (.n 386) (.n 384) (.n 385)) (by decide +kernel)
    have q := a 35 (.assertEq (.n 52) (.n 386)) (by decide +kernel)
    simp only [Atom.Holds, tb_word_zero] at m331 c332 m333 a334 m335 m336 a337 m338 m339 a340 q
    have q' := e_add_eq_zero_iff.mp q
    rw [h63, a340, m339, a337, m336, a334, m333, c332, m331, m335, m338, q0, q1, q2, q3, q4, q5,
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
  have hB0 : (lyCap 356).map σ = capOf (Fs.perm ⟨capOf s.perm,
      [(w0, dsObserve), (w1, dsObserve), (w2, dsObserve), (w3, dsObserve)]⟩) := by
    rw [B0]; rfl
  have hA2 : (⟨capOf s.perm, [(w0, dsObserve), (w1, dsObserve), (w2, dsObserve),
      (w3, dsObserve)]⟩ : Fs).absorbAll [w4, w5] dsObserve =
      ⟨(lyCap 356).map σ, [(w4, dsObserve), (w5, dsObserve)]⟩ := by
    rw [tb_absorbAll_full' _ (by simp) _ (by simp) (by simp), hB0]
    rfl
  rw [hA0, hA1, hA2] at hstep
  have hsq1 : ((⟨(lyCap 356).map σ, [(w4, dsObserve), (w5, dsObserve)]⟩ : Fs).squeezeN 1).1 =
      [σ (.n 387)] := by
    have e357 : σ (.n 387) = challengeOf
        (⟨(lyCap 356).map σ, [(w4, dsObserve), (w5, dsObserve)]⟩ : Fs).perm := by
      rw [P2 0 (by omega)]; exact (Keccak.challengeOf_cells _).symm
    rw [e357]; rfl
  have hsq2 : ((⟨(lyCap 356).map σ, [(w4, dsObserve), (w5, dsObserve)]⟩ : Fs).squeezeN 1).2 =
      ⟨(lyCap 387).map σ, []⟩ := by rw [B2]; rfl
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
  have hcs := tb_holds_slice hnr h 38 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (395 + k)) (.n 173) k)) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hcs
  simp only [Atom.Holds] at hcs
  have l341 := a 37 (.load (.n 387) (.n 185) 40) (by decide +kernel)
  have c354 := a 43 (.const (.n 400) (word 256 0)) (by decide +kernel)
  have m355 := a 44 (.mul (.n 401) (.n 5) (.n 400)) (by decide +kernel)
  have l355 := a 45 (.load (.n 401) (.n 173) 5) (by decide +kernel)
  have c365 := a 58 (.const (.n 411) (word 1099511627776 0)) (by decide +kernel)
  have m366 := a 59 (.mul (.n 412) (.n 185) (.n 411)) (by decide +kernel)
  have l366 := a 60 (.load (.n 412) (.n 173) 9) (by decide +kernel)
  have c367 := a 61 (.const (.n 413) (word 1 0)) (by decide +kernel)
  have l367 := a 62 (.load (.n 413) (.n 173) 10) (by decide +kernel)
  have c368 := a 63 (.const (.n 414) (word 1 0)) (by decide +kernel)
  have l368 := a 64 (.load (.n 414) (.n 173) 11) (by decide +kernel)
  have c369 := a 65 (.const (.n 415) (word 1 0)) (by decide +kernel)
  have l369 := a 66 (.load (.n 415) (.n 173) 12) (by decide +kernel)
  simp only [Atom.Holds] at l341 c354 m355 l355 c365 m366 l366 c367 l367 c368 l368 c369 l369
  rw [tb_word_one] at c367 c368 c369
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num, tb_word_two_pow (by norm_num)] at c354
  rw [show (1099511627776 : ℕ) = 2 ^ 40 by norm_num, tb_word_two_pow (by norm_num)] at c365
  have VAL : ∀ t < 3, ∀ b u v off : ℕ, Stmt.HoldsList C rd σ
      [.atom (.add (.n b) (.n u) (.n v)), .atom (.mul (.n (b + 1)) (.n 387) (.n b)),
        .atom (.add (.n (b + 2)) (.n u) (.n (b + 1))), .atom (.load (.n (b + 2)) (.n 173) off)]
      True kret → LoadHolds rd (σ (.n 173)) off (σ (.n u) + σ (.n 387) * (σ (.n u) + σ (.n v))) := by
    intro t _ b u v off hv
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hv
    obtain ⟨e0, e1, e2, l⟩ := hv
    rw [e2, e1, e0] at l
    exact l
  have V0 := VAL 0 (by omega) 402 343 347 6 (tb_holds_slice hnr h 46 _ (by decide +kernel))
  have V1 := VAL 1 (by omega) 405 351 355 7 (tb_holds_slice hnr h 50 _ (by decide +kernel))
  have V2 := VAL 2 (by omega) 408 372 376 8 (tb_holds_slice hnr h 54 _ (by decide +kernel))
  rw [q0, q1] at V0
  rw [q2, q3] at V1
  rw [q4, q5] at V2
  refine ⟨by simp [lyCap], fun k hk => ?_, rfl, ?_, by simp, fun t ht => ?_, ?_, by simp, ?_,
    ?_, ?_, ?_⟩
  · have hg : ((lyCap 387).map σ).getD k 0 = σ (.n (395 + k)) := by
      simp [lyCap, List.getD_eq_getElem?_getD, hk]
    rw [hg, show 13 * ((1 - 1) / 2) + k = k by norm_num]
    exact hcs k hk
  · rw [m355, c354] at l355
    have hlen : ([] ++ ([w0, w1] ++ ([w2, w3] ++ [w4, w5]))).length = 6 := rfl
    rw [hlen, mul_assoc, ← pow_add]
    exact l355
  · rw [show 13 * ((1 - 1) / 2) + 6 + t = 6 + t by norm_num]
    interval_cases t
    · convert V0 using 1; simp [multilinearEval, foldPairs]; ring
    · convert V1 using 1; simp [multilinearEval, foldPairs]; ring
    · convert V2 using 1; simp [multilinearEval, foldPairs]; ring
  · rw [m366, c365] at l366
    exact l366
  · simp only [List.append_nil]
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    obtain rfl : k = 0 := by omega
    rw [tb_loadHolds_mul_gen_pow]
    exact l341
  · rw [c367] at l367; exact l367
  · rw [c368] at l368; exact l368
  · rw [c369] at l369; exact l369

/-- **The radix-four root layer** (an even depth): from the sponge `s` the roots wait in, one
step of two levels to the layer record of `L = 2` (record `0`), the cursor past the roots
`σ 5·g^2`. -/
theorem rt_four (h : Stmt.HoldsList C rd σ rtFour True kret) {s : Fs} {st : GkrState}
    (hpt : st.point = []) (hvl : st.values.length = 3)
    (h59 : σ (.n 36) = s.squeeze.1) (h63 : σ (.n 52) = polyEval st.values s.squeeze.1)
    (hcap : (lyCap 36).map σ = capOf s.perm)
    (z42 : σ (.n 32) = 0) (z43 : σ (.n 33) = 0) (z44 : σ (.n 34) = 0) (z45 : σ (.n 35) = 0) :
    ∃ (xs : List E) (st' : GkrState) (s' : Fs), RunsTo (gkrStep 2 false st) s xs st' s' ∧
      TbReadsAt rd (σ (.n 5) * gen ^ 2) xs ∧
      GkSlot rd (σ (.n 173)) 2 s' (σ (.n 5) * gen ^ 2 * gen ^ xs.length) st'
        (σ (.n 185) * gen ^ 40) 1 1 gen := by
  have hnr := rtFour_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have EV : ∀ i < 12, _ := fun i hi => ch_ev (tb_holds_slice hnr h (rtPos i) (chT (.n 5) 2 190 i)
    (rtFour_check i hi))
  have hp : ∀ i < 12, FsPackOk σ (.n (chB 190 i)) (chB 190 i + 1) dsObserve :=
    fun i hi => (EV i hi).2.1
  have cp : ∀ i < 12, σ (.n (chB 190 i + 3)) = σ (.n (chB 190 i)) := fun i hi => (EV i hi).2.2
  set W := chWords σ 190 with hW
  -- the sponge: three blocks of four children, then `y`'s two permutations
  have k1 := a 16 (.keccak (chRate 190 0 ++ lyCap 36) (lyOuts 206) false false) (by decide +kernel)
  obtain ⟨-, B0⟩ := ch_perm_block (fun i hi => hp (4 * 0 + i) (by omega)) k1
  rw [hcap] at B0
  have k2 := a 33 (.keccak (chRate 190 1 ++ lyCap 206) (lyOuts 235) false false) (by decide +kernel)
  obtain ⟨-, B1⟩ := ch_perm_block (fun i hi => hp (4 * 1 + i) (by omega)) k2
  have k3 := a 67 (.keccak (chRate 190 2 ++ lyCap 235) (lyOuts 280) false false) (by decide +kernel)
  obtain ⟨P2, B2⟩ := ch_perm_block (fun i hi => hp (4 * 2 + i) (by omega)) k3
  set sp : Fs := ((s.squeeze.2.absorbAll (W 0) dsObserve).absorbAll (W 1) dsObserve).absorbAll
    (W 2) dsObserve with hsp
  have hA : sp = ⟨(lyCap 235).map σ, (W 2).map (·, dsObserve)⟩ := by
    rw [hsp]
    have A0 : s.squeeze.2.absorbAll (W 0) dsObserve = ⟨capOf s.perm, (W 0).map (·, dsObserve)⟩ := by
      rw [absorbAll_short _ _ _ (by simp [Fs.squeeze, hW, chWords_length])]
      simp [Fs.squeeze]
    rw [A0, tb_absorbAll_full _ (by simp [hW, chWords_length]) _ (chWords_length σ 190 1),
      show capOf (Fs.perm ⟨capOf s.perm, (W 0).map (·, dsObserve)⟩) = (lyCap 206).map σ by
        rw [B0],
      tb_absorbAll_full _ (by simp [chWords_length]) _ (chWords_length σ 190 2), ← B1]
  rw [← hA] at P2 B2
  have k4 := a 68 (.keccak ([.n 32, .n 32, .n 32, .n 32, .n 32, .n 33, .n 34, .n 35] ++
    lyCap 280) (lyOuts 293) false false) (by decide +kernel)
  obtain ⟨P3, B3⟩ := ly_keccak k4
  rw [ly_zero_rate z42 z43 z44 z45, B2] at P3 B3
  have hsq1 : (sp.squeezeN 2).1 = [σ (.n 280), σ (.n 293)] := by
    have e248 : σ (.n 280) = challengeOf sp.perm := by
      rw [P2 0 (by omega)]; exact (Keccak.challengeOf_cells _).symm
    have e262 : σ (.n 293) = challengeOf (permOf (rateOf [] ++ capOf sp.perm)) := by
      rw [P3 0 (by omega)]; exact (Keccak.challengeOf_cells _).symm
    rw [e248, e262]; rfl
  have hsq2 : (sp.squeezeN 2).2 = ⟨(lyCap 293).map σ, []⟩ := by
    rw [B3]; rfl
  -- the check
  obtain ⟨v0, v1, v2, hv3⟩ : ∃ v0 v1 v2, st.values = [v0, v1, v2] := by
    match st.values, hvl with
    | [v0, v1, v2], _ => exact ⟨v0, v1, v2, rfl⟩
  have hcheck : polyEval st.values s.squeeze.1 =
      polyEval [prodE (W 0), prodE (W 1), prodE (W 2)] s.squeeze.1 := by
    have m218 := a 50 (.mul (.n 264) (.n 251) (.n 255)) (by decide +kernel)
    have m219 := a 51 (.mul (.n 265) (.n 264) (.n 259)) (by decide +kernel)
    have m220 := a 52 (.mul (.n 266) (.n 265) (.n 263)) (by decide +kernel)
    have c221 := a 53 (.const (.n 267) (word 0 0)) (by decide +kernel)
    have m222 := a 54 (.mul (.n 268) (.n 36) (.n 267)) (by decide +kernel)
    have a223 := a 55 (.add (.n 269) (.n 266) (.n 268)) (by decide +kernel)
    have m224 := a 56 (.mul (.n 270) (.n 222) (.n 226)) (by decide +kernel)
    have m225 := a 57 (.mul (.n 271) (.n 270) (.n 230)) (by decide +kernel)
    have m226 := a 58 (.mul (.n 272) (.n 271) (.n 234)) (by decide +kernel)
    have m227 := a 59 (.mul (.n 273) (.n 36) (.n 269)) (by decide +kernel)
    have a228 := a 60 (.add (.n 274) (.n 272) (.n 273)) (by decide +kernel)
    have m229 := a 61 (.mul (.n 275) (.n 193) (.n 197)) (by decide +kernel)
    have m230 := a 62 (.mul (.n 276) (.n 275) (.n 201)) (by decide +kernel)
    have m231 := a 63 (.mul (.n 277) (.n 276) (.n 205)) (by decide +kernel)
    have m232 := a 64 (.mul (.n 278) (.n 36) (.n 274)) (by decide +kernel)
    have a233 := a 65 (.add (.n 279) (.n 277) (.n 278)) (by decide +kernel)
    have q := a 66 (.assertEq (.n 52) (.n 279)) (by decide +kernel)
    simp only [Atom.Holds, tb_word_zero] at m218 m219 m220 c221 m222 a223 m224 m225 m226 m227
    simp only [Atom.Holds] at a228 m229 m230 m231 m232 a233 q
    have q' := e_add_eq_zero_iff.mp q
    rw [h63, a233, m232, a228, m227, a223, m222, c221, m220, m219, m218, m226, m225, m224, m231,
      m230, m229, h59,
      show σ (.n 193) = σ (.n 190) from cp 0 (by omega),
      show σ (.n 197) = σ (.n 194) from cp 1 (by omega),
      show σ (.n 201) = σ (.n 198) from cp 2 (by omega),
      show σ (.n 205) = σ (.n 202) from cp 3 (by omega),
      show σ (.n 222) = σ (.n 219) from cp 4 (by omega),
      show σ (.n 226) = σ (.n 223) from cp 5 (by omega),
      show σ (.n 230) = σ (.n 227) from cp 6 (by omega),
      show σ (.n 234) = σ (.n 231) from cp 7 (by omega),
      show σ (.n 251) = σ (.n 248) from cp 8 (by omega),
      show σ (.n 255) = σ (.n 252) from cp 9 (by omega),
      show σ (.n 259) = σ (.n 256) from cp 10 (by omega),
      show σ (.n 263) = σ (.n 260) from cp 11 (by omega)] at q'
    rw [q', hW, chWords_eq, chWords_eq, chWords_eq]
    simp only [chB, polyEval, prodE, List.foldr, List.foldl]
    ring
  have hstep := gkrStep_run (step := 2) le_rfl false (rt_sumcheck hpt _ 2 s.squeeze.2)
    (chWords_length σ 190 0) (chWords_length σ 190 1) (chWords_length σ 190 2) hcheck
  rw [show ((s.squeeze.2.absorbAll (chWords σ 190 0) dsObserve).absorbAll (chWords σ 190 1)
    dsObserve).absorbAll (chWords σ 190 2) dsObserve = sp from rfl, hsq1, hsq2] at hstep
  refine ⟨_, _, _, hstep, ?_, ?_⟩
  · intro k hk
    have hk12 : k < 12 := by simpa [chWords_length] using hk
    apply rt_read
    convert (EV k hk12).1 using 1
    simp only [List.nil_append, chWords_eq]
    interval_cases k <;> rfl
  -- the record of `L = 2`
  have hcs := tb_holds_slice hnr h 71 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (301 + k)) (.n 173) k)) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hcs
  simp only [Atom.Holds] at hcs
  have l234 := a 69 (.load (.n 280) (.n 185) 40) (by decide +kernel)
  have l247 := a 70 (.load (.n 293) (.n 185) 41) (by decide +kernel)
  have c260 := a 76 (.const (.n 306) (word 16384 0)) (by decide +kernel)
  have m261 := a 77 (.mul (.n 307) (.n 5) (.n 306)) (by decide +kernel)
  have l261 := a 78 (.load (.n 307) (.n 173) 5) (by decide +kernel)
  have c289 := a 109 (.const (.n 335) (word 1099511627776 0)) (by decide +kernel)
  have m290 := a 110 (.mul (.n 336) (.n 185) (.n 335)) (by decide +kernel)
  have l290 := a 111 (.load (.n 336) (.n 173) 9) (by decide +kernel)
  have c291 := a 112 (.const (.n 337) (word 1 0)) (by decide +kernel)
  have l291 := a 113 (.load (.n 337) (.n 173) 10) (by decide +kernel)
  have c292 := a 114 (.const (.n 338) (word 1 0)) (by decide +kernel)
  have l292 := a 115 (.load (.n 338) (.n 173) 11) (by decide +kernel)
  have c293 := a 116 (.const (.n 339) (word 2 0)) (by decide +kernel)
  have l293 := a 117 (.load (.n 339) (.n 173) 12) (by decide +kernel)
  simp only [Atom.Holds] at l234 l247 c260 m261 l261 c289 m290 l290 c291 l291 c292 l292 c293 l293
  rw [tb_word_gen] at c293
  rw [tb_word_one] at c291 c292
  rw [show (16384 : ℕ) = 2 ^ 14 by norm_num, tb_word_two_pow (by norm_num)] at c260
  rw [show (1099511627776 : ℕ) = 2 ^ 40 by norm_num, tb_word_two_pow (by norm_num)] at c289
  have VAL : ∀ b off t, (b = 308 + 9 * t) → t < 3 →
      Stmt.HoldsList C rd σ (chValT 190 280 293 173 t b off) True kret →
      LoadHolds rd (σ (.n 173)) off (multilinearEval (W t) [σ (.n 280), σ (.n 293)]) := by
    intro b off t hb ht hv
    obtain ⟨ev, l⟩ := ch_val hv
    rw [ev] at l
    have hw : ∀ i < 4, σ (.n (chB 190 (4 * t + i) + 3)) = σ (.n (chB 190 (4 * t + i))) :=
      fun i hi => cp _ (by omega)
    rw [hw 0 (by omega), hw 1 (by omega), hw 2 (by omega), hw 3 (by omega)] at l
    rw [hW, chWords_eq]
    simpa using l
  refine ⟨by simp [lyCap], fun k hk => ?_, rfl, ?_, by simp, fun t ht => ?_, ?_, by simp, ?_,
    ?_, ?_, ?_⟩
  · have hg : ((lyCap 293).map σ).getD k 0 = σ (.n (301 + k)) := by
      simp [lyCap, List.getD_eq_getElem?_getD, hk]
    rw [hg, show 13 * ((2 - 1) / 2) + k = k by norm_num]
    exact hcs k hk
  · rw [m261, c260] at l261
    have hlen : ([] ++ (chWords σ 190 0 ++ (chWords σ 190 1 ++ chWords σ 190 2))).length = 12 := by
      simp only [List.nil_append, List.length_append, chWords_length]
    rw [hlen, mul_assoc, ← pow_add]
    exact l261
  · rw [show 13 * ((2 - 1) / 2) + 6 + t = 6 + t by norm_num]
    have hv : ([W 0, W 1, W 2].map fun c ↦ multilinearEval c [σ (.n 280), σ (.n 293)]).getD t 0 =
        multilinearEval (W t) [σ (.n 280), σ (.n 293)] := by
      interval_cases t <;> rfl
    rw [hv]
    interval_cases t
    · exact VAL 308 6 0 rfl (by omega) (tb_holds_slice hnr h 79 _ (by decide +kernel))
    · exact VAL 317 7 1 rfl (by omega) (tb_holds_slice hnr h 89 _ (by decide +kernel))
    · exact VAL 326 8 2 rfl (by omega) (tb_holds_slice hnr h 99 _ (by decide +kernel))
  · rw [m290, c289] at l290
    exact l290
  · simp only [List.append_nil]
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    rw [tb_loadHolds_mul_gen_pow]
    interval_cases k
    · exact l234
    · exact l247
  · rw [c291] at l291; exact l291
  · rw [c292] at l292; exact l292
  · rw [c293] at l293; exact l293

end Sem

end
end LeanVM.Guest.B1.Tables
