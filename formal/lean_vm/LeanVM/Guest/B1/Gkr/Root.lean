/-
  LeanVM.Guest.B1.Gkr.Root

  `verify_bus_gkr`'s root-most layer: one step of the specification's GKR walk from the roots,
  of one level at an odd depth and of two at an even one, to the layer slot of its point.
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.B1.Gkr.LayerTail
public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Tables.Basic
import LeanVM.Guest.KernelLit

/-!
# The root-most layer

The root-most layer has no rounds: the combiner, drawn from the two roots waiting in the sponge,
batches the three trees' roots into the claim the children's products check. `verify_bus_gkr`
runs it in its body, in the two arms of an `ite` on `odd_g = g^(depth % 2)`, here renumbered
(`rtUn`; the body's are `rtSh` of them: values below `19` kept, those from `19` `71` up, those from
`66` `105` up):

* `rt_two` (`core% «verify_bus_gkr» s388_e`, an odd depth): two children a tree, `y` one coordinate
  (its grind of `0` bits a permutation of the two waiting), the slot of `L = 1`;
* `rt_four` (`core% «verify_bus_gkr» s388_t`, an even depth): four children a tree, `y` two
  coordinates, the slot of `L = 2`.

Both start from the body's combiner `σ 46`, the claim `σ 62`, the sponge's capacity after the
combiner `σ 54 .. σ 58` and the zeros `σ 42 .. σ 45`, the cursor past the roots at `σ 5·g^2`, the
point rows at `σ 22` and the slot at `σ 139`, in the arms' numbering.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The arms' numbering from the body's. -/
def rtUn (v : V) : V :=
  if 171 ≤ v.idx then .n (v.idx - 105) else if 90 ≤ v.idx ∧ v.idx < 137 then .n (v.idx - 71) else v

/-- The body's numbering from the arms': values from `19` on `71` up, from `66` on `105` up. -/
def rtSh (v : V) : V :=
  if 66 ≤ v.idx then .n (v.idx + 105) else if 19 ≤ v.idx then .n (v.idx + 71) else v

/-- The binary root layer, the `ite`'s else arm, renumbered (`rtUn`). -/
noncomputable def rtTwo : List Stmt := Stmt.renameList rtUn (core% «verify_bus_gkr» s388_e)

/-- The radix-four root layer, the `ite`'s then arm, renumbered (`rtUn`). -/
noncomputable def rtFour : List Stmt := Stmt.renameList rtUn (core% «verify_bus_gkr» s388_t)

open LeanVM.Guest.KernelLit in
/-- The else arm is `rtTwo` in the body's numbering. -/
kernel_rfl rtTwo_eq : (core% «verify_bus_gkr» s388_e) = Stmt.renameList rtSh rtTwo

open LeanVM.Guest.KernelLit in
/-- The then arm is `rtFour` in the body's numbering. -/
kernel_rfl rtFour_eq : (core% «verify_bus_gkr» s388_t) = Stmt.renameList rtSh rtFour

theorem rtTwo_noRet : Stmt.noRetList rtTwo = true := by decide +kernel

theorem rtFour_noRet : Stmt.noRetList rtFour = true := by decide +kernel

/-- The first radix-four record's position, `GEN ** ROUND_SLOTS`. -/
theorem tb_word_128 : word 128 0 = gen ^ 7 := by
  rw [show (128 : ℕ) = 2 ^ 7 by norm_num, word_two_pow (by norm_num)]

/-- Child `i`'s read's first statement in a root arm. -/
def rtPos (i : ℕ) : ℕ := 4 * i + i / 4

theorem rtTwo_check : ∀ i < 6,
    stmtsEqb (chT (.n 5) 2 288 i) ((rtTwo.drop (rtPos i)).take (chT (.n 5) 2 288 i).length) =
      true := by
  decide +kernel

theorem rtFour_check : ∀ i < 12,
    stmtsEqb (chT (.n 5) 2 142 i) ((rtFour.drop (rtPos i)).take (chT (.n 5) 2 142 i).length) =
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
  rw [loadHolds_mul_gen_pow]; exact h

/-- **The binary root layer** (an odd depth): from the sponge `s` the roots wait in, one step of
one level to the slot of `L = 1`, the cursor past the roots `σ 5·g^2`. -/
theorem rt_two (h : Stmt.HoldsList C rd σ rtTwo True kret)
    (h140 : σ (.n 139) = σ (.n 16) * gen ^ 10) {s : Fs} {st : GkrState}
    (hpt : st.point = []) (hvl : st.values.length = 3)
    (h59 : σ (.n 46) = s.squeeze.1) (h63 : σ (.n 62) = polyEval st.values s.squeeze.1)
    (hcap : (lyCap 46).map σ = capOf s.perm)
    (z42 : σ (.n 42) = 0) (z43 : σ (.n 43) = 0) (z44 : σ (.n 44) = 0) (z45 : σ (.n 45) = 0) :
    ∃ (xs : List E) (st' : GkrState) (s' : Fs), RunsTo (gkrStep 1 false st) s xs st' s' ∧
      ReadsAt rd (σ (.n 5) * gen ^ 2) xs ∧
      GkSlot rd (σ (.n 16)) 1 s' (σ (.n 5) * gen ^ 2 * gen ^ xs.length) st'
        (σ (.n 22) * gen ^ 40) (gen ^ 7) := by
  have hnr := rtTwo_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have EV : ∀ i < 6, _ := fun i hi => ch_ev (tb_holds_slice hnr h (rtPos i) (chT (.n 5) 2 288 i)
    (rtTwo_check i hi))
  have hp : ∀ i < 6, FsPackOk σ (.n (chB 288 i)) (chB 288 i + 1) dsObserve :=
    fun i hi => (EV i hi).2.1
  have cp : ∀ i < 6, σ (.n (chB 288 i + 3)) = σ (.n (chB 288 i)) := fun i hi => (EV i hi).2.2
  set w0 := σ (.n 288)
  set w1 := σ (.n 292)
  set w2 := σ (.n 296)
  set w3 := σ (.n 300)
  set w4 := σ (.n 317)
  set w5 := σ (.n 321)
  have q0 : σ (.n 291) = w0 := cp 0 (by omega)
  have q1 : σ (.n 295) = w1 := cp 1 (by omega)
  have q2 : σ (.n 299) = w2 := cp 2 (by omega)
  have q3 : σ (.n 303) = w3 := cp 3 (by omega)
  have q4 : σ (.n 320) = w4 := cp 4 (by omega)
  have q5 : σ (.n 324) = w5 := cp 5 (by omega)
  -- the sponge: four children, a permutation, two waiting, `y`'s permutation
  have k1 := a 16 (.keccak (chRate 288 0 ++ lyCap 46) (lyOuts 304) false false) (by decide +kernel)
  obtain ⟨-, B0⟩ := ch_perm_block (fun i hi => hp (4 * 0 + i) (by omega)) k1
  rw [hcap] at B0
  have k2 := a 36 (.keccak ([.n 318, .n 319, .n 322, .n 323, .n 42, .n 43, .n 44, .n 45] ++
    lyCap 304) (lyOuts 335) false false) (by decide +kernel)
  obtain ⟨P2, B2⟩ := ly_keccak k2
  have hr2 : (([.n 318, .n 319, .n 322, .n 323, .n 42, .n 43, .n 44, .n 45] ++ lyCap 304 :
      List V).map σ) = rateOf [(w4, dsObserve), (w5, dsObserve)] ++ (lyCap 304).map σ := by
    obtain ⟨e321, e322⟩ := Prod.ext_iff.mp (fsPackT_cells (hp 4 (by omega)))
    obtain ⟨e325, e326⟩ := Prod.ext_iff.mp (fsPackT_cells (hp 5 (by omega)))
    norm_num [chB] at e321 e322 e325 e326
    rw [List.map_append, rateOf_eq_cells _ (by simp)]
    simp [pendCells, e321, e322, e325, e326, z42, z43, z44, z45, w4, w5]
  rw [hr2] at P2 B2
  -- the check
  obtain ⟨v0, v1, v2, hv3⟩ : ∃ v0 v1 v2, st.values = [v0, v1, v2] := by
    match st.values, hvl with
    | [v0, v1, v2], _ => exact ⟨v0, v1, v2, rfl⟩
  have hcheck : polyEval st.values s.squeeze.1 =
      polyEval [prodE [w0, w1], prodE [w2, w3], prodE [w4, w5]] s.squeeze.1 := by
    have m328 := a 25 (.mul (.n 325) (.n 320) (.n 324)) (by decide +kernel)
    have c329 := a 26 (.const (.n 326) (word 0 0)) (by decide +kernel)
    have m330 := a 27 (.mul (.n 327) (.n 46) (.n 326)) (by decide +kernel)
    have a331 := a 28 (.add (.n 328) (.n 325) (.n 327)) (by decide +kernel)
    have m332 := a 29 (.mul (.n 329) (.n 299) (.n 303)) (by decide +kernel)
    have m333 := a 30 (.mul (.n 330) (.n 46) (.n 328)) (by decide +kernel)
    have a334 := a 31 (.add (.n 331) (.n 329) (.n 330)) (by decide +kernel)
    have m335 := a 32 (.mul (.n 332) (.n 291) (.n 295)) (by decide +kernel)
    have m336 := a 33 (.mul (.n 333) (.n 46) (.n 331)) (by decide +kernel)
    have a337 := a 34 (.add (.n 334) (.n 332) (.n 333)) (by decide +kernel)
    have q := a 35 (.assertEq (.n 62) (.n 334)) (by decide +kernel)
    simp only [Atom.Holds, word_zero] at m328 c329 m330 a331 m332 m333 a334 m335 m336 a337 q
    have q' := e_add_eq_zero_iff.mp q
    rw [h63, a337, m336, a334, m333, a331, m330, c329, m328, m332, m335, q0, q1, q2, q3, q4, q5,
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
  have hB0 : (lyCap 304).map σ = capOf (Fs.perm ⟨capOf s.perm,
      [(w0, dsObserve), (w1, dsObserve), (w2, dsObserve), (w3, dsObserve)]⟩) := by
    rw [B0]; rfl
  have hA2 : (⟨capOf s.perm, [(w0, dsObserve), (w1, dsObserve), (w2, dsObserve),
      (w3, dsObserve)]⟩ : Fs).absorbAll [w4, w5] dsObserve =
      ⟨(lyCap 304).map σ, [(w4, dsObserve), (w5, dsObserve)]⟩ := by
    rw [tb_absorbAll_full' _ (by simp) _ (by simp) (by simp), hB0]
    rfl
  rw [hA0, hA1, hA2] at hstep
  have hsq1 : ((⟨(lyCap 304).map σ, [(w4, dsObserve), (w5, dsObserve)]⟩ : Fs).squeezeN 1).1 =
      [σ (.n 335)] := by
    have e351 : σ (.n 335) = challengeOf
        (⟨(lyCap 304).map σ, [(w4, dsObserve), (w5, dsObserve)]⟩ : Fs).perm := by
      rw [P2 0 (by omega)]; exact (Keccak.challengeOf_cells _).symm
    rw [e351]; rfl
  have hsq2 : ((⟨(lyCap 304).map σ, [(w4, dsObserve), (w5, dsObserve)]⟩ : Fs).squeezeN 1).2 =
      ⟨(lyCap 335).map σ, []⟩ := by rw [B2]; rfl
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
  have ld : ∀ k w, LoadHolds rd (σ (.n 139)) k w → LoadHolds rd (σ (.n 16)) (10 * 1 + k) w :=
    fun k w hw => by rw [h140, loadHolds_mul_gen_pow] at hw; exact hw
  have hcs := tb_holds_slice hnr h 40 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (343 + k)) (.n 139) k)) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hcs
  simp only [Atom.Holds] at hcs
  have l351 := a 37 (.load (.n 335) (.n 22) 40) (by decide +kernel)
  have c353 := a 45 (.const (.n 349) (word 256 0)) (by decide +kernel)
  have m354 := a 46 (.mul (.n 350) (.n 5) (.n 349)) (by decide +kernel)
  have l354 := a 47 (.load (.n 350) (.n 139) 5) (by decide +kernel)
  have c364 := a 60 (.const (.n 360) (word 128 0)) (by decide +kernel)
  have l364 := a 61 (.load (.n 360) (.n 139) 9) (by decide +kernel)
  simp only [Atom.Holds] at l351 c353 m354 l354 c364 l364
  rw [tb_word_128] at c364
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num, word_two_pow (by norm_num)] at c353
  have VAL : ∀ t < 3, ∀ b u v off : ℕ, Stmt.HoldsList C rd σ
      [.atom (.add (.n b) (.n u) (.n v)), .atom (.mul (.n (b + 1)) (.n 335) (.n b)),
        .atom (.add (.n (b + 2)) (.n u) (.n (b + 1))), .atom (.load (.n (b + 2)) (.n 139) off)]
      True kret → LoadHolds rd (σ (.n 139)) off (σ (.n u) + σ (.n 335) * (σ (.n u) + σ (.n v))) := by
    intro t _ b u v off hv
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hv
    obtain ⟨e0, e1, e2, l⟩ := hv
    rw [e2, e1, e0] at l
    exact l
  have V0 := VAL 0 (by omega) 351 291 295 6 (tb_holds_slice hnr h 48 _ (by decide +kernel))
  have V1 := VAL 1 (by omega) 354 299 303 7 (tb_holds_slice hnr h 52 _ (by decide +kernel))
  have V2 := VAL 2 (by omega) 357 320 324 8 (tb_holds_slice hnr h 56 _ (by decide +kernel))
  rw [q0, q1] at V0
  rw [q2, q3] at V1
  rw [q4, q5] at V2
  refine ⟨by simp [lyCap], fun k hk => ?_, rfl, ?_, by simp, fun t ht => ?_, by simp, ?_, ?_⟩
  · have hg : ((lyCap 335).map σ).getD k 0 = σ (.n (343 + k)) := by
      simp [lyCap, List.getD_eq_getElem?_getD, hk]
    rw [hg]
    exact ld _ _ (hcs k hk)
  · rw [m354, c353] at l354
    have hlen : ([] ++ ([w0, w1] ++ ([w2, w3] ++ [w4, w5]))).length = 6 := rfl
    rw [hlen, mul_assoc, ← pow_add]
    exact ld _ _ l354
  · rw [show 10 * 1 + 6 + t = 10 * 1 + (6 + t) by ring]
    apply ld
    interval_cases t
    · convert V0 using 1; simp [multilinearEval, foldPairs]; ring
    · convert V1 using 1; simp [multilinearEval, foldPairs]; ring
    · convert V2 using 1; simp [multilinearEval, foldPairs]; ring
  · simp only [List.append_nil]
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    obtain rfl : k = 0 := by omega
    rw [loadHolds_mul_gen_pow]
    exact l351
  · rw [c364] at l364; exact ld _ _ l364

/-- **The radix-four root layer** (an even depth): from the sponge `s` the roots wait in, one
step of two levels to the slot of `L = 2`, the cursor past the roots `σ 5·g^2`. -/
theorem rt_four (h : Stmt.HoldsList C rd σ rtFour True kret)
    (h140 : σ (.n 139) = σ (.n 16) * gen ^ 20) {s : Fs} {st : GkrState}
    (hpt : st.point = []) (hvl : st.values.length = 3)
    (h59 : σ (.n 46) = s.squeeze.1) (h63 : σ (.n 62) = polyEval st.values s.squeeze.1)
    (hcap : (lyCap 46).map σ = capOf s.perm)
    (z42 : σ (.n 42) = 0) (z43 : σ (.n 43) = 0) (z44 : σ (.n 44) = 0) (z45 : σ (.n 45) = 0) :
    ∃ (xs : List E) (st' : GkrState) (s' : Fs), RunsTo (gkrStep 2 false st) s xs st' s' ∧
      ReadsAt rd (σ (.n 5) * gen ^ 2) xs ∧
      GkSlot rd (σ (.n 16)) 2 s' (σ (.n 5) * gen ^ 2 * gen ^ xs.length) st'
        (σ (.n 22) * gen ^ 40) (gen ^ 7) := by
  have hnr := rtFour_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have EV : ∀ i < 12, _ := fun i hi => ch_ev (tb_holds_slice hnr h (rtPos i) (chT (.n 5) 2 142 i)
    (rtFour_check i hi))
  have hp : ∀ i < 12, FsPackOk σ (.n (chB 142 i)) (chB 142 i + 1) dsObserve :=
    fun i hi => (EV i hi).2.1
  have cp : ∀ i < 12, σ (.n (chB 142 i + 3)) = σ (.n (chB 142 i)) := fun i hi => (EV i hi).2.2
  set W := chWords σ 142 with hW
  -- the sponge: three blocks of four children, then `y`'s two permutations
  have k1 := a 16 (.keccak (chRate 142 0 ++ lyCap 46) (lyOuts 158) false false) (by decide +kernel)
  obtain ⟨-, B0⟩ := ch_perm_block (fun i hi => hp (4 * 0 + i) (by omega)) k1
  rw [hcap] at B0
  have k2 := a 33 (.keccak (chRate 142 1 ++ lyCap 158) (lyOuts 187) false false) (by decide +kernel)
  obtain ⟨-, B1⟩ := ch_perm_block (fun i hi => hp (4 * 1 + i) (by omega)) k2
  have k3 := a 67 (.keccak (chRate 142 2 ++ lyCap 187) (lyOuts 232) false false) (by decide +kernel)
  obtain ⟨P2, B2⟩ := ch_perm_block (fun i hi => hp (4 * 2 + i) (by omega)) k3
  set sp : Fs := ((s.squeeze.2.absorbAll (W 0) dsObserve).absorbAll (W 1) dsObserve).absorbAll
    (W 2) dsObserve with hsp
  have hA : sp = ⟨(lyCap 187).map σ, (W 2).map (·, dsObserve)⟩ := by
    rw [hsp]
    have A0 : s.squeeze.2.absorbAll (W 0) dsObserve = ⟨capOf s.perm, (W 0).map (·, dsObserve)⟩ := by
      rw [absorbAll_short _ _ _ (by simp [Fs.squeeze, hW, chWords_length])]
      simp [Fs.squeeze]
    rw [A0, tb_absorbAll_full _ (by simp [hW, chWords_length]) _ (chWords_length σ 142 1),
      show capOf (Fs.perm ⟨capOf s.perm, (W 0).map (·, dsObserve)⟩) = (lyCap 158).map σ by
        rw [B0],
      tb_absorbAll_full _ (by simp [chWords_length]) _ (chWords_length σ 142 2), ← B1]
  rw [← hA] at P2 B2
  have k4 := a 68 (.keccak ([.n 42, .n 42, .n 42, .n 42, .n 42, .n 43, .n 44, .n 45] ++
    lyCap 232) (lyOuts 245) false false) (by decide +kernel)
  obtain ⟨P3, B3⟩ := ly_keccak k4
  rw [ly_zero_rate z42 z43 z44 z45, B2] at P3 B3
  have hsq1 : (sp.squeezeN 2).1 = [σ (.n 232), σ (.n 245)] := by
    have e248 : σ (.n 232) = challengeOf sp.perm := by
      rw [P2 0 (by omega)]; exact (Keccak.challengeOf_cells _).symm
    have e262 : σ (.n 245) = challengeOf (permOf (rateOf [] ++ capOf sp.perm)) := by
      rw [P3 0 (by omega)]; exact (Keccak.challengeOf_cells _).symm
    rw [e248, e262]; rfl
  have hsq2 : (sp.squeezeN 2).2 = ⟨(lyCap 245).map σ, []⟩ := by
    rw [B3]; rfl
  -- the check
  obtain ⟨v0, v1, v2, hv3⟩ : ∃ v0 v1 v2, st.values = [v0, v1, v2] := by
    match st.values, hvl with
    | [v0, v1, v2], _ => exact ⟨v0, v1, v2, rfl⟩
  have hcheck : polyEval st.values s.squeeze.1 =
      polyEval [prodE (W 0), prodE (W 1), prodE (W 2)] s.squeeze.1 := by
    have m219 := a 50 (.mul (.n 216) (.n 203) (.n 207)) (by decide +kernel)
    have m220 := a 51 (.mul (.n 217) (.n 216) (.n 211)) (by decide +kernel)
    have m221 := a 52 (.mul (.n 218) (.n 217) (.n 215)) (by decide +kernel)
    have c222 := a 53 (.const (.n 219) (word 0 0)) (by decide +kernel)
    have m223 := a 54 (.mul (.n 220) (.n 46) (.n 219)) (by decide +kernel)
    have a224 := a 55 (.add (.n 221) (.n 218) (.n 220)) (by decide +kernel)
    have m225 := a 56 (.mul (.n 222) (.n 174) (.n 178)) (by decide +kernel)
    have m226 := a 57 (.mul (.n 223) (.n 222) (.n 182)) (by decide +kernel)
    have m227 := a 58 (.mul (.n 224) (.n 223) (.n 186)) (by decide +kernel)
    have m228 := a 59 (.mul (.n 225) (.n 46) (.n 221)) (by decide +kernel)
    have a229 := a 60 (.add (.n 226) (.n 224) (.n 225)) (by decide +kernel)
    have m230 := a 61 (.mul (.n 227) (.n 145) (.n 149)) (by decide +kernel)
    have m231 := a 62 (.mul (.n 228) (.n 227) (.n 153)) (by decide +kernel)
    have m232 := a 63 (.mul (.n 229) (.n 228) (.n 157)) (by decide +kernel)
    have m233 := a 64 (.mul (.n 230) (.n 46) (.n 226)) (by decide +kernel)
    have a234 := a 65 (.add (.n 231) (.n 229) (.n 230)) (by decide +kernel)
    have q := a 66 (.assertEq (.n 62) (.n 231)) (by decide +kernel)
    simp only [Atom.Holds, word_zero] at m219 m220 m221 c222 m223 a224 m225 m226 m227 m228
    simp only [Atom.Holds] at a229 m230 m231 m232 m233 a234 q
    have q' := e_add_eq_zero_iff.mp q
    rw [h63, a234, m233, a229, m228, a224, m223, c222, m221, m220, m219, m227, m226, m225, m232,
      m231, m230, h59,
      show σ (.n 145) = σ (.n 142) from cp 0 (by omega),
      show σ (.n 149) = σ (.n 146) from cp 1 (by omega),
      show σ (.n 153) = σ (.n 150) from cp 2 (by omega),
      show σ (.n 157) = σ (.n 154) from cp 3 (by omega),
      show σ (.n 174) = σ (.n 171) from cp 4 (by omega),
      show σ (.n 178) = σ (.n 175) from cp 5 (by omega),
      show σ (.n 182) = σ (.n 179) from cp 6 (by omega),
      show σ (.n 186) = σ (.n 183) from cp 7 (by omega),
      show σ (.n 203) = σ (.n 200) from cp 8 (by omega),
      show σ (.n 207) = σ (.n 204) from cp 9 (by omega),
      show σ (.n 211) = σ (.n 208) from cp 10 (by omega),
      show σ (.n 215) = σ (.n 212) from cp 11 (by omega)] at q'
    rw [q', hW, chWords_eq, chWords_eq, chWords_eq]
    simp only [chB, polyEval, prodE, List.foldr, List.foldl]
    ring
  have hstep := gkrStep_run (step := 2) le_rfl false (rt_sumcheck hpt _ 2 s.squeeze.2)
    (chWords_length σ 142 0) (chWords_length σ 142 1) (chWords_length σ 142 2) hcheck
  rw [show ((s.squeeze.2.absorbAll (chWords σ 142 0) dsObserve).absorbAll (chWords σ 142 1)
    dsObserve).absorbAll (chWords σ 142 2) dsObserve = sp from rfl, hsq1, hsq2] at hstep
  refine ⟨_, _, _, hstep, ?_, ?_⟩
  · intro k hk
    have hk12 : k < 12 := by simpa [chWords_length] using hk
    apply rt_read
    convert (EV k hk12).1 using 1
    simp only [List.nil_append, chWords_eq]
    interval_cases k <;> rfl
  -- the slot of `L = 2`
  have ld : ∀ k w, LoadHolds rd (σ (.n 139)) k w → LoadHolds rd (σ (.n 16)) (10 * 2 + k) w :=
    fun k w hw => by rw [h140, loadHolds_mul_gen_pow] at hw; exact hw
  have hcs := tb_holds_slice hnr h 71 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n (253 + k)) (.n 139) k)) (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hcs
  simp only [Atom.Holds] at hcs
  have l246 := a 69 (.load (.n 232) (.n 22) 40) (by decide +kernel)
  have l260 := a 70 (.load (.n 245) (.n 22) 41) (by decide +kernel)
  have c261 := a 76 (.const (.n 258) (word 16384 0)) (by decide +kernel)
  have m262 := a 77 (.mul (.n 259) (.n 5) (.n 258)) (by decide +kernel)
  have l262 := a 78 (.load (.n 259) (.n 139) 5) (by decide +kernel)
  have c290 := a 109 (.const (.n 287) (word 128 0)) (by decide +kernel)
  have l290 := a 110 (.load (.n 287) (.n 139) 9) (by decide +kernel)
  simp only [Atom.Holds] at l246 l260 c261 m262 l262 c290 l290
  rw [tb_word_128] at c290
  rw [show (16384 : ℕ) = 2 ^ 14 by norm_num, word_two_pow (by norm_num)] at c261
  have VAL : ∀ b off t, (b = 260 + 9 * t) → t < 3 →
      Stmt.HoldsList C rd σ (chValT 142 232 245 139 t b off) True kret →
      LoadHolds rd (σ (.n 139)) off (multilinearEval (W t) [σ (.n 232), σ (.n 245)]) := by
    intro b off t hb ht hv
    obtain ⟨ev, l⟩ := ch_val hv
    rw [ev] at l
    have hw : ∀ i < 4, σ (.n (chB 142 (4 * t + i) + 3)) = σ (.n (chB 142 (4 * t + i))) :=
      fun i hi => cp _ (by omega)
    rw [hw 0 (by omega), hw 1 (by omega), hw 2 (by omega), hw 3 (by omega)] at l
    rw [hW, chWords_eq]
    simpa using l
  refine ⟨by simp [lyCap], fun k hk => ?_, rfl, ?_, by simp, fun t ht => ?_, by simp, ?_, ?_⟩
  · have hg : ((lyCap 245).map σ).getD k 0 = σ (.n (253 + k)) := by
      simp [lyCap, List.getD_eq_getElem?_getD, hk]
    rw [hg]
    exact ld _ _ (hcs k hk)
  · rw [m262, c261] at l262
    have hlen : ([] ++ (chWords σ 142 0 ++ (chWords σ 142 1 ++ chWords σ 142 2))).length = 12 := by
      simp only [List.nil_append, List.length_append, chWords_length]
    rw [hlen, mul_assoc, ← pow_add]
    exact ld _ _ l262
  · rw [show 10 * 2 + 6 + t = 10 * 2 + (6 + t) by ring]
    apply ld
    have hv : ([W 0, W 1, W 2].map fun c ↦ multilinearEval c [σ (.n 232), σ (.n 245)]).getD t 0 =
        multilinearEval (W t) [σ (.n 232), σ (.n 245)] := by
      interval_cases t <;> rfl
    rw [hv]
    interval_cases t
    · exact VAL 260 6 0 rfl (by omega) (tb_holds_slice hnr h 79 _ (by decide +kernel))
    · exact VAL 269 7 1 rfl (by omega) (tb_holds_slice hnr h 89 _ (by decide +kernel))
    · exact VAL 278 8 2 rfl (by omega) (tb_holds_slice hnr h 99 _ (by decide +kernel))
  · simp only [List.append_nil]
    intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    rw [loadHolds_mul_gen_pow]
    interval_cases k
    · exact l246
    · exact l260
  · rw [c290] at l290; exact ld _ _ l290

end Sem

end
end LeanVM.Guest.B1.Tables
