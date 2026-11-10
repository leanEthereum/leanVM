/-
  LeanVM.Guest.B1.KeccakGkr.LayerCF

  `keccak_layer`'s tail, completely: the final check, the squeeze of `β`, the next claim's record,
  the return.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCE
public import LeanVM.Guest.B1.KeccakGkr.LayerCD

/-!
# The tail, completely

`layer_tail_complete`: on an evaluated valuation, with `t`'s packed cells and the capacity
canonical, the lane weights of the local point (at `loc`, in memory), and the honest final check,
`β` and the capacity are the squeeze's; and with the next claim's record (its value, its
pointers, its lanes and its flips) in memory, the tail holds and returns the capacity and the
cursor past `t`. The flips (`layerFlipT`) are computed from the stored lanes, the slice weights and the
top coordinate (`lflipT_holds`), and are the next claim's weights at the positions `ι` can flip
(`laterWeights_flip`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr LeanVM.Guest.B1.Fwd

@[expose] public section

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val}

/-- The tail up to the squeeze of `β`. -/
def tailP1 (W wv : ℕ) : List Stmt :=
  [.atom (.copy (.n W) (.n wv)), .atom (.mul (.n (W + 1)) (.n 1080) (.n W)),
    .atom (.mul (.n (W + 2)) (.n 958) (.n 1742)),
    .atom (.add (.n (W + 3)) (.n 958) (.n 1752)),
    .atom (.mul (.n (W + 4)) (.n (W + 3)) (.n 1762)),
    .atom (.add (.n (W + 5)) (.n (W + 2)) (.n (W + 4))),
    .atom (.mul (.n (W + 6)) (.n (W + 1)) (.n (W + 5))),
    .atom (.assertEq (.n (W + 6)) (.n 1741)),
    .atom (.const (.n (W + 7)) (word 0 0)), .atom (.const (.n (W + 8)) (word 0 0)),
    keccakA ([.n 1749, .n 1751, .n 1759, .n 1761, .n 1769, .n 1771, .n (W + 7), .n (W + 8)] ++
      cap5 1722) ((List.range 13).map fun k ↦ .n (W + 9 + k))]

/-- The next claim's value and pointers. -/
def tailP2 (W : ℕ) : List Stmt :=
  [.atom (.mul (.n (W + 29)) (.n (W + 28)) (.n 1762)),
    .atom (.add (.n (W + 30)) (.n 1752) (.n (W + 29))),
    .atom (.mul (.n (W + 31)) (.n (W + 28)) (.n (W + 30))),
    .atom (.add (.n (W + 32)) (.n 1742) (.n (W + 31))),
    .atom (.load (.n (W + 32)) (.n 12) 0), .atom (.load (.n 1052) (.n 12) 2),
    .atom (.load (.n 1081) (.n 12) 4), .atom (.hint (.alloc (.n (W + 33)) 25))]

/-- The local point's slice weights (its first five coordinates). -/
def tailEqf (W : ℕ) : List Stmt := eqfT (.n 1081) 0 5 32 (sliceB W)

/-- The top coordinate, `1 + top`, the flips' buffer. -/
def tailTop (W : ℕ) : List Stmt :=
  [.atom (.load (.n (topV W)) (.n 1081) 5), .atom (.const (.n (topV W + 1)) (word 1 0)),
    .atom (.add (.n (topV W + 2)) (.n (topV W + 1)) (.n (topV W))),
    .atom (.hint (.alloc (.n (topV W + 3)) 7))]

/-- The return's copies. -/
def tailP3 (W : ℕ) : List Stmt :=
  (List.range 5).map (fun j ↦ .atom (.copy (.n (topV W + 305 + j)) (.n (W + 17 + j)))) ++
  [.atom (.const (.n (topV W + 310)) (word 68719476736 0)),
    .atom (.mul (.n (topV W + 311)) (.n 1078) (.n (topV W + 310))),
    .atom (.copy (.n (topV W + 312)) (.n (topV W + 311)))]

/-- The tail before its flips. -/
def tailA1 (W wv : ℕ) : List Stmt :=
  tailP1 W wv ++ challengeT (.n (W + 9)) (.n (W + 10)) (W + 22) ++ tailP2 W ++
    lanesOutT (W + 28) laneW (W + 33) (W + 34) ++ [.atom (.load (.n (W + 33)) (.n 12) 3)] ++
    tailEqf W ++ tailTop W

/-- The tail after its flips, but its return. -/
def tailA3 (W : ℕ) : List Stmt := .atom (.load (.n (topV W + 3)) (.n 12) 5) :: tailP3 W

/-- The tail but its return. -/
def tailPre (W wv : ℕ) : List Stmt := tailA1 W wv ++ lflipsT W ++ tailA3 W

theorem tailT_split (W wv : ℕ) : tailT W wv = tailPre W wv ++
    [.ret [.n (topV W + 305), .n (topV W + 306), .n (topV W + 307), .n (topV W + 308),
      .n (topV W + 309), .n (topV W + 312)]] := by
  simp [tailT, tailPre, tailA1, tailA3, tailP1, tailP2, tailP3, tailEqf, tailTop, keccakA,
    List.append_assoc]

/-- The canonical inputs of the squeeze of `β`. -/
def tailA : List ℕ := [1749, 1751, 1759, 1761, 1769, 1771, 1722, 1723, 1724, 1725, 1726]

/-- The residual atoms of the tail before the slices' weights. -/
def tailR1 (W : ℕ) : List Atom :=
  [.assertEq (.n (W + 6)) (.n 1741), .assertInK (.n (W + 22)) (.n (W + 25)),
    .load (.n (W + 32)) (.n 12) 0, .load (.n 1052) (.n 12) 2, .load (.n 1081) (.n 12) 4] ++
  (List.range 25).map (fun i ↦ .load (.n (W + 37 + 4 * i)) (.n (W + 33)) i) ++
  [.load (.n (W + 33)) (.n 12) 3]

/-- Flip `i`'s first value. -/
def flipB (W i : ℕ) : ℕ := topV W + 4 + 43 * i

/-- Flip `i`'s block. -/
def layerFlipT (W i : ℕ) : List Stmt :=
  lflipT (.n (W + 33)) (eqfVal (sliceB W) 5 32 4) (topV W) (topV W + 2) i (flipB W i)

theorem lflipsT_eq (W : ℕ) : lflipsT W = ((List.range 7).map fun i ↦
    layerFlipT W i ++ [.atom (.load (.n (flipB W i + 42)) (.n (topV W + 3)) i)]).flatten := rfl

theorem tail_kernel {first : ℕ} (hf : first < 2) :
    (tailA1 (weightEnd first) (weightVal first)).all isAtom = true ∧
    canonChk tailA (atomsL ([] ++ tailA1 (weightEnd first) (weightVal first))) = true ∧
    resid (atomsL (tailA1 (weightEnd first) (weightVal first))) =
      tailR1 (weightEnd first) ++ resid (atomsL (tailEqf (weightEnd first))) ++
        [.load (.n (topV (weightEnd first))) (.n 1081) 5] ∧
    (tailEqf (weightEnd first)).all isAtom = true ∧
    canonChk [] (atomsL ([] ++ tailEqf (weightEnd first))) = true ∧
    (resid (atomsL (tailEqf (weightEnd first)))).all (ldIn [(.n 1081, 5)]) = true ∧
    (∀ i < 7, (layerFlipT (weightEnd first) i).all isAtom = true ∧
      canonChk [] (atomsL ([] ++ layerFlipT (weightEnd first) i)) = true ∧
      (resid (atomsL (layerFlipT (weightEnd first) i))).all
        (ldIn [(.n (weightEnd first + 33), 25)]) = true) ∧
    (tailA3 (weightEnd first)).all isAtom = true ∧
    canonChk [] (atomsL ([] ++ tailA3 (weightEnd first))) = true ∧
    resid (atomsL (tailA3 (weightEnd first))) =
      [.load (.n (topV (weightEnd first) + 3)) (.n 12) 5] ∧
    weightVal first < weightEnd first ∧ 1762 < weightEnd first ∧
    weightEnd first < topV (weightEnd first) ∧
    (List.range 25).all (fun j ↦ decide (laneW j < weightEnd first)) = true := by
  interval_cases first
  all_goals exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The squeeze of `β`: after the capacity of the last position round, `t`'s three words. -/
def tailSq (σ : Val) : E × Fs :=
  sq3 ((cap5 1722).map σ) (σ (.n 1742)) (σ (.n 1752)) (σ (.n 1762))

set_option maxRecDepth 20000 in
/-- **The tail, completely.** -/
theorem layer_tail_complete {first : ℕ} (hf : first < 2)
    (hσ : ∀ v, σ v = σ (.n v.idx))
    (hg : ∀ s ∈ tailPre (weightEnd first) (weightVal first), GoodS rd S w σ s)
    (hSe : ∀ a ∈ resid (atomsL (tailEqf (weightEnd first))), a ∉ S)
    (hSt : Atom.load (.n (topV (weightEnd first))) (.n 1081) 5 ∉ S)
    (hSf : ∀ i < 7, ∀ a ∈ resid (atomsL (layerFlipT (weightEnd first) i)), a ∉ S)
    (hSfl : ∀ i < 7, Atom.load (.n (flipB (weightEnd first) i + 42))
      (.n (topV (weightEnd first) + 3)) i ∈ S)
    (hA : ∀ i ∈ tailA, IsCanonical128 (σ (.n i)))
    (p1 : FsPackOk σ (.n 1742) (1742 + 1) dsObserve)
    (p2 : FsPackOk σ (.n 1752) (1752 + 1) dsObserve)
    (p3 : FsPackOk σ (.n 1762) (1762 + 1) dsObserve)
    {locPt : List E} (hlocL : locPt.length = 11) (hloc : ReadsAt rd (σ (.n 1081)) locPt)
    (hfw : ∀ i < 25, σ (.n (laneW i)) = eqAt (locPt.drop 6) i)
    (hfin : σ (.n 1080) * σ (.n (weightVal first)) * (σ (.n 958) * σ (.n 1742) +
      (σ (.n 958) + σ (.n 1752)) * σ (.n 1762)) = σ (.n 1741)) :
    σ (.n (weightEnd first + 28)) = (tailSq σ).1 ∧
      (cap5 (weightEnd first + 17)).map σ = (tailSq σ).2.cap ∧
      ∀ {next : Prop} {kret : List E → Prop},
        LoadHolds rd (σ (.n 12)) 0 (σ (.n 1742) + (tailSq σ).1 *
          (σ (.n 1752) + (tailSq σ).1 * σ (.n 1762))) →
        LoadHolds rd (σ (.n 12)) 2 (σ (.n 1052)) →
        LoadHolds rd (σ (.n 12)) 4 (σ (.n 1081)) →
        LoadHolds rd (σ (.n 12)) 3 (σ (.n (weightEnd first + 33))) →
        ReadsAt rd (σ (.n (weightEnd first + 33))) (lanesOut locPt (tailSq σ).1) →
        LoadHolds rd (σ (.n 12)) 5 (σ (.n (topV (weightEnd first) + 3))) →
        ReadsAt rd (σ (.n (topV (weightEnd first) + 3)))
          (flipsOf (laterWeights (lanesOut locPt (tailSq σ).1) (eqKernel (locPt.take 6)))) →
        kret ((cap5 (weightEnd first + 17)).map σ ++ [σ (.n 1078) * gen ^ 36]) →
        Stmt.HoldsList C rd σ (tailT (weightEnd first) (weightVal first)) next kret := by
  obtain ⟨hall, hk, hr, halle, hke, hre, hflk, hall3, hk3, hr3, hwv, h1762, hWt, hlw0⟩ :=
    tail_kernel hf
  generalize weightEnd first = W at *
  generalize weightVal first = wv at *
  have mem : ∀ s, s ∈ tailPre W wv → GoodS rd S w σ s := hg
  have mA1 : ∀ s ∈ tailA1 W wv, GoodS rd S w σ s := fun s hs ↦
    mem s (List.mem_append_left _ (List.mem_append_left _ hs))
  have mF : ∀ s ∈ lflipsT W, GoodS rd S w σ s := fun s hs ↦
    mem s (List.mem_append_left _ (List.mem_append_right _ hs))
  have mA3 : ∀ s ∈ tailA3 W, GoodS rd S w σ s := fun s hs ↦ mem s (List.mem_append_right _ hs)
  have mA1u := mA1
  unfold tailA1 at mA1u
  have g1 : ∀ s ∈ tailP1 W wv, GoodS rd S w σ s := fun s hs ↦ mA1u s (by simp [hs])
  have gc : ∀ s ∈ challengeT (.n (W + 9)) (.n (W + 10)) (W + 22), GoodS rd S w σ s :=
    fun s hs ↦ mA1u s (by simp [hs])
  have g2 : ∀ s ∈ tailP2 W, GoodS rd S w σ s := fun s hs ↦ mA1u s (by simp [hs])
  have gl : ∀ s ∈ lanesOutT (W + 28) laneW (W + 33) (W + 34), GoodS rd S w σ s :=
    fun s hs ↦ mA1u s (by simp [hs])
  have ge : ∀ s ∈ tailEqf W, GoodS rd S w σ s := fun s hs ↦ mA1u s (by simp [hs])
  have gt : ∀ s ∈ tailTop W, GoodS rd S w σ s := fun s hs ↦ mA1u s (by simp [hs])
  have g3 : ∀ s ∈ tailP3 W, GoodS rd S w σ s := fun s hs ↦ mA3 s (List.mem_cons_of_mem _ hs)
  -- the final check's values
  have g1' := g1
  simp only [tailP1, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true] at g1'
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, -, z0, z1, gk⟩ := g1'
  simp only [GoodS, Good] at e0 e3 e5 z0 z1
  have e1' := mul_good (by omega) (by omega) e1
  have e2' := mul_good (by omega) (by omega) e2
  have e4' := mul_good (by omega) (by omega) e4
  have e6' := mul_good (by omega) (by omega) e6
  -- the squeeze of `β`
  have zc : IsCanonical128 (word 0 0) := by
    rw [word_zero]; unfold IsCanonical128; exact limb_zero 2
  have hcanI : AllCanonical (([V.n 1749, .n 1751, .n 1759, .n 1761, .n 1769, .n 1771, .n (W + 7),
      .n (W + 8)] ++ cap5 1722).map σ) := by
    intro c hc
    simp only [cap5, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    have h' := fun i hi ↦ hA i hi
    simp only [tailA, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at h'
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := h'
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact a0
    · exact a1
    · exact a2
    · exact a3
    · exact a4
    · exact a5
    · rw [z0]; exact zc
    · rw [z1]; exact zc
    · exact a6
    · exact a7
    · exact a8
    · exact a9
    · exact a10
  have kc := keccakA_complete (show Good rd S w σ (.keccak _ ((List.range 13).map fun k ↦
    .n (W + 9 + k)) false false) from gk) hcanI
  obtain ⟨-, -, -, hout⟩ := keccak_outs kc
  have c10 : IsCanonical128 (σ (.n (W + 10))) := by
    have := hout 1 (by norm_num)
    simp only [range13_map, List.getD_cons_succ, List.getD_cons_zero] at this
    rw [this]; exact cellsOfState_canonical _ _ _
  obtain ⟨ch, -⟩ := challenge_complete (C := C) gc c10
  have hsq := sq3_atoms (a := 1742) (o := W + 9) (cap := (cap5 1722).map σ) p1
    (by simpa [Nat.add_assoc] using p2) (by simpa [Nat.add_assoc] using p3)
    (by simpa [cap5, Nat.add_assoc] using kc) (by simpa [Nat.add_assoc] using ch)
    (by rw [z0, word_zero]) (by rw [z1, word_zero]) rfl
  simp only [Nat.add_assoc, Nat.reduceAdd] at hsq
  have eβ : σ (.n (W + 28)) = (tailSq σ).1 := by
    rw [tailSq, sq3]; simpa [Nat.add_assoc] using hsq.1
  have ecap : (cap5 (W + 17)).map σ = (tailSq σ).2.cap := by
    rw [tailSq, sq3, ← hsq.2]
    simp [cap5, Nat.add_assoc]
  refine ⟨eβ, ecap, fun {next kret} ho0 ho2 ho4 ho3 hlan ho5 hfl hret ↦ ?_⟩
  -- the next claim's value
  have g2' := g2
  simp only [tailP2, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true] at g2'
  obtain ⟨f29, f30, f31, f32, -, -, -, -⟩ := g2'
  simp only [GoodS, Good] at f30 f32
  have f29' := mul_good (by omega) (by omega) f29
  have f31' := mul_good (by omega) (by omega) f31
  have ev : σ (.n (W + 32)) = σ (.n 1742) + (tailSq σ).1 *
      (σ (.n 1752) + (tailSq σ).1 * σ (.n 1762)) := by
    rw [f32, f31', f30, f29', eβ]
  -- the lanes' values
  have hlv : ∀ i < 25, σ (.n (W + 37 + 4 * i)) = (lanesOut locPt (tailSq σ).1).getD i 0 := by
    intro i hi
    have gi := fun s hs ↦ gl s (List.mem_flatten.mpr ⟨_, List.mem_map.mpr
      ⟨i, List.mem_range.mpr hi, rfl⟩, hs⟩)
    simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true] at gi
    obtain ⟨a0, a1, a2, a3, -⟩ := gi
    simp only [GoodS, Good] at a1 a3
    have hlw : ∀ j < 25, laneW j < W := fun j hj ↦ by
      have := List.all_eq_true.mp hlw0 j (List.mem_range.mpr hj)
      simpa using this
    have hl3 := hlw ((i % 5 + 3) % 5 + 5 * (i / 5)) (by omega)
    have a0' := mul_good (h := a0) (by omega) (by omega)
    have a2' := mul_good (h := a2) (by omega) (by omega)
    rw [show W + 34 + 4 * i + 3 = W + 37 + 4 * i by omega] at a3
    rw [a3, a2', a1, a0', eβ, hfw i hi, hfw _ (by omega), hfw _ (by omega)]
    simp only [lanesOut, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]
  -- the slices' values
  have hEq : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (tailEqf W) next kret :=
    block_holdsP (P := []) halle hσ hke (by simpa using ge) (A := []) (by simp)
      (resid_ldIn hre hSe fun q hq ↦ by
        simp only [List.mem_singleton] at hq
        subst hq
        exact ⟨locPt, hloc, by omega⟩)
  obtain ⟨⟨rs, hrsL, hrs, hent⟩, -⟩ := eqfT_holds (pt := .n 1081) (off := 0) (n := 5)
    (count := 32) (b := sliceB W) (by norm_num) (by norm_num) (by decide) (by decide)
    (hEq (kret := fun _ ↦ True) trivial)
  have hrs5 : rs = locPt.take 5 := by
    apply List.ext_getElem (by simp [hrsL, hlocL])
    intro k h1 h2
    have := hloc k (by omega)
    have h' := hrs k h1
    rw [Nat.zero_add] at h'
    rw [List.getElem_take]
    exact loadHolds_unique h' this
  -- the top coordinate
  have gt' := gt
  simp only [tailTop, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true] at gt'
  obtain ⟨t0, t1, t2, -⟩ := gt'
  simp only [GoodS, Good] at t1 t2
  have htop : σ (.n (topV W)) = locPt.getD 5 0 := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact load_val (w := w) t0 hSt (hloc 5 (by omega))
  -- the flips
  have hflips : ∀ {nx : Prop}, nx → Stmt.HoldsList C rd σ (lflipsT W) nx kret := by
    intro nx hnx
    rw [lflipsT_eq, holdsList_range_flatten _ _ (fun i ↦ by
      show Stmt.noRetList (lflipT _ _ _ _ i _ ++ _) = true
      rw [lflipBlk_noRet]; rfl)]
    refine ⟨fun i hi ↦ ?_, hnx⟩
    obtain ⟨hai, hki, hri⟩ := hflk i hi
    have mi : ∀ s ∈ layerFlipT W i ++ [.atom (.load (.n (flipB W i + 42)) (.n (topV W + 3)) i)],
        GoodS rd S w σ s := fun s hs ↦ mF s (by
      rw [lflipsT_eq]
      exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, hs⟩)
    have hFi : ∀ {nx' : Prop} {kr : List E → Prop}, nx' →
        Stmt.HoldsList C rd σ (layerFlipT W i) nx' kr :=
      block_holdsP (P := []) hai hσ hki (by simpa using fun s hs ↦ mi s (List.mem_append_left _ hs))
        (A := []) (by simp) (resid_ldIn hri (hSf i hi) fun q hq ↦ by
          simp only [List.mem_singleton] at hq
          subst hq
          exact ⟨_, hlan, by simp [lanesOut]⟩)
    obtain ⟨hv, -⟩ := lflipT_holds (lanesOut_length _ _) hlan (hFi (kr := fun _ ↦ True) trivial)
    rw [holdsList_append]
    refine hFi ?_
    simp only [Stmt.HoldsList, Stmt.Holds]
    refine ⟨?_, trivial⟩
    have gs := mi (.atom (.load (.n (flipB W i + 42)) (.n (topV W + 3)) i)) (by simp)
    refine holds_of_good (w := w) gs ?_
    simp only [Side]
    split
    · show LoadHolds rd _ _ _
      have hfi := hfl i (by simp [flipsOf]; omega)
      simp only [flipsOf, List.getElem_map, List.getElem_range] at hfi
      rw [laterWeights_flip _ _ (by simp [hlocL]) hi] at hfi
      convert hfi using 1
      rw [hv]
      refine congrArg List.sum (List.map_congr_left fun o ho ↦ ?_)
      rw [hent _ (Nat.mod_lt _ (by norm_num)), hrs5, List.take_take, show min 5 6 = 5 from rfl]
      congr 2
      simp only [topOf]
      rw [List.getD_eq_getElem _ _ (by simp [hlocL]), List.getElem_take,
        ← List.getD_eq_getElem _ 0 (by omega), ← htop]
      split
      · rfl
      · rw [t2, t1, word_one]
    · rename_i hnS
      exact absurd (hSfl i hi) hnS
  -- the return
  have g3' := g3
  simp only [tailP3, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_true, List.mem_map, List.mem_range,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at g3'
  obtain ⟨hcp, c10', c11', c12'⟩ := g3'
  simp only [GoodS, Good] at c10' c12'
  have c11'' := mul_good (by omega) (by omega) c11'
  have hcp' : ∀ j < 5, σ (.n (topV W + 305 + j)) = σ (.n (W + 17 + j)) := fun j hj ↦ by
    have := hcp j hj
    simpa [GoodS, Good] using this
  -- the blocks
  rw [tailT_split, tailPre, holdsList_append, holdsList_append, holdsList_append]
  refine block_holdsP (P := []) hall hσ hk (by simpa using mA1) hA ?_ (hflips ?_)
  · rw [hr]
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · simp only [tailR1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          List.mem_map, List.mem_range] at ha
        rcases ha with ((rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩) | rfl
        · left
          show σ (.n (W + 6)) + σ (.n 1741) = 0
          rw [e6', e1', e0, e5, e2', e4', e3, ← hfin]
          exact e_add_self _
        · exact Or.inl ⟨ch.2.2.2.1, ch.2.2.2.2.1⟩
        · left
          show LoadHolds rd _ _ _
          rw [ev]; exact ho0
        · exact Or.inl ho2
        · exact Or.inl ho4
        · left
          show LoadHolds rd _ _ _
          rw [hlv i hi]
          have := hlan i (by simp [lanesOut]; omega)
          rwa [List.getD_eq_getElem _ _ (by simp [lanesOut]; omega)]
        · exact Or.inl ho3
      · exact resid_ldIn hre hSe (fun q hq ↦ by
          simp only [List.mem_singleton] at hq
          subst hq
          exact ⟨locPt, hloc, by omega⟩) a ha
    · simp only [List.mem_singleton] at ha
      subst ha
      exact Or.inr (side_load hSt (hloc 5 (by omega)))
  · refine block_holdsP (P := []) hall3 hσ hk3 (by simpa using mA3) (A := []) (by simp) ?_ ?_
    · rw [hr3]
      intro a ha
      simp only [List.mem_singleton] at ha
      subst ha
      exact Or.inl ho5
    · simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil]
      convert hret using 1
      have h0 := hcp' 0 (by omega)
      have h1 := hcp' 1 (by omega)
      have h2 := hcp' 2 (by omega)
      have h3 := hcp' 3 (by omega)
      have h4 := hcp' 4 (by omega)
      simp only [Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] at h0 h1 h2 h3 h4
      simp only [cap5, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        Nat.add_assoc, Nat.reduceAdd, h0, h1, h2, h3, h4, c12', c11'', c10', word_2p36]

end
end LeanVM.Guest.B1.VerifySub
