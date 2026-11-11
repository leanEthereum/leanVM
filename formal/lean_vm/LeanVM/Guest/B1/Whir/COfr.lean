/-
  LeanVM.Guest.B1.Whir.COfr

  `opening_fold_round`, honestly: at `0` bits a call of `opening_fold`, at `b > 0` bits the
  nonce ground before the fold challenge.
-/

module

public import LeanVM.Guest.B1.Whir.CPrim
public import LeanVM.Guest.B1.Whir.HelperT

/-!
# `opening_fold_round`, honestly

`ofrZero_complete`: at `0` bits the specialization relates what `opening_fold` relates.
`ofr_complete`: at `b > 0` bits, on canonical capacity cells, the nonce and the next quadratic's
two words at the cursor, the nonce's permutation (`ofrS`, the nonce absorbed after the two waiting
scalars) passing `grind_check__L{b}`, it returns the capacity of the fold challenge's squeeze,
the cursor past the three words, the folded claim, the two words and the challenge.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-! ## At `0` bits -/

/-- **`opening_fold_round` at `0` bits, honestly.** -/
theorem ofrZero_complete {name : String} (hfn : FnIs name (osParams 11) ofrZeroBody)
    {args rets : List E} (ha : args.length = 11) (hr : rets.length = 10)
    (h : coreProgram.Rel rd "opening_fold" args rets) : coreProgram.Rel rd name args rets := by
  obtain ⟨fn, hf, hps, hb⟩ := hfn
  rw [rel_iff_sem hf]
  set σ := argVal (args ++ rets ++ rets) with hσ
  have hv : ∀ i, σ (.n i) = (args ++ rets ++ rets).getD i 0 := argVal_n _
  have ra : ∀ i < 11, σ (.n i) = args.getD i 0 := fun i hi ↦ by
    rw [hv, List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]
  have r1 : ∀ i < 10, σ (.n (11 + i)) = rets.getD i 0 := fun i hi ↦ by
    rw [hv, List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by omega)]
    congr 1; omega
  have r2 : ∀ i, σ (.n (21 + i)) = rets.getD i 0 := fun i ↦ by
    rw [hv, List.getD_append_right _ _ _ _ (by simp; omega)]
    congr 1; simp; omega
  have e1 : ((List.range 11).map V.n).map σ = args := by
    refine List.ext_getElem (by simp [ha]) fun j h1 h2 ↦ ?_
    simp only [List.getElem_map, List.getElem_range]
    rw [ra j (by simpa using h1), List.getD_eq_getElem _ _ h2]
  have e2 : ∀ o, o = 11 ∨ o = 21 → (osRun o 10).map σ = rets := by
    intro o ho
    refine List.ext_getElem (by simp [osRun, hr]) fun j h1 h2 ↦ ?_
    simp only [osRun, List.getElem_map, List.getElem_range]
    rcases ho with rfl | rfl
    · rw [r1 j (by simpa [osRun] using h1), List.getD_eq_getElem _ _ h2]
    · rw [r2 j, List.getD_eq_getElem _ _ h2]
  refine ⟨σ, by rw [hps]; exact e1, ?_⟩
  rw [hb, ofrZeroBody, holdsList_flat_ret _ (by simp [Stmt.flat])]
  refine ⟨?_, e2 21 (Or.inr rfl)⟩
  rw [allOk_append, allOk_cons]
  refine ⟨⟨by simp only [StmtOk]; rw [e1, e2 11 (Or.inl rfl)]; exact h, allOk_nil⟩, ?_⟩
  intro s hs
  simp only [List.mem_map, List.mem_range] at hs
  obtain ⟨i, hi, rfl⟩ := hs
  simp only [StmtOk, Atom.Holds]
  rw [r2 i, r1 i hi]

/-! ## At `b > 0` bits -/

/-- The permutation the nonce's absorb ends with: the two waiting scalars and the nonce over the
rate. -/
def ofrS (fs : List E) (w0 w1 nonce : E) : KeccakState :=
  (⟨fs, [(w0, dsObserve), (w1, dsObserve), (nonce, dsPowNonce)]⟩ : Fs).perm

/-- The fold challenge's squeeze from the nonce's permutation, nothing waiting. -/
def ofrS2 (fs : List E) (w0 w1 nonce : E) : KeccakState :=
  (⟨capOf (ofrS fs w0 w1 nonce), []⟩ : Fs).perm

/-- What `opening_fold_round` at `b > 0` bits returns. -/
def ofrRets (fs : List E) (w0 w1 cur c0 c1 c2 nonce d0 d2 : E) : List E :=
  let S2 := ofrS2 fs w0 w1 nonce
  let r := challengeOf S2
  capOf S2 ++ [cur * gen ^ 3, (c2 * r + c1) * r + c0, d0, d2, r]

/-- The values of `opening_fold_round` at `b > 0` bits, by segments. -/
def ofrSegs (fs : List E) (w0 w1 cur c0 c1 c2 nonce d0 d2 : E) : List (ℕ × (ℕ → E)) :=
  let S := ofrS fs w0 w1 nonce
  let S2 := ofrS2 fs w0 w1 nonce
  let r := challengeOf S2
  [(5, fun i ↦ fs.getD i 0), (6, fun i ↦ [w0, w1, cur, c0, c1, c2].getD i 0),
    (5, fun i ↦ fs.getD i 0), (9, fsPackVals w0 1), (9, fsPackVals w1 1), (1, fun _ ↦ nonce),
    (9, fsPackVals nonce 4), (2, fun _ ↦ word 0 0 0), (13, cells13F S),
    (5, fun i ↦ [word 1 0 0, word 0 0 0, word 0 0 0, word 0 0 0, word 0 0 0].getD i 0),
    (13, cells13F S2), (7, challengeVals (cells13F S2 0) (cells13F S2 1)),
    (4, fun i ↦ [c2 * r, c2 * r + c1, (c2 * r + c1) * r, (c2 * r + c1) * r + c0].getD i 0),
    (2, fun i ↦ [d0, d2].getD i 0), (5, fun i ↦ (capOf S2).getD i 0),
    (2, fun i ↦ [gw 3, cur * gw 3].getD i 0),
    (5, fun i ↦ [cur * gw 3, (c2 * r + c1) * r + c0, d0, d2, r].getD i 0)]

/-- `opening_fold_round`'s body at `b > 0` bits before its `ret`. -/
def ofrAtoms (b : ℕ) : List Stmt :=
  ((List.range 5).map fun i ↦ .atom (.copy (.n (11 + i)) (.n i))) ++
    fsPackT (.n 5) 16 1 ++ fsPackT (.n 6) 25 1 ++
    [.atom (.load (.n 34) (.n 7) 0)] ++ fsPackT (.n 34) 35 4 ++
    [.atom (.const (.n 44) (word 0 0 0)), .atom (.const (.n 45) (word 0 0 0)),
      keccakA ([22, 24, 31, 33, 41, 43, 44, 45, 11, 12, 13, 14, 15].map V.n) (osRun 46 13),
      .call ("grind_check__L" ++ natStr b) [.n 46] []] ++
    (osPad none 59).1 ++ osSqueeze0 59 [54, 55, 56, 57, 58] 64 ++
    [.atom (.mul (.n 84) (.n 10) (.n 83)), .atom (.add (.n 85) (.n 84) (.n 9)),
      .atom (.mul (.n 86) (.n 85) (.n 83)), .atom (.add (.n 87) (.n 86) (.n 8)),
      .atom (.load (.n 88) (.n 7) 1), .atom (.load (.n 89) (.n 7) 2)] ++
    ((List.range 5).map fun i ↦ .atom (.copy (.n (90 + i)) (.n (72 + i)))) ++
    [.atom (.const (.n 95) (gw 3)), .atom (.mul (.n 96) (.n 7) (.n 95)),
      .atom (.copy (.n 97) (.n 96)), .atom (.copy (.n 98) (.n 87)), .atom (.copy (.n 99) (.n 88)),
      .atom (.copy (.n 100) (.n 89)), .atom (.copy (.n 101) (.n 83))]

theorem ofrBody_atoms (b : ℕ) : ofrBody b =
    ofrAtoms b ++ [.ret [.n 90, .n 91, .n 92, .n 93, .n 94, .n 97, .n 98, .n 99, .n 100, .n 101]] := by
  simp [ofrBody, ofrAtoms]

/-- **`opening_fold_round` at `b > 0` bits, honestly**: on canonical capacity cells `fs`, the
nonce and the next quadratic's two words at the cursor, the nonce's permutation passing the
grinding check, the specialization returns `ofrRets`. -/
theorem ofr_complete {b : ℕ} {name : String} (hfn : FnIs name (osParams 11) (ofrBody b))
    {fs : List E} (hfl : fs.length = 5) (hcan : AllCanonical fs) {w0 w1 cur c0 c1 c2 nonce d0 d2 : E}
    (hrd : ReadsAt rd cur [nonce, d0, d2])
    (hgr : coreProgram.Rel rd ("grind_check__L" ++ natStr b)
      [cellsOfState (ofrS fs w0 w1 nonce) false 0] []) :
    coreProgram.Rel rd name (fs ++ [w0, w1, cur, c0, c1, c2])
      (ofrRets fs w0 w1 cur c0 c1 c2 nonce d0 d2) := by
  obtain ⟨fn, hf, hps, hb⟩ := hfn
  rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | ⟨f4, _ | ⟨f5, rest⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hfl <;> try omega
  set S := ofrS [f0, f1, f2, f3, f4] w0 w1 nonce with hS
  set S2 := ofrS2 [f0, f1, f2, f3, f4] w0 w1 nonce with hS2
  set r := challengeOf S2 with hr
  set segs := ofrSegs [f0, f1, f2, f3, f4] w0 w1 cur c0 c1 c2 nonce d0 d2 with hsegs
  set σ := segVal segs with hσ
  have hv : ∀ i, σ (.n i) = segLookup segs i := segVal_n segs
  have sv : ∀ (m : ℕ) (hm : m < segs.length) (o : ℕ), segLen (segs.take m) = o → ∀ i,
      i < segs[m].1 → σ (.n (o + i)) = segs[m].2 i := fun m hm o ho i hi ↦ by
    have := seg_val (σ := σ) (k := 0) (segs := segs) (fun j _ ↦ by rw [Nat.zero_add]; exact hv j)
      m hm o ho i hi
    rwa [Nat.zero_add] at this
  have g : ∀ i < 102, σ (.n i) = segLookup segs i := fun i _ ↦ hv i
  rw [rel_iff_sem hf]
  refine ⟨σ, ?_, ?_⟩
  · rw [hps]
    simp [osParams, List.range_succ, hv, hsegs, ofrSegs, segLookup]
  · rw [hb, ofrBody_atoms, holdsList_flat_ret _ (by simp [ofrAtoms, fsPackT, osPad, osSqueeze0, keccakA,
      challengeT, Stmt.flat])]
    have a : ∀ i < 5, σ (.n i) = [f0, f1, f2, f3, f4].getD i 0 := fun i hi ↦ by
      simpa [hsegs, ofrSegs] using sv 0 (by simp [hsegs, ofrSegs]) 0 (by simp [segLen]) i
        (by simp [hsegs, ofrSegs]; omega)
    have a0 : σ (.n 0) = f0 := by simpa using a 0 (by omega)
    have a1 : σ (.n 1) = f1 := by simpa using a 1 (by omega)
    have a2 : σ (.n 2) = f2 := by simpa using a 2 (by omega)
    have a3 : σ (.n 3) = f3 := by simpa using a 3 (by omega)
    have a4 : σ (.n 4) = f4 := by simpa using a 4 (by omega)
    have aw : ∀ i < 6, σ (.n (5 + i)) = [w0, w1, cur, c0, c1, c2].getD i 0 := fun i hi ↦ by
      simpa [hsegs, ofrSegs] using sv 1 (by simp [hsegs, ofrSegs]) 5
        (by simp [hsegs, ofrSegs, segLen]) i (by simp [hsegs, ofrSegs]; omega)
    have a5 : σ (.n 5) = w0 := by simpa using aw 0 (by omega)
    have a6 : σ (.n 6) = w1 := by simpa using aw 1 (by omega)
    have a7 : σ (.n 7) = cur := by simpa using aw 2 (by omega)
    have a8 : σ (.n 8) = c0 := by simpa using aw 3 (by omega)
    have a9 : σ (.n 9) = c1 := by simpa using aw 4 (by omega)
    have a10 : σ (.n 10) = c2 := by simpa using aw 5 (by omega)
    have vf : ∀ i < 5, σ (.n (11 + i)) = [f0, f1, f2, f3, f4].getD i 0 := fun i hi ↦ by
      simpa [hsegs, ofrSegs] using sv 2 (by simp [hsegs, ofrSegs]) 11
        (by simp [hsegs, ofrSegs, segLen]) i (by simp [hsegs, ofrSegs]; omega)
    have pw0 : ∀ i < 9, σ (.n (16 + i)) = fsPackVals (σ (.n 5)) 1 i := fun i hi ↦ by
      rw [a5]; simpa [hsegs, ofrSegs] using sv 3 (by simp [hsegs, ofrSegs]) 16
        (by simp [hsegs, ofrSegs, segLen]) i (by simp [hsegs, ofrSegs]; omega)
    have pw1 : ∀ i < 9, σ (.n (25 + i)) = fsPackVals (σ (.n 6)) 1 i := fun i hi ↦ by
      rw [a6]; simpa [hsegs, ofrSegs] using sv 4 (by simp [hsegs, ofrSegs]) 25
        (by simp [hsegs, ofrSegs, segLen]) i (by simp [hsegs, ofrSegs]; omega)
    have vn : σ (.n 34) = nonce := by
      simpa [hsegs, ofrSegs] using sv 5 (by simp [hsegs, ofrSegs]) 34
        (by simp [hsegs, ofrSegs, segLen]) 0 (by simp [hsegs, ofrSegs])
    have pn : ∀ i < 9, σ (.n (35 + i)) = fsPackVals (σ (.n 34)) 4 i := fun i hi ↦ by
      rw [vn]; simpa [hsegs, ofrSegs] using sv 6 (by simp [hsegs, ofrSegs]) 35
        (by simp [hsegs, ofrSegs, segLen]) i (by simp [hsegs, ofrSegs]; omega)
    have vz : ∀ i < 2, σ (.n (44 + i)) = word 0 0 0 := fun i hi ↦ by
      simpa [hsegs, ofrSegs] using sv 7 (by simp [hsegs, ofrSegs]) 44
        (by simp [hsegs, ofrSegs, segLen]) i (by simp [hsegs, ofrSegs]; omega)
    have vk : ∀ c < 13, σ (.n (46 + c)) = cells13F S c := fun c hc ↦ by
      simpa [hsegs, ofrSegs] using sv 8 (by simp [hsegs, ofrSegs]) 46
        (by simp [hsegs, ofrSegs, segLen]) c (by simp [hsegs, ofrSegs]; omega)
    have vp : ∀ i < 5, σ (.n (59 + i)) =
        [word 1 0 0, word 0 0 0, word 0 0 0, word 0 0 0, word 0 0 0].getD i 0 := fun i hi ↦ by
      simpa [hsegs, ofrSegs] using sv 9 (by simp [hsegs, ofrSegs]) 59
        (by simp [hsegs, ofrSegs, segLen]) i (by simp [hsegs, ofrSegs]; omega)
    have vk2 : ∀ c < 13, σ (.n (64 + c)) = cells13F S2 c := fun c hc ↦ by
      simpa [hsegs, ofrSegs] using sv 10 (by simp [hsegs, ofrSegs]) 64
        (by simp [hsegs, ofrSegs, segLen]) c (by simp [hsegs, ofrSegs]; omega)
    have vch : ∀ i < 7, σ (.n (77 + i)) = challengeVals (cells13F S2 0) (cells13F S2 1) i :=
      fun i hi ↦ by
        simpa [hsegs, ofrSegs] using sv 11 (by simp [hsegs, ofrSegs]) 77
          (by simp [hsegs, ofrSegs, segLen]) i (by simp [hsegs, ofrSegs]; omega)
    have vc : ∀ i < 4, σ (.n (84 + i)) =
        [c2 * r, c2 * r + c1, (c2 * r + c1) * r, (c2 * r + c1) * r + c0].getD i 0 := fun i hi ↦ by
      simpa [hsegs, ofrSegs] using sv 12 (by simp [hsegs, ofrSegs]) 84
        (by simp [hsegs, ofrSegs, segLen]) i (by simp [hsegs, ofrSegs]; omega)
    have vd : ∀ i < 2, σ (.n (88 + i)) = [d0, d2].getD i 0 := fun i hi ↦ by
      simpa [hsegs, ofrSegs] using sv 13 (by simp [hsegs, ofrSegs]) 88
        (by simp [hsegs, ofrSegs, segLen]) i (by simp [hsegs, ofrSegs]; omega)
    have vq : ∀ i < 5, σ (.n (90 + i)) = (capOf S2).getD i 0 := fun i hi ↦ by
      simpa [hsegs, ofrSegs] using sv 14 (by simp [hsegs, ofrSegs]) 90
        (by simp [hsegs, ofrSegs, segLen]) i (by simp [hsegs, ofrSegs]; omega)
    have vg : ∀ i < 2, σ (.n (95 + i)) = [gw 3, cur * gw 3].getD i 0 := fun i hi ↦ by
      simpa [hsegs, ofrSegs] using sv 15 (by simp [hsegs, ofrSegs]) 95
        (by simp [hsegs, ofrSegs, segLen]) i (by simp [hsegs, ofrSegs]; omega)
    have vr : ∀ i < 5, σ (.n (97 + i)) = [cur * gw 3, (c2 * r + c1) * r + c0, d0, d2, r].getD i 0 :=
      fun i hi ↦ by
        simpa [hsegs, ofrSegs] using sv 16 (by simp [hsegs, ofrSegs]) 97
          (by simp [hsegs, ofrSegs, segLen]) i (by simp [hsegs, ofrSegs]; omega)
    -- the packs
    obtain ⟨okw0, cw0, cw0'⟩ := fsPackT_complete (C := coreProgram.Rel rd) (rd := rd) pw0
    obtain ⟨okw1, cw1, cw1'⟩ := fsPackT_complete (C := coreProgram.Rel rd) (rd := rd) pw1
    obtain ⟨okn, cn, cn'⟩ := fsPackT_complete (C := coreProgram.Rel rd) (rd := rd) pn
    rw [a5] at cw0 cw0'; rw [a6] at cw1 cw1'; rw [vn] at cn cn'
    -- the nonce's permutation
    have hins : (([22, 24, 31, 33, 41, 43, 44, 45, 11, 12, 13, 14, 15] : List ℕ).map V.n).map σ =
        pendCells [(w0, dsObserve), (w1, dsObserve), (nonce, dsPowNonce)] ++ List.replicate 2 0 ++
          [f0, f1, f2, f3, f4] := by
      have z0 := vz 0 (by omega); have z1 := vz 1 (by omega)
      have q0 := vf 0 (by omega); have q1 := vf 1 (by omega); have q2 := vf 2 (by omega)
      have q3 := vf 3 (by omega); have q4 := vf 4 (by omega)
      simp only [Nat.add_zero, List.getD_cons_zero, List.getD_cons_succ, word_zero] at z0 z1 q0 q1 q2 q3 q4
      simp only [List.map_cons, List.map_nil]
      rw [cw0, cw0', cw1, cw1', cn, cn', z0, z1, q0, q1, q2, q3, q4]
      simp [pendCells, dsObserve, dsPowNonce, List.replicate]
    have hSe : permOf (pendCells [(w0, dsObserve), (w1, dsObserve), (nonce, dsPowNonce)] ++
        List.replicate 2 0 ++ [f0, f1, f2, f3, f4]) = S := by
      rw [hS, ofrS, perm_eq_cells _ (by simp)]; rfl
    have hk : (Atom.keccak (([22, 24, 31, 33, 41, 43, 44, 45, 11, 12, 13, 14, 15] : List ℕ).map V.n)
        (osRun 46 13) false false).Holds rd σ := by
      apply keccakA_of (by rfl) (by rfl)
      · rw [hins]
        intro x hx
        simp only [List.mem_append, List.mem_replicate] at hx
        rcases hx with (hx | hx) | hx
        · exact pendCells_canonical _ x hx
        · rw [hx.2, zero_eq_ofLimbs]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
        · exact hcan x hx
      · rw [hins, hSe]
        funext c
        simp only [cells13, osRun, List.map_map, Function.comp_def]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range c.isLt,
          Option.map_some, Option.getD_some]
        have := vk c.val c.isLt
        simp only [cells13F, c.isLt, ↓reduceDIte] at this
        exact this
    have v46 : σ (.n 46) = cellsOfState S false 0 := by simpa [cells13F] using vk 0 (by omega)
    -- the squeeze
    have hcm : ([54, 55, 56, 57, 58] : List ℕ).map (fun i ↦ σ (.n i)) = capOf S := by
      simp only [List.map_cons, List.map_nil, capOf]
      have e8 := vk 8 (by omega); have e9 := vk 9 (by omega); have e10 := vk 10 (by omega)
      have e11 := vk 11 (by omega); have e12 := vk 12 (by omega)
      simp only [cells13F, show (8 : ℕ) < 13 from by decide, show (9 : ℕ) < 13 from by decide,
        show (10 : ℕ) < 13 from by decide, show (11 : ℕ) < 13 from by decide,
        show (12 : ℕ) < 13 from by decide, ↓reduceDIte] at e8 e9 e10 e11 e12
      rw [e8, e9, e10, e11, e12]; rfl
    have hS2' : (⟨([54, 55, 56, 57, 58] : List ℕ).map (fun i ↦ σ (.n i)), []⟩ : Fs).perm = S2 := by
      rw [hcm, hS2, hS]; rfl
    have p1 := vp 1 (by omega); have p2 := vp 2 (by omega); have p3 := vp 3 (by omega)
    have p4 := vp 4 (by omega)
    simp only [List.getD_cons_zero, List.getD_cons_succ, word_zero] at p1 p2 p3 p4
    have k0 : σ (.n 64) = cellsOfState S2 false 0 := by simpa [cells13F] using vk2 0 (by omega)
    have k1 : σ (.n 65) = cellsOfState S2 false 1 := by simpa [cells13F] using vk2 1 (by omega)
    have hsq := osSqueeze0_complete (C := coreProgram.Rel rd) (rd := rd) (σ := σ) (p := 59)
      (cap := [54, 55, 56, 57, 58]) (j := 64) rfl ⟨p1, p2, p3, p4⟩
      (by rw [hcm]; exact capOf_canonical _) (fun c hc ↦ by rw [hS2']; exact vk2 c hc)
      (fun i hi ↦ by
        rw [k0, k1, show 64 + 13 + i = 77 + i by ring, vch i hi, cells13F, cells13F]; simp)
    rw [hS2'] at hsq
    have v83 : σ (.n 83) = r := hsq.2
    have c0' := vc 0 (by omega); have c1' := vc 1 (by omega); have c2' := vc 2 (by omega)
    have c3' := vc 3 (by omega)
    have d0' := vd 0 (by omega); have d1' := vd 1 (by omega)
    have g0 := vg 0 (by omega); have g1 := vg 1 (by omega)
    have r0 := vr 0 (by omega); have r1 := vr 1 (by omega); have r2 := vr 2 (by omega)
    have r3 := vr 3 (by omega); have r4 := vr 4 (by omega)
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at c0' c1' c2' c3' d0' d1'
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at g0 g1 r0 r1 r2 r3 r4
    have hq : ∀ i < 5, σ (.n (90 + i)) = σ (.n (72 + i)) := fun i hi ↦ by
      rw [vq i hi, show 72 + i = 64 + (8 + i) by ring, vk2 _ (by omega)]
      interval_cases i <;> simp [capOf, cells13F]
    refine ⟨?_, ?_⟩
    · simp only [ofrAtoms, allOk_append]
      refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, okw0⟩, okw1⟩, ?_⟩, okn⟩, ?_⟩, ?_⟩, hsq.1⟩, ?_⟩, ?_⟩, ?_⟩
      · intro s hs
        simp only [List.mem_map, List.mem_range] at hs
        obtain ⟨i, hi, rfl⟩ := hs
        simp only [StmtOk, Atom.Holds]
        rw [vf i hi, a i hi]
      · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
        rw [vn, a7]; exact hrd 0 (by simp)
      · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds, List.map_cons, List.map_nil]
        refine ⟨by simpa using vz 0 (by omega), by simpa using vz 1 (by omega), hk, ?_⟩
        rw [v46]; exact hgr
      · simp only [osPad, allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
        have p0 := vp 0 (by omega)
        simp only [List.getD_cons_zero, Nat.add_zero] at p0
        exact ⟨p0, by rw [p1, word_zero], by rw [p2, word_zero], by rw [p3, word_zero],
          by rw [p4, word_zero]⟩
      · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
        refine ⟨by rw [c0', a10, v83], by rw [c1', c0', a9], by rw [c2', c1', v83],
          by rw [c3', c2', a8], ?_, ?_⟩
        · rw [d0', a7]; exact hrd 1 (by simp)
        · rw [d1', a7]; exact hrd 2 (by simp)
      · intro s hs
        simp only [List.mem_map, List.mem_range] at hs
        obtain ⟨i, hi, rfl⟩ := hs
        simp only [StmtOk, Atom.Holds]
        exact hq i hi
      · simp only [allOk_cons, allOk_nil, and_true, StmtOk, Atom.Holds]
        exact ⟨g0, by rw [g1, a7, g0], by rw [r0, g1], by rw [r1, c3'], by rw [r2, d0'],
          by rw [r3, d1'], by rw [r4, v83]⟩
    · have q0 := vq 0 (by omega); have q1 := vq 1 (by omega); have q2 := vq 2 (by omega)
      have q3 := vq 3 (by omega); have q4 := vq 4 (by omega)
      simp only [Nat.add_zero] at q0
      simp only [List.map_cons, List.map_nil, ofrRets, ← hS2, ← hr]
      rw [q0, q1, q2, q3, q4, r0, r1, r2, r3, r4, gw_eq (by decide)]
      simp [capOf]

end
end LeanVM.Guest.B1.Whir
