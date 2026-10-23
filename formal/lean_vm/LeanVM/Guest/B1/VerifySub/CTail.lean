/-
  LeanVM.Guest.B1.VerifySub.CTail

  `verify_sub`'s last blocks, complete: the batching, the stack's size with the opening and the
  terminal, and the exported claims.
-/

module

public import LeanVM.Guest.B1.VerifySub.CRing

/-!
# The batching, the opening and `defer_out`, complete (G:2211-2280)
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

variable {C : CallRel} {rd : Reader} {D : VsData} {P : VsPtrs} {out : E} {bytecode : List K}

/-! ## The batching -/

/-- The claims' values. -/
def vals (D : VsData) : List E := D.claims.map (·.value)

/-- The running target after claim `j`. -/
def lamT (D : VsData) (j : ℕ) : E :=
  ringTarget D.s D.mcs + ((List.range (j + 1)).map fun i ↦ D.lam ^ (i + 1) * (vals D).getD i 0).sum

theorem lpP_succ (j : ℕ) : lpP (j + 1) = 1184 + 4 * j := by simp [lpP]

theorem lpT_succ (j : ℕ) : lpT (j + 1) = 1187 + 4 * j := by simp [lpT, lpP]; omega

theorem lpP_lt (j : ℕ) : lpP j < 1184 + 4 * j ∧ 1180 ≤ lpP j ∨ lpP j = 1179 := by
  unfold lpP; split <;> omega

theorem lpT_lt (j : ℕ) : lpT j < 1184 + 4 * j ∧ 1183 ≤ lpT j := by
  unfold lpT lpP; split <;> omega

theorem numBelow_lp : ∀ j < 111, NumBelow (1184 + 4 * (j + 1)) (Stmt.valsList (lpBlk j)) :=
  fun j hj => numBelow_of_B (by revert j hj; decide +kernel)

/-- **Claim `j + 1` of the batching** (G:2224-2228). -/
theorem c_lpBlk {j : ℕ} (hj : j < 111) (hv : ReadsAt rd P.pool (vals D))
    (hvl : (vals D).length = 112) (hlp : ReadsAt rd P.lam (powersFrom D.lam D.lam 112)) (σ : Val)
    (hσ : σ (.n 1179) = D.lam ∧ σ (.n 1180) = P.lam ∧ σ (.n 7) = P.pool ∧
      σ (.n (lpP j)) = D.lam ^ (j + 1) ∧ σ (.n (lpT j)) = lamT D j) :
    Completes C rd (1184 + 4 * j) (1184 + 4 * (j + 1)) (lpBlk j) σ (fun σ' =>
      σ' (.n 1179) = D.lam ∧ σ' (.n 1180) = P.lam ∧ σ' (.n 7) = P.pool ∧
        σ' (.n (lpP (j + 1))) = D.lam ^ (j + 1 + 1) ∧ σ' (.n (lpT (j + 1))) = lamT D (j + 1)) := by
  obtain ⟨h1179, h1180, h7, hP, hT⟩ := hσ
  have hpl := lpP_lt j
  have htl := lpT_lt j
  have nP : ∀ i < 4, lpP j ≠ 1184 + 4 * j + i := fun i _ => by omega
  have nT : ∀ i < 4, lpT j ≠ 1184 + 4 * j + i := fun i _ => by omega
  have hvj : LoadHolds rd P.pool (j + 1) ((vals D).getD (j + 1) 0) := readsAt_getD hv (by omega)
  have hlj : LoadHolds rd P.lam (j + 1) (D.lam ^ (j + 1 + 1)) := by
    have := readsAt_getD hlp (k := j + 1) (by rw [length_powersFrom]; omega)
    rwa [getD_powersFrom _ _ _ _ (by omega), ← pow_succ'] at this
  refine completes_upds [(1184 + 4 * j, D.lam ^ (j + 1 + 1)), (1185 + 4 * j, (vals D).getD (j + 1) 0),
    (1186 + 4 * j, D.lam ^ (j + 1 + 1) * (vals D).getD (j + 1) 0), (1187 + 4 * j, lamT D (j + 1))]
    (by simp; omega) (fun next kret hn => ?_) ?_
  · simp only [lpBlk, lpP_succ, lpT_succ, Stmt.HoldsList, Stmt.Holds, Atom.Holds, upds_n, upds_nil]
    simp only [show 1184 + 4 * j + 1 = 1185 + 4 * j by omega, show 1184 + 4 * j + 2 = 1186 + 4 * j by omega,
      show (1179 : ℕ) ≠ 1184 + 4 * j by omega, show (1179 : ℕ) ≠ 1185 + 4 * j by omega,
      show (1179 : ℕ) ≠ 1186 + 4 * j by omega, show (1179 : ℕ) ≠ 1187 + 4 * j by omega,
      show (1180 : ℕ) ≠ 1184 + 4 * j by omega, show (1180 : ℕ) ≠ 1185 + 4 * j by omega,
      show (1180 : ℕ) ≠ 1186 + 4 * j by omega, show (1180 : ℕ) ≠ 1187 + 4 * j by omega,
      show (7 : ℕ) ≠ 1184 + 4 * j by omega, show (7 : ℕ) ≠ 1185 + 4 * j by omega,
      show (7 : ℕ) ≠ 1186 + 4 * j by omega, show (7 : ℕ) ≠ 1187 + 4 * j by omega,
      show lpP j ≠ 1184 + 4 * j by omega, show lpP j ≠ 1185 + 4 * j by omega,
      show lpP j ≠ 1186 + 4 * j by omega, show lpP j ≠ 1187 + 4 * j by omega,
      show lpT j ≠ 1184 + 4 * j by omega, show lpT j ≠ 1185 + 4 * j by omega,
      show lpT j ≠ 1186 + 4 * j by omega, show lpT j ≠ 1187 + 4 * j by omega,
      show 1185 + 4 * j ≠ 1184 + 4 * j by omega, show 1186 + 4 * j ≠ 1184 + 4 * j by omega,
      show 1186 + 4 * j ≠ 1185 + 4 * j by omega, show 1187 + 4 * j ≠ 1184 + 4 * j by omega,
      show 1187 + 4 * j ≠ 1185 + 4 * j by omega, show 1187 + 4 * j ≠ 1186 + 4 * j by omega,
      ↓reduceIte, h1179, h1180, h7, hP, hT]
    refine ⟨by rw [← pow_succ], hlj, hvj, by vs_triv, ?_, hn⟩
    unfold lamT
    rw [List.range_succ (n := j + 1)]
    simp [add_assoc]
  · simp only [lpP_succ, lpT_succ, upds_n, upds_nil,
      show (1179 : ℕ) ≠ 1184 + 4 * j by omega, show (1179 : ℕ) ≠ 1185 + 4 * j by omega,
      show (1179 : ℕ) ≠ 1186 + 4 * j by omega, show (1179 : ℕ) ≠ 1187 + 4 * j by omega,
      show (1180 : ℕ) ≠ 1184 + 4 * j by omega, show (1180 : ℕ) ≠ 1185 + 4 * j by omega,
      show (1180 : ℕ) ≠ 1186 + 4 * j by omega, show (1180 : ℕ) ≠ 1187 + 4 * j by omega,
      show (7 : ℕ) ≠ 1184 + 4 * j by omega, show (7 : ℕ) ≠ 1185 + 4 * j by omega,
      show (7 : ℕ) ≠ 1186 + 4 * j by omega, show (7 : ℕ) ≠ 1187 + 4 * j by omega,
      show 1187 + 4 * j ≠ 1184 + 4 * j by omega, show 1187 + 4 * j ≠ 1185 + 4 * j by omega,
      show 1187 + 4 * j ≠ 1186 + 4 * j by omega, ↓reduceIte, h1179, h1180, h7]
    exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-- The values the batching reads and leaves. -/
def lamIn (D : VsData) (P : VsPtrs) : List (ℕ × E) :=
  [(7, P.pool), (810, (digestScalars D.cvM).1), (811, (digestScalars D.cvM).2),
    (1150, ringTarget D.s D.mcs)]

def lamOut (D : VsData) (P : VsPtrs) : List (ℕ × E) :=
  [(1171, (digestScalars D.cvL).1), (1172, (digestScalars D.cvL).2), (1180, P.lam), (1627, D.target)]

theorem bLam_eq : bLam = squeezeT (.n 810) (.n 811) 1166 ++
    [.atom (.hint (.alloc (.n 1180) 112)), .atom (.load (.n 1179) (.n 1180) 0),
      .atom (.load (.n 1181) (.n 7) 0), .atom (.mul (.n 1182) (.n 1179) (.n 1181)),
      .atom (.add (.n 1183) (.n 1150) (.n 1182))] ++
    ((List.range 111).map lpBlk).flatten ++ [.atom (.mul (.n 1628) (.n 1624) (.n 1179))] := rfl

theorem target_eq (hl : D.claims.length = 112) : D.target = lamT D 111 := by
  have hvl : (vals D).length = 112 := by simp [vals, hl]
  rw [VsData.target, show D.claims.length = (vals D).length by simp [vals], show
    ringTarget D.s D.mcs :: D.claims.map (·.value) = ringTarget D.s D.mcs :: vals D from rfl,
    dot_powers_cons, hvl, lamT]

/-- **The batching** (G:2219-2229): `lam`, its powers stored, the opening's target. -/
theorem c_lam (hcl : D.claims.length = 112) (hm : VsMem0 rd D P out) (σ : Val)
    (hσ : Fixes σ (lamIn D P)) :
    Completes C rd 1166 1629 bLam σ (fun σ' => Fixes σ' (lamOut D P)) := by
  have hvl : (vals D).length = 112 := by simp [vals, hcl]
  have hv : ReadsAt rd P.pool (vals D) := hm.pool
  have hlp : ReadsAt rd P.lam (powersFrom D.lam D.lam 112) := hm.lam
  have h7 : σ (.n 7) = P.pool := hσ.get (by simp [lamIn])
  have h1150 : σ (.n 1150) = ringTarget D.s D.mcs := hσ.get (by simp [lamIn])
  rw [bLam_eq]
  refine Completes.append (m := 1628) (P := fun σ' => (σ' (.n 1179) = D.lam ∧ σ' (.n 1180) = P.lam ∧
      σ' (.n 7) = P.pool ∧ σ' (.n (lpP 111)) = D.lam ^ (111 + 1) ∧ σ' (.n (lpT 111)) = lamT D 111) ∧
      Fixes σ' [(1171, (digestScalars D.cvL).1), (1172, (digestScalars D.cvL).2)])
    (by omega) (by omega) (numBelow_of_B (by decide +kernel)) ?_ fun σ3 _ ⟨⟨j1179, j1180, _, jP, jT⟩, jf⟩ => ?_
  · refine Completes.append (m := 1184) (P := fun σ' => (σ' (.n 1179) = D.lam ∧ σ' (.n 1180) = P.lam ∧
        σ' (.n 7) = P.pool ∧ σ' (.n (lpP 0)) = D.lam ^ (0 + 1) ∧ σ' (.n (lpT 0)) = lamT D 0) ∧
        Fixes σ' [(1171, (digestScalars D.cvL).1), (1172, (digestScalars D.cvL).2)])
      (by omega) (by omega) (numBelow_of_B (by decide +kernel)) ?_ fun σ2 _ ⟨hi, jf⟩ => ?_
    · refine Completes.append (m := 1180) (P := fun σ' => (σ' (.n 1171), σ' (.n 1172)) =
          digestScalars D.cvL ∧ σ' (.n 1179) = D.lam ∧ σ' (.n 7) = P.pool ∧
          σ' (.n 1150) = ringTarget D.s D.mcs)
        (by omega) (by omega) (numBelow_of_B (by decide +kernel)) ?_ fun σ1 _ ⟨k1171, k1179, k7, k1150⟩ => ?_
      · exact completes_squeezeT (b := 1166) ⟨810, by omega, rfl⟩ ⟨811, by omega, rfl⟩
          (by rw [hσ.get (k := 810) (e := (digestScalars D.cvM).1) (by simp [lamIn]),
            hσ.get (k := 811) (e := (digestScalars D.cvM).2) (by simp [lamIn])])
          fun σ' e h5 h13 => ⟨h5, h13, by rw [e.apply (by omega)]; exact h7,
            by rw [e.apply (by omega)]; exact h1150⟩
      · have hv0 : LoadHolds rd P.pool 0 ((vals D).getD 0 0) := readsAt_getD hv (by omega)
        have hl0 : LoadHolds rd P.lam 0 D.lam := by
          have := readsAt_getD hlp (k := 0) (by rw [length_powersFrom]; omega)
          rwa [getD_powersFrom _ _ _ _ (by omega), pow_zero, mul_one] at this
        refine completes_upds [(1180, P.lam), (1181, (vals D).getD 0 0), (1182, D.lam * (vals D).getD 0 0),
          (1183, ringTarget D.s D.mcs + D.lam * (vals D).getD 0 0)] (by simp) (fun next kret hn => ?_) ?_
        · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
          vs_ev
          rw [k1179, k7, k1150]
          exact ⟨trivial, hl0, hv0, by vs_triv, by vs_triv, hn⟩
        · refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · vs_ev; exact k1179
          · vs_ev
          · vs_ev; exact k7
          · simp only [lpP, ↓reduceIte]; vs_ev; rw [k1179]; simp
          · simp only [lpT, ↓reduceIte]; vs_ev; simp [lamT]
          · intro p hp
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
            rcases hp with rfl | rfl <;> vs_ev
            · exact congrArg Prod.fst k1171
            · exact congrArg Prod.snd k1171
    · have key := Completes.flatten (C := C) (rd := rd) (blk := lpBlk) (st := fun j ↦ 1184 + 4 * j)
        (Inv := fun j σ' ↦ σ' (.n 1179) = D.lam ∧ σ' (.n 1180) = P.lam ∧ σ' (.n 7) = P.pool ∧
          σ' (.n (lpP j)) = D.lam ^ (j + 1) ∧ σ' (.n (lpT j)) = lamT D j) 111 (fun _ _ => by omega)
        numBelow_lp (fun j hj σ' h => c_lpBlk hj hv hvl hlp σ' h) σ2 hi
      exact key.keep jf (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> simp)
  · refine completes_upds [(1628, D.lam ^ (111 + 1) * D.lam)] (by simp) (fun next kret hn => ?_) ?_
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
      vs_ev
      rw [show (1624 : ℕ) = lpP 111 from rfl, jP, j1179]
      exact ⟨rfl, hn⟩
    · intro p hp
      simp only [lamOut, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> vs_ev
      · exact jf.get (by simp)
      · exact jf.get (by simp)
      · exact j1180
      · rw [show (1627 : ℕ) = lpT 111 from rfl, jT, target_eq hcl]

/-! ## The stack's size, the opening and the terminal -/

/-- The values the opening block reads. -/
def openIn (D : VsData) (P : VsPtrs) (lp sq : E) : List (ℕ × E) :=
  [(4, lp), (5, sq), (8, P.cplen), (138, gen ^ (D.rate - 1)), (144, gen ^ D.logMem), (155, P.kbase),
    (417, gen ^ log2Ceil D.pushTotal), (418, P.zeta), (419, D.x0), (434, D.x1), (709, P.chi),
    (713, D.gzcn), (715, D.rm), (718, gen ^ D.tau), (726, curW D P), (733, P.ctab), (734, P.zvals),
    (1171, (digestScalars D.cvL).1), (1172, (digestScalars D.cvL).2), (1180, P.lam), (1627, D.target)]

theorem openNames_getD {j : ℕ} (hj : j < 28) : openNames.getD j "" = openNames[j]'(by simp [openNames]; omega) :=
  List.getD_eq_getElem _ _ _

/-- **The stack's size, the opening and the terminal** (G:2231-2263). -/
theorem c_open (hlow : LowDef 6 rd) {bytecode : List K} {lp sq : E}
    (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) (hC : VsCallsOk C bytecode D P lp sq)
    (σ : Val) (hσ : Fixes σ (openIn D P lp sq)) :
    Completes C rd 1629 1652 bOpen σ (fun _ => True) := by
  have e : ∀ k e, (k, e) ∈ openIn D P lp sq → σ (.n k) = e := fun k e h => hσ.get h
  set μ := (layoutOf bytecode D.logMem D.rows).stackLog with hμ
  have hμe : μ = max 15 (log2Ceil D.stackTot) := stackLog_eq hb _ _
  have h1 := hok.stack_ge
  have h2 := hok.stack_le
  have hr1 := hok.rate_ge
  have hr2 := hok.rate_le
  set r := D.rate
  set sel := μ - 22 + 7 * (r - 1)
  have hsel : sel < 28 := by omega
  refine completes_upds [(1629, gen ^ D.stackTot), (1630, P.off), (1631, P.kap), (1632, gen ^ μ),
    (1633, word 8198552432976855044 0 0), (1634, gen ^ (μ - 22)), (1635, word 64 0 0),
    (1636, (rcLow rd (μ - 22) 7).1), (1637, (rcLow rd (μ - 22) 7).2.1),
    (1638, (rcLow rd (μ - 22) 7).2.2), (1639, gen ^ (r - 1) * gen ^ (r - 1)),
    (1640, gen ^ (r - 1) * gen ^ (r - 1) * gen ^ (r - 1)),
    (1641, gen ^ (r - 1) * gen ^ (r - 1) * gen ^ (r - 1) * (gen ^ (r - 1) * gen ^ (r - 1) * gen ^ (r - 1))),
    (1642, gen ^ (r - 1) * gen ^ (r - 1) * gen ^ (r - 1) * (gen ^ (r - 1) * gen ^ (r - 1) * gen ^ (r - 1)) *
      gen ^ (r - 1)), (1643, gen ^ sel), (1644, word 134217728 0 0),
    (1645, (rcLow rd sel 28).1), (1646, (rcLow rd sel 28).2.1),
    (1647, (rcLow rd sel 28).2.2), (1648, D.w.target), (1649, P.pt), (1650, D.w.inner),
    (1651, D.w.residual)] (by simp) (fun next kret hn => ?_) trivial
  simp only [bOpen, Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hn⟩
  · vs_ev; rw [e 155 P.kbase (by simp [openIn]), e 5 sq (by simp [openIn])]; exact hC.certify
  · vs_ev
    rw [e 4 lp (by simp [openIn]), e 5 sq (by simp [openIn]), hμe]
    exact hC.log2Stack
  · simp only [Atom.Holds]; vs_ev
  · simp only [Atom.Holds]; vs_ev
    conv_rhs => rw [show μ = (μ - 22) + 22 by omega, pow_add, mul_assoc, mul_comm (gen ^ 22),
      minShiftInv, mul_one]
  · simp only [Atom.Holds]; vs_ev
  · exact rc_holds_low hlow (K := 7) (e := μ - 22) (by omega) (by omega) (by vs_ev)
      (by vs_ev) (by vs_ev) (by vs_ev) (by vs_ev; exact word_two_pow (a := 6) (by decide))
  · simp only [Atom.Holds]; vs_ev; rw [e 138 (gen ^ (r - 1)) (by simp [openIn, r])]
  · simp only [Atom.Holds]; vs_ev; rw [e 138 (gen ^ (r - 1)) (by simp [openIn, r])]
  · simp only [Atom.Holds]; vs_ev
  · simp only [Atom.Holds]; vs_ev; rw [e 138 (gen ^ (r - 1)) (by simp [openIn, r])]
  · simp only [Atom.Holds]; vs_ev
    simp only [← pow_add]; congr 1; omega
  · simp only [Atom.Holds]; vs_ev
  · exact rc_holds_low hlow (K := 28) (e := sel) (by omega) hsel (by vs_ev)
      (by vs_ev) (by vs_ev) (by vs_ev) (by vs_ev; exact word_two_pow (a := 27) (by decide))
  · vs_ev
    refine ⟨sel, by simp [openNames]; omega, by rw [gen_pow_eq_ofK], ?_⟩
    rw [e 1171 (digestScalars D.cvL).1 (by simp [openIn]), e 1172 (digestScalars D.cvL).2 (by simp [openIn]), e 1627 D.target (by simp [openIn]),
      e 419 D.x0 (by simp [openIn]), e 434 D.x1 (by simp [openIn]), e 726 (curW D P) (by simp [openIn])]
    have hn : openNames[sel]'(by simp [openNames]; omega) = openName μ r := by
      rw [openName, ← openNames_getD (by omega)]
    rw [hn]
    exact hC.opening
  · vs_ev
    rw [e 418 P.zeta (by simp [openIn]), e 709 P.chi (by simp [openIn]), e 715 D.rm (by simp [openIn]),
      e 417 (gen ^ log2Ceil D.pushTotal) (by simp [openIn]), e 713 D.gzcn (by simp [openIn]), e 144 (gen ^ D.logMem) (by simp [openIn]),
      e 718 (gen ^ D.tau) (by simp [openIn]), e 8 P.cplen (by simp [openIn]), e 1180 P.lam (by simp [openIn]),
      e 734 P.zvals (by simp [openIn]), e 733 P.ctab (by simp [openIn])]
    exact hC.terminal

/-! ## `defer_out` -/

/-- **A copy into `defer_out`**: `src[i]`, through the fresh value `v`, at `defer_out[j]`. -/
theorem c_cpBlk {v i j : ℕ} {src : ℕ} (hs : src < v) (hv : 6 < v) {ps w : E}
    (hi : LoadHolds rd ps i w) (hj : LoadHolds rd out j w) (σ : Val) (hsrc : σ (.n src) = ps)
    (h6 : σ (.n 6) = out) :
    Completes C rd v (v + 1) (cpBlk v (.n src) i j) σ
      (fun σ' => σ' (.n src) = ps ∧ σ' (.n 6) = out) := by
  refine completes_upds [(v, w)] (by simp) (fun next kret hn => ?_) ?_
  · simp only [cpBlk, Stmt.HoldsList, Stmt.Holds, Atom.Holds, upds_n, upds_nil,
      show src ≠ v by omega, show (6 : ℕ) ≠ v by omega, ↓reduceIte, hsrc, h6]
    exact ⟨hi, hj, hn⟩
  · simp only [upds_n, upds_nil, show src ≠ v by omega, show (6 : ℕ) ≠ v by omega, ↓reduceIte, hsrc,
      h6, and_self]

theorem getD_take' {xs : List E} {n k : ℕ} (hk : k < n) (hl : k < xs.length) :
    (xs.take n).getD k 0 = xs.getD k 0 := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_take, ← List.getD_eq_getElem]

theorem depth_ge (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) : 18 ≤ D.gr.2.1.length := by
  rw [depth_eq hb hok]
  have : 2 ^ 17 < D.pushTotal := by
    simp only [VsData.pushTotal, pushKappas, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons]
    have := Nat.one_le_two_pow (n := D.logMem)
    omega
  exact log2Ceil_ge this

/-- The cells of `defer_out`, segment by segment. -/
theorem out_cells (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) (hm : VsMem0 rd D P out) :
    (∀ k < 18, LoadHolds rd out k (D.gr.2.1.getD k 0)) ∧ (∀ k < 4, LoadHolds rd out (18 + k) (D.alphas.getD k 0)) ∧
      LoadHolds rd out 22 D.bv ∧ LoadHolds rd out 23 D.alpha ∧ LoadHolds rd out 24 D.zSkip ∧
      (∀ k < 8, LoadHolds rd out (25 + k) (D.chi.getD k 0)) ∧
      (∀ k < 8, LoadHolds rd out (33 + k) (D.rcs.getD k 0)) ∧
      (∀ k < 64, LoadHolds rd out (41 + k) (D.s.getD k 0)) ∧ LoadHolds rd out 105 D.mv := by
  have hd := depth_ge hb hok
  have hal : D.alphas.length = 4 := by simp [VsData.alphas, sqAll_eq]
  have hcl := hok.chi_length
  have hrl := hok.rcs_length
  have hsl := hok.s_length
  have h := hm.out
  simp only [Node.fixedCells, VsData.fresh, List.reverse_reverse] at h
  have hbp : (D.gr.2.1.take 18 ++ D.alphas).length = 22 := by simp [hal]; omega
  have h1 := readsAt_left (readsAt_left (readsAt_left (readsAt_left (readsAt_left h))))
  have h2 := readsAt_right (readsAt_left (readsAt_left (readsAt_left (readsAt_left h))))
  have h3 := readsAt_right (readsAt_left (readsAt_left (readsAt_left h)))
  have h4 := readsAt_right (readsAt_left (readsAt_left h))
  have h5 := readsAt_right (readsAt_left h)
  have h6 := readsAt_right h
  simp only [List.length_append, hbp, List.length_cons, List.length_nil, List.length_take, hrl, hsl, show min 8 D.chi.length = 8 by omega] at h2 h3 h4 h5 h6
  have at_ : ∀ {p : E} {xs : List E} {o k : ℕ}, ReadsAt rd (p * gen ^ o) xs → k < xs.length →
      LoadHolds rd p (o + k) (xs.getD k 0) := fun hr hk => by
    rw [← loadHolds_mul_gen_pow]; exact readsAt_getD hr hk
  refine ⟨fun k hk => ?_, fun k hk => ?_, ?_, ?_, ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, ?_⟩
  · have := readsAt_getD (readsAt_left h1) (k := k) (by simp; omega)
    rwa [getD_take' (by omega) (by omega)] at this
  · have := readsAt_getD (readsAt_right h1) (k := k) (by omega)
    rwa [List.length_take, show min 18 D.gr.2.1.length = 18 by omega,
      loadHolds_mul_gen_pow] at this
  · have := at_ (o := 22) (k := 0) h2 (by simp); simpa using this
  · have := at_ (o := 22) (k := 1) h2 (by simp); simpa using this
  · have := at_ (o := 22) (k := 2) h2 (by simp); simpa using this
  · have := at_ (o := 25) h3 (k := k) (by simp; omega)
    rwa [getD_take' (by omega) (by omega)] at this
  · exact at_ (o := 33) h4 (by omega)
  · exact at_ (o := 41) h5 (by omega)
  · have := at_ (o := 105) (k := 0) h6 (by simp); simpa using this

/-- The values the export reads. -/
def deferIn (D : VsData) (P : VsPtrs) (out : E) : List (ℕ × E) :=
  [(6, out), (418, P.zeta), (451, P.alpha), (714, D.bv), (721, P.zchis), (722, P.lrs), (723, P.zpart),
    (727, D.zSkip), (728, D.alpha), (729, D.mv)]

theorem bDefer_eq : bDefer = ((List.range 18).map fun k ↦ cpBlk (1652 + k) (.n 418) k k).flatten ++
    ((List.range 4).map fun k ↦ cpBlk (1670 + k) (.n 451) k (18 + k)).flatten ++
    [.atom (.load (.n 714) (.n 6) 22), .atom (.load (.n 728) (.n 6) 23),
      .atom (.load (.n 727) (.n 6) 24)] ++
    ((List.range 8).map fun k ↦ cpBlk (1674 + 2 * k) (.n 721) k (25 + k) ++
      cpBlk (1675 + 2 * k) (.n 722) k (33 + k)).flatten ++
    ((List.range 64).map fun k ↦ cpBlk (1690 + k) (.n 723) k (41 + k)).flatten ++
    [.atom (.load (.n 729) (.n 6) 105)] := rfl

/-- A copy keeping the export's inputs. -/
theorem c_cpKeep {v i j src : ℕ} (hs : src < v) {ps w : E} (hi : LoadHolds rd ps i w)
    (hj : LoadHolds rd out j w) (σ : Val) (hσ : Fixes σ (deferIn D P out)) (hv : 729 < v)
    (hsrc : (src, ps) ∈ deferIn D P out) :
    Completes C rd v (v + 1) (cpBlk v (.n src) i j) σ (fun σ' => Fixes σ' (deferIn D P out)) :=
  ((c_cpBlk hs (by omega) hi hj σ (hσ.get hsrc) (hσ.get (by simp [deferIn]))).keep hσ
    (by intro p hp; simp [deferIn] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp <;> omega)).post fun _ _ h => h.2

/-- **`defer_out`** (G:2265-2279): the claims on the fixed polynomials, in `fixedCells` order. -/
theorem c_defer (hb : bytecode.length = 2 ^ 22) (hok : D.Ok bytecode) (hm : VsMem0 rd D P out)
    (σ : Val) (hσ : Fixes σ (deferIn D P out)) :
    Completes C rd 1652 1754 bDefer σ (fun _ => True) := by
  obtain ⟨o1, o2, o22, o23, o24, o3, o4, o5, o105⟩ := out_cells hb hok hm
  have hd := depth_ge hb hok
  have hal : D.alphas.length = 4 := by simp [VsData.alphas, sqAll_eq]
  have hcl := hok.chi_length
  have get : ∀ {σ' : Val} {k e}, Fixes σ' (deferIn D P out) → (k, e) ∈ deferIn D P out → σ' (.n k) = e :=
    fun h hk => h.get hk
  rw [bDefer_eq]
  have fam : ∀ (n b : ℕ) (blk : ℕ → List Stmt), (∀ k < n, NumBelow (b + (k + 1)) (Stmt.valsList (blk k))) →
      (∀ k < n, ∀ σ', Fixes σ' (deferIn D P out) →
        Completes C rd (b + k) (b + (k + 1)) (blk k) σ' (fun σ'' => Fixes σ'' (deferIn D P out))) →
      ∀ σ', Fixes σ' (deferIn D P out) →
        Completes C rd b (b + n) ((List.range n).map blk).flatten σ' (fun σ'' => Fixes σ'' (deferIn D P out)) :=
    fun n b blk hnb hb σ' h => by
      have := Completes.flatten (C := C) (rd := rd) (blk := blk) (st := fun k ↦ b + k)
        (Inv := fun _ σ'' ↦ Fixes σ'' (deferIn D P out)) n (fun _ _ => by omega) hnb hb σ' h
      simpa using this
  refine Completes.append (m := 1754) (P := fun σ' => Fixes σ' (deferIn D P out)) (by omega) (by omega)
    (numBelow_of_B (by decide +kernel)) ?_ fun σ5 _ h5 => ?_
  · refine Completes.append (m := 1690) (P := fun σ' => Fixes σ' (deferIn D P out)) (by omega) (by omega)
      (numBelow_of_B (by decide +kernel)) ?_ fun σ4 _ h4 => ?_
    · refine Completes.append (m := 1674) (P := fun σ' => Fixes σ' (deferIn D P out)) (by omega) (by omega)
        (numBelow_of_B (by decide +kernel)) ?_ fun σ3 _ h3 => ?_
      · refine Completes.append (m := 1674) (hi := 1674) (P := fun σ' => Fixes σ' (deferIn D P out))
          (by omega) le_rfl (numBelow_of_B (by decide +kernel)) ?_ fun σ2 _ h2 => ?_
        · refine Completes.append (m := 1670) (P := fun σ' => Fixes σ' (deferIn D P out))
            (by omega) (by omega) (numBelow_of_B (by decide +kernel)) ?_ fun σ1 _ h1 => ?_
          · exact fam 18 1652 _ (fun k hk => numBelow_of_B (by revert k hk; decide +kernel))
              (fun k hk σ' h => c_cpKeep (ps := P.zeta) (by omega) (readsAt_getD hm.zeta (by omega))
                (o1 k hk) σ' h (by omega) (by simp [deferIn])) σ hσ
          · exact fam 4 1670 _ (fun k hk => numBelow_of_B (by revert k hk; decide +kernel))
              (fun k hk σ' h => c_cpKeep (ps := P.alpha) (by omega) (readsAt_getD hm.alpha (by omega))
                (o2 k hk) σ' h (by omega) (by simp [deferIn])) σ1 h1
        · refine completes_upds [] (by simp) (fun next kret hn => ?_) (by simpa using h2)
          simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, upds_nil]
          rw [get (e := out) h2 (by simp [deferIn]), get (e := D.bv) h2 (by simp [deferIn]),
            get (e := D.alpha) h2 (by simp [deferIn]), get (e := D.zSkip) h2 (by simp [deferIn])]
          exact ⟨o22, o23, o24, hn⟩
      · have := Completes.flatten (C := C) (rd := rd) (blk := fun k ↦ cpBlk (1674 + 2 * k) (.n 721) k
          (25 + k) ++ cpBlk (1675 + 2 * k) (.n 722) k (33 + k)) (st := fun k ↦ 1674 + 2 * k)
          (Inv := fun _ σ'' ↦ Fixes σ'' (deferIn D P out)) 8 (fun _ _ => by omega)
          (fun k hk => numBelow_of_B (by revert k hk; decide +kernel)) (fun k hk σ' h => ?_) σ3 h3
        · simpa using this
        · refine Completes.append (m := 1675 + 2 * k) (P := fun σ'' => Fixes σ'' (deferIn D P out))
            (by omega) (by omega) (numBelow_of_B (by revert k hk; decide +kernel)) ?_
            fun σ'' _ h'' => ?_
          · rw [show 1675 + 2 * k = 1674 + 2 * k + 1 by omega]
            exact c_cpKeep (v := 1674 + 2 * k) (src := 721) (i := k) (j := 25 + k) (ps := P.zchis)
              (by omega) (readsAt_getD hm.zchis (by rw [hcl]; omega)) (o3 k hk) σ' h (by omega)
              (by simp [deferIn])
          · rw [show 1674 + 2 * (k + 1) = 1675 + 2 * k + 1 by omega]
            exact c_cpKeep (v := 1675 + 2 * k) (src := 722) (i := k) (j := 33 + k) (ps := P.lrs)
              (by omega) (readsAt_getD hm.lrs (by rw [hok.rcs_length]; omega)) (o4 k hk) σ'' h''
              (by omega) (by simp [deferIn])
    · exact fam 64 1690 _ (fun k hk => numBelow_of_B (by revert k hk; decide +kernel))
        (fun k hk σ' h => c_cpKeep (by omega) (readsAt_getD hm.zpart (by rw [hok.s_length]; omega))
          (o5 k hk) σ' h (by omega) (by simp [deferIn])) σ4 h4
  · refine completes_upds [] (by simp) (fun next kret hn => ⟨?_, hn⟩) trivial
    show LoadHolds rd (upds σ5 [] (.n 6)) 105 (upds σ5 [] (.n 729))
    rw [upds_nil, get (e := out) h5 (by simp [deferIn]), get (e := D.mv) h5 (by simp [deferIn])]; exact o105

end
end LeanVM.Guest.B1.VerifySub
