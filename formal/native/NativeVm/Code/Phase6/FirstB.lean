module

public import NativeVm.Code.Phase6.FirstA
public import NativeVm.Code.Phase6.FirstCopy

/-!
# The first claim: the instance weights, the point and its segment's size

`KECCAK`'s point `inst` (`n ≤ 30` coordinates) at `eInst`, its size at `eInstN`. `pure_fcKn`: the
instance weights' coordinates `min 4 n` at `eKn`; `pure_fcMuN`: their count `2^min 4 n` at
`eMuN`; `pure_fcMu`: `eqKernel` of them, `16` entries, at `eMu`; `pure_fcPt`: the point
`inst[4..n] ++ segment` at `ePt`; `pure_fcPtN`: its size at `ePtN`; `pure_fcSegN`: its size from
`packBits` at `eSegN`.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code LeanVM.Parameters LeanVM.Protocol.Verifier Finset
open NativeVm.Transcript (wd wdisp Env rf_trans)
open NativeVm.Field (eOf eOf_inj)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW}

theorem fshl_pow {k : Nat} (hk : k < 64) : (1 : UInt64) <<< k.toUInt64 = (2 ^ k).toUInt64 := by
  rw [← UInt64.toNat_inj, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk]
  have h2 : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hk
  simp [Nat.shiftLeft_eq]

theorem fdec_ltu {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    decide (a.toUInt64 < b.toUInt64) = decide (a < b) := by
  simp only [decide_eq_decide]
  exact toUInt64_lt' ha hb

theorem fimm (k : Nat) : (Int64.ofNat k).toUInt64 = k.toUInt64 := (rfl)

/-! ## The instance weights -/

/-- `(r9, r10) :=` `min 4 n`, `n` the word at `eInstN`. -/
def fcKnV : Stmt := blk [I (.load .rax (at_ .rbp (wdisp (2 * eInstN)))),
  .ite (.cmp .ltu .rax (.imm (Int64.ofNat 4))) .skip (I (.movi .rax (Int64.ofNat 4))),
  I (.mov .r9 .rax), I (.movi .r10 0)]

theorem pure_fcKn (hin : Inputs env inp s0.mem) {n : Nat} (hn : g eInstN = EW.ofK n.toUInt64)
    (hn30 : n ≤ 30) :
    Pure6 env s0 (blk (fcKnV :: stEl eKn)) g (Function.update g eKn (EW.ofK (min 4 n).toUInt64)) :=
  pure_el hin (L := [.rax, .r9, .r10]) (by p6_omega) (by decide) fun s hp hs ↦ by
    unfold fcKnV
    refine ld0 hp hs (by p6_omega) ?_
    rw [hn]
    apply WP.blk_cons
    apply WP.ite
    simp only [Cond.eval, Rhs.eval, QState.setReg_reg, ↓reduceIte, fimm, EW.ofK,
      fdec_ltu (show n < 2 ^ 64 by omega) (show 4 < 2 ^ 64 by omega)]
    by_cases h4 : n < 4
    · simp only [h4, decide_true, ↓reduceIte]
      refine WP.skip (NativeVm.Transcript.wp_reg (by rfl) ?_)
      refine NativeVm.Transcript.wp_reg (by rfl) (WP.blk_nil ?_)
      refine ⟨?_, rfl, by rf_tac⟩
      simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
      rw [Nat.min_eq_right (by omega)]
      rfl
    · simp only [h4, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine WP.ins (by rfl) (NativeVm.Transcript.wp_reg (by rfl) ?_)
      refine NativeVm.Transcript.wp_reg (by rfl) (WP.blk_nil ?_)
      refine ⟨?_, rfl, by rf_tac⟩
      simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
      rw [Nat.min_eq_left (by omega)]
      rfl

/-- `(r9, r10) :=` `2^k`, `k` the word at `eKn`. -/
def fcMuNV : Stmt := blk [I (.load .rcx (at_ .rbp (wdisp (2 * eKn)))), I (.movi .r9 1), I (.shlcl .r9),
  I (.movi .r10 0)]

theorem pure_fcMuN (hin : Inputs env inp s0.mem) {k : Nat} (hk : g eKn = EW.ofK k.toUInt64)
    (hk4 : k ≤ 4) :
    Pure6 env s0 (blk (fcMuNV :: stEl eMuN)) g (Function.update g eMuN (EW.ofK (2 ^ k).toUInt64)) :=
  pure_el hin (L := [.rcx, .r9, .r10]) (by p6_omega) (by decide) fun s hp hs ↦ by
    unfold fcMuNV
    refine ld0 hp hs (by p6_omega) ?_
    rw [hk]
    refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl) ?_)
    refine NativeVm.Transcript.wp_reg (by rfl) (WP.blk_nil ?_)
    refine ⟨?_, rfl, by rf_tac⟩
    simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, EW.ofK]
    rw [NativeVm.Field.int64One_toUInt64, shl_and63 k (by omega), Nat.mod_eq_of_lt (by omega),
      fshl_pow (by omega)]
    rfl

/-- `eqKernel` of the coordinates at `eInst`, their count at `eKn`, `16` entries. -/
def fcMuC : Stmt := blk [I (.movi .r14 0),
  tab eMu (.imm (Int64.ofNat 16)) (blk [I (.mov .r13 .r15), ekern eInst])]

theorem pure_fcMu (hin : Inputs env inp s0.mem) {k : Nat} (hk : g eKn = EW.ofK k.toUInt64)
    (hk4 : k ≤ 4) (hd : g eKd = EW.ofK (0 : Nat).toUInt64) :
    Pure6 env s0 fcMuC g (ovr g eMu 16 fun m ↦ EW.ofE (∏ j ∈ range k, kfac g eInst 0 m j)) :=
  pure_tab hin (Lv := .r13 :: kernRegs) (by p6_omega) (by decide) fun m hm s hp hs h15 ↦ by
    refine NativeVm.Transcript.wp_reg (by rfl) ?_
    refine WP.mono (ekern_spec (o := eInst) (i := m) (n := k) (d := 0) (by simpa using hp)
      (hs.congr fun _ _ ↦ rfl) (by rw [ovr_out (by p6_omega), hk])
      (by rw [ovr_out (by p6_omega), hd]) (by simp [h15]) (by omega) (by omega) (by p6_omega))
      (fun s' ⟨h1, h2, h3⟩ ↦ ⟨?_, h2, rf_trans (l := [.r13]) (by rf_tac) h3⟩) (fun _ h ↦ h)
    rw [h1, NativeVm.Equiv.EW.toE_ofE]
    refine prod_congr rfl fun j hj ↦ ?_
    have := mem_range.1 hj
    rw [kfac, kfac, ovr_out (by p6_omega)]

/-! ## The point -/

/-- `(r9, r10) :=` coordinate `r15 + 4` of `KECCAK`'s point, the segment's challenge past its end. -/
def fcPtV : Stmt := blk [I (.mov .rax .r15), I (.addi .rax (Int64.ofNat 4)),
  I (.load .rdx (at_ .rbp (wdisp (2 * eInstN)))),
  .ite (.cmp .ltu .rax (.reg .rdx))
    (blk [I (.shli .rax 4), I (.load .r9 (ix (2 * eInst))), I (.load .r10 (ix (2 * eInst + 1)))])
    (blk [I (.load .r9 (at_ .rbp (wdisp (2 * eSegPt)))),
      I (.load .r10 (at_ .rbp (wdisp (2 * eSegPt + 1))))])]

/-- The point's coordinate `m`. -/
def fcPt (g : Nat → EW) (n m : Nat) : EW := if m + 4 < n then g (eInst + (m + 4)) else g eSegPt

theorem pure_fcPt (hin : Inputs env inp s0.mem) {n : Nat} (hn : g eInstN = EW.ofK n.toUInt64)
    (hn30 : n ≤ 30) :
    Pure6 env s0 (blk [I (.movi .r14 0), tab ePt (.imm (Int64.ofNat 27)) fcPtV]) g
      (ovr g ePt 27 (fcPt g n)) :=
  pure_tab hin (Lv := [.rax, .rdx, .r9, .r10]) (by p6_omega) (by decide) fun m hm s hp hs h15 ↦ by
    unfold fcPtV
    refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl) ?_)
    refine ld0 (by simpa using hp) (hs.congr fun _ _ ↦ rfl) (by p6_omega) ?_
    rw [ovr_out (by p6_omega), hn]
    have hrax : m.toUInt64 + (Int64.ofNat 4).toUInt64 = (m + 4).toUInt64 := by
      rw [fimm, NativeVm.Transcript.toUInt64_add]
    apply WP.blk_cons
    apply WP.ite
    simp only [Cond.eval, Rhs.eval, QState.setReg_reg, reduceCtorEq, ↓reduceIte, h15, hrax, EW.ofK,
      fdec_ltu (show m + 4 < 2 ^ 64 by omega) (show n < 2 ^ 64 by omega)]
    by_cases hlt : m + 4 < n
    · simp only [hlt, decide_true, ↓reduceIte]
      refine NativeVm.Transcript.wp_reg (by rfl) ?_
      refine ldi0 (o := eInst) (i := m + 4) (by simpa using hp)
        (by simp only [QState.setReg_reg, ↓reduceIte]; exact rax16 _) (hs.congr fun _ _ ↦ rfl)
        (by p6_omega) ?_
      refine ldi1 (o := eInst) (i := m + 4) (by simpa using hp)
        (by simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]; exact rax16 _)
        (hs.congr fun _ _ ↦ rfl) (by p6_omega) (WP.blk_nil (WP.blk_nil ?_))
      refine ⟨?_, rfl, by rf_tac⟩
      simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
      rw [eOf_toE, fcPt, ite_eq_left_of_eq_true _ _ (eq_true hlt), ovr_out (by p6_omega)]
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine ld0 (by simpa using hp) (hs.congr fun _ _ ↦ rfl) (by p6_omega) ?_
      refine ld1 (by simpa using hp) (hs.congr fun _ _ ↦ rfl) (by p6_omega)
        (WP.blk_nil (WP.blk_nil ?_))
      refine ⟨?_, rfl, by rf_tac⟩
      simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
      rw [eOf_toE, fcPt, ite_eq_right_of_eq_false _ _ (eq_false hlt), ovr_out (by p6_omega)]

/-- `(r9, r10) :=` the point's size `(n - 4) + 1`, `n` the word at `eInstN`. -/
def fcPtNV : Stmt := blk [I (.load .rax (at_ .rbp (wdisp (2 * eInstN)))),
  .ite (.cmp .ltu .rax (.imm (Int64.ofNat 4))) (I (.movi .r9 1))
    (blk [I (.mov .r9 .rax), I (.subi .r9 (Int64.ofNat 3))]),
  I (.movi .r10 0)]

theorem pure_fcPtN (hin : Inputs env inp s0.mem) {n : Nat} (hn : g eInstN = EW.ofK n.toUInt64)
    (hn30 : n ≤ 30) :
    Pure6 env s0 (blk (fcPtNV :: stEl ePtN)) g
      (Function.update g ePtN (EW.ofK (n - 4 + 1).toUInt64)) :=
  pure_el hin (L := [.rax, .r9, .r10]) (by p6_omega) (by decide) fun s hp hs ↦ by
    unfold fcPtNV
    refine ld0 hp hs (by p6_omega) ?_
    rw [hn]
    apply WP.blk_cons
    apply WP.ite
    simp only [Cond.eval, Rhs.eval, QState.setReg_reg, ↓reduceIte, fimm, EW.ofK,
      fdec_ltu (show n < 2 ^ 64 by omega) (show 4 < 2 ^ 64 by omega)]
    by_cases h4 : n < 4
    · simp only [h4, decide_true, ↓reduceIte]
      refine WP.ins (by rfl) (NativeVm.Transcript.wp_reg (by rfl) (WP.blk_nil ?_))
      refine ⟨?_, rfl, by rf_tac⟩
      simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
      rw [show n - 4 + 1 = 1 by omega]
      rfl
    · simp only [h4, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl)
        (WP.blk_nil (NativeVm.Transcript.wp_reg (by rfl) (WP.blk_nil ?_))))
      refine ⟨?_, rfl, by rf_tac⟩
      simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
      rw [fimm, toUInt64_sub' (by omega) (by omega), show n - 3 = n - 4 + 1 by omega]
      rfl

/-- `(r9, r10) :=` the point's size from `packBits`, `0` below it. -/
def fcSegNV : Stmt := blk [I (.load .r9 (at_ .rbp (wdisp (2 * ePtN)))),
  I (.load .rax (at_ .rbp (wdisp (2 * ePB)))),
  .ite (.cmp .ltu .r9 (.reg .rax)) (I (.movi .r9 0)) (I (.sub .r9 .rax)),
  I (.movi .r10 0)]

theorem pure_fcSegN (hin : Inputs env inp s0.mem) {P pb : Nat} (hP : g ePtN = EW.ofK P.toUInt64)
    (hpb : g ePB = EW.ofK pb.toUInt64) (hP32 : P < 32) (hpb26 : pb ≤ 26) :
    Pure6 env s0 (blk (fcSegNV :: stEl eSegN)) g
      (Function.update g eSegN (EW.ofK (P - pb).toUInt64)) :=
  pure_el hin (L := [.rax, .r9, .r10]) (by p6_omega) (by decide) fun s hp hs ↦ by
    unfold fcSegNV
    refine ld0 hp hs (by p6_omega) ?_
    refine ld0 (by simpa using hp) (hs.congr fun _ _ ↦ rfl) (by p6_omega) ?_
    rw [hP, hpb]
    apply WP.blk_cons
    apply WP.ite
    simp only [Cond.eval, Rhs.eval, QState.setReg_reg, reduceCtorEq, ↓reduceIte, EW.ofK,
      fdec_ltu (show P < 2 ^ 64 by omega) (show pb < 2 ^ 64 by omega)]
    by_cases hlt : P < pb
    · simp only [hlt, decide_true, ↓reduceIte]
      refine WP.ins (by rfl) (NativeVm.Transcript.wp_reg (by rfl) (WP.blk_nil ?_))
      refine ⟨?_, rfl, by rf_tac⟩
      simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
      rw [show P - pb = 0 by omega]
      rfl
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine WP.ins (by rfl) (NativeVm.Transcript.wp_reg (by rfl) (WP.blk_nil ?_))
      refine ⟨?_, rfl, by rf_tac⟩
      simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
      rw [toUInt64_sub' (by omega) (by omega)]
      rfl

/-! ## Together -/

theorem append_getD' (a b : Array EW) (k : Nat) :
    (a ++ b).getD k 0 = if k < a.size then a.getD k 0 else b.getD (k - a.size) 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append]
  split <;> rfl

theorem kfc_mu (inst segment lanePoint output : Array EW) (committed : EW) :
    (keccakFirstClaim inst segment lanePoint output committed).mu = eqKernel (inst.extract 0 4) :=
  (rfl)

theorem kfc_point (inst segment lanePoint output : Array EW) (committed : EW) :
    (keccakFirstClaim inst segment lanePoint output committed).point =
      inst.extract 4 inst.size ++ segment := (rfl)

theorem kfc_point_size (inst segment lanePoint output : Array EW) (committed : EW)
    (hseg : segment.size = 1) :
    (keccakFirstClaim inst segment lanePoint output committed).point.size = inst.size - 4 + 1 := by
  rw [kfc_point, Array.size_append, Array.size_extract, hseg, Nat.min_self]

/-- The instance weights, the point, their sizes and the point's size from `packBits`. -/
def firstBC : List Stmt :=
  [blk (fcKnV :: stEl eKn), blk (fcMuNV :: stEl eMuN), blk (setW eKd 0), fcMuC,
    blk [I (.movi .r14 0), tab ePt (.imm (Int64.ofNat 27)) fcPtV], blk (fcPtNV :: stEl ePtN),
    blk (fcSegNV :: stEl eSegN)]

/-- The elements `firstBC` writes. -/
def BW (i : Nat) : Prop :=
  i = eKn ∨ i = eKd ∨ i = eMuN ∨ i = ePtN ∨ i = eSegN ∨ (eMu ≤ i ∧ i < eMu + 16) ∨
    (ePt ≤ i ∧ i < ePt + 27)

theorem pure_firstB (hin : Inputs env inp s0.mem) {inst output segment lanePoint : Array EW}
    {committed : EW} {pb : Nat} (hinst : inst.size ≤ 30)
    (hinstN : g eInstN = EW.ofK inst.size.toUInt64)
    (hinstG : ∀ i < inst.size, g (eInst + i) = inst.getD i 0)
    (hseg : segment.size = 1) (hsegG : g eSegPt = segment.getD 0 0)
    (hpb : g ePB = EW.ofK pb.toUInt64) (hpb26 : pb ≤ 26) :
    ∃ g', Pure6 env s0 (blk firstBC) g g' ∧ (∀ i, ¬ BW i → g' i = g i) ∧
      (keccakFirstClaim inst segment lanePoint output committed).mu.size ≤ 16 ∧
      g' eMuN = EW.ofK (keccakFirstClaim inst segment lanePoint output committed).mu.size.toUInt64 ∧
      (∀ i < (keccakFirstClaim inst segment lanePoint output committed).mu.size,
        g' (eMu + i) = (keccakFirstClaim inst segment lanePoint output committed).mu.getD i 0) ∧
      (keccakFirstClaim inst segment lanePoint output committed).point.size < 32 ∧
      g' ePtN = EW.ofK (keccakFirstClaim inst segment lanePoint output committed).point.size.toUInt64 ∧
      (∀ i < (keccakFirstClaim inst segment lanePoint output committed).point.size,
        g' (ePt + i) = (keccakFirstClaim inst segment lanePoint output committed).point.getD i 0) ∧
      g' eSegN = EW.ofK
        ((keccakFirstClaim inst segment lanePoint output committed).point.size - pb).toUInt64 := by
  set n := inst.size
  set k := min 4 n
  have hk4 : k ≤ 4 := Nat.min_le_left _ _
  set g1 := Function.update g eKn (EW.ofK k.toUInt64)
  set g2 := Function.update g1 eMuN (EW.ofK (2 ^ k).toUInt64)
  set g3 := Function.update g2 eKd (EW.ofK (0 : Nat).toUInt64)
  set g4 := ovr g3 eMu 16 fun m ↦ EW.ofE (∏ j ∈ range k, kfac g3 eInst 0 m j)
  set g5 := ovr g4 ePt 27 (fcPt g4 n)
  set g6 := Function.update g5 ePtN (EW.ofK (n - 4 + 1).toUInt64)
  set g7 := Function.update g6 eSegN (EW.ofK (n - 4 + 1 - pb).toUInt64)
  have e3 : ∀ i, ¬ (i = eKn ∨ i = eMuN ∨ i = eKd) → g3 i = g i := fun i hi ↦ by
    simp only [not_or] at hi
    simp only [g3, g2, g1]
    rw [Function.update_of_ne hi.2.2, Function.update_of_ne hi.2.1, Function.update_of_ne hi.1]
  have e4 : ∀ i, ¬ (i = eKn ∨ i = eMuN ∨ i = eKd ∨ (eMu ≤ i ∧ i < eMu + 16)) → g4 i = g i :=
    fun i hi ↦ by
      simp only [not_or, not_and, Nat.not_lt] at hi
      simp only [g4]
      rw [ovr_out (by p6_omega), e3 i (by simp only [not_or]; exact ⟨hi.1, hi.2.1, hi.2.2.1⟩)]
  have p1 : Pure6 env s0 (blk (fcKnV :: stEl eKn)) g g1 := pure_fcKn hin hinstN hinst
  have p2 : Pure6 env s0 (blk (fcMuNV :: stEl eMuN)) g1 g2 :=
    pure_fcMuN hin (by simp only [g1]; rw [Function.update_self]) hk4
  have p3 : Pure6 env s0 (blk (setW eKd 0)) g2 g3 := pure_setW hin (by p6_omega)
  have p4 : Pure6 env s0 fcMuC g3 g4 := pure_fcMu hin (by
    simp only [g3, g2, g1]
    rw [Function.update_of_ne (by p6_ne), Function.update_of_ne (by p6_ne),
      Function.update_self]) hk4 (by simp only [g3]; rw [Function.update_self])
  have p5 : Pure6 env s0 (blk [I (.movi .r14 0), tab ePt (.imm (Int64.ofNat 27)) fcPtV]) g4 g5 :=
    pure_fcPt hin (by rw [e4 _ (by p6_omega), hinstN]) hinst
  have p6 : Pure6 env s0 (blk (fcPtNV :: stEl ePtN)) g5 g6 :=
    pure_fcPtN hin (by simp only [g5]; rw [ovr_out (by p6_omega), e4 _ (by p6_omega), hinstN]) hinst
  have p7 : Pure6 env s0 (blk (fcSegNV :: stEl eSegN)) g6 g7 :=
    pure_fcSegN hin (by simp only [g6]; rw [Function.update_self])
      (by simp only [g6, g5]
          rw [Function.update_of_ne (by p6_ne), ovr_out (by p6_omega), e4 _ (by p6_omega), hpb])
      (by omega) hpb26
  have hmu := kfc_mu inst segment lanePoint output committed
  have hmuS : (eqKernel (inst.extract 0 4)).size = 2 ^ k := by
    rw [eqKernel_size, Array.size_extract, Nat.sub_zero]
  have hPS := kfc_point_size inst segment lanePoint output committed hseg
  -- the values, read in `g7`
  have m7 : ∀ i < 16, g7 (eMu + i) = g4 (eMu + i) := fun i hi ↦ by
    simp only [g7, g6, g5]
    rw [Function.update_of_ne (by p6_omega), Function.update_of_ne (by p6_omega),
      ovr_out (by p6_omega)]
  have pt7 : ∀ i < 27, g7 (ePt + i) = fcPt g4 n i := fun i hi ↦ by
    simp only [g7, g6, g5]
    rw [Function.update_of_ne (by p6_omega), Function.update_of_ne (by p6_omega),
      ovr_in (by omega) (by omega), Nat.add_sub_cancel_left]
  refine ⟨g7, Pure6.cons p1 (Pure6.cons p2 (Pure6.cons p3 (Pure6.cons p4 (Pure6.cons p5
    (Pure6.cons p6 (Pure6.single p7)))))), fun i hi ↦ ?_, ?_, ?_, fun i hi ↦ ?_, ?_, ?_,
    fun i hi ↦ ?_, ?_⟩
  · simp only [BW, not_or, not_and, Nat.not_lt] at hi
    simp only [g7, g6, g5]
    rw [Function.update_of_ne hi.2.2.2.2.1, Function.update_of_ne hi.2.2.2.1, ovr_out (by p6_omega),
      e4 i (by simp only [not_or, not_and, Nat.not_lt]; exact ⟨hi.1, hi.2.2.1, hi.2.1, hi.2.2.2.2.2.1⟩)]
  · rw [hmu, hmuS]
    exact le_trans (Nat.pow_le_pow_right (by norm_num) hk4) (by norm_num)
  · simp only [g7, g6, g5]
    rw [Function.update_of_ne (by p6_ne), Function.update_of_ne (by p6_ne), ovr_out (by p6_omega)]
    simp only [g4]
    rw [ovr_out (by p6_omega), hmu, hmuS]
    simp only [g3, g2]
    rw [Function.update_of_ne (by p6_ne), Function.update_self]
  · rw [hmu, hmuS] at hi
    have h16 : 2 ^ k ≤ 16 := le_trans (Nat.pow_le_pow_right (by norm_num) hk4) (by norm_num)
    rw [hmu, m7 i (by omega)]
    simp only [g4]
    rw [ovr_in (by omega) (by omega), Nat.add_sub_cancel_left]
    apply NativeVm.Equiv.EW.toE_injective
    rw [NativeVm.Equiv.EW.toE_ofE, eqKernel_getD _ (by rw [Array.size_extract, Nat.sub_zero]; exact hi),
      Array.size_extract, Nat.sub_zero]
    refine prod_congr rfl fun j hj ↦ ?_
    have hj' := mem_range.1 hj
    have hjn : j < n := lt_of_lt_of_le hj' (Nat.min_le_right _ _)
    rw [kfac, Nat.add_zero, e3 _ (by p6_omega), hinstG j hjn,
      extract_getD' _ (by omega) (by omega), Nat.zero_add]
  · rw [hPS]; omega
  · simp only [g7, g6]
    rw [Function.update_of_ne (by p6_ne), Function.update_self, hPS]
  · rw [hPS] at hi
    rw [pt7 i (by omega), kfc_point, append_getD', fcPt, Array.size_extract, Nat.min_self]
    by_cases h : i + 4 < n
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
        e4 _ (by p6_omega), Nat.add_comm i 4, hinstG _ (by omega),
        extract_getD' _ (by omega) (by omega)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
        ite_eq_right_of_eq_false _ _ (eq_false (by omega)), e4 _ (by p6_omega), hsegG,
        show i - (n - 4) = 0 by omega]
  · simp only [g7]
    rw [Function.update_self, hPS]

end NativeVm.Code.P6
