module

public import NativeVm.Code.Phase6.Claim
public import NativeVm.Code.Phase6.Lookup

/-!
# The first claim: the lane weights, the bit weights and the value

`pure_lanes`: `eqKernel` of the lane point at `eLanes`; `pure_bitW`: the bit weights
`lanes[j / 64] · 2^(j % 64)` at `eW`; `pure_wf`: their copy at `eWF`; `pure_cv`: the claim's value
`committed + segment_0 · Σ_{l < 25} lanes_l · output_l` at `eCV`.
-/

@[expose] public section

namespace NativeVm.Code.P6

open Native NativeVm.Model NativeVm.Code LeanVM.Parameters LeanVM.Protocol.Verifier Finset
open NativeVm.Transcript (wd wdisp Env rf_trans)
open NativeVm.Field (eOf eOf_inj emul emul_spec eRegs eadd eadd_spec)

variable {env : Env} {inp : Input} {s0 s : QState} {t : TState} {g : Nat → EW}

/-! ## The lanes' equality weights -/

/-- `eqKernel` of the lane point, `32` entries. -/
def lanesC : List Stmt := [blk (setW eKn 5), blk (setW eKd 0),
  blk [I (.movi .r14 0), tab eLanes (.imm (Int64.ofNat 32)) (blk [I (.mov .r13 .r15), ekern eLanePt])]]

theorem pure_lanes (hin : Inputs env inp s0.mem) {lp : Array EW} (hsz : lp.size = 5)
    (hlp : ∀ k < 5, g (eLanePt + k) = lp.getD k 0) :
    Pure6 env s0 (blk lanesC) g (ovr (Function.update (Function.update g eKn
      (EW.ofK (5 : Nat).toUInt64)) eKd (EW.ofK (0 : Nat).toUInt64)) eLanes 32
      fun m ↦ (eqKernel lp).getD m 0) := by
  refine Pure6.cons (pure_setW hin (by p6_omega)) (Pure6.cons (pure_setW hin (by p6_omega))
    (Pure6.single (pure_tab hin (Lv := .r13 :: kernRegs) (by p6_omega) (by decide)
      fun m hm s hp hs h15 ↦ ?_)))
  refine NativeVm.Transcript.wp_reg (by rfl) ?_
  refine WP.mono (ekern_spec (o := eLanePt) (i := m) (n := 5) (d := 0) (by simpa using hp)
    (hs.congr fun _ _ ↦ rfl) (by rw [ovr_out (by p6_omega), Function.update_of_ne (by p6_ne),
      Function.update_self]) (by rw [ovr_out (by p6_omega), Function.update_self])
    (by simp [h15]) (by omega) (by omega) (by p6_omega))
    (fun s' ⟨h1, h2, h3⟩ ↦ ⟨?_, h2, rf_trans (l := [.r13]) (by rf_tac) h3⟩) (fun _ h ↦ h)
  rw [h1, eqKernel_getD lp (by rw [hsz]; omega), hsz]
  refine prod_congr rfl fun k hk ↦ ?_
  have := mem_range.1 hk
  rw [kfac, ovr_out (by p6_omega), Function.update_of_ne (by p6_omega),
    Function.update_of_ne (by p6_omega), Nat.add_zero, hlp k this]

/-! ## The bit weights -/

/-- The weight of bit position `r15`: `lanes[r15 / 64] · 2^(r15 % 64)`. -/
def bitWV : Stmt := blk [I (.mov .rax .r15), I (.shri .rax 6), I (.shli .rax 4),
  I (.load .r11 (ix (2 * eLanes))), I (.load .r12 (ix (2 * eLanes + 1))), I (.mov .rcx .r15),
  I (.movi .r9 1), I (.shlcl .r9), I (.movi .r10 0), emul]

/-- The first claim's weight of bit position `j`. -/
def bitW (lanes : Array EW) (j : Nat) : EW :=
  lanes.getD (j / 64) 0 * EW.ofK ((1 : UInt64) <<< (j % 64).toUInt64)

theorem shl_and63 (m : Nat) (hm : m < 2 ^ 64) :
    (1 : UInt64) <<< (m.toUInt64 &&& 63) = (1 : UInt64) <<< (m % 64).toUInt64 := by
  have := and63 hm
  rw [show (63 : Int64).toUInt64 = 63 from rfl] at this
  rw [this]

theorem pure_bitW (hin : Inputs env inp s0.mem) {lanes : Array EW}
    (hl : ∀ k < 25, g (eLanes + k) = lanes.getD k 0) :
    Pure6 env s0 (blk [I (.movi .r14 0), tab eW (.imm (Int64.ofNat 1600)) bitWV]) g
      (ovr g eW 1600 (bitW lanes)) :=
  pure_tab hin (Lv := .r11 :: .r12 :: eRegs) (by p6_omega) (by decide) fun m hm s hp hs h15 ↦ by
    have hN := scrN_lt
    unfold bitWV
    refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl)
      (NativeVm.Transcript.wp_reg (by rfl) ?_))
    refine ldi0 (o := eLanes) (i := m / 64) (by simpa using hp)
      (by simp only [QState.setReg_reg, ↓reduceIte, h15]; exact shr6 (by omega)) hs
      (by p6_omega) ?_
    refine ldi1 (o := eLanes) (i := m / 64) (by simpa using hp)
      (by simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, h15]; exact shr6 (by omega))
      (hs.congr fun _ _ ↦ rfl) (by p6_omega) ?_
    refine NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl)
      (NativeVm.Transcript.wp_reg (by rfl) (NativeVm.Transcript.wp_reg (by rfl) ?_)))
    refine WP.mono (emul_spec _) (fun s' ⟨e1, e2, e3⟩ ↦ ⟨?_, e2, ?_⟩) (fun _ h ↦ h)
    · rw [e1]
      simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte, h15]
      rw [eOf_toE, NativeVm.Field.int64One_toUInt64, NativeVm.Field.int64Zero_toUInt64,
        shl_and63 m (by omega), ovr_out (by p6_omega), hl _ (by omega), bitW,
        NativeVm.Equiv.EW.toE_mul, mul_comm]
      rfl
    · exact rf_trans (l := [.rax, .r11, .r12, .rcx, .r9, .r10]) (by rf_tac) e3

/-- The bit weights' copy at `eWF`. -/
def wfC : Stmt := blk [I (.movi .r14 0), tab eWF (.imm (Int64.ofNat 1600)) (lterm eW)]

theorem pure_wf (hin : Inputs env inp s0.mem) :
    Pure6 env s0 wfC g (ovr g eWF 1600 fun m ↦ g (eW + m)) :=
  pure_tab hin (Lv := [.rax, .r9, .r10]) (by p6_omega) (by decide) fun m hm s hp hs h15 ↦
    WP.mono (lterm_spec hp hs (by p6_omega) h15) (fun s' ⟨e1, e2, e3⟩ ↦
      ⟨by rw [e1, ovr_out (by p6_omega)], e2, e3⟩) (fun _ h ↦ h)

/-! ## The value -/

/-- `committed + segment_0 · Σ_{l < 25} lanes_l · output_l`. -/
def cvV : Stmt := blk ([ssum (.imm (Int64.ofNat 25)) (dterm eLanes eOut)] ++ ldB eSegPt ++ [emul] ++
  ldB eComm ++ [eadd])

theorem pure_cv (hin : Inputs env inp s0.mem) {x : EW}
    (hx : x.toE = (g eComm).toE +
      (∑ i ∈ range 25, (g (eLanes + i)).toE * (g (eOut + i)).toE) * (g eSegPt).toE) :
    Pure6 env s0 (blk (cvV :: stEl eCV)) g (Function.update g eCV x) :=
  pure_el hin (L := sumRegs ++ dRegs) (by p6_omega) (by decide) fun s hp hs ↦ by
    unfold cvV
    simp only [List.cons_append, List.append_assoc]
    refine WP.blk_cons (WP.mono (ssum_spec (N := 25) (Lt := dRegs)
      (T := fun i ↦ (g (eLanes + i)).toE * (g (eOut + i)).toE) (by decide) (by omega)
      (fun _ _ ↦ rfl) (fun i hi t ht h15 hm ↦ dterm_spec
        (by rw [sum_frame ht (by decide)]; exact hp) (hs.congr fun a _ ↦ by rw [hm])
        (by p6_omega) (by p6_omega) h15)) (fun s1 ⟨e1, e2, e3⟩ ↦ ?_) (fun _ h ↦ h))
    have hp1 : s1.reg .rbp = sb env := by rw [sum_frame e3 (by decide)]; exact hp
    have hs1 : Scr s1.mem (sb env) g := hs.congr fun a _ ↦ by rw [e2]
    refine ldB_spec hp1 hs1 (by p6_omega) ?_
    refine WP.blk_cons (WP.mono (emul_spec _) (fun s2 ⟨f1, f2, f3⟩ ↦ ?_) (fun _ h ↦ h))
    have hp2 : s2.reg .rbp = sb env := by rw [f3 .rbp (by decide)]; simpa using hp1
    refine ldB_spec hp2 (hs1.congr fun a _ ↦ by rw [f2]; rfl) (by p6_omega) ?_
    refine WP.mono (eadd_spec _) (fun s3 ⟨k1, k2, k3⟩ ↦ ⟨?_, ?_, ?_⟩) (fun _ h ↦ h)
    · rw [k1, hx]
      simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
      rw [f1]
      simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
      rw [e1, eOf_toE, eOf_toE]
      ring
    · rw [k2]; simp only [QState.setReg_mem]; rw [f2]; simp only [QState.setReg_mem]; rw [e2]
    · exact rf_trans e3 (rf_trans (l := [.r11, .r12]) (l'' := dRegs) (by rf_tac)
        (rf_trans (l'' := dRegs) f3 (rf_trans (l := [.r11, .r12]) (l'' := dRegs) (by rf_tac) k3)))

/-! ## Together -/

theorem extract_getD' (a : Array EW) {i j k : Nat} (h : i + k < j) (h2 : i + k < a.size) :
    (a.extract i j).getD k 0 = a.getD (i + k) 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  split <;> simp_all; omega

theorem kfc_weights (inst segment lanePoint output : Array EW) (committed : EW) :
    (keccakFirstClaim inst segment lanePoint output committed).weights =
      (Array.range keccakBits).map (bitW (eqKernel lanePoint)) := (rfl)

theorem kfc_value (inst segment lanePoint output : Array EW) (committed : EW) :
    (keccakFirstClaim inst segment lanePoint output committed).value = committed +
      (eqKernel segment).getD (keccakSegments - 1) 0 *
        dot ((eqKernel lanePoint).extract 0 25) output := (rfl)

theorem kfc_weights_getD (inst segment lanePoint output : Array EW) (committed : EW) {j : Nat}
    (hj : j < 1600) : (keccakFirstClaim inst segment lanePoint output committed).weights.getD j 0 =
      bitW (eqKernel lanePoint) j := by
  rw [kfc_weights]
  exact getD_map_range keccakBits _ _ hj

/-- The weights, their copy and the value. -/
def firstAC : List Stmt :=
  [blk lanesC, blk [I (.movi .r14 0), tab eW (.imm (Int64.ofNat 1600)) bitWV], wfC,
    blk (cvV :: stEl eCV)]

/-- The elements `firstAC` writes. -/
def AW (i : Nat) : Prop :=
  i = eKn ∨ i = eKd ∨ i = eCV ∨ (eLanes ≤ i ∧ i < eLanes + 32) ∨ (eW ≤ i ∧ i < eW + 1600) ∨
    (eWF ≤ i ∧ i < eWF + 1600)

theorem pure_firstA (hin : Inputs env inp s0.mem) {inst output segment lanePoint : Array EW}
    {committed : EW}
    (hout : output.size = 25) (houtG : ∀ l < 25, g (eOut + l) = output.getD l 0)
    (hseg : segment.size = 1) (hsegG : g eSegPt = segment.getD 0 0)
    (hlp : lanePoint.size = 5) (hlpG : ∀ i < 5, g (eLanePt + i) = lanePoint.getD i 0)
    (hcomm : g eComm = committed) :
    ∃ g', Pure6 env s0 (blk firstAC) g g' ∧ (∀ i, ¬ AW i → g' i = g i) ∧
      (∀ j < 1600, g' (eW + j) =
        (keccakFirstClaim inst segment lanePoint output committed).weights.getD j 0) ∧
      (∀ j < 1600, g' (eWF + j) =
        (keccakFirstClaim inst segment lanePoint output committed).weights.getD j 0) ∧
      g' eCV = (keccakFirstClaim inst segment lanePoint output committed).value := by
  set lanes := eqKernel lanePoint
  set g1 := ovr (Function.update (Function.update g eKn (EW.ofK (5 : Nat).toUInt64)) eKd
    (EW.ofK (0 : Nat).toUInt64)) eLanes 32 fun m ↦ lanes.getD m 0
  have k1 : ∀ i, ¬ (i = eKn ∨ i = eKd ∨ (eLanes ≤ i ∧ i < eLanes + 32)) → g1 i = g i := by
    intro i hi
    simp only [not_or, not_and, Nat.not_lt] at hi
    simp only [g1]
    rw [ovr_out (by p6_omega), Function.update_of_ne hi.2.1, Function.update_of_ne hi.1]
  have l1 : ∀ k < 32, g1 (eLanes + k) = lanes.getD k 0 := fun k hk ↦ by
    simp only [g1]; rw [ovr_in (by omega) (by omega), Nat.add_sub_cancel_left]
  set g2 := ovr g1 eW 1600 (bitW lanes)
  set g3 := ovr g2 eWF 1600 fun m ↦ g2 (eW + m)
  have w2 : ∀ j < 1600, g2 (eW + j) = bitW lanes j := fun j hj ↦ by
    simp only [g2]; rw [ovr_in (by omega) (by omega), Nat.add_sub_cancel_left]
  have w3 : ∀ j < 1600, g3 (eW + j) = bitW lanes j := fun j hj ↦ by
    simp only [g3]; rw [ovr_out (by p6_omega), w2 j hj]
  have f3 : ∀ j < 1600, g3 (eWF + j) = bitW lanes j := fun j hj ↦ by
    simp only [g3]; rw [ovr_in (by omega) (by omega), Nat.add_sub_cancel_left, w2 j hj]
  have k3 : ∀ i, ¬ AW i → g3 i = g i := fun i hi ↦ by
    simp only [AW, not_or, not_and, Nat.not_lt] at hi
    simp only [g3, g2]
    rw [ovr_out (by p6_omega), ovr_out (by p6_omega), k1 i (by
      simp only [not_or, not_and, Nat.not_lt]; exact ⟨hi.1, hi.2.1, hi.2.2.2.1⟩)]
  have k3' : ∀ i, ¬ AW i → g3 i = g i := k3
  have hcv : (keccakFirstClaim inst segment lanePoint output committed).value.toE =
      (g3 eComm).toE + (∑ i ∈ range 25, (g3 (eLanes + i)).toE * (g3 (eOut + i)).toE) *
        (g3 eSegPt).toE := by
    have hS : keccakSegments - 1 = 1 := by decide
    have hk1 : ((eqKernel segment).getD 1 0).toE = (segment.getD 0 0).toE := by
      rw [eqKernel_getD _ (by rw [hseg]; decide), hseg, Finset.prod_range_one]
      rfl
    have hsz : ((eqKernel lanePoint).extract 0 25).size = 25 := by
      rw [Array.size_extract, eqKernel_size, hlp]; rfl
    have hd : (dot ((eqKernel lanePoint).extract 0 25) output).toE =
        ∑ i ∈ range 25, (g3 (eLanes + i)).toE * (g3 (eOut + i)).toE := by
      rw [toE_dot_range, hsz, hout, Nat.min_self]
      refine sum_congr rfl fun i hi ↦ ?_
      have := mem_range.1 hi
      rw [extract_getD' _ (by omega) (by rw [eqKernel_size, hlp]; omega), Nat.zero_add,
        k3' (eOut + i) (by simp only [AW]; p6_omega), houtG i this]
      have e : g3 (eLanes + i) = lanes.getD i 0 := by
        simp only [g3, g2]
        rw [ovr_out (by p6_omega), ovr_out (by p6_omega), l1 i (by omega)]
      rw [e]
    rw [kfc_value, hS, NativeVm.Equiv.EW.toE_add, NativeVm.Equiv.EW.toE_mul, hk1, hd,
      k3' _ (by simp only [AW]; p6_omega), k3' _ (by simp only [AW]; p6_omega), hcomm, hsegG,
      mul_comm]
  refine ⟨Function.update g3 eCV (keccakFirstClaim inst segment lanePoint output committed).value,
    Pure6.cons (pure_lanes hin hlp hlpG) (Pure6.cons (pure_bitW hin fun k hk ↦ l1 k (by omega))
      (Pure6.cons (pure_wf hin) (Pure6.single (pure_cv hin hcv)))), fun i hi ↦ ?_,
    fun j hj ↦ ?_, fun j hj ↦ ?_, Function.update_self ..⟩
  · rw [Function.update_of_ne (fun e ↦ hi (by simp only [AW]; omega)), k3 i hi]
  · rw [Function.update_of_ne (by p6_omega), w3 j hj, kfc_weights_getD _ _ _ _ _ hj]
  · rw [Function.update_of_ne (by p6_omega), f3 j hj, kfc_weights_getD _ _ _ _ _ hj]

end NativeVm.Code.P6
