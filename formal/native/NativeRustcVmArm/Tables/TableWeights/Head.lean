module

public import NativeRustcVmArm.Tables.TableWeights.Body

/-!
# `table_weights`: the loop head and the first multiplication

`b10` (`.LTableWeights_4`) stores weight 5 in its places and loads the challenge's high limb
(`HeadBlock`, `hd_of`: the state `Hd`); `b11` (no equality coordinate) or `b2`
(`.LTableWeights_2`, the equality point's coordinate) compute the factor (`head_step`: `It` to
`Pre3`); `b3` (`.LTableWeights_3`) loads the challenge's low limb and multiplies weight 0
(`first_step`: `Pre3` to `Mid c 0`).
-/

namespace NativeRustcVmArm.Tables.TableWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Tables
open NativeRustcVmArm.Vm.TableWeights
open NativeRustcVm (wordOf ewOf)

@[expose] public section

/-- The run's facts of the entry state: the stack, the frame, the inputs. -/
structure Ctx (m0 : MachineData) : Prop where
  stk : StackOk m0 tableWeightsStack
  geo : Geo m0
  out : In m0 (rg m0 .X0) 96
  hts : In m0 (rg m0 .X1) 48
  eq : In m0 (rg m0 .X2) (16 * m0.regs.X3.toNat)
  pt : In m0 (rg m0 .X4) (16 * n m0)

/-- After `b10`: coordinate `c`'s challenge's high limb (X24), the six weights in place. -/
structure Hd (m0 : MachineData) (c : Nat) (m : MachineData) : Prop where
  lt : c < n m0
  frm : Frm m0 m
  x22 : rg m .X22 = BitVec.ofNat 64 c
  x23 : rg m .X23 = rg m0 .X2 + BitVec.ofNat 64 (8 + 16 * c)
  x27 : rg m .X27 = rg m0 .X4 + BitVec.ofNat 64 (16 * c)
  x24 : rg m .X24 = (ch m0 c).c1.toBitVec
  w : ∀ j < 6, WAt m0 m j ((W m0 c).getD j 0)

/-- What `b10` (and then `b11`) does. -/
structure HeadBlock (S : SState) : Prop where
  sp : S.sp = .ptr 0 0
  writes : FrameWrites S 240
  x24 : S.reg .X24 = some (.load 1 8 8)
  regs : ∀ r ∈ [XReg.X22, .X23], S.reg r = some (.reg r)
  x27 : S.reg .X27 = some (.ptr 1 0)
  keep : ∀ i < 5, (lo i).after S = some (lo i).sym ∧ (hi i).after S = some (hi i).sym
  lo5 : (lo 5).after S = some (.reg .X0)
  hi5 : (hi 5).after S = some (.reg .X9)
  slots : ∀ p ∈ koffs, loadSym S.mem 0 p 8 = .load 0 p 8

/-- What `b2` and `b3` keep. -/
structure KeepBlock (S : SState) : Prop where
  sp : S.sp = .ptr 0 0
  writes : FrameWrites S 240
  keep : ∀ i < 6, (lo i).after S = some (lo i).sym ∧ (hi i).after S = some (hi i).sym
  slots : ∀ p ∈ koffs, loadSym S.mem 0 p 8 = .load 0 p 8

end

public section

variable {m0 : MachineData}

theorem ctx_of (hpre : TableWeightsPre m0) : Ctx m0 :=
  ⟨hpre.1, geo_of hpre.1, ⟨hpre.2.1, hpre.2.2.1⟩, ⟨hpre.2.2.2.1.1, hpre.2.2.2.1.2.1⟩,
    hpre.2.2.2.2.1, hpre.2.2.2.2.2⟩

theorem add_ofNat_ofInt (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofInt 64 (b : Int) = x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.ofInt_natCast, BitVec.add_assoc, BitVec.ofNat_add]

/-- The point's coordinate `c`, an input. -/
theorem Ctx.ptc (hc : Ctx m0) {c : Nat} (hlt : c < n m0) :
    In m0 (rg m0 .X4 + BitVec.ofNat 64 (16 * c)) 16 :=
  hc.pt.sub (by omega) (by omega)

/-- The environment of a coordinate's region: well formed. -/
theorem Ctx.wf_in (hc : Ctx m0) {m : MachineData} (hf : Frm m0 m) {x : BitVec 64}
    (hx : In m0 x 16) : (Env.ofMachine m [(fb m0, 240), (x, 16)]).WF :=
  Env.wf_of ⟨⟨(hf.frameOk hc.geo).mapped, hc.geo.hi⟩, ⟨hx.mapped hf, hx.1.2⟩, trivial⟩
    (List.pairwise_pair.mpr (hx.apart_frame hc.stk))

/-- A coordinate's limb through the environment. -/
theorem Ctx.load_in (hc : Ctx m0) {m : MachineData} (hf : Frm m0 m) {x : BitVec 64}
    (hx : In m0 x 16) {o : Nat} (ho : o + 8 ≤ 16) :
    (Env.ofMachine m [(fb m0, 240), (x, 16)]).load 1 o 8 =
      (wordOf m0.dmem (x + BitVec.ofNat 64 o)).toBitVec := by
  rw [load8]
  show (wordOf m.dmem (x + BitVec.ofNat 64 o)).toBitVec = _
  rw [hx.word hc.stk hf ho]

theorem ch_c0 {c : Nat} (hlt : c < n m0) :
    (ch m0 c).c0 = wordOf m0.dmem (rg m0 .X4 + BitVec.ofNat 64 (16 * c) + BitVec.ofNat 64 0) := by
  rw [ch_eq hlt, NativeRustcVm.addr_add_zero]; rfl

theorem ch_c1 {c : Nat} (hlt : c < n m0) :
    (ch m0 c).c1 = wordOf m0.dmem (rg m0 .X4 + BitVec.ofNat 64 (16 * c) + BitVec.ofNat 64 8) := by
  rw [ch_eq hlt]; rfl

theorem e_c {c : Nat} (hlt : c < m0.regs.X3.toNat) (o : Nat) (ho : o = 0 ∨ o = 8) :
    (if o = 0 then ((E m0).getD c 0).c0 else ((E m0).getD c 0).c1) =
      wordOf m0.dmem (rg m0 .X2 + BitVec.ofNat 64 (16 * c) + BitVec.ofNat 64 o) := by
  rw [E_getD hlt]
  rcases ho with rfl | rfl
  · rw [NativeRustcVm.addr_add_zero]; rfl
  · rfl

theorem headB_b10 : HeadBlock (after b10 headS) := by
  rw [after_eq run_b10]
  exact ⟨rfl, rfl, rfl, by decide, rfl, by decide, rfl, rfl, by decide⟩

theorem headB_b11 : HeadBlock (after b11 (after b10 headS)) := by
  rw [after_eq run_b11]
  exact ⟨rfl, rfl, rfl, by decide, rfl, by decide, rfl, rfl, by decide⟩

theorem keepB_b2 : KeepBlock (after b2 eqS) := by
  rw [after_eq run_b2]
  exact ⟨rfl, rfl, by decide, by decide⟩

theorem keepB_b3 : KeepBlock (after b3 headS) := by
  rw [after_eq run_b3]
  exact ⟨rfl, rfl, by decide, by decide⟩

variable [Labels]

/-- **After `b10`.** -/
theorem hd_of (hc : Ctx m0) {c : Nat} {m st : MachineData} (hit : It m0 c m) {S : SState}
    (hm : Match (Env.ofMachine m [(fb m0, 240), (rg m0 .X4 + BitVec.ofNat 64 (16 * c), 16)]) S st)
    (hb : HeadBlock S) : Hd m0 c st := by
  have hx := hc.ptc hit.lt
  have hwf := hc.wf_in hit.frm hx
  refine ⟨hit.lt, frm_of_match hc.geo hit.frm hwf hm hb.sp hb.writes hb.slots, ?_, ?_, ?_, ?_,
    fun j hj => ?_⟩
  · rw [rg_keep hm (hb.regs .X22 (by simp))]; exact hit.x22
  · rw [rg_keep hm (hb.regs .X23 (by simp))]; exact hit.x23
  · rw [show rg st .X27 = _ from hm.regs .X27 _ hb.x27]
    simp [Sym.eval]
  · rw [show rg st .X24 = _ from hm.regs .X24 _ hb.x24]
    show (Env.ofMachine m _).load 1 8 8 = _
    rw [hc.load_in hit.frm hx (by omega), ch_c1 hit.lt]
  · by_cases hj5 : j < 5
    · obtain ⟨hl, hh⟩ := hb.keep j hj5
      have hw := hit.w j hj5
      exact ⟨by rw [Pl.val_keep hwf hm lo_ok hl, Pl.sym_eval]; exact hw.1,
        by rw [Pl.val_keep hwf hm hi_ok hh, Pl.sym_eval]; exact hw.2⟩
    · obtain rfl : j = 5 := by omega
      exact ⟨by rw [Pl.val_keep hwf hm lo_ok hb.lo5]; exact hit.x0,
        by rw [Pl.val_keep hwf hm hi_ok hb.hi5]; exact hit.x9⟩

/-- The weights and the frame through a block that keeps them. -/
theorem keep_of (hc : Ctx m0) {c : Nat} {m st : MachineData} {x : BitVec 64} (hx : In m0 x 16)
    (hf : Frm m0 m) (hw : ∀ j < 6, WAt m0 m j ((W m0 c).getD j 0)) {S : SState}
    (hm : Match (Env.ofMachine m [(fb m0, 240), (x, 16)]) S st) (hb : KeepBlock S) :
    Frm m0 st ∧ ∀ j < 6, WAt m0 st j ((W m0 c).getD j 0) := by
  have hwf := hc.wf_in hf hx
  refine ⟨frm_of_match hc.geo hf hwf hm hb.sp hb.writes hb.slots, fun j hj => ?_⟩
  obtain ⟨hl, hh⟩ := hb.keep j hj
  exact ⟨by rw [Pl.val_keep hwf hm lo_ok hl, Pl.sym_eval]; exact (hw j hj).1,
    by rw [Pl.val_keep hwf hm hi_ok hh, Pl.sym_eval]; exact (hw j hj).2⟩

end

end NativeRustcVmArm.Tables.TableWeights
