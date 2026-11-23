module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.Ext

/-!
# Instance slices used by the output claim

The two source slices partition `inst` at its fourth coordinate, including the short-input case.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.KeccakGkr.SeqZ NativeVm.Model
open NativeRustcVm.Transcript (DecArea)
open NativeRustcVm.KeccakGkr (off)

public section

variable [Labels] {m0 : MachineData} {a : DecArea} {inst : Array EW}

theorem Chg.instAt (c : Ctx a inst m0) {d d' : DataMem} {L : List (Nat × Nat)}
    {O : List (Nat × Nat × Nat)} (h : Chg m0 d d' L O) (hL : okL L = true)
    (hO : okO O = true) (hi : NativeRustcVm.EWsAt d (reg m0 .rdx) inst.toList) :
    NativeRustcVm.EWsAt d' (reg m0 .rdx) inst.toList := by
  apply NativeRustcVm.Tables.EWsAt.of_same (n := 16 * inst.size) hi _ (by simp)
  apply same_num h c.iW
  intro q hq
  apply ChgR.ro c hL hO c.iS _ hq
  intro i h1 h4
  rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
  · exact c.ti
  · exact c.si
  · exact c.ci
  · exact c.oi

theorem instAt_bound (c : Ctx a inst m0) {wr : Nat → Bool} {T : SState}
    {vals : Nat → BitVec 64} {d : MachineData}
    (h : BndZ m0 3344 3368 verifyKeccakStack (rsOf m0) wr T vals d)
    (hi : NativeRustcVm.EWsAt m0.dmem (reg m0 .rdx) inst.toList) :
    NativeRustcVm.EWsAt d.dmem (reg m0 .rdx) inst.toList := by
  apply NativeRustcVm.Tables.EWsAt.of_same (n := 16 * inst.size) hi _ (by simp)
  exact same_ro c h.same c.iW c.iS (fun _ ↦ c.ti.symm) (fun _ ↦ c.si.symm)
    (fun _ ↦ c.ci.symm) (fun _ ↦ c.oi.symm)

theorem min4_value (hsize : inst.size = (reg m0 .rcx).toNat) :
    min4S.eval (Env.ofMachine m0 []) = BitVec.ofNat 64 (min inst.size 4) := by
  unfold min4S
  rw [eval_ite_ult _ _ _ (by decide)]
  change (if (reg m0 .rcx).toNat < 4 then reg m0 .rcx else 4#64) = _
  rw [← hsize]
  split
  · rename_i h
    rw [Nat.min_eq_left (by omega)]
    simp [hsize]
  · rename_i h
    rw [Nat.min_eq_right (by omega)]

theorem hi_value (hsize : inst.size = (reg m0 .rcx).toNat) :
    hiS.eval (Env.ofMachine m0 []) = BitVec.ofNat 64 (inst.size - 4) := by
  unfold hiS
  rw [eval_ite_ult _ _ _ (by decide)]
  change (if (reg m0 .rcx).toNat < 4 then 0#64 else
    BinOp.apply .sub .W64 (reg m0 .rcx) 4#64) = _
  rw [← hsize]
  split
  · rename_i h
    rw [Nat.sub_eq_zero_of_le (by omega)]
  · rename_i h
    simp only [BinOp.apply, low_W64, ext_W64]
    rw [show NativeRustcX64.reg m0 .rcx = BitVec.ofNat 64 inst.size by simp [hsize],
      BitVec.ofNat_sub_ofNat_of_le inst.size 4 (by decide) (by omega)]

theorem high_value (hsize : inst.size = (reg m0 .rcx).toNat) :
    rHighS.eval (Env.ofMachine m0 []) =
      if inst.size < 4 then 8#64 else off (reg m0 .rdx) 64 := by
  unfold rHighS
  change (if !(SBool.cmp .ult .W64 (.reg .rcx) (.lit 4)).eval (Env.ofMachine m0 [])
    then BinOp.apply .add .W64 (reg m0 .rdx) 64#64 else 8#64) = _
  rw [eval_ult (.reg .rcx) (c := 4) (by decide)]
  change (if !(decide ((reg m0 .rcx).toNat < 4)) then
    BinOp.apply .add .W64 (reg m0 .rdx) 64#64 else 8#64) = _
  rw [← hsize, add64]
  by_cases h : inst.size < 4 <;> simp [h, off]

theorem inst_slice_footprint (c : Ctx a inst m0) {wr : Nat → Bool} {mc : MachineData}
    (ca : CallAt m0 wr 48 mc) {j n : Nat} (hjn : j + n ≤ inst.size)
    (hj : (reg m0 .rdx).toNat + 16 * j < 2 ^ 64) :
    Readable mc (off (reg m0 .rdx) (16 * j)) (16 * n) ∧
      Apart (off (fb m0) 408) 584 (off (reg m0 .rdx) (16 * j)) (16 * n) ∧
      OffStack mc (off (reg m0 .rdx) (16 * j)) (16 * n) bufEWExtendStack := by
  have hbase := c.iW
  have hsep := c.iS
  have hK := c.K
  have hsp := c.sp
  have hfb := off_fb c (o := 408) (by decide)
  have hsb := ca.sb c (N := bufEWExtendStack) (by rw [vk_eq]; decide)
  have he : (off (reg m0 .rdx) (16 * j)).toNat = (reg m0 .rdx).toNat + 16 * j :=
    toNat_add_ofNat _ _ hj
  refine ⟨⟨NativeRustcVmX64.Transcript.mapped_off
    (NativeRustcVm.Transcript.Mapped.keeps c.iM ca.kept) (by omega), ?_⟩, ?_, ?_⟩
  · show _ ≤ _
    rw [he]
    omega
  · change _ ∨ _
    rw [he, hfb]
    unfold Sep at hsep
    rw [vk_eq] at hK hsp hsep
    omega
  · change _ ∨ _
    rw [he, hsb]
    unfold Sep at hsep
    rw [vk_eq] at hK hsp hsep
    have := ca.oc8
    simp only [bufEWExtendStack] at *
    omega

theorem low_empty_footprint (c : Ctx a inst m0) {wr : Nat → Bool} {mc : MachineData}
    (ca : CallAt m0 wr 48 mc) {p : BitVec 64} (hp : p.toNat ≤ 8) :
    Readable mc p 0 ∧ Apart (off (fb m0) 408) 584 p 0 ∧
      OffStack mc p 0 bufEWExtendStack := by
  have hfb := off_fb c (o := 408) (by decide)
  have hsb := ca.sb c (N := bufEWExtendStack) (by rw [vk_eq]; decide)
  have hsp := c.sp
  rw [vk_eq] at hsp
  refine ⟨⟨?_, ?_⟩, Or.inr ?_, Or.inl ?_⟩
  · intro i hi
    omega
  · show p.toNat + 0 ≤ 2 ^ 64
    omega
  · rw [hfb]
    omega
  · rw [hsb]
    change p.toNat + 0 ≤ (rspOf m0).toNat - 3344 + 48 - 8
    omega

theorem high_ews {d : DataMem} (hsize : inst.size = (reg m0 .rcx).toNat)
    (hi : NativeRustcVm.EWsAt d (reg m0 .rdx) inst.toList) :
    NativeRustcVm.EWsAt d (rHighS.eval (Env.ofMachine m0 [])) (inst.toList.drop 4) := by
  rw [high_value hsize]
  split
  · rename_i h
    rw [List.drop_eq_nil_of_le (by simp; omega)]
    simp [NativeRustcVm.EWsAt, NativeRustcVm.BytesAt]
  · exact hi.drop 4

theorem high_footprint (c : Ctx a inst m0) {wr : Nat → Bool} {mc : MachineData}
    (ca : CallAt m0 wr 48 mc) (hsize : inst.size = (reg m0 .rcx).toNat) :
    Readable mc (rHighS.eval (Env.ofMachine m0 [])) (16 * (inst.size - 4)) ∧
      Apart (off (fb m0) 408) 584 (rHighS.eval (Env.ofMachine m0 []))
        (16 * (inst.size - 4)) ∧
      OffStack mc (rHighS.eval (Env.ofMachine m0 [])) (16 * (inst.size - 4))
        bufEWExtendStack := by
  rw [high_value hsize]
  split
  · rename_i h
    rw [Nat.sub_eq_zero_of_le (by omega), Nat.mul_zero]
    exact low_empty_footprint c ca (by decide)
  · rename_i h
    have hiW := c.iW
    by_cases hstrict : (reg m0 .rdx).toNat + 64 < 2 ^ 64
    · exact inst_slice_footprint c ca (j := 4) (by omega) hstrict
    · have hs : inst.size = 4 := by omega
      have he : (reg m0 .rdx).toNat + 64 = 2 ^ 64 := by omega
      have hz : off (reg m0 .rdx) 64 = 0#64 := by
        apply BitVec.eq_of_toNat_eq
        change ((reg m0 .rdx).toNat + 64) % 2 ^ 64 = 0
        rw [he, Nat.mod_self]
      rw [hs, hz]
      exact low_empty_footprint c ca (by decide)

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
