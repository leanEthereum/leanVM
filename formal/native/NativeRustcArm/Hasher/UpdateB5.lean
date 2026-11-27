module

public import NativeRustcArm.Hasher.UpdateCopy

/-!
# `Hasher::update`'s loop: counting the copied bytes

After `memcpy`, `b5` stores `buf_len + t` into `buf_len` and goes to `.LUpdate_1` unless the
buffer is full (`b5_spec`): then the hasher is the turn's (`updateStep`, `Mid`); else it falls
through to the absorption (`Full`). The turn's bytes in the model: `takeN`, `copied`, `counted`,
`updateStep_eq`.
-/

namespace NativeRustcArm.Hasher.Update

open NativeRustc NativeRustc.Keccak LeanVM.Protocol.KeccakHash NativeRustcArm.Sym NativeRustcArm.Common.Update NativeRustcArm

@[expose] public section

/-- The bytes a turn from the hasher `Hc`, `c` input bytes absorbed, takes. -/
def takeN (m0 : MachineData) (c : Nat) (Hc : List UInt8) : Nat := min (136 - bufLen Hc) (nOf m0 - c)

/-- The hasher with them copied into its buffer. -/
def copied (m0 : MachineData) (c : Nat) (Hc : List UInt8) : List UInt8 :=
  writeAt Hc (200 + bufLen Hc) (((input m0).drop c).take (takeN m0 c Hc))

/-- And `buf_len` advanced. -/
def counted (m0 : MachineData) (c : Nat) (Hc : List UInt8) : List UInt8 :=
  writeAt (copied m0 c Hc) 336 (wordBytes (bufLen Hc + takeN m0 c Hc).toUInt64)

/-- At the absorption (`b6`): the buffer is full. -/
structure Full (m0 m1 : MachineData) (c : Nat) (Hc : List UInt8) (m : MachineData) : Prop where
  frame : Frame m0 m1 m
  le : c ≤ nOf m0
  x19 : (m.regs.getXReg .X19).toBitVec = BitVec.ofNat 64 (nOf m0 - c)
  x21 : (m.regs.getXReg .X21).toBitVec = dAt m0 + BitVec.ofNat 64 c
  x22 : (m.regs.getXReg .X22).toBitVec = BitVec.ofNat 64 (takeN m0 c Hc)
  holds : Holds m0 Hc c
  lt : bufLen Hc < 136
  len : Hc.length = 344
  full : bufLen Hc + takeN m0 c Hc = 136
  bytes : hasher m0 m = counted m0 c Hc

end

public section

theorem length_input (m0 : MachineData) : (input m0).length = nOf m0 := length_bytesOf ..

/-- **A turn of the model's loop**, as the code runs it. -/
theorem updateStep_eq (m0 : MachineData) (c : Nat) (Hc : List UInt8) :
    (updateStep Hc ((input m0).drop c)).1 =
      if bufLen Hc + takeN m0 c Hc = 136 then
        writeAt (writeAt (counted m0 c Hc) 0 (absorb ((counted m0 c Hc).take 200)
          (((counted m0 c Hc).drop 200).take 136))) 336 (wordBytes 0)
      else counted m0 c Hc := by
  unfold updateStep counted copied takeN
  rw [List.length_drop, length_input]
  by_cases h : bufLen Hc + min (136 - bufLen Hc) (nOf m0 - c) = 136 <;> simp only [h, ↓reduceIte]

theorem holds_turn {m0 : MachineData} {c : Nat} {Hc : List UInt8} (hle : c ≤ nOf m0)
    (hh : Holds m0 Hc c) : Holds m0 (updateStep Hc ((input m0).drop c)).1 (c + takeN m0 c Hc) := by
  intro a ha
  have := holds_updateStep_drop (D := input m0) (by rw [length_input]; exact hle) hh a ha
  rwa [length_input] at this

variable [ElfHost] {sec k : Nat}

set_option linter.unusedSimpArgs false in
/-- **Counting the copied bytes**: to `.LUpdate_1` after the turn, or to the absorption. -/
theorem b5_spec (hp : PlacedIn code sec k) {m0 m1 m : MachineData} (hpre : UpdatePre m0) {c : Nat}
    {Hc : List UInt8} (hcp : Copied m0 m1 c Hc m) :
    Eventually (elfStep1 ElfHost.exe)
      (fun st => (st.pc = ElfHost.addrOf sec (k + NativeRustcArm.Common.Update.b1Offset) ∧ Mid m0 m1 c (takeN m0 c Hc) st.data) ∨
        (st.pc = ElfHost.addrOf sec (k + NativeRustcArm.Common.Update.b6Offset) ∧ Full m0 m1 c Hc st.data))
      ⟨m, ElfHost.addrOf sec (k + NativeRustcArm.Common.Update.b5Offset)⟩ := by
  have g := geo_of hpre
  have hwf := wf_head hpre hcp.frame
  have hm := match_headS hcp.frame
  have hb0 : (Env.ofMachine m [(hAt m0, 344)]).base 0 = hAt m0 := Env.base_ofMachine m _ _ rfl
  have hn : nOf m0 < 2 ^ 64 := UInt64.toNat_lt _
  have hle := hcp.le
  have hL := hcp.lt
  generalize hLdef : bufLen Hc = L at hL
  generalize htdef : takeN m0 c Hc = t
  have ht : t ≤ 136 - L ∧ t ≤ nOf m0 - c ∧ (0 < t ∨ c = nOf m0) := by
    rw [← htdef, takeN, hLdef]
    omega
  have hcop : hasher m0 m = copied m0 c Hc := hcp.bytes
  have hclen : (copied m0 c Hc).length = 344 := by rw [← hcop]; exact length_bytesOf ..
  -- `buf_len`'s bytes are the hasher's at the loop head.
  have hs : (((input m0).drop c).take (takeN m0 c Hc)).length = t := by
    rw [List.length_take, List.length_drop, length_input, ← htdef, takeN, hLdef]
    omega
  have h336 : (hasher m0 m).drop 336 = Hc.drop 336 := by
    rw [hcop]
    refine ext_getD (by simp [hclen, hcp.len]) fun j hj => ?_
    simp only [List.length_drop, hclen] at hj
    rw [Native.Keccak.Proof.getD_drop, Native.Keccak.Proof.getD_drop, copied, getD_writeAt _ _ _ _ (by rw [hs, hcp.len]; omega), hs,
      hLdef, ite_neg' (by omega)]
  have hload : (Env.ofMachine m [(hAt m0, 344)]).load 0 336 8 =
      BitVec.ofInt 64 (Int.ofBytes (Hc.drop 336)) := by
    refine Env.load_of_bytesAt (by simp [hcp.len]) ?_
    rw [hb0, ← h336]
    have := bytesAt_bytesOf (d := m.dmem) (a := hAt m0 + BitVec.ofNat 64 336) (n := 8)
      fun i hi => by rw [add_ofNat_add]; exact hcp.frame.kept _ (hpre.2.2.2.1 _ (by omega))
    rwa [bytesOf_add _ _ (n := 344) (by omega), List.take_of_length_le (by simp [length_bytesOf])]
      at this
  have hV0 : (BitVec.ofInt 64 (Int.ofBytes (Hc.drop 336))).toNat = L := by
    rw [← hLdef, bufLen, lane_ofBytes (by simp [hcp.len])]
    rfl
  have hx22 : (m.regs.getXReg .X22).toBitVec = BitVec.ofNat 64 t := by
    rw [hcp.x22, ← htdef]
    rfl
  have hV : BitVec.ofInt 64 (Int.ofBytes (Hc.drop 336)) + BitVec.ofNat 64 t =
      BitVec.ofNat 64 (L + t) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hV0, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  refine exec_then_elf (hb5 hp) run_b5 hwf hm fun st5 hm5 hpc5 => ?_
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
    Env.ofMachine_regs, hload, hx22, hV, Nat.add_assoc, NativeRustcArm.Common.Update.b5_next] at hpc5
  -- Memory: the new `buf_len`.
  have hmem5 : ∀ j < 344, st5.data.dmem.get? (hAt m0 + BitVec.ofNat 64 j) =
      if 336 ≤ j then some (byteOf (BitVec.ofNat 64 (L + t)) (j - 336))
      else m.dmem.get? (hAt m0 + BitVec.ofNat 64 j) := by
    intro j hj
    rw [hm5.mem 0 (hAt m0) 344 rfl j hj]
    by_cases h : 336 ≤ j
    · simp only [memByte, findWrite, h, show j < 336 + 8 by omega, and_self, ↓reduceIte, Sym.eval,
        BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, hload, hx22, hV]
    · simp only [memByte, findWrite, h, false_and, and_false, ↓reduceIte, Env.ofMachine_mem0]
  have hcnt : counted m0 c Hc = writeAt (copied m0 c Hc) 336 (wordBytes (L + t).toUInt64) := by
    rw [counted, hLdef, htdef]
  have hbytes : hasher m0 st5.data = counted m0 c Hc := by
    rw [hcnt]
    refine ext_getD (by rw [hasher, length_bytesOf, length_writeAt (by simp [length_wordBytes, hclen]),
      hclen]) fun j hj => ?_
    rw [hasher, length_bytesOf] at hj
    rw [hasher, getD_bytesOf _ _ hj, hmem5 j hj, getD_writeAt _ _ _ _ (by
      simp [length_wordBytes, hclen]), length_wordBytes]
    by_cases h : 336 ≤ j
    · rw [ite_pos' h, ite_pos' ⟨h, by omega⟩,
        show (L + t).toUInt64 = UInt64.ofBitVec (BitVec.ofNat 64 (L + t)) from rfl,
        wordBytes_ofBitVec]
      simp [List.getD_eq_getElem?_getD, show j - 336 < 8 by omega]
    · rw [ite_neg' h, ite_neg' (by omega), ← hcop, hasher, getD_bytesOf _ _ hj]
  have hfr : Frame m0 m1 st5.data := by
    refine hcp.frame.update (fun r hr => ?_) (UInt64.toBitVec_inj.mp (hm5.sp.trans hm.sp.symm))
      (fun p hp => hm5.get?_mem0 hwf ?_) (hm5.kept hwf)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm hm5 rfl rfl
    · rintro ⟨w, hw, b, sz, hb, h1, h2⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw
      simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact hp (Or.inl ((inRange_iff g.h).mpr ⟨by simp at h1; omega, by simp at h2; omega⟩))
  have hx19 : (st5.data.regs.getXReg .X19).toBitVec = BitVec.ofNat 64 (nOf m0 - c) := by
    rw [Match.reg_atom hm5 rfl]; exact hcp.x19
  have hx21 : (st5.data.regs.getXReg .X21).toBitVec = dAt m0 + BitVec.ofNat 64 c := by
    rw [Match.reg_atom hm5 rfl]; exact hcp.x21
  have hx22' : (st5.data.regs.getXReg .X22).toBitVec = BitVec.ofNat 64 t := by
    rw [Match.reg_atom hm5 rfl]; exact hx22
  refine Eventually.done _ ?_
  by_cases hfull : L + t = 136
  · right
    rw [ite_neg' (by simp [hfull])] at hpc5
    refine ⟨hpc5, hfr, hle, hx19, hx21, htdef ▸ hx22', hcp.holds, hcp.lt, hcp.len,
      by rw [hLdef, htdef]; exact hfull, hbytes⟩
  · left
    rw [ite_pos' (by
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      omega), lbl_1 hp] at hpc5
    have hstep : hasher m0 st5.data = (updateStep Hc ((input m0).drop c)).1 := by
      rw [hbytes, updateStep_eq, hLdef, htdef, ite_neg' hfull]
    refine ⟨hpc5, ⟨hfr, by omega, by rw [← htdef]; omega, hx19, hx21, htdef ▸ hx22', ?_, ?_⟩⟩
    · show (st5.data.regs.getXReg .X0).toBitVec.toNat = _
      rw [hm5.regs .X0 _ rfl]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, hload, hx22, hV]
      rw [hbytes, hcnt, bufLen_writeAt hclen, BitVec.toNat_ofNat]
      rfl
    · rw [hstep, ← htdef]
      exact holds_turn hle hcp.holds

end

end NativeRustcArm.Hasher.Update
