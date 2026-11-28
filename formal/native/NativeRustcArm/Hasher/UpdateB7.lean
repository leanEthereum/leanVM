module

public import NativeRustcArm.Hasher.UpdateAbsorb

/-!
# `Hasher::update`'s loop: emptying the buffer

After `keccak_f`, `b7` stores `0` into `buf_len` and jumps to `.LUpdate_1`: the hasher is the
turn's (`updateStep` of a full buffer, `b7_spec`).
-/

namespace NativeRustcArm.Hasher.Update

open NativeRustc NativeRustc.Keccak LeanVM.Protocol.KeccakHash NativeRustcArm.Sym
open NativeRustcArm.Common.Update NativeRustcArm

public section

variable [Host] {k : Nat}

set_option linter.unusedSimpArgs false in
/-- **Emptying the buffer.** -/
theorem b7_spec (hp : Placed code k) {m0 m1 m : MachineData} (hpre : UpdatePre m0) {c : Nat}
    {Hc : List UInt8} (hab : Absorbed m0 m1 c Hc m) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + NativeRustcArm.Common.Update.b1Offset) ∧ Mid m0 m1 c (takeN m0 c Hc) st.data)
      ⟨m, Host.addrOf (k + NativeRustcArm.Common.Update.b7Offset)⟩ := by
  have g := geo_of hpre
  have hwf := wf_head hpre hab.frame
  have hm := match_headS hab.frame
  have hA := hab.bytes
  generalize hAdef : writeAt (counted m0 c Hc) 0 (absorb ((counted m0 c Hc).take 200)
    (((counted m0 c Hc).drop 200).take 136)) = A at hA
  have hstep : (updateStep Hc ((input m0).drop c)).1 = writeAt A 336 (wordBytes 0) := by
    rw [updateStep_eq, ite_pos' hab.full, hAdef]
  have hlenA : A.length = 344 := by rw [← hA]; exact length_bytesOf ..
  refine exec_then (hb7 hp) run_b7 hwf hm fun st7 hm7 hpc7 => ?_
  simp only [PcOk, lbl_1 hp] at hpc7
  have hmem7 : ∀ j < 344, st7.data.dmem.get? (hAt m0 + BitVec.ofNat 64 j) =
      if 336 ≤ j then some 0 else m.dmem.get? (hAt m0 + BitVec.ofNat 64 j) := by
    intro j hj
    rw [hm7.mem 0 (hAt m0) 344 rfl j hj]
    by_cases h : 336 ≤ j
    · simp only [memByte, findWrite, h, show j < 336 + 8 by omega, and_self, ↓reduceIte, Sym.eval]
      simp [byteOf]
    · simp only [memByte, findWrite, h, false_and, and_false, ↓reduceIte, Env.ofMachine_mem0]
  have hbytes : hasher m0 st7.data = writeAt A 336 (wordBytes 0) := by
    refine ext_getD (by rw [hasher, length_bytesOf, length_writeAt (by simp [length_wordBytes,
      hlenA]), hlenA]) fun j hj => ?_
    rw [hasher, length_bytesOf] at hj
    rw [hasher, getD_bytesOf _ _ hj, hmem7 j hj, getD_writeAt _ _ _ _ (by
      simp [length_wordBytes, hlenA]), length_wordBytes]
    by_cases h : 336 ≤ j
    · rw [ite_pos' h, ite_pos' ⟨h, by omega⟩]
      rw [show wordBytes (0 : UInt64) = List.replicate 8 0 from rfl, List.getD_eq_getElem?_getD,
        List.getElem?_replicate]
      split <;> rfl
    · rw [ite_neg' h, ite_neg' (by omega), ← hA, hasher, getD_bytesOf _ _ hj]
  have hfr : Frame m0 m1 st7.data := by
    refine hab.frame.update (fun r hr => ?_) (UInt64.toBitVec_inj.mp (hm7.sp.trans hm.sp.symm))
      (fun p hp => hm7.get?_mem0 hwf fun hw => hp (Or.inl ((inRange_iff g.h).mpr
        (written_hasher (by decide) hw)))) (hm7.kept hwf)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm hm7 rfl rfl
  have hL := hab.lt
  have hfull := hab.full
  have hle := hab.le
  have ht : takeN m0 c Hc ≤ nOf m0 - c := by unfold takeN; omega
  refine Eventually.done _ ⟨hpc7, hfr, by omega, Or.inl (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Match.reg_atom hm7 rfl]; exact hab.x19
  · rw [Match.reg_atom hm7 rfl]; exact hab.x21
  · rw [Match.reg_atom hm7 rfl]; exact hab.x22
  · show (st7.data.regs.getXReg .X0).toBitVec.toNat = _
    rw [hm7.regs .X0 _ rfl, hbytes, bufLen_writeAt hlenA]
    rfl
  · rw [hbytes, ← hstep]
    exact holds_turn hle hab.holds

end

end NativeRustcArm.Hasher.Update
