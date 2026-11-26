module

public import NativeRustcArm.SphincsVerify.Fors.TreeB

/-!
# A FORS tree's end: its root stored (`b84`)

From `TEnd c` (`b84`): the root at `12864` stored at `20064 + 16 c` (the `stp` runs in the
environment of the root's 16 bytes), the next tree's registers, and the loop's branch: the next
tree's head `AtTree (c + 1)` at `b51`, or after the 24th, `AtForsKey` at `b85`.
-/

namespace NativeRustcArm.SphincsVerifyProof.Fors

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm
  LeanVM.Protocol.KeccakHash Native.Keccak
open NativeRustcArm.Sphincs.SphincsVerify

public section

variable {r : Run} [Labels]

/-- A change in the frame's bytes `a .. a + n` above the leaves keeps the bytes `Low` keeps. -/
theorem low_of_same (hpre : r.Pre) {m m' : MachineData} {a n : Nat} (ha : 18184 ≤ a)
    (han : a + n ≤ 21616) (hout : SameOutside m.dmem m'.dmem (InRange (r.off a) n)) :
    Low r m m' := by
  intro o ho
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  apply hout
  rw [inRange_iff (by rw [r.off_toNat hpre (by omega)]; omega), r.off_toNat hpre (by omega),
    r.off_toNat hpre (by omega)]
  omega

/-- The bytes `o .. o + len` of the frame, apart from `a .. a + n`, kept by a change there. -/
theorem bytesAt_of_same (hpre : r.Pre) {m m' : MachineData} {a n : Nat} (han : a + n ≤ 21616)
    (hout : SameOutside m.dmem m'.dmem (InRange (r.off a) n)) {o : Nat} {bs : List UInt8}
    (ho : o + bs.length ≤ 21616) (hd : o + bs.length ≤ a ∨ a + n ≤ o)
    (h : BytesAt m.dmem (r.off o) bs) : BytesAt m'.dmem (r.off o) bs :=
  bytesAt_of_sameOutside h hout fun i hi hin ↦ by
    have hb := r.base_toNat hpre
    have := r.m0.regs.SP.toNat_lt
    rw [Run.off_add, inRange_iff (by rw [r.off_toNat hpre (by omega)]; omega),
      r.off_toNat hpre (by omega), r.off_toNat hpre (by omega)] at hin
    omega

omit [Labels] in
theorem roots_succ (c : Nat) :
    ((List.range (c + 1)).map r.forsRoot).flatten =
      ((List.range c).map r.forsRoot).flatten ++ r.forsRoot c := by
  rw [List.range_succ, List.map_append, List.flatten_append]
  simp

omit [Labels] in
theorem shl4' (c : Nat) :
    BitVec.ofNat 64 c <<< 4 = BitVec.ofNat 64 (16 * c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

end

public section

variable {r : Run} [Host]

/-- **A tree's end** (`b84`): from `TEnd c`, the next tree's head, or after the 24th, `b85`. -/
theorem tree_end (hp : Placed code r.k) (hpre : r.Pre) {c : Nat} {m : MachineData}
    (h : TEnd r c m) :
    Eventually (step1 Host.exe)
      (fun st ↦ (c + 1 < 24 ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b51Offset ∧ AtTree r (c + 1) st.data) ∨
        (c + 1 = 24 ∧ st.pc = r.pc NativeRustcArm.Sphincs.SphincsVerify.b85Offset ∧ r.AtForsKey st.data)) ⟨m, r.pc NativeRustcArm.Sphincs.SphincsVerify.b84Offset⟩ := by
  obtain ⟨hT, h19, h25, h23, h20, h27, hcur⟩ := h
  have hB := hT.base
  have hc24 := hT.hc
  have h19' : (m.regs.getXReg .X19).toBitVec = BitVec.ofNat 64 c := h19
  have hcl : (r.forsUpTo c 10).length = 16 := length_forsUpTo c 10
  have hrl := length_rootsMem (r := r) hc24.le
  -- `b84a`: the root's address, the next tree's registers
  have hwf := r.frame_wf hpre hB.frame (fun _ ↦ 0)
  have hm : Match (r.env m) s0 m := match_frameS hpre hB trivial trivial
  refine exec_then (hb84a hp) run_b84a hwf hm fun st1 hm1 hpc1 ↦ ?_
  have hd1 : st1.data.dmem = m.dmem := hm1.dmem_eq hwf rfl
  obtain ⟨hB1, -⟩ := hB.of_match hpre hm1 hwf rfl rfl rfl rfl rfl rfl
  have h8 : Run.RegIs st1.data .X8 (r.off (20064 + 16 * c)) := by
    rw [Run.RegIs, hm1.regs .X8 _ rfl]
    simp only [Sym.eval, BinOp.apply, UnOp.apply, low_W64, ext_W64, shiftW, Env.ofMachine_regs,
      h19', shl4']
    have e : (r.env m).base 0 + BitVec.ofInt 64 20064 = r.off 20064 := by
      show r.base + _ = r.base + _
      simp
    rw [e, Run.off_add]
  -- `b84b`: the root stored, in the environment of its 16 bytes
  refine ev_at (hpc1.trans (pc_after (by rfl))) ?_
  have hslot : 20064 + 16 * c + 16 ≤ 21520 := by omega
  have hwf2 : (Env.ofMachine st1.data [(r.off (20064 + 16 * c), 16)]).WF :=
    Env.wf_of ⟨r.frame_mapped hpre hB1.frame (by omega), trivial⟩ (List.pairwise_singleton _ _)
  have hm2 : Match (Env.ofMachine st1.data [(r.off (20064 + 16 * c), 16)]) (ldS .X8) st1.data :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl
      ⟨by
        show _ = r.off (20064 + 16 * c) + BitVec.ofInt 64 0
        rw [h8]
        simp, trivial⟩ trivial trivial trivial
  refine exec_then (hb84b hp) run_b84b hwf2 hm2 fun st2 hm2' hpc2 ↦ ?_
  have hout2 := same_of_one hm2' hwf2 rfl
  have hF2 : r.Frame st2.data :=
    Run.Frame.of_block hB1.frame (by rw [sp_of hm2' rfl]; exact hB1.frame.1)
      (by rw [reg_of hm2' rfl]; exact hB1.frame.2.1) hout2
      (fun p hp ↦ r.inRange_off hpre (a := 20064 + 16 * c) (n := 16) hslot hp) (hm2'.kept hwf2)
  have hB2 : Base r st2.data := hB1.of_keep (low_of_same hpre (by omega) (by omega) hout2) hF2
    (reg_of hm2' rfl) (reg_of hm2' rfl) (reg_of hm2' rfl)
  have hroot : BytesAt st2.data.dmem (r.off (20064 + 16 * c)) (r.forsUpTo c 10) := by
    have hc0 := bytesAt_slice hcur 0 8
    have hc8 := bytesAt_slice hcur 8 8
    rw [List.drop_zero, Nat.add_zero] at hc0
    have e0 : (List.range 8).map (byteOf ((r.env m).load 0 12864 8)) = (r.forsUpTo c 10).take 8 :=
      bytes_load hc0 (by simp [hcl]) le_rfl
    have e8 : (List.range 8).map (byteOf ((r.env m).load 0 12872 8)) =
        ((r.forsUpTo c 10).drop 8).take 8 :=
      bytes_load hc8 (by simp [hcl]) le_rfl
    have x9 : (st1.data.regs.getXReg .X9).toBitVec = (r.env m).load 0 12864 8 := hm1.regs .X9 _ rfl
    have x10 : (st1.data.regs.getXReg .X10).toBitVec = (r.env m).load 0 12872 8 :=
      hm1.regs .X10 _ rfl
    refine pieces16 hcl ?_ ?_
    · have := hm2'.bytesAt_write (r := 0) (o := 0) (n := 8) (v := .reg .X9) rfl (by decide)
        (by decide)
      rw [Run.off_add, Nat.add_zero] at this
      simp only [Sym.eval, Env.ofMachine_regs, x9, e0] at this
      exact this
    · have := hm2'.bytesAt_write (r := 0) (o := 8) (n := 8) (v := .reg .X10) rfl (by decide)
        (by decide)
      rw [Run.off_add] at this
      simp only [Sym.eval, Env.ofMachine_regs, x10, e8] at this
      exact this
  have hroots2 : BytesAt st2.data.dmem (r.off 20064) ((List.range (c + 1)).map r.forsRoot).flatten := by
    rw [roots_succ, Run.forsRoot_eq r hc24]
    refine bytesAt_cat (n := 16 * c) hrl ?_ hroot
    exact bytesAt_of_same hpre (by omega) hout2 (by rw [hrl]; omega) (by rw [hrl]; omega)
      (hd1 ▸ hT.roots)
  -- the loop's test
  have hz : st2.data.status.z = decide (c + 1 = 24) := by
    have e2 := hm2'.flags _ rfl
    have e1 := hm1.flags _ rfl
    rw [e2]
    show st1.data.status.z = _
    rw [e1]
    simp only [SFlags.eval, SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64,
      Env.ofMachine_regs, h19']
    rw [show BitVec.ofNat 64 c + BitVec.ofNat 64 1 = BitVec.ofNat 64 (c + 1) from
      (BitVec.ofNat_add c 1).symm]
    exact ofNat_beq_ofNat (by omega) (by decide)
  -- `b84c`
  refine ev_at (hpc2.trans (pc_after (by rfl))) ?_
  have hwf3 := r.frame_wf hpre hB2.frame (fun _ ↦ 0)
  have hm3 : Match (r.env st2.data) s84c st2.data := match_frameS hpre hB2 trivial trivial
  refine exec_then (hb84c hp) run_b84c hwf3 hm3 fun st3 hm3' hpc3 ↦ ?_
  have hd3 : st3.data.dmem = st2.data.dmem := hm3'.dmem_eq hwf3 rfl
  obtain ⟨hB3, -⟩ := hB2.of_match hpre hm3' hwf3 rfl rfl rfl rfl rfl rfl
  simp only [PcOk, SBool.eval] at hpc3
  change st3.pc = if (!st2.data.status.z) = true then _ else _ at hpc3
  rw [hz] at hpc3
  have e20 : wordBytes (st3.data.regs.getXReg .X20) = be64 (r.key 0).tree := by
    rw [reg_of hm3' rfl, reg_of hm2' rfl, reg_of hm1 rfl]; exact h20
  have e25 : Run.RegIs st3.data .X25 (kpW r) := by
    rw [Run.RegIs, reg_of hm3' rfl, reg_of hm2' rfl, reg_of hm1 rfl]; exact h25
  have e23 : Run.RegIs st3.data .X23 (r.off 15936) := by
    rw [Run.RegIs, reg_of hm3' rfl, reg_of hm2' rfl, reg_of hm1 rfl]; exact h23
  have e27 : Run.RegIs st3.data .X27 (r.off 19008) := by
    rw [Run.RegIs, reg_of hm3' rfl, reg_of hm2' rfl, reg_of hm1 rfl]; exact h27
  by_cases hc1 : c + 1 = 24
  · rw [decide_eq_true hc1] at hpc3
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc3
    refine .done _ (Or.inr ⟨hc1, hpc3.trans (pc_after (by rfl)), hB3.frame, hB3.inputs, e20,
      ?_, e23, e27, ?_, hB3.w400, hB3.w408⟩)
    · rw [show st3.data.regs.getXReg .X25 = UInt64.ofBitVec (kpW r) from UInt64.toBitVec_inj.mp e25]
      exact wordBytes_kpW r
    · rw [hd3, ← hc1]; exact hroots2
  · rw [decide_eq_false hc1] at hpc3
    simp only [Bool.not_false, ↓reduceIte] at hpc3
    refine .done _ (Or.inl ⟨by omega, hpc3.trans (lbl_13 hp), ⟨⟨hB3, by omega, hd3 ▸ hroots2⟩,
      ?_, ?_, ?_, ?_, e23, ?_, e25, e20⟩⟩)
    · rw [Run.RegIs, reg_of hm3' rfl, reg_of hm2' rfl, hm1.regs .X19 _ rfl]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, h19']
      exact (BitVec.ofNat_add c 1).symm
    · rw [Run.RegIs, reg_of hm3' rfl, reg_of hm2' rfl, hm1.regs .X24 _ rfl]
      exact load_word hB.w416
    · exact (hm3'.regs .X9 _ rfl).trans (eval_ptr 484)
    · exact hm3'.regs .X8 _ rfl
    · exact hm3'.regs .X10 _ rfl

end

end NativeRustcArm.SphincsVerifyProof.Fors
