module

public import NativeRustcArm.Code.Common.Memcpy.Names

public import NativeRustcArm.Hasher.UpdateGeom

/-!
# `Hasher::update`'s loop: copying into the buffer

From the loop head (`Inv`), `b2`–`b4` take `t = min (136 - buf_len) remaining` bytes (the slice
bounds checks, branches to `slice_index_fail`, fail since `buf_len < 136`) and call
`memcpy(buf + buf_len, data, t)`; on its return the hasher is the one before with those bytes
written after the buffered ones (`Copied`, `copy_spec`).
-/

namespace NativeRustcArm.Hasher.Update

open NativeRustc NativeRustc.Keccak NativeRustcArm.Sym NativeRustcArm.Common.Update NativeRustcArm

@[expose] public section

/-- After `memcpy`: the hasher `Hc` of the loop head with `t` input bytes copied into its buffer;
X19, X21 as at the loop head and X22 `t`. -/
structure Copied (m0 m1 : MachineData) (c : Nat) (Hc : List UInt8) (m : MachineData) : Prop where
  frame : Frame m0 m1 m
  le : c ≤ nOf m0
  x19 : (m.regs.getXReg .X19).toBitVec = BitVec.ofNat 64 (nOf m0 - c)
  x21 : (m.regs.getXReg .X21).toBitVec = dAt m0 + BitVec.ofNat 64 c
  x22 : (m.regs.getXReg .X22).toBitVec =
    BitVec.ofNat 64 (min (136 - bufLen Hc) (nOf m0 - c))
  holds : Holds m0 Hc c
  lt : bufLen Hc < 136
  len : Hc.length = 344
  bytes : hasher m0 m = writeAt Hc (200 + bufLen Hc)
    (((input m0).drop c).take (min (136 - bufLen Hc) (nOf m0 - c)))

end

public section

/-- The count `csel` picks: the remaining bytes, or the room in the buffer if less. -/
theorem toNat_take {x0 x19 : BitVec 64} (h : x0.toNat < 136) :
    (if x19.ult (BitVec.ofNat 64 136 - x0) = true then x19 else BitVec.ofNat 64 136 - x0).toNat =
      min (136 - x0.toNat) x19.toNat := by
  have h1 : (BitVec.ofNat 64 136 - x0).toNat = 136 - x0.toNat := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  by_cases hc : x19.toNat < 136 - x0.toNat
  · rw [ite_pos' (by simp [BitVec.ult, h1, hc])]
    omega
  · rw [ite_neg' (by simp [BitVec.ult, h1, hc]), h1]
    omega

theorem inRange_zero {a p : BitVec 64} : ¬InRange a 0 p := Nat.not_lt_zero _

variable [ElfHost] {sec k : Nat}

/-- **Copying into the buffer.** -/
theorem copy_spec (hp : PlacedIn code sec k)
    (hmemcpy : ElfSpec (Labels.label NativeRustcArm.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {m0 m1 m : MachineData} (hpre : UpdatePre m0)
    (h01 : SameOutside m0.dmem m1.dmem (InRange (spAt m0 - 64#64) 64)) {c : Nat}
    (hinv : Inv m0 m1 c m) :
    Eventually (elfStep1 ElfHost.exe)
      (fun st => st.pc = ElfHost.addrOf sec (k + NativeRustcArm.Common.Update.b5Offset) ∧ Copied m0 m1 c (hasher m0 m) st.data)
      ⟨m, ElfHost.addrOf sec (k + NativeRustcArm.Common.Update.b2Offset)⟩ := by
  have g := geo_of hpre
  obtain ⟨a0, ha0⟩ := hpre.2.2.1
  have hHc := hinv.holds a0 ha0
  have hlen : (hasher m0 m).length = 344 := length_bytesOf ..
  have hL : bufLen (hasher m0 m) < 136 := by
    rw [bufLen_of_holds hHc]
    exact Nat.mod_lt _ (by omega)
  have hn : nOf m0 < 2 ^ 64 := UInt64.toNat_lt _
  have hle := hinv.le
  generalize hLdef : bufLen (hasher m0 m) = L at hL
  have hx0 : (m.regs.getXReg .X0).toBitVec.toNat = L := hLdef ▸ hinv.x0
  have hmap : Mapped m.dmem (hAt m0) 344 := fun i hi => hinv.frame.kept _ (hpre.2.2.2.1 i hi)
  have hwf : (Env.ofMachine m [(hAt m0, 344)]).WF :=
    Env.wf_of ⟨⟨hmap, g.h⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hb0 : (Env.ofMachine m [(hAt m0, 344)]).base 0 = hAt m0 := Env.base_ofMachine m _ _ rfl
  have hm : Match (Env.ofMachine m [(hAt m0, 344)]) headS m :=
    match_ofMachine ⟨rfl, by simp, trivial⟩ rfl
      ⟨by simp only [Sym.eval, hb0, hinv.frame.x20]; simp,
        by simp only [Sym.eval, hb0, hinv.frame.x23]; rfl,
        by simp only [Sym.eval, hinv.frame.x24], trivial⟩
      trivial trivial trivial
  -- The take `csel` computes.
  have hx19 := hinv.x19
  have hx19n : (m.regs.getXReg .X19).toBitVec.toNat = nOf m0 - c := by
    rw [hx19, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨TV, hTV, htv⟩ : ∃ TV, (if (m.regs.getXReg .X19).toBitVec.ult
      (136#64 - (m.regs.getXReg .X0).toBitVec) = true then (m.regs.getXReg .X19).toBitVec
      else 136#64 - (m.regs.getXReg .X0).toBitVec) = TV ∧ TV.toNat = min (136 - L) (nOf m0 - c) :=
    ⟨_, rfl, by rw [toNat_take (by rw [hx0]; exact hL), hx0, hx19n]⟩
  -- `b2`: the take, and `b.lo` to the panic not taken.
  refine exec_then_elf (hb2 hp) run_b2 hwf hm fun st2 hm2 hpc2 => ?_
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
    Env.ofMachine_regs, hTV] at hpc2
  rw [ite_neg' (by
    simp only [BitVec.ult, BitVec.toNat_add, htv, hx0, decide_eq_true_eq, MemWidth.bits]
    omega)] at hpc2
  -- `b3`: `b.hs` to the panic not taken.
  refine exec_at_elf (hb3 hp) (exec_after run_b2 run_b3) hwf hpc2 hm2 fun st3 hm3 hpc3 => ?_
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
    Env.ofMachine_regs, hTV] at hpc3
  rw [ite_neg' (by
    simp only [BitVec.ult, BitVec.toNat_add, htv, hx0, BitVec.toNat_ofNat, Bool.not_eq_true',
      decide_eq_false_iff_not, Nat.not_lt, MemWidth.bits]
    omega)] at hpc3
  -- `b4`: `memcpy`'s arguments.
  have hr4 := run_b4
  rw [after_eq run_b2] at hr4
  refine exec_at_elf (hb4 hp) (exec_after (exec_after run_b2 run_b3) hr4) hwf hpc3 hm3
    fun st4 hm4 hpc4 => ?_
  have hmem4 : ∀ p, st4.data.dmem.get? p = m.dmem.get? p := fun p =>
    hm4.get?_mem0 hwf fun ⟨_, hw, _⟩ => by simp at hw
  have hX0 : (st4.data.regs.getXReg .X0).toBitVec = hAt m0 + BitVec.ofNat 64 (200 + L) := by
    rw [hm4.regs .X0 _ rfl]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs, hb0]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hx0, MemWidth.bits,
      show BitVec.ofInt 64 200 = 200#64 from rfl]
    have := g.h
    omega
  have hX1 : (st4.data.regs.getXReg .X1).toBitVec = dAt m0 + BitVec.ofNat 64 c := by
    rw [hm4.regs .X1 _ rfl]
    exact hinv.x21
  have hX22 : (st4.data.regs.getXReg .X22).toBitVec = TV := by
    rw [hm4.regs .X22 _ rfl]
    simp only [Sym.eval, SBool.eval, BinOp.apply, CmpOp.apply, low_W64, ext_W64,
      Env.ofMachine_regs, hTV]
  have hX2 : (st4.data.regs.getXReg .X2).toNat = min (136 - L) (nOf m0 - c) := by
    show (st4.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [hm4.regs .X2 _ rfl]
    simp only [Sym.eval, SBool.eval, BinOp.apply, CmpOp.apply, low_W64, ext_W64,
      Env.ofMachine_regs, hTV, htv]
  generalize htdef : min (136 - L) (nOf m0 - c) = t at hX2
  have ht : t ≤ 136 - L ∧ t ≤ nOf m0 - c := by omega
  refine call_then_elf hpc4 hmemcpy ?pre fun st' hpc' hpost => ?_
  case pre =>
    refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_⟩
    · show (st4.data.dmem.get? ((st4.data.regs.getXReg .X0).toBitVec + _)).isSome
      have hi' : i < t := by rw [← hX2]; exact hi
      rw [hX0, add_ofNat_add, hmem4]
      exact hmap _ (by omega)
    · show (st4.data.dmem.get? ((st4.data.regs.getXReg .X1).toBitVec + _)).isSome
      have hi' : i < t := by rw [← hX2]; exact hi
      rw [hX1, add_ofNat_add, hmem4]
      exact hinv.frame.kept _ (hpre.2.2.2.2.2.1 _ (by unfold nOf at hle ht; omega))
    · show (st4.data.regs.getXReg .X0).toBitVec.toNat + (st4.data.regs.getXReg .X2).toNat ≤ _
      rw [hX0, hX2, toNat_add_ofNat' (by have := g.h; omega)]
      have := g.h
      omega
    · show (st4.data.regs.getXReg .X1).toBitVec.toNat + (st4.data.regs.getXReg .X2).toNat ≤ _
      rw [hX1, hX2]
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [h0]
        exact Nat.le_of_lt (BitVec.isLt _)
      · rw [toNat_add_ofNat' (by have := g.d; omega)]
        have := g.d
        omega
    · show (st4.data.regs.getXReg .X0).toBitVec.toNat + (st4.data.regs.getXReg .X2).toNat ≤
          (st4.data.regs.getXReg .X1).toBitVec.toNat ∨ (st4.data.regs.getXReg .X1).toBitVec.toNat +
          (st4.data.regs.getXReg .X2).toNat ≤ (st4.data.regs.getXReg .X0).toBitVec.toNat
      rw [hX0, hX1, hX2]
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [h0, Nat.add_zero, Nat.add_zero]
        exact Nat.le_total _ _
      · rw [toNat_add_ofNat' (by have := g.h; omega), toNat_add_ofNat' (by have := g.d; omega)]
        have := g.hd
        omega
  obtain ⟨-, hbytes, hsame, hsaved⟩ := hpost
  have h0' : st4.data.regs.X0.toBitVec = _ := hX0
  have h1' : st4.data.regs.X1.toBitVec = _ := hX1
  have h2' : st4.data.regs.X2.toNat = _ := hX2
  rw [h0', h1', h2'] at hbytes
  rw [h0', h2'] at hsame
  have hreg : ∀ r, calleeSaved r = true → st'.data.regs.getXReg r = st4.data.regs.getXReg r :=
    hsaved.1
  have hfr : Frame m0 m1 st'.data := by
    refine hinv.frame.update (fun r hr => ?_) (hsaved.2.1.trans (UInt64.toBitVec_inj.mp
      (hm4.sp.trans hm.sp.symm))) (fun p hp => ?_) (fun p hp => hsaved.2.2 p (by rw [hmem4]; exact hp))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact (hreg _ rfl).trans (Match.reg_eq hm hm4 rfl rfl)
    · rw [hsame p fun hr => hp (Or.inl ?_), hmem4]
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        exact absurd hr inRange_zero
      · rw [inRange_iff (by rw [toNat_add_ofNat' (by have := g.h; omega)]; have := g.h; omega),
          toNat_add_ofNat' (by have := g.h; omega)] at hr
        rw [inRange_iff g.h]
        omega
  refine Eventually.done _ ⟨by rw [hpc']; rfl, hfr, hle, ?_, ?_, ?_, hinv.holds, hLdef ▸ hL, hlen, ?_⟩
  · rw [hreg .X19 rfl, Match.reg_atom hm4 rfl]
    exact hx19
  · rw [hreg .X21 rfl, Match.reg_atom hm4 rfl]
    exact hinv.x21
  · rw [hreg .X22 rfl, hLdef, htdef, hX22]
    apply BitVec.eq_of_toNat_eq
    rw [htv, htdef, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · -- The hasher: the copied bytes in the buffer, the rest as at the loop head.
    rw [hLdef, htdef]
    have hsrc : ((input m0).drop c).take t = bytesOf st4.data.dmem (dAt m0 + BitVec.ofNat 64 c) t := by
      rw [input, ← bytesOf_add _ _ (by omega)]
      refine (bytesOf_congr fun i hi => ?_).symm
      rw [add_ofNat_add, hmem4, input_same g hinv.frame h01 (by omega)]
    have hsl : (((input m0).drop c).take t).length = t := by
      rw [hsrc, length_bytesOf]
    refine ext_getD (by rw [hasher, length_bytesOf, length_writeAt (by rw [hsl, hlen]; omega), hlen])
      fun i hi => ?_
    rw [hasher, length_bytesOf] at hi
    rw [hasher, getD_bytesOf _ _ hi, getD_writeAt _ _ _ _ (by rw [hsl, hlen]; omega), hsl]
    by_cases hin : 200 + L ≤ i ∧ i < 200 + L + t
    · rw [ite_pos' hin, show hAt m0 + BitVec.ofNat 64 i =
          hAt m0 + BitVec.ofNat 64 (200 + L) + BitVec.ofNat 64 (i - (200 + L)) by
          rw [add_ofNat_add]; congr 2; omega,
        hbytes (i - (200 + L)) (by rw [length_bytesOf]; omega), hsrc]
      simp only [Option.getD_some, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by rw [length_bytesOf]; omega)]
      rfl
    · rw [ite_neg' hin, hsame _ fun hr => hin ?_, hmem4, ← getD_bytesOf _ _ hi]
      · rfl
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        exact absurd hr inRange_zero
      · rw [inRange_add_iff (by have := g.h; omega) (by have := g.h; omega) h0] at hr
        exact hr

end

end NativeRustcArm.Hasher.Update
