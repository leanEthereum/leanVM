module

public import NativeRustcArm.Code.Common.Finalize.Names
public import NativeRustcArm.Code.Common.Memcpy.Names
public import NativeRustcArm.Code.Common.Update.Names

public import NativeRustcArm.XmssVerify.Calls
meta import NativeRustcArm.Code.Xmss.XmssVerify
public meta import NativeRustcArm.XmssVerify.Parse

/-!
# `xmss_verify`: a Merkle node's hash

The calls of the inlined `node`/`th` of a path step, the same on both layers (blocks 9 to 13 on
the bottom layer, 19 to 23 on the top, `b20` to `b23` the same blocks as `b10` to `b13`): from a
new hasher at `5408` (the frame's offsets), `update` with the public parameter at `2464`,
`update` with the address at `5392`, `memcpy` of the hasher to `5048`, `update` of the copy with
the children at `5016`, `finalize` of the copy to `5408` (`hashNode`). Blocks 9 and 19 set up the
first `update` from different registers; `hashNode` takes such a block as an argument.
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym NativeRustcArm LeanVM.Protocol.KeccakHash NativeRustc

set_option Elab.async false

@[expose] public section

sym_block b9_exec := exec b9 (stF0 [])

/-- The symbolic state after block 9. -/
def st9 : SState := ((exec b9 (stF0 [])).getD (stF0 [], .fall)).1

theorem b9_exec' : exec b9 (stF0 []) = some (st9, .call NativeRustcArm.Common.Update.entryLabel) := by
  rw [b9_exec]
  rfl

theorem st9_facts : st9.mem = [] ∧ keeps (stF0 []) st9 = true ∧ st9.reg .X0 = some (.ptr 0 5408) ∧
    st9.reg .X1 = some (.ptr 0 2464) ∧ st9.reg .X2 = some (.lit 16) := by decide +kernel

sym_block b19_exec := exec b19 (stF0 [(.X27, .ptr 0 2448)])

/-- The symbolic state after block 19. -/
def st19 : SState := ((exec b19 (stF0 [(.X27, .ptr 0 2448)])).getD (stF0 [], .fall)).1

theorem b19_exec' : exec b19 (stF0 [(.X27, .ptr 0 2448)]) = some (st19, .call NativeRustcArm.Common.Update.entryLabel) := by
  rw [b19_exec]
  rfl

theorem st19_facts : st19.mem = [] ∧ keeps (stF0 [(.X27, .ptr 0 2448)]) st19 = true ∧
    st19.reg .X0 = some (.ptr 0 5408) ∧ st19.reg .X1 = some (.ptr 0 2464) ∧
    st19.reg .X2 = some (.lit 16) := by decide +kernel

sym_block b10_exec := exec b10 (stF0 [])

/-- The symbolic state after block 10. -/
def st10 : SState := ((exec b10 (stF0 [])).getD (stF0 [], .fall)).1

theorem b10_exec' : exec b10 (stF0 []) = some (st10, .call NativeRustcArm.Common.Update.entryLabel) := by
  rw [b10_exec]
  rfl

theorem st10_facts : st10.mem = [] ∧ keeps (stF0 []) st10 = true ∧
    st10.reg .X0 = some (.ptr 0 5408) ∧ st10.reg .X1 = some (.ptr 0 5392) ∧
    st10.reg .X2 = some (.lit 16) := by decide +kernel

sym_block b11_exec := exec b11 (stF0 [])

/-- The symbolic state after block 11. -/
def st11 : SState := ((exec b11 (stF0 [])).getD (stF0 [], .fall)).1

theorem b11_exec' : exec b11 (stF0 []) = some (st11, .call NativeRustcArm.Common.Memcpy.entryLabel) := by
  rw [b11_exec]
  rfl

theorem st11_facts : st11.mem = [] ∧ keeps (stF0 []) st11 = true ∧
    st11.reg .X0 = some (.ptr 0 5048) ∧ st11.reg .X1 = some (.ptr 0 5408) ∧
    st11.reg .X2 = some (.lit 344) := by decide +kernel

sym_block b12_exec := exec b12 (stF0 [])

/-- The symbolic state after block 12. -/
def st12 : SState := ((exec b12 (stF0 [])).getD (stF0 [], .fall)).1

theorem b12_exec' : exec b12 (stF0 []) = some (st12, .call NativeRustcArm.Common.Update.entryLabel) := by
  rw [b12_exec]
  rfl

theorem st12_facts : st12.mem = [] ∧ keeps (stF0 []) st12 = true ∧
    st12.reg .X0 = some (.ptr 0 5048) ∧ st12.reg .X1 = some (.ptr 0 5016) ∧
    st12.reg .X2 = some (.lit 32) := by decide +kernel

sym_block b13_exec := exec b13 (stF0 [])

/-- The symbolic state after block 13. -/
def st13 : SState := ((exec b13 (stF0 [])).getD (stF0 [], .fall)).1

theorem b13_exec' : exec b13 (stF0 []) = some (st13, .call NativeRustcArm.Common.Finalize.entryLabel) := by
  rw [b13_exec]
  rfl

theorem st13_facts : st13.mem = [] ∧ keeps (stF0 []) st13 = true ∧
    st13.reg .X0 = some (.ptr 0 5408) ∧ st13.reg .X1 = some (.ptr 0 5048) := by decide +kernel

/-- Blocks 20 to 23 are blocks 10 to 13. -/
theorem b20_23 : b20 = b10 ∧ b21 = b11 ∧ b22 = b12 ∧ b23 = b13 := by decide +kernel

/-- Blocks 10 to 13 at `j` and after. -/
def HashPos [Host] (j : Nat) : Prop :=
  b10.IsInfixAt Host.prog j ∧ b11.IsInfixAt Host.prog (j + (NativeRustcArm.Xmss.XmssVerify.b11Offset - NativeRustcArm.Xmss.XmssVerify.b10Offset)) ∧
    b12.IsInfixAt Host.prog (j + (NativeRustcArm.Xmss.XmssVerify.b12Offset - NativeRustcArm.Xmss.XmssVerify.b10Offset)) ∧ b13.IsInfixAt Host.prog (j + (NativeRustcArm.Xmss.XmssVerify.b13Offset - NativeRustcArm.Xmss.XmssVerify.b10Offset))

end

public section

variable [Host] {w : Nat → UInt64} {m₀ : MachineData}

theorem hashPos_bottom {k : Nat} (hp : Placed code k) : HashPos (k + NativeRustcArm.Xmss.XmssVerify.b10Offset) :=
  ⟨b10_in_code.trans hp.1 (List.cons_ne_nil _ _), b11_in_code.trans hp.1 (List.cons_ne_nil _ _),
    b12_in_code.trans hp.1 (List.cons_ne_nil _ _), b13_in_code.trans hp.1 (List.cons_ne_nil _ _)⟩

theorem hashPos_top {k : Nat} (hp : Placed code k) : HashPos (k + NativeRustcArm.Xmss.XmssVerify.b20Offset) := by
  obtain ⟨h20, h21, h22, h23⟩ := b20_23
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← h20]; exact b20_in_code.trans hp.1 (List.cons_ne_nil _ _)
  · rw [← h21]; exact b21_in_code.trans hp.1 (List.cons_ne_nil _ _)
  · rw [← h22]; exact b22_in_code.trans hp.1 (List.cons_ne_nil _ _)
  · rw [← h23]; exact b23_in_code.trans hp.1 (List.cons_ne_nil _ _)

/-- A register a call block set to a frame pointer. -/
theorem regPtr {m m' : MachineData} {S : SState} {r : XReg} {o : Nat}
    (hr : ∀ r v, S.reg r = some v →
      (m'.regs.getXReg r).toBitVec = v.eval (Env.ofMachine m [(ad m₀ fb, 5872)]))
    (h : S.reg r = some (.ptr 0 o)) : (m'.regs.getXReg r).toBitVec = ad m₀ (fb + o) :=
  (hr _ _ h).trans (eval_ptr0 _)

/-- A register a call block set to a literal. -/
theorem regLit {m m' : MachineData} {S : SState} {r : XReg} {n : Nat}
    (hr : ∀ r v, S.reg r = some v →
      (m'.regs.getXReg r).toBitVec = v.eval (Env.ofMachine m [(ad m₀ fb, 5872)]))
    (h : S.reg r = some (.lit n)) (hn : n < 2 ^ 64) : (m'.regs.getXReg r).toNat = n := by
  have : (m'.regs.getXReg r).toBitVec = BitVec.ofNat 64 n := hr _ _ h
  rw [toNat_X, this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

omit [Host] in
theorem length_new : Keccak.new.length = 344 := by
  unfold Keccak.new
  exact List.length_replicate

/-- **A Merkle node's hash**: from a block like block 9 at `j9` (`update` of the new hasher
at `5408` with the public parameter at `2464`) and blocks 10 to 13 at `j`, the hash of the
public parameter `pp`, the address `A` at `5392` and the children `Ch` at `5016` at `5408`, the
frame's bytes below `5016` kept. -/
theorem hashNode (Cs : Callees) (P : Pre w m₀) {j9 j : Nat} {ds9 : List Directive}
    {known9 : List (XReg × Sym)} {S9 : SState} (hk9 : ds9.IsInfixAt Host.prog j9)
    (hj : j9 + ds9.length = j) (hx9 : exec ds9 (stF0 known9) = some (S9, .call NativeRustcArm.Common.Update.entryLabel))
    (hf9 : S9.mem = [] ∧ keeps (stF0 known9) S9 = true ∧ S9.reg .X0 = some (.ptr 0 5408) ∧
      S9.reg .X1 = some (.ptr 0 2464) ∧ S9.reg .X2 = some (.lit 16))
    (hpos : HashPos j) {st : MachineState} (hpc : st.pc = Host.addrOf j9)
    (C : Common m₀ st.data)
    (hknown : AllOf (fun p => (st.data.regs.getXReg p.1).toBitVec =
      p.2.eval (Env.ofMachine st.data [(ad m₀ fb, 5872)])) known9)
    {pp A Ch : List UInt8} (hlp : pp.length = 16) (hlA : A.length = 16) (hlC : Ch.length = 32)
    (hh : BytesAt st.data.dmem (ad m₀ (fb + 5408)) Keccak.new)
    (hpp : BytesAt st.data.dmem (ad m₀ (fb + 2464)) pp)
    (hA : BytesAt st.data.dmem (ad m₀ (fb + 5392)) A)
    (hC : BytesAt st.data.dmem (ad m₀ (fb + 5016)) Ch) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (j + (NativeRustcArm.Xmss.XmssVerify.b13End - NativeRustcArm.Xmss.XmssVerify.b10Offset)) → Common m₀ st'.data →
      Saved st.data st'.data →
      BytesAt st'.data.dmem (ad m₀ (fb + 5408)) (Keccak.hashBytes (pp ++ A ++ Ch)) →
      (∀ (o : Nat) (bs : List UInt8), o + bs.length ≤ 5016 →
        BytesAt st.data.dmem (ad m₀ (fb + o)) bs → BytesAt st'.data.dmem (ad m₀ (fb + o)) bs) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  obtain ⟨p10, p11, p12, p13⟩ := hpos
  obtain ⟨m9, k9, x0, x1, x2⟩ := hf9
  -- Block 9 and `update` with the public parameter.
  refine callBlock P hk9 hx9 m9 k9 hpc C hknown fun s1 hpc1 hret1 C1 hs1 hd1 hr1 => ?_
  have hh1 : Keccak.HasherHolds (bytesOf s1.data.dmem (ad m₀ (fb + 5408)) 344) [] := by
    rw [hd1, bytesOf_of hh length_new]
    exact Keccak.holds_new
  refine updateCall Cs.update P hpc1 hret1 C1 (h := 5408) (d := 2464) (regPtr hr1 x0)
    (regPtr hr1 x1)
    (by rw [hlp]; exact regLit hr1 x2 (by decide)) hh1 (hd1 ▸ hpp) (by decide) (by omega)
    (by omega) (by omega) fun s2 hpc2 C2 hs2 hh2 hsm2 => ?_
  -- Block 10 and `update` with the address.
  obtain ⟨m10, k10, y0, y1, y2⟩ := st10_facts
  refine callBlock P p10 b10_exec' m10 k10 (hpc2.trans (by rw [hj])) C2 trivial
    fun s3 hpc3 hret3 C3 hs3 hd3 hr3 => ?_
  have hA3 : BytesAt s3.data.dmem (ad m₀ (fb + 5392)) A := by
    rw [hd3]
    exact keep_callR P C1 (by decide) (by decide) hsm2 (hd1 ▸ hA) (by omega) (by omega)
  refine updateCall Cs.update P hpc3 hret3 C3 (h := 5408) (d := 5392) (regPtr hr3 y0)
    (regPtr hr3 y1)
    (by rw [hlA]; exact regLit hr3 y2 (by decide)) (hd3 ▸ hh2) hA3 (by decide) (by omega)
    (by omega) (by omega) fun s4 hpc4 C4 hs4 hh4 hsm4 => ?_
  -- Block 11 and `memcpy` of the hasher.
  obtain ⟨m11, k11, z0, z1, z2⟩ := st11_facts
  refine callBlock P p11 b11_exec' m11 k11 hpc4 C4 trivial fun s5 hpc5 hret5 C5 hs5 hd5 hr5 => ?_
  refine memcpyCall Cs.memcpy P hpc5 hret5 C5 (dst := 5048) (src := 5408) (regPtr hr5 z0)
    (regPtr hr5 z1) (regLit hr5 z2 (by decide)) (by omega) (by omega) (by omega) (by omega)
    fun s6 hpc6 C6 hs6 hb6 hsm6 => ?_
  have hh6 : Keccak.HasherHolds (bytesOf s6.data.dmem (ad m₀ (fb + 5048)) 344) (pp ++ A) := by
    rw [bytesOf_of hb6 (length_bytesOf _ _ _), hd5]
    exact hh4
  -- Block 12 and `update` of the copy with the children.
  have hC6 : BytesAt s6.data.dmem (ad m₀ (fb + 5016)) Ch := by
    have h1 := keep_callR P C1 (by decide) (by decide) hsm2 (hd1 ▸ hC) (by omega) (by omega)
    have h3 := keep_callR P C3 (by decide) (by decide) hsm4 (hd3 ▸ h1) (by omega) (by omega)
    exact keep_callR P C5 (Nat.zero_le _) (by decide) hsm6 (hd5 ▸ h3) (by omega) (by omega)
  obtain ⟨m12, k12, u0, u1, u2⟩ := st12_facts
  refine callBlock P p12 b12_exec' m12 k12 hpc6 C6 trivial fun s7 hpc7 hret7 C7 hs7 hd7 hr7 => ?_
  refine updateCall Cs.update P hpc7 hret7 C7 (h := 5048) (d := 5016) (regPtr hr7 u0)
    (regPtr hr7 u1)
    (by rw [hlC]; exact regLit hr7 u2 (by decide)) (hd7 ▸ hh6) (hd7 ▸ hC6) (by decide)
    (by omega) (by omega) (by omega) fun s8 hpc8 C8 hs8 hh8 hsm8 => ?_
  -- Block 13 and `finalize` of the copy.
  obtain ⟨m13, k13, v0, v1⟩ := st13_facts
  refine callBlock P p13 b13_exec' m13 k13 hpc8 C8 trivial fun s9 hpc9 hret9 C9 hs9 hd9 hr9 => ?_
  refine finalizeCall Cs.finalize P hpc9 hret9 C9 (o := 5408) (h := 5048) (regPtr hr9 v0)
    (regPtr hr9 v1) (hd9 ▸ hh8)
    (by omega) (by omega) (by omega) fun s10 hpc10 C10 hs10 hb10 hsm10 => ?_
  refine cont s10 hpc10 C10 ?_ ?_ fun o bs ho hb => ?_
  · exact hs1.trans (hs2.trans (hs3.trans (hs4.trans (hs5.trans (hs6.trans (hs7.trans
      (hs8.trans (hs9.trans hs10))))))))
  · simpa only [List.append_assoc] using hb10
  · have h1 := keep_callR P C1 (by decide) (by decide) hsm2 (hd1 ▸ hb) (by omega) (by omega)
    have h3 := keep_callR P C3 (by decide) (by decide) hsm4 (hd3 ▸ h1) (by omega) (by omega)
    have h5 := keep_callR P C5 (Nat.zero_le _) (by decide) hsm6 (hd5 ▸ h3) (by omega) (by omega)
    have h7 := keep_callR P C7 (by decide) (by decide) hsm8 (hd7 ▸ h5) (by omega) (by omega)
    exact keep_callR P C9 (by decide) (by decide) hsm10 (hd9 ▸ h7) (by omega) (by omega)

end

end NativeRustcArm.Xmss.XmssVerify
