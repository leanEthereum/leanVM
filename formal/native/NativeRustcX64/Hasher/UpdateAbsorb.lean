module

public import NativeRustcX64.Code.Common.KeccakF.Names

public import NativeRustcX64.Hasher.UpdateCount

/-!
# `Hasher::update`'s loop: absorbing a full buffer (x86-64)

`b7` XORs the buffer's 17 lanes into the state's (`xorBlock`) and calls `keccak_f` on the state;
on its return the state is `absorb` of the state and the buffer (`Absorbed`, `absorb_spec`).
-/

namespace NativeRustcX64.Hasher.Update

open NativeRustc NativeRustc.Keccak LeanVM.Protocol.KeccakHash NativeRustcX64.Sym
open NativeRustcX64.Common.Update NativeRustcX64.KeccakF NativeRustcX64.Hasher

@[expose] public section

/-- After `keccak_f`: the state absorbed the full buffer. -/
structure Absorbed [Labels] (m0 : MachineData) (c : Nat) (Hc : List UInt8) (m : MachineData) : Prop where
  frame : Frame m0 m
  le : c ≤ nOf m0
  rbx : reg m .rbx = BitVec.ofNat 64 (nOf m0 - c)
  r15 : reg m .r15 = dAt m0 + BitVec.ofNat 64 c
  r12 : reg m .r12 = BitVec.ofNat 64 (takeN m0 c Hc)
  holds : Holds m0 Hc c
  lt : bufLen Hc < 136
  len : Hc.length = 344
  full : bufLen Hc + takeN m0 c Hc = 136
  bytes : hasher m0 m = writeAt (counted m0 c Hc) 0
    (absorb ((counted m0 c Hc).take 200) (((counted m0 c Hc).drop 200).take 136))

end

public section

theorem rcBytes_length : rcBytes.length = 192 := by
  rw [show rcBytes = Native.Keccak.wordsBytes LeanVM.Parameters.keccakRC from rfl,
    Native.Keccak.Proof.length_wordsBytes]
  rfl

/-- `keccak_f`'s stack below the frame is `update`'s. -/
theorem frm_sub {m0 : MachineData} (g : Geo m0) :
    frm m0 - BitVec.ofNat 64 288 = rspOf m0 - BitVec.ofNat 64 updateStack := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_sub_ofNat (by rw [frm_toNat g]; have := g.s; omega), frm_toNat g,
    toNat_sub_ofNat (by have := g.s; exact this)]
  have := g.s
  show (spAt m0).toNat - 112 - 288 = (spAt m0).toNat - 400
  omega

variable [ElfHost] {sec k : Nat}

set_option linter.unusedSimpArgs false in
/-- **Absorbing a full buffer.** -/
theorem absorb_spec (hp : PlacedIn code sec k)
    (hkf : ElfSpec (Labels.label NativeRustcX64.Common.KeccakF.entryLabel) KeccakFPre KeccakFPost)
    {m0 m : MachineData} (hpre : UpdatePre m0) {c : Nat} {Hc : List UInt8}
    (hfu : Full m0 c Hc m) :
    Eventually (elfStep1 ElfHost.exe)
      (fun st => st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b8Offset) ∧ Absorbed m0 c Hc st.data)
      ⟨m, ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b7Offset)⟩ := by
  have g := geo_of hpre
  have gr := geoRc_of hpre
  let env := Env.ofMachine m [(hAt m0, 344), (frm m0, 120), (gotAddr "memcpy", 8)] (fun _ => 0)
    (ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b8Offset)).toBitVec
  have hwf : env.WF := wf_head hpre hfu.frame
  have hm : Match env headS m := match_headS hpre hfu.frame
  have hb0 : env.base 0 = hAt m0 := rfl
  have hfrN := frm_toNat g
  have hH : hasher m0 m = counted m0 c Hc := hfu.bytes
  generalize hc2 : counted m0 c Hc = H2 at hH
  have hlen2 : H2.length = 344 := by rw [← hH]; exact length_bytesOf ..
  refine exec_then_elf (hb7 hp) run_b7 hwf (fun _ _ => rfl) hm fun st7 hm7 hpc7 => ?_
  have hfw := findWrite_b7
  rw [after_eq run_b7] at hfw
  have hl := b7_mem
  rw [after_eq run_b7] at hl
  have hmem7 : ∀ j < 344, (st7.data.dmem.get? (hAt m0 + BitVec.ofNat 64 j)).getD 0 =
      if j < 136 then H2.getD j 0 ^^^ H2.getD (200 + j) 0 else H2.getD j 0 := by
    intro j hj
    rw [hm7.mem 0 _ 344 rfl j hj]
    unfold memByte
    rw [hfw j hj]
    by_cases h : j < 136
    · rw [ite_pos' h, ite_pos' h]
      simp only [Option.getD_some, Sym.eval, BinOp.apply, low_W64, ext_W64]
      rw [byteOf_xor, byteOf_load (by omega) (by omega), byteOf_load (by omega) (by omega), hb0,
        show 8 * (j / 8) + j % 8 = j by omega, show 200 + 8 * (j / 8) + j % 8 = 200 + j by omega,
        ← hH, hasher, getD_bytesOf _ _ (by omega), getD_bytesOf _ _ (by omega)]
      rfl
    · rw [ite_neg' h, ite_neg' h, ← hH, hasher, getD_bytesOf _ _ hj]
      rfl
  have hxor : bytesOf st7.data.dmem (hAt m0) 200 =
      NativeRustc.Keccak.xorBlock (H2.take 200) ((H2.drop 200).take 136) := by
    refine ext_getD (by simp [length_bytesOf, NativeRustc.Keccak.xorBlock, length_stateBytes])
      fun j hj => ?_
    rw [length_bytesOf] at hj
    rw [getD_bytesOf _ _ hj, hmem7 j (by omega), getD_xorBlock _ _ hj,
      Native.Keccak.Proof.getD_take, ite_pos' hj]
    by_cases h : j < 136
    · rw [ite_pos' h, ite_pos' h, Native.Keccak.Proof.getD_take, ite_pos' h,
        Native.Keccak.Proof.getD_drop]
    · rw [ite_neg' h, ite_neg' h]
  have hrsp7 : rspOf st7.data = frm m0 := by
    show reg st7.data .rsp = _
    rw [show reg st7.data .rsp = _ from hm7.regs .rsp _ rfl]
    show frm m0 + BitVec.ofInt 64 0 = _
    exact BitVec.add_zero _
  have hs := g.s
  have hsb : stackBelow st7.data 288 = rspOf m0 - BitVec.ofNat 64 updateStack := by
    rw [stackBelow, hrsp7, frm_sub g]
  have hsbN : (rspOf m0 - BitVec.ofNat 64 updateStack).toNat = (spAt m0).toNat - 400 :=
    stackBelow_toNat hs
  have hX0 : reg st7.data .rdi = hAt m0 := by
    rw [show reg st7.data .rdi = _ from hm7.regs .rdi _ rfl]
    exact BitVec.add_zero _
  have hnw7 : ∀ p, ¬ChgL m0 p → st7.data.dmem.get? p = m.dmem.get? p := fun p hp =>
    hm7.get?_mem0 hwf fun ⟨w, hw, b, sz, hb, h1, h2⟩ => hp (by
      change ([(hAt m0, 344), (frm m0, 120), (gotAddr "memcpy", 8)] :
        List (BitVec 64 × Nat))[w.r]? = some (b, sz) at hb
      rw [chgL_iff g]
      rcases hl w hw with ⟨hr, hle⟩ | ⟨hr, hle⟩
      · rw [hr] at hb
        obtain ⟨rfl, rfl⟩ : hAt m0 = b ∧ 344 = sz := by simpa using hb
        omega
      · rw [hr] at hb
        obtain ⟨rfl, rfl⟩ : frm m0 = b ∧ 120 = sz := by simpa using hb
        rw [hfrN] at h1 h2
        omega)
  have hrc7 : BytesAt st7.data.dmem rcAddr rcBytes := fun i hi => by
    rw [rcBytes_length] at hi
    have hnot : ¬ChgL m0 (rcAddr + BitVec.ofNat 64 i) := by
      rw [chgL_iff g, toNat_add_ofNat' (by have := gr.nw; omega)]
      have := gr.hr
      have := gr.rs
      omega
    rw [hnw7 _ hnot, rc_same g gr hfu.frame hi]
    exact hpre.2.1.1 i (by rw [rcBytes_length]; exact hi)
  refine call_then_elf hpc7 hkf ?pre fun st' hpc' hrsp' hpost => ?_
  case pre =>
    refine ⟨⟨?_, ?_, fun i hi => ?_⟩, ⟨hrc7, gr.nw, ?_⟩, fun i hi => ?_, ?_, ?_, ?_⟩
    · show 288 ≤ (rspOf st7.data).toNat
      rw [hrsp7, hfrN]
      omega
    · rw [hrsp7, hfrN]
      have := g.s8
      omega
    · show (st7.data.dmem.get? (stackBelow st7.data 288 + _)).isSome
      rw [hsb]
      exact hm7.kept hwf _ (hfu.frame.kept _ (hpre.1.2.2 i (by
        have h' : keccakFStack = 288 := rfl
        rw [h'] at hi
        show i < 400 + 8
        omega)))
    · show _ + 192 ≤ (stackBelow st7.data 288).toNat ∨ (stackBelow st7.data 288).toNat + 296 ≤ _
      rw [hsb, hsbN]
      have := gr.rs
      omega
    · show (st7.data.dmem.get? (reg st7.data .rdi + _)).isSome
      rw [hX0]
      exact hm7.kept hwf _ (hfu.frame.kept _ (hpre.2.2.2.1 i (by omega)))
    · show (reg st7.data .rdi).toNat + 200 ≤ _
      rw [hX0]
      have := g.h
      omega
    · show (reg st7.data .rdi).toNat + 200 ≤ (stackBelow st7.data 288).toNat ∨
        (stackBelow st7.data 288).toNat + (288 + 8) ≤ (reg st7.data .rdi).toNat
      rw [hX0, hsb, hsbN]
      have := g.hs
      omega
    · show (reg st7.data .rdi).toNat + 200 ≤ rcAddr.toNat ∨
        rcAddr.toNat + 192 ≤ (reg st7.data .rdi).toNat
      rw [hX0]
      have := gr.hr
      omega
  obtain ⟨hbytesK, hsameK, hsavedK⟩ := hpost
  have hX0' : reg st7.data .rdi = _ := hX0
  simp only [reg] at hX0'
  simp only [hX0', hxor, show keccakFStack = 288 from rfl] at hbytesK hsameK
  rw [hsb] at hsameK
  have hreg : ∀ r, calleeSaved r = true → st'.data.regs.get64 r = st7.data.regs.get64 r :=
    hsavedK.1
  have hfr : Frame m0 st'.data := by
    refine hfu.frame.update g ((hreg .r13 rfl).trans (Match.reg_eq hm hm7 rfl rfl))
      ((hreg .r14 rfl).trans (Match.reg_eq hm hm7 rfl rfl))
      (hrsp'.trans (by rw [hrsp7, hfu.frame.rsp])) (fun p hp => ?_)
      (fun p hp => hsavedK.2 p (hm7.kept hwf p hp))
      ((hreg .rbp rfl).trans (hm7.regs .rbp (.label "memcpy") rfl))
    rw [hsameK p fun hr => hp ?_, hnw7 p hp]
    rw [chgL_iff g]
    rcases hr with hr | hr
    · rw [inRange_iff (by have := g.h; omega)] at hr
      omega
    · rw [inRange_iff (by rw [hsbN]; have := g.s8; omega), hsbN] at hr
      omega
  refine Eventually.done _ ⟨by rw [hpc']; rfl, hfr, hfu.le, ?_, ?_, ?_, hfu.holds, hfu.lt,
    hfu.len, hfu.full, ?_⟩
  · exact (hreg .rbx rfl).trans ((Match.reg_atom hm7 rfl).trans hfu.rbx)
  · exact (hreg .r15 rfl).trans ((Match.reg_atom hm7 rfl).trans hfu.r15)
  · exact (hreg .r12 rfl).trans ((Match.reg_atom hm7 rfl).trans hfu.r12)
  · rw [hc2]
    have hA : (absorb (H2.take 200) ((H2.drop 200).take 136)).length = 200 := by
      rw [absorb, keccakF, length_stateBytes]
    refine ext_getD (by rw [hasher, length_bytesOf, length_writeAt (by omega), hlen2])
      fun j hj => ?_
    rw [hasher, length_bytesOf] at hj
    rw [hasher, getD_bytesOf _ _ hj, getD_writeAt _ _ _ _ (by omega), hA]
    by_cases h : j < 200
    · rw [ite_pos' ⟨Nat.zero_le _, h⟩, hbytesK j (by rw [keccakF, length_stateBytes]; exact h),
        Nat.sub_zero, absorb]
      simp [List.getD_eq_getElem?_getD, show j < (keccakF (NativeRustc.Keccak.xorBlock
        (H2.take 200) ((H2.drop 200).take 136))).length by
          rw [keccakF, length_stateBytes]; exact h]
    · rw [ite_neg' (by omega), hsameK _ (fun hr => ?_)]
      · have := hmem7 j hj
        rw [ite_neg' (by omega)] at this
        exact this
      rcases hr with hr | hr
      · rw [inRange_self_iff (by have := g.h; omega) (by have := g.h; omega) (by omega)] at hr
        omega
      · rw [inRange_iff (by rw [hsbN]; have := g.s8; omega), hsbN,
          toNat_add_ofNat' (by have := g.h; omega)] at hr
        have := g.hs
        omega

end

end NativeRustcX64.Hasher.Update
