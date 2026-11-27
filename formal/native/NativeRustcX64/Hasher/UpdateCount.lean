module

public import NativeRustcX64.Hasher.UpdateCopy

/-!
# `Hasher::update`'s loop: counting the copied bytes (x86-64)

After `memcpy`, `b6` stores `buf_len + t` into `buf_len` and goes to `.LUpdate_5` unless the
buffer is full (`count_spec`): then the hasher is the turn's (`updateStep`, `Mid`); else it falls
through to the absorption (`Full`). The turn's bytes in the model: `takeN`, `copied`, `counted`,
`updateStep_eq`.
-/

namespace NativeRustcX64.Hasher.Update

open NativeRustc NativeRustc.Keccak LeanVM.Protocol.KeccakHash NativeRustcX64.Sym
open NativeRustcX64.Common.Update NativeRustcX64.KeccakF NativeRustcX64.Hasher

@[expose] public section

/-- The bytes a turn from the hasher `Hc`, `c` input bytes absorbed, takes. -/
def takeN (m0 : MachineData) (c : Nat) (Hc : List UInt8) : Nat :=
  min (136 - bufLen Hc) (nOf m0 - c)

/-- The hasher with them copied into its buffer. -/
def copied (m0 : MachineData) (c : Nat) (Hc : List UInt8) : List UInt8 :=
  writeAt Hc (200 + bufLen Hc) (((input m0).drop c).take (takeN m0 c Hc))

/-- And `buf_len` advanced. -/
def counted (m0 : MachineData) (c : Nat) (Hc : List UInt8) : List UInt8 :=
  writeAt (copied m0 c Hc) 336 (wordBytes (bufLen Hc + takeN m0 c Hc).toUInt64)

/-- At the absorption (`b7`): the buffer is full. -/
structure Full [Labels] (m0 : MachineData) (c : Nat) (Hc : List UInt8) (m : MachineData) : Prop where
  frame : Frame m0 m
  le : c ≤ nOf m0
  rbx : reg m .rbx = BitVec.ofNat 64 (nOf m0 - c)
  r15 : reg m .r15 = dAt m0 + BitVec.ofNat 64 c
  r12 : reg m .r12 = BitVec.ofNat 64 (takeN m0 c Hc)
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
/-- **Counting the copied bytes**: to `.LUpdate_5` after the turn, or to the absorption. -/
theorem count_spec (hp : PlacedIn code sec k) {m0 m : MachineData} (hpre : UpdatePre m0) {c : Nat}
    {Hc : List UInt8} (hcp : Copied m0 c Hc m) :
    Eventually (elfStep1 ElfHost.exe)
      (fun st => (st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b2Offset) ∧ Mid m0 c (takeN m0 c Hc) st.data) ∨
        (st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b7Offset) ∧ Full m0 c Hc st.data))
      ⟨m, ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b6Offset)⟩ := by
  have g := geo_of hpre
  let env := Env.ofMachine m [(hAt m0, 344), (frm m0, 120), (gotAddr "memcpy", 8)]
  have hwf : env.WF := wf_head hpre hcp.frame
  have hm : Match env headS m := match_headS hpre hcp.frame
  have henv : ∀ r, env.regs r = reg m r := fun _ => rfl
  have hb0 : env.base 0 = hAt m0 := rfl
  have hn : nOf m0 < 2 ^ 64 := BitVec.isLt _
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
    rw [Native.Keccak.Proof.getD_drop, Native.Keccak.Proof.getD_drop, copied,
      getD_writeAt _ _ _ _ (by rw [hs, hcp.len]; omega), hs, hLdef, ite_neg' (by omega)]
  have hload : env.load 0 336 8 = BitVec.ofInt 64 (Int.ofBytes (Hc.drop 336)) := by
    refine Env.load_of_bytesAt (by simp [hcp.len]) ?_
    rw [hb0, ← h336]
    have := bytesAt_bytesOf (d := m.dmem) (a := hAt m0 + BitVec.ofNat 64 336) (n := 8)
      fun i hi => by rw [add_ofNat_add]; exact hcp.frame.kept _ (hpre.2.2.2.1 _ (by omega))
    rwa [bytesOf_add _ _ (n := 344) (by omega), List.take_of_length_le
      (by simp [length_bytesOf])] at this
  have hV0 : (BitVec.ofInt 64 (Int.ofBytes (Hc.drop 336))).toNat = L := by
    rw [← hLdef, bufLen, lane_ofBytes (by simp [hcp.len])]
    rfl
  have hr12 : reg m .r12 = BitVec.ofNat 64 t := by
    rw [hcp.r12, ← htdef]
    rfl
  have hV : BitVec.ofNat 64 t + BitVec.ofInt 64 (Int.ofBytes (Hc.drop 336)) =
      BitVec.ofNat 64 (L + t) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hV0, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  refine exec_then_elf (hb6 hp) run_b6 hwf nofun hm fun st6 hm6 hpc6 => ?_
  simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
    henv, hload, hr12, hV, Nat.add_assoc, NativeRustcX64.Common.Update.b6_next] at hpc6
  -- Memory: the new `buf_len`.
  have hmem6 : ∀ j < 344, st6.data.dmem.get? (hAt m0 + BitVec.ofNat 64 j) =
      if 336 ≤ j then some (byteOf (BitVec.ofNat 64 (L + t)) (j - 336))
      else m.dmem.get? (hAt m0 + BitVec.ofNat 64 j) := by
    intro j hj
    rw [hm6.mem 0 (hAt m0) 344 rfl j hj]
    by_cases h : 336 ≤ j
    · simp only [memByte, findWrite, h, show j < 336 + 8 by omega, and_self, ↓reduceIte, Sym.eval,
        BinOp.apply, low_W64, ext_W64, henv, hload, hr12, hV]
    · simp only [memByte, findWrite, h, false_and, and_false, ↓reduceIte]
      rfl
  have hcnt : counted m0 c Hc = writeAt (copied m0 c Hc) 336 (wordBytes (L + t).toUInt64) := by
    rw [counted, hLdef, htdef]
  have hbytes : hasher m0 st6.data = counted m0 c Hc := by
    rw [hcnt]
    refine ext_getD (by rw [hasher, length_bytesOf, length_writeAt (by
      simp [length_wordBytes, hclen]), hclen]) fun j hj => ?_
    rw [hasher, length_bytesOf] at hj
    rw [hasher, getD_bytesOf _ _ hj, hmem6 j hj, getD_writeAt _ _ _ _ (by
      simp [length_wordBytes, hclen]), length_wordBytes]
    by_cases h : 336 ≤ j
    · rw [ite_pos' h, ite_pos' ⟨h, by omega⟩,
        show (L + t).toUInt64 = UInt64.ofBitVec (BitVec.ofNat 64 (L + t)) from rfl,
        wordBytes_ofBitVec]
      simp [List.getD_eq_getElem?_getD, show j - 336 < 8 by omega]
    · rw [ite_neg' h, ite_neg' (by omega), ← hcop, hasher, getD_bytesOf _ _ hj]
  have hfr : Frame m0 st6.data := by
    refine hcp.frame.update g (Match.reg_eq hm hm6 rfl rfl) (Match.reg_eq hm hm6 rfl rfl)
      (Match.reg_eq hm hm6 rfl rfl) (fun p hp => hm6.get?_mem0 hwf ?_) (hm6.kept hwf)
      (hm6.regs .rbp (.label "memcpy") rfl)
    rintro ⟨w, hw, b, sz, hb, h1, h2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    subst hw
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    rw [chgL_iff g] at hp
    exact hp (Or.inl ⟨by simp at h1; omega, by simp at h2; omega⟩)
  have hrbx : reg st6.data .rbx = BitVec.ofNat 64 (nOf m0 - c) :=
    (Match.reg_atom hm6 rfl).trans hcp.rbx
  have hr15 : reg st6.data .r15 = dAt m0 + BitVec.ofNat 64 c :=
    (Match.reg_atom hm6 rfl).trans hcp.r15
  have hr12' : reg st6.data .r12 = BitVec.ofNat 64 t := (Match.reg_atom hm6 rfl).trans hr12
  refine Eventually.done _ ?_
  by_cases hfull : L + t = 136
  · right
    rw [ite_neg' (by simp [hfull])] at hpc6
    exact ⟨hpc6, hfr, hle, hrbx, hr15, htdef ▸ hr12', hcp.holds, hcp.lt, hcp.len,
      by rw [hLdef, htdef]; exact hfull, hbytes⟩
  · left
    rw [ite_pos' (by
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      omega), lbl_5 hp] at hpc6
    have hstep : hasher m0 st6.data = (updateStep Hc ((input m0).drop c)).1 := by
      rw [hbytes, updateStep_eq, hLdef, htdef, ite_neg' hfull]
    refine ⟨hpc6, ⟨hfr, by omega, by rw [← htdef]; omega, hrbx, hr15, htdef ▸ hr12', ?_, ?_⟩⟩
    · rw [show reg st6.data .rdi = _ from hm6.regs .rdi _ rfl]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, henv, hload, hr12, hV]
      rw [hbytes, hcnt, bufLen_writeAt hclen, BitVec.toNat_ofNat]
      rfl
    · rw [hstep, ← htdef]
      exact holds_turn hle hcp.holds

end

end NativeRustcX64.Hasher.Update
