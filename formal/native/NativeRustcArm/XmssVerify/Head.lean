module

public import NativeRustcArm.XmssVerify.Callee
meta import NativeRustcArm.Code.Xmss.XmssVerify

/-!
# `xmss_verify`: the prologue

Block 0 from the entry: the callee-saved registers to the save area, the frame allocated,
`memset(frame + 48, 0, 2400)`; block 1: the input's words 0 to 8 into registers, the message's
words 4 to 7 to the frame at `8`, the leaf index's `u32` at `44`; to the head of the loop copying
the signature's words (`LoopAt` before its first turn). One environment per block: region 0 the
frame, 1 the input words.
-/

namespace NativeRustcArm.Xmss.XmssVerify

open NativeRustcArm.Sym NativeRustcArm LeanVM.Protocol.KeccakHash

set_option Elab.async false

@[expose] public section

/-- The message's bytes from the input words. -/
def msgBytes (w : Nat → UInt64) : List UInt8 := NativeRustc.Xmss.messageBytes w

/-- At the head of the loop copying the signature's words, before turn `i`. -/
structure LoopAt (w : Nat → UInt64) (m₀ m : MachineData) (i : Nat) : Prop where
  common : Common m₀ m
  x19 : (m.regs.getXReg .X19).toBitVec = ad m₀ (fb + 48)
  x20 : (m.regs.getXReg .X20).toBitVec = m₀.regs.X0.toBitVec
  x12 : (m.regs.getXReg .X12).toBitVec = ad m₀ (fb + 64 + 32 * i)
  x8 : (m.regs.getXReg .X8) = w 0
  x9 : (m.regs.getXReg .X9) = w 1
  x10 : (m.regs.getXReg .X10) = w 2
  x11 : (m.regs.getXReg .X11) = w 3
  x24 : (m.regs.getXReg .X24) = w 8
  x23 : (m.regs.getXReg .X23).toNat = (w 8).toNat % 2 ^ 32
  msg : ∀ k < 4, BytesAt m.dmem (ad m₀ (fb + 8 + 8 * k)) (wordBytes (w (4 + k)))
  li : BytesAt m.dmem (ad m₀ (fb + 44)) ((wordBytes (w 8)).take 4)
  sig : ∀ k < 4 * i, BytesAt m.dmem (ad m₀ (fb + 48 + 8 * k)) (wordBytes (w (9 + k)))
  x21 : (m.regs.getXReg .X21).toBitVec = ad m₀ (fb + 5392)
  x13 : (m.regs.getXReg .X13).toBitVec = inp m₀ + BitVec.ofNat 64 (96 + 32 * i)
  x14 : (m.regs.getXReg .X14).toBitVec = BitVec.ofNat 64 (300 - 4 * i)

/-- The symbolic state at the entry: region 0 the frame (SP its top), 1 the input words. -/
def st0 : SState := init [(5872, true), (2472, false)] (.ptr 0 5872) [(.X0, .ptr 1 (-1024))]

sym_block b0_exec := exec b0 st0

/-- The symbolic state after block 0. -/
def st0' : SState := ((exec b0 st0).getD (st0, .fall)).1

theorem st0'_facts : st0'.reg .X0 = some (.ptr 0 48) ∧ st0'.reg .X1 = some (.lit 0) ∧
    st0'.reg .X2 = some (.lit 2400) ∧ st0'.reg .X19 = some (.ptr 0 48) ∧
    st0'.reg .X20 = some (.ptr 1 (-1024)) ∧ st0'.reg .X29 = some (.ptr 0 5776) ∧
    st0'.sp = .ptr 0 0 ∧ writesIn st0' [0] = true := by decide +kernel

theorem st0'_x21 : st0'.reg .X21 = some (.ptr 0 5392) := by decide +kernel

theorem st0'_x22 : st0'.reg .X22 = some (.ptr 0 44) := by decide +kernel

theorem st0'_save : ∀ j < 12, ∀ t < 8,
    findWrite 0 (5776 + 8 * j + t) st0'.mem = some (.reg (saveRegs.getD j .X0), t) := by
  decide +kernel

/-- The symbolic state at block 1: region 0 the frame (SP its base), 1 the input words. -/
def st1 : SState := init [(5872, true), (2472, false)] (.ptr 0 0)
  [(.X20, .ptr 1 (-1024)), (.X19, .ptr 0 48), (.X21, .ptr 0 5392), (.X22, .ptr 0 44)]

sym_block b1_exec := exec b1 st1

/-- The symbolic state after block 1. -/
def st1' : SState := ((exec b1 st1).getD (st1, .fall)).1

theorem st1'_facts : st1'.reg .X8 = some (.load 1 0 8) ∧ st1'.reg .X9 = some (.load 1 8 8) ∧
    st1'.reg .X10 = some (.load 1 16 8) ∧ st1'.reg .X11 = some (.load 1 24 8) ∧
    st1'.reg .X12 = some (.ptr 0 64) ∧ st1'.reg .X24 = some (.load 1 64 8) ∧
    st1'.reg .X23 = some (.un .trunc .W32 (.load 1 64 8)) ∧ st1'.reg .X19 = some (.ptr 0 48) ∧
    st1'.reg .X20 = some (.ptr 1 (-1024)) ∧ st1'.reg .X29 = some (.reg .X29) ∧
    st1'.sp = .ptr 0 0 ∧ writesIn st1' [0] = true ∧
    (∀ x, 5776 ≤ x → x < 5872 → findWrite 0 x st1'.mem = none) := by decide +kernel

theorem st1'_x21 : st1'.reg .X21 = some (.ptr 0 5392) := by decide +kernel

theorem st1'_x13 : st1'.reg .X13 = some (.ptr 1 96) := by decide +kernel

theorem st1'_x14 : st1'.reg .X14 = some (.lit 300) := by decide +kernel

theorem st1'_msg : ∀ k < 4, ∀ t < 8,
    findWrite 0 (8 + 8 * k + t) st1'.mem = some (.load 1 (8 * (4 + k)) 8, t) := by decide +kernel

theorem st1'_li : ∀ t < 4, findWrite 0 (44 + t) st1'.mem = some (.load 1 (8 * 8) 8, t) := by
  decide +kernel

section
variable [Labels] {w : Nat → UInt64} {m₀ : MachineData}

/-- The frame and the input words as an environment's regions. -/
def regs0 (m₀ : MachineData) : List (BitVec 64 × Nat) := [(ad m₀ fb, 5872), (inp m₀, 2472)]

theorem frame16 (P : Pre w m₀) : (ad m₀ fb).toNat % 16 = 0 := by
  rw [P.ad_toNat (by rw [fb_eq]; omega), P.loNat, fb_eq]
  have := P.sp16
  have := P.spLe
  have : m₀.regs.SP.toBitVec.toNat = m₀.regs.SP.toNat := rfl
  omega

theorem regs0_wf (P : Pre w m₀) {m : MachineData} (hk : Kept m₀.dmem m.dmem) :
    (Env.ofMachine m (regs0 m₀)).WF :=
  Env.wf_of ⟨⟨(P.mapped.sub (i := fb) (k := 5872) (by rw [fb_eq])).kept hk,
      P.ad_nw (o := fb) (s := 5872) (by rw [fb_eq])⟩,
    ⟨P.inpMapped.kept hk, P.inpNW⟩, trivial⟩
    (List.pairwise_pair.mpr (by
      have := P.inp_apart (i := 0) (n := 2472) (o := fb) (s := 5872) (by omega) (by rw [fb_eq])
        (by omega) (by omega)
      simpa using this.symm))

omit [Labels] in
theorem inp_eq (m₀ : MachineData) :
    inp m₀ + BitVec.ofInt 64 (-1024) = m₀.regs.X0.toBitVec := by
  unfold inp xmssInput
  rw [BitVec.add_assoc, show BitVec.ofNat 64 1024 + BitVec.ofInt 64 (-1024) = 0 by decide]
  exact BitVec.add_zero _

omit [Labels] in
theorem sp_eq (m₀ : MachineData) : ad m₀ fb + BitVec.ofInt 64 5872 = m₀.regs.SP.toBitVec := by
  unfold ad lo stackBelow
  rw [BitVec.add_assoc, show BitVec.ofNat 64 fb + BitVec.ofInt 64 5872 =
    BitVec.ofNat 64 xmssVerifyStack by decide, BitVec.sub_add_cancel]

/-- A word of the input copied by a block: the input word's bytes. -/
theorem copy_word (P : Pre w m₀) {env : Env} {S : SState} {m : MachineData}
    (hm : Match env S m) {rd od rs os : Nat} {bd : BitVec 64} {szd : Nat}
    (hbd : env.regions[rd]? = some (bd, szd)) (hle : od + 8 ≤ szd) {i : Nat} (hi : i < 309)
    (hbs : ∀ t < 8, env.base rs + BitVec.ofNat 64 (os + t) = inp m₀ + BitVec.ofNat 64 (8 * i + t))
    (hmem : SameOutside m₀.dmem env.mem0 (InRange (lo m₀) 9200))
    (hf : ∀ t < 8, findWrite rd (od + t) S.mem = some (.load rs os 8, t)) :
    BytesAt m.dmem (bd + BitVec.ofNat 64 od) (wordBytes (w i)) := by
  intro t ht
  rw [NativeRustc.length_wordBytes] at ht
  rw [addr_add_addr, hm.get?_load hbd (by omega) (hf t ht) ht (le_refl 8), hbs t ht,
    ← addr_add_addr, P.words_at hmem hi t (by rw [NativeRustc.length_wordBytes]; exact ht)]
  rfl

/-- A register a block loaded from an input word is the word. -/
theorem load_word (P : Pre w m₀) {env : Env} (hmem : SameOutside m₀.dmem env.mem0 (InRange (lo m₀) 9200))
    {rs os i : Nat} (hi : i < 309)
    (hbs : env.base rs + BitVec.ofNat 64 os = inp m₀ + BitVec.ofNat 64 (8 * i)) :
    env.load rs os 8 = (w i).toBitVec := by
  rw [Env.load_of_bytesAt (bs := wordBytes (w i)) (NativeRustc.length_wordBytes _)
    (by rw [hbs]; exact P.words_at hmem hi), ← UInt64.toBitVec_ofBitVec (w i).toBitVec,
    show UInt64.ofBitVec (w i).toBitVec = w i from rfl, ← regBytes_eq_wordBytes, ofBytes_regBytes]

/-- **A block keeps `Common`** when it keeps SP and X29 and writes only the frame (region 0)
outside the save area. -/
theorem Common.block (P : Pre w m₀) {m m' : MachineData} (C : Common m₀ m)
    {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {S S' : SState}
    (hwf : (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars).WF)
    (hm₀ : Match (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars) S m)
    (hm : Match (Env.ofMachine m ((ad m₀ fb, 5872) :: rest) vars) S' m') (hsp : S'.sp = S.sp)
    {v : Sym} (h29 : S.reg .X29 = some v) (h29' : S'.reg .X29 = some v)
    (hw : writesIn S' [0] = true) (hsave : ∀ x, 5776 ≤ x → x < 5872 → findWrite 0 x S'.mem = none) :
    Common m₀ m' where
  sp := by rw [Match.sp_eq hm₀ hm hsp]; exact C.sp
  x29 := by rw [Match.reg_eq hm₀ hm h29 h29']; exact C.x29
  save j hj t ht := by
    rw [length_regBytes] at ht
    have := C.save j hj t (by rw [length_regBytes]; exact ht)
    rw [show fb + 5776 + 8 * j = fb + (5776 + 8 * j) by omega, ← ad_add, addr_add_addr] at this ⊢
    rw [hm.mem 0 _ 5872 rfl _ (by omega)]
    unfold memByte
    rw [hsave _ (by omega) (by omega)]
    exact this
  same := (C.same.trans (hm.sameOutside_in hwf hw)).mono fun p hp => hp.elim id fun ⟨r, hr, b, sz, hb, hin⟩ => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact P.inRange_lo (by rw [fb_eq]) hin
  kept := C.kept.trans (hm.kept hwf)

end

end

end NativeRustcArm.Xmss.XmssVerify
