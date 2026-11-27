module

public import NativeRustcX64.Code.Common.Finalize.Names

public import NativeRustcX64.Hasher.Bytes
public import NativeRustcX64.Hasher.FinalizeExec
public import NativeRustcX64.Got

/-!
# `Hasher::finalize` (x86-64): where things are, what its states keep

From the entry state `m0` (output at `oAt m0`, hasher at `hAt m0`, RSP `spAt m0`; the frame of
392 bytes at `frAt m0`, 384 below RSP): `FinalizePre`'s addresses as numbers (`Geo`, `geo_of`);
what every state after the prologue `m1` keeps between blocks (`Fr`: RSP at the frame's offset 8,
the output pointer in RBX, RBP and R13, memory as `m1`'s but in the frame's first 352 bytes and
`keccak_f`'s stack below it (`ChgF`), every mapped byte); the hasher and the round constants stay
as at the entry (`hasher_same`, `rc_same`). The byte facts of the final block (`getD_finalBlock`)
and of the values the executor computes (`byteOf_xorW8`, `byteOf_ofNat_ofBytes`). The blocks'
places and labels (`hb<k>`, `lbl_entry`).
-/

namespace NativeRustcX64.Hasher.Finalize

open NativeRustc NativeRustc.Keccak NativeRustcX64.Sym NativeRustcX64.Common.Finalize

@[expose] public section

/-- The output's address at the entry. -/
def oAt (m : MachineData) : BitVec 64 := reg m .rdi
/-- The hasher's address at the entry. -/
def hAt (m : MachineData) : BitVec 64 := reg m .rsi
/-- RSP at the entry. -/
def spAt (m : MachineData) : BitVec 64 := rspOf m
/-- The frame's address. -/
def frAt (m : MachineData) : BitVec 64 := spAt m - 384#64

/-- Frame, input hasher, and the ordinary-memory slot read by the current block. -/
def gotRegions [Labels] (m0 : MachineData) (l : Label) : List (BitVec 64 × Nat) :=
  [(frAt m0, 392), (hAt m0, 344), (gotAddr l, 8)]

/-- The hasher's bytes at the entry. -/
def hbytes (m0 : MachineData) : List UInt8 := bytesOf m0.dmem (hAt m0) 344

/-- What the states after the prologue change: the frame's first 352 bytes and the 288 bytes of
`keccak_f`'s stack below it. -/
def ChgF (m0 : MachineData) (p : BitVec 64) : Prop := InRange (frAt m0 - 288#64) 640 p

/-- What every state between blocks after the prologue keeps. -/
structure Fr (m0 m1 m : MachineData) : Prop where
  rsp : reg m .rsp = frAt m0 + 8#64
  rbx : reg m .rbx = oAt m0
  saved : ∀ r ∈ [Reg64.rbp, .r13], reg m r = reg m0 r
  same : SameOutside m1.dmem m.dmem (ChgF m0)
  kept : Kept m0.dmem m.dmem

/-- `FinalizePre`'s addresses as numbers. -/
structure Geo (m0 : MachineData) : Prop where
  o : (oAt m0).toNat + 32 ≤ 2 ^ 64
  h : (hAt m0).toNat + 344 ≤ 2 ^ 64
  s : 672 ≤ (spAt m0).toNat
  s8 : (spAt m0).toNat + 8 ≤ 2 ^ 64
  oh : (oAt m0).toNat + 32 ≤ (hAt m0).toNat ∨ (hAt m0).toNat + 344 ≤ (oAt m0).toNat
  hs : (hAt m0).toNat + 344 ≤ (spAt m0).toNat - 672 ∨ (spAt m0).toNat + 8 ≤ (hAt m0).toNat
  os : (oAt m0).toNat + 32 ≤ (spAt m0).toNat - 672 ∨ (spAt m0).toNat + 8 ≤ (oAt m0).toNat

/-- The round constants' place as numbers. -/
structure GeoRc [Labels] (m0 : MachineData) : Prop where
  nw : rcAddr.toNat + 192 ≤ 2 ^ 64
  rs : rcAddr.toNat + 192 ≤ (spAt m0).toNat - 672 ∨ (spAt m0).toNat + 8 ≤ rcAddr.toNat
  ro : (oAt m0).toNat + 32 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ (oAt m0).toNat

end

public section

theorem toNat_sub_ofNat' {a : BitVec 64} {j : Nat} (h : j ≤ a.toNat) :
    (a - BitVec.ofNat 64 j).toNat = a.toNat - j := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := a.isLt
  omega

theorem stackBelow_toNat {m : MachineData} {n : Nat} (h : n ≤ (rspOf m).toNat) :
    (stackBelow m n).toNat = (rspOf m).toNat - n :=
  toNat_sub_ofNat' h

theorem geo_of {m0 : MachineData} [Labels] (hpre : FinalizePre m0) : Geo m0 := by
  obtain ⟨⟨hs, hs8, -⟩, -, -, -, hh, -, ho, hoh, hhs, hos, -⟩ := hpre
  have hb : (stackBelow m0 finalizeStack).toNat = (rspOf m0).toNat - 672 := stackBelow_toNat hs
  have hu : finalizeStack = 672 := rfl
  unfold Apart at hoh hhs hos
  rw [hb, hu] at hhs hos
  refine ⟨ho, hh, hu ▸ hs, hs8, hoh, ?_, ?_⟩
  · exact hhs.imp id fun h => by unfold hAt spAt; have := hu ▸ hs; omega
  · exact hos.imp id fun h => by unfold oAt spAt; have := hu ▸ hs; omega

theorem geoRc_of {m0 : MachineData} [Labels] (hpre : FinalizePre m0) : GeoRc m0 := by
  obtain ⟨⟨hs, -, -⟩, ⟨-, hnw, hrs⟩, -, -, -, -, -, -, -, -, hor, -⟩ := hpre
  have hb : (stackBelow m0 finalizeStack).toNat = (rspOf m0).toNat - 672 := stackBelow_toNat hs
  have hu : finalizeStack = 672 := rfl
  unfold Apart at hrs hor
  rw [hb, hu] at hrs
  refine ⟨hnw, ?_, hor⟩
  exact hrs.imp id fun h => by unfold spAt; have := hu ▸ hs; omega

/-- The loader assumptions at the finalize entry. -/
theorem got_of {m0 : MachineData} [Labels] (hpre : FinalizePre m0) :
    GotAt m0 finalizeStack [(oAt m0, 32), (hAt m0, 344)] ["memcpy", "memset"] :=
  hpre.2.2.2.2.2.2.2.2.2.2.2

theorem frAt_toNat {m0 : MachineData} (g : Geo m0) : (frAt m0).toNat = (spAt m0).toNat - 384 :=
  toNat_sub_ofNat' (by have := g.s; omega)

theorem chg_base {m0 : MachineData} (g : Geo m0) :
    (frAt m0 - 288#64).toNat = (spAt m0).toNat - 672 := by
  rw [toNat_sub_ofNat' (by rw [frAt_toNat g]; have := g.s; omega), frAt_toNat g]
  omega

/-- What the states change, as numbers. -/
theorem chgF_iff {m0 : MachineData} (g : Geo m0) (p : BitVec 64) :
    ChgF m0 p ↔ (spAt m0).toNat - 672 ≤ p.toNat ∧ p.toNat < (spAt m0).toNat - 32 := by
  unfold ChgF
  rw [inRange_iff (by rw [chg_base g]; have := g.s8; omega), chg_base g]
  have := g.s
  omega

/-- The frame's first 352 bytes are in `ChgF`. -/
theorem chg_of_frame {m0 : MachineData} (g : Geo m0) {o n : Nat} (hn : o + n ≤ 352)
    {p : BitVec 64} (hp : (frAt m0).toNat + o ≤ p.toNat ∧ p.toNat < (frAt m0).toNat + o + n) :
    ChgF m0 p := by
  rw [chgF_iff g]
  rw [frAt_toNat g] at hp
  have := g.s
  omega

/-- The frame, as numbers. -/
theorem frame_iff {m0 : MachineData} (g : Geo m0) (p : BitVec 64) :
    InRange (frAt m0) 384 p ↔ (spAt m0).toNat - 384 ≤ p.toNat ∧ p.toNat < (spAt m0).toNat := by
  rw [inRange_iff (by rw [frAt_toNat g]; have := g.s8; omega), frAt_toNat g]
  have := g.s
  omega

/-- **The hasher is as at the entry** in any state after the prologue. -/
theorem hasher_same {m0 m1 m : MachineData} (g : Geo m0) (hfr : Fr m0 m1 m)
    (h01 : SameOutside m0.dmem m1.dmem (InRange (frAt m0) 384)) {i : Nat} (hi : i < 344) :
    m.dmem.get? (hAt m0 + BitVec.ofNat 64 i) = m0.dmem.get? (hAt m0 + BitVec.ofNat 64 i) := by
  have ht := toNat_add_ofNat' (a := hAt m0) (i := i) (by have := g.h; omega)
  rw [hfr.same _ (by rw [chgF_iff g, ht]; have := g.hs; omega),
    h01 _ (by rw [frame_iff g, ht]; have := g.hs; omega)]

/-- **The round constants are as at the entry** in any state after the prologue. -/
theorem rc_same {m0 m1 m : MachineData} [Labels] (g : Geo m0) (gr : GeoRc m0)
    (hfr : Fr m0 m1 m) (h01 : SameOutside m0.dmem m1.dmem (InRange (frAt m0) 384)) {i : Nat}
    (hi : i < 192) :
    m.dmem.get? (rcAddr + BitVec.ofNat 64 i) = m0.dmem.get? (rcAddr + BitVec.ofNat 64 i) := by
  have ht := toNat_add_ofNat' (a := rcAddr) (i := i) (by have := gr.nw; omega)
  rw [hfr.same _ (by rw [chgF_iff g, ht]; have := gr.rs; omega),
    h01 _ (by rw [frame_iff g, ht]; have := gr.rs; omega)]

/-- Neither the prologue nor any intermediate frame mutation changes a GOT slot. -/
theorem got_same {m0 m1 m : MachineData} [Labels] (hpre : FinalizePre m0)
    (hfr : Fr m0 m1 m)
    (h01 : SameOutside m0.dmem m1.dmem (InRange (frAt m0) 384))
    {l : Label} (hl : l ∈ ["memcpy", "memset"]) {i : Nat} (hi : i < 8) :
    m.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
      m0.dmem.get? (gotAddr l + BitVec.ofNat 64 i) := by
  have g := geo_of hpre
  obtain ⟨_, hn, hs, _⟩ := (got_of hpre).1 l hl
  have hb := stackBelow_toNat g.s
  change Apart (gotAddr l) 8 (stackBelow m0 finalizeStack) (finalizeStack + 8) at hs
  change (stackBelow m0 finalizeStack).toNat = (spAt m0).toNat - 672 at hb
  unfold Apart at hs
  rw [hb] at hs
  change _ ≤ _ ∨ (spAt m0).toNat - 672 + (672 + 8) ≤ _ at hs
  have ht := toNat_add_ofNat' (a := gotAddr l) (i := i) (by
    change (gotAddr l).toNat + 8 ≤ 2 ^ 64 at hn
    omega)
  have hs0 := g.s
  rw [hfr.same _ (by rw [chgF_iff g, ht]; omega),
    h01 _ (by rw [frame_iff g, ht]; omega)]

/-- `Fr` after a step that keeps RSP, RBX, RBP and R13, changes memory only in `ChgF` and unmaps
nothing. -/
theorem Fr.update {m0 m1 m m' : MachineData} (hf : Fr m0 m1 m)
    (hr : ∀ r ∈ [Reg64.rsp, .rbx, .rbp, .r13], reg m' r = reg m r)
    (hs : SameOutside m.dmem m'.dmem (ChgF m0)) (hk : Kept m.dmem m'.dmem) : Fr m0 m1 m' where
  rsp := by rw [hr .rsp (by simp)]; exact hf.rsp
  rbx := by rw [hr .rbx (by simp)]; exact hf.rbx
  saved r h := by
    rw [hr r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)), hf.saved r h]
  same p hp := by rw [hs p hp]; exact hf.same p hp
  kept p hp := hk p (hf.kept p hp)

/-- **`Fr` after a block ending in a call and the callee's return**: the block keeps RBX, RBP and
R13 and leaves RSP at the frame's start (the return-address slot), its writes and the callee's
are in `ChgF`, and the callee returns 8 above with the callee-saved registers kept. -/
theorem Fr.after_call [Labels] {m0 m1 m : MachineData} {st st' : MachineState}
    {rs : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hf : Fr m0 m1 m) (hm : Match (Env.ofMachine m rs vs ret) S st.data)
    (hwf : (Env.ofMachine m rs vs ret).WF) (hb : (Env.ofMachine m rs vs ret).base 0 = frAt m0)
    (hrsp : S.reg .rsp = some (.ptr 0 0))
    (hregs : ∀ r ∈ [Reg64.rbx, .rbp, .r13], S.reg r = some (.reg r))
    (hwr : ∀ p, Written (Env.ofMachine m rs vs ret) S p → ChgF m0 p)
    (hcall : rspOf st'.data = rspOf st.data + 8#64) (hsaved : Saved st.data st'.data)
    {R : BitVec 64 → Prop} (hsame : SameOutside st.data.dmem st'.data.dmem R)
    (hR : ∀ p, R p → ChgF m0 p) : Fr m0 m1 st'.data where
  rsp := by
    show rspOf st'.data = _
    rw [hcall]
    show st.data.regs.get64 .rsp + 8#64 = _
    rw [hm.regs .rsp _ hrsp]
    simp [Sym.eval, hb]
  rbx := by
    show st'.data.regs.get64 .rbx = _
    rw [hsaved.1 .rbx rfl, hm.regs .rbx _ (hregs .rbx (by simp))]
    exact hf.rbx
  saved r h := by
    have hc : calleeSaved r = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> rfl
    show st'.data.regs.get64 r = _
    rw [hsaved.1 r hc, hm.regs r _ (hregs r (List.mem_cons_of_mem _ h))]
    exact hf.saved r h
  same p hp := by
    rw [hsame p fun h => hp (hR p h), hm.get?_mem0 hwf fun h => hp (hwr p h)]
    exact hf.same p hp
  kept p hp := hsaved.2 p (hm.kept hwf p (hf.kept p hp))

/-- `Fr` after a block without calls that keeps RSP, RBX, RBP and R13 and writes in `ChgF`. -/
theorem Fr.after_block [Labels] {m0 m1 m m' : MachineData}
    {rs : List (BitVec 64 × Nat)} {vs : Nat → BitVec 64} {ret : BitVec 64} {S S' : SState}
    (hf : Fr m0 m1 m) (hm₀ : Match (Env.ofMachine m rs vs ret) S m)
    (hm : Match (Env.ofMachine m rs vs ret) S' m') (hwf : (Env.ofMachine m rs vs ret).WF)
    (hregs : ∀ r ∈ [Reg64.rsp, .rbx, .rbp, .r13], ∃ v, S.reg r = some v ∧ S'.reg r = some v)
    (hwr : ∀ p, Written (Env.ofMachine m rs vs ret) S' p → ChgF m0 p) : Fr m0 m1 m' :=
  hf.update (fun r hr => by
      obtain ⟨v, h0, h1⟩ := hregs r hr
      exact Match.reg_eq hm₀ hm h0 h1)
    (fun p hp => hm.get?_mem0 hwf fun h => hp (hwr p h)) (hm.kept hwf)

/-! ## Bytes -/

theorem getD_modify (l : List UInt8) (i j : Nat) (f : UInt8 → UInt8) :
    (l.modify i f).getD j 0 = if j = i ∧ j < l.length then f (l.getD j 0) else l.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_modify]
  by_cases h : j < l.length
  · rw [List.getElem?_eq_getElem h]
    by_cases hij : j = i
    · subst hij
      simp [h]
    · simp [hij, Ne.symm hij]
  · rw [List.getElem?_eq_none (by omega)]
    simp [h]

/-- **A byte of the final block**: the remaining byte, or `0`, XOR `PAD_FIRST` after them, XOR
`PAD_LAST` at the end. -/
theorem getD_finalBlock {T : List UInt8} (hT : T.length < 136) {j : Nat} (hj : j < 136) :
    (finalBlock T).getD j 0 =
      ((if j < T.length then T.getD j 0 else 0) ^^^ (if j = T.length then 1 else 0)) ^^^
        (if j = 135 then 0x80 else 0) := by
  have hl : (T ++ List.replicate (136 - T.length) 0).length = 136 := by simp; omega
  have hpad : (T ++ List.replicate (136 - T.length) 0).getD j 0 = if j < T.length then T.getD j 0
      else 0 := by
    simp only [List.getD_eq_getElem?_getD]
    by_cases h : j < T.length
    · rw [List.getElem?_append_left h, ite_pos' h]
    · rw [List.getElem?_append_right (by omega), List.getElem?_replicate, ite_neg' h]
      split <;> rfl
  rw [finalBlock, getD_modify, List.length_modify, hl, getD_modify, hl, hpad]
  by_cases h2 : j = 135
  · rw [ite_pos' ⟨h2, hj⟩, ite_pos' h2]
    by_cases h1 : j = T.length
    · rw [ite_pos' ⟨h1, hj⟩, ite_pos' h1]
    · rw [ite_neg' (fun h => h1 h.1), ite_neg' h1, UInt8.xor_zero]
  · rw [ite_neg' (fun h => h2 h.1), ite_neg' h2, UInt8.xor_zero]
    by_cases h1 : j = T.length
    · rw [ite_pos' ⟨h1, hj⟩, ite_pos' h1]
    · rw [ite_neg' (fun h => h1 h.1), ite_neg' h1, UInt8.xor_zero]

/-- Byte 0 of an 8-bit XOR. -/
theorem byteOf_xorW8 (x y : BitVec 64) :
    byteOf (BinOp.apply .xor .W8 x y) 0 = byteOf x 0 ^^^ byteOf y 0 := by
  apply UInt8.toNat_inj.mp
  simp only [BinOp.apply, ext, low, byteOf, UInt8.toNat_ofNat', UInt8.toNat_xor, Nat.mul_zero,
    Nat.pow_zero, Nat.div_one]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, BitVec.toNat_setWidth, BitVec.toNat_xor, Nat.testBit_xor]
  by_cases hj : j < 8
  · simp [hj, show j < 64 by omega]
  · simp [hj]

/-- Byte 0 of a 64-bit XOR (of any width-64 byte). -/
theorem byteOf_xorW64 (x y : BitVec 64) (t : Nat) :
    byteOf (BinOp.apply .xor .W64 x y) t = byteOf x t ^^^ byteOf y t := by
  simp only [BinOp.apply, low_W64, ext_W64]
  exact byteOf_xor x y t

theorem byteOf_ofNat_lt (c : Nat) (hc : c < 256) : byteOf (BitVec.ofNat 64 c) 0 = UInt8.ofNat c := by
  simp only [byteOf, BitVec.toNat_ofNat, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  congr 1
  omega

/-- The byte `t` of the value of bytes `bs`. -/
theorem byteOf_ofNat_ofBytes (bs : List UInt8) (hn : bs.length ≤ 8) (t : Nat) :
    byteOf (BitVec.ofNat 64 (Nat.ofBytes bs)) t = bs.getD t 0 := by
  have := byteOf_ofBytes_of_le bs hn t
  rwa [ofBytes_natCast, BitVec.ofInt_natCast] at this

/-! ## Places -/

variable [ElfHost] {sec k : Nat}

theorem hb0 (hp : PlacedIn code sec k) :
    b0.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcX64.Common.Finalize.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : PlacedIn code sec k) :
    b1.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcX64.Common.Finalize.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : PlacedIn code sec k) :
    b2.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcX64.Common.Finalize.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : PlacedIn code sec k) :
    b3.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcX64.Common.Finalize.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : PlacedIn code sec k) :
    b4.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcX64.Common.Finalize.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : PlacedIn code sec k) :
    b5.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcX64.Common.Finalize.b5Offset) :=
  b5_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb5ab (hp : PlacedIn code sec k) :
    (b5a ++ b5b).IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcX64.Common.Finalize.b5Offset) := by
  rw [b5a, b5b, List.take_append_drop]
  exact hb5 hp
theorem hb5a (hp : PlacedIn code sec k) :
    b5a.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcX64.Common.Finalize.b5Offset) :=
  (List.IsInfixAt.append (hb5ab hp)).1
theorem hb5b (hp : PlacedIn code sec k) :
    b5b.IsInfixAt (ElfHost.sectionProg sec) (k + (NativeRustcX64.Common.Finalize.b5Offset + b5a.length)) :=
  (List.IsInfixAt.append (hb5ab hp)).2
theorem hb6 (hp : PlacedIn code sec k) :
    b6.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcX64.Common.Finalize.b6Offset) :=
  b6_in_code.trans hp.1 (List.cons_ne_nil _ _)

theorem lbl_entry (hp : PlacedIn code sec k) :
    Labels.label NativeRustcX64.Common.Finalize.entryLabel =
      ElfHost.addrOf sec (k + NativeRustcX64.Common.Finalize.b0Offset) :=
  hp.label NativeRustcX64.Common.Finalize.entry_at

end

end NativeRustcX64.Hasher.Finalize
