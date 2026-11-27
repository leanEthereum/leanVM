module

public import NativeRustcX64.Code.Common.Update.Names

public import NativeRustcX64.Hasher.Bytes
public import NativeRustcX64.Hasher.UpdateExec
public import NativeRustcX64.KeccakF.Inv
public import NativeRustcX64.Got

/-!
# `Hasher::update`'s loop: its states (x86-64)

From the entry state `m0` (hasher at `hAt m0`, input `input m0` of `nOf m0` bytes, RSP `spAt m0`,
the frame at `frm m0`): what every state after the prologue keeps (`Frame`: the hasher and buffer
pointers, RSP, the pushed registers in the frame, the resolved `memcpy` target in RBP, memory
as `m0`'s but in the hasher and the stack below RSP (`Chg`), every mapped byte); the loop head
`.LUpdate_1` having absorbed the input's first
`c` bytes (`Inv`); `.LUpdate_5` after a turn that took `t` more (`Mid`). `UpdatePre`'s addresses as
numbers (`Geo`, `geo_of`); the input and the round constants as at the entry (`input_same`,
`rc_same`). The blocks' places and labels (`hb<k>`, `lbl_*`).
-/

namespace NativeRustcX64.Hasher.Update

open NativeRustc NativeRustc.Keccak NativeRustcX64.Sym NativeRustcX64.Common.Update
open NativeRustcX64.KeccakF NativeRustcX64.Hasher

@[expose] public section

/-- The hasher's address at the entry. -/
def hAt (m : MachineData) : BitVec 64 := reg m .rdi
/-- The input's address at the entry. -/
def dAt (m : MachineData) : BitVec 64 := reg m .rsi
/-- The input's length at the entry. -/
def nOf (m : MachineData) : Nat := (reg m .rdx).toNat
/-- RSP at the entry. -/
def spAt (m : MachineData) : BitVec 64 := rspOf m
/-- The frame: 112 bytes below the entry's RSP. -/
def frm (m : MachineData) : BitVec 64 := spAt m - 112#64

/-- The input. -/
def input (m0 : MachineData) : List UInt8 := bytesOf m0.dmem (dAt m0) (nOf m0)

/-- The hasher's bytes in `m`. -/
def hasher (m0 m : MachineData) : List UInt8 := bytesOf m.dmem (hAt m0) 344

/-- What `update` changes: the hasher and the stack below RSP. -/
def Chg (m0 : MachineData) (p : BitVec 64) : Prop :=
  InRange (hAt m0) 344 p ∨ InRange (stackBelow m0 updateStack) updateStack p

/-- What the loop changes: the hasher and the stack below the pushed registers. -/
def ChgL (m0 : MachineData) (p : BitVec 64) : Prop :=
  InRange (hAt m0) 344 p ∨ InRange (stackBelow m0 updateStack) 352 p

/-- The bytes `H` have absorbed the input's first `c` bytes after whatever the entry's had. -/
def Holds (m0 : MachineData) (H : List UInt8) (c : Nat) : Prop :=
  ∀ a, HasherHolds (hasher m0 m0) a → HasherHolds H (a ++ (input m0).take c)

/-- The frame's slots of the pushed registers. -/
def pushSlots : List (Nat × Reg64) :=
  [(64, .rbx), (72, .r12), (80, .r13), (88, .r14), (96, .r15), (104, .rbp)]

/-- What every state after the prologue keeps. -/
structure Frame [Labels] (m0 m : MachineData) : Prop where
  r14 : reg m .r14 = hAt m0
  r13 : reg m .r13 = hAt m0 + 200#64
  rsp : rspOf m = frm m0 + 8#64
  saved : AllOf (fun p : Nat × Reg64 =>
    WordAt m.dmem (frm m0 + BitVec.ofNat 64 p.1) (reg m0 p.2)) pushSlots
  same : SameOutside m0.dmem m.dmem (Chg m0)
  kept : Kept m0.dmem m.dmem
  rbp : reg m .rbp = (Labels.label "memcpy").toBitVec

/-- **The loop head** `.LUpdate_1`, the input's first `c` bytes absorbed. -/
structure Inv [Labels] (m0 : MachineData) (c : Nat) (m : MachineData) : Prop where
  frame : Frame m0 m
  le : c ≤ nOf m0
  rbx : reg m .rbx = BitVec.ofNat 64 (nOf m0 - c)
  r15 : reg m .r15 = dAt m0 + BitVec.ofNat 64 c
  rdi : (reg m .rdi).toNat = bufLen (hasher m0 m)
  holds : Holds m0 (hasher m0 m) c

/-- **`.LUpdate_5`**, after a turn from `c` absorbed bytes that took `t` more. -/
structure Mid [Labels] (m0 : MachineData) (c t : Nat) (m : MachineData) : Prop where
  frame : Frame m0 m
  le : c + t ≤ nOf m0
  pos : 0 < t ∨ c = nOf m0
  rbx : reg m .rbx = BitVec.ofNat 64 (nOf m0 - c)
  r15 : reg m .r15 = dAt m0 + BitVec.ofNat 64 c
  r12 : reg m .r12 = BitVec.ofNat 64 t
  rdi : (reg m .rdi).toNat = bufLen (hasher m0 m)
  holds : Holds m0 (hasher m0 m) (c + t)

/-- `UpdatePre`'s addresses as numbers. -/
structure Geo (m0 : MachineData) : Prop where
  h : (hAt m0).toNat + 344 ≤ 2 ^ 64
  d : (dAt m0).toNat + nOf m0 ≤ 2 ^ 64
  s : 400 ≤ (spAt m0).toNat
  s8 : (spAt m0).toNat + 8 ≤ 2 ^ 64
  hd : (hAt m0).toNat + 344 ≤ (dAt m0).toNat ∨ (dAt m0).toNat + nOf m0 ≤ (hAt m0).toNat
  hs : (hAt m0).toNat + 344 ≤ (spAt m0).toNat - 400 ∨ (spAt m0).toNat + 8 ≤ (hAt m0).toNat
  ds : (dAt m0).toNat + nOf m0 ≤ (spAt m0).toNat - 400 ∨ (spAt m0).toNat + 8 ≤ (dAt m0).toNat

/-- The round constants' place, as numbers. -/
structure GeoRc [Labels] (m0 : MachineData) : Prop where
  nw : rcAddr.toNat + 192 ≤ 2 ^ 64
  rs : rcAddr.toNat + 192 ≤ (spAt m0).toNat - 400 ∨ (spAt m0).toNat + 8 ≤ rcAddr.toNat
  hr : (hAt m0).toNat + 344 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ (hAt m0).toNat

end

public section

theorem toNat_sub_ofNat {a : BitVec 64} {j : Nat} (h : j ≤ a.toNat) :
    (a - BitVec.ofNat 64 j).toNat = a.toNat - j := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := a.isLt
  omega

theorem stackBelow_toNat {m : MachineData} {n : Nat} (h : n ≤ (rspOf m).toNat) :
    (stackBelow m n).toNat = (rspOf m).toNat - n :=
  toNat_sub_ofNat h

theorem geo_of {m0 : MachineData} [Labels] (hpre : UpdatePreElf m0) : Geo m0 := by
  obtain ⟨⟨hs, hs8, -⟩, -, -, -, hh, -, hd, hhd, hhs, hds, -⟩ := hpre
  have hu : updateStack = 400 := rfl
  have hb : (stackBelow m0 updateStack).toNat = (rspOf m0).toNat - 400 := stackBelow_toNat hs
  unfold Apart at hhs hds
  rw [hb, hu] at hhs hds
  refine ⟨hh, hd, hs, hs8, hhd, ?_, ?_⟩
  · exact hhs.imp id fun h => by unfold hAt spAt; omega
  · exact hds.imp id fun h => by unfold dAt spAt; omega

theorem geoRc_of {m0 : MachineData} [Labels] (hpre : UpdatePreElf m0) : GeoRc m0 := by
  obtain ⟨⟨hs, -, -⟩, ⟨-, hnw, hrs⟩, -, -, -, -, -, -, -, -, hhr, -⟩ := hpre
  have hu : updateStack = 400 := rfl
  have hb : (stackBelow m0 updateStack).toNat = (rspOf m0).toNat - 400 := stackBelow_toNat hs
  unfold Apart at hrs
  rw [hb, hu] at hrs
  exact ⟨hnw, hrs.imp id fun h => by unfold spAt; omega, hhr⟩

/-- The loader assumptions at the update entry. -/
theorem got_of {m0 : MachineData} [Labels] (hpre : UpdatePreElf m0) :
    GotAt m0 updateStack [(hAt m0, 344)] ["memcpy"] :=
  hpre.2.2.2.2.2.2.2.2.2.2.2

theorem frm_toNat {m0 : MachineData} (g : Geo m0) : (frm m0).toNat = (spAt m0).toNat - 112 :=
  toNat_sub_ofNat (by have := g.s; omega)

/-- What `update` changes, as numbers. -/
theorem chg_iff {m0 : MachineData} (g : Geo m0) (p : BitVec 64) :
    Chg m0 p ↔ ((hAt m0).toNat ≤ p.toNat ∧ p.toNat < (hAt m0).toNat + 344) ∨
      ((spAt m0).toNat - 400 ≤ p.toNat ∧ p.toNat < (spAt m0).toNat) := by
  have hb : (stackBelow m0 updateStack).toNat = (spAt m0).toNat - 400 :=
    stackBelow_toNat g.s
  have hu : updateStack = 400 := rfl
  unfold Chg
  rw [hu] at hb ⊢
  rw [inRange_iff g.h, inRange_iff (by rw [hb]; have := g.s8; have := g.s; omega), hb]
  have := g.s
  omega

/-- The stack's bytes from the frame. -/
theorem stack_frm {m0 : MachineData} (g : Geo m0) {i : Nat} (hi : i < 120) :
    rspOf m0 - BitVec.ofNat 64 updateStack + BitVec.ofNat 64 (288 + i) =
      frm m0 + BitVec.ofNat 64 i := by
  have hs := g.s
  have hs8 := g.s8
  have hsb : (rspOf m0 - BitVec.ofNat 64 updateStack).toNat = (spAt m0).toNat - 400 :=
    stackBelow_toNat hs
  have e1 : (rspOf m0 - BitVec.ofNat 64 updateStack + BitVec.ofNat 64 (288 + i)).toNat =
      (spAt m0).toNat - 112 + i := by
    rw [toNat_add_ofNat' (by rw [hsb]; omega), hsb]
    omega
  have e2 : (frm m0 + BitVec.ofNat 64 i).toNat = (spAt m0).toNat - 112 + i := by
    rw [toNat_add_ofNat' (by rw [frm_toNat g]; omega), frm_toNat g]
  exact BitVec.eq_of_toNat_eq (e1.trans e2.symm)

/-- The frame's mapped bytes: the stack's at the entry. -/
theorem frm_mapped {m0 : MachineData} [Labels] (hpre : UpdatePreElf m0) :
    Mapped m0.dmem (frm m0) 120 := fun i hi => by
  have := hpre.1.2.2 (288 + i) (by show 288 + i < 400 + 8; omega)
  rwa [stack_frm (geo_of hpre) hi] at this

/-- What the loop changes, as numbers. -/
theorem chgL_iff {m0 : MachineData} (g : Geo m0) (p : BitVec 64) :
    ChgL m0 p ↔ ((hAt m0).toNat ≤ p.toNat ∧ p.toNat < (hAt m0).toNat + 344) ∨
      ((spAt m0).toNat - 400 ≤ p.toNat ∧ p.toNat < (spAt m0).toNat - 48) := by
  have hb : (stackBelow m0 updateStack).toNat = (spAt m0).toNat - 400 :=
    stackBelow_toNat g.s
  unfold ChgL
  rw [inRange_iff g.h, inRange_iff (by rw [hb]; have := g.s8; have := g.s; omega), hb]
  have := g.s
  omega

theorem chg_of_chgL {m0 : MachineData} (g : Geo m0) {p : BitVec 64} (h : ChgL m0 p) : Chg m0 p := by
  rw [chgL_iff g] at h
  rw [chg_iff g]
  omega

theorem hasher_congr {m0 m m' : MachineData} (h : ∀ p, m'.dmem.get? p = m.dmem.get? p) :
    hasher m0 m' = hasher m0 m :=
  bytesOf_congr fun _ _ => h _

/-- A pushed register's slot is outside what the loop changes. -/
theorem push_not_chgL {m0 : MachineData} (g : Geo m0) {o i : Nat} (ho : 64 ≤ o) (hoi : o + i < 112) :
    ¬ChgL m0 (frm m0 + BitVec.ofNat 64 o + BitVec.ofNat 64 i) := by
  rw [chgL_iff g, add_ofNat_add, toNat_add_ofNat' (by rw [frm_toNat g]; have := g.s8; omega),
    frm_toNat g]
  have := g.hs
  have := g.s
  omega

/-- `Frame` after a step that keeps the frame pointers and resolved call target, changes memory
only where the loop does, and unmaps nothing. -/
theorem Frame.update [Labels] {m0 m m' : MachineData} (g : Geo m0) (hf : Frame m0 m)
    (h13 : reg m' .r13 = reg m .r13) (h14 : reg m' .r14 = reg m .r14) (hsp : rspOf m' = rspOf m)
    (hd : ∀ p, ¬ChgL m0 p → m'.dmem.get? p = m.dmem.get? p) (hk : Kept m.dmem m'.dmem)
    (hbp : reg m' .rbp = (Labels.label "memcpy").toBitVec) :
    Frame m0 m' where
  r14 := h14.trans hf.r14
  r13 := h13.trans hf.r13
  rsp := hsp.trans hf.rsp
  saved := by
    have hs := hf.saved
    simp only [AllOf, pushSlots] at hs ⊢
    obtain ⟨s0, s1, s2, s3, s4, s5, -⟩ := hs
    have key : ∀ {o : Nat} {w : BitVec 64}, 64 ≤ o → o + 8 ≤ 112 →
        WordAt m.dmem (frm m0 + BitVec.ofNat 64 o) w →
        WordAt m'.dmem (frm m0 + BitVec.ofNat 64 o) w := fun ho ho8 hw i hi => by
      simp only [List.length_map, List.length_range] at hi
      rw [hd _ (push_not_chgL g ho (by omega))]
      exact hw i (by simp [hi])
    exact ⟨key (by decide) (by decide) s0, key (by decide) (by decide) s1,
      key (by decide) (by decide) s2, key (by decide) (by decide) s3,
      key (by decide) (by decide) s4, key (by decide) (by decide) s5, trivial⟩
  same p hp := by
    rw [hd p fun h => hp (chg_of_chgL g h)]
    exact hf.same p hp
  kept p hp := hk p (hf.kept p hp)
  rbp := hbp

/-- **The input is as at the entry** in any state of the loop. -/
theorem input_same {m0 m : MachineData} [Labels] (g : Geo m0) (hfr : Frame m0 m) {i : Nat}
    (hi : i < nOf m0) :
    m.dmem.get? (dAt m0 + BitVec.ofNat 64 i) = m0.dmem.get? (dAt m0 + BitVec.ofNat 64 i) := by
  have ht := toNat_add_ofNat' (a := dAt m0) (i := i) (by have := g.d; omega)
  rw [hfr.same _ (by rw [chg_iff g, ht]; have := g.hd; have := g.ds; omega)]

/-- **The round constants are as at the entry** in any state of the loop. -/
theorem rc_same {m0 m : MachineData} [Labels] (g : Geo m0) (gr : GeoRc m0) (hfr : Frame m0 m)
    {i : Nat} (hi : i < 192) :
    m.dmem.get? (rcAddr + BitVec.ofNat 64 i) = m0.dmem.get? (rcAddr + BitVec.ofNat 64 i) := by
  have ht := toNat_add_ofNat' (a := rcAddr) (i := i) (by have := gr.nw; omega)
  rw [hfr.same _ (by rw [chg_iff g, ht]; have := gr.hr; have := gr.rs; omega)]

/-- The loop's frame cannot change the loader's `memcpy` slot. -/
theorem got_same {m0 m : MachineData} [Labels] (hpre : UpdatePreElf m0) (hfr : Frame m0 m)
    {i : Nat} (hi : i < 8) :
    m.dmem.get? (gotAddr "memcpy" + BitVec.ofNat 64 i) =
      m0.dmem.get? (gotAddr "memcpy" + BitVec.ofNat 64 i) := by
  have g := geo_of hpre
  obtain ⟨_, hn, hs, ha⟩ := (got_of hpre).1 "memcpy" (by simp)
  have hh := ha (hAt m0, 344) (by simp)
  change Apart (gotAddr "memcpy") 8 (hAt m0) 344 at hh
  have hb := stackBelow_toNat g.s
  change Apart (gotAddr "memcpy") 8 (stackBelow m0 updateStack) (updateStack + 8) at hs
  change (stackBelow m0 updateStack).toNat = (spAt m0).toNat - 400 at hb
  unfold Apart at hs hh
  rw [hb] at hs
  change _ ≤ _ ∨ (spAt m0).toNat - 400 + (400 + 8) ≤ _ at hs
  have ht := toNat_add_ofNat' (a := gotAddr "memcpy") (i := i) (by
    change (gotAddr "memcpy").toNat + 8 ≤ 2 ^ 64 at hn
    omega)
  apply hfr.same
  rw [chg_iff g, ht]
  have := g.s
  omega

/-- The GOT slot is apart from both symbolic data regions. -/
theorem got_apart {m0 : MachineData} [Labels] (hpre : UpdatePreElf m0) :
    Apart (hAt m0) 344 (gotAddr "memcpy") 8 ∧
      Apart (frm m0) 120 (gotAddr "memcpy") 8 := by
  have g := geo_of hpre
  obtain ⟨_, _, hs, ha⟩ := (got_of hpre).1 "memcpy" (by simp)
  have hh := ha (hAt m0, 344) (by simp)
  refine ⟨hh.symm, ?_⟩
  change Apart (gotAddr "memcpy") 8 (stackBelow m0 updateStack) (updateStack + 8) at hs
  unfold Apart at hs ⊢
  rw [stackBelow_toNat (n := updateStack) g.s] at hs
  rw [frm_toNat g]
  change _ ≤ (spAt m0).toNat - 400 ∨
    (spAt m0).toNat - 400 + (400 + 8) ≤ _ at hs
  have := g.s
  omega

/-- The loop environment contains the hasher, frame, and read-only loader slot. -/
theorem wf_head {m0 m : MachineData} [Labels] (hpre : UpdatePreElf m0) (hfr : Frame m0 m)
    {vs : Nat → BitVec 64} {ret : BitVec 64} :
    (Env.ofMachine m [(hAt m0, 344), (frm m0, 120), (gotAddr "memcpy", 8)] vs ret).WF := by
  have g := geo_of hpre
  obtain ⟨hhg, hfg⟩ := got_apart hpre
  have hhf : Apart (hAt m0) 344 (frm m0) 120 := by
    unfold Apart
    rw [frm_toNat g]
    have := g.hs
    have := g.s
    omega
  refine Env.wf_of ⟨⟨fun i hi => hfr.kept _ (hpre.2.2.2.1 i hi), g.h⟩,
    ⟨fun i hi => hfr.kept _ (frm_mapped hpre i hi), ?_⟩,
    ⟨fun i hi => hfr.kept _ ((got_of hpre).mapped (by simp) i hi),
      ((got_of hpre).1 "memcpy" (by simp)).2.1⟩, trivial⟩ ?_
  · show (frm m0).toNat + 120 ≤ _
    rw [frm_toNat g]
    have := g.s8
    have := g.s
    omega
  · apply List.pairwise_cons.mpr
    refine ⟨?_, List.pairwise_pair.mpr hfg⟩
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact hhf
    · exact hhg

/-- `headS` describes a loop state, including the actual loader bytes and RBP target. -/
theorem match_headS {m0 m : MachineData} [Labels] (hpre : UpdatePreElf m0)
    (hfr : Frame m0 m) {vs : Nat → BitVec 64} {ret : BitVec 64} :
    Match (Env.ofMachine m [(hAt m0, 344), (frm m0, 120), (gotAddr "memcpy", 8)] vs ret)
      headS m := by
  have hm := match_ofMachine (m := m)
    (regions := [(hAt m0, 344), (frm m0, 120), (gotAddr "memcpy", 8)])
    (vars := vs) (ret := ret) (sregions := [344, 120, 8])
    (known := [(.r14, .ptr 0 0), (.r13, .ptr 0 200), (.rsp, .ptr 1 8),
      (.rbp, .label "memcpy")])
    (labels := []) (bounds := []) (aliases := [(.gotSlot "memcpy", 2, 0)])
    ⟨rfl, rfl, rfl, trivial⟩
    ⟨hfr.r14.trans (BitVec.add_zero _).symm, hfr.r13.trans rfl,
      hfr.rsp.trans rfl, hfr.rbp, trivial⟩
    trivial trivial ⟨(BitVec.add_zero _).symm, trivial⟩
  apply hm.withKnownBytes (r := 2) (off := 0) (n := 8) (v := .label "memcpy")
  intro i hi
  simp only [Nat.zero_add]
  change m.dmem.get? (gotAddr "memcpy" + BitVec.ofNat 64 i) = _
  rw [got_same hpre hfr hi]
  exact (got_of hpre).byte (l := "memcpy") (by simp) hi

/-! ## Places -/

variable [ElfHost] {sec k : Nat}

theorem hb0 (hp : PlacedIn code sec k) :
    b0.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcX64.Common.Update.b0Offset) :=
  b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb2 (hp : PlacedIn code sec k) :
    b2.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcX64.Common.Update.b2Offset) :=
  b2_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb3 (hp : PlacedIn code sec k) :
    b3.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcX64.Common.Update.b3Offset) :=
  b3_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb4 (hp : PlacedIn code sec k) :
    b4.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcX64.Common.Update.b4Offset) :=
  b4_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb5 (hp : PlacedIn code sec k) :
    b5.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcX64.Common.Update.b5Offset) :=
  b5_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb6 (hp : PlacedIn code sec k) :
    b6.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcX64.Common.Update.b6Offset) :=
  b6_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb7 (hp : PlacedIn code sec k) :
    b7.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcX64.Common.Update.b7Offset) :=
  b7_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb8 (hp : PlacedIn code sec k) :
    b8.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcX64.Common.Update.b8Offset) :=
  b8_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb9 (hp : PlacedIn code sec k) :
    b9.IsInfixAt (ElfHost.sectionProg sec) (k + NativeRustcX64.Common.Update.b9Offset) :=
  b9_in_code.trans hp.1 (List.cons_ne_nil _ _)

theorem lbl_entry (hp : PlacedIn code sec k) :
    Labels.label NativeRustcX64.Common.Update.entryLabel =
      ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b0Offset) :=
  hp.label NativeRustcX64.Common.Update.entry_at
theorem lbl_5 (hp : PlacedIn code sec k) :
    Labels.label NativeRustcX64.Common.Update.label_5 =
      ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b2Offset) :=
  hp.label NativeRustcX64.Common.Update.label_5_at
theorem lbl_1 (hp : PlacedIn code sec k) :
    Labels.label NativeRustcX64.Common.Update.label_1 =
      ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b3Offset) :=
  hp.label NativeRustcX64.Common.Update.label_1_at
theorem lbl_6 (hp : PlacedIn code sec k) :
    Labels.label NativeRustcX64.Common.Update.label_6 =
      ElfHost.addrOf sec (k + NativeRustcX64.Common.Update.b9Offset) :=
  hp.label NativeRustcX64.Common.Update.label_6_at

end

end NativeRustcX64.Hasher.Update
