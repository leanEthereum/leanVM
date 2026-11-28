module

public import NativeRustcArm.Hasher.UpdateInv

/-!
# `Hasher::update`: where things are

The addresses `UpdatePre` places, as numbers (`Geo`, `geo_of`): the hasher, the input and the
256 bytes of stack below SP do not wrap and are apart. What the loop changes (`Chg`) and the frame
miss the input (`input_same`).
-/

namespace NativeRustcArm.Hasher.Update

open NativeRustc NativeRustc.Keccak NativeRustcArm.Sym NativeRustcArm

public section

/-- `UpdatePre`'s addresses as numbers. -/
structure Geo (m0 : MachineData) : Prop where
  h : (hAt m0).toNat + 344 ≤ 2 ^ 64
  d : (dAt m0).toNat + nOf m0 ≤ 2 ^ 64
  s : 256 ≤ (spAt m0).toNat
  al : (spAt m0).toNat % 16 = 0
  hd : (hAt m0).toNat + 344 ≤ (dAt m0).toNat ∨ (dAt m0).toNat + nOf m0 ≤ (hAt m0).toNat
  hs : (hAt m0).toNat + 344 ≤ (spAt m0).toNat - 256 ∨ (spAt m0).toNat ≤ (hAt m0).toNat
  ds : (dAt m0).toNat + nOf m0 ≤ (spAt m0).toNat - 256 ∨ (spAt m0).toNat ≤ (dAt m0).toNat

theorem toNat_sub_ofNat {a : BitVec 64} {j : Nat} (h : j ≤ a.toNat) :
    (a - BitVec.ofNat 64 j).toNat = a.toNat - j := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := a.isLt
  omega

theorem stackBelow_toNat {m : MachineData} {n : Nat} (h : n ≤ m.regs.SP.toNat) :
    (stackBelow m n).toNat = m.regs.SP.toNat - n :=
  toNat_sub_ofNat h

theorem geo_of {m0 : MachineData} [Labels] (hpre : UpdatePre m0) : Geo m0 := by
  obtain ⟨⟨hal, hs, -⟩, -, -, -, hh, -, hd, hhd, hhs, hds, -⟩ := hpre
  have hs' : 256 ≤ m0.regs.SP.toNat := hs
  have hb : (stackBelow m0 updateStack).toNat = m0.regs.SP.toNat - 256 := stackBelow_toNat hs'
  unfold Apart at hhs hds
  rw [hb] at hhs hds
  have e1 : (spAt m0).toNat = m0.regs.SP.toNat := rfl
  have hu : updateStack = 256 := rfl
  refine ⟨hh, hd, hs', hal, hhd, ?_, ?_⟩
  · rw [e1]
    exact hhs.imp id fun h => by unfold hAt; omega
  · rw [e1]
    exact hds.imp id fun h => by unfold dAt; omega

/-- The round constants' place, as numbers. -/
structure GeoRc [Labels] (m0 : MachineData) : Prop where
  nw : rcAddr.toNat + 192 ≤ 2 ^ 64
  rs : rcAddr.toNat + 192 ≤ (spAt m0).toNat - 256 ∨ (spAt m0).toNat ≤ rcAddr.toNat
  hr : (hAt m0).toNat + 344 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ (hAt m0).toNat

theorem geoRc_of {m0 : MachineData} [Labels] (hpre : UpdatePre m0) : GeoRc m0 := by
  obtain ⟨⟨-, hs, -⟩, ⟨-, hnw, hrs⟩, -, -, -, -, -, -, -, -, hhr⟩ := hpre
  have hs' : 256 ≤ m0.regs.SP.toNat := hs
  have hb : (stackBelow m0 updateStack).toNat = m0.regs.SP.toNat - 256 := stackBelow_toNat hs'
  have e1 : (spAt m0).toNat = m0.regs.SP.toNat := rfl
  have hu : updateStack = 256 := rfl
  unfold Apart at hrs
  rw [hb] at hrs
  refine ⟨hnw, ?_, hhr⟩
  rw [e1]
  exact hrs.imp id fun h => by omega

/-- What the loop changes, as numbers. -/
theorem chg_iff {m0 : MachineData} (g : Geo m0) (p : BitVec 64) :
    Chg m0 p ↔ ((hAt m0).toNat ≤ p.toNat ∧ p.toNat < (hAt m0).toNat + 344) ∨
      ((spAt m0).toNat - 256 ≤ p.toNat ∧ p.toNat < (spAt m0).toNat - 64) := by
  have h256 : (spAt m0 - 256#64).toNat = (spAt m0).toNat - 256 := toNat_sub_ofNat g.s
  unfold Chg
  rw [inRange_iff g.h, inRange_iff (by rw [h256]; have := (spAt m0).isLt; omega), h256]
  have := g.s
  omega

/-- The frame, as numbers. -/
theorem frame_iff {m0 : MachineData} (g : Geo m0) (p : BitVec 64) :
    InRange (spAt m0 - 64#64) 64 p ↔
      (spAt m0).toNat - 64 ≤ p.toNat ∧ p.toNat < (spAt m0).toNat := by
  have h64 : (spAt m0 - 64#64).toNat = (spAt m0).toNat - 64 := toNat_sub_ofNat (by have := g.s; omega)
  rw [inRange_iff (by rw [h64]; have := (spAt m0).isLt; omega), h64]
  have := g.s
  omega

/-- The environment of a loop state: the hasher, region 0. -/
theorem wf_head {m0 m1 m : MachineData} [Labels] (hpre : UpdatePre m0) (hfr : Frame m0 m1 m) :
    (Env.ofMachine m [(hAt m0, 344)]).WF :=
  Env.wf_of ⟨⟨fun i hi => hfr.kept _ (hpre.2.2.2.1 i hi), (geo_of hpre).h⟩, trivial⟩
    (List.pairwise_singleton _ _)

/-- `headS` describes a loop state. -/
theorem match_headS {m0 m1 m : MachineData} [Labels] (hfr : Frame m0 m1 m) :
    Match (Env.ofMachine m [(hAt m0, 344)]) headS m := by
  have hb0 : (Env.ofMachine m [(hAt m0, 344)]).base 0 = hAt m0 := Env.base_ofMachine m _ _ rfl
  exact match_ofMachine ⟨rfl, by simp, trivial⟩ rfl
      ⟨by simp only [Sym.eval, hb0, hfr.x20]; simp,
        by simp only [Sym.eval, hb0, hfr.x23]; rfl,
        by simp only [Sym.eval, hfr.x24], trivial⟩
      trivial trivial trivial

/-- **The input is as at the entry** in any state of the loop. -/
theorem input_same {m0 m1 m : MachineData} (g : Geo m0) (hfr : Frame m0 m1 m)
    (h01 : SameOutside m0.dmem m1.dmem (InRange (spAt m0 - 64#64) 64)) {i : Nat}
    (hi : i < nOf m0) :
    m.dmem.get? (dAt m0 + BitVec.ofNat 64 i) = m0.dmem.get? (dAt m0 + BitVec.ofNat 64 i) := by
  have ht := toNat_add_ofNat' (a := dAt m0) (i := i) (by have := g.d; omega)
  rw [hfr.same _ (by rw [chg_iff g, ht]; have := g.hd; have := g.ds; omega),
    h01 _ (by rw [frame_iff g, ht]; have := g.ds; omega)]

/-- **The round constants are as at the entry** in any state of the loop. -/
theorem rc_same {m0 m1 m : MachineData} [Labels] (g : Geo m0) (gr : GeoRc m0) (hfr : Frame m0 m1 m)
    (h01 : SameOutside m0.dmem m1.dmem (InRange (spAt m0 - 64#64) 64)) {i : Nat} (hi : i < 192) :
    m.dmem.get? (rcAddr + BitVec.ofNat 64 i) = m0.dmem.get? (rcAddr + BitVec.ofNat 64 i) := by
  have ht := toNat_add_ofNat' (a := rcAddr) (i := i) (by have := gr.nw; omega)
  rw [hfr.same _ (by rw [chg_iff g, ht]; have := gr.hr; have := gr.rs; omega),
    h01 _ (by rw [frame_iff g, ht]; have := gr.rs; omega)]

end

end NativeRustcArm.Hasher.Update
