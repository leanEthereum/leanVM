import Rv64Verifier.Proofs.Walk.R6N

/-!
# `walk`: a side's start

The block at `0x80001ba4` starts side `σ` from its tuple `(side, lanes, flag, missing)` at
`sp + 2160 + 40 σ`: the lanes to `sp + 1288`, the flag and the missing lane to the closure's
environment, `count`'s base into `s5`, the cell pointers.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FormOk formOf formBuf flushesDeep OptAt)

/-- Before side `σ`'s start: `KM`'s state but the side's words, its tuple at `sp + 2160 + 40 σ`,
`O_M`'s address at `sp + 184`. -/
structure KMb (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q : Word) (B : Nat) (σ : Nat) (F : LayoutMirror.FlushesRust) :
    Prop where
  m : M6 OI s u A k R Q B
  fl : FlAt s u F B
  lens : u.getMem (s.getReg .x2 - 2520) = 6 ∧ u.getMem (s.getReg .x2 - 2504) = 0
  even : ∀ i < 13,
    OptAt u (s.getReg .x2 - 1344 + BitVec.ofNat 64 (32 * i))
      (LayoutMirror.keccakCellLanesAt false i).1 ∧
    OptAt u (s.getReg .x2 - 1344 + BitVec.ofNat 64 (32 * i) + 16)
      (LayoutMirror.keccakCellLanesAt false i).2
  odd : ∀ i < 13,
    OptAt u (s.getReg .x2 - 928 + BitVec.ofNat 64 (32 * i))
      (LayoutMirror.keccakCellLanesAt true i).1 ∧
    OptAt u (s.getReg .x2 - 928 + BitVec.ofNat 64 (32 * i) + 16)
      (LayoutMirror.keccakCellLanesAt true i).2
  p184 : u.getMem (s.getReg .x2 - 2472) = 0xa00001b8
  tside : u.getMem (s.getReg .x2 - 496 + BitVec.ofNat 64 (40 * σ)) = BitVec.ofNat 64 σ
  tlanes : u.getMem (s.getReg .x2 - 496 + BitVec.ofNat 64 (40 * σ) + 8) =
    BitVec.ofNat 64 (sideLanes σ)
  tflag : u.getMem (s.getReg .x2 - 496 + BitVec.ofNat 64 (40 * σ) + 16) = BitVec.ofNat 64 (10 + σ)
  tmissing : OptAt u (s.getReg .x2 - 496 + BitVec.ofNat 64 (40 * σ) + 24) (sideMissing σ)
  next : σ = 0 → u.getMem (s.getReg .x2 - 456) = 1 ∧ u.getMem (s.getReg .x2 - 448) = 40 ∧
    u.getMem (s.getReg .x2 - 440) = 11 ∧ u.getMem (s.getReg .x2 - 432) = 0

/-- Side 0 done: side 1's start. -/
theorem KM.toKMb {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {F : LayoutMirror.FlushesRust}
    (hpre : WalkPre s) (h : KM OI s u A k R Q B 0 F) : KMb OI s u A k R Q B 1 F := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨n1, n2, n3, n4, n5⟩ := h.next rfl
  have a0 : s.getReg .x2 - 496 + BitVec.ofNat 64 (40 * 1) = s.getReg .x2 - 456 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a8 : s.getReg .x2 - 456 + 8 = s.getReg .x2 - 448 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a16 : s.getReg .x2 - 456 + 16 = s.getReg .x2 - 440 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a24 : s.getReg .x2 - 456 + 24 = s.getReg .x2 - 432 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  exact {
    m := h.m, fl := h.fl, lens := h.lens, even := h.even, odd := h.odd
    p184 := n1
    tside := by rw [a0]; exact n2
    tlanes := by rw [a0, a8]; exact n3
    tflag := by rw [a0, a16]; exact n4
    tmissing := by rw [a0, a24]; exact n5
    next := fun h ↦ absurd h (by decide) }

theorem optMove {u t : MachineState} {a b : Word} {o : Option Nat} (h : OptAt u a o)
    (h0 : t.getMem b = u.getMem a) (h8 : t.getMem (b + 8) = u.getMem (a + 8)) : OptAt t b o := by
  cases o with
  | none => simp only [OptAt] at h ⊢; rw [h0]; exact h
  | some x => simp only [OptAt] at h ⊢; rw [h0, h8]; exact h

set_option maxRecDepth 8192 in
/-- Side `σ`'s start: its tuple read, the side's words written, to the loop's head at cell 0. -/
theorem sideStart {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {σ : Nat} {F : LayoutMirror.FlushesRust}
    (hpre : WalkPre s) (h : KMb OI s u A k R Q B σ F) (hσ : σ < 2) (hpc : u.pc = 0x80001ba4)
    (x10 : u.getReg .x10 = BitVec.ofNat 64 σ) (x15 : u.getReg .x15 = BitVec.ofNat 64 σ)
    (x8 : u.getReg .x8 = s.getReg .x2 - 200) (x18 : u.getReg .x18 = 13)
    (x20 : u.getReg .x20 = s.getReg .x2 - 176) (x25 : u.getReg .x25 = s.getReg .x2 - 272)
    (x26 : u.getReg .x26 = s.getReg .x2 - 512) :
    ∃ t, Reaches Image.code u t ∧ t.pc = 0x80001d74 ∧ KM OI s t A k R Q B σ F ∧ KR s t σ 0 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := h.m.inv.sp
  have hT : BitVec.ofNat 64 σ * 32 + BitVec.ofNat 64 σ * 8 = BitVec.ofNat 64 (40 * σ) := by
    rcases (show σ = 0 ∨ σ = 1 by omega) with rfl | rfl <;> rfl
  obtain ⟨t, rt, g⟩ := Sym.BlockSpec.reaches b80001ba4_spec hpc (by
    rv_eval [sp, x10, x26]
    rw [hT]
    and_intros
    all_goals first
      | valid_access hval [hb1, hσ]
      | (intro he; have := congrArg BitVec.toNat he; addr_omega [hb1, hσ, this]))
  have fr : Rv64Verifier.Layout.DFrame u t fun a ↦ Within a (s.getReg .x2 - 1368) 8 ∨
      Within a (s.getReg .x2 - 2456) 8 ∨ Within a (s.getReg .x2 - 296) 8 ∨
      Within a (s.getReg .x2 - 272) 8 ∨ Within a (s.getReg .x2 - 248) 16 := Expect.ldframe g (by
    rv_eval [sp, x10, x26]
    simp only [Within]
    and_intros <;> addr_omega [hb1])
  have kt := b80001ba4_keeps g
  have keep (y : Word) (hy : (s.getReg .x2 - 2656).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 2456).toNat ∨
      (s.getReg .x2 - 2448).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 1368).toNat ∨
      (s.getReg .x2 - 1360).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 296).toNat ∨
      (s.getReg .x2 - 288).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 272).toNat ∨
      (s.getReg .x2 - 264).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 248).toNat ∨
      (s.getReg .x2 - 232).toNat ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2 - 104).toNat ∨
      y.toNat + 8 ≤ (s.getReg .x2 - 2656).toNat) : t.getMem y = u.getMem y :=
    fr y (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw | hw | hw | hw <;> addr_omega [hx, hw, hy, hb1])
      (by addr_omega [hy, hb1])
  have hn : heapNext t = heapNext u := by
    simp only [heapNext]; rw [keep _ (by addr_omega [hb1])]
  have hh := h.m.inv.heap
  have M := h.m.step hpre (fr.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha
      · exact Or.inl (by simp only [Within] at ha ⊢; addr_omega [ha, hb1])
      · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr ha))))
      · exact Or.inl (by simp only [Within] at ha ⊢; addr_omega [ha, hb1])
      · exact Or.inl (by simp only [Within] at ha ⊢; addr_omega [ha, hb1])
      · exact Or.inl (by simp only [Within] at ha ⊢; addr_omega [ha, hb1]))
    ⟨hn ▸ hh.lo, hn ▸ hh.hi⟩ hn.ge (kt .x2 (by decide))
  have FL := h.fl.frame hpre fr (fun x hx hw ↦ by
      simp only [Within] at hx hw; rcases hw with hw | hw | hw | hw | hw <;> addr_omega [hx, hw, hb1])
    (fun x hx hw ↦ by
      have := (h.fl.ok.deep_below hx).2; have hu := hh.hi
      simp only [heapEnd, heapNext] at this hu
      simp only [Within] at hw; rcases hw with hw | hw | hw | hw | hw <;> addr_omega [hw, this, hu, hb1])
    hh hn.ge
  have e (N M : Word) (hNM : N.toNat + M.toNat = 2656) : u.getReg .x2 + N = s.getReg .x2 - M :=
    spAdd hpre sp hNM
  have e26 (N M : Word) (hNM : N.toNat + M.toNat = 512) : u.getReg .x26 + N = s.getReg .x2 - M := by
    rw [x26]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hNM]
  have Tu : u.getReg .x2 + 2160 + (u.getReg .x10 * 32 + u.getReg .x10 * 8) =
      s.getReg .x2 - 496 + BitVec.ofNat 64 (40 * σ) := by
    rw [x10, hT, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hσ]
  have t0 : u.getMem (u.getReg .x2 + 2160 + (u.getReg .x10 * 32 + u.getReg .x10 * 8)) =
      BitVec.ofNat 64 σ := by rw [Tu]; exact h.tside
  have T8 : u.getReg .x2 + 2160 + (u.getReg .x10 * 32 + u.getReg .x10 * 8) + 8 =
      s.getReg .x2 - 496 + BitVec.ofNat 64 (40 * σ) + 8 := by rw [Tu]
  have T16 : u.getReg .x2 + 2160 + (u.getReg .x10 * 32 + u.getReg .x10 * 8) + 16 =
      s.getReg .x2 - 496 + BitVec.ofNat 64 (40 * σ) + 16 := by rw [Tu]
  have T24 : u.getReg .x2 + 2160 + (u.getReg .x10 * 32 + u.getReg .x10 * 8) + 24 =
      s.getReg .x2 - 496 + BitVec.ofNat 64 (40 * σ) + 24 := by rw [Tu]
  have T32 : u.getReg .x2 + 2160 + (u.getReg .x10 * 32 + u.getReg .x10 * 8) + 32 =
      s.getReg .x2 - 496 + BitVec.ofNat 64 (40 * σ) + 24 + 8 := by
    rw [Tu]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hσ]
  refine ⟨t, rt, b80001ba4_pc g, {
    m := M
    fl := FL.1
    lens := by rw [keep _ (by addr_omega [hb1]), keep _ (by addr_omega [hb1])]; exact h.lens
    even := fun i hi ↦ ⟨OptAt.congr (h.even i hi).1 (keep _ (by addr_omega [hb1, hi]))
        (keep _ (by addr_omega [hb1, hi])),
      OptAt.congr (h.even i hi).2 (keep _ (by addr_omega [hb1, hi])) (keep _ (by addr_omega [hb1, hi]))⟩
    odd := fun i hi ↦ ⟨OptAt.congr (h.odd i hi).1 (keep _ (by addr_omega [hb1, hi]))
        (keep _ (by addr_omega [hb1, hi])),
      OptAt.congr (h.odd i hi).2 (keep _ (by addr_omega [hb1, hi])) (keep _ (by addr_omega [hb1, hi]))⟩
    side := by rw [← e 200 2456 (by decide), b80001ba4_m_x2_200 g, x15]
    lanes := by rw [← e 1288 1368 (by decide), b80001ba4_m_x2_1288 g, T8]; exact h.tlanes
    lanesPtr := by rw [← e26 240 272 (by decide), b80001ba4_m_x26_240 g, e 1288 1368 (by decide)]
    flag := by rw [← e26 216 296 (by decide), b80001ba4_m_x26_216 g, T16]; exact h.tflag
    missing := optMove h.tmissing (by rw [← e26 264 248 (by decide), b80001ba4_m_x26_264 g, T24])
      (by rw [show s.getReg .x2 - 248 + 8 = u.getReg .x26 + 272 by
            rw [x26]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
          b80001ba4_m_x26_272 g, T32])
    next := fun hσ0 ↦ by
      obtain ⟨n1, n2, n3, n4⟩ := h.next hσ0
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [keep _ (by addr_omega [hb1])]
      · exact h.p184
      · exact n1
      · exact n2
      · exact n3
      · exact n4 }, {
    x8 := by rw [kt .x8 (by decide)]; exact x8
    x9 := by rw [b80001ba4_x9 g, e 1744 912 (by decide)]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    x18 := by rw [kt .x18 (by decide)]; exact x18
    x19 := by rw [b80001ba4_x19 g, e 1328 1328 (by decide)]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    x20 := by rw [kt .x20 (by decide)]; exact x20
    x21 := by
      rw [b80001ba4_x21 g, t0, x18]
      rcases (show σ = 0 ∨ σ = 1 by omega) with rfl | rfl <;> rfl
    x22 := by
      rw [b80001ba4_x22 g, e 184 2472 (by decide), h.p184]; apply BitVec.eq_of_toNat_eq
      have ha : (0xa00001b8 : Word).toNat = 0xa00001b8 := rfl
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, ha]
    x23 := by rw [b80001ba4_x23 g]; rfl
    x25 := by rw [kt .x25 (by decide)]; exact x25
    x26 := by rw [kt .x26 (by decide)]; exact x26
    x27 := (b80001ba4_x27 g).trans t0 }⟩

end Rv64Verifier.Proofs.Walk
