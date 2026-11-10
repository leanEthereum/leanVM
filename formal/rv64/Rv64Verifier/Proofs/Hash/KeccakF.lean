import Rv64Verifier.Proofs.Hash.KeccakFChecks
import Rv64Verifier.Proofs.Hash.Bytes

/-!
# `verifier::hash::keccak_f`

compiled at `0x80004210` (`Blocks/F5.lean`): `0x80004210` makes a 640-byte frame and calls
`memcpy` to copy `KECCAK_RC` to `sp + 144` (`sp` the frame's); `0x80004264` loads the lanes into
the loop head's registers and slots (`hd`). The loop body is one round: θ (`0x800042e4`) writes
the lanes back; `0x800044e4` stores `KECCAK_RC[k]` at `sp + 112` and calls `memset` to clear `b`
at `sp + 336`; ρ and π (`0x80004528`, 25 iterations) fill `b`; χ and ι (`0x80004564`, then the
branch at `0x800047d8`) write the lanes and the loop head's registers. `0x800047dc` returns.

The proof: `setup`, then `round` 24 times by `Reaches.loop` with `Head`, then `exit`. Every
block's side conditions come from `oblig_all` (regions: the lanes, the slots `sp .. sp + 128`,
`b`), and its lanes from the kernel checks of `KeccakFChecks.lean`.
-/

namespace Rv64Verifier.Hash.KeccakF
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.Blocks.F5 Rv64Verifier.Contracts
  Rv64Verifier.Model

/-! ## Invariants -/

/-- The lanes `keccak_f` is given. -/
def lanesIn (s : MachineState) : List Word := s.readWords (s.getReg .x10) 25

/-- The callee-saved registers as the prologue saves them, from `sp - 104`. -/
def savedRegs (s : MachineState) : List Word :=
  [s.getReg .x27, s.getReg .x26, s.getReg .x25, s.getReg .x24, s.getReg .x23, s.getReg .x22,
    s.getReg .x21, s.getReg .x20, s.getReg .x19, s.getReg .x18, s.getReg .x9, s.getReg .x8,
    s.getReg .x1]

/-- What the loop keeps: the round constants at `sp + 144`, the saved registers, and memory
outside the lanes and the stack. -/
structure Common (s t : MachineState) : Prop where
  rc : t.readWords (s.getReg .x2 - 496) 24 = keccakRCRust
  saved : t.readWords (s.getReg .x2 - 104) 13 = savedRegs s
  frame : ∀ a, ¬ Within a (s.getReg .x10) 200 → ¬ Within a (stackLo s keccakFStack) keccakFStack →
    t.getMem a = s.getMem a

/-- The loop head, after `k` rounds. -/
structure Head (s t : MachineState) (k : Nat) : Prop extends Common s t where
  pc : t.pc = 0x800042e4
  lt : k < 24
  sp : t.getReg .x2 = s.getReg .x2 - 640
  x8 : t.getReg .x8 = s.getReg .x10
  x25 : t.getReg .x25 = BitVec.ofNat 64 k
  lanes : ∀ j, (hd j).eval t = (rounds (lanesIn s) k).getD j 0
  mem : t.readWords (s.getReg .x10) 25 = rounds (lanesIn s) k

/-- After the last round, at the epilogue. -/
structure Exit (s t : MachineState) : Prop extends Common s t where
  pc : t.pc = 0x800047dc
  sp : t.getReg .x2 = s.getReg .x2 - 640
  mem : t.readWords (s.getReg .x10) 25 = keccakFRust (lanesIn s)

/-- Memory outside the lanes, `sp .. sp + 128` with the 16 bytes below, and `b`. -/
def RoundFrame (s t u : MachineState) : Prop :=
  ∀ a, ¬ Within a (s.getReg .x10) 200 → ¬ Within a (s.getReg .x2 - 656) 144 →
    Apart a 8 (s.getReg .x2 - 304) 200 → u.getMem a = t.getMem a

/-! ## Bounds -/

structure Bounds (s : MachineState) : Prop where
  sp : 0x20 + 656 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
    (s.getReg .x2).toNat % 16 = 0
  st : 0x20 ≤ (s.getReg .x10).toNat ∧ (s.getReg .x10).toNat % 8 = 0 ∧
    (s.getReg .x10).toNat + 200 ≤ 0xc0000008
  apart : Apart (s.getReg .x10) 200 (s.getReg .x2 - 656) 656
  tables : Apart keccakTablesAddr keccakTablesSize (s.getReg .x2 - 656) 656
  tablesSt : Apart keccakTablesAddr keccakTablesSize (s.getReg .x10) 200

theorem _root_.Rv64Verifier.Contracts.KeccakFPre.bounds {s : MachineState} (h : KeccakFPre s) : Bounds s := by
  have hs := h.stack.bounds (by decide) (by decide)
  have hst := ValidMemRange.bounds h.state (by decide)
  have ha := h.stateStack
  have ht := h.tablesStack
  refine ⟨?_, ⟨hst.1, hst.2.1, by omega⟩, ?_, ?_, h.tablesState⟩
  · simp only [keccakFStack, memStack] at hs; omega
  · simp only [stackLo, keccakFStack, memStack] at ha ⊢; exact ha
  · simp only [stackLo, keccakFStack, memStack] at ht ⊢; exact ht

theorem Common.of_frame {s t u : MachineState} (hb : Bounds s) (hc : Common s t)
    (hf : RoundFrame s t u) : Common s u where
  rc := by
    rw [← hc.rc]
    apply readWords_congr
    intro i hi
    have := hb.sp; have := hb.apart
    exact hf _ (by addr_omega [hb.sp, hb.st, hb.apart, hi]) (by addr_omega [hb.sp, hb.apart, hb.st, hi])
      (by addr_omega [hb.sp, hb.apart, hb.st, hi])
  saved := by
    rw [← hc.saved]
    apply readWords_congr
    intro i hi
    exact hf _ (by addr_omega [hb.sp, hb.st, hb.apart, hi]) (by addr_omega [hb.sp, hb.apart, hb.st, hi])
      (by addr_omega [hb.sp, hb.apart, hb.st, hi])
  frame a h₁ h₂ := by
    rw [← hc.frame a h₁ h₂]
    exact hf a h₁ (by addr_omega [h₂, hb.apart, hb.st, hb.sp]) (by addr_omega [h₂, hb.apart, hb.st, hb.sp])

theorem RoundFrame.trans {s t u v : MachineState} (h₁ : RoundFrame s t u) (h₂ : RoundFrame s u v) :
    RoundFrame s t v :=
  fun a ha hb hc ↦ (h₂ a ha hb hc).trans (h₁ a ha hb hc)

/-! ## Regions -/

theorem stateR_start (t : MachineState) : stateR.start t = t.getReg .x8 := BitVec.add_zero _
theorem slotsR_start (t : MachineState) : slotsR.start t = t.getReg .x2 := BitVec.add_zero _
theorem bR_start (t : MachineState) : bR.start t = t.getReg .x2 + 336 := rfl
theorem rcR_start (t : MachineState) : rcR.start t = t.getReg .x10 := BitVec.add_zero _
theorem stateR_n : stateR.n = 25 := rfl
theorem slotsR_n : slotsR.n = 16 := rfl
theorem bR_n : bR.n = 25 := rfl
theorem rcR_n : rcR.n = 1 := rfl

theorem regionsApart_two {t : MachineState} {R₁ R₂ : Region}
    (h : Apart (R₁.start t) (8 * R₁.n) (R₂.start t) (8 * R₂.n)) : RegionsApart t [R₁, R₂] :=
  List.pairwise_cons.mpr ⟨fun R hR ↦ by
    simp only [List.mem_singleton] at hR; subst hR; exact h, List.pairwise_singleton _ _⟩

theorem regionsApart_three {t : MachineState} {R₁ R₂ R₃ : Region}
    (h₁₂ : Apart (R₁.start t) (8 * R₁.n) (R₂.start t) (8 * R₂.n))
    (h₁₃ : Apart (R₁.start t) (8 * R₁.n) (R₃.start t) (8 * R₃.n))
    (h₂₃ : Apart (R₂.start t) (8 * R₂.n) (R₃.start t) (8 * R₃.n)) :
    RegionsApart t [R₁, R₂, R₃] :=
  List.pairwise_cons.mpr ⟨fun R hR ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact h₁₂
    · exact h₁₃, regionsApart_two h₂₃⟩

theorem regionsOk_two {t : MachineState} {R₁ R₂ : Region} (h₁ : ValidMemRange (R₁.start t) R₁.n)
    (h₂ : ValidMemRange (R₂.start t) R₂.n) : RegionsOk t [R₁, R₂] := by
  intro R hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl
  · exact h₁
  · exact h₂

theorem regionsOk_three {t : MachineState} {R₁ R₂ R₃ : Region}
    (h₁ : ValidMemRange (R₁.start t) R₁.n) (h₂ : ValidMemRange (R₂.start t) R₂.n)
    (h₃ : ValidMemRange (R₃.start t) R₃.n) : RegionsOk t [R₁, R₂, R₃] := by
  intro R hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl
  · exact h₁
  · exact h₂
  · exact h₃

/-- A part of `keccak_f`'s stack is valid. -/
theorem stack_sub {s : MachineState} (hpre : KeccakFPre s) {b : Word} {m : Nat}
    (h1 : (s.getReg .x2).toNat - 656 ≤ b.toNat) (h2 : b.toNat + 8 * m ≤ (s.getReg .x2).toNat)
    (h3 : b.toNat % 8 = 0) : ValidMemRange b m := by
  have hb := hpre.bounds
  refine ValidMemRange.sub hpre.stack.valid ?_ ?_ ?_ <;> addr_omega [hb.sp, hb.apart, hb.st, h1, h2, h3]

/-! ## θ -/

theorem thetaRust_getD {L : List Word} (hL : L.length = 25) {i : Nat} (hi : i < 25) :
    (thetaRust L).getD i 0 = theta (fun j ↦ L.getD j 0) i := by
  rw [thetaRust_eq hL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

/-- At `memset`'s call in round `k`: the lanes after θ, the round constant and `k` in their
slots, `memset`'s arguments. -/
structure AtMemset (s t : MachineState) (k : Nat) : Prop where
  pc : t.pc = 0x800126f4
  ra : t.getReg .x1 = 0x8000450c
  sp : t.getReg .x2 = s.getReg .x2 - 640
  x8 : t.getReg .x8 = s.getReg .x10
  x10 : t.getReg .x10 = s.getReg .x2 - 304
  x11 : t.getReg .x11 = 0
  x12 : t.getReg .x12 = 200
  kslot : t.getMem (s.getReg .x2 - 552) = BitVec.ofNat 64 k
  rc : t.getMem (s.getReg .x2 - 528) = keccakRCRust.getD k 0
  mem : t.readWords (s.getReg .x10) 25 = thetaRust (rounds (lanesIn s) k)

theorem key_eval (t : MachineState) (r : Reg) (off : Nat) :
    (key r off).eval t = t.getReg r + BitVec.ofNat 64 off := rfl

theorem theta_step {s t : MachineState} (hpre : KeccakFPre s) {k : Nat} (ht : Head s t k) :
    ∃ u, Reaches Image.code t u ∧ RoundFrame s t u ∧ AtMemset s u k := by
  have hb := hpre.bounds
  have hk := ht.lt
  have hL : (rounds (lanesIn s) k).length = 25 := length_rounds (readWords_length _ _ _) k
  have hlanes : (fun j ↦ (hd j).eval t) = fun j ↦ (rounds (lanesIn s) k).getD j 0 :=
    funext ht.lanes
  -- θ
  have hok₁ : RegionsOk t [stateR, slotsR] := regionsOk_two
    (by rw [stateR_start, ht.x8]; exact hpre.state)
    (by rw [slotsR_start, slotsR_n, ht.sp]; refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp, hb.apart, hb.st])
  have hap₁ : RegionsApart t [stateR, slotsR] := regionsApart_two
    (by rw [stateR_start, slotsR_start, stateR_n, slotsR_n, ht.x8, ht.sp]; addr_omega [hb.apart, hb.st, hb.sp])
  obtain ⟨u₁, hr₁, h₁⟩ := BlockSpec.reaches b800042e4_spec ht.pc
    (oblig_all hok₁ hap₁ (bs := []) (fun _ h ↦ by cases h) (extra := []) trivial theta_obl)
  have k₁ := b800042e4_keeps h₁
  have hθ (i : Nat) (hi : i < 22) : u₁.getMem (s.getReg .x10 + BitVec.ofNat 64 (8 * i)) =
      (thetaRust (rounds (lanesIn s) k)).getD i 0 := by
    have := h₁.mem_of_ok (List.all_eq_true.mp theta_mem i (List.mem_range.mpr hi))
    rw [thetaE_eval, hlanes, key_eval, ht.x8] at this
    rw [this, thetaRust_getD hL (by omega)]
  have hθreg (r : Reg) (i : Nat) (hi : i < 25) (hr : regOk b800042e4 r (thetaE hd i) = true) :
      u₁.getReg r = (thetaRust (rounds (lanesIn s) k)).getD i 0 := by
    rw [h₁.reg_of_ok hr, thetaE_eval, hlanes, thetaRust_getD hL hi]
  have hx11 := hθreg .x11 22 (by decide) (by
    have := theta_regs; simp only [Bool.and_eq_true] at this; exact this.1.1)
  have hx5 := hθreg .x5 23 (by decide) (by
    have := theta_regs; simp only [Bool.and_eq_true] at this; exact this.1.2)
  have hx16 := hθreg .x16 24 (by decide) (by
    have := theta_regs; simp only [Bool.and_eq_true] at this; exact this.2)
  have hu₁2 : u₁.getReg .x2 = s.getReg .x2 - 640 := (k₁ .x2 (by decide)).trans ht.sp
  have hu₁8 : u₁.getReg .x8 = s.getReg .x10 := (k₁ .x8 (by decide)).trans ht.x8
  have hu₁10 := b800042e4_x10 h₁
  rw [ht.sp, ht.x25] at hu₁10
  have hk₁ := b800042e4_m_x2_88 h₁
  rw [ht.sp, ht.x25] at hk₁
  have hfr₁ (a : Word) (h₁a : ¬ Within a (s.getReg .x10) 200)
      (h₂a : ¬ Within a (s.getReg .x2 - 640) 128) : u₁.getMem a = t.getMem a :=
    h₁.frame_regions hok₁ theta_writes a (by
      intro R hR
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl
      · rw [stateR_start, ht.x8]; exact h₁a
      · rw [slotsR_start, ht.sp]; exact h₂a)
  -- the round constant, and `memset`'s call
  have hok₂ : RegionsOk u₁ [stateR, slotsR, rcR] := regionsOk_three
    (by rw [stateR_start, hu₁8]; exact hpre.state)
    (by rw [slotsR_start, slotsR_n, hu₁2]; refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp, hb.apart, hb.st])
    (by
      rw [rcR_start, rcR_n, hu₁10]
      refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp, hb.apart, hb.st, hk])
  have hap₂ : RegionsApart u₁ [stateR, slotsR, rcR] := regionsApart_three
    (by rw [stateR_start, slotsR_start, stateR_n, slotsR_n, hu₁8, hu₁2]; addr_omega [hb.apart, hb.st, hb.sp])
    (by
      rw [stateR_start, rcR_start, stateR_n, rcR_n, hu₁8, hu₁10]; addr_omega [hb.apart, hb.st, hb.sp, hk])
    (by
      rw [slotsR_start, rcR_start, slotsR_n, rcR_n, hu₁2, hu₁10]; addr_omega [hb.sp, hb.apart, hb.st, hk])
  obtain ⟨u₂, hr₂, h₂⟩ := BlockSpec.reaches b800044e4_spec (b800042e4_pc h₁)
    (oblig_all hok₂ hap₂ (bs := []) (fun _ h ↦ by cases h) (extra := []) trivial rc_obl)
  have k₂ := b800044e4_keeps h₂
  have hu₂2 : u₂.getReg .x2 = s.getReg .x2 - 640 := (k₂ .x2 (by decide)).trans hu₁2
  have hu₂8 : u₂.getReg .x8 = s.getReg .x10 := (k₂ .x8 (by decide)).trans hu₁8
  have hfr₂ (a : Word) (h₁a : ¬ Within a (s.getReg .x10) 200)
      (h₂a : ¬ Within a (s.getReg .x2 - 640) 128) : u₂.getMem a = u₁.getMem a :=
    h₂.frame_regions (by
      intro R hR
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl
      · exact hok₂ _ (by simp)
      · exact hok₂ _ (by simp)) rc_writes a (by
      intro R hR
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl
      · rw [stateR_start, hu₁8]; exact h₁a
      · rw [slotsR_start, hu₁2]; exact h₂a)
  have hrc : u₁.getMem (u₁.getReg .x10) = keccakRCRust.getD k 0 := by
    rw [hu₁10, hfr₁ _ (by addr_omega [hb.sp, hb.st, hb.apart, hk]) (by addr_omega [hb.sp, hb.apart, hb.st, hk]),
      ← ht.rc, readWords_getD _ _ _ _ hk]
    congr 1
    addr_omega [hb.sp, hb.apart, hb.st, hk]
  refine ⟨u₂, hr₁.trans hr₂, ?_, ?_⟩
  · intro a h₁a h₂a _
    rw [hfr₂ a h₁a (by addr_omega [h₂a, hb.apart, hb.st, hb.sp]), hfr₁ a h₁a (by addr_omega [h₂a, hb.apart, hb.st, hb.sp])]
  refine ⟨b800044e4_pc h₂, b800044e4_x1 h₂, hu₂2, hu₂8, ?_, b800044e4_x11 h₂, b800044e4_x12 h₂,
    ?_, ?_, ?_⟩
  · rw [b800044e4_x10 h₂, hu₁2]; addr_omega [hb.sp, hb.apart, hb.st]
  · have hw := h₂.frame (s.getReg .x2 - 552) (by
      rv_eval [hu₁8, hu₁2]
      and_intros <;> addr_omega [hb.sp, hb.st, hb.apart])
    rw [hw, ← hk₁]
    congr 1
    addr_omega [hb.sp, hb.apart, hb.st]
  · have := b800044e4_m_x2_112 h₂
    rw [hrc, hu₁2] at this
    rw [← this]
    congr 1
    addr_omega [hb.sp, hb.apart, hb.st]
  · apply readWords_eq (length_thetaRust hL)
    intro i hi
    by_cases h22 : i < 22
    · rw [← hθ i h22]
      apply h₂.frame
      rv_eval [hu₁8, hu₁2]
      and_intros <;> addr_omega [hb.sp, hb.st, hb.apart, h22]
    · have hm (off : Nat) (hoff : off = 8 * i) (r : Reg) (j : Nat) (hj : j = i)
          (hr : u₂.getMem (u₁.getReg .x8 + BitVec.ofNat 64 off) = u₁.getReg r)
          (hv : u₁.getReg r = (thetaRust (rounds (lanesIn s) k)).getD j 0) :
          u₂.getMem (s.getReg .x10 + BitVec.ofNat 64 (8 * i)) =
            (thetaRust (rounds (lanesIn s) k)).getD i 0 := by
        rw [← hoff, ← hu₁8, hr, hv, hj]
      have : i = 22 ∨ i = 23 ∨ i = 24 := by omega
      rcases this with rfl | rfl | rfl
      · exact hm 176 rfl .x11 22 rfl (b800044e4_m_x8_176 h₂) hx11
      · exact hm 184 rfl .x5 23 rfl (b800044e4_m_x8_184 h₂) hx5
      · exact hm 192 rfl .x16 24 rfl (b800044e4_m_x8_192 h₂) hx16

/-! ## `memset` and ρ, π -/

/-- The tables, where `KeccakTables` puts them. -/
theorem tables_frame {s t : MachineState} (hb : Bounds s) (ht : KeccakTables s)
    (hf : ∀ a, ¬ Within a (s.getReg .x10) 200 →
      ¬ Within a (stackLo s keccakFStack) keccakFStack → t.getMem a = s.getMem a) :
    KeccakTables t := by
  unfold KeccakTables at ht ⊢
  rw [← ht]
  apply readWords_congr
  intro i hi
  exact hf _ (by addr_omega [hb.tablesSt, hi]) (by addr_omega [hb.sp, hb.st, hb.apart, hb.tables, hi])

theorem table_get {t : MachineState} (h : KeccakTables t) {i : Nat} (hi : i < 62) :
    t.getMem (keccakTablesAddr + BitVec.ofNat 64 (8 * i)) = keccakTableWords.getD i 0 := by
  rw [← readWords_getD _ _ _ _ hi, h]

theorem pi_get {t : MachineState} (h : KeccakTables t) {i : Nat} (hi : i < 25) :
    t.getMem (0xa00005b8 + BitVec.ofNat 64 (8 * i)) = BitVec.ofNat 64 (keccakPiRust.getD i 0) ∧
      keccakPiRust.getD i 0 < 25 := by
  have hp := List.all_eq_true.mp pi_table i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  refine ⟨?_, hp.2⟩
  rw [← hp.1, ← table_get h (by omega)]
  congr 1
  addr_omega [hi]

theorem rho_get {t : MachineState} (h : KeccakTables t) {i : Nat} (hi : i < 25) :
    (rhoE i).eval t = BitVec.ofNat 64 (keccakRhoRust.getD i 0) ∧ keccakRhoRust.getD i 0 < 64 := by
  have hp := List.all_eq_true.mp rho_table i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  refine ⟨?_, hp.2⟩
  simp only [rhoE, E.eval, UnOp.eval, LoadKind.fromWord]
  rw [hp.1.1, table_get h (by omega), hp.1.2]

/-- `slli`, `srli` by the negated amount and `or`: a rotation. -/
theorem rot_eval (x : Word) {n : Nat} (hn : n < 64) :
    x <<< ((BitVec.ofNat 64 n).toNat % 64) ||| x >>> ((0 - BitVec.ofNat 64 n).toNat % 64) =
      x.rotateLeft n := by
  by_cases h0 : n = 0
  · subst h0
    have : x >>> 64 = 0 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      rw [Nat.div_eq_of_lt x.isLt]
      rfl
    simp [BitVec.rotateLeft_def, this]
  · have h1 : (BitVec.ofNat 64 n).toNat % 64 = n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), Nat.mod_eq_of_lt hn]
    have h2 : (0 - BitVec.ofNat 64 n).toNat % 64 = 64 - n := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]
      have : (0 : Word).toNat = 0 := rfl
      omega
    rw [h1, h2, BitVec.rotateLeft_def, Nat.mod_eq_of_lt hn]

/-- In the ρ and π loop, before iteration `i`. -/
structure PiInv (s v w : MachineState) (A : List Word) (i : Nat) : Prop where
  le : i ≤ 25
  pc : w.pc = if i < 25 then 0x80004528 else 0x80004564
  sp : w.getReg .x2 = s.getReg .x2 - 640
  x8 : w.getReg .x8 = s.getReg .x10
  x10 : w.getReg .x10 = 0xa00005b8
  x11 : w.getReg .x11 = rhoAddr i
  x12 : w.getReg .x12 = s.getReg .x10 + BitVec.ofNat 64 (8 * i)
  x13 : w.getReg .x13 = 0xa00005b8 + BitVec.ofNat 64 (8 * i)
  x17 : w.getReg .x17 = s.getReg .x2 - 304
  b : w.readWords (s.getReg .x2 - 304) 25 = (List.range i).foldl (rhoPiStep A) (List.replicate 25 0)
  frame : ∀ a, Apart a 8 (s.getReg .x2 - 304) 200 → w.getMem a = v.getMem a

theorem pi_hsub : CodeSub (codeWindow Image.code 4426 15) Image.code :=
  codeWindow_sub _ _ _ (by decide)

theorem foldl_range_succ {α : Type} (f : α → Nat → α) (a : α) (n : Nat) :
    (List.range (n + 1)).foldl f a = f ((List.range n).foldl f a) n := by
  rw [List.range_succ, List.foldl_append]
  rfl

theorem pi_step {s v w : MachineState} (hpre : KeccakFPre s) (hv : KeccakTables v)
    {A : List Word} (hA : v.readWords (s.getReg .x10) 25 = A) {i : Nat} (hi : i < 25)
    (hw : PiInv s v w A i) : ∃ w', Reaches Image.code w w' ∧ PiInv s v w' A (i + 1) := by
  have hb := hpre.bounds
  have htw : KeccakTables w := by
    unfold KeccakTables at hv ⊢
    rw [← hv]
    apply readWords_congr
    intro j hj
    exact hw.frame _ (by addr_omega [hb.sp, hb.st, hb.apart, hb.tables, hj])
  have hpc : w.pc = 0x80004528 := by rw [hw.pc]; simp [hi]
  obtain ⟨hpi, hpi25⟩ := pi_get htw hi
  obtain ⟨hrho, hrho64⟩ := rho_get htw hi
  have h3 : ((3 : Word).toNat % 64) = 3 := rfl
  have hkey : piKey.eval w = s.getReg .x2 - 304 + BitVec.ofNat 64 (8 * keccakPiRust.getD i 0) := by
    simp only [piKey, Addr.eval, E.eval, BinOp.eval, h3, hw.x17, hw.x13, hpi, Sym.add_zero_lit,
      Sym.shiftLeft_eq_mul]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega
  obtain ⟨w', hst, h⟩ := run_spec (cfg := cfg) (rs := [])
    (List.all_eq_true.mp pi_run i (List.mem_range.mpr hi)) pi_hsub
    (s := w) (u := w) (by rw [← hpc]; exact withConsts_toState _ (by simp [hw.x11]))
    (fun _ h ↦ by cases h) List.Pairwise.nil (fun _ h ↦ by cases h) (by
      show Oblig.all w [Oblig.valid piKey 8, Oblig.valid ⟨some (.reg .x13), 0⟩ 8,
        Oblig.valid ⟨some (.reg .x12), 0⟩ 8]
      simp only [Oblig.all, Oblig.holds]
      refine ⟨?_, ?_, ?_⟩
      · rw [hkey]
        valid_access hpre.stack.valid [hb.sp, hpi25]
      · simp only [Addr.eval, E.eval, hw.x13, Sym.validAccess_eight]
        constructor <;> addr_omega [hi]
      · simp only [Addr.eval, E.eval, hw.x12]
        valid_access hpre.state [hb.st, hi])
  have hr (r : Reg) (e : E) (hm : (r, e) ∈ (piX i).regs) : w'.getReg r = e.eval w := h.2.1 _ hm
  have hfr (a : Word) (ha : a ≠ piKey.eval w) : w'.getMem a = w.getMem a :=
    h.2.2.2 a fun k hk ↦ by
      simp only [piX, List.mem_singleton] at hk
      rw [hk]; exact ha
  have hval : w'.getMem (s.getReg .x2 - 304 + BitVec.ofNat 64 (8 * keccakPiRust.getD i 0)) =
      (A.getD i 0).rotateLeft (keccakRhoRust.getD i 0) := by
    have hm := h.2.2.1 (piKey, piVal i) (by simp [piX])
    rw [hkey] at hm
    rw [hm]
    simp only [piVal, E.eval, BinOp.eval, hrho, hw.x12, rot_eval _ hrho64]
    rw [← hA, readWords_getD _ _ _ _ hi, hw.frame _ (by addr_omega [hb.sp, hb.st, hb.apart, hi])]
  refine ⟨w', ⟨_, hst⟩, ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [h.1]
    simp only [piX, E.eval, CmpOp.eval, BinOp.eval, hw.x13, hw.x10]
    by_cases hlast : i + 1 < 25
    · rw [ite_bne_of_ne (by addr_omega [hi, hlast])]; simp [hlast]
    · rw [ite_bne_of_eq (by addr_omega [hi, hlast])]; simp [hlast]
  · rw [hr .x2 (.reg .x2) (by simp [piX])]; exact hw.sp
  · rw [hr .x8 (.reg .x8) (by simp [piX])]; exact hw.x8
  · rw [hr .x10 (.reg .x10) (by simp [piX])]; exact hw.x10
  · rw [hr .x11 (.c (rhoAddr (i + 1))) (by simp [piX])]; rfl
  · rw [hr .x12 (.bin .add (.reg .x12) (.c 8)) (by simp [piX])]
    simp only [E.eval, BinOp.eval, hw.x12]
    addr_omega [hi, hb.st]
  · rw [hr .x13 (.bin .add (.reg .x13) (.c 8)) (by simp [piX])]
    simp only [E.eval, BinOp.eval, hw.x13]
    addr_omega [hi]
  · rw [hr .x17 (.reg .x17) (by simp [piX])]; exact hw.x17
  · rw [foldl_range_succ, ← hw.b]
    exact readWords_set hval fun j hj hne ↦ hfr _ (by
      rw [hkey]; addr_omega [hb.sp, hj, hpi25, hne])
  · intro a ha
    rw [hfr a (by rw [hkey]; addr_omega [ha, hb.sp, hpi25]), hw.frame a ha]

/-- `b` cleared by `memset`, and the loop's setup: before the ρ and π loop. -/
theorem memset_step (hMemset : MemsetSpec) {s u : MachineState} (hpre : KeccakFPre s) {k : Nat}
    (hu : AtMemset s u k) : ∃ v, Reaches Image.code u v ∧ ((RoundFrame s u v ∧
      PiInv s v v (thetaRust (rounds (lanesIn s) k)) 0 ∧
      v.getMem (s.getReg .x2 - 552) = BitVec.ofNat 64 k ∧
      v.getMem (s.getReg .x2 - 528) = keccakRCRust.getD k 0 ∧
      v.readWords (s.getReg .x10) 25 = thetaRust (rounds (lanesIn s) k)) ∨ Dead Image.code v) := by
  have hb := hpre.bounds
  have h200 : (u.getReg .x12).toNat = 200 := by rw [hu.x12]; rfl
  have hmpre : MemsetPre u := {
    dst := by
      rw [h200, hu.x10]
      exact mapped_of_range (n := 25) (by
        refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp, hb.st, hb.apart])
    stack := ⟨by
        simp only [stackLo, memStack, hu.sp]
        refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp, hb.st, hb.apart],
      by rw [hu.sp]; addr_omega [hb.sp]⟩
    dstStack := by rw [h200, hu.x10]; simp only [stackLo, memStack, hu.sp]; addr_omega [hb.sp] }
  obtain ⟨v, hr, ⟨hvpc, hpres, hpost⟩ | hdead⟩ := hMemset.call (Reaches.refl u) hu.pc hmpre
  swap
  · exact ⟨v, hr, Or.inr hdead⟩
  have hv2 : v.getReg .x2 = s.getReg .x2 - 640 := (hpres.reg .x2).trans hu.sp
  have hv8 : v.getReg .x8 = s.getReg .x10 := (hpres.reg .x8).trans hu.x8
  have hfr (a : Word) (h₁ : Apart a 8 (s.getReg .x2 - 304) 200)
      (h₂ : ¬ Within a (s.getReg .x2 - 656) 16) : v.getMem a = u.getMem a := by
    apply hpost.frame a
    · rw [h200, hu.x10]; exact h₁
    · simp only [stackLo, memStack, hu.sp]; addr_omega [h₂, hb.sp]
  have hzero : bytesAt v (s.getReg .x2 - 304) 200 = List.replicate 200 0 := by
    have := hpost.bytes
    rw [h200, hu.x10, hu.x11] at this
    exact this
  obtain ⟨v₁, hr₁, h₁⟩ := BlockSpec.reaches b8000450c_spec
    (by rw [hvpc, returnAddress_eq, hu.ra]; decide) trivial
  have k₁ := b8000450c_keeps h₁
  have hm₁ := b8000450c_mem_same h₁
  refine ⟨v₁, hr.trans hr₁, Or.inl ⟨fun a h₁a h₂a h₃a ↦ ?_, ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, fun _ _ ↦ rfl⟩, ?_, ?_, ?_⟩⟩
  · rw [hm₁, hfr a h₃a (by addr_omega [h₂a, hb.sp])]
  · rw [b8000450c_pc h₁]; rfl
  · rw [k₁ .x2 (by decide), hv2]
  · rw [k₁ .x8 (by decide), hv8]
  · exact b8000450c_x10 h₁
  · rw [b8000450c_x11 h₁]; rfl
  · rw [b8000450c_x12 h₁, hv8]; simp
  · rw [b8000450c_x13 h₁]; rfl
  · rw [b8000450c_x17 h₁, hv2]; addr_omega [hb.sp]
  · apply readWords_eq (by simp)
    intro i hi
    rw [hm₁, getMem_of_bytesAt_zero (by addr_omega [hb.sp]) hzero (by omega), List.range_zero,
      List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    simp [hi]
  · rw [hm₁, hfr _ (by addr_omega [hb.sp]) (by addr_omega [hb.sp]), hu.kslot]
  · rw [hm₁, hfr _ (by addr_omega [hb.sp]) (by addr_omega [hb.sp]), hu.rc]
  · rw [← hu.mem]
    apply readWords_congr
    intro i hi
    rw [hm₁, hfr _ (by addr_omega [hb.sp, hb.st, hb.apart, hi])
      (by addr_omega [hb.sp, hb.st, hb.apart, hi])]

theorem pi_loop {s v : MachineState} (hpre : KeccakFPre s) (hv : KeccakTables v)
    {A : List Word} (hA : v.readWords (s.getReg .x10) 25 = A) (h0 : PiInv s v v A 0) :
    ∀ n ≤ 25, ∃ w, Reaches Image.code v w ∧ PiInv s v w A n
  | 0, _ => ⟨v, Reaches.refl v, h0⟩
  | n + 1, hn => by
    obtain ⟨w, hr, hw⟩ := pi_loop hpre hv hA h0 n (by omega)
    obtain ⟨w', hr', hw'⟩ := pi_step hpre hv hA (by omega) hw
    exact ⟨w', hr.trans hr', hw'⟩

/-! ## χ and ι -/

theorem chi_congr {f g : Nat → Word} (h : ∀ j < 25, f j = g j) {i : Nat} (hi : i < 25) :
    chi f i = chi g i := by
  unfold chi
  rw [h i hi, h _ (by omega), h _ (by omega)]

theorem slot_eval (w : MachineState) (off : Nat) :
    (slot off).eval w = w.getMem (w.getReg .x2 + BitVec.ofNat 64 off) := rfl

theorem outE_eval (w : MachineState) (i : Nat) :
    (outE i).eval w = chi (fun j ↦ (bE j).eval w) i ^^^ (if i = 0 then (slot 112).eval w else 0) := by
  by_cases h : i = 0
  · subst h
    simp only [outE, ↓reduceIte, E.eval, BinOp.eval, chiE_eval]
  · simp only [outE, h, ↓reduceIte, chiE_eval, Sym.xor_zero_lit]

theorem getD_map_range {f : Nat → Word} {n i : Nat} (hi : i < n) :
    ((List.range n).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem hd_ge {j : Nat} (hj : 25 ≤ j) : hd j = .c 0 := by
  simp only [hd, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by simp only [headE, List.length_cons, List.length_nil]; omega)]
  rfl

theorem getD_ge {l : List Word} (hl : l.length = 25) {j : Nat} (hj : 25 ≤ j) : l.getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

/-- Before χ in round `k`: `b`, the round constant and `k` in their slots. -/
structure AtChi (s w : MachineState) (k : Nat) : Prop where
  pc : w.pc = 0x80004564
  sp : w.getReg .x2 = s.getReg .x2 - 640
  x8 : w.getReg .x8 = s.getReg .x10
  kslot : w.getMem (s.getReg .x2 - 552) = BitVec.ofNat 64 k
  rc : w.getMem (s.getReg .x2 - 528) = keccakRCRust.getD k 0
  b : w.readWords (s.getReg .x2 - 304) 25 = rhoPiRust (thetaRust (rounds (lanesIn s) k))

theorem chi_hsub : CodeSub (codeWindow Image.code 4441 158) Image.code :=
  codeWindow_sub _ _ _ (by decide)

theorem chi_step {s w : MachineState} (hpre : KeccakFPre s) {k : Nat} (hk : k < 24)
    (hw : AtChi s w k) : ∃ u, Reaches Image.code w u ∧ RoundFrame s w u ∧
      u.pc = (if k + 1 < 24 then 0x800042e4 else 0x800047dc) ∧
      u.getReg .x2 = s.getReg .x2 - 640 ∧ u.getReg .x8 = s.getReg .x10 ∧
      u.getReg .x25 = BitVec.ofNat 64 (k + 1) ∧
      (∀ j, (hd j).eval u = (rounds (lanesIn s) (k + 1)).getD j 0) ∧
      u.readWords (s.getReg .x10) 25 = rounds (lanesIn s) (k + 1) := by
  have hb := hpre.bounds
  have hL : (rounds (lanesIn s) k).length = 25 := length_rounds (readWords_length _ _ _) k
  have hL' : (rounds (lanesIn s) (k + 1)).length = 25 := length_rounds (readWords_length _ _ _) _
  have hA := length_thetaRust hL
  have hok : RegionsOk w [stateR, slotsR, bR] := regionsOk_three
    (by rw [stateR_start, hw.x8]; exact hpre.state)
    (by rw [slotsR_start, slotsR_n, hw.sp]; refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp])
    (by rw [bR_start, bR_n, hw.sp]; refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp])
  have hap : RegionsApart w [stateR, slotsR, bR] := regionsApart_three
    (by rw [stateR_start, slotsR_start, stateR_n, slotsR_n, hw.x8, hw.sp]
        addr_omega [hb.sp, hb.st, hb.apart])
    (by rw [stateR_start, bR_start, stateR_n, bR_n, hw.x8, hw.sp]
        addr_omega [hb.sp, hb.st, hb.apart])
    (by rw [slotsR_start, bR_start, slotsR_n, bR_n, hw.sp]; addr_omega [hb.sp])
  obtain ⟨u, hst, h⟩ := run_spec (cfg := cfg) chi_run chi_hsub (s := w) (u := w)
    (by rw [← hw.pc]; exact SymState.init_toState w) hok hap (fun _ h ↦ by cases h) trivial
  have hB (j : Nat) (hj : j < 25) : (bE j).eval w =
      (rhoPiRust (thetaRust (rounds (lanesIn s) k))).getD j 0 := by
    rw [bE, slot_eval, ← hw.b, readWords_getD _ _ _ _ hj, hw.sp]
    exact congrArg w.getMem (by addr_omega [hb.sp, hj])
  have hrc : (slot 112).eval w = keccakRCRust.getD k 0 := by
    rw [slot_eval, hw.sp, ← hw.rc]
    exact congrArg w.getMem (by addr_omega [hb.sp])
  have hout (i : Nat) (hi : i < 25) : (outE i).eval w = (rounds (lanesIn s) (k + 1)).getD i 0 := by
    rw [outE_eval, chi_congr hB hi, hrc, rounds_succ _ hk, keccakRoundRust_stages,
      chiRust_eq hA (length_rhoPiRust _), getD_map_range hi]
  have hfr (a : Word) (h₁ : ¬ Within a (s.getReg .x10) 200)
      (h₂ : ¬ Within a (s.getReg .x2 - 640) 128) : u.getMem a = w.getMem a :=
    h.frame_regions (by
      intro R hR
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl
      · exact hok _ (by simp)
      · exact hok _ (by simp)) chi_writes a (by
      intro R hR
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl
      · rw [stateR_start, hw.x8]; exact h₁
      · rw [slotsR_start, hw.sp]; exact h₂)
  have hreg (r : Reg) (e : E) (hm : (r, e) ∈ [(Reg.x2, E.reg .x2), (Reg.x8, E.reg .x8),
      (Reg.x25, E.bin .add (slot 88) (.c 1))]) : u.getReg r = e.eval w :=
    h.2.1 _ (List.mem_append_left _ hm)
  refine ⟨u, ⟨_, hst⟩, fun a h₁ h₂ _ ↦ hfr a h₁ (by addr_omega [h₂, hb.sp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.1]
    simp only [chiX, E.eval, CmpOp.eval, BinOp.eval, slot_eval, hw.sp]
    rw [show s.getReg .x2 - 640 + BitVec.ofNat 64 88 = s.getReg .x2 - 552 by addr_omega [hb.sp],
      hw.kslot]
    by_cases hlast : k + 1 < 24
    · rw [ite_bne_of_ne (by addr_omega [hk, hlast])]; simp [hlast]
    · rw [ite_bne_of_eq (by addr_omega [hk, hlast])]; simp [hlast]
  · rw [hreg .x2 (.reg .x2) (by simp)]; exact hw.sp
  · rw [hreg .x8 (.reg .x8) (by simp)]; exact hw.x8
  · rw [hreg .x25 (.bin .add (slot 88) (.c 1)) (by simp)]
    simp only [E.eval, BinOp.eval, slot_eval, hw.sp]
    rw [show s.getReg .x2 - 640 + BitVec.ofNat 64 88 = s.getReg .x2 - 552 by addr_omega [hb.sp],
      hw.kslot]
    addr_omega [hk]
  · intro j
    by_cases hj : j < 25
    · rw [h.eval_of_atomOk (List.all_eq_true.mp chi_head j (List.mem_range.mpr hj)), hout j hj]
    · rw [hd_ge (by omega), getD_ge hL' (by omega)]
      rfl
  · apply readWords_eq hL'
    intro i hi
    have hm := h.2.2.1 (key .x8 (8 * i), outE i)
      (List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    rw [key_eval, hw.x8] at hm
    rw [hm, hout i hi]

/-! ## A round -/

theorem round (hMemset : MemsetSpec) {s t : MachineState} (hpre : KeccakFPre s) {k : Nat}
    (ht : Head s t k) : ∃ u, Reaches Image.code t u ∧
      (Head s u (k + 1) ∨ Exit s u ∨ Dead Image.code u) := by
  have hb := hpre.bounds
  have hk := ht.lt
  obtain ⟨u₁, hr₁, hf₁, hm⟩ := theta_step hpre ht
  obtain ⟨v, hr₂, ⟨hf₂, hpi0, hks, hrcs, hmem⟩ | hdead⟩ := memset_step hMemset hpre hm
  swap
  · exact ⟨v, hr₁.trans hr₂, Or.inr (Or.inr hdead)⟩
  have hcv : Common s v := Common.of_frame hb (Common.of_frame hb ht.toCommon hf₁) hf₂
  have htab : KeccakTables v := tables_frame hb hpre.tables hcv.frame
  obtain ⟨w, hr₃, hw⟩ := pi_loop hpre htab hmem hpi0 25 le_rfl
  have hf₃ : RoundFrame s v w := fun a _ _ ha ↦ hw.frame a ha
  have hchi : AtChi s w k := {
    pc := by rw [hw.pc]; rfl
    sp := hw.sp
    x8 := hw.x8
    kslot := by rw [hw.frame _ (by addr_omega [hb.sp])]; exact hks
    rc := by rw [hw.frame _ (by addr_omega [hb.sp])]; exact hrcs
    b := hw.b }
  obtain ⟨u, hr₄, hf₄, hpc, hsp, hx8, hx25, hlanes, hmem'⟩ := chi_step hpre hk hchi
  have hcu : Common s u := Common.of_frame hb hcv (hf₃.trans hf₄)
  have hr : Reaches Image.code t u := hr₁.trans (hr₂.trans (hr₃.trans hr₄))
  by_cases hlast : k + 1 < 24
  · exact ⟨u, hr, Or.inl ⟨hcu, by rw [hpc]; simp [hlast], hlast, hsp, hx8, hx25, hlanes, hmem'⟩⟩
  · have h24 : k + 1 = 24 := by omega
    exact ⟨u, hr, Or.inr (Or.inl ⟨hcu, by rw [hpc]; simp [hlast], hsp,
      by rw [hmem', h24, rounds_24]⟩)⟩

/-! ## Entry -/

theorem setup (hMemcpy : MemcpySpec) {s : MachineState} (hpc : s.pc = 0x80004210)
    (hpre : KeccakFPre s) : ∃ t, Reaches Image.code s t ∧ (Head s t 0 ∨ Dead Image.code t) := by
  have hb := hpre.bounds
  obtain ⟨t₁, hr₁, h₁⟩ := BlockSpec.reaches b80004210_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hb.sp])
  have k₁ := b80004210_keeps h₁
  have hf₁ := b80004210_frame h₁ (by addr_omega [hb.sp])
  have h192 : (t₁.getReg .x12).toNat = 192 := by rw [b80004210_x12 h₁]; rfl
  have ht₁2 := b80004210_x2 h₁
  have ht₁10 := b80004210_x10 h₁
  have ht₁11 := b80004210_x11 h₁
  have hmpre : MemcpyPre t₁ := {
    dst := by
      rw [h192, ht₁10]
      exact mapped_of_range (n := 24) (by
        refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp, hb.st, hb.apart])
    src := by rw [h192, ht₁11]; simp only [Runtime.Mapped]; decide
    apart := by rw [h192, ht₁10, ht₁11]; addr_omega [hb.sp, hb.tables]
    stack := ⟨by
        simp only [stackLo, memStack, ht₁2]
        refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp, hb.st, hb.apart],
      by rw [ht₁2]; addr_omega [hb.sp]⟩
    dstStack := by rw [h192, ht₁10]; simp only [stackLo, memStack, ht₁2]; addr_omega [hb.sp]
    srcStack := by
      rw [h192, ht₁11]; simp only [stackLo, memStack, ht₁2]; addr_omega [hb.sp, hb.tables] }
  obtain ⟨v, hr₂, ⟨hvpc, hpres, hpost⟩ | hdead⟩ :=
    hMemcpy.call hr₁ (b80004210_pc h₁) hmpre
  swap
  · exact ⟨v, hr₂, Or.inr hdead⟩
  have hv2 : v.getReg .x2 = s.getReg .x2 - 640 := (hpres.reg .x2).trans ht₁2
  have hv8 : v.getReg .x8 = s.getReg .x10 := (hpres.reg .x8).trans (b80004210_x8 h₁)
  have hfr₂ (a : Word) (h₁a : Apart a 8 (s.getReg .x2 - 496) 192)
      (h₂a : ¬ Within a (s.getReg .x2 - 656) 16) : v.getMem a = t₁.getMem a := by
    apply hpost.frame a
    · rw [h192, ht₁10]; exact h₁a
    · simp only [stackLo, memStack, ht₁2]; addr_omega [h₂a, hb.sp]
  have hok : RegionsOk v [stateR, slotsR] := regionsOk_two
    (by rw [stateR_start, hv8]; exact hpre.state)
    (by rw [slotsR_start, slotsR_n, hv2]; refine stack_sub hpre ?_ ?_ ?_ <;> addr_omega [hb.sp])
  have hap : RegionsApart v [stateR, slotsR] := regionsApart_two
    (by rw [stateR_start, slotsR_start, stateR_n, slotsR_n, hv8, hv2]
        addr_omega [hb.sp, hb.st, hb.apart])
  obtain ⟨t, hr₃, h₃⟩ := BlockSpec.reaches b80004264_spec
    (by rw [hvpc, returnAddress_eq, b80004210_x1 h₁]; decide)
    (oblig_all hok hap (bs := []) (fun _ h ↦ by cases h) (extra := []) trivial setup_obl)
  have k₃ := b80004264_keeps h₃
  have hfr₃ (a : Word) (ha : ¬ Within a (s.getReg .x2 - 640) 128) : t.getMem a = v.getMem a :=
    h₃.frame_regions (by
      intro R hR
      simp only [List.mem_singleton] at hR
      subst hR
      exact hok _ (by simp)) setup_writes a (by
      intro R hR
      simp only [List.mem_singleton] at hR
      subst hR
      rw [slotsR_start, hv2]; exact ha)
  -- memory outside the stack, the frame and the round constants
  have hout (a : Word) (h₁a : ¬ Within a (stackLo s keccakFStack) keccakFStack) :
      t.getMem a = s.getMem a := by
    rw [hfr₃ a (by addr_omega [h₁a, hb.sp]), hfr₂ a (by addr_omega [h₁a, hb.sp])
      (by addr_omega [h₁a, hb.sp]), hf₁ a (by addr_omega [h₁a, hb.sp])]
  have hsaved (a : Word) (h₁a : (s.getReg .x2).toNat - 104 ≤ a.toNat)
      (h₂a : a.toNat < (s.getReg .x2).toNat) : t.getMem a = t₁.getMem a := by
    rw [hfr₃ a (by addr_omega [h₁a, h₂a, hb.sp]),
      hfr₂ a (by addr_omega [h₁a, h₂a, hb.sp]) (by addr_omega [h₁a, h₂a, hb.sp])]
  have hbytes : bytesAt v (s.getReg .x2 - 496) 192 = bytesAt t₁ keccakTablesAddr 192 := by
    have := hpost.bytes
    rw [h192, ht₁10, ht₁11] at this
    exact this
  refine ⟨t, hr₂.trans hr₃, Or.inl ⟨⟨?_, ?_, ?_⟩, b80004264_pc h₃, by decide, ?_, ?_, ?_,
    ?_, ?_⟩⟩
  · apply readWords_eq (by rfl)
    intro j hj
    have hrc := List.all_eq_true.mp rc_table j (List.mem_range.mpr hj)
    rw [beq_iff_eq] at hrc
    rw [← hrc, hfr₃ _ (by addr_omega [hb.sp, hj]),
      ← table_get hpre.tables (by omega : j < 62), ← hf₁ _ (by addr_omega [hb.sp, hb.tables, hj])]
    have hb8 := getMem_of_bytesAt (s := t₁) (t := v) (a := s.getReg .x2 - 496)
      (b := keccakTablesAddr) (n := 192) (by addr_omega [hb.sp]) (by decide) hbytes (j := j)
      (by omega)
    exact hb8
  · simp only [MachineState.readWords_succ, MachineState.readWords_zero, savedRegs,
      List.cons.injEq, and_true]
    rv_eval []
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [hsaved _ (by addr_omega [hb.sp]) (by addr_omega [hb.sp])]
    · exact b80004210_m_x2_n104 h₁
    · exact b80004210_m_x2_n96 h₁
    · exact b80004210_m_x2_n88 h₁
    · exact b80004210_m_x2_n80 h₁
    · exact b80004210_m_x2_n72 h₁
    · exact b80004210_m_x2_n64 h₁
    · exact b80004210_m_x2_n56 h₁
    · exact b80004210_m_x2_n48 h₁
    · exact b80004210_m_x2_n40 h₁
    · exact b80004210_m_x2_n32 h₁
    · exact b80004210_m_x2_n24 h₁
    · exact b80004210_m_x2_n16 h₁
    · exact b80004210_m_x2_n8 h₁
  · intro a _ h₂a
    exact hout a h₂a
  · rw [k₃ .x2 (by decide), hv2]
  · rw [k₃ .x8 (by decide), hv8]
  · rw [b80004264_x25 h₃]; rfl
  · intro j
    rw [rounds_zero]
    by_cases hj : j < 25
    · rw [h₃.eval_of_atomOk (List.all_eq_true.mp setup_head j (List.mem_range.mpr hj))]
      simp only [E.eval, Addr.toE_eval, key_eval, hv8]
      rw [hfr₂ _ (by addr_omega [hb.sp, hb.st, hb.apart, hj])
          (by addr_omega [hb.sp, hb.st, hb.apart, hj]),
        hf₁ _ (by addr_omega [hb.sp, hb.st, hb.apart, hj]), lanesIn, readWords_getD _ _ _ _ hj]
    · rw [hd_ge (by omega), getD_ge (l := lanesIn s) (readWords_length _ _ _) (by omega)]
      rfl
  · rw [rounds_zero]
    apply readWords_congr
    intro i hi
    exact hout _ (by addr_omega [hb.sp, hb.st, hb.apart, hi])

/-! ## Exit -/

theorem exit {s t : MachineState} (hpre : KeccakFPre s) (ht : Exit s t) :
    ∃ u, Reaches Image.code t u ∧ u.pc = returnAddress s ∧ Preserves s u ∧ KeccakFPost s u := by
  have hb := hpre.bounds
  obtain ⟨u, hr, h⟩ := BlockSpec.reaches b800047dc_spec ht.pc (by
    rv_eval [ht.sp]
    and_intros <;> valid_access hpre.stack.valid [hb.sp])
  have hm := b800047dc_mem_same h
  have hsv := ht.saved
  simp only [MachineState.readWords_succ, MachineState.readWords_zero, savedRegs,
    List.cons.injEq, and_true] at hsv
  rv_eval [] at hsv
  obtain ⟨h27, h26, h25, h24, h23, h22, h21, h20, h19, h18, h9, h8, h1⟩ := hsv
  have hslot (off : Nat) (a : Word) (ha : s.getReg .x2 - 640 + BitVec.ofNat 64 off = a) :
      t.getMem (t.getReg .x2 + BitVec.ofNat 64 off) = t.getMem a := by rw [ht.sp, ha]
  have hx (r : Reg) (off : Nat) {a : Word} {v : Word}
      (hr : u.getReg r = t.getMem (t.getReg .x2 + BitVec.ofNat 64 off))
      (ha : s.getReg .x2 - 640 + BitVec.ofNat 64 off = a) (hv : t.getMem a = v) : u.getReg r = v := by
    rw [hr, hslot off a ha, hv]
  refine ⟨u, hr, ?_, ?_, ⟨?_, fun a h₁ h₂ ↦ ?_⟩⟩
  · rw [b800047dc_pc h, returnAddress_eq, ht.sp,
      show s.getReg .x2 - 640 + (632 : Word) = s.getReg .x2 - 8 by addr_omega [hb.sp], h1]
  · apply preserves_of
    · rw [b800047dc_x2 h, ht.sp]; addr_omega [hb.sp]
    · exact hx .x8 624 (b800047dc_x8 h) (by addr_omega [hb.sp]) h8
    · exact hx .x9 616 (b800047dc_x9 h) (by addr_omega [hb.sp]) h9
    · exact hx .x18 608 (b800047dc_x18 h) (by addr_omega [hb.sp]) h18
    · exact hx .x19 600 (b800047dc_x19 h) (by addr_omega [hb.sp]) h19
    · intro r hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hx .x20 592 (b800047dc_x20 h) (by addr_omega [hb.sp]) h20
      · exact hx .x21 584 (b800047dc_x21 h) (by addr_omega [hb.sp]) h21
      · exact hx .x22 576 (b800047dc_x22 h) (by addr_omega [hb.sp]) h22
      · exact hx .x23 568 (b800047dc_x23 h) (by addr_omega [hb.sp]) h23
      · exact hx .x24 560 (b800047dc_x24 h) (by addr_omega [hb.sp]) h24
      · exact hx .x25 552 (b800047dc_x25 h) (by addr_omega [hb.sp]) h25
      · exact hx .x26 544 (b800047dc_x26 h) (by addr_omega [hb.sp]) h26
      · exact hx .x27 536 (b800047dc_x27 h) (by addr_omega [hb.sp]) h27
  · rw [show s.readWords (s.getReg .x10) 25 = lanesIn s from rfl, ← ht.mem]
    exact readWords_congr fun i _ ↦ hm _
  · rw [hm, ht.frame a h₁ h₂]

/-! ## `keccak_f` -/

/-- **`keccak_f` meets its contract**, given `memcpy`'s and `memset`'s. -/
theorem keccak_f_spec (hMemcpy : MemcpySpec) (hMemset : MemsetSpec) : KeccakFSpec := by
  intro s hpc hpre
  obtain ⟨t, hst, ht | hdead⟩ := setup hMemcpy hpc hpre
  swap
  · exact ⟨t, hst, Or.inr hdead⟩
  obtain ⟨u, htu, hu⟩ := Reaches.loop (code := Image.code) (fun t ↦ ∃ k, Head s t k)
    (fun t ↦ 24 - (t.getReg .x25).toNat) (fun u ↦ Exit s u ∨ Dead Image.code u)
    (fun t ⟨k, ht⟩ ↦ by
      obtain ⟨u, hr, hu | hu | hu⟩ := round hMemset hpre ht
      · refine Or.inr ⟨u, hr, ⟨k + 1, hu⟩, ?_⟩
        rw [hu.x25, ht.x25, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        have := hu.lt
        omega
      · exact Or.inl ⟨u, hr, Or.inl hu⟩
      · exact Or.inl ⟨u, hr, Or.inr hu⟩) t ⟨0, ht⟩
  rcases hu with hu | hdead
  · obtain ⟨v, huv, hpc', hpres, hpost⟩ := exit hpre hu
    exact ⟨v, hst.trans (htu.trans huv), Or.inl ⟨hpc', hpres, hpost⟩⟩
  · exact ⟨u, hst.trans htu, Or.inr hdead⟩

end Rv64Verifier.Hash.KeccakF
