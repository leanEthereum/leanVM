import Rv64Verifier.Proofs.Gkr.LayerR13

/-!
# `keccak::verify_layer`: `linear_transpose`'s column sums

`keccak.rs:91-95` at `0x8000fed8..0x8000ffb8`: `columns = vec![ZERO; 320]` at `f + 1584`
(`from_elem`), then `columns[j % 320] += g[j]` for each `j` (`col_loop`), `j % 320` by a `mulhu`
division (`0xcccccccccccccccd`, then `>> 8`).
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-! ## The partial column sums -/

/-- `columns[q]` once `g[0..j]` are added. -/
def colAcc (gv : Nat → E) (j q : Nat) : E :=
  ∑ y ∈ Finset.range 5, if 320 * y + q < j then gv (320 * y + q) else 0

theorem colAcc_zero (gv : Nat → E) (q : Nat) : colAcc gv 0 q = 0 := by
  simp [colAcc]

theorem colAcc_succ (gv : Nat → E) {j q : Nat} (hj : j < 1600) (hq : q < 320) :
    colAcc gv (j + 1) q = colAcc gv j q + if j % 320 = q then gv j else 0 := by
  have e : ∀ y, (if 320 * y + q < j + 1 then gv (320 * y + q) else 0) =
      (if 320 * y + q < j then gv (320 * y + q) else 0) + if 320 * y + q = j then gv j else 0 := by
    intro y
    by_cases h1 : 320 * y + q < j
    · rw [ite_eq_left (by omega), ite_eq_left h1, ite_eq_right (by omega), add_zero]
    · by_cases h2 : 320 * y + q = j
      · rw [ite_eq_left (by omega), ite_eq_right h1, ite_eq_left h2, zero_add, h2]
      · rw [ite_eq_right (by omega), ite_eq_right h1, ite_eq_right h2, add_zero]
  unfold colAcc
  rw [Finset.sum_congr rfl fun y _ ↦ e y, Finset.sum_add_distrib]
  congr 1
  by_cases hq' : j % 320 = q
  · rw [ite_eq_left hq', Finset.sum_eq_single (j / 320)]
    · rw [ite_eq_left (by omega)]
    · intro y _ hy; rw [ite_eq_right (by omega)]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  · rw [ite_eq_right hq']
    exact Finset.sum_eq_zero fun y _ ↦ by rw [ite_eq_right (by omega)]

theorem colAcc_full (gv : Nat → E) {x z : Nat} (hx : x < 5) (hz : z < 64) :
    colAcc gv 1600 (64 * x + z) = colL gv x z := by
  unfold colAcc colL
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  have := Finset.mem_range.1 hy
  rw [ite_eq_left (by omega)]
  congr 1; ring

/-! ## The division by 320 -/

theorem mulhu320 {j : Nat} (hj : j < 2 ^ 32) :
    rv64_mulhu (BitVec.ofNat 64 j) 0xcccccccccccccccd >>> 8 = BitVec.ofNat 64 (j / 320) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Hash.toNat_mulhu, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  show j * 14757395258967641293 / 2 ^ 64 / 2 ^ 8 = j / 320
  omega

theorem colAddr (c : Word) (j : Nat) :
    c + BitVec.ofNat 64 (24 * j) + (BitVec.ofNat 64 (j / 320) * 512 - BitVec.ofNat 64 (j / 320) * 8192) =
      c + BitVec.ofNat 64 (24 * (j % 320)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat,
    show (512 : Word).toNat = 512 from rfl, show (8192 : Word).toNat = 8192 from rfl]
  omega

theorem colAddrK (c : Word) (j : Nat) (k : Word) :
    c + BitVec.ofNat 64 (24 * j) + k + (BitVec.ofNat 64 (j / 320) * 512 - BitVec.ofNat 64 (j / 320) * 8192) =
      c + BitVec.ofNat 64 (24 * (j % 320)) + k := by
  rw [BitVec.add_assoc (c + _) k, BitVec.add_comm k, ← BitVec.add_assoc, colAddr]

theorem st24d (b : Word) (k : Nat) (d : Word) :
    b + BitVec.ofNat 64 (24 * k) + d + 24 = b + BitVec.ofNat 64 (24 * (k + 1)) + d := by
  rw [BitVec.add_assoc (b + _) d, BitVec.add_comm d, ← BitVec.add_assoc, st24]

theorem ofNat_ne0 {n : Nat} (h0 : 0 < n) (h1 : n < 2 ^ 64) : BitVec.ofNat 64 n ≠ 0 := by
  intro h; have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, show (0 : Word).toNat = 0 from rfl] at this; omega

/-! ## The column loop -/

/-- What the column loop reads, at its start `w₀`: `g` at `G`, the columns at `C` after it. -/
structure CC (w₀ : MachineState) (C G : Word) (gv : Nat → E) : Prop where
  x8 : w₀.getReg .x8 = C
  x15 : w₀.getReg .x15 = 0xcccccccccccccccd
  x24 : w₀.getReg .x24 = 320
  g : ∀ p < 1600, eAt w₀ (G + BitVec.ofNat 64 (24 * p)) = gv p
  cp : C.toNat % 8 = 0 ∧ heapStart ≤ C.toNat ∧ C.toNat + 7680 ≤ heapEnd
  gp : G.toNat % 8 = 0 ∧ heapStart ≤ G.toNat ∧ G.toNat + 38400 ≤ C.toNat

/-- The registers the column loop keeps. -/
abbrev cRegs : List Reg := [.x2, .x8, .x15, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- The column loop at its head `0x8000ff2c`, `g[0..j]` added. -/
structure CI (w₀ w : MachineState) (C G : Word) (gv : Nat → E) (j : Nat) : Prop where
  regs : ∀ r ∈ cRegs, w.getReg r = w₀.getReg r
  x10 : w.getReg .x10 = BitVec.ofNat 64 j
  x11 : w.getReg .x11 + 1 = BitVec.ofNat 64 j
  x12 : w.getReg .x12 = BitVec.ofNat 64 (24 * (1600 - j))
  x13 : w.getReg .x13 = C + BitVec.ofNat 64 (24 * j) + 16
  x14 : w.getReg .x14 = C + BitVec.ofNat 64 (24 * j) + 8
  x16 : w.getReg .x16 = C + BitVec.ofNat 64 (24 * j)
  x17 : w.getReg .x17 = G + BitVec.ofNat 64 (24 * j) + 16
  frame : DFrame w₀ w (Within · C 7680)
  col : ∀ q < 320, eAt w (C + BitVec.ofNat 64 (24 * q)) = colAcc gv j q
  lt : j < 1600

/-- The column loop done, at `0x8000ffb8`. -/
structure CX (w₀ w : MachineState) (C : Word) (gv : Nat → E) : Prop where
  regs : ∀ r ∈ cRegs, w.getReg r = w₀.getReg r
  frame : DFrame w₀ w (Within · C 7680)
  col : ∀ q < 320, eAt w (C + BitVec.ofNat 64 (24 * q)) = colAcc gv 1600 q

set_option maxHeartbeats 8000000 in
theorem col_step {w₀ w : MachineState} {C G : Word} {gv : Nat → E} {j : Nat}
    (Cc : CC w₀ C G gv) (I : CI w₀ w C G gv j) (hpc : w.pc = 0x8000ff2c) :
    ∃ v, Reaches Image.code w v ∧ ((CI w₀ v C G gv (j + 1) ∧ v.pc = 0x8000ff2c) ∨
      (CX w₀ v C gv ∧ v.pc = 0x8000ffb8) ∨ Dead Image.code v) := by
  have hj := I.lt
  have hcp := Cc.cp
  have hgp := Cc.gp
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000ff2c_spec hpc trivial
  have pc₁ := h₁.pc
  rv_eval [] at pc₁
  rcases eq_ite_cases pc₁ with ⟨-, pc₁⟩ | ⟨-, pc₁⟩
  · exact ⟨t₁, hr₁, Or.inr (Or.inr (dead_of_fetch (by rw [pc₁]; exact trap)))⟩
  have k₁ := b8000ff2c_keeps h₁
  have hm₁ := b8000ff2c_mem_same h₁
  have x10₁ : t₁.getReg .x10 = BitVec.ofNat 64 j := by rw [k₁ .x10 (by decide), I.x10]
  have x15₁ : t₁.getReg .x15 = 0xcccccccccccccccd := by
    rw [k₁ .x15 (by decide), I.regs .x15 (by decide), Cc.x15]
  have x13₁ : t₁.getReg .x13 = C + BitVec.ofNat 64 (24 * j) + 16 := by rw [k₁ .x13 (by decide), I.x13]
  have x14₁ : t₁.getReg .x14 = C + BitVec.ofNat 64 (24 * j) + 8 := by rw [k₁ .x14 (by decide), I.x14]
  have x16₁ : t₁.getReg .x16 = C + BitVec.ofNat 64 (24 * j) := by rw [k₁ .x16 (by decide), I.x16]
  have x17₁ : t₁.getReg .x17 = G + BitVec.ofNat 64 (24 * j) + 16 := by rw [k₁ .x17 (by decide), I.x17]
  have hq := mulhu320 (j := j) (by omega)
  have hCV : ValidMemRange C 960 := heap_vmr hcp.2.1 (by omega) hcp.1
  have hGV : ValidMemRange G 4800 := heap_vmr hgp.2.1 (by omega) hgp.1
  have hjq : j % 320 < 320 := Nat.mod_lt _ (by omega)
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000ff4c_spec pc₁ (by
    rv_eval [x10₁, x15₁, x13₁, x14₁, x16₁, x17₁, hq, colAddrK, colAddr]
    and_intros <;> first
      | valid_access hCV [hcp, hjq]
      | valid_access hGV [hgp, hj]
      | addr_omega [hcp, hjq])
  have k₂ := b8000ff4c_keeps h₂
  have n0 : t₂.getMem (C + BitVec.ofNat 64 (24 * (j % 320)) + 16) =
      t₁.getMem (C + BitVec.ofNat 64 (24 * (j % 320)) + 16) ^^^ t₁.getMem (G + BitVec.ofNat 64 (24 * j) + 16) :=
    h₂.mem_eq 0 (by decide) (by rv_eval [x10₁, x15₁, x13₁, hq, colAddrK])
      (by rv_eval [x10₁, x15₁, x13₁, x17₁, hq, colAddrK])
  have n1 : t₂.getMem (C + BitVec.ofNat 64 (24 * (j % 320)) + 8) =
      t₁.getMem (C + BitVec.ofNat 64 (24 * (j % 320)) + 8) ^^^ t₁.getMem (G + BitVec.ofNat 64 (24 * j) + 8) :=
    h₂.mem_eq 1 (by decide) (by rv_eval [x10₁, x15₁, x14₁, hq, colAddrK])
      (by rv_eval [x10₁, x15₁, x14₁, x17₁, hq, colAddrK])
  have n2 : t₂.getMem (C + BitVec.ofNat 64 (24 * (j % 320))) =
      t₁.getMem (C + BitVec.ofNat 64 (24 * (j % 320))) ^^^ t₁.getMem (G + BitVec.ofNat 64 (24 * j)) :=
    h₂.mem_eq 2 (by decide) (by rv_eval [x10₁, x15₁, x16₁, hq, colAddr])
      (by rv_eval [x10₁, x15₁, x16₁, x17₁, hq, colAddr])
  have f₂ : MemFrame t₁ t₂ (C + BitVec.ofNat 64 (24 * (j % 320))) 24 :=
    h₂.memFrame (by
      rv_eval [x10₁, x15₁, x13₁, x14₁, x16₁, hq, colAddrK, colAddr]
      and_intros <;> addr_omega [hcp, hjq])
  have gj : eAt t₁ (G + BitVec.ofNat 64 (24 * j)) = gv j := by
    rw [← Cc.g j hj, ← I.frame.eAt fun i hi hw ↦ by addr_omega [hw, hi, hcp, hgp, hj]]
    unfold Rv64Verifier.eAt; rw [hm₁, hm₁, hm₁]
  have cold : eAt t₁ (C + BitVec.ofNat 64 (24 * (j % 320))) = colAcc gv j (j % 320) := by
    rw [← I.col _ hjq]; unfold Rv64Verifier.eAt; rw [hm₁, hm₁, hm₁]
  have col₂ (q : Nat) (hq' : q < 320) :
      eAt t₂ (C + BitVec.ofNat 64 (24 * q)) = colAcc gv (j + 1) q := by
    rw [colAcc_succ gv hj hq']
    by_cases hqe : j % 320 = q
    · subst hqe
      rw [ite_eq_left rfl]
      apply eAt_eq_of_limbs
      rw [limbs_add, ← cold, ← gj]
      simp only [limbs_eAt]
      rv_eval [n0, n1, n2]
    · rw [ite_eq_right hqe, add_zero, f₂.eAt (by addr_omega [hcp, hjq, hq', hqe]) (by addr_omega [hcp, hq']),
        ← I.col q hq']
      unfold Rv64Verifier.eAt; rw [hm₁, hm₁, hm₁]
  have F₂ : DFrame w₀ t₂ (Within · C 7680) :=
    (I.frame.trans (DFrame.of_same hm₁ _) fun _ h ↦ h).trans (DFrame.of_memFrame f₂) fun a h ↦ by
      addr_omega [h, hcp, hjq]
  have regs₂ (r : Reg) (hr : r ∈ cRegs) : t₂.getReg r = w₀.getReg r := by
    rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _), I.regs r hr]
  have x12₁ : t₁.getReg .x12 = BitVec.ofNat 64 (24 * (1600 - j)) := by rw [k₁ .x12 (by decide), I.x12]
  have e12 : t₁.getReg .x12 - 24 = BitVec.ofNat 64 (24 * (1600 - (j + 1))) := by
    rw [x12₁]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (24 : Word).toNat = 24 from rfl]
    omega
  have hr := hr₁.trans hr₂
  by_cases hl : j + 1 < 1600
  · refine ⟨t₂, hr, Or.inl ⟨{
      regs := regs₂
      x10 := by rw [b8000ff4c_x10 h₂, x10₁, ofNat_succ]
      x11 := by rw [k₂ .x11 (by decide), b8000ff2c_x11 h₁, I.x11, ofNat_succ]
      x12 := by rw [b8000ff4c_x12 h₂, e12]
      x13 := by rw [b8000ff4c_x13 h₂, x13₁, st24d]
      x14 := by rw [b8000ff4c_x14 h₂, x14₁, st24d]
      x16 := by rw [b8000ff4c_x16 h₂, x16₁, st24]
      x17 := by rw [b8000ff4c_x17 h₂, x17₁, st24d]
      frame := F₂
      col := col₂
      lt := hl }, b8000ff4c_pc_taken h₂ ?_⟩⟩
    rw [e12]; exact ofNat_ne0 (by omega) (by omega)
  · refine ⟨t₂, hr, Or.inr (Or.inl ⟨{
      regs := regs₂
      frame := F₂
      col := fun q hq' ↦ by rw [col₂ q hq', show j + 1 = 1600 by omega] }, b8000ff4c_pc_not_taken h₂ ?_⟩)⟩
    rw [e12, show 1600 - (j + 1) = 0 by omega]; rfl

theorem col_loop {w₀ : MachineState} {C G : Word} {gv : Nat → E} (Cc : CC w₀ C G gv) :
    ∀ n j w, j + n = 1600 → CI w₀ w C G gv j → w.pc = 0x8000ff2c →
      ∃ v, Reaches Image.code w v ∧ ((CX w₀ v C gv ∧ v.pc = 0x8000ffb8) ∨ Dead Image.code v)
  | 0, j, w, hn, Q, _ => absurd Q.lt (by omega)
  | n + 1, j, w, hn, Q, hpc => by
    obtain ⟨v, hr, ⟨Q', hpc'⟩ | ⟨X, hpc'⟩ | hd⟩ := col_step Cc Q hpc
    · obtain ⟨t, hr', ht⟩ := col_loop Cc n (j + 1) v (by omega) Q' hpc'
      exact ⟨t, hr.trans hr', ht⟩
    · exact ⟨v, hr, Or.inl ⟨X, hpc'⟩⟩
    · exact ⟨v, hr, Or.inr hd⟩

/-! ## From `J15` -/

/-- After the column sums, at `0x8000ffb8`: the columns in `s0` (length in `s8`), `g` in `s7`. -/
structure J16 (s u v : MachineState) (eqZ eqLane t : List E) (beta : E) : Prop where
  pc : v.pc = 0x8000ffb8
  base : Base s v
  mono : heapNext u ≤ heapNext v
  frame : DFrame u v (SW2 s (heapNext u) (heapNext v))
  x22 : v.getReg .x22 = 1600
  x24 : v.getReg .x24 = 320
  gbuf : heapNext u ≤ (v.getReg .x23).toNat ∧ (v.getReg .x23).toNat + 38400 ≤ (v.getReg .x8).toNat ∧
    (v.getReg .x23).toNat % 8 = 0
  cbuf : (v.getReg .x8).toNat + 7680 ≤ heapNext v ∧ (v.getReg .x8).toNat % 8 = 0
  gE : ∀ p < 1600, eAt v (v.getReg .x23 + BitVec.ofNat 64 (24 * p)) =
    gOf (nextWeightsRust eqZ eqLane beta) p
  cE : ∀ q < 320, eAt v (v.getReg .x8 + BitVec.ofNat 64 (24 * q)) =
    colAcc (gOf (nextWeightsRust eqZ eqLane beta)) 1600 q
  val : (v.getReg .x19, v.getReg .x20, v.getReg .x21) =
    limbs (t.getD 0 0 + beta * (t.getD 1 0 + beta * t.getD 2 0))
  x26 : v.getReg .x26 = u.getReg .x26
  x27 : v.getReg .x27 = 0x3333333333333334

set_option maxHeartbeats 16000000 in
theorem columns (hFE : MultilinearContracts.FromElemSpec) {s u w : MachineState}
    {eqZ eqLane t : List E} {beta : E} (hpre : VerifyLayerPre s) (hsu : heapNext s ≤ heapNext u)
    (K : J15 s u w eqZ eqLane t beta) :
    ∃ v, Reaches Image.code w v ∧ (J16 s u v eqZ eqLane t beta ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have B := K.base
  have hnx := hpre.stack.next
  have hab := hpre.stack.above
  have hrs := hpre.stack.rodata
  simp only [stackLo] at hnx hab hrs
  unfold verifyLayerStack at hb hnx hab hrs
  have hH0 := hpre.heap.lo
  have hgb := K.gbuf
  have hkm := K.mono
  -- `0x8000fed8`: `from_elem(f + 1584, ZERO, 320)`
  obtain ⟨t₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b8000fed8_spec K.pc trivial
  have k₀ := b8000fed8_keeps h₀
  have hm₀ := b8000fed8_mem_same h₀
  have x2₀ : t₀.getReg .x2 = s.getReg .x2 - 1712 := (k₀ .x2 (by decide)).trans B.x2
  have B₀ : Base s t₀ := B.same x2₀ hm₀
  have x10₀ : t₀.getReg .x10 = s.getReg .x2 - 128 := by rw [b8000fed8_x10 h₀, B.x2]; rv_eval []
  have x11₀ : t₀.getReg .x11 = 0xa0000068 := b8000fed8_x11 h₀
  have x12₀ : t₀.getReg .x12 = 320 := b8000fed8_x12 h₀
  have hfe : MultilinearContracts.FromElemPre t₀ := {
    heap := B₀.heap
    out := by rw [x10₀]; exact slot_vmr hpre (by decide) (by decide) (by decide)
    elem := by rw [x11₀]; exact zero_vmr
    stack := hpre.stack.sub 1712 x2₀ (by unfold verifyLayerStack MultilinearContracts.fromElemStack tryAllocStack; decide)
      (by decide) (by decide) (by decide) (by decide)
    outFree := by rw [x10₀]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega [hb, hab, hnx]
    outStack := by
      rw [x10₀]; simp only [stackLo, x2₀, MultilinearContracts.fromElemStack, tryAllocStack]
      addr_omega [hb]
    elemFree := by rw [x11₀]; refine ⟨Or.inr ?_, ?_⟩ <;> addr_omega []
    elemStack := by
      rw [x11₀]; simp only [stackLo, x2₀, MultilinearContracts.fromElemStack, tryAllocStack]
      addr_omega [hb, hrs]
    elemOut := by rw [x11₀, x10₀]; addr_omega [hb, hrs] }
  have hzero : eAt t₀ 0xa0000068 = 0 := by
    have hrod := B₀.rodata hpre
    apply eAt_eq_of_limbs
    rv_eval [hrod.word (a := 0xa0000068) (v := 0), hrod.word (a := 0xa0000070) (v := 0),
      hrod.word (a := 0xa0000078) (v := 0)]
    rfl
  obtain ⟨t₁, hr₁, ⟨hpc₁, hpres₁, FE⟩ | hd⟩ := hFE.call hr₀ (b8000fed8_pc h₀) hfe
  swap
  · exact ⟨_, hr₁, Or.inr hd⟩
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 1712 := (hpres₁.reg .x2).trans x2₀
  have fev := FE.vec.raw
  have fel := FE.len
  have fef := FE.fresh
  have fee := FE.elems
  simp only [x10₀, x12₀, x11₀, RawVecOk, Buf, vecPtr, vecCap, vecLen, vecEs, NewBuf, hzero] at fev fel fef fee
  rv_eval [] at fev
  rv_eval [] at fel
  rv_eval [] at fef
  rv_eval [] at fee
  have hH1 := FE.heap.hi
  have hm1 := FE.mono
  obtain ⟨C, hCd⟩ : ∃ C, t₁.getMem (s.getReg .x2 - 120) = C := ⟨_, rfl⟩
  rw [hCd] at fev fef fee
  rw [fel, show (320 : Word).toNat = 320 from rfl] at fee
  have hN₀ : heapNext t₀ = heapNext w := by simp only [heapNext, hm₀]
  have hC : heapNext w ≤ C.toNat ∧ C.toNat + 7680 ≤ heapNext t₁ := by
    rcases fef.2 with h | h
    · omega
    · rw [hN₀] at h; exact h
  have B₁ : Base s t₁ := B₀.next hpre x2₁ FE.heap FE.mono (DFrame.of_byteFrame FE.frame)
    fun a ha ↦ cframe_lw hpre B₀ 128 (by decide) (by decide)
      (by unfold MultilinearContracts.fromElemStack tryAllocStack sumcheckStack; decide) FE.heap x10₀ a ha
  have F₁ : DFrame w t₁ (SW2 s (heapNext w) (heapNext t₁)) :=
    (DFrame.of_same hm₀ _).trans (DFrame.of_byteFrame FE.frame) fun a h ↦ by
      simp only [Fresh, stackLo, x10₀, x2₀, MultilinearContracts.fromElemStack, tryAllocStack] at h
      rcases h with h | h | h | h
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))
      · exact Or.inl (by addr_omega [h, hb])
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by rw [← hN₀]; exact h.1, h.2⟩)))
  -- `0x8000fef0`: the loop's registers
  obtain ⟨w₀, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000fef0_spec
    (by rw [hpc₁, returnAddress_eq, b8000fed8_x1 h₀]; decide) (by
      rv_eval [x2₁]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₂ := b8000fef0_keeps h₂
  have hm₂ := b8000fef0_mem_same h₂
  have x2₂ : w₀.getReg .x2 = s.getReg .x2 - 1712 := (k₂ .x2 (by decide)).trans x2₁
  have B₂ : Base s w₀ := B₁.same x2₂ hm₂
  have hN₂ : heapNext w₀ = heapNext t₁ := by simp only [heapNext, hm₂]
  have F₂ : DFrame w w₀ (SW2 s (heapNext w) (heapNext w₀)) := by
    rw [hN₂]; exact F₁.trans (DFrame.of_same hm₂ _) fun _ h ↦ h
  have reg (r : Reg) (hr : r ∈ [Reg.x19, .x20, .x21, .x22, .x23, .x26, .x27]) :
      w₀.getReg r = w.getReg r := by
    rw [k₂ r (mem_of_mem hr _), hpres₁.reg r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      k₀ r (mem_of_mem hr _)]
  obtain ⟨G, hGd⟩ : ∃ G, w.getReg .x23 = G := ⟨_, rfl⟩
  rw [hGd] at hgb
  have Cc : CC w₀ C G (gOf (nextWeightsRust eqZ eqLane beta)) := {
    x8 := by rw [b8000fef0_x8 h₂, x2₁]; rv_eval [hCd]
    x15 := b8000fef0_x15 h₂
    x24 := by rw [b8000fef0_x24 h₂, x2₁]; rv_eval [fel]
    g := fun p hp ↦ by
      rw [F₂.eAt fun k hk ↦ by
        rw [add_ofNat_add]; exact sw2_buf hpre B.heap.hi (n := 38400) hgb.2.1 _ (by omega), ← hGd]
      exact K.gE p hp
    cp := ⟨fev.1, by simp only [heapStart] at hH0 ⊢; omega, by have h1 := hC.2; have h2 := hH1; omega⟩
    gp := ⟨hgb.2.2, by have h1 := hgb.1; simp only [heapStart] at hH0 ⊢; omega, by have h1 := hgb.2.1; have h2 := hC.1; omega⟩ }
  have I₀ : CI w₀ w₀ C G (gOf (nextWeightsRust eqZ eqLane beta)) 0 := {
    regs := fun _ _ ↦ rfl
    x10 := b8000fef0_x10 h₂
    x11 := by rw [b8000fef0_x11 h₂]; rfl
    x12 := by rw [b8000fef0_x12 h₂, hpres₁.reg .x22, k₀ .x22 (by decide), K.x22]; rfl
    x13 := by rw [b8000fef0_x13 h₂, x2₁, Nat.mul_zero, add_ofNat_zero]; rv_eval [hCd]
    x14 := by rw [b8000fef0_x14 h₂, x2₁, Nat.mul_zero, add_ofNat_zero]; rv_eval [hCd]
    x16 := by rw [b8000fef0_x16 h₂, x2₁, Nat.mul_zero, add_ofNat_zero]; rv_eval [hCd]
    x17 := by rw [b8000fef0_x17 h₂, Nat.mul_zero, add_ofNat_zero, hpres₁.reg .x23, k₀ .x23 (by decide), hGd]
    frame := DFrame.refl _ _
    col := fun q hq ↦ by
      rw [colAcc_zero, show eAt w₀ (C + BitVec.ofNat 64 (24 * q)) = eAt t₁ (C + BitVec.ofNat 64 (24 * q)) by
        unfold Rv64Verifier.eAt; rw [hm₂, hm₂, hm₂], ← getD_eListAt _ _ hq, fee,
        List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact hq), List.getElem_replicate]
    lt := by decide }
  obtain ⟨v, hr₃, ⟨X, hpc₃⟩ | hd⟩ := col_loop Cc 1600 0 w₀ rfl I₀ (b8000fef0_pc h₂)
  swap
  · exact ⟨v, hr₁.trans (hr₂.trans hr₃), Or.inr hd⟩
  have hNv : v.getMem nextAddr = w₀.getMem nextAddr := X.frame _ fun i hi hw ↦ by
    addr_omega [hw, hi, hC, hH1]
  have hNv' : heapNext v = heapNext w₀ := by simp only [heapNext, hNv]
  have Bv : Base s v := B₂.next hpre ((X.regs .x2 (by decide)).trans x2₂)
    ⟨by rw [hNv']; exact B₂.heap.lo, by rw [hNv']; exact B₂.heap.hi⟩ (le_of_eq hNv'.symm)
    X.frame fun a h ↦ ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [h, hC, hsu, hkm],
      by rw [hNv', hN₂]; addr_omega [h, hC]⟩))), by addr_omega [h, hb, hC, hH1, hab]⟩
  have x8v : v.getReg .x8 = C := by rw [X.regs .x8 (by decide), Cc.x8]
  have x23v : v.getReg .x23 = G := by rw [X.regs .x23 (by decide), reg .x23 (by decide), hGd]
  refine ⟨v, hr₁.trans (hr₂.trans hr₃), Or.inl {
    pc := hpc₃
    base := Bv
    mono := by rw [hNv', hN₂]; omega
    frame := (K.frame.mono fun a h ↦ sw2_mono (by rw [hNv', hN₂]; omega) h).trans
      (F₂.trans X.frame fun a h ↦ Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [h, hC],
        by rw [hN₂]; addr_omega [h, hC]⟩)))) fun a h ↦ by
      simp only [SW2] at h ⊢
      rcases h with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by rw [hNv']; exact h.2⟩)))
    x22 := by rw [X.regs .x22 (by decide), reg .x22 (by decide), K.x22]
    x24 := by rw [X.regs .x24 (by decide), Cc.x24]
    gbuf := by rw [x23v, x8v]; exact ⟨hgb.1, by omega, hgb.2.2⟩
    cbuf := by rw [x8v, hNv', hN₂]; exact ⟨hC.2, fev.1⟩
    gE := fun p hp ↦ by
      rw [x23v, X.frame.eAt fun k hk hw ↦ by addr_omega [hw, hk, hC, hgb, hp], ← Cc.g p hp]
    cE := fun q hq ↦ by rw [x8v]; exact X.col q hq
    val := by
      rw [X.regs .x19 (by decide), X.regs .x20 (by decide), X.regs .x21 (by decide),
        reg .x19 (by decide), reg .x20 (by decide), reg .x21 (by decide), K.val]
    x26 := by rw [X.regs .x26 (by decide), reg .x26 (by decide), K.x26]
    x27 := by rw [X.regs .x27 (by decide), reg .x27 (by decide), K.x27] }⟩

end Rv64Verifier.Gkr.Layer
