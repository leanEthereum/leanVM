module

public import NativeRustcVmArm.Code.Vm.IvWord.Names
public import NativeRustcVmArm.Keccak.WordsIv.Lane

/-!
# `keccak256_words::<fiat_shamir_iv's closure>`: the last block's words

`tail_run`: from the last block's head (`TailStart`, the lanes the whole blocks' state `stI`),
the machine inevitably reaches the padding block with lane 16's word in X0 and the closure's
words `base` to `base + 15` XORed into the first 16 lanes (`X0At … 631`). The head's branch
(`tail_head`), lane `j`'s step (`tail{j}`: `laneL_step` below the count, else `laneZ_step`) and
lane 16's word (`tail16`).
-/

namespace NativeRustcVmArm.WordsIv

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcArm.KeccakF (wordAt_keep)
open NativeRustcVmArm.WordsHash (frame nb Lanes pre pre_zero)
open NativeRustcVm.Keccak (wordBlocks)
open Vm.Keccak256WordsOfFiatShamirIv

@[expose] public section

/-- The last block's first word. -/
abbrev base (m0 : MachineData) : Nat := 17 * nb m0

/-- The state after the whole blocks. -/
abbrev stI (m0 : MachineData) : KeccakState := wordBlocks (wv m0) (nb m0)

/-- **At the last block's head**: the lanes the whole blocks' state. -/
def TailStart [Host] (m0 : MachineData) (k : Nat) (st : MachineState) : Prop :=
  Ctx m0 st.data ∧ Lanes m0 st.data (Keccak.lane (stI m0)) ∧ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.b2Offset)

/-- The `iv_word` contract. -/
abbrev IvSpec [Host] : Prop :=
  Spec (label NativeRustcVmArm.Vm.IvWord.entryLabel) NativeRustcVmArm.IvWordPre NativeRustcVmArm.IvWordPost

end

public section

theorem ult_nat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

variable [Host]

omit [Host] in
/-- A label of a block. -/
theorem label_at [Host] {k : Nat} (hp : Placed code k) {b : List Directive} {j : Nat}
    (hb : b.IsInfixAt code j) {l : Label} {b' : List Directive} (h : b = .label l :: b') :
    Labels.label l = Host.addrOf (k + j) := by
  subst h
  exact hp.label (List.IsInfixAt.cons hb).1

omit [Host] in
/-- A block in the program. -/
theorem ic [Host] {k : Nat} (hp : Placed code k) {b : List Directive} {j : Nat}
    (hb : b.IsInfixAt code j) (hne : b ≠ []) : b.IsInfixAt Host.prog (k + j) :=
  hb.trans hp.1 hne

/-- **The last block's head**: to lane 0. -/
theorem tail_head {k : Nat} (hp : Placed code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailStart m0 k st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .X24 (stI m0) (base m0) 0 26 455) st := by
  obtain ⟨hc, hl, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hpc
  subst hpc
  obtain ⟨hwf, hm⟩ := frame_env g hc
  refine exec_then (ic hp b2_in_code (List.cons_ne_nil _ _)) tailHead hwf hm
    fun st hm' hpc => .done _ ⟨?_, ?_, ?_, fun h => absurd h (by decide), ?_⟩
  · exact ctx_step g.stk hc hm' hwf rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
      (fun w hw => by cases hw)
  · rw [pre_zero]
    exact fun i hi => wordAt_keep (r := 0) (sz := 288) hm' rfl (by omega) rfl (hl i hi)
  · exact (hm'.regs .X24 _ rfl).trans hc.x24
  · have := nb_le g
    have := count_lt g
    have := g.small
    simp only [PcOk, SBool.eval, Sym.eval, CmpOp.apply, Sym.low_W64, Env.ofMachine_regs] at hpc
    rw [hpc]
    show (if (!((m.regs.getXReg .X24).toBitVec).ult (m.regs.getXReg .X23).toBitVec) = true then _
      else _) = _
    rw [hc.x24, hc.x23, x1_bv, ult_nat (by omega) (by omega)]
    by_cases h : base m0 + 0 < m0.regs.X1.toNat
    · simp only [show base m0 < m0.regs.X1.toNat by omega, h, decide_true, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte]
      rfl
    · simp only [show ¬ base m0 < m0.regs.X1.toNat by omega, h, decide_false, Bool.not_false,
        ↓reduceIte]
      exact label_at hp b76_in_code rfl

theorem tail0 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .X24 (stI m0) (base m0) 0 26 455 st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .X24 (stI m0) (base m0) 1 462 36) st := by
  obtain ⟨hc, hl, hB, -, hpc⟩ := h
  obtain ⟨d, pc⟩ := st
  simp only at hc hl hB hpc
  by_cases hin : base m0 + 0 < m0.regs.X1.toNat
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact laneL_step hiv g (B := base m0) (j := 0) (by decide) le_rfl hin hc hl hB rfl
      (ic hp b3_in_code (List.cons_ne_nil _ _)) tailC0 rfl rfl rfl rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl
      (ic hp b4_in_code (List.cons_ne_nil _ _)) rfl tailX0 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl
      (fun h => absurd h (by decide)) (pos := true) rfl (label_at hp b77_in_code rfl) rfl
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact laneZ_step g (B := base m0) (j := 0) (by decide) le_rfl (by omega) hc hl hB
      (ic hp b76_in_code (List.cons_ne_nil _ _)) tailZ0 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl
      (fun h => absurd h (by decide)) (pos := false) rfl (label_at hp b5_in_code rfl) rfl

set_option hygiene false in
/-- Lane `j` of the last block, `0 < j < 16`: its call `c` and XOR `x` (`bc`, `bx`) below the
count, else its zero block `z` (`bz`); the next lane's zero block `bzn` and call block `bcn`. -/
local macro "tail_lane " j:num c:ident x:ident z:ident bc:ident bx:ident bz:ident bzn:ident
    bcn:ident h2:term : tactic => `(tactic| (
  obtain ⟨hc, hl, hB, -, hpc⟩ := h
  obtain ⟨d, pc⟩ := st
  simp only at hc hl hB hpc
  by_cases hin : base m0 + $j < m0.regs.X1.toNat
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact laneL_step hiv g (B := base m0) (j := $j) (by decide) le_rfl hin hc hl hB rfl
      (ic hp $bc (List.cons_ne_nil _ _)) $c rfl rfl rfl rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl
      (ic hp $bx (List.cons_ne_nil _ _)) rfl $x rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl
      $h2 (pos := false) rfl (label_at hp $bzn rfl) rfl
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact laneZ_step g (B := base m0) (j := $j) (by decide) le_rfl (by omega) hc hl hB
      (ic hp $bz (List.cons_ne_nil _ _)) $z rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl
      $h2 (pos := true) rfl (label_at hp $bcn rfl) rfl))

theorem tail1 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .X24 (stI m0) (base m0) 1 462 36 st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .X24 (stI m0) (base m0) 2 473 43) st := by
  tail_lane 1 tailC1 tailX1 tailZ1 b77_in_code b78_in_code b5_in_code b6_in_code b79_in_code
    (fun h => absurd h (by decide))

theorem tail2 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .X24 (stI m0) (base m0) 2 473 43 st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .X24 (stI m0) (base m0) 3 484 50) st := by
  tail_lane 2 tailC2 tailX2 tailZ2 b79_in_code b80_in_code b6_in_code b7_in_code b81_in_code
    (fun h => absurd h (by decide))

theorem tail3 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .X24 (stI m0) (base m0) 3 484 50 st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .X24 (stI m0) (base m0) 4 495 57) st := by
  tail_lane 3 tailC3 tailX3 tailZ3 b81_in_code b82_in_code b7_in_code b8_in_code b83_in_code
    (fun h => absurd h (by decide))

theorem tail4 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .X24 (stI m0) (base m0) 4 495 57 st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .X24 (stI m0) (base m0) 5 506 64) st := by
  tail_lane 4 tailC4 tailX4 tailZ4 b83_in_code b84_in_code b8_in_code b9_in_code b85_in_code
    (fun h => absurd h (by decide))

theorem tail5 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .X24 (stI m0) (base m0) 5 506 64 st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .X24 (stI m0) (base m0) 6 517 71) st := by
  tail_lane 5 tailC5 tailX5 tailZ5 b85_in_code b86_in_code b9_in_code b10_in_code b87_in_code
    (fun h => absurd h (by decide))

theorem tail6 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .X24 (stI m0) (base m0) 6 517 71 st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .X24 (stI m0) (base m0) 7 528 78) st := by
  tail_lane 6 tailC6 tailX6 tailZ6 b87_in_code b88_in_code b10_in_code b11_in_code b89_in_code
    (fun h => absurd h (by decide))

theorem tail7 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .X24 (stI m0) (base m0) 7 528 78 st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .X24 (stI m0) (base m0) 8 539 85) st := by
  tail_lane 7 tailC7 tailX7 tailZ7 b89_in_code b90_in_code b11_in_code b12_in_code b91_in_code
    (fun h => absurd h (by decide))

theorem tail8 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .X24 (stI m0) (base m0) 8 539 85 st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .X24 (stI m0) (base m0) 9 550 92) st := by
  tail_lane 8 tailC8 tailX8 tailZ8 b91_in_code b92_in_code b12_in_code b13_in_code b93_in_code
    (fun h => absurd h (by decide))

theorem tail9 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .X24 (stI m0) (base m0) 9 550 92 st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .X24 (stI m0) (base m0) 10 561 99) st := by
  tail_lane 9 tailC9 tailX9 tailZ9 b93_in_code b94_in_code b13_in_code b14_in_code b95_in_code
    (fun h => absurd h (by decide))

theorem tail10 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .X24 (stI m0) (base m0) 10 561 99 st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .X24 (stI m0) (base m0) 11 572 106) st := by
  tail_lane 10 tailC10 tailX10 tailZ10 b95_in_code b96_in_code b14_in_code b15_in_code
    b97_in_code (fun h => absurd h (by decide))

theorem tail11 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .X24 (stI m0) (base m0) 11 572 106 st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .X24 (stI m0) (base m0) 12 583 113) st := by
  tail_lane 11 tailC11 tailX11 tailZ11 b97_in_code b98_in_code b15_in_code b16_in_code
    b99_in_code (fun h => absurd h (by decide))

theorem tail12 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .X24 (stI m0) (base m0) 12 583 113 st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .X24 (stI m0) (base m0) 13 594 120) st := by
  tail_lane 12 tailC12 tailX12 tailZ12 b99_in_code b100_in_code b16_in_code b17_in_code
    b101_in_code (fun h => absurd h (by decide))

theorem tail13 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .X24 (stI m0) (base m0) 13 594 120 st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .X24 (stI m0) (base m0) 14 605 127) st := by
  tail_lane 13 tailC13 tailX13 tailZ13 b101_in_code b102_in_code b17_in_code b18_in_code
    b103_in_code (fun h => absurd h (by decide))

theorem tail14 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .X24 (stI m0) (base m0) 14 605 127 st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .X24 (stI m0) (base m0) 15 616 134) st := by
  tail_lane 14 tailC14 tailX14 tailZ14 b103_in_code b104_in_code b18_in_code b19_in_code
    b105_in_code (fun h => absurd h (by decide))

theorem tail15 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .X24 (stI m0) (base m0) 15 616 134 st) :
    Eventually (step1 Host.exe) (LaneAt m0 k .X24 (stI m0) (base m0) 16 627 141) st := by
  tail_lane 15 tailC15 tailX15 tailZ15 b105_in_code b106_in_code b19_in_code b20_in_code
    b107_in_code (fun _ _ => rfl)

/-- **Lane 16's word**, to the padding block. -/
theorem tail16 {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : LaneAt m0 k .X24 (stI m0) (base m0) 16 627 141 st) :
    Eventually (step1 Host.exe) (X0At m0 k .X24 (stI m0) (base m0) NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.b108Offset) st := by
  obtain ⟨hc, hl, hB, h2, hpc⟩ := h
  have h2' := h2 rfl rfl
  obtain ⟨d, pc⟩ := st
  simp only at hc hl hB h2' hpc
  by_cases hin : base m0 + 16 < m0.regs.X1.toNat
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact lane16L_step hiv g (B := base m0) hin hc hl hB rfl
      (ic hp b107_in_code (List.cons_ne_nil _ _)) tailC16 rfl rfl rfl h2' rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl rfl
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact lane16Z_step g (B := base m0) (by omega) hc hl hB
      (ic hp b20_in_code (List.cons_ne_nil _ _)) tailZ16 rfl rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (label_at hp b108_in_code rfl)

/-- **The last block's words.** -/
theorem tail_run {k : Nat} (hp : Placed code k) (hiv : IvSpec) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailStart m0 k st) :
    Eventually (step1 Host.exe) (X0At m0 k .X24 (stI m0) (base m0) NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.b108Offset) st := by
  refine Eventually.bind (tail_head hp g h) fun st0 h0 => ?_
  refine Eventually.bind (tail0 hp hiv g h0) fun st1 h1 => ?_
  refine Eventually.bind (tail1 hp hiv g h1) fun st2 h2 => ?_
  refine Eventually.bind (tail2 hp hiv g h2) fun st3 h3 => ?_
  refine Eventually.bind (tail3 hp hiv g h3) fun st4 h4 => ?_
  refine Eventually.bind (tail4 hp hiv g h4) fun st5 h5 => ?_
  refine Eventually.bind (tail5 hp hiv g h5) fun st6 h6 => ?_
  refine Eventually.bind (tail6 hp hiv g h6) fun st7 h7 => ?_
  refine Eventually.bind (tail7 hp hiv g h7) fun st8 h8 => ?_
  refine Eventually.bind (tail8 hp hiv g h8) fun st9 h9 => ?_
  refine Eventually.bind (tail9 hp hiv g h9) fun st10 h10 => ?_
  refine Eventually.bind (tail10 hp hiv g h10) fun st11 h11 => ?_
  refine Eventually.bind (tail11 hp hiv g h11) fun st12 h12 => ?_
  refine Eventually.bind (tail12 hp hiv g h12) fun st13 h13 => ?_
  refine Eventually.bind (tail13 hp hiv g h13) fun st14 h14 => ?_
  refine Eventually.bind (tail14 hp hiv g h14) fun st15 h15 => ?_
  refine Eventually.bind (tail15 hp hiv g h15) fun st16 h16 => ?_
  exact tail16 hp hiv g h16

end

end NativeRustcVmArm.WordsIv
