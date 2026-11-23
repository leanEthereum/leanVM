module

public import NativeRustcVmX64.Layout.Ladder.Exec
public import NativeRustcVmX64.Layout.Ladder.Table
public import NativeRustcVmX64.Code.Vm.Ladder.Names

/-!
# `ladder`'s window and level count (`b0` to `b8`, x86-64)

Outside the window `b0` branches to `b11`, `b16` store the `None` tag and return (`outside`).
Inside, one environment (`envA`: region 0 the frame, region 1 `QUERY_LEVELS`' entry word): `b1`,
`b3`, `b5` compare `μ` with `20`, `24`, `28`, `b2`, `b4`, `b6`, `b7` set the count and the
registers of the levels past the third, `b8` checks the count against `QUERY_LEVELS`, up to `b9`
(`head`, the state there `R9`).
-/

namespace NativeRustcVmX64.Layout.Ladder

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Ladder NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript LeanVM.Parameters NativeRustcVm.Layout
open NativeRustcVmX64.Layout.Stack (WritesW wordAt_writesW)

@[expose] public section

/-- `QUERY_LEVELS`' entry `(r - 1, μ - 16)`. -/
def lvBase [Labels] (m : MachineData) : BitVec 64 :=
  rodataAddr .queryLevels +
    BitVec.ofNat 64 (120 * ((reg m .rdx).toNat - 1) + 8 * ((reg m .rsi).toNat - 16))

/-- The environment from the entry, inside the window. -/
abbrev envA [Labels] (m : MachineData) : Env :=
  frameEnv m m 72 [(lvBase m, 8)] (fun _ ↦ 0) 0

/-- **At `b9`**, for the entry `m` (`μ` in RSI, `r` in RDX): the frame, memory changed only in it,
the result's address, `r`, the count, `μ - 16`, `r - 1`, and the registers of the levels past the
third. -/
structure R9 (m d : MachineData) : Prop where
  frame : Frame m 72 slots 0 d
  dmem : NativeRustcVm.SameOutside m.dmem d.dmem (NativeRustcVm.InRange (stackBelow m 72) 72)
  rdi : reg d .rdi = reg m .rdi
  rdx : reg d .rdx = reg m .rdx
  rcx : (reg d .rcx).toNat = nOf (reg m .rsi).toNat
  r14 : (reg d .r14).toNat = (reg m .rsi).toNat - 16
  r15 : (reg d .r15).toNat = (reg m .rdx).toNat - 1
  l3 : 3 < nOf (reg m .rsi).toNat →
    (reg d .r12).toNat = 4 ∧ (reg d .r9).toNat = (reg m .rdx).toNat + 9
  l4 : 4 < nOf (reg m .rsi).toNat →
    (reg d .r13).toNat = 4 ∧ (reg d .r10).toNat = (reg m .rdx).toNat + 12
  l5 : 5 < nOf (reg m .rsi).toNat →
    (reg d .r11).toNat = 4 ∧ (reg d .rbx).toNat = (reg m .rdx).toNat + 15

end

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 72 := by decide

/-- `x + L` with `L = 2^64 - c`: `x - c` below `k` iff `x` in `[c, c + k)`. -/
theorem add_neg_ult (x : BitVec 64) (L c k : Nat) (hL : L + c = 2 ^ 64) (hc : 0 < c)
    (hc' : c < 2 ^ 32) (hk : k < 2 ^ 32) :
    (BinOp.apply .add .W64 x (BitVec.ofNat 64 L)).ult (BitVec.ofNat 64 k) =
      decide (c ≤ x.toNat ∧ x.toNat < c + k) := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.ult]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, BitVec.toNat_add,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := x.isLt
  omega

/-- `x + L` with `L = 2^64 - c`, for `c ≤ x`: `x - c`. -/
theorem add_neg_toNat (x : BitVec 64) (L c : Nat) (hL : L + c = 2 ^ 64) (h : c ≤ x.toNat) :
    (BinOp.apply .add .W64 x (BitVec.ofNat 64 L)).toNat = x.toNat - c := by
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := x.isLt
  omega

/-- `x + c`, small. -/
theorem add_lit_toNat (x : BitVec 64) (c : Nat) (h : x.toNat + c < 2 ^ 64) :
    (BinOp.apply .add .W64 x (BitVec.ofNat 64 c)).toNat = x.toNat + c := by
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem toNat_lit {c : Nat} (h : c < 2 ^ 64) : (BitVec.ofNat 64 c).toNat = c := by
  rw [BitVec.toNat_ofNat]; omega

theorem merge_test (x : BitVec 64) (b : Bool) :
    low .W8 (BinOp.apply .merge .W8 x (if b = true then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)) =
      if b = true then 1#8 else 0#8 := by
  simp only [BinOp.apply, low8_replaceLow]
  cases b <;> rfl

/-- The window's test, as `b0` computes it. -/
theorem window_eval [Labels] {env : Env} {μ r : Nat} (h1 : (env.regs .rsi).toNat = μ)
    (h2 : (env.regs .rdx).toNat = r) : winSym.eval env = !decide (Whir.Admissible μ r) := by
  have k1 := add_neg_ult (env.regs .rsi) 18446744073709551600 16 15 (by decide) (by decide)
    (by decide) (by decide)
  have k2 := add_neg_ult (env.regs .rdx) 18446744073709551615 1 4 (by decide) (by decide)
    (by decide) (by decide)
  rw [h1] at k1
  rw [h2] at k2
  simp only [winSym, SBool.eval, Sym.eval, CmpOp.apply, low_W64, k1, k2]
  rw [show BinOp.apply .and .W8 _ _ = ext .W8 (low .W8 _ &&& low .W8 _) from rfl, low_ext,
    merge_test, merge_test]
  rw [show decide (Whir.Admissible μ r) =
      (decide (16 ≤ μ ∧ μ < 16 + 15) && decide (1 ≤ r ∧ r < 1 + 4)) by
    rw [← Bool.decide_and]
    exact decide_eq_decide.mpr (by rw [admissible_iff]; omega)]
  cases decide (16 ≤ μ ∧ μ < 16 + 15) <;> cases decide (1 ≤ r ∧ r < 1 + 4) <;> decide

theorem ge_table : ∀ μ < 31, ∀ c ∈ [20, 24, 28],
    ((low .W64 (BinOp.apply .sub .W64 (BitVec.ofNat 64 μ) (BitVec.ofNat 64 c))).msb ==
      CmpOp.apply .subV .W64 (BitVec.ofNat 64 μ) (BitVec.ofNat 64 c)) = decide (c ≤ μ) := by
  decide +kernel

/-- `μ ≥ c`, signed, as `b1`, `b3`, `b5` compute it. -/
theorem ge_eval [Labels] {env : Env} {μ : Nat} (hμ : μ < 31) (h1 : (env.regs .rsi).toNat = μ)
    {c : Nat} (hc : c ∈ [20, 24, 28]) : (geSym c).eval env = decide (c ≤ μ) := by
  have e : env.regs .rsi = BitVec.ofNat 64 μ := by
    apply BitVec.eq_of_toNat_eq; rw [h1, toNat_lit (by omega)]
  simp only [geSym, SBool.eval, Sym.eval, e]
  exact ge_table μ hμ c hc

end

public section

/-- `A + x + B - 128`, with `L = 2^64 - 128` (the literal kept abstract: the kernel recursed on
the concrete one). -/
theorem addr_eq (x A B : BitVec 64) (L : Nat) (hL : L + 128 = 2 ^ 64)
    (_hx : x.toNat + 480 ≤ 2 ^ 64) (a b : Nat) (_ha : a ≤ 3) (hb : 16 ≤ b) (hb' : b ≤ 30)
    (hA : A.toNat = 120 * a) (hB : B.toNat = 8 * b) :
    BinOp.apply .add .W64 (BinOp.apply .add .W64 (BinOp.apply .add .W64 A x) B)
      (BitVec.ofNat 64 L) = x + BitVec.ofNat 64 (120 * a + 8 * (b - 16)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat, hA, hB]
  omega

end

public section

variable [Labels]

/-- The row of `QUERY_LEVELS`' entry the executor's alias names. -/
theorem lvSym_eval {m : MachineData} (hadm : Whir.Admissible (reg m .rsi).toNat (reg m .rdx).toNat)
    (hR : RodataAt m 72) : lvSym.eval (envA m) = (envA m).base 1 + BitVec.ofInt 64 0 := by
  have hb := admissible_iff.mp hadm
  have hn := hR.noWrap .queryLevels
  rw [length_levels_bytes] at hn
  have hn' : (rodataAddr .queryLevels).toNat + 480 ≤ 2 ^ 64 := hn
  rw [ofInt_zero64, BitVec.add_zero]
  show BinOp.apply .add .W64 (BinOp.apply .add .W64 (BinOp.apply .add .W64
    (BinOp.apply .mul .W64 (BinOp.apply .add .W64 (reg m .rdx) (BitVec.ofNat 64 18446744073709551615))
      (BitVec.ofNat 64 120)) (rodataAddr .queryLevels))
    (BinOp.apply .mul .W64 (reg m .rsi) (BitVec.ofNat 64 8)))
    (BitVec.ofNat 64 18446744073709551488) = lvBase m
  have hR4 : (reg m .rdx).toNat ≤ 4 := hb.2.2.2
  have t1 : (BinOp.apply .add .W64 (reg m .rdx) (BitVec.ofNat 64 18446744073709551615)).toNat =
      (reg m .rdx).toNat - 1 := add_neg_toNat _ _ 1 (by decide) hb.2.2.1
  have t2 : (BinOp.apply .mul .W64 (BinOp.apply .add .W64 (reg m .rdx)
      (BitVec.ofNat 64 18446744073709551615)) (BitVec.ofNat 64 120)).toNat =
      120 * ((reg m .rdx).toNat - 1) := by
    simp only [BinOp.apply, low_W64, ext_W64] at t1 ⊢
    rw [BitVec.toNat_mul, t1, BitVec.toNat_ofNat]; omega
  have t3 : (BinOp.apply .mul .W64 (reg m .rsi) (BitVec.ofNat 64 8)).toNat =
      8 * (reg m .rsi).toNat := by
    simp only [BinOp.apply, low_W64, ext_W64]
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat]; omega
  exact addr_eq _ _ _ _ (by decide) hn' _ _ (by omega) hb.1 hb.2.1 t2 t3

/-- `b8`'s check passes: `QUERY_LEVELS`' entry is the count. -/
theorem count_eval {m : MachineData} (hR : RodataAt m 72)
    (hadm : Whir.Admissible (reg m .rsi).toNat (reg m .rdx).toNat) :
    (cntSym (nOf (reg m .rsi).toNat)).eval (envA m) = false := by
  have hb := admissible_iff.mp hadm
  have hw := levels_word (hR.bytesAt .queryLevels) hadm
  rw [NativeRustcVm.addr_add_add] at hw
  have hl : (envA m).load 1 0 8 = (nOf (reg m .rsi).toNat).toUInt64.toBitVec :=
    load_ofMachine (o := 0) rfl (by rw [off_zero]; exact hw)
  have hn := nOf_le (reg m .rsi).toNat
  simp only [cntSym, SBool.eval, Sym.eval, CmpOp.apply, low_W64, hl]
  rw [show (nOf (reg m .rsi).toNat).toUInt64.toBitVec = BitVec.ofNat 64 (nOf (reg m .rsi).toNat)
    from rfl]
  simp

/-- **At `b9`**: the registers, from a head path ending in `S` (count `n`). -/
theorem r9_of {m st : MachineData} (hwf : (envA m).WF)
    (hadm : Whir.Admissible (reg m .rsi).toNat (reg m .rdx).toNat) {S : SState} {n : Nat}
    (hm : Match (envA m) S st) (hS : HeadOk S n) (hn : n = nOf (reg m .rsi).toNat) : R9 m st := by
  obtain ⟨hpro, hws, h7, h2, h1, h14, h15, h3, h4, h5⟩ := hS
  have hb := admissible_iff.mp hadm
  have hr2 : (reg m .rdx).toNat ≤ 4 := hb.2.2.2
  have hreg : ∀ {r : Reg64} {v : Sym}, S.reg r = some v → reg st r = v.eval (envA m) :=
    fun h ↦ hm.regs _ _ h
  have hadd : ∀ {r : Reg64} {c : Nat}, S.reg r = some (addS .rdx c) → c ≤ 15 →
      (reg st r).toNat = (reg m .rdx).toNat + c := by
    intro r c h hc
    rw [hreg h]
    show (BinOp.apply .add .W64 (reg m .rdx) (BitVec.ofNat 64 c)).toNat = _
    exact add_lit_toNat _ c (by omega)
  have hlit : ∀ {r : Reg64} {c : Nat}, S.reg r = some (.lit c) → c < 2 ^ 64 →
      (reg st r).toNat = c := fun h hc ↦ by rw [hreg h]; exact toNat_lit hc
  have hnn := nOf_le (reg m .rsi).toNat
  refine ⟨Frame.of_prologue Frame.entry hwf hm hpro slots_le (by decide),
    sameOutside_low hwf hm (r := 0) rfl (by decide) hws, hreg h7, hreg h2, ?_, ?_, ?_,
    fun h ↦ ⟨hlit (h3 (hn ▸ h)).1 (by decide), hadd (h3 (hn ▸ h)).2 (by decide)⟩,
    fun h ↦ ⟨hlit (h4 (hn ▸ h)).1 (by decide), hadd (h4 (hn ▸ h)).2 (by decide)⟩,
    fun h ↦ ⟨hlit (h5 (hn ▸ h)).1 (by decide), hadd (h5 (hn ▸ h)).2 (by decide)⟩⟩
  · rw [hlit h1 (by omega), hn]
  · rw [hreg h14]; exact add_neg_toNat _ _ 16 (by decide) hb.1
  · rw [hreg h15]; exact add_neg_toNat _ _ 1 (by decide) hb.2.2.1

end

public section

variable [Host] {k : Nat}

/-- **Outside the window**: `b0`, `b11`, `b16`, the `None` tag. -/
theorem outside (hp : Placed code k) {m : MachineData} (hpre : LadderPre m)
    (hadm : ¬Whir.Admissible (reg m .rsi).toNat (reg m .rdx).toNat) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m ∧ rspOf st.data = rspOf m + 8#64 ∧
      LadderPost m st.data) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.Ladder.b0Offset)⟩ := by
  obtain ⟨hst, -, ⟨hOm, hOn⟩, hOS, -⟩ := hpre
  set o := reg m .rdi with hodef
  have hfnw : NativeRustcVm.NoWrap (stackBelow m 72) (72 + 8) := frame_noWrap hst (by decide)
  let env := frameEnv m m 72 [(o, 160)] (fun _ ↦ 0) 0
  have hwf : env.WF := frame_wf ⟨frame_mapped hst (by decide), hfnw⟩
    (fun x hx ↦ by obtain rfl := List.mem_singleton.mp hx; exact ⟨hOm, hOn⟩)
    (List.pairwise_pair.mpr (Apart.symm' hOS))
  have hm : Match env outS m :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, known_ptr rfl rfl, trivial⟩ trivial trivial
      trivial
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_o0 hwf nofun hm
    fun st1 hm1 hpc1 ↦ ?_
  have hc : winSym.eval env = true := by
    rw [window_eval (μ := (reg m .rsi).toNat) (r := (reg m .rdx).toNat) rfl rfl,
      decide_eq_false hadm]; rfl
  simp only [PcOk] at hpc1
  rw [hc] at hpc1
  simp (config := { decide := true }) only [↓reduceIte] at hpc1
  rw [hp.label NativeRustcVmX64.Vm.Ladder.label_11_at] at hpc1
  refine exec_at (infix_of b11_in_code (by simp [b11]) hp) exit_o11 hwf nofun hpc1 hm1
    fun st2 hm2 hpc2 ↦ ?_
  simp only [PcOk] at hpc2
  rw [hp.label NativeRustcVmX64.Vm.Ladder.label_16_at] at hpc2
  refine exec_at (infix_of b16_in_code (by simp [b16]) hp) exit_o16 hwf nofun hpc2 hm2
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hk, hrsp, hws, hW⟩ := end_o16
  simp only [PcOk] at hpc3
  refine .done _ ⟨by rw [hpc3]; exact Frame.entry.load_ret hst (by decide), ?_, ?_, ?_,
    Match.saved hm hm3 hwf rfl hk⟩
  · show reg st3.data .rsp = _
    rw [show reg st3.data .rsp = _ from hm3.regs .rsp _ hrsp,
      show (Sym.ptr 0 80).eval env = off (stackBelow m 72) 80 from eval_ptr0 (o := 80),
      frame_add 72 8]
  · rw [ladder_none hadm]
    have w := wordAt_writesW hm3 (r := 1) rfl hW (o := 0) (v := .lit 0) (by simp) (by decide)
    rw [off_zero] at w
    exact w
  · have h := sameOutside_W2 hwf hm3 (r := 0) (r' := 1) rfl rfl
      (W := fun j ↦ j < 72) (W' := fun j ↦ j < 8) fun w hw ↦ by
        rcases hws w hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact .inl ⟨h1, by omega, fun j _ hj ↦ by omega⟩
        · exact .inr ⟨h1, by omega, fun j _ hj ↦ by omega⟩
    intro q hq
    refine h q fun hq' ↦ hq ?_
    rcases hq' with ⟨j, -, hj, rfl⟩ | ⟨j, -, hj, rfl⟩
    · exact .inr (inRange_off_self (N := 72) hj (by omega))
    · exact .inl (inRange_off_self (N := 160) (by omega) (by omega))

/-- **`b0` to `b8`**: inside the window, from the entry to `b9`. -/
theorem head (hp : Placed code k) {m : MachineData} (hpre : LadderPre m)
    (hadm : Whir.Admissible (reg m .rsi).toNat (reg m .rdx).toNat) {R : MachineState → Prop}
    (cont : ∀ st, st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Ladder.b9Offset) → R9 m st.data → Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.Ladder.b0Offset)⟩ := by
  obtain ⟨hst, hR, -, -, -⟩ := hpre
  have hb := admissible_iff.mp hadm
  set μ := (reg m .rsi).toNat with hμ
  have hL := hR.bytesAt .queryLevels
  have hLn := hR.noWrap .queryLevels
  rw [length_levels_bytes] at hLn
  have hLm := hL.mapped
  rw [length_levels_bytes] at hLm
  have hsub : 120 * ((reg m .rdx).toNat - 1) + 8 * (μ - 16) + 8 ≤ 480 := by omega
  have hlv : (lvBase m).toNat =
      (rodataAddr .queryLevels).toNat + (120 * ((reg m .rdx).toNat - 1) + 8 * (μ - 16)) :=
    NativeRustcVm.toNat_add_ofNat (by unfold NativeRustcVm.NoWrap at hLn; omega)
  have hfnw : NativeRustcVm.NoWrap (stackBelow m 72) (72 + 8) := frame_noWrap hst (by decide)
  have hap : NativeRustcVm.Apart (stackBelow m 72) (72 + 8) (lvBase m) 8 := by
    have h := hR.apart .queryLevels
    rw [length_levels_bytes] at h
    exact NativeRustcVm.Apart.mono (Apart.symm' h) le_rfl le_rfl (by omega) (by omega)
  have hwf : (envA m).WF := frame_wf ⟨frame_mapped hst (by decide), hfnw⟩
    (fun x hx ↦ by
      obtain rfl := List.mem_singleton.mp hx
      exact ⟨NativeRustcVm.Mapped.sub hLm hsub, NativeRustcVm.NoWrap.sub hLn hsub⟩)
    (List.pairwise_pair.mpr hap)
  have hm : Match (envA m) entryA m :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial
      ⟨lvSym_eval hadm hR, trivial⟩
  have hc8 := count_eval hR hadm
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_a0 hwf nofun hm
    fun s0 hm0 hpc0 ↦ ?_
  have c0 : winSym.eval (envA m) = false := by
    rw [window_eval (μ := μ) (r := (reg m .rdx).toNat) rfl rfl, decide_eq_true hadm]; rfl
  simp only [PcOk] at hpc0
  rw [c0] at hpc0
  simp (config := { decide := true }) only [↓reduceIte] at hpc0
  rw [NativeRustcVmX64.Vm.Ladder.b0_length] at hpc0
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_a1 hwf nofun hpc0 hm0
    fun s1 hm1 hpc1 ↦ ?_
  have g20 := ge_eval (env := envA m) (μ := μ) (by omega) rfl (c := 20) (by simp)
  simp only [PcOk] at hpc1
  rw [g20] at hpc1
  -- The four paths end alike at `b8`.
  have at8 : ∀ {S₀ S : SState} {n : Nat} {st : MachineState},
      exec b8 S₀ = some (S, .cond (cntSym n) NativeRustcVmX64.Vm.Ladder.label_11) → HeadOk S n → n = nOf μ →
      st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.Ladder.b8Offset) → Match (envA m) S₀ st.data →
      Eventually (step1 Host.exe) R st := by
    intro S₀ S n st hx hS hn hpc hmS
    refine exec_at (infix_of b8_in_code (by simp [b8]) hp) hx hwf nofun hpc hmS
      fun s8 hm8 hpc8 ↦ ?_
    simp only [PcOk] at hpc8
    rw [hn, hc8] at hpc8
    simp (config := { decide := true }) only [↓reduceIte] at hpc8
    exact cont s8 (hpc8.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Ladder.b8_next))
      (r9_of hwf hadm hm8 hS hn)
  by_cases h20 : 20 ≤ μ
  · rw [decide_eq_true h20] at hpc1
    simp (config := { decide := true }) only [↓reduceIte] at hpc1
    rw [hp.label NativeRustcVmX64.Vm.Ladder.label_3_at] at hpc1
    refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_a3 hwf nofun hpc1 hm1
      fun s3 hm3 hpc3 ↦ ?_
    have g24 := ge_eval (env := envA m) (μ := μ) (by omega) rfl (c := 24) (by simp)
    simp only [PcOk] at hpc3
    rw [g24] at hpc3
    by_cases h24 : 24 ≤ μ
    · rw [decide_eq_true h24] at hpc3
      simp (config := { decide := true }) only [↓reduceIte] at hpc3
      rw [hp.label NativeRustcVmX64.Vm.Ladder.label_5_at] at hpc3
      refine exec_at (infix_of b5_in_code (by simp [b5]) hp) exit_a5 hwf nofun hpc3 hm3
        fun s5 hm5 hpc5 ↦ ?_
      have g28 := ge_eval (env := envA m) (μ := μ) (by omega) rfl (c := 28) (by simp)
      simp only [PcOk] at hpc5
      rw [g28] at hpc5
      by_cases h28 : 28 ≤ μ
      · rw [decide_eq_true h28] at hpc5
        simp (config := { decide := true }) only [↓reduceIte] at hpc5
        rw [hp.label NativeRustcVmX64.Vm.Ladder.label_7_at] at hpc5
        refine exec_at (infix_of b7_in_code (by simp [b7]) hp) exit_a7 hwf nofun hpc5 hm5
          fun s7 hm7 hpc7 ↦ ?_
        simp only [PcOk] at hpc7
        exact at8 exit_a8d ok_h6 (by unfold nOf; split_ifs <;> omega)
          (hpc7.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Ladder.b7_next)) hm7
      · rw [decide_eq_false h28] at hpc5
        simp (config := { decide := true }) only [↓reduceIte] at hpc5
        refine exec_at (infix_of b6_in_code (by simp [b6]) hp) exit_a6 hwf nofun
          (hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Ladder.b5_next)) hm5 fun s6 hm6 hpc6 ↦ ?_
        simp only [PcOk] at hpc6
        exact at8 exit_a8c ok_h5 (by unfold nOf; split_ifs <;> omega)
          (hpc6.trans (hp.label NativeRustcVmX64.Vm.Ladder.label_8_at)) hm6
    · rw [decide_eq_false h24] at hpc3
      simp (config := { decide := true }) only [↓reduceIte] at hpc3
      refine exec_at (infix_of b4_in_code (by simp [b4]) hp) exit_a4 hwf nofun
        (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Ladder.b3_next)) hm3 fun s4 hm4 hpc4 ↦ ?_
      simp only [PcOk] at hpc4
      exact at8 exit_a8b ok_h4 (by unfold nOf; split_ifs <;> omega)
        (hpc4.trans (hp.label NativeRustcVmX64.Vm.Ladder.label_8_at)) hm4
  · rw [decide_eq_false h20] at hpc1
    simp (config := { decide := true }) only [↓reduceIte] at hpc1
    refine exec_at (infix_of b2_in_code (by simp [b2]) hp) exit_a2 hwf nofun
      (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.Ladder.b1_next)) hm1 fun s2 hm2 hpc2 ↦ ?_
    simp only [PcOk] at hpc2
    exact at8 exit_a8a ok_h3 (by unfold nOf; split_ifs <;> omega)
      (hpc2.trans (hp.label NativeRustcVmX64.Vm.Ladder.label_8_at)) hm2

end

end NativeRustcVmX64.Layout.Ladder
