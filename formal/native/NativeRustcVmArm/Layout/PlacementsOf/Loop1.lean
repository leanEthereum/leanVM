module

public import NativeRustcVmArm.Code.Vm.PlacementsOf.Names
public import NativeRustcVmArm.Layout.PlacementsOf.Base

/-!
# `placements_of`: the first loop, the stacked columns and their sizes (`b3` to `b7`)

At `.L2` (`I1 c c`): the stacked columns below `c` (`below c`) and their log-sizes are in
`block_cols` and `block_sizes`. Column `c`'s slot byte (`b4`) and output byte (`b5`) decide whether
it is stacked; if so `b6`, `b7` append it (`I1 (c + 1) c`); `b3` counts on (`step1`).
-/

namespace NativeRustcVmArm.Layout.PlacementsOf

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PlacementsOf
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt wordOf addr_add_add addr_add_zero toNat_add_ofNat)
open NativeRustcVmArm.Arrays (Body calleeRegs inSlots keepsAll restores)

public section

/-! ## Addresses and bytes -/

theorem idx_eval [Labels] (env : Env) (p i : XReg) :
    (idx p i).eval env = env.regs p + BitVec.ofNat 64 (8 * (env.regs i).toNat) := by
  rw [show idx p i = .bin .add .W64 (.reg p) (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg i)) from rfl]
  sym_simp
  congr 1
  simp only [BitVec.apply_mem_extend, BitVec.unsigned]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofNat, Int.shiftLeft_eq,
    show ((2 : Int) ^ 3) = ((8 : Nat) : Int) from rfl, ← Int.natCast_mul, ← Int.natCast_emod,
    Int.toNat_natCast, Nat.mul_comm]

theorem idxB_eval [Labels] (env : Env) (p i : XReg) :
    (idxB p i).eval env = env.regs p + BitVec.ofNat 64 (env.regs i).toNat := by
  rw [show idxB p i = .bin .add .W64 (.reg p) (.un (.memExtend ⟨.UXTX, .E0⟩) .W64 (.reg i))
    from rfl]
  sym_simp
  congr 1

theorem sw32_beq (b : UInt8) {n : Nat} (hn : n < 256) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 b.toNat) == BitVec.setWidth 32 (BitVec.ofNat 64 n)) =
      decide (b.toNat = n) := by
  have := b.toNat_lt
  by_cases h : b.toNat = n
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq, ← BitVec.toNat_inj,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega

theorem ofNat_ult' {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x).ult (BitVec.ofNat 64 y) = decide (x < y) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem ofNat_beq' {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x == BitVec.ofNat 64 y) = decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne]
    intro he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_ofNat] at this
    omega

theorem tbv (x : UInt64) : x.toBitVec = BitVec.ofNat 64 x.toNat := by simp

/-! ## The invariant -/

section
variable [Labels]

/-- **The first loop**: the stacked columns below `c`, their sizes; the counter at `j`. -/
structure I1 (m0 : MachineData) (c j : Nat) (st : MachineData) : Prop where
  body : Bd m0 st
  le : c ≤ 158
  x8 : st.regs.X8.toNat = j
  x21 : st.regs.X21.toNat = 1264 - 8 * j
  x22 : st.regs.X22.toNat = (below c).length
  x19 : st.regs.X19 = m0.regs.X0
  x20 : st.regs.X20 = m0.regs.X1
  x23 : st.regs.X23.toBitVec = rodataAddr .keccakSlot
  x24 : st.regs.X24.toBitVec = rodataAddr .keccakOutput
  x25 : st.regs.X25.toBitVec = fb m0
  x26 : st.regs.X26.toBitVec = fb m0 + BitVec.ofNat 64 1264
  cols : ∀ q (h : q < (below c).length),
    WordAt st.dmem (fb m0 + BitVec.ofNat 64 (8 * q)) ((below c)[q]).toUInt64
  sizes : ∀ q (h : q < (below c).length),
    WordAt st.dmem (fb m0 + BitVec.ofNat 64 (1264 + 8 * q)) (κ m0 (below c)[q]).toUInt64

theorem I1.mono {m0 st st' : MachineData} {c j : Nat} (h : I1 m0 c j st) (hb : Bd m0 st')
    (hd : st'.dmem = st.dmem) (h8 : st'.regs.X8 = st.regs.X8) (h21 : st'.regs.X21 = st.regs.X21)
    (h22 : st'.regs.X22 = st.regs.X22) (h19 : st'.regs.X19 = st.regs.X19)
    (h20 : st'.regs.X20 = st.regs.X20) (h23 : st'.regs.X23 = st.regs.X23)
    (h24 : st'.regs.X24 = st.regs.X24) (h25 : st'.regs.X25 = st.regs.X25)
    (h26 : st'.regs.X26 = st.regs.X26) : I1 m0 c j st' :=
  ⟨hb, h.le, h8 ▸ h.x8, h21 ▸ h.x21, h22 ▸ h.x22, h19 ▸ h.x19, h20 ▸ h.x20, h23 ▸ h.x23,
    h24 ▸ h.x24, h25 ▸ h.x25, h26 ▸ h.x26, hd ▸ h.cols, hd ▸ h.sizes⟩

/-- A column not stacked leaves the stacked columns. -/
theorem I1.skip {m0 st : MachineData} {c : Nat} (h : I1 m0 c c st) (hc : c < 158)
    (hn : isBlockF c = false) : I1 m0 (c + 1) c st := by
  have e : below (c + 1) = below c := by rw [below_succ, hn]; simp
  exact ⟨h.body, by omega, h.x8, h.x21, e ▸ h.x22, h.x19, h.x20, h.x23, h.x24, h.x25, h.x26,
    e ▸ h.cols, e ▸ h.sizes⟩

omit [Labels] in
theorem length_slot : (NativeRustcVm.Data.Item.bytes .keccakSlot).length = 158 := by
  simp [NativeRustcVm.Data.Item.bytes, NativeRustcVm.Data.keccakSlot, columnCount_158]

omit [Labels] in
theorem length_out : (NativeRustcVm.Data.Item.bytes .keccakOutput).length = 158 := by
  simp [NativeRustcVm.Data.Item.bytes, NativeRustcVm.Data.keccakOutput, columnCount_158]

omit [Labels] in
theorem slot_get {c : Nat} (hc : c < 158) :
    (NativeRustcVm.Data.Item.bytes .keccakSlot)[c]'(by rw [length_slot]; exact hc) =
      NativeRustcVm.Data.slotByte (slotF c) := slot_byte hc

omit [Labels] in
theorem out_get {c : Nat} (hc : c < 158) :
    (NativeRustcVm.Data.Item.bytes .keccakOutput)[c]'(by rw [length_out]; exact hc) =
      if outF c then 1 else 0 := out_byte hc

omit [Labels] in
theorem slotByte_lt {c : Nat} : (NativeRustcVm.Data.slotByte (slotF c)).toNat < 256 :=
  UInt8.toNat_lt _

omit [Labels] in
theorem toUInt64_toNat' {x : UInt64} : x.toNat.toUInt64 = x := by
  apply UInt64.toNat.inj; simp

end

/-- A word of the frame no write of a block touched. -/
theorem keep_frame [Labels] {m0 : MachineData} (hF : Facts m0) {env : Env} {S : SState}
    {st m : MachineData} (hm : Match env S m) (hwf : env.WF) (hd : env.mem0 = st.dmem) {o : Nat}
    (ho : o + 8 ≤ 5136)
    (hW : ∀ w ∈ S.mem, ∀ b sz, env.regions[w.r]? = some (b, sz) → w.off + w.n ≤ sz ∧
      ∃ o', b = fb m0 + BitVec.ofNat 64 o' ∧ o' + sz ≤ 5136 ∧ (o + 8 ≤ o' ∨ o' + sz ≤ o))
    {v : UInt64} (h : WordAt st.dmem (fb m0 + BitVec.ofNat 64 o) v) :
    WordAt m.dmem (fb m0 + BitVec.ofNat 64 o) v := by
  refine NativeRustcVm.Layout.WordAt.of_same h (n := 8) (fun j hj ↦ ?_) (Nat.le_refl _)
  rw [← hd]
  refine hm.get?_mem0 hwf fun ⟨w, hw, b, sz, hb, h1, h2⟩ ↦ ?_
  obtain ⟨hle, o', rfl, ho', hd'⟩ := hW w hw b sz hb
  rw [addr_add_add, fb_add hF (by omega)] at h1 h2
  rw [fb_add hF (by omega)] at h1 h2
  omega

variable [Host] {k : Nat}

theorem L1_eq (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.PlacementsOf.label_1 = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b3Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.PlacementsOf.b3Offset) NativeRustcVmArm.Vm.PlacementsOf.label_1_at

/-- **`b7`**: column `c` appended. -/
theorem append (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {c : Nat} (hc : c < 158)
    (hblk : isBlockF c = true) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b7Offset))
    (hI : I1 m0 c c st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b3Offset) ∧ I1 m0 (c + 1) c st'.data)
      st := by
  have hb := hI.body
  set n := (below c).length with hn
  have hn94 : n ≤ 94 := below_length_le hI.le
  have hk := Layout.readable_sub (o := 8 * c) (j := 8) hF.kr hb.kept
    (by unfold kappasBytes columnCountW; omega)
  have hko := Layout.offStack_sub (o := 8 * c) (j := 8) hF.ko hF.kr.2
    (by unfold kappasBytes columnCountW; omega) (by omega)
  have f1 := frame_readable hF hb (o := 8 * n) (n := 8) (by omega)
  have f2 := frame_readable hF hb (o := 1264 + 8 * n) (n := 8) (by omega)
  let env := Env.ofMachine st.data [(kk m0 + BitVec.ofNat 64 (8 * c), 8),
    (fb m0 + BitVec.ofNat 64 (8 * n), 8), (fb m0 + BitVec.ofNat 64 (1264 + 8 * n), 8)]
  have hwf : env.WF := Env.wf_of ⟨⟨hk.1, hk.2⟩, ⟨f1.1, f1.2⟩, ⟨f2.1, f2.2⟩, trivial⟩
    (List.Pairwise.cons (by
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact (frame_apart_off hF (by omega) hko).symm
        · exact (frame_apart_off hF (by omega) hko).symm)
      (List.Pairwise.cons (by
          intro e he
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          subst he
          exact frame_apart hF (by omega) (by omega) (by omega))
        (List.Pairwise.cons nofun .nil)))
  have h8 : (st.data.regs.getXReg .X8).toBitVec.toNat = c := hI.x8
  have h22 : (st.data.regs.getXReg .X22).toBitVec.toNat = n := hI.x22
  have hm : Match env l7S st.data :=
    match_ofMachine ⟨rfl, nofun, rfl, nofun, rfl, nofun, trivial⟩ rfl
    trivial trivial trivial
    ⟨by
      show (idx .X19 .X8).eval env = _
      rw [idx_eval]
      simp only [env, Env.ofMachine_regs, Env.base_ofMachine_eq, List.getElem?_cons_zero,
        Option.map_some, Option.getD_some, Layout.ofInt_zero, BitVec.add_zero, h8]
      rw [show st.data.regs.getXReg .X19 = m0.regs.X0 from hI.x19],
     by
      show (idx .X25 .X22).eval env = _
      rw [idx_eval]
      simp only [env, Env.ofMachine_regs, Env.base_ofMachine_eq, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.map_some, Option.getD_some, Layout.ofInt_zero,
        BitVec.add_zero, h22]
      rw [show (st.data.regs.getXReg .X25).toBitVec = fb m0 from hI.x25],
     by
      show (idx .X26 .X22).eval env = _
      rw [idx_eval]
      simp only [env, Env.ofMachine_regs, Env.base_ofMachine_eq, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.map_some, Option.getD_some, Layout.ofInt_zero,
        BitVec.add_zero, h22]
      rw [show (st.data.regs.getXReg .X26).toBitVec = fb m0 + BitVec.ofNat 64 1264 from hI.x26,
        addr_add_add], trivial⟩
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) run_b7 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨k7, w7, f7a, f7b⟩ := Arrays.after_eq run_b7 ▸ b7_facts
  have hregion : ∀ (r off n : Nat) (b : BitVec 64) (sz : Nat), ((r = 1 ∨ r = 2) ∧ off + n ≤ 8) →
      env.regions[r]? = some (b, sz) → off + n ≤ sz ∧
        ((b = fb m0 + BitVec.ofNat 64 (8 * (below c).length) ∧ sz = 8) ∨
          (b = fb m0 + BitVec.ofNat 64 (1264 + 8 * (below c).length) ∧ sz = 8)) := by
    intro r off n' b sz ⟨hr, hle⟩ hb'
    rcases hr with rfl | rfl <;>
      simp only [env, Env.ofMachine_regions, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Prod.mk.injEq] at hb' <;> obtain ⟨rfl, rfl⟩ := hb'
    · exact ⟨hle, .inl ⟨rfl, rfl⟩⟩
    · exact ⟨hle, .inr ⟨rfl, rfl⟩⟩
  have hb1 : Bd m0 st1.data := Bd.of_write hF hb hm hm1 hwf rfl k7 fun p hw ↦ by
    obtain ⟨w, hw', b, sz, hb', hin⟩ := written_in hwf hw fun w hw b sz hb' ↦
      (hregion _ _ _ b sz (w7 w hw) hb').1
    rcases (hregion _ _ _ b sz (w7 w hw') hb').2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨a1, a2⟩ := frame_low hF (by omega) hin; exact ⟨.inr a1, a2⟩
    · obtain ⟨a1, a2⟩ := frame_low hF (by omega) hin; exact ⟨.inr a1, a2⟩
  have keep : ∀ {o : Nat} {v : UInt64}, (o + 8 ≤ 8 * n ∨ (1264 ≤ o ∧ o + 8 ≤ 1264 + 8 * n)) →
      WordAt st.data.dmem (fb m0 + BitVec.ofNat 64 o) v →
      WordAt st1.data.dmem (fb m0 + BitVec.ofNat 64 o) v := fun ho h ↦
    keep_frame hF hm1 hwf rfl (by omega) (fun w hw b sz hb' ↦ by
      obtain ⟨hle, hc'⟩ := hregion _ _ _ b sz (w7 w hw) hb'
      rcases hc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hle, 8 * n, rfl, by omega, by omega⟩
      · exact ⟨hle, 1264 + 8 * n, rfl, by omega, by omega⟩) h
  have new1 : WordAt st1.data.dmem (fb m0 + BitVec.ofNat 64 (8 * n)) c.toUInt64 := by
    have := Layout.Match.wordAt_write hm1 (r := 1) (o := 0) rfl (by omega) f7a
    rw [addr_add_zero] at this
    convert this using 1
    apply UInt64.toNat.inj
    show c.toUInt64.toNat = (st.data.regs.getXReg .X8).toNat
    rw [show (st.data.regs.getXReg .X8).toNat = c from hI.x8]
    simp; omega
  have new2 : WordAt st1.data.dmem (fb m0 + BitVec.ofNat 64 (1264 + 8 * n)) (κ m0 c).toUInt64 := by
    have := Layout.Match.wordAt_write hm1 (r := 2) (o := 0) rfl (by omega) f7b
    rw [addr_add_zero] at this
    convert this using 1
    simp only [Sym.eval]
    rw [load_word', Env.ofMachine_mem0]
    simp only [env, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
      Option.getD_some, addr_add_zero, UInt64.ofBitVec_toBitVec]
    rw [kap_same hF hb hc, κ_eq m0 hc, toUInt64_toNat']
  have hbl : below (c + 1) = below c ++ [c] := by rw [below_succ, hblk]; rfl
  have hk22 := hm1.regs .X22 _ rfl
  sym_simp at hk22
  simp only [PcOk] at hpc1
  refine .done _ ⟨hpc1.trans (L1_eq hp), hb1, by omega,
    (by rw [show st1.data.regs.X8 = st.data.regs.X8 from
      Match.reg_eq hm hm1 (r := .X8) rfl rfl]; exact hI.x8),
    (by rw [show st1.data.regs.X21 = st.data.regs.X21 from
      Match.reg_eq hm hm1 (r := .X21) rfl rfl]; exact hI.x21),
    ?_,
    (by rw [show st1.data.regs.X19 = st.data.regs.X19 from
      Match.reg_eq hm hm1 (r := .X19) rfl rfl]; exact hI.x19),
    (by rw [show st1.data.regs.X20 = st.data.regs.X20 from
      Match.reg_eq hm hm1 (r := .X20) rfl rfl]; exact hI.x20),
    (by rw [show st1.data.regs.X23 = st.data.regs.X23 from
      Match.reg_eq hm hm1 (r := .X23) rfl rfl]; exact hI.x23),
    (by rw [show st1.data.regs.X24 = st.data.regs.X24 from
      Match.reg_eq hm hm1 (r := .X24) rfl rfl]; exact hI.x24),
    (by rw [show st1.data.regs.X25 = st.data.regs.X25 from
      Match.reg_eq hm hm1 (r := .X25) rfl rfl]; exact hI.x25),
    (by rw [show st1.data.regs.X26 = st.data.regs.X26 from
      Match.reg_eq hm hm1 (r := .X26) rfl rfl]; exact hI.x26),
    fun q hq ↦ ?_, fun q hq ↦ ?_⟩
  · show (st1.data.regs.getXReg .X22).toBitVec.toNat = _
    rw [hk22, hbl, List.length_append, ← hn, BitVec.toNat_add]
    rw [show (env.regs .X22).toNat = n from h22]
    simp; omega
  · simp only [hbl, List.length_append, List.length_singleton] at hq
    rcases Nat.lt_or_ge q n with hq' | hq'
    · rw [show (below (c + 1))[q] = (below c)[q] by
        simp only [hbl]; exact List.getElem_append_left hq']
      exact keep (.inl (by omega)) (hI.cols q hq')
    · obtain rfl : q = n := by omega
      rw [show (below (c + 1))[n] = c by
        simp only [hbl, hn]; exact List.getElem_concat_length rfl _]
      exact new1
  · simp only [hbl, List.length_append, List.length_singleton] at hq
    rcases Nat.lt_or_ge q n with hq' | hq'
    · rw [show (below (c + 1))[q] = (below c)[q] by
        simp only [hbl]; exact List.getElem_append_left hq']
      exact keep (.inr ⟨by omega, by omega⟩) (hI.sizes q hq')
    · obtain rfl : q = n := by omega
      rw [show (below (c + 1))[n] = c by
        simp only [hbl, hn]; exact List.getElem_concat_length rfl _]
      exact new2

omit [Host] in
theorem slotByte_255 {c : Nat} :
    (NativeRustcVm.Data.slotByte (slotF c)).toNat = 255 ↔ slotF c = none := by
  rw [← slotByte_none]
  constructor
  · intro h; apply UInt8.toNat.inj; rw [h]; rfl
  · intro h; rw [h]; rfl

omit [Host] in
/-- A block without memory keeps the registers no slot holds. -/
theorem rk {b : List Directive} {S' : SState} {x : Exit} (hx : exec b regsS = some (S', x))
    (hb : b ∈ [b1, b2, b3, b6, b8, b9, b10, b11, b12, b13, b14, b18, b19, b23, b24, b25, b28,
      b29] := by simp only [List.mem_cons, true_or, or_true]) :
    keepsAll regsS S' keptRegs = true :=
  Arrays.after_eq hx ▸ regs_keep b hb

/-- **A turn** from `.L2`: column `c` tested, appended if stacked; at `.L1`. -/
theorem turn1 (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {c : Nat} (hc : c < 158)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b4Offset)) (hI : I1 m0 c c st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b3Offset) ∧ I1 m0 (c + 1) c st'.data)
      st := by
  have hb := hI.body
  -- `b4`: the slot byte
  refine byte_step (infix_of b4_in_code (by simp [b4]) hp) run_b4 b4_keep hF hb hpc .keccakSlot
    (by rw [length_slot]; exact hc) hI.x23 hI.x8 (idxB_eval · .X23 .X8)
    fun st1 hpc1 hb1 hd1 hr1 hl1 _ ↦ ?_
  have hI1 : I1 m0 c c st1.data := hI.mono hb1 hd1 (hr1 .X8 rfl) (hr1 .X21 rfl) (hr1 .X22 rfl)
    (hr1 .X19 rfl) (hr1 .X20 rfl) (hr1 .X23 rfl) (hr1 .X24 rfl) (hr1 .X25 rfl) (hr1 .X26 rfl)
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  rw [hl1, sw32_beq _ (by decide), slot_get hc] at hpc1
  obtain ⟨f1, t1⟩ := Arrays.pc_cond hpc1
  by_cases hs : slotF c = none
  swap
  · refine .done _ ⟨(f1 (by simp [slotByte_255, hs])).trans (L1_eq hp), hI1.skip hc ?_⟩
    rw [isBlockF_eq c hc]; simp [hs]
  have hpc2 := pc_of (t1 (by rw [hs]; decide)) (show k + NativeRustcVmArm.Vm.PlacementsOf.b4Offset + b4.length = k + NativeRustcVmArm.Vm.PlacementsOf.b5Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.PlacementsOf.b4_next])
  -- `b5`: the output byte
  refine byte_step (infix_of b5_in_code (by simp [b5]) hp) run_b5 b5_keep hF hb1 hpc2 .keccakOutput
    (by rw [length_out]; exact hc) hI1.x24 hI1.x8 (idxB_eval · .X24 .X8)
    fun st2 hpc3 hb2 hd2 hr2 hl2 _ ↦ ?_
  have hI2 : I1 m0 c c st2.data := hI1.mono hb2 hd2 (hr2 .X8 rfl) (hr2 .X21 rfl) (hr2 .X22 rfl)
    (hr2 .X19 rfl) (hr2 .X20 rfl) (hr2 .X23 rfl) (hr2 .X24 rfl) (hr2 .X25 rfl) (hr2 .X26 rfl)
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  rw [hl2, sw32_beq _ (by decide), out_get hc] at hpc3
  obtain ⟨f2, t2⟩ := Arrays.pc_cond hpc3
  by_cases ho : outF c = false
  swap
  · refine .done _ ⟨(f2 (by simp [ho])).trans (L1_eq hp), hI2.skip hc ?_⟩
    rw [isBlockF_eq c hc]; simp [hs] at ho ⊢; exact ho
  have hpc4 := pc_of (t2 (by simp [ho])) (show k + NativeRustcVmArm.Vm.PlacementsOf.b5Offset + b5.length = k + NativeRustcVmArm.Vm.PlacementsOf.b6Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.PlacementsOf.b5_next])
  have hblk : isBlockF c = true := by rw [isBlockF_eq c hc]; simp [hs, ho]
  -- `b6`: room
  refine regs_step (infix_of b6_in_code (by simp [b6]) hp) run_b6
    (rk run_b6) hb2 hpc4 fun st3 hm3 hpc5 hb3 hd3 hr3 ↦ ?_
  have hI3 : I1 m0 c c st3.data := hI2.mono hb3 hd3 (hr3 .X8 rfl) (hr3 .X21 rfl) (hr3 .X22 rfl)
    (hr3 .X19 rfl) (hr3 .X20 rfl) (hr3 .X23 rfl) (hr3 .X24 rfl) (hr3 .X25 rfl) (hr3 .X26 rfl)
  simp only [PcOk] at hpc5
  sym_simp at hpc5
  have hn := below_length_le hI2.le
  have e22 : (Env.ofMachine st2.data []).regs .X22 = BitVec.ofNat 64 (below c).length :=
    BitVec.eq_of_toNat_eq (by
      show st2.data.regs.X22.toNat = _
      rw [hI2.x22, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  rw [e22, ofNat_ult' (by omega) (by decide)] at hpc5
  have hpc6 := pc_of ((Arrays.pc_cond hpc5).2 (by simp; omega))
    (show k + NativeRustcVmArm.Vm.PlacementsOf.b6Offset + b6.length = k + NativeRustcVmArm.Vm.PlacementsOf.b7Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.PlacementsOf.b6_next])
  exact append hp hF hc hblk hpc6 hI3

/-- **`.L1`** (`b3`): on to the next column, or out of the loop. -/
theorem l1 (hp : Placed code k) {m0 : MachineData} {c : Nat} (hc : c < 158) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b3Offset)) (hI : I1 m0 (c + 1) c st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ (c + 1 < 158 ∧ st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b4Offset) ∧
      I1 m0 (c + 1) (c + 1) st'.data) ∨ (c + 1 = 158 ∧ st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b8Offset) ∧
      I1 m0 158 158 st'.data)) st := by
  refine regs_step (infix_of b3_in_code (by simp [b3]) hp) run_b3 (rk run_b3) hI.body
    hpc fun st1 hm1 hpc1 hb1 hd1 hr1 ↦ ?_
  have h8 := hm1.regs .X8 _ rfl
  have h21 := hm1.regs .X21 _ rfl
  sym_simp at h8 h21
  have hx8 : st1.data.regs.X8.toNat = c + 1 := by
    show (st1.data.regs.getXReg .X8).toBitVec.toNat = _
    rw [h8, BitVec.toNat_add, show (Env.ofMachine st.data []).regs .X8 = st.data.regs.X8.toBitVec
      from rfl, UInt64.toNat_toBitVec, hI.x8]
    simp; omega
  have hx21 : st1.data.regs.X21.toNat = 1264 - 8 * (c + 1) := by
    show (st1.data.regs.getXReg .X21).toBitVec.toNat = _
    rw [h21, BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def]; show 8 % 2 ^ 64 ≤ st.data.regs.X21.toNat; rw [hI.x21]; omega)]
    show st.data.regs.X21.toNat - 8 % 2 ^ 64 = _
    rw [hI.x21]; omega
  have hI1 : I1 m0 (c + 1) (c + 1) st1.data :=
    ⟨hb1, hI.le, hx8, hx21, by rw [show st1.data.regs.X22 = _ from hr1 .X22 rfl]; exact hI.x22,
      (hr1 .X19 rfl).trans hI.x19,
      (hr1 .X20 rfl).trans hI.x20,
      by rw [show st1.data.regs.X23 = _ from hr1 .X23 rfl]; exact hI.x23,
      by rw [show st1.data.regs.X24 = _ from hr1 .X24 rfl]; exact hI.x24,
      by rw [show st1.data.regs.X25 = _ from hr1 .X25 rfl]; exact hI.x25,
      by rw [show st1.data.regs.X26 = _ from hr1 .X26 rfl]; exact hI.x26,
      hd1 ▸ hI.cols, hd1 ▸ hI.sizes⟩
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  have e21 : (Env.ofMachine st.data []).regs .X21 = BitVec.ofNat 64 (1264 - 8 * c) :=
    BitVec.eq_of_toNat_eq (by
      show st.data.regs.X21.toNat = _
      rw [hI.x21, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
  rw [e21, ofNat_beq' (by omega) (by decide)] at hpc1
  obtain ⟨f, t⟩ := Arrays.pc_cond hpc1
  by_cases hlast : c + 1 = 158
  · refine .done _ (.inr ⟨hlast, (f (by simp; omega)).trans (hp.label (j := NativeRustcVmArm.Vm.PlacementsOf.b8Offset) NativeRustcVmArm.Vm.PlacementsOf.label_6_at), ?_⟩)
    rw [← hlast]; exact hlast ▸ hI1
  · exact .done _ (.inl ⟨by omega, pc_of (t (by simp; omega)) rfl, hI1⟩)

end

end NativeRustcVmArm.Layout.PlacementsOf
