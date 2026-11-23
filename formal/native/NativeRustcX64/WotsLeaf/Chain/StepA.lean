module

public import NativeRustcX64.WotsLeaf.Chain.StepB

/-!
# A chain step, part A: the payload, the address, `P` and the address absorbed

From `b17` (directive 191, `Run.AtStep`): the payload (the current value and `i` as a `u128`) at
`672`, the address of step `p` at `472` and `memset` of hasher A at `112` (`b17`, `seg_b17`), `P`
buffered (`b18`, `seg_b18`), `p + 1` at `56` (`b21`), the inlined `update`'s loop copying the
address into A's buffer after `P` (`b24`, `b25`, `b26`, its `memcpy`, `b27`, `b23`,
`seg_b21`); then `b31` (directive 359).
-/

namespace NativeRustcX64.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcX64.Sym NativeRustcX64.Xmss.WotsLeaf Chain
open LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The byte `b17` stores at `479`: `t | p << 5`. -/
def stepByteSym : Sym :=
  .un .trunc .W8 (.bin .merge .W8 (.bin .merge .W8 (.un .trunc .W32 (.reg .r14))
    (.bin .shl .W8 (.un .trunc .W32 (.reg .r14)) (.lit 5))) (.bin .add .W8 (.bin .merge .W8
      (.un .trunc .W32 (.reg .r14)) (.bin .shl .W8 (.un .trunc .W32 (.reg .r14)) (.lit 5))) (.lit 1)))

end

public section

theorem length_regBytes' (v : BitVec 64) : (regBytes v).length = 8 := length_regBytes v

theorem length_u32Bytes' (x : UInt32) : (u32Bytes x).length = 4 := by
  simp [u32Bytes, Native.XmssVerifier.bytes]

theorem length_addr (r : Run) (t : UInt8) (p : Nat) : (r.addr t p).length = 16 := by
  simp [Run.addr, address, length_u32Bytes']

theorem length_pp (r : Run) : r.pp.length = 16 := length_bytesOf _ _ _

theorem length_u128Bytes (i : Nat) : (u128Bytes i).length = 16 := by
  simp [u128Bytes, length_wordBytes]

section
variable [Labels]

/-- A 4-byte word the frame holds as a value's bytes loads as the value. -/
theorem load_word4 {r : Run} {m : MachineData} {extra : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {o : Nat} {v : BitVec 64} (hv : v.toNat < 2 ^ 32)
    (h : BytesAt m.dmem (r.off o) ((List.range 4).map (byteOf v))) :
    (r.envR m extra ret).load 0 o 4 = v := by
  rw [Env.load_of_bytesAt (by simp) h]
  have hb := Sym.ofBytes_byteOf v 0 4
  simp only [Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at hb
  rw [hb, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  omega

/-- **The step's byte**: `1 | p << 5`. -/
theorem bytes_step (env : Env) {p : Nat} (hp : p < 3) (h : env.regs .r14 = BitVec.ofNat 64 p) :
    (List.range 1).map (byteOf (stepByteSym.eval env)) = [(1 : UInt8) ||| p.toUInt8 <<< 5] := by
  simp only [stepByteSym, Sym.eval, h]
  rcases (show p = 0 ∨ p = 1 ∨ p = 2 by omega) with rfl | rfl | rfl <;> decide

end

theorem hi16_lt (r : Run) : r.hi16.toNat < 2 ^ 32 := by
  rw [Run.hi16, BinOp.apply, toNat_ext]
  exact BitVec.isLt _

/-- The `u128` payload's high half: `i`'s word and zeros. -/
theorem u128Bytes_eq (i : Nat) : u128Bytes i = wordBytes i.toUInt64 ++ List.replicate 8 0 := rfl

variable [Host] {r : Run}

/-- **`b26`, `b27`, `b23`**: the address copied into A's buffer after `P`, `buf_len` 32; then
`b31`. -/
theorem seg_b26 (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre) {i p : Nat}
    (hp3 : p < 3) {ad P : List UInt8} (had : ad.length = 16) (hP : P.length = 32)
    {R : MachineState → Prop} {m : MachineData}
    (hK : Keep r (r.stepSlots i ++ [(56, 8, regBytes (BitVec.ofNat 64 (p + 1))), (672, 32, P),
      (112, 200, List.replicate 200 0), (312, 16, r.pp), (472, 16, ad),
      (448, 8, regBytes (BitVec.ofNat 64 16))]) m)
    (hdi : Run.RegIs m .rdi (BitVec.ofNat 64 16)) (h15 : Run.RegIs m .r15 (BitVec.ofNat 64 16))
    (hbx : Run.RegIs m .rbx (r.off 472)) (h14 : Run.RegIs m .r14 (BitVec.ofNat 64 16))
    (h12 : Run.RegIs m .r12 (r.off 112))
    (h13 : Run.RegIs m .r13 (Labels.label "memcpy").toBitVec)
    (cont : StepCont r i p (r.pp ++ ad ++ P) R) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b26Offset⟩ := by
  -- `b26`: `memcpy` of the address.
  refine frameCall r hp hpre b26_in_code (List.cons_ne_nil _ _) run_b26 (by decide) rfl hK
    trivial extraOK_nil ⟨known_lit hdi, known_lit h15, known_ptr hbx, h13, trivial⟩ trivial trivial
    hc.1 fun m₁ hm₁ hK₁ _ ↦ ?_
  obtain ⟨-, -, -, -, ⟨-, -, had₁⟩, -⟩ := allOf_right hK₁.2
  obtain ⟨hpre₁, hpost₁⟩ := memcpyFrame hpre hK₁ (regIs_ptr hm₁ rfl) (regIs_ptr hm₁ rfl)
    (toNat_of_lit hm₁ rfl (by decide)) (by decide) (by decide) (by decide) rfl had had₁
  refine ⟨hpre₁, fun m₂ hsp hQ ↦ ?_⟩
  obtain ⟨hK₂, hS₂, -, hB⟩ := hpost₁ m₂ hsp hQ
  obtain ⟨t56, t672, t112, ⟨-, -, hpp₂⟩, -, ⟨-, -, h448⟩, -⟩ := allOf_right hK₂.2
  have hK₂' : Keep r (r.stepSlots i ++ [(56, 8, regBytes (BitVec.ofNat 64 (p + 1))), (672, 32, P),
      (112, 200, List.replicate 200 0), (312, 32, r.pp ++ ad)]) m₂ :=
    hK₂.left.add ⟨t56, t672, t112, ⟨by simp only [List.length_append, length_pp, had],
      by norm_num, BytesAt.cat hpp₂ hB (by rw [length_pp])⟩, trivial⟩
  have h15₂ : Run.RegIs m₂ .r15 (BitVec.ofNat 64 16) := RegIs.of_saved hS₂ rfl (regIs_lit hm₁ rfl)
  have h14₂ : Run.RegIs m₂ .r14 (BitVec.ofNat 64 16) :=
    RegIs.of_saved hS₂ rfl (regIs_reg hm₁ rfl h14)
  have hbx₂ : Run.RegIs m₂ .rbx (r.off 472) := RegIs.of_saved hS₂ rfl (regIs_ptr hm₁ rfl)
  have h12₂ : Run.RegIs m₂ .r12 (r.off 112) := RegIs.of_saved hS₂ rfl (regIs_reg hm₁ rfl h12)
  have h13₂ : Run.RegIs m₂ .r13 (Labels.label "memcpy").toBitVec :=
    RegIs.of_saved hS₂ rfl (hm₁.regs .r13 _ rfl)
  -- `b27`: `buf_len` 32.
  have hm₀ := match_seeded (match_frameS
    (fun _ hl _ hi => r.got_byte hpre hK₂'.1.2.2.1 hl hi) hK₂'.1.1 (sextra := []) (extra := [])
    (ret := (r.pc (NativeRustcX64.Xmss.WotsLeaf.b27Offset + b27.length)).toBitVec) (k := [(.r15, .lit 16)]) (bounds := [])
    (aliases := []) trivial ⟨known_lit h15₂, trivial⟩ trivial trivial)
    h448
  refine frameStepS r hp hpre b27_in_code (List.cons_ne_nil _ _) run_b27 (by decide) rfl hK₂'
    extraOK_nil hm₀ fun st3 hm3 hK3 _ hpc3 ↦ ?_
  have h32 : BytesAt st3.data.dmem (r.off 448) (regBytes (BitVec.ofNat 64 32)) :=
    frame_covers hm3 (o := 448) (n := 8) (v := .lit 32) (by decide) (by decide +kernel)
  refine pc_at ((pc_true hpc3).trans (Run.label_of_block r hp b23_in_code rfl)) ?_
  obtain ⟨u56, u672, u112, u312, -⟩ := allOf_right hK3.2
  have hK3' : Keep r (r.stepSlots i ++ [(56, 8, regBytes (BitVec.ofNat 64 (p + 1))), (672, 32, P),
      (112, 200, List.replicate 200 0), (312, 32, r.pp ++ ad),
      (448, 8, regBytes (BitVec.ofNat 64 32))]) st3.data :=
    hK3.left.add ⟨u56, u672, u112, u312, ⟨length_regBytes _, by norm_num, h32⟩, trivial⟩
  -- `b23`: the loop's end.
  refine frameStep r hp hpre b23_in_code (List.cons_ne_nil _ _) run_b23 (by decide) rfl hK3'
    trivial extraOK_nil ⟨known_lit (regIs_reg hm3 rfl h14₂), known_lit (regIs_lit hm3 rfl),
      known_ptr (regIs_reg hm3 rfl hbx₂), trivial⟩ trivial trivial fun st4 hm4 hK4 _ hpc4 ↦ ?_
  refine pc_at ((pc_true hpc4).trans (Run.label_of_block r hp b31_in_code rfl)) ?_
  exact seg_b31 hp hc hpre hp3 (by simp only [List.length_append, length_pp, had]) hP hK4
    (regIs_reg hm4 rfl (regIs_reg hm3 rfl h12₂))
    (regIs_reg hm4 rfl (regIs_reg hm3 rfl h13₂)) cont

/-- **`b21`, `b24`, `b25`**: `p + 1` at `56`, the loop's first bounds; then `b26`. -/
theorem seg_b21 (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre) {i p : Nat}
    (hp3 : p < 3) {ad P : List UInt8} (had : ad.length = 16) (hP : P.length = 32)
    {R : MachineState → Prop} {m : MachineData}
    (hK : Keep r (r.stepSlots i ++ [(672, 32, P), (112, 200, List.replicate 200 0),
      (312, 16, r.pp), (472, 16, ad), (448, 8, regBytes (BitVec.ofNat 64 16))]) m)
    (hdi : Run.RegIs m .rdi (BitVec.ofNat 64 16)) (h14 : Run.RegIs m .r14 (BitVec.ofNat 64 p))
    (h12 : Run.RegIs m .r12 (r.off 112))
    (h13 : Run.RegIs m .r13 (Labels.label "memcpy").toBitVec)
    (cont : StepCont r i p (r.pp ++ ad ++ P) R) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b21Offset⟩ := by
  refine frameStep r hp hpre b21_in_code (List.cons_ne_nil _ _) run_b21 (by decide) rfl hK
    trivial extraOK_nil trivial trivial trivial fun st1 hm1 hK1 _ hpc1 ↦ ?_
  have h56 : BytesAt st1.data.dmem (r.off 56) (regBytes (BitVec.ofNat 64 (p + 1))) := by
    have := frame_covers hm1 (o := 56) (n := 8) (v := .bin .add .W64 (.reg .r14) (.lit 1))
      (by decide) (by decide +kernel)
    have e : (Sym.bin .add .W64 (.reg .r14) (.lit 1)).eval
        (r.envR m [] (r.pc (NativeRustcX64.Xmss.WotsLeaf.b21Offset + b21.length)).toBitVec) = BitVec.ofNat 64 (p + 1) := by
      show BinOp.apply .add .W64 (m.regs.get64 .r14) (BitVec.ofNat 64 1) = _
      rw [show m.regs.get64 .r14 = BitVec.ofNat 64 p from h14]
      simp only [BinOp.apply, low_W64, ext_W64]
      rw [BitVec.ofNat_add]
    rw [e] at this
    exact this
  obtain ⟨s672, s112, s312, s472, s448, -⟩ := allOf_right hK1.2
  have hK1' : Keep r (r.stepSlots i ++ [(56, 8, regBytes (BitVec.ofNat 64 (p + 1))), (672, 32, P),
      (112, 200, List.replicate 200 0), (312, 16, r.pp), (472, 16, ad),
      (448, 8, regBytes (BitVec.ofNat 64 16))]) st1.data :=
    hK1.left.add ⟨⟨length_regBytes _, by norm_num, h56⟩, s672, s112, s312, s472, s448, trivial⟩
  refine pc_at (hpc1.trans (Run.label_of_block r hp b24_in_code rfl)) ?_
  have hdi1 := regIs_reg hm1 rfl hdi
  have h12₁ := regIs_reg hm1 rfl h12
  -- `b24`, `b25`: the bounds.
  refine frameStep r hp hpre b24_in_code (List.cons_ne_nil _ _) run_b24 (by decide) rfl hK1'
    trivial extraOK_nil ⟨known_lit hdi1, known_lit (regIs_lit hm1 rfl),
      known_ptr (regIs_ptr hm1 rfl), trivial⟩ trivial trivial fun st2 hm2 hK2 _ hpc2 ↦ ?_
  refine pc_at (pc_false hpc2) ?_
  refine frameStep r hp hpre b25_in_code (List.cons_ne_nil _ _) run_b25 (by decide) rfl hK2
    trivial extraOK_nil ⟨known_lit (regIs_lit hm2 rfl), trivial⟩ trivial trivial
    fun st3 hm3 hK3 _ hpc3 ↦ ?_
  refine pc_at (pc_false hpc3) ?_
  exact seg_b26 hp hc hpre hp3 had hP hK3 (regIs_reg hm3 rfl (regIs_lit hm2 rfl))
    (regIs_reg hm3 rfl (regIs_lit hm2 rfl)) (regIs_reg hm3 rfl (regIs_ptr hm2 rfl))
    (regIs_reg hm3 rfl (regIs_lit hm2 rfl)) (regIs_reg hm3 rfl (regIs_reg hm2 rfl h12₁))
    (regIs_reg hm3 rfl (regIs_reg hm2 rfl (regIs_reg hm1 rfl h13))) cont

/-- **`b18`**: `P` buffered in A, `buf_len` 16; then `b21`. -/
theorem seg_b18 (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre) {i p : Nat}
    (hp3 : p < 3) {ad P : List UInt8} (had : ad.length = 16) (hP : P.length = 32)
    {R : MachineState → Prop} {m : MachineData}
    (hK : Keep r (r.stepSlots i ++ [(672, 32, P), (112, 200, List.replicate 200 0),
      (472, 16, ad)]) m)
    (h448 : BytesAt m.dmem (r.off 448) (regBytes (BitVec.ofNat 64 0)))
    (h14 : Run.RegIs m .r14 (BitVec.ofNat 64 p)) (h12 : Run.RegIs m .r12 (r.off 112))
    (h13 : Run.RegIs m .r13 (Labels.label "memcpy").toBitVec)
    (cont : StepCont r i p (r.pp ++ ad ++ P) R) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b18Offset⟩ := by
  have hin := r.pre_pp hpre
  have h104 := (stepSlots_chain hK.2).2.2.2.2.1.2.2
  have hm₀ := match_seeded (match_frameS
    (fun _ hl _ hi => r.got_byte hpre hK.1.2.2.1 hl hi) hK.1.1 (sextra := [16])
    (extra := [(reg r.m0 .rsi, 16)]) (ret := (r.pc (NativeRustcX64.Xmss.WotsLeaf.b18Offset + b18.length)).toBitVec) (k := [])
    (bounds := [])
    (aliases := [(.load 0 104 8, (4, 0))]) ⟨rfl, trivial⟩ trivial trivial ⟨by
      show (r.envR m [(reg r.m0 .rsi, 16)] _).load 0 104 8 = reg r.m0 .rsi + BitVec.ofInt 64 0
      rw [r.load_word h104]
      simp, trivial⟩) h448
  refine frameStepS r hp hpre b18_in_code (List.cons_ne_nil _ _) run_b18 (by decide) rfl hK
    (r.extraOK_input hpre hK.1.2.2.2 hin
      (fun l hl => ((r.got hpre).1 l hl).2.2.2 (reg r.m0 .rsi, 16) (by simp))) hm₀ fun st hm hK1 _ hpc ↦ ?_
  have hpp0 : BytesAt m.dmem (reg r.m0 .rsi + BitVec.ofNat 64 0) r.pp := by
    rw [BitVec.add_zero]
    exact r.input_bytes hpre ((r.frame_iff m).1 hK.1) hin
  have hpp : BytesAt st.data.dmem (r.off 312) r.pp :=
    copy16 hm (k := 0) (b := r.base) (sz := 2784) rfl (o := 312) (k' := 4) (o' := 0) (by decide)
      (by decide +kernel) (by decide +kernel) (length_pp r) hpp0
  have h16 : BytesAt st.data.dmem (r.off 448) (regBytes (BitVec.ofNat 64 16)) :=
    frame_covers hm (o := 448) (n := 8) (v := .lit 16) (by decide) (by decide +kernel)
  obtain ⟨s672, s112, s472, -⟩ := allOf_right hK1.2
  refine pc_at ((pc_true hpc).trans (Run.label_of_block r hp b21_in_code rfl)) ?_
  exact seg_b21 hp hc hpre hp3 had hP
    (hK1.left.add ⟨s672, s112, ⟨length_pp r, by norm_num, hpp⟩, s472,
      ⟨length_regBytes _, by norm_num, h16⟩, trivial⟩)
    (regIs_lit hm rfl) (regIs_reg hm rfl h14) (regIs_reg hm rfl h12)
    (regIs_reg hm rfl h13) cont

/-- **`b17`**: the payload at `672`, the step's address at `472`, `memset` of hasher A; then
`b18`. -/
theorem seg_b17 (hp : Placed Xmss.WotsLeaf.code r.k) (hc : Callees) (hpre : r.Pre) {i p : Nat}
    (hp3 : p < 3) {cur : List UInt8} (hcur : cur.length = 16) {R : MachineState → Prop}
    {m : MachineData} (hA : r.AtStep i p cur m)
    (cont : StepCont r i p (r.pp ++ r.addr 1 p ++ (cur ++ u128Bytes i)) R) :
    Eventually (step1 Host.exe) R ⟨m, r.pc NativeRustcX64.Xmss.WotsLeaf.b17Offset⟩ := by
  obtain ⟨hK, h80, h14, hdx, h12, h13, hbx⟩ := hA
  obtain ⟨s8, s48, s52, -, -, -, -⟩ : SlotsAt r m r.chainSlots :=
    allOf_left (allOf_left (allOf_left hK.2))
  refine frameCall r hp hpre b17_in_code (List.cons_ne_nil _ _) run_b17 (by decide) rfl hK
    trivial extraOK_nil ⟨hbx, trivial⟩ trivial trivial hc.2.1 fun m₁ hm₁ hK₁ _ ↦ ?_
  -- The payload.
  have p1 := frame_copy16 hm₁ (o := 672) (o' := 80) (by decide) (by decide +kernel)
    (by decide +kernel) hcur h80
  have p2 : BytesAt m₁.dmem (r.off 688) (wordBytes i.toUInt64) := by
    have := frame_covers hm₁ (o := 688) (n := 8) (v := .reg .rdx) (by decide) (by decide +kernel)
    rw [show (Sym.reg .rdx).eval (r.envR m [] (r.pc (NativeRustcX64.Xmss.WotsLeaf.b17Offset + b17.length)).toBitVec) =
      BitVec.ofNat 64 i from hdx] at this
    rw [← regBytes_ofNat]
    exact this
  have p3 : BytesAt m₁.dmem (r.off 696) (List.replicate 8 0) := by
    have := frame_covers hm₁ (o := 696) (n := 8) (v := .lit 0) (by decide) (by decide +kernel)
    rwa [show (Sym.lit 0).eval (r.envR m [] (r.pc (NativeRustcX64.Xmss.WotsLeaf.b17Offset + b17.length)).toBitVec) =
      BitVec.ofNat 64 0 from rfl, bytes_zero] at this
  have hpay : BytesAt m₁.dmem (r.off 672) (cur ++ u128Bytes i) :=
    BytesAt.cat p1 (BytesAt.cat p2 p3 (by rw [length_wordBytes])) (by rw [hcur])
  -- The address.
  have a1 := covers_load hm₁ (o := 472) (n := 4) (o' := 52) (by decide) (by decide)
    (by decide +kernel) (length_u32Bytes' r.e) s52.2.2
  have a2 : BytesAt m₁.dmem (r.off 476) ((u32Bytes r.hi).take 2) := by
    have := frame_covers hm₁ (o := 476) (n := 2) (v := .un .trunc .W16 (.load 0 8 8)) (by decide)
      (by decide +kernel)
    rw [show (Sym.un .trunc .W16 (.load 0 8 8)).eval
        (r.envR m [] (r.pc (NativeRustcX64.Xmss.WotsLeaf.b17Offset + b17.length)).toBitVec) = UnOp.apply .trunc .W16 r.layerW by
      show UnOp.apply .trunc .W16 ((r.envR m [] _).load 0 8 8) = _
      rw [r.load_word s8.2.2], bytes_layerW16] at this
    exact this
  have a3 : BytesAt m₁.dmem (r.off 478) (((u32Bytes r.hi).drop 2).take 1) := by
    have := frame_covers hm₁ (o := 478) (n := 1) (v := .un .trunc .W8 (.load 0 48 4)) (by decide)
      (by decide +kernel)
    rw [show (Sym.un .trunc .W8 (.load 0 48 4)).eval
        (r.envR m [] (r.pc (NativeRustcX64.Xmss.WotsLeaf.b17Offset + b17.length)).toBitVec) = UnOp.apply .trunc .W8 r.hi16 by
      show UnOp.apply .trunc .W8 ((r.envR m [] _).load 0 48 4) = _
      rw [load_word4 (hi16_lt r) s48.2.2], byte_hi16] at this
    exact this
  have a4 : BytesAt m₁.dmem (r.off 479) [(1 : UInt8) ||| p.toUInt8 <<< 5] := by
    have := frame_covers hm₁ (o := 479) (n := 1) (v := stepByteSym) (by decide)
      (by decide +kernel)
    rwa [bytes_step (r.envR m [] (r.pc (NativeRustcX64.Xmss.WotsLeaf.b17Offset + b17.length)).toBitVec) hp3 h14] at this
  have a5 : BytesAt m₁.dmem (r.off 480) (List.replicate 8 0) := by
    have := frame_covers hm₁ (o := 480) (n := 8) (v := .lit 0) (by decide) (by decide +kernel)
    rwa [show (Sym.lit 0).eval (r.envR m [] (r.pc (NativeRustcX64.Xmss.WotsLeaf.b17Offset + b17.length)).toBitVec) =
      BitVec.ofNat 64 0 from rfl, bytes_zero] at this
  have had : BytesAt m₁.dmem (r.off 472) (r.addr 1 p) := by
    rw [Run.addr_eq]
    refine BytesAt.cat a1 (BytesAt.cat a2 (BytesAt.cat a3 (BytesAt.cat a4 a5 rfl) ?_) ?_) ?_
    · simp [u32Bytes, Native.XmssVerifier.bytes]
    · simp [u32Bytes, Native.XmssVerifier.bytes]
    · rw [length_u32Bytes']
  -- `memset` of hasher A.
  have hK₁' : CallKeep r (r.stepSlots i ++ [(472, 16, r.addr 1 p), (672, 32, cur ++ u128Bytes i)])
      m₁ :=
    hK₁.add ⟨⟨length_addr r 1 p, by norm_num, had⟩,
      ⟨by simp only [List.length_append, hcur, length_u128Bytes], by norm_num, hpay⟩, trivial⟩
  obtain ⟨hpre₁, hpost₁⟩ := memsetFrame hpre hK₁' (regIs_of_reg hm₁ rfl h12) (byte_zero hm₁ rfl)
    (toNat_of_lit hm₁ rfl (by decide)) (by decide) rfl
  refine ⟨hpre₁, fun m₂ hsp hQ ↦ ?_⟩
  obtain ⟨hK₂, hS₂, -, hZ⟩ := hpost₁ m₂ hsp hQ
  obtain ⟨t472, t672, -⟩ := allOf_right hK₂.2
  have hZ0 : BytesAt m₂.dmem (r.off 112) (List.replicate 200 0) := by
    have := take_of_bytesAt hZ 200
    rwa [List.take_replicate, show min 200 344 = 200 from rfl] at this
  have hZ448 : BytesAt m₂.dmem (r.off 448) (regBytes (BitVec.ofNat 64 0)) := by
    rw [regBytes_zero]
    have := BytesAt.sub hZ 336 8
    rwa [List.drop_replicate, List.take_replicate] at this
  exact seg_b18 hp hc hpre hp3 (length_addr r 1 p)
    (by simp only [List.length_append, hcur, length_u128Bytes])
    (hK₂.left.add ⟨t672, ⟨by simp only [List.length_replicate], by norm_num, hZ0⟩, t472, trivial⟩)
    hZ448 (RegIs.of_saved hS₂ rfl (regIs_reg hm₁ rfl h14))
    (RegIs.of_saved hS₂ rfl (regIs_reg hm₁ rfl h12))
    (RegIs.of_saved hS₂ rfl (regIs_reg hm₁ rfl h13)) cont

end

end NativeRustcX64.WotsLeafProof
