module

public import NativeRustcArm.WotsLeaf.Chain.Exec
public import NativeRustcArm.WotsLeaf.Codeword.Facts
public import NativeRustcArm.WotsLeaf.Leaf.Bytes
public import NativeRustcArm.SphincsVerify.InlineTh.Final
public import NativeRustcArm.SphincsVerify.InlineTh.Model

/-!
# What the chains keep

Through the chains the frame's invariant, its fixed slots (`Run.cSlots`: `out`, the chain values'
address, `hi >> 16`, `e`, `hi`, the codeword) and the ends so far `E` at 440 stay (`Run.CK`): the
chains' blocks and calls write the frame only from byte 1368 on, past the 58 ends (`CK.of_block`,
`CK.of_blockR`, `CK.of_call`). The registers through a step (`Run.SRegs`). Bytes a block writes
(`frame_copy16`, `frame_write_zero`), a chain step's bytes (`bytes_word`, `byte_tstep`), `th` of a
short input (`th_short`).
-/

namespace NativeRustcArm.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcArm.Sym Chain
open NativeRustcArm.SphincsVerifyProof.InlineTh LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The chains' fixed slots: `out`, the values' address, `hi >> 16`, `e`, `hi`, the codeword. -/
def Run.cSlots (r : Run) (x : List UInt8) : List Slot :=
  [(0, 8, wordBytes r.m0.regs.X0), (8, 8, wordBytes r.m0.regs.X7), (20, 4, u32Bytes (r.hi >>> 16)),
    (24, 4, u32Bytes r.e), (28, 4, u32Bytes r.hi), (380, 58, x)]

/-- **What the chains keep**: the fixed slots, the ends so far `E` at 440. -/
def Run.CK (r : Run) (x E : List UInt8) (m : MachineData) : Prop :=
  Keep r (r.cSlots x) m ∧ BytesAt m.dmem (r.off 440) E ∧ E.length ≤ 928

/-- **The registers through a step**: X19 `136`, X20 `P`'s address, X21 and X23 the hashers'
buffers, X22 the step's position, X28 the chain. -/
def Run.SRegs (r : Run) (m : MachineData) (pos i : Nat) : Prop :=
  Run.RegIs m .X19 (BitVec.ofNat 64 136) ∧ Run.RegIs m .X20 r.m0.regs.X1.toBitVec ∧
    Run.RegIs m .X21 (r.off 1976) ∧ Run.RegIs m .X23 (r.off 1632) ∧
    Run.RegIs m .X22 (BitVec.ofNat 64 pos) ∧ Run.RegIs m .X28 (BitVec.ofNat 64 i)

/-- Each of the `n` bytes at `o` in region `r` is a byte of a zero literal's newest write. -/
def zeroAt (ws : List Write) (r o n : Nat) : Bool :=
  (List.range n).all fun i ↦ match findWrite r (o + i) ws with
    | some (.lit 0, _) => true
    | _ => false

end

public section

theorem chainSlots_eq (r : Run) (x E : List UInt8) :
    r.chainSlots x E = r.cSlots x ++ [(440, E.length, E)] := rfl

theorem cSlots_kept (r : Run) (x : List UInt8) {S : SState} (h : Run.noWriteIn S 0 440 = true) :
    slotsKept S (r.cSlots x) = true := by
  simp only [slotsKept, Run.cSlots, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨noWriteIn_mono h (by omega) (by omega), noWriteIn_mono h (by omega) (by omega),
    noWriteIn_mono h (by omega) (by omega), noWriteIn_mono h (by omega) (by omega),
    noWriteIn_mono h (by omega) (by omega), noWriteIn_mono h (by omega) (by omega)⟩

theorem cSlots_off (r : Run) (x : List UInt8) {a n : Nat} (ha : 1368 ≤ a) :
    slotsOff (r.cSlots x) a n = true := by
  simp only [slotsOff, Run.cSlots, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq]
  omega

theorem take_of_bytesAt {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs)
    (n : Nat) : BytesAt d a (bs.take n) :=
  BytesAt.left (cs := bs.drop n) (by rwa [List.take_append_drop])

section
variable {r : Run} [Labels]

/-- **A block of the frame writing from byte 1368 on keeps what the chains keep.** -/
theorem CK.of_block (hpre : r.Pre) {x E : List UInt8} {m m' : MachineData}
    (hK : r.CK x E m) {vars : Nat → BitVec 64} {S : SState} (hm : Match (r.env m vars) S m')
    (hwf : (r.env m vars).WF) (hok : blockOK S = true) (hw : Run.noWriteIn S 0 1368 = true) :
    r.CK x E m' :=
  ⟨hK.1.of_block hpre hm hwf hok (cSlots_kept r x (noWriteIn_mono hw (by omega) (by omega))),
    r.bytesAt_kept hpre hm hwf (by have := hK.2.2; omega) hK.2.1
      (noWriteIn_mono hw (by omega) (by have := hK.2.2; omega)),
    hK.2.2⟩

/-- Slots a block in the frame's environment with more regions does not write stay. -/
theorem SlotsAt.of_blockR (hpre : r.Pre) {m m' : MachineData} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {S : SState} (hm : Match (r.envR m rest vars) S m')
    (hwf : (r.envR m rest vars).WF) (hin : Run.inRegions S = true) {L : List Slot}
    (h : SlotsAt r m L) (hL : slotsKept S L = true) : SlotsAt r m' L :=
  allOf_imp (fun s hs ⟨hl, ho, hb⟩ ↦ ⟨hl, ho, r.bytesAt_keptR hpre hm hwf hin (by omega) hb
    (by rw [hl]; exact slotsKept_spec hL s hs)⟩) h

/-- **A block with more regions, writing the frame from byte 1368 on, keeps what the chains
keep.** -/
theorem CK.of_blockR (hpre : r.Pre) {x E : List UInt8} {m m' : MachineData}
    (hK : r.CK x E m) {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (r.envR m rest vars) S m') (hwf : (r.envR m rest vars).WF)
    (hin : Run.inRegions S = true) (hfw : Run.frameWrites S = true) (hsp : S.sp = .ptr 0 0)
    (h29 : S.reg .X29 = some (.ptr 0 2656)) (hw : Run.noWriteIn S 0 1368 = true) :
    r.CK x E m' :=
  ⟨⟨Run.Frame.of_match r hpre hK.1.1 hm hwf hsp h29 hfw,
      hK.1.2.of_blockR hpre hm hwf hin
        (cSlots_kept r x (noWriteIn_mono hw (by omega) (by omega)))⟩,
    r.bytesAt_keptR hpre hm hwf hin (by have := hK.2.2; omega) hK.2.1
      (noWriteIn_mono hw (by omega) (by have := hK.2.2; omega)),
    hK.2.2⟩

omit [Labels] in
/-- **A call changing the frame from byte 1368 on keeps what the chains keep.** -/
theorem CK.of_call {x E : List UInt8} {m₁ m₂ : MachineData} (hK : r.CK x E m₁)
    (hK₂ : Keep r (r.cSlots x) m₂) {a n : Nat} (hc : KC r m₁ m₂ a n) (ha : 1368 ≤ a) :
    r.CK x E m₂ :=
  ⟨hK₂, hc 440 E (by have := hK.2.2; omega) (by have := hK.2.2; omega) hK.2.1, hK.2.2⟩

omit [Labels] in
theorem SRegs.of_saved {m m' : MachineData} (hS : Saved m m') {pos i : Nat}
    (h : r.SRegs m pos i) : r.SRegs m' pos i :=
  ⟨RegIs.of_saved hS rfl h.1, RegIs.of_saved hS rfl h.2.1, RegIs.of_saved hS rfl h.2.2.1,
    RegIs.of_saved hS rfl h.2.2.2.1, RegIs.of_saved hS rfl h.2.2.2.2.1,
    RegIs.of_saved hS rfl h.2.2.2.2.2⟩

/-- The registers a block of the frame keeps. -/
theorem SRegs.of_block {m m' : MachineData} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (r.env m vars) S m') (h19 : S.reg .X19 = some (.lit 136))
    (h20 : S.reg .X20 = some (.reg .X20)) (h21 : S.reg .X21 = some (.ptr 0 1976))
    (h23 : S.reg .X23 = some (.ptr 0 1632)) (h22 : S.reg .X22 = some (.reg .X22))
    (h28 : S.reg .X28 = some (.reg .X28)) {pos i : Nat} (h : r.SRegs m pos i) :
    r.SRegs m' pos i :=
  ⟨regIs_lit hm h19, regIs_reg hm h20 h.2.1, regIs_ptr hm h21, regIs_ptr hm h23,
    regIs_reg hm h22 h.2.2.2.2.1, regIs_reg hm h28 h.2.2.2.2.2⟩

/-- The registers `keptK` are known. -/
theorem knownK {m : MachineData} {pos i : Nat} (h : r.SRegs m pos i) {k : List (XReg × Sym)}
    (hk : KnownOK r m k) : KnownOK r m (k ++ keptK) :=
  allOf_append hk ⟨known_lit h.1, known_ptr h.2.2.1, known_ptr h.2.2.2.1, trivial⟩

/-! ## Bytes a block writes in the frame -/

theorem frame_write_load {m m' : MachineData} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (r.env m vars) S m') {o o' n : Nat} (ho : o + n ≤ 2752)
    (hw : covers S.mem 0 o n (.load 0 o' n) = true) {bs : List UInt8} (hlen : bs.length = n)
    (hn : n ≤ 8) (h : BytesAt m.dmem (r.off o') bs) : BytesAt m'.dmem (r.off o) bs :=
  bytesAt_write_load hm (b := r.base) (sz := 2752) rfl ho hw hlen hn h

/-- **16 bytes copied** by two 8-byte loads and stores. -/
theorem frame_copy16 {m m' : MachineData} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (r.env m vars) S m') {o o' : Nat} (ho : o + 16 ≤ 2752)
    (hw1 : covers S.mem 0 o 8 (.load 0 o' 8) = true)
    (hw2 : covers S.mem 0 (o + 8) 8 (.load 0 (o' + 8) 8) = true) {bs : List UInt8}
    (hlen : bs.length = 16) (h : BytesAt m.dmem (r.off o') bs) : BytesAt m'.dmem (r.off o) bs := by
  rw [← List.take_append_drop 8 bs]
  have h1 := frame_write_load hm (by omega) hw1 (bs := bs.take 8) (by simp [hlen]) (by decide)
    (BytesAt.zero (by simpa using BytesAt.slice h 0 8))
  have h2 := frame_write_load hm (by omega) hw2 (bs := bs.drop 8) (by simp [hlen]) (by decide)
    (by
      have := BytesAt.slice h 8 8
      rwa [r.off_add, List.take_of_length_le (by simp [hlen])] at this)
  refine BytesAt.append h1 ?_
  rw [List.length_take, Nat.min_eq_left (by omega), r.off_add]
  exact h2

/-- **Zeros written** in the frame. -/
theorem frame_write_zero {m m' : MachineData} {vars : Nat → BitVec 64} {S : SState}
    (hm : Match (r.env m vars) S m') {o n : Nat} (ho : o + n ≤ 2752)
    (hz : zeroAt S.mem 0 o n = true) : BytesAt m'.dmem (r.off o) (List.replicate n 0) := by
  intro i hi
  rw [List.length_replicate] at hi
  simp only [zeroAt, List.all_eq_true, List.mem_range] at hz
  have h := hz i hi
  rw [List.getElem_replicate]
  show m'.dmem.get? (r.base + BitVec.ofNat 64 o + BitVec.ofNat 64 i) = _
  rw [addr_add_add, hm.mem 0 r.base 2752 rfl (o + i) (by omega)]
  unfold memByte
  revert h
  cases findWrite 0 (o + i) S.mem with
  | none => simp
  | some vt =>
    obtain ⟨v, t⟩ := vt
    cases v <;> simp_all
    rename_i c
    rcases c with _ | c
    · simp [Sym.eval, byteOf]
    · simp at *

omit [Labels] in
/-- **Bytes side by side** in the frame. -/
theorem BytesAt.cat {d : DataMem} {o o' : Nat} {a b : List UInt8} (h1 : BytesAt d (r.off o) a)
    (h2 : BytesAt d (r.off o') b) (ho : o' = o + a.length) : BytesAt d (r.off o) (a ++ b) :=
  BytesAt.append h1 (by rw [r.off_add, ← ho]; exact h2)

/-- **A literal written** in the frame. -/
theorem frame_write_lit {m m' : MachineData} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {S : SState} (hm : Match (r.envR m rest vars) S m') {o n : Nat}
    (ho : o + n ≤ 2752) {c : Nat} (hw : covers S.mem 0 o n (.lit c) = true) :
    BytesAt m'.dmem (r.off o) ((List.range n).map (byteOf (BitVec.ofNat 64 c))) :=
  bytesAt_write_val hm (b := r.base) (sz := 2752) rfl ho hw

omit [Labels] in
/-- **A slice of a copy**: bytes `c .. c + t` of a copy of the `n` bytes at `o'` are those at
`o' + c`. -/
theorem copy_slice {d d' : DataMem} {o o' n c : Nat} {bs : List UInt8}
    (hB : BytesAt d' (r.off o) (bytesOf d (r.off o') n)) (hc : c + bs.length ≤ n)
    (h : BytesAt d (r.off (o' + c)) bs) : BytesAt d' (r.off (o + c)) bs := by
  have := BytesAt.slice hB c bs.length
  rw [← Hasher.bytesOf_add _ _ hc, r.off_add, r.off_add, bytesOf_of_bytesAt h] at this
  exact this

theorem eval_ptr0R (m : MachineData) (rest : List (BitVec 64 × Nat)) (vars : Nat → BitVec 64)
    (o : Nat) : (Sym.ptr 0 o).eval (r.envR m rest vars) = r.off o := by
  simp only [Sym.eval, Run.off, BitVec.ofInt_natCast]
  rfl

/-- **A register a block with more regions sets to the frame's byte `o`.** -/
theorem regIs_ptrR {m m' : MachineData} {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {S : SState} (hm : Match (r.envR m rest vars) S m') {y : XReg} {o : Nat}
    (h : S.reg y = some (.ptr 0 o)) : Run.RegIs m' y (r.off o) := by
  unfold Run.RegIs
  rw [hm.regs y _ h, eval_ptr0R]

/-- **16 bytes copied** between two regions by two 8-byte loads and stores. -/
theorem copy16_gen {env : Env} {S : SState} {m' : MachineData} (hm : Match env S m')
    {k : Nat} {b : BitVec 64} {sz : Nat} (hb : env.regions[k]? = some (b, sz)) {o : Nat}
    (ho : o + 16 ≤ sz) {k' o' : Nat} (hw1 : covers S.mem k o 8 (.load k' o' 8) = true)
    (hw2 : covers S.mem k (o + 8) 8 (.load k' (o' + 8) 8) = true) {bs : List UInt8}
    (hlen : bs.length = 16) (h : BytesAt env.mem0 (env.base k' + BitVec.ofNat 64 o') bs) :
    BytesAt m'.dmem (b + BitVec.ofNat 64 o) bs := by
  rw [← List.take_append_drop 8 bs]
  have h1 := bytesAt_write_load hm hb (by omega) hw1 (bs := bs.take 8) (by simp [hlen])
    (by decide) (by simpa using BytesAt.slice h 0 8)
  have h2 := bytesAt_write_load hm hb (by omega) hw2 (bs := bs.drop 8) (by simp [hlen])
    (by decide) (by
      have := BytesAt.slice h 8 8
      rwa [addr_add_add, List.take_of_length_le (by simp [hlen])] at this)
  refine BytesAt.append h1 ?_
  rw [List.length_take, Nat.min_eq_left (by omega), addr_add_add]
  exact h2

/-! ## The slots -/

omit [Labels] in
theorem CK.slot8 {x E : List UInt8} {m : MachineData} (h : r.CK x E m) :
    BytesAt m.dmem (r.off 8) (wordBytes r.m0.regs.X7) := h.1.2.2.1.2.2

omit [Labels] in
theorem CK.slot20 {x E : List UInt8} {m : MachineData} (h : r.CK x E m) :
    BytesAt m.dmem (r.off 20) (u32Bytes (r.hi >>> 16)) := h.1.2.2.2.1.2.2

omit [Labels] in
theorem CK.slot24 {x E : List UInt8} {m : MachineData} (h : r.CK x E m) :
    BytesAt m.dmem (r.off 24) (u32Bytes r.e) := h.1.2.2.2.2.1.2.2

omit [Labels] in
theorem CK.slot28 {x E : List UInt8} {m : MachineData} (h : r.CK x E m) :
    BytesAt m.dmem (r.off 28) (u32Bytes r.hi) := h.1.2.2.2.2.2.1.2.2

omit [Labels] in
theorem CK.slot380 {x E : List UInt8} {m : MachineData} (h : r.CK x E m) :
    BytesAt m.dmem (r.off 380) x := h.1.2.2.2.2.2.2.1.2.2

omit [Labels] in
theorem CK.length_x {x E : List UInt8} {m : MachineData} (h : r.CK x E m) : x.length = 58 :=
  h.1.2.2.2.2.2.2.1.1

/-- **Literal words the memory holds**, as the writes of the symbolic state. -/
theorem match_withLit {m : MachineData} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {S : SState} (hm : Match (r.envR m rest vars) S m) (hS : S.mem = [])
    {o c : Nat} (h : BytesAt m.dmem (r.off o) ((List.range 8).map (byteOf (BitVec.ofNat 64 c)))) :
    Match (r.envR m rest vars) { S with mem := [litW o c] } m :=
  Match.withWrites hm hS fun w hw b sz hb i hi ↦ by
    simp only [List.mem_singleton] at hw
    subst hw
    simp only [litW, Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have := h i (by simp; exact hi)
    rw [r.off_add] at this
    simp only [litW]
    rw [show r.base + BitVec.ofNat 64 (o + i) = r.off (o + i) from rfl, this]
    simp [Sym.eval]

end

/-! ## A step's bytes -/

/-- A word's eight bytes. -/
theorem bytes_word (i : Nat) :
    (List.range 8).map (byteOf (BitVec.ofNat 64 i)) = wordBytes i.toUInt64 :=
  (Hasher.wordBytes_ofBitVec _).symm

/-- The address's type and step byte: `1 | step << 5`. -/
theorem byte_tstep {pos : Nat} (h : pos ≤ 2) :
    (List.range 1).map (byteOf (BinOp.apply .orr .W32 (BitVec.ofNat 64 1)
      (UnOp.apply (.shift .LSL 5) .W32 (BitVec.ofNat 64 pos)))) =
        [(1 : UInt8) ||| pos.toUInt8 <<< 5] := by
  obtain rfl | rfl | rfl : pos = 0 ∨ pos = 1 ∨ pos = 2 := by omega
  all_goals decide

theorem length_addr (r : Run) (t : UInt8) (pos : Nat) : (r.addr t pos).length = 16 := by
  simp [Run.addr, address, length_u32Bytes]

theorem length_pp (r : Run) : r.pp.length = 16 := by
  simp [Run.pp, WotsLeafPre.pp, bytesOf]

theorem length_u128Bytes (i : Nat) : (u128Bytes i).length = 16 := by
  simp [u128Bytes, length_wordBytes]

/-- **`th` of a short input**: the first 16 bytes of `keccak_f` of the padded input XORed into
the zero state. -/
theorem th_short {pp : List UInt8} {tw : Tweak} {p : List UInt8}
    (h : (pp ++ address tw ++ p).length < 136) :
    th pp tw p = (Keccak.keccakF (Keccak.xorBlock (List.replicate 200 0)
      (Keccak.finalBlock (pp ++ address tw ++ p)))).take 16 := by
  rw [th, hashBytes_short h, List.take_take]
  rfl

theorem length_th (pp : List UInt8) (tw : Tweak) (p : List UInt8) : (th pp tw p).length = 16 := by
  rw [th, List.length_take, length_hashBytes]
  rfl

end

end NativeRustcArm.WotsLeafProof
