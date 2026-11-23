module

public import NativeRustcX64.WotsLeaf.Codeword.Region
public import NativeRustcX64.WotsLeaf.Chain.Exec

/-!
# The chains: their model and the steps' tools

Chain `j`'s end (`Run.endOf`), the ends of the first `n` chains (`Run.endsPre`), the slots of the
chains' loop (`Run.outerSlots`, `Run.endSlots`, `Run.stepSlots`). A block run from any literal
state matching the machine (`frameStepS`), a seeded state with the literal words the memory holds
(`match_seeded`). The bytes a block writes and copies (`frame_copy16`, `copy_slice`,
`BytesAt.cat`).
-/

namespace NativeRustcX64.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcX64.Sym NativeRustcX64.Xmss.WotsLeaf Chain
open LeanVM.Protocol.KeccakHash

@[expose] public section

/-- Chain `j`'s digit. -/
def Run.digit (r : Run) (j : Nat) : Nat := ((r.digitsPre 58).getD j 0).toNat

/-- Chain `j`'s end: from its digit, `3 - digit` steps from the signature's value. -/
def Run.endOf (r : Run) (j : Nat) : List UInt8 :=
  chain r.pp r.layer r.e j (r.digit j) (3 - r.digit j) (r.values.getD j [])

/-- The ends of the first `n` chains. -/
def Run.endsPre (r : Run) (n : Nat) : List UInt8 := ((List.range n).map r.endOf).flatten

/-- A chain step's tweak: type 1 at step `p`. -/
def Run.tw (r : Run) (p : Nat) : Tweak := (tweak 1 r.hi r.e).withStep p

/-- The slots of the chains' loop at chain `i`: the chains', the ends so far at `1080`. -/
def Run.outerSlots (r : Run) (i : Nat) : List Slot :=
  r.chainSlots ++ [(1080, 16 * i, r.endsPre i)]

/-- The slots at chain `i`'s end: the loop's, `16 i` at `456`. -/
def Run.endSlots (r : Run) (i : Nat) : List Slot :=
  r.outerSlots i ++ [(456, 8, regBytes (BitVec.ofNat 64 (16 * i)))]

/-- The slots of chain `i`'s steps: the end's, `i` at `464`. -/
def Run.stepSlots (r : Run) (i : Nat) : List Slot :=
  r.endSlots i ++ [(464, 8, regBytes (BitVec.ofNat 64 i))]

end

public section

section
variable {r : Run} [Labels]

/-- **A seeded state**: the frame's fresh state with literal words the memory holds. -/
theorem match_seeded {m : MachineData} {extra : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {k : List (Reg64 × Sym)} {sextra : List Nat} {aliases : List (Sym × Nat × Int)}
    (hm : Match (r.envR m extra ret) (frameS k sextra [] aliases) m) {o v : Nat}
    (h : BytesAt m.dmem (r.off o) (regBytes (BitVec.ofNat 64 v))) :
    Match (r.envR m extra ret) (seeded k [litW o v] sextra aliases) m := by
  refine Match.withWrites hm rfl fun w hw b sz hb i hi ↦ ?_
  simp only [List.mem_singleton] at hw
  subst hw
  cases hb
  have := h i (by simp [regBytes]; exact hi)
  rw [Run.off, addr_add_add] at this
  show m.dmem.get? (r.base + BitVec.ofNat 64 (o + i)) = some (byteOf (BitVec.ofNat 64 v) i)
  rw [this]
  simp [regBytes]

/-- A register a block sets: its symbolic value's. -/
theorem regIs_eval {m m' : MachineData} {extra : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {S : SState} (hm : Match (r.envR m extra ret) S m') {y : Reg64} {v : Sym}
    (h : S.reg y = some v) {x : BitVec 64} (hx : v.eval (r.envR m extra ret) = x) :
    Run.RegIs m' y x := by
  unfold Run.RegIs reg
  rw [hm.regs y _ h, hx]

/-- The frame's bytes a block's newest writes of a value cover. -/
theorem covers_bytes {m m' : MachineData} {extra : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {S : SState} (hm : Match (r.envR m extra ret) S m') {o n : Nat} (ho : o + n ≤ 2784) {v : Sym}
    (hc : covers S.mem 0 o n v = true) {bs : List UInt8}
    (hb : (List.range n).map (byteOf (v.eval (r.envR m extra ret))) = bs) :
    BytesAt m'.dmem (r.off o) bs := by
  rw [← hb]
  exact frame_covers hm ho hc

/-- The frame's bytes a block's newest writes of a load of the frame's bytes cover. -/
theorem covers_load {m m' : MachineData} {extra : List (BitVec 64 × Nat)} {ret : BitVec 64}
    {S : SState} (hm : Match (r.envR m extra ret) S m') {o n o' : Nat} (ho : o + n ≤ 2784)
    (hn : n ≤ 8) (hc : covers S.mem 0 o n (.load 0 o' n) = true) {bs : List UInt8}
    (hl : bs.length = n) (h : BytesAt m.dmem (r.off o') bs) : BytesAt m'.dmem (r.off o) bs :=
  bytesAt_write_load hm (b := r.base) (sz := 2784) rfl ho hc hl hn h

end

theorem allOf_of_mem {α : Type} {P : α → Prop} : ∀ {l : List α}, (∀ a ∈ l, P a) → AllOf P l
  | [], _ => trivial
  | a :: _, h => ⟨h a List.mem_cons_self, allOf_of_mem fun b hb ↦ h b (List.mem_cons_of_mem _ hb)⟩

/-- A slot's bytes. -/
theorem SlotsAt.get {r : Run} {m : MachineData} {L : List Slot} (h : SlotsAt r m L) {o n : Nat}
    {bs : List UInt8} (hs : (o, n, bs) ∈ L) : BytesAt m.dmem (r.off o) bs :=
  (mem_of_allOf h hs).2.2

/-- A new slot. -/
theorem SlotsAt.push {r : Run} {m : MachineData} {L : List Slot} (h : SlotsAt r m L) {o n : Nat}
    {bs : List UInt8} (hb : BytesAt m.dmem (r.off o) bs) (hl : bs.length = n) (ho : o + n ≤ 2712) :
    SlotsAt r m (L ++ [(o, n, bs)]) :=
  allOf_append h ⟨⟨hl, ho, hb⟩, trivial⟩

/-- What the frame keeps, with a new slot. -/
theorem Keep.push {r : Run} {m : MachineData} {L : List Slot} (h : Keep r L m) {o n : Nat}
    {bs : List UInt8} (hb : BytesAt m.dmem (r.off o) bs) (hl : bs.length = n) (ho : o + n ≤ 2712) :
    Keep r (L ++ [(o, n, bs)]) m :=
  ⟨h.1, h.2.push hb hl ho⟩

/-- What the frame keeps at a callee's entry, with a new slot. -/
theorem CallKeep.push {r : Run} {m : MachineData} {L : List Slot} (h : CallKeep r L m) {o n : Nat}
    {bs : List UInt8} (hb : BytesAt m.dmem (r.off o) bs) (hl : bs.length = n) (ho : o + n ≤ 2712) :
    CallKeep r (L ++ [(o, n, bs)]) m :=
  ⟨h.1, h.2.push hb hl ho⟩

/-- What the frame keeps, of a sublist of the slots. -/
theorem Keep.sub {r : Run} {m : MachineData} {L L' : List Slot} (h : Keep r L m)
    (hs : ∀ s ∈ L', s ∈ L) : Keep r L' m :=
  ⟨h.1, allOf_of_mem fun s hm ↦ mem_of_allOf h.2 (hs s hm)⟩

section
variable [Host]

/-- **A block of the frame from a literal state matching the machine**, its writes keeping the
frame's invariant and missing the slots; `cont` from where it ends. -/
theorem frameStepS (r : Run) (hp : Placed Xmss.WotsLeaf.code r.k) (hpre : r.Pre)
    {ds : List Directive} {j : Nat} (hb : ds.IsInfixAt Xmss.WotsLeaf.code j) (hne : ds ≠ [])
    {S₀ S' : SState} {x : Exit} (hx : exec ds S₀ = some (S', x)) (hok : blockOK S' 0 = true)
    {L : List Slot} (hL : slotsKept S' L = true) {m : MachineData} (hK : Keep r L m)
    {extra : List (BitVec 64 × Nat)} (hxo : ExtraOK r m extra)
    (hm₀ : Match (r.envR m extra (r.pc (j + ds.length)).toBitVec) S₀ m) {R : MachineState → Prop}
    (cont : ∀ st, Match (r.envR m extra (r.pc (j + ds.length)).toBitVec) S' st.data →
      Keep r L st.data → KB r S' m st.data →
      PcOk (r.envR m extra (r.pc (j + ds.length)).toBitVec) x (r.pc (j + ds.length)) st →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m, r.pc j⟩ := by
  have hwf := envR_wf hpre ((r.frame_iff m).1 hK.1).kept hxo (r.pc (j + ds.length)).toBitVec
  exact blk r hp hb hne hx hwf rfl hm₀ fun st hm hpc ↦
    cont st hm (hK.of_block hpre hm hwf hok hL) (kb_of_block hpre hm hwf) hpc

end

/-- `i`'s word, a `u128`'s low half. -/
theorem regBytes_ofNat (i : Nat) :
    regBytes (BitVec.ofNat 64 i) = wordBytes i.toUInt64 := by
  rw [regBytes, ← Hasher.wordBytes_ofBitVec]
  rfl

/-- `0`'s bytes. -/
theorem regBytes_zero : regBytes (BitVec.ofNat 64 0) = List.replicate 8 0 := bytes_zero 8

/-- **Bytes side by side** in the frame. -/
theorem BytesAt.cat {r : Run} {d : DataMem} {o o' : Nat} {a b : List UInt8}
    (h1 : BytesAt d (r.off o) a) (h2 : BytesAt d (r.off o') b) (ho : o' = o + a.length) :
    BytesAt d (r.off o) (a ++ b) :=
  BytesAt.append h1 (by rw [Run.off_add, ← ho]; exact h2)

theorem take_of_bytesAt {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs)
    (n : Nat) : BytesAt d a (bs.take n) :=
  BytesAt.left (cs := bs.drop n) (by rwa [List.take_append_drop])

/-- **A slice of a copy**: bytes `c .. c + t` of a copy of the `n` bytes at `o'` are those at
`o' + c`. -/
theorem copy_slice {r : Run} {d d' : DataMem} {o o' n c : Nat} {bs : List UInt8}
    (hB : BytesAt d' (r.off o) (bytesOf d (r.off o') n)) (hc : c + bs.length ≤ n)
    (h : BytesAt d (r.off (o' + c)) bs) : BytesAt d' (r.off (o + c)) bs := by
  have := BytesAt.slice hB c bs.length
  rw [← Hasher.bytesOf_add _ _ hc, Run.off_add, Run.off_add, bytesOf_of_bytesAt h] at this
  exact this

/-- A slice of the frame's bytes. -/
theorem BytesAt.sub {r : Run} {d : DataMem} {o : Nat} {bs : List UInt8}
    (h : BytesAt d (r.off o) bs) (c n : Nat) : BytesAt d (r.off (o + c)) ((bs.drop c).take n) := by
  have := BytesAt.slice h c n
  rwa [Run.off_add] at this

theorem Keep.left {r : Run} {m : MachineData} {L L' : List Slot} (h : Keep r (L ++ L') m) :
    Keep r L m :=
  ⟨h.1, allOf_left h.2⟩

theorem Keep.add {r : Run} {m : MachineData} {L L' : List Slot} (h : Keep r L m)
    (h' : SlotsAt r m L') : Keep r (L ++ L') m :=
  ⟨h.1, allOf_append h.2 h'⟩

theorem CallKeep.add {r : Run} {m : MachineData} {L L' : List Slot} (h : CallKeep r L m)
    (h' : SlotsAt r m L') : CallKeep r (L ++ L') m :=
  ⟨h.1, allOf_append h.2 h'⟩

section
variable [Labels]

theorem pc_true {env : Env} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond (.lit true) l) next st) : st.pc = Labels.label l := h

theorem pc_false {env : Env} {l : Label} {next : Int64} {st : MachineState}
    (h : PcOk env (.cond (.lit false) l) next st) : st.pc = next := h

/-- **16 bytes copied** between regions by two 8-byte loads and stores. -/
theorem copy16 {env : Env} {S : SState} {m' : MachineData} (hm : Match env S m')
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

/-- **16 bytes copied** in the frame. -/
theorem frame_copy16 {r : Run} {m m' : MachineData} {extra : List (BitVec 64 × Nat)}
    {ret : BitVec 64} {S : SState} (hm : Match (r.envR m extra ret) S m') {o o' : Nat}
    (ho : o + 16 ≤ 2784) (hw1 : covers S.mem 0 o 8 (.load 0 o' 8) = true)
    (hw2 : covers S.mem 0 (o + 8) 8 (.load 0 (o' + 8) 8) = true) {bs : List UInt8}
    (hlen : bs.length = 16) (h : BytesAt m.dmem (r.off o') bs) : BytesAt m'.dmem (r.off o) bs :=
  copy16 hm (b := r.base) (sz := 2784) rfl ho hw1 hw2 hlen h

/-- **`memcpy(a, b, n)`** from the frame: the `n` bytes from `b` at `a`. -/
theorem memcpyFrame' {r : Run} (hpre : r.Pre) {L : List Slot} {m₁ : MachineData}
    (hK : CallKeep r L m₁) {a b n : Nat} (h0 : Run.RegIs m₁ .rdi (r.off a))
    (h1 : Run.RegIs m₁ .rsi (r.off b)) (h2 : (reg m₁ .rdx).toNat = n) (ha : a + n ≤ 2712)
    (hb : b + n ≤ 2768) (hd : a + n ≤ b ∨ b + n ≤ a) (hL : slotsOff L a n = true) :
    MemcpyPre m₁ ∧ ∀ m₂, rspOf m₂ = rspOf m₁ + 8#64 → MemcpyPost m₁ m₂ →
      Keep r L m₂ ∧ Saved m₁ m₂ ∧ BytesAt m₂.dmem (r.off a) (bytesOf m₁.dmem (r.off b) n) := by
  refine ⟨r.memcpy_pre hpre hK.1 h0 h1 h2 (by omega) hb hd, fun m₂ hsp hQ ↦ ?_⟩
  obtain ⟨hB, hout, hS⟩ := r.memcpy_out h0 h1 h2 hQ
  exact ⟨Keep.of_call hpre hK hS hsp ha (by decide) hout hL, hS, hB⟩

end

/-- The low two bytes of `layer << 23`. -/
theorem bytes_layerW16 (r : Run) :
    (List.range 2).map (byteOf (UnOp.apply .trunc .W16 r.layerW)) = (u32Bytes r.hi).take 2 := by
  have h1 : (UnOp.apply .trunc .W16 r.layerW).toNat = 0 := by
    have hs : shiftCount .W32 (BitVec.ofNat 64 23) = 23 := by decide
    simp only [UnOp.apply, Run.layerW, BinOp.apply, toNat_ext, toNat_low, BitVec.toNat_shiftLeft,
      hs, Width.bits, Nat.shiftLeft_eq]
    omega
  have hz : byteOf (UnOp.apply .trunc .W16 r.layerW) = fun _ ↦ 0 :=
    funext fun t ↦ by simp [byteOf, h1]
  rw [show r.hi = layerHi (reg r.m0 .rdx).toNat 0 from rfl, hi_take2, hz]
  rfl

/-- The byte of `hi >> 16`: `hi`'s third. -/
theorem byte_hi16 (r : Run) :
    (List.range 1).map (byteOf (UnOp.apply .trunc .W8 r.hi16)) = ((u32Bytes r.hi).drop 2).take 1 := by
  have h1 : (UnOp.apply .trunc .W8 r.hi16).toNat = (reg r.m0 .rdx).toNat * 128 % 2 ^ 32 % 256 := by
    have hs : shiftCount .W32 (BitVec.ofNat 64 23) = 23 := by decide
    have hs' : shiftCount .W32 (BitVec.ofNat 64 16) = 16 := by decide
    simp only [UnOp.apply, Run.hi16, Run.layerW, BinOp.apply, toNat_ext, toNat_low,
      BitVec.toNat_shiftLeft, Codeword.toNat_ushiftRight', hs, hs', Width.bits, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow, Nat.reducePow]
    omega
  rw [show r.hi = layerHi (reg r.m0 .rdx).toNat 0 from rfl, ← byte_hi2]
  simp only [List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  apply u8_ext
  have h2 : (UnOp.apply .trunc .W8 (BinOp.apply .shl .W32 (reg r.m0 .rdx) (BitVec.ofNat 64 7))).toNat =
      (reg r.m0 .rdx).toNat * 128 % 2 ^ 32 % 256 := by
    have hs : shiftCount .W32 (BitVec.ofNat 64 7) = 7 := by decide
    simp only [UnOp.apply, BinOp.apply, toNat_ext, toNat_low, BitVec.toNat_shiftLeft, hs,
      Width.bits, Nat.shiftLeft_eq]
    omega
  simp [byteOf_toNat, h1, h2]

end

end NativeRustcX64.WotsLeafProof
