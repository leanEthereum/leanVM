module

public import NativeRustcX64.SphincsVerify.Calls
public import NativeRustcX64.LayerRead.Glue
public import NativeRustc.Sphincs.ParseMem
public import NativeRustcX64.SphincsVerify.Bswap

/-!
# What the parse's proof shares (x86-64)

- **Facts**: the frame's bytes the parse has written so far, a literal list of (offset, length,
  bytes) (`Facts`, `Facts.get`); kept by a block whose region 0 is the frame and which does not
  write them (`factsOK`, `Facts.of_block`), by a change of the frame's bytes apart from them
  (`factsApart`, `Facts.keep`), by a call changing a range apart from them (`Facts.of_call`); the
  checks decided on the facts' layout (`factsOK_layout`, `factsApart_layout`).
- A block's writes inside an interval of one region (`sameOutside_hull`); the frame's invariant
  after a block whose writes are in the frame below the saved registers, RSP kept
  (`frame_of_hull`); frame bytes kept by a change elsewhere (`fact_keep`).
- Bytes a block stored: loaded (`copies`, `copy`), loaded at an index (`copiesX`, `copyX`), a
  register stored whole (`holdsReg`, `bytesAt_reg`), the low 4 bytes of a value (`holdsLow`,
  `Low4`, `bytesAt_low`), through `bswap` and truncation (`Low4.bswap`, `Low4.trunc`).
- Registers kept (`keepsRegs`), counted loops (`count_loop`), a loop's exit test (`pc_cond`),
  addresses (`alias_neg`, `alias_pos`, `bv_lin`, `eval_ptr`, `eval_base`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym LeanVM.Protocol.KeccakHash

@[expose] public section

/-- The context's address. -/
abbrev ctx (r : Run) : BitVec 64 := reg r.m0 .rdi

/-- The frame's bytes at the listed offsets: `(o, n, bs)`, `n` bytes `bs` at `o`. -/
def Facts (r : Run) (d : DataMem) : List (Nat × Nat × List UInt8) → Prop
  | [] => True
  | (o, n, bs) :: L => (bs.length = n ∧ BytesAt d (r.off o) bs) ∧ Facts r d L

/-- No write of region 0 in the bytes `o .. o + n`. -/
def noW0 (S : SState) (o n : Nat) : Bool :=
  S.mem.all fun w => w.r != 0 || decide (w.off + w.n ≤ o) || decide (o + n ≤ w.off)

/-- The facts are in the frame and no write of region 0 touches them. -/
def factsOK (S : SState) (L : List (Nat × Nat × List UInt8)) : Bool :=
  L.all fun p => decide (p.1 + p.2.1 ≤ 29384) && noW0 S p.1 p.2.1

/-- The facts are in the frame and apart from the bytes `a .. a + n`. -/
def factsApart (L : List (Nat × Nat × List UInt8)) (a n : Nat) : Bool :=
  L.all fun p => decide (p.1 + p.2.1 ≤ 29384) && (decide (p.1 + p.2.1 ≤ a) || decide (a + n ≤ p.1))

/-- The facts' layout is in the frame and no write of region 0 touches it. -/
def layoutOK (S : SState) (L : List (Nat × Nat)) : Bool :=
  L.all fun p => decide (p.1 + p.2 ≤ 29384) && noW0 S p.1 p.2

/-- The facts' layout is in the frame and apart from the bytes `a .. a + n`. -/
def layoutApart (L : List (Nat × Nat)) (a n : Nat) : Bool :=
  L.all fun p => decide (p.1 + p.2 ≤ 29384) && (decide (p.1 + p.2 ≤ a) || decide (a + n ≤ p.1))

/-- The writes of a state in region `ri`, between `lo` and `hi`. -/
def writesIn (S : SState) (ri lo hi : Nat) : Bool :=
  S.mem.all fun w => w.r == ri && decide (lo ≤ w.off) && decide (w.off + w.n ≤ hi)

/-- `S` keeps `S₀`'s registers `rs`, which `S₀` knows. -/
def keepsRegs (rs : List Reg64) (S₀ S : SState) : Bool :=
  rs.all fun x => (S₀.reg x).isSome && S.reg x == S₀.reg x

/-- Byte `i` of region `r` holds the byte at `o' + i` of region `r'` that a load read. -/
def copies (ws : List Write) (r o r' o' n : Nat) : Bool :=
  (List.range n).all fun i =>
    match findWrite r (o + i) ws with
    | some (.load r'' off k, u) => r'' == r' && off + u == o' + i && decide (u < k) && decide (k ≤ 8)
    | _ => false

/-- Byte `i` of region `r` holds the byte at `o' + I + i` of region `r'` that an indexed load
read, `I` the index. -/
def copiesX (ws : List Write) (r o r' o' : Nat) (I : Sym) (n : Nat) : Bool :=
  (List.range n).all fun i =>
    match findWrite r (o + i) ws with
    | some (.loadx r'' off idx k, u) =>
      r'' == r' && off + u == o' + i && idx == I && decide (u < k) && decide (k ≤ 8)
    | _ => false

/-- The 8 bytes at `o` of region `r` are register `x`'s, stored whole. -/
def holdsReg (ws : List Write) (r o : Nat) (x : Reg64) : Bool :=
  (List.range 8).all fun i =>
    match findWrite r (o + i) ws with
    | some (.reg y, u) => y == x && u == i
    | _ => false

/-- The 4 bytes at `o` of region `r` are the low bytes of `v`. -/
def holdsLow (ws : List Write) (r o : Nat) (v : Sym) : Bool :=
  (List.range 4).all fun i => findWrite r (o + i) ws == some (v, i)

/-- The low 4 bytes of `v` are `bs`. -/
def Low4 (v : BitVec 64) (bs : List UInt8) : Prop := bs.length = 4 ∧ ∀ t < 4, byteOf v t = bs.getD t 0

end

public section

/-! ## Facts -/

theorem facts_append (r : Run) (d : DataMem) :
    ∀ (L L' : List (Nat × Nat × List UInt8)), Facts r d (L ++ L') ↔ Facts r d L ∧ Facts r d L'
  | [], _ => by simp [Facts]
  | (o, n, bs) :: L, L' => by
    simp only [List.cons_append, Facts, facts_append r d L L', and_assoc]

theorem off_add (r : Run) (a i : Nat) : r.off a + BitVec.ofNat 64 i = r.off (a + i) :=
  Run.off_add r a i

theorem factsOK_layout (S : SState) (L : List (Nat × Nat × List UInt8)) :
    factsOK S L = layoutOK S (L.map fun p => (p.1, p.2.1)) := by
  simp only [factsOK, layoutOK, List.all_map]
  rfl

theorem factsApart_layout (L : List (Nat × Nat × List UInt8)) (a n : Nat) :
    factsApart L a n = layoutApart (L.map fun p => (p.1, p.2.1)) a n := by
  simp only [factsApart, layoutApart, List.all_map]
  rfl

theorem Facts.mem {r : Run} {d : DataMem} :
    ∀ {L : List (Nat × Nat × List UInt8)}, Facts r d L → ∀ {o n : Nat} {bs : List UInt8},
      (o, n, bs) ∈ L → bs.length = n ∧ BytesAt d (r.off o) bs
  | [], _, _, _, _, h => by cases h
  | (o', n', bs') :: L, ⟨h1, h⟩, o, n, bs, hm => by
    rcases List.mem_cons.mp hm with he | hm
    · cases he
      exact h1
    · exact Facts.mem h hm

theorem Facts.of_mem {r : Run} {d : DataMem} :
    ∀ {L : List (Nat × Nat × List UInt8)},
      (∀ o n bs, (o, n, bs) ∈ L → bs.length = n ∧ BytesAt d (r.off o) bs) → Facts r d L
  | [], _ => trivial
  | (o, n, bs) :: _, h => ⟨h o n bs List.mem_cons_self,
    Facts.of_mem fun o' n' bs' hm ↦ h o' n' bs' (List.mem_cons_of_mem _ hm)⟩

/-- The frame's bytes `xs` at `o`, `ys` right after. -/
theorem bytesAt_cat {r : Run} {d : DataMem} {o k o' : Nat} {xs ys : List UInt8}
    (hx : BytesAt d (r.off o) xs) (hl : xs.length = k) (ho : o + k = o')
    (hy : BytesAt d (r.off o') ys) : BytesAt d (r.off o) (xs ++ ys) :=
  BytesAt.append hx (by rw [off_add, hl, ho]; exact hy)

theorem Facts.get {r : Run} {d : DataMem} {L : List (Nat × Nat × List UInt8)} (h : Facts r d L)
    {o n : Nat} {bs : List UInt8} (hm : (o, n, bs) ∈ L) : BytesAt d (r.off o) bs :=
  (h.mem hm).2

theorem findWrite_none {S : SState} {o n : Nat} (h : noW0 S o n = true) {i : Nat} (hi : i < n) :
    findWrite 0 (o + i) S.mem = none := by
  simp only [noW0, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  cases hf : findWrite 0 (o + i) S.mem with
  | none => rfl
  | some vt =>
    obtain ⟨w, hw, hwr, h1, h2⟩ := mem_of_findWrite hf
    rcases h w hw with (h' | h') | h'
    · exact absurd hwr h'
    · omega
    · omega

section
variable (r : Run) [Labels]

/-- **Facts kept by a block** of an environment whose region 0 is the frame, which does not
write them. -/
theorem Facts.of_block {m m' : MachineData} {regions : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} (hb : regions[0]? = some (r.base, 29392))
    {S' : SState} (hm' : Match (Env.ofMachine m regions vars ret) S' m') :
    ∀ {L : List (Nat × Nat × List UInt8)}, Facts r m.dmem L → factsOK S' L = true →
      Facts r m'.dmem L
  | [], _, _ => trivial
  | (o, n, bs) :: L, ⟨⟨hl, hb'⟩, h⟩, hok => by
    simp only [factsOK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hok
    refine ⟨⟨hl, fun i hi ↦ ?_⟩, Facts.of_block hb hm' h hok.2⟩
    obtain ⟨⟨ho, hn⟩, -⟩ := hok
    rw [off_add, Run.off, hm'.mem 0 r.base 29392 hb (o + i) (by omega)]
    unfold memByte
    rw [findWrite_none hn (by omega)]
    have := hb' i hi
    rwa [off_add, Run.off] at this

/-- **Facts kept by a change** of the frame's bytes apart from them. -/
theorem Facts.keep (hpre : r.Pre) {d d' : DataMem} {a n : Nat} (ha : a + n ≤ 29384)
    (hs : SameOutside d d' (InRange (r.off a) n)) :
    ∀ {L : List (Nat × Nat × List UInt8)}, Facts r d L → factsApart L a n = true → Facts r d' L
  | [], _, _ => trivial
  | (o, k, bs) :: L, ⟨⟨hl, hb⟩, h⟩, hok => by
    simp only [factsApart, List.all_cons, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at hok
    refine ⟨⟨hl, bytesAt_of_sameOutside hb hs fun i hi ↦ ?_⟩, Facts.keep hpre ha hs h hok.2⟩
    rw [off_add]
    exact r.not_inRange_off hpre ha (by omega) (by omega)

/-- **Facts kept by a call** changing the frame's bytes `a .. a + n` and its stack. -/
theorem Facts.of_call (hpre : r.Pre) {m m' : MachineData} (hc : r.AtCall m) {a n N : Nat}
    (ha : a + n ≤ 29384) (hN : N ≤ finalizeStack)
    (hout : SameOutside m.dmem m'.dmem (r.CallOut m a n N)) :
    ∀ {L : List (Nat × Nat × List UInt8)}, Facts r m.dmem L → factsApart L a n = true →
      Facts r m'.dmem L
  | [], _, _ => trivial
  | (o, k, bs) :: L, ⟨⟨hl, hb⟩, h⟩, hok => by
    simp only [factsApart, List.all_cons, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at hok
    exact ⟨⟨hl, r.bytesAt_of_call hpre hc ha hN hout (by omega) (by omega) hb⟩,
      Facts.of_call hpre hc ha hN hout h hok.2⟩

end

/-! ## Memory after a block -/

section
variable [Labels] {env : Env} {S : SState} {m : MachineData}

/-- **A block's writes in an interval of region `ri`**: memory changed only there. -/
theorem sameOutside_hull (hm : Match env S m) (hwf : env.WF) {ri : Nat} {B : BitVec 64}
    {sz lo hi : Nat} (hb : env.regions[ri]? = some (B, sz)) (hhi : hi ≤ sz)
    (hall : writesIn S ri lo hi = true) :
    SameOutside env.mem0 m.dmem (InRange (B + BitVec.ofNat 64 lo) (hi - lo)) := by
  have hnw := hwf.noWrap ri B sz hb
  intro p hp
  apply hm.get?_mem0 hwf
  rintro ⟨w, hw, b, sz', hb', h1, h2⟩
  have := List.all_eq_true.mp hall w hw
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  obtain ⟨⟨hr, hlo⟩, hhi'⟩ := this
  rw [hr, hb] at hb'
  simp only [Option.some.injEq, Prod.mk.injEq] at hb'
  obtain ⟨rfl, rfl⟩ := hb'
  apply hp
  rw [Sym.inRange_iff (by rw [Sym.toNat_add_ofNat _ _ (by omega)]; omega),
    Sym.toNat_add_ofNat _ _ (by omega)]
  omega

/-- **Bytes stored from loads**. -/
theorem copy (hm : Match env S m) {r o r' o' n : Nat} {B : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (B, sz)) (hle : o + n ≤ sz) (hc : copies S.mem r o r' o' n = true)
    {bs : List UInt8} (hl : bs.length = n)
    (h : BytesAt env.mem0 (env.base r' + BitVec.ofNat 64 o') bs) :
    BytesAt m.dmem (B + BitVec.ofNat 64 o) bs := by
  intro i hi
  have hc := List.all_eq_true.mp hc i (List.mem_range.mpr (hl ▸ hi))
  rw [addr_add, hm.mem r B sz hb (o + i) (by omega)]
  unfold memByte
  split at hc
  · rename_i r'' off k u hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨rfl, hoff⟩, hu⟩, hk⟩ := hc
    rw [hf]
    simp only [Sym.eval, Option.some.injEq]
    rw [byteOf_load hu hk, hoff, ← addr_add, h i hi]
    rfl
  · cases hc

/-- **Bytes stored from indexed loads**, the index `I`. -/
theorem copyX (hm : Match env S m) {r o r' o' n : Nat} {I : Sym} {B : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (B, sz)) (hle : o + n ≤ sz)
    (hc : copiesX S.mem r o r' o' I n = true) {bs : List UInt8} (hl : bs.length = n)
    (h : BytesAt env.mem0 (env.base r' + BitVec.ofNat 64 (o' + (I.eval env).toNat)) bs) :
    BytesAt m.dmem (B + BitVec.ofNat 64 o) bs := by
  intro i hi
  have hc := List.all_eq_true.mp hc i (List.mem_range.mpr (hl ▸ hi))
  rw [addr_add, hm.mem r B sz hb (o + i) (by omega)]
  unfold memByte
  split at hc
  · rename_i r'' off idx k u hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨rfl, hoff⟩, rfl⟩, hu⟩, hk⟩ := hc
    rw [hf]
    simp only [Sym.eval, Option.some.injEq]
    rw [byteOf_load hu hk, show off + (idx.eval env).toNat + u = o' + (idx.eval env).toNat + i by
      omega, ← addr_add, h i hi]
    rfl
  · cases hc

omit [Labels] in
theorem getElem_wordBytes (v : BitVec 64) {i : Nat} (hi : i < (wordBytes (UInt64.ofBitVec v)).length) :
    (wordBytes (UInt64.ofBitVec v))[i] = byteOf v i := by
  have h := regBytes_eq_wordBytes v
  have hl : i < (regBytes v).length := by rw [h]; exact hi
  simp only [← h, regBytes, List.getElem_map, List.getElem_range]

/-- **A register stored whole**: its bytes. -/
theorem bytesAt_reg (hm : Match env S m) {r o : Nat} {B : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (B, sz)) (hle : o + 8 ≤ sz) {x : Reg64}
    (hc : holdsReg S.mem r o x = true) {v : UInt64} (hv : env.regs x = v.toBitVec) :
    BytesAt m.dmem (B + BitVec.ofNat 64 o) (wordBytes v) := by
  intro i hi
  have hi8 : i < 8 := by rwa [length_wordBytes] at hi
  have hc := List.all_eq_true.mp hc i (List.mem_range.mpr hi8)
  rw [addr_add, hm.mem r B sz hb (o + i) (by omega)]
  unfold memByte
  split at hc
  · rename_i y u hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨hy, rfl⟩ := hc
    cases Reg64.eq_of_beq hy
    rw [hf]
    simp only [Sym.eval, Option.some.injEq]
    rw [hv]
    exact (getElem_wordBytes v.toBitVec _).symm
  · cases hc

/-- **The low 4 bytes of a value stored**. -/
theorem bytesAt_low (hm : Match env S m) {r o : Nat} {B : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (B, sz)) (hle : o + 4 ≤ sz) {v : Sym}
    (hc : holdsLow S.mem r o v = true) {bs : List UInt8} (hv : Low4 (v.eval env) bs) :
    BytesAt m.dmem (B + BitVec.ofNat 64 o) bs := by
  intro i hi
  have hi4 : i < 4 := by rw [hv.1] at hi; exact hi
  have hc := List.all_eq_true.mp hc i (List.mem_range.mpr hi4)
  rw [beq_iff_eq] at hc
  rw [addr_add, hm.mem r B sz hb (o + i) (by omega)]
  unfold memByte
  rw [hc]
  simp only [Option.some.injEq]
  rw [hv.2 i hi4, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

end

/-- Words' bytes from each word's. -/
theorem bytesAt_words {d : DataMem} :
    ∀ (ws : List UInt64) {a : BitVec 64},
      (∀ i (h : i < ws.length), BytesAt d (a + BitVec.ofNat 64 (8 * i)) (wordBytes ws[i])) →
      BytesAt d a (Native.Keccak.wordsBytes ws)
  | [], _, _ => fun i hi => by simp [Native.Keccak.wordsBytes] at hi
  | w :: ws, a, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.mul_zero, List.getElem_cons_zero] at h0
    rw [show a + BitVec.ofNat 64 0 = a by simp] at h0
    have : Native.Keccak.wordsBytes (w :: ws) = wordBytes w ++ Native.Keccak.wordsBytes ws := rfl
    rw [this]
    refine BytesAt.append h0 (bytesAt_words ws fun i hi => ?_)
    have := h (i + 1) (by simp; omega)
    rw [List.getElem_cons_succ] at this
    rw [length_wordBytes, addr_add, show 8 + 8 * i = 8 * (i + 1) by omega]
    exact this

/-- A region pointer's value. -/
theorem eval_ptr [Labels] {m : MachineData} {regions : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {i : Nat} {b : BitVec 64} {n : Nat}
    (h : regions[i]? = some (b, n)) (o : Int) :
    Sym.eval (Env.ofMachine m regions vars ret) (.ptr i o) = b + BitVec.ofInt 64 o := by
  show Env.base _ i + _ = _
  rw [Env.base_ofMachine m regions vars ret h]

/-- A pointer into the frame, region 0 its base. -/
theorem eval_base [Labels] (r : Run) {m : MachineData} {regions : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {i n : Nat} (h : regions[i]? = some (r.base, n))
    (o : Nat) : Sym.eval (Env.ofMachine m regions vars ret) (.ptr i (o : Int)) = r.off o := by
  rw [eval_ptr h, BitVec.ofInt_natCast]
  rfl

/-! ## The low bytes of values -/

theorem Low4.trunc {v : BitVec 64} {bs : List UInt8} (h : Low4 v bs) :
    Low4 (UnOp.apply .trunc .W32 v) bs := by
  refine ⟨h.1, fun t ht ↦ ?_⟩
  rw [← h.2 t ht]
  apply byteOf_eq_of_getLsbD
  intro j hj
  simp only [UnOp.apply, ext, low, Width.bits, BitVec.getLsbD_setWidth]
  simp only [show 8 * t + j < 32 by omega, decide_true, Bool.true_and, show 8 * t + j < 64 by omega]

theorem Low4.bswap {v : BitVec 64} {bs : List UInt8} (h : Low4 v bs) :
    Low4 (UnOp.apply .bswap .W32 v) bs.reverse := by
  refine ⟨by rw [List.length_reverse, h.1], fun t ht ↦ ?_⟩
  rw [byteOf_bswap32 v ht, h.2 (3 - t) (by omega), List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_reverse (by rw [h.1]; omega), h.1]

theorem Low4.of_eq {v v' : BitVec 64} {bs : List UInt8} (h : Low4 v bs) (he : v' = v) :
    Low4 v' bs := he ▸ h

theorem Low4.load [Labels] {env : Env} {r o : Nat} {bs : List UInt8} (hl : bs.length = 4)
    (h : BytesAt env.mem0 (env.base r + BitVec.ofNat 64 o) bs) : Low4 (env.load r o 4) bs := by
  refine ⟨hl, fun t ht ↦ ?_⟩
  rw [byteOf_load ht (by decide), ← addr_add, h t (by omega), List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega)]

theorem Low4.word {x : UInt64} : Low4 x.toBitVec (be32 x.toUInt32).reverse := by
  refine ⟨by simp [be32], fun t ht ↦ ?_⟩
  have h := byteOf_eq_toUInt32 x.toBitVec ht
  rw [h]
  interval_cases t <;> simp [be32]

/-! ## Registers kept -/

section
variable [Labels] {env : Env}

theorem keepsRegs_regs {rs : List Reg64} {S₀ S : SState} {m m' : MachineData}
    (hm : Match env S₀ m) (hm' : Match env S m') (h : keepsRegs rs S₀ S = true) :
    ∀ x ∈ rs, m'.regs.get64 x = m.regs.get64 x := by
  simp only [keepsRegs, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  intro x hx
  obtain ⟨hs, he⟩ := h x hx
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  exact Match.reg_eq hm hm' hv (he.trans hv)

end

/-! ## Loops and addresses -/

/-- **A counted loop**: from turn `j < N` in `P j`, each turn reaches the exit `Q` or turn
`j + 1 < N`. -/
theorem count_loop {σ : Type} {tr : σ → (σ → Prop) → Prop} {Q : σ → Prop} {P : Nat → σ → Prop}
    (N : Nat)
    (step : ∀ j s, j < N → P j s → Eventually tr (fun s' => Q s' ∨ (j + 1 < N ∧ P (j + 1) s')) s) :
    ∀ {j s}, j < N → P j s → Eventually tr Q s := by
  intro j s hj h
  refine loop (fun n s => ∃ j, j < N ∧ n = N - j ∧ P j s) (fun n s ⟨j, hj, hn, h⟩ => ?_)
    ⟨j, hj, rfl, h⟩
  refine eventually_weaken _ _ _ _ (fun s' h' => ?_) (step j s hj h)
  rcases h' with hq | ⟨hj', hp⟩
  · exact Or.inl hq
  · exact Or.inr ⟨N - (j + 1), by omega, j + 1, hj', rfl, hp⟩

/-- An address a negative constant below another. -/
theorem alias_neg {A B : BitVec 64} (k : Nat) (h : A + BitVec.ofNat 64 k = B) :
    A = B + BitVec.ofInt 64 (-(k : Int)) := by
  subst h
  rw [BitVec.ofInt_neg, BitVec.ofInt_natCast, BitVec.add_assoc]
  simp

/-- An address a constant above another. -/
theorem alias_pos {A B : BitVec 64} (k : Nat) (h : A = B + BitVec.ofNat 64 k) :
    A = B + BitVec.ofInt 64 (k : Int) := by
  rw [BitVec.ofInt_natCast]
  exact h

/-- Linear arithmetic of addresses: the frame's and the input's, with constants. -/
macro "bv_lin" : tactic => `(tactic| (
  try simp only [Run.off, Run.input, ctx]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  try simp only [show Width.W64.bits = 64 from rfl]
  omega))

/-- **A loop's exit test**: `X ≠ L` jumps back, `X = L` falls through. -/
theorem pc_cond [Labels] {env : Env} {X : Sym} {L : Nat} {lab : Label} {next : Int64}
    {st : MachineState} (hpc : PcOk env (.cond (.not (.cmp .eq .W64 X (.lit L))) lab) next st)
    {v : Nat} (hv : X.eval env = BitVec.ofNat 64 v) (hv' : v < 2 ^ 64) (hL : L < 2 ^ 64) :
    (v ≠ L → st.pc = Labels.label lab) ∧ (v = L → st.pc = next) := by
  simp only [PcOk, SBool.eval, CmpOp.apply, low_W64, Sym.eval, hv] at hpc
  constructor
  · intro h
    rw [Sym.ite_pos] at hpc
    · exact hpc
    · simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
      intro he
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv', Nat.mod_eq_of_lt hL] at this
      exact h this
  · rintro rfl
    rw [Sym.ite_neg (by simp)] at hpc
    exact hpc

/-! ## The frame's invariant after a block -/

section
variable (r : Run) [Labels]

/-- **Frame bytes kept** by a change in another range of the frame. -/
theorem fact_keep (hpre : r.Pre) {d d' : DataMem} {o a n L : Nat} {bs : List UInt8}
    (h : BytesAt d (r.off o) bs) (hs : SameOutside d d' (InRange (r.off a) n)) (hl : bs.length = L)
    (hd : o + L ≤ a ∨ a + n ≤ o) (ho : o + L ≤ 29384) (ha : a + n ≤ 29384) :
    BytesAt d' (r.off o) bs :=
  bytesAt_of_sameOutside h hs fun i hi ↦ by
    rw [off_add]
    exact r.not_inRange_off hpre ha (by omega) (by omega)

/-- **The frame's invariant after a block** that writes only the frame's bytes `d + lo .. d + hi`
(region `ri` the frame from `d`) below the saved registers, RSP the base. -/
theorem frame_of_hull (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m)
    {regions : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} {ri d n lo hi : Nat}
    (hb : regions[ri]? = some (r.off d, n)) (hn : hi ≤ n) (hlo : lo ≤ hi) (hhi : d + hi ≤ 29336)
    {S' : SState} (hm' : Match (Env.ofMachine m regions vars ret) S' m')
    (hwf : (Env.ofMachine m regions vars ret).WF) (hw : writesIn S' ri lo hi = true)
    (hsp : rspOf m' = r.base) :
    r.Frame m' ∧ SameOutside m.dmem m'.dmem (InRange (r.off (d + lo)) (hi - lo)) := by
  have hout := sameOutside_hull hm' hwf hb (lo := lo) (hi := hi) hn hw
  rw [off_add] at hout
  exact ⟨Run.Frame.of_change hF.2.1 hF.2.2.1 hF.2.2.2 hsp hout
    (fun _ h ↦ r.inRange_off hpre (by omega) h) (hm'.kept hwf), hout⟩

end

end

end NativeRustcX64.SphincsVerifyProof.Parse
