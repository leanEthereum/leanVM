import Rv64Verifier.Proofs.Walk.Body10

/-!
# `walk`: the bus blocks' loop, `count` (R10)

`count.extend(table.count_columns().iter().map(|&local| block(&vec![col(local, 0)])))`: the
count columns of the `i`-th opcode are a `.rodata` slice (`countRod`), `reserve` makes room
(`Vec<BusBlock>::reserve`), then per column `alloc(8, 24)`, `col(local, 0)` into it, `clone` of
that one-form slice into `sp + 1728` and the block stored at the buffer's end; the length is
stored back after the loop. During the loop `count` is its buffer `p`, capacity `c` and the `n`
blocks stored so far (`VecsC`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror
  Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The count columns' slice of each opcode. -/
def colPtr : Nat → Word
  | 2 => 0xa0000308
  | 4 => 0xa0000258
  | 5 => 0xa0000328
  | _ => 0xa0000218

theorem countRod {u : MachineState} (ro : RodataOk u) {i : Nat} (hi : i < 6) :
    u.getMem (0xa0000400 + BitVec.ofNat 64 i * 16) = colPtr i ∧
    u.getMem (0xa0000400 + BitVec.ofNat 64 i * 16 + 8) =
      BitVec.ofNat 64 (countColumnsRust.getD i []).length ∧
    ∀ j < (countColumnsRust.getD i []).length,
      u.getMem (colPtr i + BitVec.ofNat 64 (8 * j)) =
        BitVec.ofNat 64 ((countColumnsRust.getD i []).getD j 0) := by
  interval_cases i
  all_goals refine ⟨ro.word, ro.word, fun j hj ↦ ?_⟩
  · have : j < 4 := lt_of_lt_of_eq hj (by decide)
    interval_cases j <;> exact ro.word
  · have : j < 4 := lt_of_lt_of_eq hj (by decide)
    interval_cases j <;> exact ro.word
  · have : j < 2 := lt_of_lt_of_eq hj (by decide)
    interval_cases j <;> exact ro.word
  · have : j < 4 := lt_of_lt_of_eq hj (by decide)
    interval_cases j <;> exact ro.word
  · have : j < 4 := lt_of_lt_of_eq hj (by decide)
    interval_cases j <;> exact ro.word
  · have : j < 27 := lt_of_lt_of_eq hj (by decide)
    interval_cases j <;> exact ro.word

/-- Blocks whose bytes were copied from `p` to `p'`, their coordinates' footprints kept. -/
theorem blocksAt_moved {c t : MachineState} {w : Word → Prop} (fr : Layout.DFrame c t w)
    {p p' : Word} {cc c' n : Nat} (hok : BlocksSound c p cc n)
    (hb : bytesAt t p' (48 * n) = bytesAt c p (48 * n)) (hp' : Buf t p' (c' * 48) 8) (hn : n ≤ c')
    (hd : ∀ x, blocksDeep c p n x → ¬ w x) (hsep : ∀ x, blocksDeep c p n x → ¬ Within x p' (48 * c'))
    (hheap : HeapOk c) (mono : heapNext c ≤ heapNext t) :
    blocksAt t p' n = blocksAt c p n ∧ BlocksSound t p' c' n ∧ blocksDeep t p' n = blocksDeep c p n := by
  have hpa := hp'.1
  have hpb := hok.buf.1
  have g (j : Nat) (hj : j < n) (k : Nat) (hk : k + 8 ≤ 48) (hk8 : k % 8 = 0) :
      t.getMem (p' + BitVec.ofNat 64 (48 * j) + BitVec.ofNat 64 k) =
        c.getMem (p + BitVec.ofNat 64 (48 * j) + BitVec.ofNat 64 k) := by
    rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact getMem_eq_of_bytesAt hb hpa hpb (by omega) (by omega)
  have hel (j : Nat) (hj : j < n) :=
    formVecOf_moved fr (e := p + BitVec.ofNat 64 (48 * j)) (e' := p' + BitVec.ofNat 64 (48 * j))
      (by simpa using g j hj 0 (by decide) (by decide)) (g j hj 8 (by decide) (by decide))
      (g j hj 16 (by decide) (by decide)) (hok.elems j hj) (fun x hx ↦ hd x ⟨j, hj, hx⟩) hheap mono
  have hdeep : blocksDeep t p' n = blocksDeep c p n := by
    funext x
    apply propext
    simp only [blocksDeep]
    exact exists_congr fun j ↦ ⟨fun ⟨hj, hx⟩ ↦ ⟨hj, by rwa [(hel j hj).2.2] at hx⟩,
      fun ⟨hj, hx⟩ ↦ ⟨hj, by rwa [(hel j hj).2.2]⟩⟩
  refine ⟨?_, ⟨hp', hn, fun j hj ↦ (hel j hj).2.1, fun x hx ↦ ?_⟩, hdeep⟩
  · simp only [blocksAt]
    refine List.map_congr_left fun j hm ↦ ?_
    have hj := List.mem_range.mp hm
    have g24 : t.getMem (p' + BitVec.ofNat 64 (48 * j) + 24) =
        c.getMem (p + BitVec.ofNat 64 (48 * j) + 24) := g j hj 24 (by decide) (by decide)
    have g32 : t.getMem (p' + BitVec.ofNat 64 (48 * j) + 32) =
        c.getMem (p + BitVec.ofNat 64 (48 * j) + 32) := g j hj 32 (by decide) (by decide)
    have g40 : t.getMem (p' + BitVec.ofNat 64 (48 * j) + 40) =
        c.getMem (p + BitVec.ofNat 64 (48 * j) + 40) := g j hj 40 (by decide) (by decide)
    simp only [blockOf, (hel j hj).1, g24, g32, g40]
  · rw [hdeep] at hx; exact hsep x hx

/-- What a `GrowW` frame of a `Vec<BusBlock>` reaching memory from `lo` on writes is in `X10`. -/
theorem growX10 {OI : MachineState → Word → List (List Opening) → Prop} {s c t : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} {lo : Nat} (h : Base10 OI s c A k R Q B lo) {a : Word}
    (ha1 : (s.getReg .x2 - 2080).toNat ≤ a.toNat) (ha2 : a.toNat + 24 ≤ (s.getReg .x2 - 104).toNat)
    (hok : BlocksOk c a) (hf : ∀ x, blocksFoot c a x → lo ≤ x.toNat)
    (mono : heapNext c ≤ heapNext t) {x : Word} (hx : GrowW s c t a x) : X10 s lo B t x := by
  have hbd := BlocksSound.bounds hok
  have hl := h.loLe
  simp only [GrowW] at hx
  rcases hx with hx | hx | hx | hx | hx
  · exact Or.inl (Or.inl ⟨by simp only [Within] at hx; omega, by simp only [Within] at hx; omega⟩)
  · refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨hf x (Or.inl hx), ?_⟩))))
    simp only [Within] at hx
    rcases hbd.2 with h0 | h0
    · rw [h0] at hx; omega
    · omega
  · exact Or.inl (Or.inr (Or.inr (Or.inl hx)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hx))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨by have := hx.1; omega, hx.2⟩))))

/-- A frame word apart from the grown `Vec`'s header is kept by a `GrowW` frame. -/
theorem growFrameWord {s c t : MachineState} (hpre : WalkPre s) (hc : HeapOk c) (ht : HeapOk t)
    {a : Word} (hok : BlocksOk c a) {w : Word → Prop} (fr : Layout.DFrame c t w)
    (hw : ∀ x, w x → GrowW s c t a x) {x : Word} (h1 : (s.getReg .x2 - 2656).toNat ≤ x.toNat)
    (h2 : x.toNat + 8 ≤ (s.getReg .x2 - 104).toNat) (h3 : Apart x 8 a 24) :
    t.getMem x = c.getMem x := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hbd := BlocksSound.bounds hok
  have hci := hc.hi
  have hhi := ht.hi
  simp only [heapEnd] at hci hhi
  refine fr x (fun y hy hwy ↦ ?_) (by addr_omega [h2, hb1])
  have := hw y hwy
  simp only [GrowW] at this
  rcases this with h4 | h4 | h4 | h4 | h4
  · simp only [Within, Apart] at hy h4 h3; addr_omega [hy, h4, h3]
  · simp only [Within] at hy h4
    rcases hbd.2 with h0 | h0
    · rw [h0] at h4; omega
    · addr_omega [hy, h4, h0, hci, h1, hb1]
  · simp only [Within] at hy h4; addr_omega [hy, h4, h1, hb1]
  · simp only [Within, nextAddr] at hy h4; addr_omega [hy, h4, h1, hb1]
  · simp only [Within, Fresh, heapNext] at hy h4 hhi; addr_omega [hy, h4, h1, hb1, hhi]

/-- A heap word below `lo` is kept by a `GrowW` frame of a `Vec` reaching memory from `lo` on. -/
theorem growHeapWord {s c t : MachineState} (hpre : WalkPre s) (hc : HeapOk c) {lo : Nat}
    (hlo : lo ≤ heapNext c) {a : Word} (ha1 : (s.getReg .x2 - 2080).toNat ≤ a.toNat)
    (hf : ∀ x, blocksFoot c a x → lo ≤ x.toNat) {w : Word → Prop} (fr : Layout.DFrame c t w)
    (hw : ∀ x, w x → GrowW s c t a x) {x : Word} (h2 : x.toNat + 8 ≤ lo) : t.getMem x = c.getMem x := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hci := hc.hi
  simp only [heapEnd] at hci
  refine fr x (fun y hy hwy ↦ ?_) (by addr_omega [h2, hlo, hci])
  have := hw y hwy
  simp only [GrowW] at this
  rcases this with h4 | h4 | h4 | h4 | h4
  · simp only [Within] at hy h4; addr_omega [hy, h4, h2, hlo, hci, ha1, hb1]
  · have := hf y (Or.inl h4); simp only [Within] at hy; omega
  · simp only [Within] at hy h4; addr_omega [hy, h4, h2, hlo, hci, hb1]
  · simp only [Within, nextAddr] at hy h4; addr_omega [hy, h4, h2, hlo, hci]
  · simp only [Within, Fresh] at hy h4; omega

theorem mul48 (L : Word) : L * 32 + L * 16 = BitVec.ofNat 64 (48 * L.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have h32 : (32 : Word).toNat = 32 := rfl
  have h16 : (16 : Word).toNat = 16 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h32, h16]
  omega

/-- `count`'s buffer `p` of capacity `c` and what its first `n` blocks reach. -/
@[rv_addr] def cFoot (u : MachineState) (p : Word) (c n : Nat) (x : Word) : Prop :=
  Within x p (48 * c) ∨ blocksDeep u p n x

/-- `push` and `pull` as in `Vecs10`; `count` as its buffer and its first `n` blocks. -/
structure VecsC (s u : MachineState) (lo : Nat) (P1 P2 P3 : List BusBlockRust) (p : Word)
    (c n : Nat) : Prop where
  push : BlocksOk u (s.getReg .x2 - 416)
  pull : BlocksOk u (s.getReg .x2 - 224)
  pushV : blocksOf u (s.getReg .x2 - 416) = P1
  pullV : blocksOf u (s.getReg .x2 - 224) = P2
  count : BlocksSound u p c n
  countV : blocksAt u p n = P3
  fresh : ∀ x, (blocksFoot u (s.getReg .x2 - 416) x ∨ blocksFoot u (s.getReg .x2 - 224) x ∨
    cFoot u p c n x) → lo ≤ x.toNat
  d1 : ∀ x, blocksFoot u (s.getReg .x2 - 416) x → ¬ blocksFoot u (s.getReg .x2 - 224) x
  d2 : ∀ x, blocksFoot u (s.getReg .x2 - 416) x → ¬ cFoot u p c n x
  d3 : ∀ x, blocksFoot u (s.getReg .x2 - 224) x → ¬ cFoot u p c n x

/-- The number of count columns of opcode `i`. -/
abbrev nCols (i : Nat) : Nat := (countColumnsRust.getD i []).length

theorem nCols_pos {i : Nat} (hi : i < 6) : 0 < nCols i := by interval_cases i <;> decide

theorem nCols_le {i : Nat} (hi : i < 6) : nCols i ≤ 27 := by interval_cases i <;> decide

/-- The count blocks of the first `j` count columns. -/
def countPre (A : List E) (i j : Nat) : List BusBlockRust :=
  ((countColumnsRust.getD i []).take j).map fun l ↦ blkOf A i [colRust l 0]

/-- In the count loop at `0x80002f9c`, `j` of the `i`-th table's count blocks stored. -/
structure CountAt (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo i : Nat)
    (P : List BusBlockRust × List BusBlockRust × List BusBlockRust) (p : Word) (c L0 j : Nat) :
    Prop where
  base : Base10 OI s u A k R Q B lo
  op5 : u.getMem (B + 472) = 5
  vecs : VecsC s u lo P.1 P.2.1 (P.2.2 ++ countPre A i j) p c (L0 + j)
  lt : i < 6
  jlt : j ≤ nCols i
  room : L0 + nCols i ≤ c
  hdr : u.getMem (s.getReg .x2 - 512) = BitVec.ofNat 64 c ∧ u.getMem (s.getReg .x2 - 504) = p ∧
    u.getMem (s.getReg .x2 - 496) = BitVec.ofNat 64 L0
  x9 : u.getReg .x9 = BitVec.ofNat 64 (i + 1)
  x18 : u.getReg .x18 = s.getReg .x2 - 1488
  x19 : u.getReg .x19 = s.getReg .x2 - 1344
  x21 : u.getReg .x21 = 0xa0000400
  x22 : u.getReg .x22 = B + BitVec.ofNat 64 (80 * i)
  x20 : u.getReg .x20 = p + BitVec.ofNat 64 (48 * (L0 + j))
  x23 : u.getReg .x23 = BitVec.ofNat 64 (L0 + j)
  x24 : u.getReg .x24 = BitVec.ofNat 64 (nCols i - j)
  x27 : u.getReg .x27 = colPtr i + BitVec.ofNat 64 (8 * j)
  n : u.getMem (s.getReg .x2 - 2472) = 6
  hgt : u.getMem (s.getReg .x2 - 1488) = BitVec.ofNat 64 ((tableLogHeightsRust (rowsOf A)).getD i 0)
  row : u.getMem (s.getReg .x2 - 1344) = (rowsOf A).getD i 0

/-- `VecsC` is kept by writes in the frame apart from `push`'s and `pull`'s headers. -/
theorem VecsC.keepFrame {s c t : MachineState} {lo : Nat} {P1 P2 P3 : List BusBlockRust}
    {p : Word} {cc n : Nat} (hpre : WalkPre s) (V : VecsC s c lo P1 P2 P3 p cc n) (hc : HeapOk c)
    (mono : heapNext c ≤ heapNext t) {w : Word → Prop}
    (fr : Layout.DFrame c t w) (hw : ∀ x, w x → (s.getReg .x2 - 2656).toNat ≤ x.toNat ∧
      x.toNat < (s.getReg .x2 - 104).toNat ∧ ¬ Within x (s.getReg .x2 - 416) 24 ∧
      ¬ Within x (s.getReg .x2 - 224) 24) :
    VecsC s t lo P1 P2 P3 p cc n := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hci := hc.hi
  simp only [heapEnd] at hci
  have K (a : Word) (hok : BlocksOk c a) (ha1 : (s.getReg .x2 - 2080).toNat ≤ a.toNat)
      (ha2 : a.toNat + 24 ≤ (s.getReg .x2 - 104).toNat)
      (hh : ∀ x, w x → ¬ Within x a 24) :=
    vecKeep fr hok (by addr_omega [ha2, hb1, hb2]) (fun x hx hwx ↦ hh x hwx hx) (fun x hx hwx ↦ by
      have h1 := hok.foot_below hx
      have h2 := hw x hwx
      simp only [heapStart] at h1
      addr_omega [h1, h2, hci, hb1]) hc mono
  have kp := K _ V.push (by addr_omega [hb1]) (by addr_omega [hb1]) fun x hx ↦ (hw x hx).2.2.1
  have kl := K _ V.pull (by addr_omega [hb1]) (by addr_omega [hb1]) fun x hx ↦ (hw x hx).2.2.2
  have hbd := BlocksSound.bounds V.count
  have hle := V.count.le
  have kc := blocksAt_frame fr V.count (fun x hx hwx ↦ by
      have h2 := hw x hwx
      simp only [Within] at hx
      rcases hbd.2 with h0 | h0
      · omega
      · simp only [heapStart] at h0; addr_omega [hx, h0, h2, hci, hb1, hle])
    (fun x hx hwx ↦ by
      have h1 := BlocksSound.deep_below V.count hx
      have h2 := hw x hwx
      simp only [heapStart] at h1
      addr_omega [h1, h2, hci, hb1]) hc mono
  have hcf : cFoot t p cc n = cFoot c p cc n := by
    funext x; simp only [cFoot, kc.2.2]
  refine ⟨kp.1, kl.1, by rw [kp.2.1]; exact V.pushV, by rw [kl.2.1]; exact V.pullV, kc.2.1,
    by rw [kc.1]; exact V.countV, ?_, ?_, ?_, ?_⟩ <;> simp only [kp.2.2, kl.2.2, hcf]
  · exact V.fresh
  · exact V.d1
  · exact V.d2
  · exact V.d3

theorem ofNat_toNat' (x : Word) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp

set_option maxRecDepth 8192 in
/-- The count columns' slice, `count.reserve(n)`, and `count`'s buffer and length loaded. -/
theorem countPrep (hRes : ReserveFreshSpec 0x800060bc 48 8)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo i : Nat}
    {P : List BusBlockRust × List BusBlockRust × List BusBlockRust} (hpre : WalkPre s)
    (hpc : u.pc = 0x80002f5c) (h : Mid10 OI s u A k R Q B lo i P) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨ (t.pc = 0x80002f9c ∧ ∃ p c L0,
      CountAt OI s t A k R Q B lo i P p c L0 0)) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have H := h.base
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := H.inv.sp
  have hi := h.lt
  have ro := H.inv.rodata hpre
  obtain ⟨r0, r8, -⟩ := countRod ro hi
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80002f5c_spec hpc (by
    rv_eval [h.x21, h.x10]
    simp only [Sym.validAccess_eight]
    interval_cases i <;> decide)
  have m₁ := b80002f5c_mem_same h₁
  have k₁ := b80002f5c_keeps h₁
  have hn₁ : heapNext u₁ = heapNext u := by simp only [heapNext, m₁]
  have hv₁ : HeapOk u₁ := ⟨hn₁ ▸ H.inv.heap.lo, hn₁ ▸ H.inv.heap.hi⟩
  have B₁ := H.same hpre m₁ (k₁ .x2 (by decide))
  have V₁ := h.vecs.keepFrame hpre H.inv.heap hn₁.ge (Layout.DFrame.of_same m₁ (fun _ ↦ False))
    fun _ h ↦ h.elim
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₁ .x2 (by decide)]; exact sp
  have e2144 : u.getReg .x2 + 2144 = s.getReg .x2 - 512 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 512 := by rw [b80002f5c_x10 h₁, e2144]
  have x11₁ : u₁.getReg .x11 = BitVec.ofNat 64 (nCols i) := by
    rw [b80002f5c_x11 h₁, h.x21, h.x10]; exact r8
  -- `count.reserve(n)`
  have hab := hpre.stack.above
  have hx := hpre.stack.next
  rw [stackLo_eq] at hab hx
  rw [stack_eq] at hx
  simp only [heapEnd] at hab
  have pre : ReservePre 48 8 u₁ := {
    heap := hv₁
    self := by
      rw [x10₁]; exact validMemRange_of (by addr_omega [hb1, hb3]) (Or.inr ⟨by addr_omega [hb1],
        by addr_omega [hb1, hb2]⟩)
    vec := by rw [x10₁]; exact BlocksSound.vecOk V₁.count
    stack := stk10 hpre B₁.inv (by decide) (by decide)
    selfFree := by
      rw [x10₁]; exact ⟨Or.inr (by addr_omega [hab, hb1]), by simp only [Apart]; addr_omega [hx, hb1]⟩
    selfStack := by rw [x10₁, stackLo_callee B₁.inv]; simp only [Apart]; addr_omega [hb1] }
  obtain ⟨t₁, hrt₁, ⟨hpct₁, hp₁, post, hsame⟩ | hd⟩ := hRes u₁ (b80002f5c_pc h₁) pre
  swap
  · exact ⟨t₁, hr₁.trans hrt₁, Or.inl hd⟩
  have pcap := post.cap
  have pvec := post.vec
  have plen := post.len
  have pbytes := post.bytes
  have pframe := post.frame
  have phv := post.heap
  have pmono := post.mono
  rw [x10₁, x11₁] at pcap
  rw [x10₁] at pvec plen pbytes pframe hsame
  have hhi := phv.hi
  have hci := hv₁.hi
  simp only [heapEnd] at hhi hci
  have fr : Layout.DFrame u₁ t₁ (GrowW s u₁ t₁ (s.getReg .x2 - 512)) := (pframe.dframe).mono fun x hx ↦ by
    rcases hx with hx | hx | hx | hx
    · exact Or.inl (by simp only [Within] at hx ⊢; omega)
    · rw [stackLo_callee B₁.inv] at hx
      exact Or.inr (Or.inr (Or.inl (by simp only [Within] at hx ⊢; addr_omega [hx, hb1])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hx)))
  have hcf : ∀ x, blocksFoot u₁ (s.getReg .x2 - 512) x → lo ≤ x.toNat := fun x hx ↦ V₁.fresh x (Or.inr (Or.inr hx))
  have B₂ : Base10 OI s t₁ A k R Q B lo := B₁.keep hpre fr (fun x hx ↦ growX10 B₁
    (by addr_omega [hb1]) (by addr_omega [hb1]) V₁.count hcf pmono hx) phv pmono
    (hp₁ .x2 (by decide))
  have kp := growKeep hpre hv₁ phv pmono fr (fun _ h ↦ h) (b := s.getReg .x2 - 416)
    (by addr_omega [hb1]) (by addr_omega [hb1]) (by addr_omega [hb1])
    (by simp only [Apart]; addr_omega [hb1]) V₁.count V₁.push
    fun x hx hb ↦ V₁.d2 x hx (Or.inl hb)
  have kl := growKeep hpre hv₁ phv pmono fr (fun _ h ↦ h) (b := s.getReg .x2 - 224)
    (by addr_omega [hb1]) (by addr_omega [hb1]) (by addr_omega [hb1])
    (by simp only [Apart]; addr_omega [hb1]) V₁.count V₁.pull
    fun x hx hb ↦ V₁.d3 x hx (Or.inl hb)
  -- `count`'s blocks, at the buffer `reserve` leaves
  have hcnt := V₁.count
  have hle0 := hcnt.le
  have hbuf' := BlocksSound.bounds (n := 0) ⟨pvec.raw, Nat.zero_le _,
    fun _ h ↦ absurd h (Nat.not_lt_zero _), fun _ ⟨_, h, _⟩ ↦ absurd h (Nat.not_lt_zero _)⟩
  have hdeep_below : ∀ x, blocksDeep u₁ (vecPtr u₁ (s.getReg .x2 - 512)) (vecLen u₁ (s.getReg .x2 - 512)).toNat x → heapStart ≤ x.toNat ∧ x.toNat < heapNext u₁ :=
    fun x hx ↦ BlocksSound.deep_below hcnt hx
  have mv := blocksAt_moved fr (p' := vecPtr t₁ (s.getReg .x2 - 512))
    (c' := (vecCap t₁ (s.getReg .x2 - 512)).toNat) hcnt
    (bytesAt_eq_iff.mpr fun j hj ↦ bytesAt_eq_iff.mp pbytes j (by
      have := hcnt.le; omega))
    pvec.raw (by rw [← plen]; exact pvec.len)
    (fun x hx hw ↦ by
      have hdb := hdeep_below x hx
      simp only [heapStart] at hdb
      rcases hw with hw | hw | hw | hw | hw
      · simp only [Within] at hw; addr_omega [hw, hdb, hci, hb1]
      · exact hcnt.sep x hx hw
      · simp only [Within] at hw; addr_omega [hw, hdb, hci, hb1]
      · simp only [Within, nextAddr] at hw; addr_omega [hw, hdb, hci]
      · simp only [Fresh] at hw; omega)
    (fun x hx hw ↦ by
      rcases hsame with ⟨e1, e2⟩ | hnb
      · simp only [e1, e2] at hw; exact hcnt.sep x hx hw
      · have hdb := hdeep_below x hx
        simp only [NewBuf, Within] at hnb hw
        rcases hnb.2 with h0 | h0
        · omega
        · omega)
    hv₁ pmono
  -- `count` as a buffer and its blocks
  have hP3 : blocksAt t₁ (vecPtr t₁ (s.getReg .x2 - 512)) (vecLen u₁ (s.getReg .x2 - 512)).toNat =
      P.2.2 ++ countPre A i 0 := by
    rw [mv.1]; simp only [countPre, List.take_zero, List.map_nil, List.append_nil]; exact V₁.countV
  have hnew : ∀ x, Within x (vecPtr t₁ (s.getReg .x2 - 512))
      (48 * (vecCap t₁ (s.getReg .x2 - 512)).toNat) →
      Within x (vecPtr u₁ (s.getReg .x2 - 512)) (48 * (vecCap u₁ (s.getReg .x2 - 512)).toNat) ∨
        heapNext u₁ ≤ x.toNat := fun x hx ↦ by
    rcases hsame with ⟨e1, e2⟩ | hnb
    · rw [e1, e2] at hx; exact Or.inl hx
    · simp only [NewBuf, Within] at hnb hx
      rcases hnb.2 with h0 | h0
      · omega
      · exact Or.inr (by omega)
  have VC : VecsC s t₁ lo P.1 P.2.1 (P.2.2 ++ countPre A i 0) (vecPtr t₁ (s.getReg .x2 - 512))
      (vecCap t₁ (s.getReg .x2 - 512)).toNat (vecLen u₁ (s.getReg .x2 - 512)).toNat := by
    refine ⟨kp.1, kl.1, by rw [kp.2.1]; exact V₁.pushV, by rw [kl.2.1]; exact V₁.pullV, mv.2.1,
      hP3, fun x hx ↦ ?_, fun x hx hy ↦ ?_, fun x hx hy ↦ ?_, fun x hx hy ↦ ?_⟩
    · rw [kp.2.2, kl.2.2] at hx
      rcases hx with hx | hx | hx | hx
      · exact V₁.fresh x (Or.inl hx)
      · exact V₁.fresh x (Or.inr (Or.inl hx))
      · rcases hnew x hx with h | h
        · exact V₁.fresh x (Or.inr (Or.inr (Or.inl h)))
        · have := B₁.loLe; omega
      · rw [mv.2.2] at hx; exact V₁.fresh x (Or.inr (Or.inr (Or.inr hx)))
    · rw [kp.2.2] at hx; rw [kl.2.2] at hy; exact V₁.d1 x hx hy
    · rw [kp.2.2] at hx
      rcases hy with hy | hy
      · rcases hnew x hy with h | h
        · exact V₁.d2 x hx (Or.inl h)
        · have := (V₁.push.foot_below hx).2; omega
      · rw [mv.2.2] at hy; exact V₁.d2 x hx (Or.inr hy)
    · rw [kl.2.2] at hx
      rcases hy with hy | hy
      · rcases hnew x hy with h | h
        · exact V₁.d3 x hx (Or.inl h)
        · have := (V₁.pull.foot_below hx).2; omega
      · rw [mv.2.2] at hy; exact V₁.d3 x hx (Or.inr hy)
  -- `count`'s buffer and length in registers
  have pc₂ : t₁.pc = 0x80002f84 := by rw [hpct₁, returnAddress_eq, b80002f5c_x1 h₁]; decide
  have x20₁ : t₁.getReg .x20 = s.getReg .x2 - 512 := by
    rw [hp₁ .x20 (by decide), k₁ .x20 (by decide)]; exact h.x20
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80002f84_spec pc₂ (by
    rv_eval [x20₁]
    simp only [Sym.validAccess_eight]
    and_intros <;> addr_omega [hb1, hb2, hb3])
  have m₂ := b80002f84_mem_same h₂
  have k₂ := b80002f84_keeps h₂
  have hn₂ : heapNext u₂ = heapNext t₁ := by simp only [heapNext, m₂]
  have e8 : s.getReg .x2 - 512 + (8 : Word) = s.getReg .x2 - 504 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e16 : s.getReg .x2 - 512 + (16 : Word) = s.getReg .x2 - 496 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have kr (r : Reg) (hr : r ∈ calleeSaved) (h1 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x12, .x13,
      .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x25, .x26, .x28, .x29, .x30,
      .x31] : List Reg))
      (h2 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x12, .x13, .x14, .x15, .x16, .x17, .x18,
        .x19, .x21, .x22, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg)) :
      u₂.getReg r = u.getReg r := by rw [k₂ r h2, hp₁ r hr, k₁ r h1]
  have fw (x : Word) (h1 : (s.getReg .x2 - 2656).toNat ≤ x.toNat)
      (h2 : x.toNat + 8 ≤ (s.getReg .x2 - 104).toNat) (h3 : Apart x 8 (s.getReg .x2 - 512) 24) :
      u₂.getMem x = u.getMem x := by
    rw [m₂, growFrameWord hpre hv₁ phv V₁.count fr (fun _ h ↦ h) h1 h2 h3, m₁]
  refine ⟨u₂, hr₁.trans (hrt₁.trans hr₂), Or.inr ⟨b80002f84_pc h₂, vecPtr t₁ (s.getReg .x2 - 512),
    (vecCap t₁ (s.getReg .x2 - 512)).toNat, (vecLen u₁ (s.getReg .x2 - 512)).toNat, {
    base := B₂.same hpre m₂ (k₂ .x2 (by decide))
    op5 := by
      have hB := H.bufB
      have hl := H.loLe
      rw [m₂, growHeapWord hpre hv₁ B₁.loLe (by addr_omega [hb1]) hcf fr (fun _ h ↦ h)
        (by addr_omega [hB, hl, hci]), m₁]
      exact h.op5
    vecs := VC.keepFrame hpre phv hn₂.ge (Layout.DFrame.of_same m₂ (fun _ ↦ False)) fun _ h ↦ h.elim
    lt := hi
    jlt := Nat.zero_le _
    room := by
      have : (BitVec.ofNat 64 (nCols i)).toNat = nCols i := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := nCols_le hi; omega)
      omega
    hdr := by
      refine ⟨?_, ?_, ?_⟩
      · rw [m₂, ofNat_toNat']; rfl
      · rw [m₂, vecPtr, e8]
      · rw [m₂, ofNat_toNat', ← plen, vecLen, e16]
    x9 := by
      rw [k₂ .x9 (by decide), hp₁ .x9 (by decide), b80002f5c_x9 h₁, h.x9]
      have : (1 : Word).toNat = 1 := rfl
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, this]; omega
    x18 := by rw [kr .x18 (by decide) (by decide) (by decide)]; exact h.x18
    x19 := by rw [kr .x19 (by decide) (by decide) (by decide)]; exact h.x19
    x21 := by rw [kr .x21 (by decide) (by decide) (by decide)]; exact h.x21
    x22 := by rw [kr .x22 (by decide) (by decide) (by decide)]; exact h.x22
    x20 := by
      rw [b80002f84_x20 h₂, x20₁, e8, e16, mul48, Nat.add_zero, ← plen, vecPtr, vecLen, e8, e16]
    x23 := by rw [b80002f84_x23 h₂, x20₁, e16, Nat.add_zero, ← plen, ofNat_toNat', vecLen, e16]
    x24 := by
      rw [k₂ .x24 (by decide), hp₁ .x24 (by decide), b80002f5c_x24 h₁, h.x21, h.x10, r8, Nat.sub_zero]
    x27 := by
      rw [k₂ .x27 (by decide), hp₁ .x27 (by decide), b80002f5c_x27 h₁, h.x21, h.x10, r0]
      simp
    n := by
      rw [fw _ (by addr_omega [hb1]) (by addr_omega [hb1]) (by simp only [Apart]; addr_omega [hb1])]
      exact h.n
    hgt := by
      rw [fw _ (by addr_omega [hb1]) (by addr_omega [hb1]) (by simp only [Apart]; addr_omega [hb1])]
      exact h.hgt
    row := by
      rw [fw _ (by addr_omega [hb1]) (by addr_omega [hb1]) (by simp only [Apart]; addr_omega [hb1])]
      exact h.row }⟩⟩

end Rv64Verifier.Proofs.Walk
