import Rv64Verifier.Proofs.Walk.Count10

/-!
# `walk`: the count loop's body (R10)

`VecsC.keepAbove`: writes at or above `NEXT` (fresh heap, `NEXT`, the stack) apart from `push`'s and
`pull`'s headers keep `VecsC`. `VecsC.store`: the block stored at the end of `count`'s blocks,
its coordinates a `Vec<Form>` whose footprint was allocated after everything `VecsC` reaches.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror
  Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

section
variable {s c t : MachineState} {lo : Nat} {P1 P2 P3 : List BusBlockRust} {p : Word} {cc n : Nat}

/-- Everything `VecsC` reaches is below `NEXT`. -/
theorem VecsC.below (V : VecsC s c lo P1 P2 P3 p cc n) {x : Word}
    (hx : blocksFoot c (s.getReg .x2 - 416) x ∨ blocksFoot c (s.getReg .x2 - 224) x ∨
      cFoot c p cc n x) : x.toNat < heapNext c := by
  rcases hx with hx | hx | hx | hx
  · exact (V.push.foot_below hx).2
  · exact (V.pull.foot_below hx).2
  · have hb := BlocksSound.bounds V.count
    simp only [Within] at hx
    rcases hb.2 with h0 | h0
    · rw [h0] at hx; omega
    · omega
  · exact (BlocksSound.deep_below V.count hx).2

theorem VecsC.keepAbove (hpre : WalkPre s) (V : VecsC s c lo P1 P2 P3 p cc n) (hc : HeapOk c)
    (mono : heapNext c ≤ heapNext t) {w : Word → Prop} (fr : Layout.DFrame c t w)
    (hw : ∀ x, w x → heapNext c ≤ x.toNat ∧ ¬ Within x (s.getReg .x2 - 416) 24 ∧
      ¬ Within x (s.getReg .x2 - 224) 24) :
    VecsC s t lo P1 P2 P3 p cc n ∧ ∀ x, (blocksFoot t (s.getReg .x2 - 416) x ∨
      blocksFoot t (s.getReg .x2 - 224) x ∨ cFoot t p cc n x) → x.toNat < heapNext c := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have K (a : Word) (hok : BlocksOk c a) (ha2 : a.toNat + 24 ≤ (s.getReg .x2 - 104).toNat)
      (hh : ∀ x, w x → ¬ Within x a 24) (hb : ∀ x, blocksFoot c a x → x.toNat < heapNext c) :=
    vecKeep fr hok (by addr_omega [ha2, hb1, hb2]) (fun x hx hwx ↦ hh x hwx hx)
      (fun x hx hwx ↦ absurd (hw x hwx).1 (by have := hb x hx; omega)) hc mono
  have kp := K _ V.push (by addr_omega [hb1]) (fun x hx ↦ (hw x hx).2.1)
    fun x hx ↦ V.below (Or.inl hx)
  have kl := K _ V.pull (by addr_omega [hb1]) (fun x hx ↦ (hw x hx).2.2)
    fun x hx ↦ V.below (Or.inr (Or.inl hx))
  have hle := V.count.le
  have kc := blocksAt_frame fr V.count
    (fun x hx hwx ↦ absurd (hw x hwx).1 (by
      have := V.below (x := x) (Or.inr (Or.inr (Or.inl (by simp only [Within] at hx ⊢; omega))))
      omega))
    (fun x hx hwx ↦ absurd (hw x hwx).1 (by
      have := V.below (x := x) (Or.inr (Or.inr (Or.inr hx))); omega)) hc mono
  have hcf : cFoot t p cc n = cFoot c p cc n := by
    funext x; simp only [cFoot, kc.2.2]
  refine ⟨⟨kp.1, kl.1, by rw [kp.2.1]; exact V.pushV, by rw [kl.2.1]; exact V.pullV, kc.2.1,
    by rw [kc.1]; exact V.countV, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [kp.2.2, kl.2.2, hcf]
  · exact V.fresh
  · exact V.d1
  · exact V.d2
  · exact V.d3
  · exact fun x hx ↦ V.below hx

theorem blocksAt_succ (u : MachineState) (p : Word) (n : Nat) :
    blocksAt u p (n + 1) = blocksAt u p n ++ [blockOf u (p + BitVec.ofNat 64 (48 * n))] := by
  simp only [blocksAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem blocksDeep_succ {u : MachineState} {p : Word} {n : Nat} {x : Word} :
    blocksDeep u p (n + 1) x ↔
      blocksDeep u p n x ∨ formVecDeep u (p + BitVec.ofNat 64 (48 * n)) x := by
  simp only [blocksDeep]
  constructor
  · rintro ⟨j, hj, hx⟩
    by_cases h : j < n
    · exact Or.inl ⟨j, h, hx⟩
    · have : j = n := by omega
      subst this; exact Or.inr hx
  · rintro (⟨j, hj, hx⟩ | hx)
    · exact ⟨j, by omega, hx⟩
    · exact ⟨n, by omega, hx⟩

/-- The block stored at `count`'s end, its coordinates' header copied from `sp + 1728`. -/
theorem VecsC.store (hpre : WalkPre s) (V : VecsC s c lo P1 P2 P3 p cc n) (hc : HeapOk c)
    (hn : n < cc) {N0 : Nat} (hlo : lo ≤ N0)
    (hb : ∀ x, (blocksFoot c (s.getReg .x2 - 416) x ∨ blocksFoot c (s.getReg .x2 - 224) x ∨
      cFoot c p cc n x) → x.toNat < N0)
    (hok : FormVecOk c (s.getReg .x2 - 928))
    (hd : ∀ x, formVecDeep c (s.getReg .x2 - 928) x → N0 ≤ x.toNat)
    (fr : MemFrame c t (p + BitVec.ofNat 64 (48 * n)) 48)
    (w0 : t.getMem (p + BitVec.ofNat 64 (48 * n)) = c.getMem (s.getReg .x2 - 928))
    (w8 : t.getMem (p + BitVec.ofNat 64 (48 * n) + 8) = c.getMem (s.getReg .x2 - 928 + 8))
    (w16 : t.getMem (p + BitVec.ofNat 64 (48 * n) + 16) = c.getMem (s.getReg .x2 - 928 + 16)) :
    VecsC s t lo P1 P2 (P3 ++ [blockOf t (p + BitVec.ofNat 64 (48 * n))]) p cc (n + 1) ∧
      formVecOf t (p + BitVec.ofNat 64 (48 * n)) = formVecOf c (s.getReg .x2 - 928) := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hbd := BlocksSound.bounds V.count
  have hle := V.count.le
  have hci := hc.hi
  simp only [heapEnd, heapStart] at hci hbd
  have hP : p.toNat + 48 * cc ≤ heapNext c := by rcases hbd.2 with h0 | h0 <;> omega
  have hP0 : 0x20000000 ≤ p.toNat := by rcases hbd.2 with h0 | h0 <;> omega
  have hslot : ∀ x, Within x (p + BitVec.ofNat 64 (48 * n)) 48 → Within x p (48 * cc) :=
    fun x hx ↦ by simp only [Within] at hx ⊢; addr_omega [hx, hP, hP0, hn, hci]
  have dfr := MemFrame.dframe fr
  have hn' : heapNext t = heapNext c := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr _ (by simp only [Within, nextAddr]; addr_omega [hP, hP0, hn, hci]))
  have K (a : Word) (hok : BlocksOk c a) (ha1 : (s.getReg .x2 - 2080).toNat ≤ a.toNat)
      (ha2 : a.toNat + 24 ≤ (s.getReg .x2 - 104).toNat)
      (hf : ∀ x, blocksFoot c a x → ¬ cFoot c p cc n x) :=
    vecKeep dfr hok (by addr_omega [ha2, hb1, hb2])
      (fun x hx hwx ↦ by simp only [Within] at hx hwx; addr_omega [hx, hwx, ha1, hP, hP0, hn, hci, hb1])
      (fun x hx hwx ↦ hf x hx (Or.inl (hslot x hwx))) hc hn'.ge
  have kp := K _ V.push (by addr_omega [hb1]) (by addr_omega [hb1]) V.d2
  have kl := K _ V.pull (by addr_omega [hb1]) (by addr_omega [hb1]) V.d3
  have kc := blocksAt_frame dfr V.count
    (fun x hx hwx ↦ by simp only [Within] at hx hwx; addr_omega [hx, hwx, hP, hP0, hn, hci])
    (fun x hx hwx ↦ V.count.sep x hx (hslot x hwx)) hc hn'.ge
  have hS928 : (s.getReg .x2 - 928).toNat + 24 ≤ 2 ^ 64 := by addr_omega [hb1]
  have mv := formVecOf_moved dfr (e := s.getReg .x2 - 928) (e' := p + BitVec.ofNat 64 (48 * n))
    w0 w8 w16 hok (fun x hx hwx ↦ by
      have h1 := hd x hx
      have h2 := hb x (Or.inr (Or.inr (Or.inl (hslot x hwx))))
      omega) hc hn'.ge
  have hdeep : ∀ x, blocksDeep t p (n + 1) x ↔
      blocksDeep c p n x ∨ formVecDeep c (s.getReg .x2 - 928) x := fun x ↦ by
    rw [blocksDeep_succ, kc.2.2, mv.2.2]
  have hcf : ∀ x, cFoot t p cc (n + 1) x ↔ cFoot c p cc n x ∨ formVecDeep c (s.getReg .x2 - 928) x :=
    fun x ↦ by simp only [cFoot, hdeep x, or_assoc]
  refine ⟨⟨kp.1, kl.1, by rw [kp.2.1]; exact V.pushV, by rw [kl.2.1]; exact V.pullV,
    ⟨kc.2.1.buf, by omega, fun j hj ↦ ?_, fun x hx hw ↦ ?_⟩, ?_, fun x hx ↦ ?_,
    fun x hx hy ↦ ?_, fun x hx hy ↦ ?_, fun x hx hy ↦ ?_⟩, mv.1⟩
  · by_cases h : j < n
    · exact kc.2.1.elems j h
    · have : j = n := by omega
      subst this; exact mv.2.1
  · rcases (hdeep x).mp hx with h | h
    · exact V.count.sep x h hw
    · have h1 := hd x h
      have h2 := hb x (Or.inr (Or.inr (Or.inl hw)))
      omega
  · rw [blocksAt_succ, kc.1, V.countV]
  · simp only [kp.2.2, kl.2.2] at hx
    rcases hx with hx | hx | hx
    · exact V.fresh x (Or.inl hx)
    · exact V.fresh x (Or.inr (Or.inl hx))
    · rcases (hcf x).mp hx with h | h
      · exact V.fresh x (Or.inr (Or.inr h))
      · exact le_trans hlo (hd x h)
  · rw [kp.2.2] at hx; rw [kl.2.2] at hy; exact V.d1 x hx hy
  · rw [kp.2.2] at hx
    rcases (hcf x).mp hy with h | h
    · exact V.d2 x hx h
    · have h1 := hd x h; have h2 := hb x (Or.inl hx); omega
  · rw [kl.2.2] at hx
    rcases (hcf x).mp hy with h | h
    · exact V.d3 x hx h
    · have h1 := hd x h; have h2 := hb x (Or.inr (Or.inl hx)); omega

end

theorem colPtr_bounds {i j : Nat} (hi : i < 6) (hj : j < 27) :
    (colPtr i + BitVec.ofNat 64 (8 * j)).toNat = (colPtr i).toNat + 8 * j ∧
      0xa0000218 ≤ (colPtr i).toNat ∧ (colPtr i).toNat ≤ 0xa0000328 ∧ (colPtr i).toNat % 8 = 0 := by
  have : (colPtr i).toNat = 0xa0000218 ∨ (colPtr i).toNat = 0xa0000308 ∨
      (colPtr i).toNat = 0xa0000258 ∨ (colPtr i).toNat = 0xa0000328 := by
    interval_cases i <;> decide
  refine ⟨?_, by omega, by omega, by omega⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega


/-- At `0x80002fe8`: the column's `Vec<Form>` at `sp + 1728`, reaching only memory from `N0` on,
everything `VecsC` reaches below `N0`. -/
structure AtFe8 (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo i : Nat)
    (P : List BusBlockRust × List BusBlockRust × List BusBlockRust) (p : Word) (c L0 j N0 : Nat) :
    Prop where
  base : Base10 OI s u A k R Q B lo
  op5 : u.getMem (B + 472) = 5
  vecs : VecsC s u lo P.1 P.2.1 (P.2.2 ++ countPre A i j) p c (L0 + j)
  below : ∀ x, (blocksFoot u (s.getReg .x2 - 416) x ∨ blocksFoot u (s.getReg .x2 - 224) x ∨
    cFoot u p c (L0 + j) x) → x.toNat < N0
  nok : FormVecOk u (s.getReg .x2 - 928)
  deep : ∀ x, formVecDeep u (s.getReg .x2 - 928) x → N0 ≤ x.toNat
  lo : lo ≤ N0
  coords : formVecOf u (s.getReg .x2 - 928) = [colRust ((countColumnsRust.getD i []).getD j 0) 0]
  lt : i < 6
  jlt : j < nCols i
  room : L0 + nCols i ≤ c
  hdr : u.getMem (s.getReg .x2 - 512) = BitVec.ofNat 64 c ∧ u.getMem (s.getReg .x2 - 504) = p ∧
    u.getMem (s.getReg .x2 - 496) = BitVec.ofNat 64 L0
  x8 : u.getReg .x8 = (rowsOf A).getD i 0
  x26 : u.getReg .x26 = BitVec.ofNat 64 ((tableLogHeightsRust (rowsOf A)).getD i 0)
  x9 : u.getReg .x9 = BitVec.ofNat 64 (i + 1)
  x18 : u.getReg .x18 = s.getReg .x2 - 1488
  x19 : u.getReg .x19 = s.getReg .x2 - 1344
  x21 : u.getReg .x21 = 0xa0000400
  x20 : u.getReg .x20 = p + BitVec.ofNat 64 (48 * (L0 + j))
  x22 : u.getReg .x22 = B + BitVec.ofNat 64 (80 * i)
  x23 : u.getReg .x23 = BitVec.ofNat 64 (L0 + j)
  x24 : u.getReg .x24 = BitVec.ofNat 64 (nCols i - j)
  x27 : u.getReg .x27 = colPtr i + BitVec.ofNat 64 (8 * j)
  n : u.getMem (s.getReg .x2 - 2472) = 6
  hgt : u.getMem (s.getReg .x2 - 1488) = BitVec.ofNat 64 ((tableLogHeightsRust (rowsOf A)).getD i 0)
  row : u.getMem (s.getReg .x2 - 1344) = (rowsOf A).getD i 0

set_option maxRecDepth 8192 in
/-- One count column's `alloc(8, 24)`, `col(local, 0)` into it, and `clone` of the one-form slice
to `sp + 1728`. -/
theorem countA (hAS : AllocSpec) (hCol : ColSpec) (hCl : CloneSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo i : Nat}
    {P : List BusBlockRust × List BusBlockRust × List BusBlockRust} {p : Word} {c L0 j : Nat}
    (hpre : WalkPre s) (hpc : u.pc = 0x80002f9c) (h : CountAt OI s u A k R Q B lo i P p c L0 j)
    (hj : j < nCols i) :
    ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨
      (t.pc = 0x80002fe8 ∧ ∃ N0, AtFe8 OI s t A k R Q B lo i P p c L0 j N0)) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have H := h.base
  have V := h.vecs
  have hi := h.lt
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := H.inv.sp
  have ro := H.inv.rodata hpre
  have rj := (countRod ro hi).2.2 j hj
  have hj27 : j < 27 := lt_of_lt_of_le hj (nCols_le hi)
  obtain ⟨cp1, cp2, cp3, cp4⟩ := colPtr_bounds hi hj27
  have hl := H.loLe
  have hhu := H.inv.heap.hi
  have hs0 := hpre.heap.lo
  simp only [heapEnd, heapStart] at hhu hs0
  -- `alloc(8, 24)`
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80002f9c_spec hpc (by
    rv_eval [h.x27]
    simp only [Sym.validAccess_eight]
    addr_omega [cp1, cp2, cp3, cp4, hj27])
  have m₁ := b80002f9c_mem_same h₁
  have k₁ := b80002f9c_keeps h₁
  have hn₁ : heapNext u₁ = heapNext u := by simp only [heapNext, m₁]
  have x26₁ : u₁.getReg .x26 = BitVec.ofNat 64 ((countColumnsRust.getD i []).getD j 0) := by
    rw [b80002f9c_x26 h₁, h.x27]; exact rj
  have preA : AllocPre u₁ := ⟨⟨hn₁ ▸ H.inv.heap.lo, hn₁ ▸ H.inv.heap.hi⟩, by
    rw [b80002f9c_x10 h₁]; decide⟩
  obtain ⟨t₁, hrt₁, ⟨hpct₁, hp₁, postA⟩ | hd⟩ := hAS.call (Reaches.refl u₁) (b80002f9c_pc h₁) preA
  swap
  · exact ⟨t₁, hr₁.trans hrt₁, Or.inl hd⟩
  have hal := postA.aligned
  have hab := postA.above
  have hnx := postA.next
  rw [b80002f9c_x10 h₁] at hal
  rw [b80002f9c_x11 h₁] at hnx
  have e8 : (8 : Word).toNat = 8 := rfl
  have e24 : (24 : Word).toNat = 24 := rfl
  rw [e8] at hal
  rw [e24] at hnx
  rw [hn₁] at hab
  set F := t₁.getReg .x10 with hF
  have hht₁ := postA.heap.hi
  simp only [heapEnd] at hht₁
  have hlo0 := H.inv.heap.lo
  simp only [heapStart] at hlo0
  have hF8 : F.toNat % 8 = 0 := hal
  have hFlo : heapNext u ≤ F.toNat := hab
  have hFhi : F.toNat + 24 ≤ 2013265920 := by rw [← hnx]; exact hht₁
  have m₁₂ (a : Word) (ha : a ≠ nextAddr) : t₁.getMem a = u.getMem a := by rw [postA.mem a ha, m₁]
  have frA : Layout.DFrame u t₁ (Within · nextAddr 8) := fun a ha _ ↦
    m₁₂ a fun he ↦ ha a ⟨le_refl _, by omega⟩ (by rw [he]; simp only [Within]; omega)
  have hnA : heapNext u ≤ heapNext t₁ := by rw [hnx]; omega
  have B₁ : Base10 OI s t₁ A k R Q B lo := H.keep hpre frA
    (fun x hx ↦ Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hx))))) postA.heap hnA
    (by rw [hp₁ .x2 (by decide), k₁ .x2 (by decide)])
  -- `col(local, 0)` into the new 24 bytes
  have pc₂ : t₁.pc = 0x80002fb0 := by rw [hpct₁, returnAddress_eq, b80002f9c_x1 h₁]; decide
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80002fb0_spec pc₂ (by rv_eval [])
  have pc₂' := b80002fb0_pc_taken h₂ (fun he ↦ by
    have := congrArg BitVec.toNat he; rw [← hF] at this; have h0 : (0 : Word).toNat = 0 := rfl
    omega)
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80002fb8_spec pc₂' (by rv_eval [])
  have m₃ (a : Word) : u₃.getMem a = t₁.getMem a := by
    rw [b80002fb8_mem_same h₃, b80002fb0_mem_same h₂]
  have k₃ (r : Reg) (h1 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x13, .x14, .x15, .x16,
      .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x26, .x27, .x28, .x29, .x30, .x31] : List Reg)) :
      u₃.getReg r = t₁.getReg r := by
    rw [b80002fb8_keeps h₃ r h1, b80002fb0_keeps h₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 ⊢
      rcases h1 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h | h | h | h | h <;> simp [h])]
  have hn₃ : heapNext u₃ = heapNext t₁ := by simp only [heapNext, m₃]
  have hv₃ : HeapOk u₃ := ⟨hn₃ ▸ postA.heap.lo, hn₃ ▸ postA.heap.hi⟩
  have B₃ := B₁.same hpre m₃ (k₃ .x2 (by decide))
  have x10₃ : u₃.getReg .x10 = F := by rw [k₃ .x10 (by decide)]
  have hab3 := hpre.stack.above
  have hx3 := hpre.stack.next
  rw [stackLo_eq] at hab3 hx3
  rw [stack_eq] at hx3
  simp only [heapEnd] at hab3
  have preC : ColPre u₃ := {
    heap := hv₃
    stack := stk10 hpre B₃.inv (by decide) (by decide)
    out := by rw [x10₃]; exact validMemRange_of hF8 (Or.inl ⟨by omega, by omega⟩)
    outFree := by
      rw [x10₃]; exact ⟨Or.inl (by rw [hn₃, hnx]), by simp only [Apart, nextAddr]; addr_omega [hFhi, hFlo, hlo0]⟩
    outStack := by rw [x10₃, stackLo_callee B₃.inv]; simp only [Apart]; addr_omega [hFhi, hb1]
    rodata := B₃.inv.rodata hpre }
  obtain ⟨t₃, hrt₃, ⟨hpct₃, hp₃, nf, fv⟩ | hd⟩ := hCol u₃ (b80002fb8_pc h₃) preC
  swap
  · exact ⟨t₃, hr₁.trans (hrt₁.trans (hr₂.trans (hr₃.trans hrt₃))), Or.inl hd⟩
  rw [x10₃, b80002fb8_x11 h₃, b80002fb8_x12 h₃] at fv
  have hm₃ := nf.mono
  have nff := nf.frame
  rw [x10₃] at nff
  have hht₃ := nf.heap.hi
  simp only [heapEnd] at hht₃
  have stkIn (c' : MachineState) (hc' : c'.getReg .x2 = s.getReg .x2 - 2656) (n : Nat) (hn : n ≤ 8736)
      (x : Word) (hx : Within x (stackLo c' n) n) : Within x (s.getReg .x2 - 11392) 8736 := by
    simp only [stackLo, hc', Within] at hx ⊢; addr_omega [hx, hb1, hn]
  have sp₃ : u₃.getReg .x2 = s.getReg .x2 - 2656 := B₃.inv.sp
  have B₄ : Base10 OI s t₃ A k R Q B lo := B₃.keep hpre nff (fun x hx ↦ by
      rcases hx with hx | hx | hx | hx
      · simp only [Within] at hx
        exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))
      · exact Or.inl (Or.inr (Or.inr (Or.inl (stkIn u₃ sp₃ _ (by decide) x hx))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hx))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨by have := hx.1; omega, hx.2⟩))))) nf.heap hm₃
    (hp₃ .x2 (by decide))
  have frAC : Layout.DFrame u t₃ fun x ↦ Within x nextAddr 8 ∨ (False ∨ (Within x F 24 ∨
      Within x (stackLo u₃ colStack) colStack ∨ Within x nextAddr 8 ∨ Fresh u₃ t₃ x)) :=
    frA.union ((Layout.DFrame.of_same m₃ (fun _ ↦ False)).union nff)
  have aboveW (x : Word) (hx : Within x nextAddr 8 ∨ Within x (s.getReg .x2 - 11392) 8736) :
      heapNext u ≤ x.toNat ∧ ¬ Within x (s.getReg .x2 - 416) 24 ∧ ¬ Within x (s.getReg .x2 - 224) 24 := by
    simp only [Within, nextAddr] at hx ⊢
    rcases hx with hx | hx <;> refine ⟨by addr_omega [hx, hhu, hb1], by addr_omega [hx, hb1],
      by addr_omega [hx, hb1]⟩
  obtain ⟨V₃, -⟩ :=
    V.keepAbove hpre H.inv.heap (by omega) frAC fun x hx ↦ by
      rcases hx with hx | (hx | hx | hx | hx | hx)
      · exact aboveW x (Or.inl hx)
      · exact hx.elim
      · simp only [Within] at hx ⊢; exact ⟨by omega, by addr_omega [hx, hFhi, hb1],
          by addr_omega [hx, hFhi, hb1]⟩
      · exact aboveW x (Or.inr (stkIn u₃ sp₃ _ (by decide) x hx))
      · exact aboveW x (Or.inl hx)
      · simp only [Within, Fresh] at hx ⊢; exact ⟨by omega, by addr_omega [hx, hht₃, hb1],
          by addr_omega [hx, hht₃, hb1]⟩
  -- `clone` of the one-form slice into `sp + 1728`
  have kR (r : Reg) (hr : r ∈ calleeSaved) (h1 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10,
      .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x26, .x27, .x28, .x29,
      .x30, .x31] : List Reg)) (h2 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x12, .x13, .x14,
      .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x27, .x28, .x29, .x30,
      .x31] : List Reg)) :
      t₃.getReg r = u.getReg r := by
    rw [hp₃ r hr, k₃ r h1, hp₁ r hr, k₁ r h2]
  have sp₄ : t₃.getReg .x2 = s.getReg .x2 - 2656 := by
    rw [kR .x2 (by decide) (by decide) (by decide)]; exact sp
  have pc₄ : t₃.pc = 0x80002fcc := by rw [hpct₃, returnAddress_eq, b80002fb8_x1 h₃]; decide
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80002fcc_spec pc₄ (by
    rv_eval [sp₄]
    simp only [Sym.validAccess_eight]
    and_intros <;> addr_omega [hb1, hb2, hb3])
  have m₄ := b80002fcc_mem_same h₄
  have k₄ := b80002fcc_keeps h₄
  have hn₄ : heapNext u₄ = heapNext t₃ := by simp only [heapNext, m₄]
  have hv₄ : HeapOk u₄ := ⟨hn₄ ▸ nf.heap.lo, hn₄ ▸ nf.heap.hi⟩
  have B₅ := B₄.same hpre m₄ (k₄ .x2 (by decide))
  have e1728 : t₃.getReg .x2 + 1728 = s.getReg .x2 - 928 := by
    rw [sp₄]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x10₄ : u₄.getReg .x10 = s.getReg .x2 - 928 := by rw [b80002fcc_x10 h₄, e1728]
  have x11₄ : u₄.getReg .x11 = F := by
    rw [b80002fcc_x11 h₄, hp₃ .x25 (by decide), b80002fb8_x25 h₃, b80002fb0_keeps h₂ .x10 (by decide)]
  have nok := nf.ok
  rw [x10₃] at nok
  have fo4 := formOf_frame (Layout.DFrame.of_same m₄ (fun _ ↦ False)) nok (fun _ _ h ↦ h)
    (fun _ _ h ↦ h) (by omega) nf.heap hn₄.ge
  have preL : ClonePre u₄ := {
    heap := hv₄
    stack := stk10 hpre B₅.inv (by decide) (by decide)
    out := by
      rw [x10₄]; exact validMemRange_of (by addr_omega [hb1, hb3]) (Or.inr ⟨by addr_omega [hb1],
        by addr_omega [hb1, hb2]⟩)
    src := by rw [x11₄, b80002fcc_x12 h₄]; exact validMemRange_of hF8 (Or.inl ⟨by omega, by simp; omega⟩)
    srcOk := by
      rw [x11₄, b80002fcc_x12 h₄]; intro i' hi'
      have : i' = 0 := by simp at hi'; omega
      subst this; simpa using fo4.2
    outFree := by
      rw [x10₄]; exact ⟨Or.inr (by addr_omega [hab3, hb1]), by simp only [Apart]; addr_omega [hx3, hb1]⟩
    srcFree := by
      rw [x11₄, b80002fcc_x12 h₄]
      exact ⟨Or.inl (by simp only [hn₄]; have := hm₃; simp; omega), by
        simp only [Apart, nextAddr]; simp; addr_omega [hFhi, hFlo, hlo0]⟩
    outStack := by rw [x10₄, stackLo_callee B₅.inv]; simp only [Apart]; addr_omega [hb1]
    srcStack := by
      rw [x11₄, b80002fcc_x12 h₄, stackLo_callee B₅.inv]; simp only [Apart]; simp
      addr_omega [hFhi, hb1] }
  obtain ⟨t₄, hrt₄, ⟨hpct₄, hp₄, nfv, fvv⟩ | hd⟩ := hCl u₄ (b80002fcc_pc h₄) preL
  swap
  · exact ⟨t₄, hr₁.trans (hrt₁.trans (hr₂.trans (hr₃.trans (hrt₃.trans (hr₄.trans hrt₄))))),
      Or.inl hd⟩
  rw [x10₄, x11₄, b80002fcc_x12 h₄] at fvv
  -- the block stored at `count`'s end
  have nfvf := nfv.frame
  rw [x10₄] at nfvf
  have hm₄ := nfv.mono
  have hht₄ := nfv.heap.hi
  simp only [heapEnd] at hht₄
  have sp₅ : u₄.getReg .x2 = s.getReg .x2 - 2656 := B₅.inv.sp
  have B₆ : Base10 OI s t₄ A k R Q B lo := B₅.keep hpre nfvf (fun x hx ↦ by
      rcases hx with hx | hx | hx | hx
      · exact Or.inl (Or.inl ⟨by simp only [Within] at hx; addr_omega [hx, hb1],
          by simp only [Within] at hx; addr_omega [hx, hb1]⟩)
      · exact Or.inl (Or.inr (Or.inr (Or.inl (stkIn u₄ sp₅ _ (by decide) x hx))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hx))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨by have := hx.1; omega, hx.2⟩))))) nfv.heap hm₄
    (hp₄ .x2 (by decide))
  have hn34 : heapNext u ≤ heapNext u₄ := by rw [hn₄]; omega
  have hhu4 := hv₄.hi
  simp only [heapEnd] at hhu4
  obtain ⟨V₄, Vb⟩ := (V₃.keepFrame hpre nf.heap hn₄.ge (Layout.DFrame.of_same m₄ (fun _ ↦ False))
    fun _ h ↦ h.elim).keepAbove hpre hv₄ hm₄ nfvf fun x hx ↦ by
      rcases hx with hx | hx | hx | hx
      · simp only [Within] at hx ⊢
        exact ⟨by addr_omega [hx, hb1, hhu4], by addr_omega [hx, hb1], by addr_omega [hx, hb1]⟩
      · rw [stackLo_callee B₅.inv] at hx
        simp only [Within] at hx ⊢
        exact ⟨by addr_omega [hx, hb1, hhu4], by addr_omega [hx, hb1], by addr_omega [hx, hb1]⟩
      · simp only [Within, nextAddr] at hx ⊢
        exact ⟨by addr_omega [hx, hhu4], by addr_omega [hx, hb1], by addr_omega [hx, hb1]⟩
      · simp only [Within, Fresh] at hx ⊢
        exact ⟨hx.1, by addr_omega [hx, hht₄, hb1], by addr_omega [hx, hht₄, hb1]⟩
  -- registers and frame words back at `t₄`
  have kR4 (r : Reg) (hr : r ∈ calleeSaved) (h0 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x9, .x13, .x14,
      .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x27, .x28, .x29, .x30,
      .x31] : List Reg)) (h1 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10,
      .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x26, .x27, .x28, .x29,
      .x30, .x31] : List Reg)) (h2 : r ∈ ([.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x12, .x13, .x14,
      .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x27, .x28, .x29, .x30,
      .x31] : List Reg)) : t₄.getReg r = u.getReg r := by
    rw [hp₄ r hr, k₄ r h0, kR r hr h1 h2]
  have sp₆ : t₄.getReg .x2 = s.getReg .x2 - 2656 := by
    rw [kR4 .x2 (by decide) (by decide) (by decide) (by decide)]; exact sp
  -- frame words apart from the iterator's slot, and heap words below `lo`, are as at `u`
  have fw3 (x : Word) (h1 : (s.getReg .x2 - 2656).toNat ≤ x.toNat)
      (h2 : x.toNat + 8 ≤ (s.getReg .x2 - 104).toNat) : t₃.getMem x = u.getMem x :=
    frAC x (fun y hy hw ↦ by
      simp only [Within] at hy
      rcases hw with hw | (hw | hw | hw | hw | hw)
      · simp only [Within, nextAddr] at hw; addr_omega [hy, hw, h1, hb1]
      · exact hw
      · simp only [Within] at hw; addr_omega [hy, hw, hFhi, h1, hb1]
      · rw [stackLo_callee B₃.inv] at hw; simp only [Within] at hw; addr_omega [hy, hw, h1, hb1]
      · simp only [Within, nextAddr] at hw; addr_omega [hy, hw, h1, hb1]
      · simp only [Fresh] at hw; addr_omega [hy, hw, hht₃, h1, hb1]) (by addr_omega [h2, hb1])
  have fwU (x : Word) (h1 : (s.getReg .x2 - 2656).toNat ≤ x.toNat)
      (h2 : x.toNat + 8 ≤ (s.getReg .x2 - 104).toNat) (h3 : Apart x 8 (s.getReg .x2 - 928) 24) :
      t₄.getMem x = u.getMem x := by
    have a1 : t₄.getMem x = u₄.getMem x := nfvf x (fun y hy hw ↦ by
      simp only [Within] at hy
      rcases hw with hw | hw | hw | hw
      · simp only [Within, Apart] at hw h3; addr_omega [hy, hw, h3]
      · rw [stackLo_callee B₅.inv] at hw; simp only [Within] at hw; addr_omega [hy, hw, h1, hb1]
      · simp only [Within, nextAddr] at hw; addr_omega [hy, hw, h1, hb1]
      · simp only [Fresh] at hw; addr_omega [hy, hw, hht₄, h1, hb1]) (by addr_omega [h2, hb1])
    rw [a1, m₄, fw3 x h1 h2]
  have hK (x : Word) (h1 : 0x20000000 ≤ x.toNat) (h2 : x.toNat + 8 ≤ lo) :
      t₄.getMem x = u.getMem x := by
    have a1 : t₄.getMem x = u₄.getMem x := nfvf x (fun y hy hw ↦ by
      simp only [Within] at hy
      rcases hw with hw | hw | hw | hw
      · simp only [Within] at hw; addr_omega [hy, hw, h2, hl, hhu, hb1]
      · rw [stackLo_callee B₅.inv] at hw; simp only [Within] at hw; addr_omega [hy, hw, h2, hl, hhu, hb1]
      · simp only [Within, nextAddr] at hw; addr_omega [hy, hw, h2, hl, hhu]
      · simp only [Fresh] at hw; omega) (by addr_omega [h2, hl, hhu])
    have a2 : t₃.getMem x = u.getMem x := frAC x (fun y hy hw ↦ by
      simp only [Within] at hy
      rcases hw with hw | (hw | hw | hw | hw | hw)
      · simp only [Within, nextAddr] at hw; addr_omega [hy, hw, h2, hl, hhu]
      · exact hw
      · simp only [Within] at hw; omega
      · rw [stackLo_callee B₃.inv] at hw; simp only [Within] at hw; addr_omega [hy, hw, h2, hl, hhu, hb1]
      · simp only [Within, nextAddr] at hw; addr_omega [hy, hw, h2, hl, hhu]
      · simp only [Fresh] at hw; omega) (by addr_omega [h2, hl, hhu])
    rw [a1, m₄, a2]
  have x20₆ : t₄.getReg .x20 = p + BitVec.ofNat 64 (48 * (L0 + j)) := by
    rw [kR4 .x20 (by decide) (by decide) (by decide) (by decide)]; exact h.x20
  have x22₆ : t₄.getReg .x22 = B + BitVec.ofNat 64 (80 * i) := by
    rw [kR4 .x22 (by decide) (by decide) (by decide) (by decide)]; exact h.x22
  have colLe : (countColumnsRust.getD i []).getD j 0 ≤ 91 :=
    getD_le (by interval_cases i <;> decide) j
  have e1312 : t₃.getReg .x2 + 1312 = s.getReg .x2 - 1344 := by
    rw [sp₄]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e1168 : t₃.getReg .x2 + 1168 = s.getReg .x2 - 1488 := by
    rw [sp₄]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x8₆ : t₄.getReg .x8 = (rowsOf A).getD i 0 := by
    rw [hp₄ .x8 (by decide), b80002fcc_x8 h₄, e1312,
      fw3 _ (by addr_omega [hb1]) (by addr_omega [hb1])]; exact h.row
  have x26₆ : t₄.getReg .x26 =
      BitVec.ofNat 64 ((tableLogHeightsRust (rowsOf A)).getD i 0) := by
    rw [hp₄ .x26 (by decide), b80002fcc_x26 h₄, e1168,
      fw3 _ (by addr_omega [hb1]) (by addr_omega [hb1])]; exact h.hgt
  have hBb := H.bufB
  have op5₄ : t₄.getMem (B + 472) = 5 := by
    rw [hK _ (by addr_omega [hBb, hs0, hl, hhu]) (by addr_omega [hBb, hl, hhu])]; exact h.op5
  have nok' := nfv.ok
  rw [x10₄] at nok'
  have nfr := nfv.fresh
  rw [x10₄] at nfr
  have hco : formVecOf t₄ (s.getReg .x2 - 928) =
      [colRust ((countColumnsRust.getD i []).getD j 0) 0] := by
    rw [fvv]
    have h1 : (1 : Word).toNat = 1 := rfl
    simp only [formsAt, h1, List.range_one, List.map_cons, List.map_nil]
    have f0 : F + BitVec.ofNat 64 (24 * 0) = F := by simp
    have h0 : (0 : Word).toNat = 0 := rfl
    rw [f0, fo4.1, fv, b80002fb0_keeps h₂ .x26 (by decide), hp₁ .x26 (by decide), x26₁, h0]
    simp only [BitVec.toNat_ofNat]
    congr 2
    exact Nat.mod_eq_of_lt (by omega)
  have pc₆ : t₄.pc = 0x80002fe8 := by rw [hpct₄, returnAddress_eq, b80002fcc_x1 h₄]; decide
  refine ⟨t₄, hr₁.trans (hrt₁.trans (hr₂.trans (hr₃.trans (hrt₃.trans (hr₄.trans hrt₄))))),
    Or.inr ⟨pc₆, heapNext u₄, {
    base := B₆
    op5 := op5₄
    vecs := V₄
    below := Vb
    nok := nok'
    deep := fun x hx ↦ (nfr x hx).1
    lo := by omega
    coords := hco
    lt := hi
    jlt := hj
    room := h.room
    hdr := by
      obtain ⟨a1, a2, a3⟩ := h.hdr
      refine ⟨?_, ?_, ?_⟩
      · rw [fwU _ (by addr_omega [hb1]) (by addr_omega [hb1]) (by simp only [Apart]; addr_omega [hb1])]
        exact a1
      · rw [fwU _ (by addr_omega [hb1]) (by addr_omega [hb1]) (by simp only [Apart]; addr_omega [hb1])]
        exact a2
      · rw [fwU _ (by addr_omega [hb1]) (by addr_omega [hb1]) (by simp only [Apart]; addr_omega [hb1])]
        exact a3
    x8 := x8₆
    x26 := x26₆
    x9 := by rw [kR4 .x9 (by decide) (by decide) (by decide) (by decide)]; exact h.x9
    x18 := by rw [kR4 .x18 (by decide) (by decide) (by decide) (by decide)]; exact h.x18
    x19 := by rw [kR4 .x19 (by decide) (by decide) (by decide) (by decide)]; exact h.x19
    x21 := by rw [kR4 .x21 (by decide) (by decide) (by decide) (by decide)]; exact h.x21
    x20 := x20₆
    x22 := x22₆
    x23 := by rw [kR4 .x23 (by decide) (by decide) (by decide) (by decide)]; exact h.x23
    x24 := by rw [kR4 .x24 (by decide) (by decide) (by decide) (by decide)]; exact h.x24
    x27 := by rw [kR4 .x27 (by decide) (by decide) (by decide) (by decide)]; exact h.x27
    n := by
      rw [fwU _ (by addr_omega [hb1]) (by addr_omega [hb1]) (by simp only [Apart]; addr_omega [hb1])]
      exact h.n
    hgt := by
      rw [fwU _ (by addr_omega [hb1]) (by addr_omega [hb1]) (by simp only [Apart]; addr_omega [hb1])]
      exact h.hgt
    row := by
      rw [fwU _ (by addr_omega [hb1]) (by addr_omega [hb1]) (by simp only [Apart]; addr_omega [hb1])]
      exact h.row }⟩⟩

set_option maxRecDepth 8192 in
/-- The block stored at `count`'s end, and the loop's branch. -/
theorem countB {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} {lo i : Nat}
    {P : List BusBlockRust × List BusBlockRust × List BusBlockRust} {p : Word} {c L0 j N0 : Nat}
    (hpre : WalkPre s) (hpc : u.pc = 0x80002fe8) (h : AtFe8 OI s u A k R Q B lo i P p c L0 j N0) :
    ∃ t, Reaches Image.code u t ∧
      t.pc = (if j + 1 < nCols i then 0x80002f9c else 0x80003024) ∧
        CountAt OI s t A k R Q B lo i P p c L0 (j + 1) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have H := h.base
  have V := h.vecs
  have hi := h.lt
  have hj := h.jlt
  have sp : u.getReg .x2 = s.getReg .x2 - 2656 := H.inv.sp
  have hl := H.loLe
  have hhu := H.inv.heap.hi
  have hs0 := hpre.heap.lo
  simp only [heapEnd, heapStart] at hhu hs0
  have hbd := BlocksSound.bounds V.count
  have hroom := h.room
  have hPc : p.toNat + 48 * c ≤ heapNext u ∧ 0x20000000 ≤ p.toNat ∧ p.toNat % 8 = 0 := by
    simp only [heapStart] at hbd
    rcases hbd.2 with h0 | h0 <;> refine ⟨by omega, by omega, hbd.1⟩
  have hBb := H.bufB
  obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80002fe8_spec hpc (by
    rv_eval [sp, h.x20, h.x22]
    simp only [Sym.validAccess_eight, ne_eq]
    and_intros
    all_goals first
      | (intro he; have := congrArg BitVec.toNat he; addr_omega [this, hb1, hb2, hPc, hroom, hj, hhu])
      | addr_omega [hb1, hb2, hb3, hPc, hroom, hj, hhu, hBb, hl, hi])
  have fr₅ : MemFrame u u₅ (p + BitVec.ofNat 64 (48 * (L0 + j))) 48 := by
    rw [← h.x20]; exact b80002fe8_frame h₅ (by rw [h.x20]; addr_omega [hPc, hroom, hj, hhu])
  have f1728 : u.getReg .x2 + 1728 = s.getReg .x2 - 928 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have f1736 : u.getReg .x2 + 1736 = s.getReg .x2 - 928 + 8 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have f1744 : u.getReg .x2 + 1744 = s.getReg .x2 - 928 + 16 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  obtain ⟨V₅, fv5⟩ := V.store hpre H.inv.heap (by omega) h.lo h.below h.nok h.deep fr₅
    (by rw [← h.x20, b80002fe8_m_x20_0 h₅, f1728])
    (by rw [← h.x20, b80002fe8_m_x20_8 h₅, f1736])
    (by rw [← h.x20, b80002fe8_m_x20_16 h₅, f1744])
  have op₆ : u.getMem (u.getReg .x22 + 72) = BitVec.ofNat 64 i := by
    rw [h.x22]; exact opAt H h.op5 hi
  have hH := heightsLe H.ok i
  have colLe : (countColumnsRust.getD i []).getD j 0 ≤ 91 :=
    getD_le (by interval_cases i <;> decide) j
  have hblk : blockOf u₅ (p + BitVec.ofNat 64 (48 * (L0 + j))) =
      blkOf A i [colRust ((countColumnsRust.getD i []).getD j 0) 0] := by
    simp only [blockOf, blkOf]
    rw [← h.x20, b80002fe8_m_x20_24 h₅, b80002fe8_m_x20_32 h₅, b80002fe8_m_x20_40 h₅, h.x26, h.x8,
      op₆, h.x20, fv5, h.coords]
    simp only [BitVec.toNat_ofNat]
    congr 1
    · exact Nat.mod_eq_of_lt (by omega)
    · exact Nat.mod_eq_of_lt (by omega)
  have hpre1 : countPre A i (j + 1) =
      countPre A i j ++ [blkOf A i [colRust ((countColumnsRust.getD i []).getD j 0) 0]] := by
    have hj' : j < (countColumnsRust.getD i []).length := hj
    unfold countPre
    rw [List.take_add_one, List.map_append, List.getElem?_eq_getElem hj']
    simp only [Option.toList_some, List.map_cons, List.map_nil, List.getD_eq_getElem _ _ hj']
  rw [hblk, List.append_assoc, ← hpre1] at V₅
  have m₅ (x : Word) (hx : ¬ Within x (p + BitVec.ofNat 64 (48 * (L0 + j))) 48) :
      u₅.getMem x = u.getMem x := fr₅ x hx
  have hn₅ : heapNext u₅ = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (m₅ _ (by simp only [Within, nextAddr]; addr_omega [hPc, hroom, hj, hhu]))
  have hv₅ : HeapOk u₅ := ⟨hn₅ ▸ H.inv.heap.lo, hn₅ ▸ H.inv.heap.hi⟩
  have k₅ := b80002fe8_keeps h₅
  have fw5 (x : Word) (h1 : (s.getReg .x2 - 2656).toNat ≤ x.toNat) :
      u₅.getMem x = u.getMem x :=
    m₅ x (by simp only [Within]; addr_omega [h1, hPc, hroom, hj, hhu, hb1])
  have hN27 := nCols_le hi
  have hsub : u.getReg .x24 - 1 = BitVec.ofNat 64 (nCols i - (j + 1)) := by
    rw [h.x24]; apply BitVec.eq_of_toNat_eq
    have h1 : (1 : Word).toNat = 1 := rfl
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, h1]; omega
  refine ⟨u₅, hr₅, ?_, {
    base := H.keep hpre (MemFrame.dframe fr₅) (fun x hx ↦ by
        have := V.fresh x (Or.inr (Or.inr (Or.inl (by
          simp only [Within] at hx ⊢; addr_omega [hx, hPc, hroom, hj, hhu]))))
        exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨this, by
          simp only [Within] at hx; rw [hn₅]; addr_omega [hx, hPc, hroom, hj, hhu]⟩)))))
      hv₅ hn₅.ge (k₅ .x2 (by decide))
    op5 := by
      rw [m₅ _ (fun hw ↦ by
        have := V.fresh (B + 472) (Or.inr (Or.inr (Or.inl (by
          simp only [Within] at hw ⊢; addr_omega [hw, hPc, hroom, hj, hhu]))))
        addr_omega [this, hBb, hl, hhu]), h.op5]
    vecs := V₅
    lt := hi
    jlt := hj
    room := hroom
    hdr := by
      obtain ⟨a1, a2, a3⟩ := h.hdr
      exact ⟨by rw [fw5 _ (by addr_omega [hb1])]; exact a1, by rw [fw5 _ (by addr_omega [hb1])]; exact a2,
        by rw [fw5 _ (by addr_omega [hb1])]; exact a3⟩
    x9 := by rw [k₅ .x9 (by decide)]; exact h.x9
    x18 := by rw [k₅ .x18 (by decide)]; exact h.x18
    x19 := by rw [k₅ .x19 (by decide)]; exact h.x19
    x21 := by rw [k₅ .x21 (by decide)]; exact h.x21
    x22 := by rw [k₅ .x22 (by decide)]; exact h.x22
    x20 := by
      rw [b80002fe8_x20 h₅, h.x20, BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      have h48 : (48 : Word).toNat = 48 := rfl
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h48]; omega
    x23 := by
      rw [b80002fe8_x23 h₅, h.x23]
      apply BitVec.eq_of_toNat_eq
      have h1 : (1 : Word).toNat = 1 := rfl
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h1]; omega
    x24 := by rw [b80002fe8_x24 h₅, hsub]
    x27 := by
      rw [b80002fe8_x27 h₅, h.x27, BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq
      have h8 : (8 : Word).toNat = 8 := rfl
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h8]; omega
    n := by rw [fw5 _ (by addr_omega [hb1])]; exact h.n
    hgt := by rw [fw5 _ (by addr_omega [hb1])]; exact h.hgt
    row := by rw [fw5 _ (by addr_omega [hb1])]; exact h.row }⟩
  split_ifs with hc
  · exact b80002fe8_pc_taken h₅ (by
      rw [hsub]; intro he; have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat] at this; have h0 : (0 : Word).toNat = 0 := rfl; omega)
  · exact b80002fe8_pc_not_taken h₅ (by
      rw [hsub]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]
      have h0 : (0 : Word).toNat = 0 := rfl; omega)

end Rv64Verifier.Proofs.Walk
