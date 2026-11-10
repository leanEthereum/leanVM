import Rv64Verifier.Proofs.Main.NewEnd

/-!
# `Bytecode::new`'s blocks: after `group`, the counts

`QS`: past `group`, what a block keeps until it writes the `Vec`s, `distinct` at `D` below `H`
(`QS.frame`, for writes in `Wq H`). `count_alloc`: `0x80000650` allocates `counts`, zeroed, at
`C`; `count_step`: one position of the count loop (`0x800006c0`), `Model.countStep` on the counts
in memory (`CL`); `count_loop`: to the loop's exit at `0x800006dc`.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.Bytecode
  Rv64Verifier.Blocks.F3

/-- What a block writes past `group`, before its `Vec`s: `main`'s scratch slots, callees' stacks,
`NEXT` and the heap from `H` on. -/
@[rv_addr] def Wq (H : Nat) (a : Word) : Prop :=
  Within a (msp + 24) 16 ∨ Within a (msp + 72) 16 ∨ Within a (msp + 104) 32 ∨
    Within a (msp + 272) 24 ∨ Within a (msp - 4096) 4096 ∨ Within a nextAddr 8 ∨
    (H ≤ a.toNat ∧ a.toNat < heapEnd)

/-- Past `group` in block `i`: its state `g` (`distinct` nonempty, at `D`, below `H`). -/
structure QS (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (g : GrpSt) (D : Word) (H : Nat) (t : MachineState) : Prop where
  k : BK s words u₀ i L Hb st t
  vecs : VecsAt t st
  bufs : VecBufs t (heapNext u₀) Hb
  go : halvesAt t (u₀.getReg .x9) 0x4000 = g.2.1
  fold : gfold words i st L = some g
  ne : g.2.2 ≠ []
  dist : t.readWords D g.2.2.length = g.2.2
  dal : D.toNat % 8 = 0
  dlo : Hb ≤ D.toNat
  dhi : D.toNat + 8 * g.2.2.length ≤ H
  hH : H ≤ heapNext t

section
variable {s u₀ t t' : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D : Word} {H : Nat}

theorem QS.frame {W : Word → Prop} (h : QS s words u₀ i L Hb st g D H t) (hf : BFrame t t' W)
    (hW : ∀ a, W a → Wq H a) (hsp : t'.getReg .x2 = msp) (hheap : HeapOk t')
    (hmono : heapNext t ≤ heapNext t') : QS s words u₀ i L Hb st g D H t' := by
  have hGO := h.k.a.groupOf
  have hSL := h.k.a.slots
  have hH0 := h.k.hb0
  have hhi := h.k.ng.heap.hi
  have hdlo := h.dlo
  have hdhi := h.dhi
  have hhH := h.hH
  simp only [heapStart] at hSL
  simp only [heapNext, heapEnd] at hGO hH0 hhi hhH
  have hW' : ∀ a, W a → WB (heapNext u₀) Hb a := by
    intro a ha
    rcases hW a ha with h1 | h1 | h1 | h1 | h1 | h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, h2⟩))))))
  have hlow : ∀ a : Word, heapStart ≤ a.toNat → a.toNat < H → byteAt t' a = byteAt t a :=
    fun a h1 h2 ↦ hf a fun hw ↦ by
      simp only [heapStart] at h1
      rcases hW a hw with h3 | h3 | h3 | h3 | h3 | h3 | ⟨h3, h4⟩
      all_goals first | omega | addr_omega [h1, h2, h3, hhH, hhi]
  have hHb : Hb ≤ heapEnd := by simp only [heapEnd]; omega
  obtain ⟨vecs, bufs⟩ := VecsAt.frame h.vecs h.bufs hf (fun a ha ↦ WB.vec hH0 hHb (hW' a ha)) hHb
  refine ⟨h.k.frame hf hW' hsp hheap hmono, vecs, bufs, ?_, h.fold, h.ne, ?_, h.dal, hdlo, hdhi,
    le_trans hhH hmono⟩
  · rw [← h.go]
    exact halvesAt_keep hGO.1 (fun a h1 h2 ↦ hlow a (by simp only [heapStart]; omega) (by omega))
      (by omega)
  · refine Eq.trans ?_ h.dist
    rw [readWords_eq_map, readWords_eq_map]
    apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    exact getMem_eq_of_bytes (by addr_omega [h.dal, hj, hdhi, hhi, hhH])
      (by addr_omega [h.dal, hj, hdhi, hhi, hhH]) fun x hx ↦ hlow _
        (by simp only [heapStart]; addr_omega [hx, hj, hdlo, hdhi, hhi, hhH, hH0, hSL, hGO])
        (by addr_omega [hx, hj, hdlo, hdhi, hhi, hhH])

/-- `group`'s exit past a block with a nonzero word. -/
theorem GS.toQS (h : GS s words u₀ i L Hb st L g t) (hf : gfold words i st L = some g)
    (hne : g.2.2 ≠ []) : QS s words u₀ i L Hb st g (t.getMem (msp + 112)) (heapNext t) t := by
  have m := h.mem
  have hpos : 0 < g.2.2.length := List.length_pos_iff.mpr hne
  obtain ⟨h1, h2⟩ := m.buf.resolve_left (by have := m.cap; omega)
  have := m.cap
  refine ⟨h.k, h.vecs, h.bufs, m.groupOf, hf, hne, m.dist, m.al, h1, ?_, le_rfl⟩
  have := Nat.mul_le_mul_right 8 m.cap
  omega

end

theorem rwords_set {t t' : MachineState} {b : Word} {n p : Nat} {v : Word}
    (hv : t'.getMem (b + BitVec.ofNat 64 (8 * p)) = v)
    (hfr : ∀ j < n, j ≠ p →
      t'.getMem (b + BitVec.ofNat 64 (8 * j)) = t.getMem (b + BitVec.ofNat 64 (8 * j))) :
    t'.readWords b n = (t.readWords b n).set p v := by
  rw [readWords_eq_map, readWords_eq_map]
  apply List.ext_getElem (by simp)
  intro j h1 _
  simp only [List.length_map, List.length_range] at h1
  rw [List.getElem_set]
  simp only [List.getElem_map, List.getElem_range]
  split
  · rename_i e; subst e; exact hv
  · rename_i e; exact hfr j h1 (Ne.symm e)

theorem rwords_zero {t : MachineState} {a : Word} {n : Nat} (ha : a.toNat % 8 = 0)
    (h : bytesAt t a (n * 8) = List.replicate (n * 8) 0) :
    t.readWords a n = List.replicate n 0 := by
  rw [readWords_eq_map]
  apply List.ext_getElem (by simp)
  intro j h1 _
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
  have hal : (a + BitVec.ofNat 64 (8 * j)).toNat % 8 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine eq_of_extractByte fun k hk ↦ ?_
  rw [← byteAt_add hal hk, BitVec.add_assoc, ← BitVec.ofNat_add]
  have e := List.getElem_of_eq h (by rw [bytesAt_length]; omega :
    8 * j + k < (bytesAt t a (n * 8)).length)
  rw [bytesAt_getElem, List.getElem_replicate] at e
  rw [e]
  simp [extractByte]


/-- `counts` after the positions `< p` of block `i`. -/
def cfold (words : List Word) (i : Nat) (g : GrpSt) (p : Nat) : List Nat :=
  (List.range p).foldl (Model.countStep (blk words i) g.2.1) (List.replicate g.2.2.length 0)

/-- In the count loop at position `p`: `counts` at `C` (from `H` on) holds `cs`. -/
structure CL (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (g : GrpSt) (D : Word) (H : Nat) (C : Word) (p : Nat)
    (cs : List Nat) (t : MachineState) : Prop where
  qs : QS s words u₀ i L Hb st g D H t
  hp : p ≤ L
  cal : C.toNat % 8 = 0
  clo : H ≤ C.toNat
  chi : C.toNat + 8 * g.2.2.length ≤ heapNext t
  m72 : t.getMem (msp + 72) = D
  m80 : t.getMem (msp + 80) = C
  cnt : t.readWords C g.2.2.length = cs.map (BitVec.ofNat 64)
  x8 : t.getReg .x8 = u₀.getReg .x8
  x10 : t.getReg .x10 = BitVec.ofNat 64 p
  x11 : t.getReg .x11 = BitVec.ofNat 64 (8 * (L - p))
  x12 : t.getReg .x12 = u₀.getReg .x9 + BitVec.ofNat 64 (2 * p)
  x13 : t.getReg .x13 = inputBase + BitVec.ofNat 64 (8 * (1 + 2 ^ 14 * i + p))
  x18 : t.getReg .x18 = BitVec.ofNat 64 g.2.2.length
  x20 : t.getReg .x20 = BitVec.ofNat 64 (8 * L)
  x21 : t.getReg .x21 = inputBase + BitVec.ofNat 64 (8 * (1 + 2 ^ 14 * i))
  x22 : t.getReg .x22 = 32768
  x23 : t.getReg .x23 = u₀.getReg .x9
  x25 : t.getReg .x25 = u₀.getReg .x8 + 0x20000
  x26 : t.getReg .x26 = BitVec.ofNat 64 ((words.getD 0 0).toNat - 2 ^ 14 * i - L)
  x27 : t.getReg .x27 = 1

theorem mspW_wq {H : Nat} {c n : Nat} (hc : (72 ≤ c ∧ c + n ≤ 88) ∨ (104 ≤ c ∧ c + n ≤ 136))
    {a : Word} (ha : Within a (msp + BitVec.ofNat 64 c) n) : Wq H a := by
  rcases hc with hc | hc
  · exact Or.inr (Or.inl (by addr_omega [ha, hc]))
  · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hc])))

section
variable {s u₀ t : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt}

/-- `0x8000064c`, a nonzero word in the block: `counts` allocated and zeroed, into the count loop. -/
theorem count_alloc (h : GS s words u₀ i L Hb st L g t) (hpc : t.pc = 0x8000064c)
    (hf : gfold words i st L = some g) (hne : g.2.2 ≠ []) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ ∃ C, v.pc = 0x800006c0 ∧
      CL s words u₀ i L Hb st g (t.getMem (msp + 112)) (heapNext t) C 0 (cfold words i g 0) v) := by
  have qs := h.toQS hf hne
  have hsp := h.k.ng.sp
  have hpos : 0 < g.2.2.length := List.length_pos_iff.mpr hne
  have hhi := h.k.ng.heap.hi
  have hdhi := qs.dhi
  simp only [heapNext, heapEnd] at hhi hdhi
  have hdl : g.2.2.length < 2 ^ 28 := by omega
  -- `0x8000064c`
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000064c_spec hpc trivial
  have k₁ := b8000064c_keeps h₁
  have hm₁ := b8000064c_mem_same h₁
  have hx18 : t.getReg .x18 ≠ 0 := by
    rw [h.x18]; intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ofNat] at this
    have h0 : (0 : Word).toNat = 0 := rfl
    omega
  have hsp₁ : t₁.getReg .x2 = msp := (k₁ .x2 (by decide)).trans hsp
  -- `0x80000650`
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b80000650_spec (b8000064c_pc_not_taken h₁ hx18)
    (by rv_eval [hsp₁, msp]; decide)
  have k₂ := b80000650_keeps h₂
  have hsp₂ : t₂.getReg .x2 = msp := (k₂ .x2 (by decide)).trans hsp₁
  have hf₂ : BFrame t₁ t₂ (Within · (msp + 72) 8) := by
    have e := BFrame.of_memFrame (b80000650_frame h₂ (by rw [hsp₁]; decide)) (by rw [hsp₁]; decide)
      (by decide)
    rw [hsp₁] at e; exact e
  have hn₂ : heapNext t₂ = heapNext t := by
    simp only [heapNext]
    rw [hf₂.getMem (by decide) fun j hj hw ↦ by addr_omega [hw, hj], hm₁]
  have x10₂ : t₂.getReg .x10 = msp + 104 := by rw [b80000650_x10 h₂, hsp₁]
  have pre : TryAllocPre .x13 .x14 t₂ := {
    heap := ⟨by rw [hn₂]; exact h.k.ng.heap.lo, by rw [hn₂]; exact h.k.ng.heap.hi⟩
    out := by rw [x10₂]; exact validRange_of (by decide) (by decide) (by decide)
    align := by rw [b80000650_x13 h₂]; decide
    size := by rw [b80000650_x14 h₂]; decide
    stack := rtStack_msp hsp₂ (by decide) (by decide)
    outFree := by
      rw [x10₂]
      exact ⟨Or.inr (by simp only [heapEnd]; decide), by addr_omega []⟩
    outStack := by rw [x10₂]; simp only [stackLo, hsp₂, tryAllocStack]; addr_omega [] }
  obtain ⟨t₃, r₃, ⟨hpc₃, hpv, post, hz⟩ | hd⟩ :=
    tryAllocZeroed.call r₂ (b80000650_pc h₂) pre
  swap
  · exact ⟨t₃, r₁.trans r₃, Or.inl hd⟩
  have hpc₃' : t₃.pc = 0x80000674 := by rw [hpc₃, returnAddress, b80000650_x1 h₂]; decide
  have hsp₃ : t₃.getReg .x2 = msp := (hpv.reg .x2).trans hsp₂
  have pf := post.frame
  rw [x10₂] at pf
  -- `0x80000674`
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b80000674_spec hpc₃' (by rv_eval [hsp₃, msp]; decide)
  have k₄ := b80000674_keeps h₄
  have hm₄ := b80000674_mem_same h₄
  by_cases htag : t₃.getMem (msp + 104) = 0
  swap
  · obtain ⟨w, rw', hw⟩ := abort (u := t₄) (by
      rw [b80000674_pc_taken h₄ (by rw [hsp₃]; exact htag)]; decide)
    exact ⟨w, r₁.trans (r₃.trans (r₄.trans rw')), Or.inl hw⟩
  have hpc₄ := b80000674_pc_not_taken h₄ (by rw [hsp₃]; exact htag)
  have hsp₄ : t₄.getReg .x2 = msp := (k₄ .x2 (by decide)).trans hsp₃
  -- `0x8000067c`
  obtain ⟨t₅, r₅, h₅⟩ := Sym.BlockSpec.reaches b8000067c_spec hpc₄ (by rv_eval [hsp₄, msp]; decide)
  have k₅ := b8000067c_keeps h₅
  have hf₅ : BFrame t₄ t₅ (Within · (msp + 80) 8) := by
    have e := BFrame.of_memFrame (b8000067c_frame h₅ (by rw [hsp₄]; decide)) (by rw [hsp₄]; decide)
      (by decide)
    rw [hsp₄] at e; exact e
  have hsp₅ : t₅.getReg .x2 = msp := (k₅ .x2 (by decide)).trans hsp₄
  -- what the allocation gives
  have e120 : (msp + 104 + 16 : Word) = msp + 120 := by decide
  obtain ⟨-, hnb⟩ := post.ok (by rw [x10₂]; exact htag)
  have hz' := hz (by rw [b80000650_x12 h₂]; decide) (by rw [x10₂]; exact htag)
  rw [x10₂, e120, b80000650_x11 h₂, b80000650_x14 h₂, k₁ .x18 (by decide), h.x18] at hz'
  rw [x10₂, e120, b80000650_x11 h₂, b80000650_x13 h₂, b80000650_x14 h₂, k₁ .x18 (by decide),
    h.x18] at hnb
  simp only [BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from rfl] at hz' hnb
  rw [Nat.mod_eq_of_lt (by omega)] at hz' hnb
  obtain ⟨hcal, hcb⟩ := hnb
  have hcb' := hcb.resolve_left (by omega)
  -- the frame from `t`
  have hn₅ : heapNext t₅ = heapNext t₃ := by
    simp only [heapNext]
    rw [hf₅.getMem (by decide) fun j hj hw ↦ by addr_omega [hw, hj], hm₄]
  have hW₃ : ∀ a, (Within a (msp + 104) 24 ∨ Within a (stackLo t₂ tryAllocStack) tryAllocStack ∨
      Within a nextAddr 8 ∨ Fresh t₂ t₃ a) → Wq (heapNext t) a := by
    intro a ha
    rcases ha with ha | ha | ha | ⟨ha1, ha2⟩
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha])))
    · simp only [stackLo, hsp₂, tryAllocStack] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)))))
      · rw [← hn₂]; exact ha1
      · have := post.heap.hi; simp only [heapNext, heapEnd] at ha2 this ⊢; omega
  have f₁ : BFrame t t₂ (Wq (heapNext t)) := (BFrame.of_same hm₁ _).trans
    (hf₂.mono fun a ha ↦ mspW_wq (c := 72) (n := 8) (by omega) ha) fun _ h ↦ h
  have f₃ : BFrame t₂ t₄ (Wq (heapNext t)) := fun a ha ↦ by
    rw [byteAt_eq, byteAt_eq, hm₄, ← byteAt_eq, ← byteAt_eq]
    exact pf.byte a fun h' ↦ ha (hW₃ a h')
  have f₅ : BFrame t₄ t₅ (Wq (heapNext t)) :=
    hf₅.mono fun a ha ↦ mspW_wq (c := 80) (n := 8) (by omega) ha
  have hf : BFrame t t₅ (Wq (heapNext t)) := (f₁.trans f₃ fun _ h ↦ h).trans f₅ fun _ h ↦ h
  have hheap₅ : HeapOk t₅ := ⟨by rw [hn₅]; exact post.heap.lo, by rw [hn₅]; exact post.heap.hi⟩
  have hmo₅ : heapNext t ≤ heapNext t₅ := by rw [hn₅, ← hn₂]; exact post.mono
  have qs₅ := qs.frame hf (fun _ h ↦ h) hsp₅ hheap₅ hmo₅
  have R : ∀ r ∈ ([.x8, .x18, .x20, .x21, .x22, .x23, .x25, .x26, .x27] : List Reg),
      t₅.getReg r = t.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (k₅ _ (by decide)).trans ((k₄ _ (by decide)).trans ((hpv.reg _ (by decide)).trans
        ((k₂ _ (by decide)).trans (k₁ _ (by decide)))))
  have m72 : t₅.getMem (msp + 72) = t.getMem (msp + 112) := by
    rw [hf₅.getMem (by decide) fun j hj hw ↦ by addr_omega [hw, hj], hm₄,
      pf.getMem fun j hj hw ↦ by
        rcases hw with hw | hw | hw | ⟨hw1, hw2⟩
        · addr_omega [hw, hj]
        · simp only [stackLo, hsp₂, tryAllocStack] at hw; addr_omega [hw, hj]
        · addr_omega [hw, hj]
        · have := post.heap.hi; simp only [heapNext, heapEnd] at hw2 this; addr_omega [hw2, this, hj],
      ← hsp₁, b80000650_m_x2_72 h₂, hsp₁, hm₁]
  have m80 : t₅.getMem (msp + 80) = t₃.getMem (msp + 120) := by
    have e := b8000067c_m_x2_80 h₅
    rw [hsp₄, hm₄] at e
    exact e
  have hn₅' := hn₅
  have hn₂' := hn₂
  simp only [heapNext] at hcb' hn₅' hn₂'
  have cnt : t₅.readWords (t₃.getMem (msp + 120)) g.2.2.length =
      (cfold words i g 0).map (BitVec.ofNat 64) := by
    show _ = (List.replicate g.2.2.length 0).map _
    have := post.heap.hi
    simp only [heapNext, heapEnd] at this
    rw [List.map_replicate, readWords_bframe hf₅ hcal (fun a ha hw ↦ by
        addr_omega [ha, hw, hcb'.1, hcb'.2, this, hn₂']) (by omega),
      readWords_same hm₄, rwords_zero hcal hz']
    rfl
  have hR : ∀ r ∈ ([.x20, .x21, .x23] : List Reg), t₄.getReg r = t.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact (k₄ _ (by decide)).trans ((hpv.reg _ (by decide)).trans
        ((k₂ _ (by decide)).trans (k₁ _ (by decide))))
  refine ⟨t₅, r₁.trans (r₃.trans (r₄.trans r₅)), Or.inr ⟨t₃.getMem (msp + 120), b8000067c_pc h₅,
    ⟨qs₅, Nat.zero_le _, hcal, ?_, ?_, m72, m80, cnt, (R .x8 (by decide)).trans h.x8, ?_, ?_, ?_, ?_,
      (R .x18 (by decide)).trans h.x18, (R .x20 (by decide)).trans h.x20,
      (R .x21 (by decide)).trans h.x21, (R .x22 (by decide)).trans h.x22,
      (R .x23 (by decide)).trans h.x23, (R .x25 (by decide)).trans h.x25,
      (R .x26 (by decide)).trans h.x26, (R .x27 (by decide)).trans h.x27⟩⟩⟩
  · simp only [heapNext]; omega
  · simp only [heapNext]; omega
  · rw [k₅ .x10 (by decide), b80000674_x10 h₄, hsp₃, htag]; rfl
  · rw [b8000067c_x11 h₅, hR .x20 (by decide), h.x20, Nat.sub_zero]
  · rw [b8000067c_x12 h₅, hR .x23 (by decide), h.x23]; simp
  · rw [b8000067c_x13 h₅, hR .x21 (by decide), h.x21, Nat.add_zero]

end


theorem cfold_succ (words : List Word) (i : Nat) (g : GrpSt) (p : Nat) :
    cfold words i g (p + 1) = Model.countStep (blk words i) g.2.1 (cfold words i g p) p := by
  simp only [cfold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

section
variable {s u₀ t t' : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D : Word} {H : Nat} {C : Word} {p : Nat} {cs : List Nat}

/-- A step that writes only `counts` and changes no register `CL` names. -/
theorem CL.write (h : CL s words u₀ i L Hb st g D H C p cs t) {W : Word → Prop}
    (hf : BFrame t t' W) (hW : ∀ a, W a → C.toNat ≤ a.toNat ∧ a.toNat < C.toNat + 8 * g.2.2.length)
    (hr : ∀ r, r ≠ .x14 → r ≠ .x15 → t'.getReg r = t.getReg r) (hn : heapNext t' = heapNext t)
    {cs' : List Nat} (hc : t'.readWords C g.2.2.length = cs'.map (BitVec.ofNat 64)) :
    CL s words u₀ i L Hb st g D H C p cs' t' := by
  have hsp : t'.getReg .x2 = msp := (hr .x2 (by decide) (by decide)).trans h.qs.k.ng.sp
  have hhi := h.qs.k.ng.heap.hi
  have hclo := h.clo
  have hchi := h.chi
  have hH := h.qs.hH
  have hb0 := h.qs.k.hb0
  have hl0 := h.qs.k.a.inv.heap.lo
  have hdlo := h.qs.dlo
  simp only [heapNext, heapEnd, heapStart] at hhi hchi hH hb0 hl0
  have hWq : ∀ a, W a → Wq H a := fun a ha ↦ by
    have := hW a ha
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by simp only [heapEnd]; omega⟩)))))
  have K : ∀ c : Nat, c = 72 ∨ c = 80 → t'.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) :=
    fun c hc ↦ hf.getMem (by rcases hc with rfl | rfl <;> decide) fun j hj hw ↦ by
      have := hW _ hw
      rcases hc with rfl | rfl <;> addr_omega [this, hj, hchi, hhi]
  refine ⟨h.qs.frame hf hWq hsp ⟨by rw [hn]; exact h.qs.k.ng.heap.lo, by rw [hn]; exact h.qs.k.ng.heap.hi⟩
    (le_of_eq hn.symm), h.hp, h.cal, h.clo, by rw [hn]; exact h.chi, (K 72 (by omega)).trans h.m72,
    (K 80 (by omega)).trans h.m80, hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [hr _ (by decide) (by decide)]; first
        | exact h.x8 | exact h.x10 | exact h.x11 | exact h.x12 | exact h.x13 | exact h.x18
        | exact h.x20 | exact h.x21 | exact h.x22 | exact h.x23 | exact h.x25 | exact h.x26
        | exact h.x27)

/-- `0x800006ac`: on to position `p + 1`, or out of the loop. -/
theorem count_adv (h : CL s words u₀ i L Hb st g D H C p cs t) (hpc : t.pc = 0x800006ac)
    (hp : p < L) :
    ∃ v, Reaches Image.code t v ∧ CL s words u₀ i L Hb st g D H C (p + 1) cs v ∧
      ((p + 1 < L ∧ v.pc = 0x800006c0) ∨ (p + 1 = L ∧ v.pc = 0x800006dc)) := by
  obtain ⟨v, rv, hv⟩ := Sym.BlockSpec.reaches b800006ac_spec hpc trivial
  have kv := b800006ac_keeps hv
  have hm := b800006ac_mem_same hv
  have hfit := h.qs.k.a.inv.fits
  simp only [inputWords] at hfit
  have hlen := h.qs.k.a.len
  have hlt := h.qs.k.lt
  have hL := h.qs.k.hL
  have hib : inputBase.toNat = 0x10000000 := rfl
  have hGO := h.qs.k.a.groupOf
  have hhi := h.qs.k.ng.heap.hi
  have hH0 := h.qs.k.ng.mono
  simp only [heapNext, heapEnd] at hGO hhi hH0
  have hsp : v.getReg .x2 = msp := (kv .x2 (by decide)).trans h.qs.k.ng.sp
  have hn : heapNext v = heapNext t := by simp only [heapNext, hm]
  have R : ∀ r ∈ ([.x8, .x18, .x20, .x21, .x22, .x23, .x25, .x26, .x27] : List Reg),
      v.getReg r = t.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact kv _ (by decide)
  have qs := h.qs.frame (BFrame.of_same hm (fun _ ↦ False)) (fun _ h ↦ h.elim) hsp
    ⟨by rw [hn]; exact h.qs.k.ng.heap.lo, by rw [hn]; exact h.qs.k.ng.heap.hi⟩ (le_of_eq hn.symm)
  have hL14 : L ≤ 2 ^ 14 := by omega
  have cl : CL s words u₀ i L Hb st g D H C (p + 1) cs v := by
    refine ⟨qs, by omega, h.cal, h.clo, by rw [hn]; exact h.chi, by rw [hm]; exact h.m72,
      by rw [hm]; exact h.m80, by rw [readWords_same hm]; exact h.cnt,
      (R .x8 (by decide)).trans h.x8, ?_, ?_, ?_, ?_, (R .x18 (by decide)).trans h.x18,
      (R .x20 (by decide)).trans h.x20, (R .x21 (by decide)).trans h.x21,
      (R .x22 (by decide)).trans h.x22, (R .x23 (by decide)).trans h.x23,
      (R .x25 (by decide)).trans h.x25, (R .x26 (by decide)).trans h.x26,
      (R .x27 (by decide)).trans h.x27⟩
    · rw [b800006ac_x10 hv, h.x10, BitVec.ofNat_add]; rfl
    · rw [b800006ac_x11 hv, h.x11]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      have h8 : (8 : Word).toNat = 8 := rfl
      rw [h8]
      omega
    · rw [b800006ac_x12 hv, h.x12]
      apply BitVec.eq_of_toNat_eq
      addr_omega [hGO, hhi, hH0, hp, hL14]
    · rw [b800006ac_x13 hv, h.x13]
      apply BitVec.eq_of_toNat_eq
      addr_omega [hib, hfit, hlen, hlt, hL, hp]
  have e11 : t.getReg .x11 - 8 = BitVec.ofNat 64 (8 * (L - (p + 1))) := by
    rw [h.x11]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have h8 : (8 : Word).toNat = 8 := rfl
    rw [h8]
    omega
  by_cases e : p + 1 = L
  · refine ⟨v, rv, cl, Or.inr ⟨e, b800006ac_pc_taken hv ?_⟩⟩
    rw [e11, ← e, Nat.sub_self]; rfl
  · refine ⟨v, rv, cl, Or.inl ⟨by omega, b800006ac_pc_not_taken hv fun he ↦ ?_⟩⟩
    rw [e11] at he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat] at this
    have h0 : (0 : Word).toNat = 0 := rfl
    omega

end


theorem cfold_length (words : List Word) (i : Nat) (g : GrpSt) :
    ∀ p, (cfold words i g p).length = g.2.2.length := by
  intro p
  induction p with
  | zero => simp [cfold]
  | succ p ih =>
    rw [cfold_succ, Model.countStep]
    split
    · rw [List.length_set, ih]
    · exact ih

theorem getD_map_ofNat {cs : List Nat} {k : Nat} (hk : k < cs.length) :
    (cs.map (BitVec.ofNat 64)).getD k 0 = BitVec.ofNat 64 (cs.getD k 0) := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem rwords_getD {t : MachineState} {C : Word} {n k : Nat} (hk : k < n) :
    (t.readWords C n).getD k 0 = t.getMem (C + BitVec.ofNat 64 (8 * k)) := by
  simp [readWords_eq_map, List.getD_eq_getElem?_getD, hk]

section
variable {s u₀ t : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D : Word} {H : Nat} {C : Word} {p : Nat}

/-- `0x800006c0`: position `p` counted, to `0x800006ac`. -/
theorem count_step (h : CL s words u₀ i L Hb st g D H C p (cfold words i g p) t)
    (hpc : t.pc = 0x800006c0) (hp : p < L) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
      (v.pc = 0x800006ac ∧ CL s words u₀ i L Hb st g D H C p (cfold words i g (p + 1)) v)) := by
  have qs := h.qs
  have hfit := qs.k.a.inv.fits
  simp only [inputWords] at hfit
  have hlen := qs.k.a.len
  have hlt := qs.k.lt
  have hL := qs.k.hL
  have hib : inputBase.toNat = 0x10000000 := rfl
  have hL14 : L ≤ 2 ^ 14 := by omega
  have hGO := qs.k.a.groupOf
  have hSL := qs.k.a.slots
  have hhi := qs.k.ng.heap.hi
  have hH0 := qs.k.ng.mono
  simp only [heapStart] at hSL
  simp only [heapNext, heapEnd] at hGO hhi hH0
  have hw : t.getMem (t.getReg .x13) = (blk words i).getD p 0 := by
    rw [h.x13, blk_getD (by omega) (by omega) hlen, ← (qs.k.ng.minv qs.k.a).input _ (by omega)]
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b800006c0_spec hpc (by
    rv_eval []
    rw [h.x13]
    exact (Sym.validAccess_eight _).mpr ⟨Or.inl ⟨by addr_omega [hib, hfit, hlen, hlt, hL, hp],
      by addr_omega [hib, hfit, hlen, hlt, hL, hp]⟩, by addr_omega [hib, hfit, hlen, hlt, hL, hp]⟩)
  have k₁ := b800006c0_keeps h₁
  have hm₁ := b800006c0_mem_same h₁
  have cl₁ := h.write (BFrame.of_same hm₁ (fun _ ↦ False)) (fun _ h ↦ h.elim) (fun r h14 _ ↦ by
      rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
        _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
      all_goals first | contradiction | exact k₁ _ (by decide) | rfl)
    (by simp only [heapNext, hm₁]) (by rw [readWords_same hm₁]; exact h.cnt)
  by_cases hz : (blk words i).getD p 0 = 0
  · have e : cfold words i g (p + 1) = cfold words i g p := by
      rw [cfold_succ]; simp only [Model.countStep, ne_eq, hz, not_true_eq_false, ↓reduceIte]
    rw [e]
    exact ⟨t₁, r₁, Or.inr ⟨b800006c0_pc_taken h₁ (by rw [hw, hz]), cl₁⟩⟩
  -- `0x800006c8`
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b800006c8_spec
    (b800006c0_pc_not_taken h₁ (by rw [hw]; exact hz)) trivial
  have k₂ := b800006c8_keeps h₂
  have hm₂ := b800006c8_mem_same h₂
  have hpc₂ := b800006c8_pc_not_taken h₂ (by rw [cl₁.x10]; exact shr14_eq_zero (by omega))
  have cl₂ := cl₁.write (BFrame.of_same hm₂ (fun _ ↦ False)) (fun _ h ↦ h.elim) (fun r h14 _ ↦ by
      rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
        _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
      all_goals first | contradiction | exact k₂ _ (by decide) | rfl)
    (by simp only [heapNext, hm₂]) (by rw [readWords_same hm₂]; exact cl₁.cnt)
  -- `0x800006d0`: `group_of[p]`
  obtain ⟨t₃, r₃, hpc₃, hr₃, hm₃⟩ := step_lhu (code := Image.code) (s := t₂) (rd := .x14)
    (rs1 := .x12) (off := 0) (by rw [hpc₂]; exact fetch_of (by decide +kernel))
    (by
      rw [off0, cl₂.x12]
      exact valid2_of (by addr_omega [hSL, hGO, hp, hL14]) (by addr_omega [hGO, hp, hL14, hhi, hH0])
        (by addr_omega [hGO, hp, hL14]))
  rw [off0, cl₂.x12] at hr₃
  set gv := g.2.1.getD p 0 with hgv
  have hgo : t₂.getHalfword (u₀.getReg .x9 + BitVec.ofNat 64 (2 * p)) = gv := by
    rw [hgv, ← cl₂.qs.go, halvesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by omega)]
    rfl
  have x14₃ : t₃.getReg .x14 = gv.zeroExtend 64 := by rw [hr₃]; simp [hgo]
  have cl₃ := cl₂.write (BFrame.of_same hm₃ (fun _ ↦ False)) (fun _ h ↦ h.elim) (fun r h14 _ ↦ by
      rw [hr₃]; simp [h14])
    (by simp only [heapNext, hm₃]) (by rw [readWords_same hm₃]; exact cl₂.cnt)
  have hgvn : (gv.zeroExtend 64 : Word).toNat = gv.toNat := by
    simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
    have := gv.isLt
    omega
  have hpos : 0 < g.2.2.length := List.length_pos_iff.mpr qs.ne
  have hdl : g.2.2.length < 2 ^ 28 := by have := h.chi; simp only [heapNext] at this; omega
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches NB.g800006d4_spec (by rw [hpc₃, hpc₂]; rfl) trivial
  have k₄ := NB.g800006d4_keeps h₄
  have hm₄ := NB.g800006d4_mem_same h₄
  by_cases hb : (t₃.getReg .x18).toNat ≤ (t₃.getReg .x14).toNat
  · obtain ⟨t₅, r₅, h₅⟩ := Sym.BlockSpec.reaches b800006d8_spec (NB.g800006d4_pc_not_taken h₄ hb)
      trivial
    obtain ⟨w, rw', hw'⟩ := abort (u := t₅) (by rw [b800006d8_pc h₅]; decide)
    exact ⟨w, r₁.trans (r₂.trans ((show Reaches Image.code t₂ t₃ from ⟨1, r₃⟩).trans
      (r₄.trans (r₅.trans rw')))), Or.inl hw'⟩
  have hgl : gv.toNat < g.2.2.length := by
    rw [x14₃, hgvn, cl₃.x18, BitVec.toNat_ofNat] at hb
    omega
  have cl₄ := cl₃.write (BFrame.of_same hm₄ (fun _ ↦ False)) (fun _ h ↦ h.elim) (fun r _ _ ↦ by
      rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
        _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
      all_goals first | exact k₄ _ (by decide) | rfl)
    (by simp only [heapNext, hm₄]) (by rw [readWords_same hm₄]; exact cl₃.cnt)
  have x14₄ : t₄.getReg .x14 = gv.zeroExtend 64 := by rw [k₄ .x14 (by decide), x14₃]
  have hsp₄ : t₄.getReg .x2 = msp := cl₄.qs.k.ng.sp
  -- `0x80000694`: `counts[gv] += 1`
  have hclo := cl₄.clo
  have hchi := cl₄.chi
  have hhi₄ := cl₄.qs.k.ng.heap.hi
  have hH := qs.hH
  have hdlo := qs.dlo
  have hdhi := qs.dhi
  have hb0 := qs.k.hb0
  have hl0 := qs.k.a.inv.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hchi hhi₄ hH hb0 hl0
  have hA : t₄.getMem (t₄.getReg .x2 + 80) + t₄.getReg .x14 * 8 = C + BitVec.ofNat 64 (8 * gv.toNat) := by
    rw [hsp₄, cl₄.m80, x14₄]
    apply BitVec.eq_of_toNat_eq
    addr_omega [hgvn, hgl, hclo, hchi, hhi₄]
  obtain ⟨t₅, r₅, h₅⟩ := Sym.BlockSpec.reaches b80000694_spec (NB.g800006d4_pc_taken h₄ (by omega)) (by
    rv_eval []
    rw [hA, hsp₄]
    exact ⟨(Sym.validAccess_eight _).mpr ⟨Or.inl ⟨by addr_omega [hgl, hclo, hchi, hhi₄, hH, hdlo, hdhi, hb0, hl0],
      by addr_omega [hgl, hclo, hchi, hhi₄]⟩, by addr_omega [cl₄.cal, hgl, hclo, hchi, hhi₄]⟩, by decide⟩)
  have k₅ := b80000694_keeps h₅
  have hf₅ : BFrame t₄ t₅ (Within · (C + BitVec.ofNat 64 (8 * gv.toNat)) 8) := by
    refine (holds_bframe h₅ ?_).mono fun a ha ↦ ?_
    · intro k hk
      simp only [b80000694, List.mem_cons, List.not_mem_nil, or_false] at hk
      subst hk
      rv_eval []
      rw [hA]
      addr_omega [cl₄.cal, hgl, hclo, hchi, hhi₄]
    · simp only [b80000694, List.mem_cons, List.not_mem_nil, or_false,
        exists_eq_left] at ha
      rv_eval [] at ha
      rw [hA] at ha
      exact ha
  have hv₅ : t₅.getMem (C + BitVec.ofNat 64 (8 * gv.toNat)) =
      BitVec.ofNat 64 ((cfold words i g p).getD gv.toNat 0 + 1) := by
    have e := b80000694_m0 h₅
    rw [hA] at e
    rw [e, ← rwords_getD hgl, cl₄.cnt, getD_map_ofNat (by rw [cfold_length]; exact hgl),
      BitVec.ofNat_add]
    rfl
  have cnt₅ : t₅.readWords C g.2.2.length = (cfold words i g (p + 1)).map (BitVec.ofNat 64) := by
    rw [rwords_set hv₅ fun j hj hne ↦ hf₅.getMem (by addr_omega [cl₄.cal, hj, hchi, hhi₄, hclo])
        fun k hk hw ↦ by addr_omega [hw, hk, hj, hne, hgl, hchi, hhi₄, hclo], cl₄.cnt,
      ← List.map_set, cfold_succ]
    simp only [Model.countStep, ne_eq, hz, not_false_eq_true, ↓reduceIte]
    rfl
  have cl₅ := cl₄.write hf₅ (fun a ha ↦ by addr_omega [ha, hgl, hchi, hhi₄, hclo])
    (fun r h14 h15 ↦ by
      rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
        _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
      all_goals first | contradiction | exact k₅ _ (by decide) | rfl)
    (by
      simp only [heapNext]
      rw [hf₅.getMem (by decide) fun k hk hw ↦ by addr_omega [hw, hk, hgl, hchi, hhi₄, hclo]])
    cnt₅
  exact ⟨t₅, r₁.trans (r₂.trans ((show Reaches Image.code t₂ t₃ from ⟨1, r₃⟩).trans
    (r₄.trans r₅))), Or.inr ⟨b80000694_pc h₅, cl₅⟩⟩

end


section
variable {s u₀ : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D : Word} {H : Nat} {C : Word}

/-- The count loop, from position `p` to its exit at `0x800006dc`. -/
theorem count_loop : ∀ m p (t : MachineState), L - p = m →
    CL s words u₀ i L Hb st g D H C p (cfold words i g p) t → t.pc = 0x800006c0 → p < L →
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
      (v.pc = 0x800006dc ∧ CL s words u₀ i L Hb st g D H C L (cfold words i g L) v)) := by
  intro m
  induction m with
  | zero => intro p t hm _ _ hp; omega
  | succ m ih =>
    intro p t hm h hpc hp
    obtain ⟨t₁, r₁, hd | ⟨hpc₁, h₁⟩⟩ := count_step h hpc hp
    · exact ⟨t₁, r₁, Or.inl hd⟩
    obtain ⟨t₂, r₂, h₂, ⟨hlt, hpc₂⟩ | ⟨he, hpc₂⟩⟩ := count_adv h₁ hpc₁ hp
    · obtain ⟨v, rv, hv⟩ := ih (p + 1) t₂ (by omega) h₂ hpc₂ hlt
      exact ⟨v, r₁.trans (r₂.trans rv), hv⟩
    · subst he
      exact ⟨t₂, r₁.trans r₂, Or.inr ⟨hpc₂, h₂⟩⟩

/-- `counts`, from `group`'s exit (`0x8000064c`) to `0x800006dc`. -/
theorem count_phase {t : MachineState} (h : GS s words u₀ i L Hb st L g t)
    (hpc : t.pc = 0x8000064c) (hf : gfold words i st L = some g) (hne : g.2.2 ≠ []) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ ∃ C, v.pc = 0x800006dc ∧
      CL s words u₀ i L Hb st g (t.getMem (msp + 112)) (heapNext t) C L (cfold words i g L) v) := by
  obtain ⟨t₁, r₁, hd | ⟨C, hpc₁, h₁⟩⟩ := count_alloc h hpc hf hne
  · exact ⟨t₁, r₁, Or.inl hd⟩
  have hL : 0 < L := by have := h.k.hL; have := h.k.lt; omega
  obtain ⟨v, rv, hv⟩ := count_loop L 0 t₁ (by omega) h₁ hpc₁ hL
  rcases hv with hd | ⟨hpcv, hv⟩
  · exact ⟨v, r₁.trans rv, Or.inl hd⟩
  · exact ⟨v, r₁.trans rv, Or.inr ⟨C, hpcv, hv⟩⟩

end

end Rv64Verifier.Proofs.Main
