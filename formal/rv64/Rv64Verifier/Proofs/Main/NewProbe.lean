import Rv64Verifier.Proofs.Main.NewEntry

/-!
# `group`'s probe

`group` looks a nonzero word up in the slots from `slot_of(word)` on (`0x800005bc`), one slot at a
time (`0x800005e0`, `0x800005f8`), until the word's group or a free slot (`0x80000620`), which
takes the next group, pushing the word onto `distinct` (`grow_one`, `0x8000057c`): `probeRust`
step by step (`probe_loop`, `probe_new`, `probe_first`), to `0x80000594` with the group in `a1`
(`GP`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.Bytecode
  Rv64Verifier.Blocks.F3

theorem getHalfword_same {t t' : MachineState} (hm : ∀ a, t'.getMem a = t.getMem a) (a : Word) :
    t'.getHalfword a = t.getHalfword a := by
  simp only [MachineState.getHalfword, hm]

theorem halvesAt_same {t t' : MachineState} (hm : ∀ a, t'.getMem a = t.getMem a) (p : Word)
    (n : Nat) : halvesAt t' p n = halvesAt t p n := by
  simp only [halvesAt, getHalfword_same hm]

theorem rwords_same {t t' : MachineState} (hm : ∀ a, t'.getMem a = t.getMem a) (p : Word)
    (n : Nat) : t'.readWords p n = t.readWords p n := by
  simp only [readWords_eq_map, hm]

/-- A block whose writes are aligned doublewords changes no byte outside them. -/
theorem holds_bframe {x : Sym.Expect} {s t : MachineState} (h : x.Holds s t)
    (h8 : ∀ k ∈ x.writes, (Sym.Addr.eval s k).toNat % 8 = 0) :
    BFrame s t (fun a ↦ ∃ k ∈ x.writes, Within a (Sym.Addr.eval s k) 8) := by
  refine BFrame.of_dwords (fun a ha ↦ h.frame a fun k hk heq ↦ ha ⟨k, hk, ?_⟩) ?_
  · rw [← heq]; simp only [Within]; omega
  · rintro a ⟨k, hk, hin⟩
    exact ⟨k, hk, within_of_alignDown (h8 k hk) (by decide) hin⟩

/-- What a block writes before its `Vec`s misses them. -/
theorem WB.vec {H0 Hb : Nat} (hH : H0 ≤ Hb) (hE : Hb ≤ heapEnd) {a : Word} (h : WB H0 Hb a) :
    ¬ Within a (msp + 240) 24 ∧ ¬ Within a (msp + 400) 72 ∧ ¬ (H0 ≤ a.toNat ∧ a.toNat < Hb) := by
  simp only [heapEnd] at hE
  rcases h with h | h | h | h | h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun h' ↦ by addr_omega [h, h'], fun h' ↦ by addr_omega [h, h'],
      fun h' ↦ by have := h'.2; addr_omega [h, this, hH, hE]⟩
  · exact ⟨fun h' ↦ by addr_omega [h, h'], fun h' ↦ by addr_omega [h, h'],
      fun h' ↦ by have := h'.2; addr_omega [h, this, hH, hE]⟩
  · exact ⟨fun h' ↦ by addr_omega [h, h'], fun h' ↦ by addr_omega [h, h'],
      fun h' ↦ by have := h'.2; addr_omega [h, this, hH, hE]⟩
  · exact ⟨fun h' ↦ by addr_omega [h, h'], fun h' ↦ by addr_omega [h, h'],
      fun h' ↦ by have := h'.2; addr_omega [h, this, hH, hE]⟩
  · exact ⟨fun h' ↦ by addr_omega [h, h'], fun h' ↦ by addr_omega [h, h'],
      fun h' ↦ by have := h'.2; addr_omega [h, this, hH, hE]⟩
  · exact ⟨fun h' ↦ by addr_omega [h, h'], fun h' ↦ by addr_omega [h, h'],
      fun h' ↦ by have := h'.2; addr_omega [h, this, hH, hE]⟩
  · exact ⟨fun h' ↦ by addr_omega [h2, h', hH, hE], fun h' ↦ by addr_omega [h2, h', hH, hE],
      fun h' ↦ by have := h'.1; omega⟩
  · simp only [heapEnd] at h2
    exact ⟨fun h' ↦ by addr_omega [h2, h'], fun h' ↦ by addr_omega [h2, h'],
      fun h' ↦ by have := h'.2; omega⟩

section
variable {s u₀ t t' : MachineState} {words : List Word} {i L Hb q : Nat} {st : Model.NewState}
  {g : GrpSt}

/-- A step that writes no memory and changes no register `GS` names. -/
theorem GS.same (h : GS s words u₀ i L Hb st q g t) (hm : ∀ a, t'.getMem a = t.getMem a)
    (hr : ∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x19 → t'.getReg r = t.getReg r) :
    GS s words u₀ i L Hb st q g t' := by
  have hn : heapNext t' = heapNext t := by simp only [heapNext, hm]
  have hsp : t'.getReg .x2 = msp := (hr .x2 (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans h.k.ng.sp
  have hf : BFrame t t' (fun _ ↦ False) := BFrame.of_same hm _
  obtain ⟨vecs, bufs⟩ := VecsAt.frame h.vecs h.bufs hf (fun _ h ↦ h.elim) (by
    have := h.k.hb; have := h.k.ng.heap.hi; simp only [heapNext] at *; omega)
  have m := h.mem
  refine ⟨h.k.frame hf (fun _ h ↦ h.elim) hsp ⟨by rw [hn]; exact h.k.ng.heap.lo,
    by rw [hn]; exact h.k.ng.heap.hi⟩ (le_of_eq hn.symm), vecs, bufs,
    ⟨fun j hj ↦ ?_, by rw [halvesAt_same hm]; exact m.groupOf, by rw [hm]; exact m.len,
      by rw [hm]; exact m.cap, by rw [hm]; exact m.al, by rw [hm, hm, hn]; exact m.buf,
      by rw [hm, rwords_same hm]; exact m.dist⟩, h.hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · simp only [getHalfword_same hm]; exact m.slots j hj
  all_goals first
    | (rw [hr _ (by decide) (by decide) (by decide) (by decide) (by decide)]; first
        | exact h.x8 | exact h.x9 | exact h.x15 | exact h.x16 | exact h.x18 | exact h.x20
        | exact h.x21 | exact h.x22 | exact h.x23 | exact h.x24 | exact h.x25 | exact h.x26
        | exact h.x27 | (rw [hm]; exact h.x10))

/-- `0x80000630`: `distinct` full, `grow_one` makes room for one more. -/
theorem grow_distinct (h : GS s words u₀ i L Hb st q g t) (hpc : t.pc = 0x80000630)
    (hfull : t.getReg .x18 = t.getMem (msp + 104)) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (GS s words u₀ i L Hb st q g v ∧
      v.pc = 0x8000057c ∧ g.2.2.length + 1 ≤ (v.getMem (msp + 104)).toNat ∧
      v.getReg .x19 = t.getReg .x19)) := by
  have hsp := h.k.ng.sp
  have m := h.mem
  have e112 : (msp + 104 + 8 : Word) = msp + 112 := by decide
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b80000630_spec hpc trivial
  have k₁ := b80000630_keeps h₁
  have hm₁ := b80000630_mem_same h₁
  have hsp₁ : t₁.getReg .x2 = msp := (k₁ .x2 (by decide)).trans hsp
  have x10₁ : t₁.getReg .x10 = msp + 104 := by rw [b80000630_x10 h₁, hsp]
  have hheap₁ : HeapOk t₁ := ⟨by simp only [heapNext, hm₁]; exact h.k.ng.heap.lo,
    by simp only [heapNext, hm₁]; exact h.k.ng.heap.hi⟩
  have hb := h.k.hb
  have hlo := h.k.ng.heap.lo
  have hb0 := h.k.hb0
  have hl0 := h.k.a.inv.heap.lo
  simp only [heapNext, heapStart] at hb hlo hb0 hl0
  have pre : GrowOnePre 8 8 t₁ := {
    heap := hheap₁
    self := by rw [x10₁]; exact validRange_of (by decide) (by decide) (by decide)
    raw := by
      rw [x10₁]
      simp only [RawVecOk, Buf, vecPtr, vecCap, hm₁, e112]
      refine ⟨m.al, m.buf.imp_right fun hb' ↦ ⟨?_, ?_⟩⟩
      · simp only [heapStart]; omega
      · have := hb'.2; simp only [heapNext, hm₁] at this ⊢; exact this
    stack := rtStack_msp hsp₁ (by decide) (by decide)
    selfFree := by
      rw [x10₁]
      exact ⟨Or.inr (by simp only [heapEnd]; decide), by addr_omega []⟩
    selfStack := by rw [x10₁]; simp only [stackLo, hsp₁, growOneStack]; addr_omega [] }
  obtain ⟨v, rv, ⟨hpcv, hpv, post, hfresh⟩ | hd⟩ :=
    growOneFresh_8000d7bc.call r₁ (b80000630_pc h₁) pre
  swap
  · exact ⟨v, rv, Or.inl hd⟩
  have hpcv' : v.pc = 0x8000063c := by rw [hpcv, returnAddress, b80000630_x1 h₁]; decide
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b8000063c_spec hpcv' (by
    have : v.getReg .x2 = msp := (hpv.reg .x2).trans hsp₁
    rv_eval [this, msp]; decide)
  have k₂ := b8000063c_keeps h₂
  have hm₂ := b8000063c_mem_same h₂
  have hspv : v.getReg .x2 = msp := (hpv.reg .x2).trans hsp₁
  have hsp₂ : t₂.getReg .x2 = msp := (k₂ .x2 (by decide)).trans hspv
  have hhi := post.heap.hi
  have hmo := post.mono
  simp only [heapNext, heapEnd] at hhi hmo
  have pf := post.frame
  have pcap := post.cap
  have pby := post.bytes
  rw [x10₁] at pf pcap pby hfresh
  have hW : ∀ a, (Within a (msp + 104) 16 ∨ Within a (stackLo t₁ growOneStack) growOneStack ∨
      Within a nextAddr 8 ∨ Fresh t₁ v a) → WB (heapNext u₀) Hb a := by
    intro a ha
    rcases ha with ha | ha | ha | ⟨ha1, ha2⟩
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha])))
    · simp only [stackLo, hsp₁, growOneStack] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))))))
      · simp only [heapNext, hm₁] at ha1; omega
      · simp only [heapNext, heapEnd] at ha2 ⊢; omega
  have hf : BFrame t t₂ fun a ↦ Within a (msp + 104) 16 ∨
      Within a (stackLo t₁ growOneStack) growOneStack ∨ Within a nextAddr 8 ∨ Fresh t₁ v a :=
    fun a ha ↦ by
      rw [byteAt_eq, byteAt_eq, hm₂, ← hm₁, ← byteAt_eq, ← byteAt_eq]
      exact pf.byte a ha
  have hn₂ : heapNext t₂ = heapNext v := by simp only [heapNext, hm₂]
  have hheap₂ : HeapOk t₂ := ⟨by rw [hn₂]; exact post.heap.lo, by rw [hn₂]; exact post.heap.hi⟩
  have hmono₂ : heapNext t ≤ heapNext t₂ := by
    rw [hn₂]; simp only [heapNext] at hmo ⊢; rw [← hm₁]; exact hmo
  have k' := h.k.frame hf hW hsp₂ hheap₂ hmono₂
  have hH0 := h.k.hb0
  have hHb : Hb ≤ heapEnd := by
    have := h.k.ng.heap.hi; have := h.k.hb; simp only [heapNext, heapEnd] at *; omega
  obtain ⟨vecs, bufs⟩ := VecsAt.frame h.vecs h.bufs hf (fun a ha ↦ WB.vec hH0 hHb (hW a ha))
    (by simp only [heapEnd] at hHb ⊢; omega)
  -- what `grow_one` keeps and gives
  have hnt1 : (t₁.getMem nextAddr).toNat = (t.getMem nextAddr).toNat := by rw [hm₁]
  have hlow : ∀ a : Word, a.toNat < heapNext t → byteAt t₂ a = byteAt t a := fun a ha ↦ hf a fun hw ↦ by
    simp only [heapNext] at ha
    rcases hw with hw | hw | hw | ⟨hw1, _⟩
    · addr_omega [hw, ha, hhi, hmo, hnt1]
    · simp only [stackLo, hsp₁, growOneStack] at hw
      addr_omega [hw, ha, hhi, hmo, hnt1]
    · addr_omega [hw, ha, hhi, hmo, hnt1]
    · simp only [heapNext, hm₁] at hw1 ha; omega
  have R : ∀ r ∈ ([.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg),
      t₂.getReg r = t.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (k₂ _ (by decide)).trans ((hpv.reg _ (by decide)).trans (k₁ _ (by decide)))
  have hlen : g.2.2.length = (t.getMem (msp + 104)).toNat := by
    have := congrArg BitVec.toNat hfull
    rw [h.x18] at this
    have hc := m.cap
    rw [← this, BitVec.toNat_ofNat]
    omega
  have hSL := h.k.a.slots
  have hGO := h.k.a.groupOf
  have hn0 := h.k.hb0
  have hnt := h.k.hb
  simp only [heapNext, heapStart] at hSL hGO hn0 hnt
  have p112 : t₂.getMem (msp + 112) = vecPtr v (msp + 104) := by rw [hm₂, vecPtr, e112]
  have p104 : t₂.getMem (msp + 104) = vecCap v (msp + 104) := by rw [hm₂, vecCap]
  refine ⟨t₂, rv.trans r₂, Or.inr ⟨⟨k', vecs, bufs, ⟨fun j hj ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    h.hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, b8000063c_pc h₂, ?_,
    R .x19 (by decide)⟩⟩
  · have e1 : t₂.getHalfword (u₀.getReg .x8 + BitVec.ofNat 64 (4 * j)) =
        t.getHalfword (u₀.getReg .x8 + BitVec.ofNat 64 (4 * j)) :=
      getHalfword_eq_of_bytes (by addr_omega [hSL, hj]) (hlow _ (by addr_omega [hSL, hj, hGO, hn0, hnt]))
        (hlow _ (by addr_omega [hSL, hj, hGO, hn0, hnt]))
    have e2 : t₂.getHalfword (u₀.getReg .x8 + BitVec.ofNat 64 (4 * j) + 2) =
        t.getHalfword (u₀.getReg .x8 + BitVec.ofNat 64 (4 * j) + 2) :=
      getHalfword_eq_of_bytes (by addr_omega [hSL, hj]) (hlow _ (by addr_omega [hSL, hj, hGO, hn0, hnt]))
        (hlow _ (by addr_omega [hSL, hj, hGO, hn0, hnt]))
    rw [e1, e2]; exact m.slots j hj
  · rw [← m.groupOf]
    exact halvesAt_keep hGO.1 (fun a h1 h2 ↦ hlow a (by addr_omega [h1, h2, hGO, hn0, hnt]))
      (by addr_omega [hGO, hn0, hnt])
  · rw [← m.len]
    exact hf.getMem (by decide) fun j hj hw ↦ by
      rcases hw with hw | hw | hw | ⟨hw1, hw2⟩
      · addr_omega [hw, hj]
      · simp only [stackLo, hsp₁, growOneStack] at hw; addr_omega [hw, hj]
      · addr_omega [hw, hj]
      · simp only [heapNext] at hw2; addr_omega [hw2, hj, hhi]
  · rw [p104]
    have : (vecCap t₁ (msp + 104)).toNat = (t.getMem (msp + 104)).toNat := by rw [vecCap, hm₁]
    omega
  · rw [p112]; exact hfresh.1
  · rw [p112, p104, hn₂]
    rcases hfresh.2 with h0 | ⟨h1, h2⟩
    · exact Or.inl h0
    · right; simp only [heapNext, hm₁] at h1 h2 ⊢; omega
  · have hb8 : bytesAt v (vecPtr v (msp + 104)) (8 * g.2.2.length) =
        bytesAt t₁ (vecPtr t₁ (msp + 104)) (8 * g.2.2.length) := by
      have e : (vecCap t₁ (msp + 104)).toNat * 8 = 8 * g.2.2.length := by
        rw [vecCap, hm₁, hlen, Nat.mul_comm]
      rw [← e]; exact pby
    have hp1 : vecPtr t₁ (msp + 104) = t.getMem (msp + 112) := by rw [vecPtr, hm₁, e112]
    rw [p112, rwords_same hm₂, readWords_eq_of_bytesAt hb8 hfresh.1 (by rw [hp1]; exact m.al),
      hp1, rwords_same hm₁]
    exact m.dist
  · exact (R .x8 (by decide)).trans h.x8
  · exact (R .x9 (by decide)).trans h.x9
  · rw [b8000063c_x10 h₂, hspv, hm₂]
  · rw [b8000063c_x15 h₂, hspv, ← hm₂]; exact k'.bm.m64
  · rw [b8000063c_x16 h₂, hpv.reg .x23, k₁ .x23 (by decide)]; exact h.x23
  · exact (R .x18 (by decide)).trans h.x18
  · exact (R .x20 (by decide)).trans h.x20
  · exact (R .x21 (by decide)).trans h.x21
  · exact (R .x22 (by decide)).trans h.x22
  · exact (R .x23 (by decide)).trans h.x23
  · exact (R .x24 (by decide)).trans h.x24
  · exact (R .x25 (by decide)).trans h.x25
  · exact (R .x26 (by decide)).trans h.x26
  · exact (R .x27 (by decide)).trans h.x27
  · rw [p104]
    have : (vecCap t₁ (msp + 104)).toNat = (t.getMem (msp + 104)).toNat := by rw [vecCap, hm₁]
    omega

end

theorem rw_snoc {t v : MachineState} {D w : Word} {n : Nat}
    (hk : ∀ j < n, v.getMem (D + BitVec.ofNat 64 (8 * j)) = t.getMem (D + BitVec.ofNat 64 (8 * j)))
    (hl : v.getMem (D + BitVec.ofNat 64 (8 * n)) = w) :
    v.readWords D (n + 1) = t.readWords D n ++ [w] := by
  rw [readWords_eq_map, readWords_eq_map, List.range_succ, List.map_append, List.map_singleton, hl]
  congr 1
  exact List.map_congr_left fun j hj ↦ hk j (List.mem_range.mp hj)

section
variable {s u₀ t : MachineState} {words : List Word} {i L Hb q : Nat} {st : Model.NewState}
  {g : GrpSt}

/-- `0x8000057c`: the word pushed onto `distinct`, its index in `a1`. -/
theorem push_57c (h : GS s words u₀ i L Hb st q g t) (hpc : t.pc = 0x8000057c)
    (hroom : g.2.2.length < (t.getMem (msp + 104)).toNat) :
    ∃ v, Reaches Image.code t v ∧ GS s words u₀ i L Hb st q (g.1, g.2.1, g.2.2 ++ [t.getReg .x19]) v ∧
      v.pc = 0x80000594 ∧ v.getReg .x11 = BitVec.ofNat 64 g.2.2.length := by
  have hsp := h.k.ng.sp
  have m := h.mem
  set D := t.getMem (msp + 112) with hD
  have hbuf : Hb ≤ D.toNat ∧ D.toNat + (t.getMem (msp + 104)).toNat * 8 ≤ heapNext t := by
    rcases m.buf with h0 | h0
    · omega
    · exact h0
  have hhi := h.k.ng.heap.hi
  have hH0 := h.k.hb0
  have hl0 := h.k.a.inv.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hbuf hhi hH0 hl0
  have hP : (D + BitVec.ofNat 64 g.2.2.length * 8).toNat = D.toNat + 8 * g.2.2.length := by addr_omega [hbuf, hhi, hroom]
  have hal : D.toNat % 8 = 0 := m.al
  have hx10 := h.x10
  have hx18 := h.x18
  obtain ⟨v, rv, hv⟩ := Sym.BlockSpec.reaches b8000057c_spec hpc (by
    rv_eval []
    rw [hsp, hx10, hx18, ← hD]
    refine ⟨by decide, (Sym.validAccess_eight _).mpr ⟨Or.inl ⟨by omega, by omega⟩, by omega⟩,
      fun he ↦ ?_⟩
    have := congrArg BitVec.toNat he
    addr_omega [this, hP, hhi, hbuf, hroom])
  have kv := b8000057c_keeps hv
  have hspv : v.getReg .x2 = msp := (kv .x2 (by decide)).trans hsp
  have hf : BFrame t v fun a ↦ Within a (msp + 120) 8 ∨
      Within a (D + BitVec.ofNat 64 g.2.2.length * 8) 8 := by
    refine (holds_bframe hv ?_).mono fun a ha ↦ ?_
    · intro k hk
      simp only [b8000057c, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · rv_eval []; rw [hsp]; decide
      · rv_eval []; rw [hx10, hx18, ← hD, hP]; omega
    · simp only [b8000057c, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
        exists_eq_left] at ha
      rv_eval [] at ha
      rw [hsp, hx10, hx18, ← hD] at ha
      exact ha
  have hHb : Hb ≤ heapEnd := by have := h.k.hb; simp only [heapNext, heapEnd] at *; omega
  simp only [heapEnd] at hHb
  have hlow : ∀ a : Word, a.toNat < Hb → byteAt v a = byteAt t a := fun a ha ↦ hf a fun hw ↦ by
    rcases hw with hw | hw
    · addr_omega [hw, ha, hHb]
    · addr_omega [hw, ha, hP, hbuf]
  have hnv : heapNext v = heapNext t := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (hf.getMem (a := nextAddr) (by decide) fun j hj hw ↦ by
      rcases hw with hw | hw
      · addr_omega [hw, hj]
      · addr_omega [hw, hj, hP, hbuf, hhi, hroom])
  have hW : ∀ a, (Within a (msp + 120) 8 ∨ Within a (D + BitVec.ofNat 64 g.2.2.length * 8) 8) →
      WB (heapNext u₀) Hb a := by
    intro a ha
    rcases ha with ha | ha
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha])))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))))))
      · addr_omega [ha, hP, hbuf, hhi, hroom]
      · simp only [heapEnd]; addr_omega [ha, hP, hbuf, hhi, hroom]
  have hheap : HeapOk v := ⟨by rw [hnv]; exact h.k.ng.heap.lo, by rw [hnv]; exact h.k.ng.heap.hi⟩
  have k' := h.k.frame hf hW hspv hheap (le_of_eq hnv.symm)
  obtain ⟨vecs, bufs⟩ := VecsAt.frame h.vecs h.bufs hf (fun a ha ↦ WB.vec h.k.hb0 (by
    simp only [heapEnd]; exact hHb) (hW a ha)) (by simp only [heapEnd]; exact hHb)
  have K : ∀ c : Nat, c % 8 = 0 → (104 ≤ c ∧ c + 8 ≤ 120) →
      v.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) := by
    intro c h8 hc
    refine hf.getMem (by addr_omega [h8, hc]) fun j hj hw ↦ ?_
    rcases hw with hw | hw
    · addr_omega [hw, hj, hc]
    · addr_omega [hw, hj, hc, hP, hbuf, hhi, hroom]
  have v104 : v.getMem (msp + 104) = t.getMem (msp + 104) := K 104 (by decide) (by decide)
  have v112 : v.getMem (msp + 112) = D := K 112 (by decide) (by decide)
  have hSL := h.k.a.slots
  have hGO := h.k.a.groupOf
  simp only [heapStart] at hSL
  simp only [heapNext] at hGO
  refine ⟨v, rv, ⟨k', vecs, bufs, ⟨fun j hj ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, h.hq, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, b8000057c_pc hv, by rw [b8000057c_x11 hv, hx18]⟩
  · have e1 : v.getHalfword (u₀.getReg .x8 + BitVec.ofNat 64 (4 * j)) =
        t.getHalfword (u₀.getReg .x8 + BitVec.ofNat 64 (4 * j)) :=
      getHalfword_eq_of_bytes (by addr_omega [hSL, hj]) (hlow _ (by addr_omega [hSL, hj, hGO, hH0]))
        (hlow _ (by addr_omega [hSL, hj, hGO, hH0]))
    have e2 : v.getHalfword (u₀.getReg .x8 + BitVec.ofNat 64 (4 * j) + 2) =
        t.getHalfword (u₀.getReg .x8 + BitVec.ofNat 64 (4 * j) + 2) :=
      getHalfword_eq_of_bytes (by addr_omega [hSL, hj]) (hlow _ (by addr_omega [hSL, hj, hGO, hH0]))
        (hlow _ (by addr_omega [hSL, hj, hGO, hH0]))
    rw [e1, e2]; exact m.slots j hj
  · rw [← m.groupOf]
    exact halvesAt_keep hGO.1 (fun a h1 h2 ↦ hlow a (by addr_omega [h1, h2, hGO, hH0]))
      (by addr_omega [hGO, hH0, hhi])
  · have e := b8000057c_m_x2_120 hv
    rw [hsp, hx18] at e
    rw [e, List.length_append, List.length_singleton, BitVec.ofNat_add]
    rfl
  · rw [v104, List.length_append, List.length_singleton]; omega
  · rw [v112]; exact hal
  · rw [v112, v104, hnv]; exact m.buf
  · rw [v112, List.length_append, List.length_singleton]
    have hk : ∀ j < g.2.2.length, v.getMem (D + BitVec.ofNat 64 (8 * j)) =
        t.getMem (D + BitVec.ofNat 64 (8 * j)) := by
      intro j hj
      refine hf.getMem (by addr_omega [hal, hj, hbuf, hroom, hhi]) fun k hk hw ↦ ?_
      rcases hw with hw | hw
      · addr_omega [hw, hk, hj, hbuf, hroom, hhi]
      · addr_omega [hw, hk, hj, hP, hbuf, hroom, hhi]
    rw [rw_snoc (t := t) hk ?_, show t.readWords D g.2.2.length = g.2.2 from m.dist]
    · have e := b8000057c_m1 hv
      rw [hx10, hx18, ← hD] at e
      rw [← e]
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [hP]
      addr_omega [hbuf, hroom, hhi]
  · exact (kv .x8 (by decide)).trans h.x8
  · exact (kv .x9 (by decide)).trans h.x9
  · rw [kv .x10 (by decide), v112]; exact hx10
  · exact (kv .x15 (by decide)).trans h.x15
  · exact (kv .x16 (by decide)).trans h.x16
  · rw [b8000057c_x18 hv, hx18, List.length_append, List.length_singleton, BitVec.ofNat_add]
    rfl
  · exact (kv .x20 (by decide)).trans h.x20
  · exact (kv .x21 (by decide)).trans h.x21
  · exact (kv .x22 (by decide)).trans h.x22
  · exact (kv .x23 (by decide)).trans h.x23
  · exact (kv .x24 (by decide)).trans h.x24
  · exact (kv .x25 (by decide)).trans h.x25
  · exact (kv .x26 (by decide)).trans h.x26
  · exact (kv .x27 (by decide)).trans h.x27

end

/-- `0x800005f8`'s wrap of the next slot. -/
theorem wrap_slot {j : Nat} (hj : j < 2 ^ 15) :
    ((if BitVec.ult ((BitVec.ofNat 64 j + 1) ^^^ 32768) 1 then (1 : Word) else 0) - 1) &&&
      (BitVec.ofNat 64 j + 1) = BitVec.ofNat 64 ((j + 1) % 2 ^ 15) := by
  by_cases e : j + 1 = 2 ^ 15
  · obtain rfl : j = 32767 := by omega
    decide
  · have h1 : BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) := by
      apply BitVec.eq_of_toNat_eq; simp
    have h2 : BitVec.ult (BitVec.ofNat 64 (j + 1) ^^^ 32768) 1 = false := by
      have hne : BitVec.ofNat 64 (j + 1) ^^^ 32768 ≠ 0#64 := fun h0 ↦ by
        have := congrArg BitVec.toNat (BitVec.xor_eq_zero_iff.mp h0)
        simp at this; omega
      simp only [BitVec.ult, decide_eq_false_iff_not, Nat.not_lt]
      have : (BitVec.ofNat 64 (j + 1) ^^^ 32768).toNat ≠ 0 := fun h0 ↦
        hne (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
      have h1' : (1 : Word).toNat = 1 := rfl
      omega
    rw [h1, h2, Nat.mod_eq_of_lt (by omega)]
    exact BitVec.allOnes_and

end Rv64Verifier.Proofs.Main
