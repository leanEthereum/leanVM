import Rv64Verifier.Proofs.Main.NewBytes
import Rv64Verifier.Proofs.Main.NewLoop

/-!
# `Bytecode::new`'s blocks: the `Block` pushed

`blockNew_eq`: `blockNewRust`'s nonempty branch is the folds the machine follows (`cfold`,
`rfold`, `pfold`, `ufold`). `push_head`: `0x800009c8` makes room in `blocks` (`grow_one` at
`0x80011c78` if full); `push_store`: `0x800004d0` stores the `Block`, to `BE` at `0x80000510`.
`blockFull`: a block with a nonzero word, the count to the `Block`; `newStage`: `Bytecode::new`.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.Bytecode
  Rv64Verifier.Blocks.F3

/-- `newRust`'s state after block `i` with a nonzero word. -/
def stNew (words : List Word) (i L : Nat) (g : GrpSt) (st : Model.NewState) : Model.NewState :=
  { blocks := st.blocks ++ [⟨i, (rfold words i L g st g.2.2.length).2.2.length,
      (ufold g st g.2.2.length).2.length⟩],
    words := (rfold words i L g st g.2.2.length).2.2,
    positions := (pfold words i L g st L).1,
    bytes := (ufold g st g.2.2.length).2,
    slots := g.1,
    groupOf := g.2.1 }

theorem blockNew_eq {words : List Word} {i L : Nat} {g : GrpSt} {st : Model.NewState}
    (hfold : foldNew (tbl words) i = some st)
    (hg : Model.groupRust (blk words i) st.slots st.groupOf = some g) (hne : g.2.2 ≠ [])
    (hbl : (blk words i).length = L) :
    foldNew (tbl words) (i + 1) = some (stNew words i L g st) := by
  rw [foldNew_succ, hfold, Option.bind_some]
  unfold Model.blockNewRust
  rw [show ((tbl words).drop (i * 2 ^ 14)).take (2 ^ 14) = blk words i from rfl]
  dsimp only
  rw [hg]
  have he : g.2.2.isEmpty = false := by
    cases h : g.2.2 with
    | nil => exact absurd h hne
    | cons _ _ => rfl
  simp only [Option.map_some, he, Bool.false_eq_true, ↓reduceIte, hbl]
  have hc : (List.range L).foldl (Model.countStep (blk words i) g.2.1)
      (List.replicate g.2.2.length 0) = cfold words i g L := rfl
  rw [hc, runs_rfold, ← ufold_all]
  rfl

/-- `n` `Block`s from two byte ranges with equal bytes, both aligned. -/
theorem blocksAt_of_bytes {t s : MachineState} {a b : Word} {n m : Nat}
    (h : bytesAt t a m = bytesAt s b m) (hm : n * 24 ≤ m) (ha : a.toNat % 8 = 0)
    (hb : b.toNat % 8 = 0) : blocksAt t a n = blocksAt s b n := by
  have e : ∀ (x : Word) (j c : Nat), x + BitVec.ofNat 64 (24 * j) + BitVec.ofNat 64 c =
      x + BitVec.ofNat 64 (24 * j + c) := fun x j c ↦ by rw [BitVec.ofNat_add, BitVec.add_assoc]
  unfold blocksAt
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_range] at hj
  have e8 : ∀ x : Word, x + BitVec.ofNat 64 (24 * j) + 8 = x + BitVec.ofNat 64 (24 * j + 8) :=
    fun x ↦ e x j 8
  have e16 : ∀ x : Word, x + BitVec.ofNat 64 (24 * j) + 16 = x + BitVec.ofNat 64 (24 * j + 16) :=
    fun x ↦ e x j 16
  rw [e8, e8, e16, e16, getMem_eq_of_bytesAt h ha hb (k := 24 * j) (by omega) (by omega),
    getMem_eq_of_bytesAt h ha hb (k := 24 * j + 8) (by omega) (by omega),
    getMem_eq_of_bytesAt h ha hb (k := 24 * j + 16) (by omega) (by omega)]

/-- At `0x800004d0`, room in `blocks`: `s2` `bytes`' length, `s3` `blocks`'. -/
structure PS (s : MachineState) (words : List Word) (u₀ : MachineState) (i L Hb : Nat)
    (st : Model.NewState) (g : GrpSt) (D C : Word) (H1 U : Nat) (t : MachineState) : Prop where
  rc : RC s words u₀ i L Hb st g D C H1 t
  m24 : t.getMem (msp + 24) = BitVec.ofNat 64 ((words.getD 0 0).toNat - 2 ^ 14 * i - L)
  vs : VS u₀ Hb H1 U 2048 { { { st with words := (rfold words i L g st g.2.2.length).2.2 } with
    positions := (pfold words i L g st L).1 } with bytes := (ufold g st g.2.2.length).2 } t
  x8 : t.getReg .x8 = u₀.getReg .x8
  x9 : t.getReg .x9 = BitVec.ofNat 64 (rfold words i L g st g.2.2.length).2.2.length
  x27 : t.getReg .x27 = 1
  room : (vecLen t (msp + 400)).toNat < (vecCap t (msp + 400)).toNat
  x18 : t.getReg .x18 = vecLen t (msp + 240)
  x19 : t.getReg .x19 = vecLen t (msp + 400)

section
variable {s u₀ t : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C : Word} {H1 U : Nat}

/-- `0x800009c8`: room made in `blocks`, `grow_one` if full. -/
theorem push_head (h : BO s words u₀ i L Hb st g D C H1 U g.2.2.length t) (hpc : t.pc = 0x800009c8) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
      (v.pc = 0x800004d0 ∧ PS s words u₀ i L Hb st g D C H1 U v)) := by
  have ub := h.ub
  have hsp := ub.rc.k.ng.sp
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b800009c8_spec hpc (by rv_eval [hsp, msp]; decide)
  have k₁ := b800009c8_keeps h₁
  have hm₁ := b800009c8_mem_same h₁
  have hn₁ : heapNext t₁ = heapNext t := by simp only [heapNext, hm₁]
  have hhi := ub.rc.k.ng.heap.hi
  have hf₁ : BFrame t t₁ (fun _ ↦ False) := BFrame.of_same hm₁ _
  have hsp₁ : t₁.getReg .x2 = msp := (k₁ .x2 (by decide)).trans hsp
  have rc₁ := ub.rc.frame hf₁ (fun _ h ↦ h.elim) hsp₁ ⟨by rw [hn₁]; exact ub.rc.k.ng.heap.lo,
    by rw [hn₁]; exact hhi⟩ (le_of_eq hn₁.symm)
  have vs₁ := ub.vs.frame hf₁ (fun _ h ↦ h.elim) (le_of_eq hn₁.symm) (by rw [hn₁]; exact hhi)
  have x18₁ : t₁.getReg .x18 = vecLen t₁ (msp + 240) := by
    rw [b800009c8_x18 h₁, hsp]; exact (hm₁ _).symm
  have x19₁ : t₁.getReg .x19 = vecLen t₁ (msp + 400) := by
    rw [b800009c8_x19 h₁, hsp]; exact (hm₁ _).symm
  have hlc := vs₁.bufs.b.len
  by_cases hfull : vecLen t (msp + 400) = vecCap t (msp + 400)
  swap
  · refine ⟨t₁, r₁, Or.inr ⟨b800009c8_pc_taken h₁ (by rw [hsp]; exact hfull), rc₁,
      by rw [hm₁]; exact ub.m24, vs₁, (k₁ .x8 (by decide)).trans ub.x8, (k₁ .x9 (by decide)).trans ub.x9,
      (k₁ .x27 (by decide)).trans ub.x27, ?_, x18₁, x19₁⟩⟩
    have e1 : vecLen t₁ (msp + 400) = vecLen t (msp + 400) := hm₁ _
    have e2 : vecCap t₁ (msp + 400) = vecCap t (msp + 400) := hm₁ _
    rw [e1, e2] at hlc ⊢
    exact lt_of_le_of_ne hlc fun e ↦ hfull (BitVec.eq_of_toNat_eq e)
  -- `0x800009d8`: `grow_one`
  have hpc₁ := b800009c8_pc_not_taken h₁ (by rw [hsp]; exact hfull)
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b800009d8_spec hpc₁ trivial
  have k₂ := b800009d8_keeps h₂
  have hm₂ := b800009d8_mem_same h₂
  have hsp₂ : t₂.getReg .x2 = msp := (k₂ .x2 (by decide)).trans hsp₁
  have x10₂ : t₂.getReg .x10 = msp + 400 := by rw [b800009d8_x10 h₂, hsp₁]
  have hn₂ : heapNext t₂ = heapNext t₁ := by simp only [heapNext, hm₂]
  have p2 : vecPtr t₂ (msp + 400) = vecPtr t₁ (msp + 400) := hm₂ _
  have c2 : vecCap t₂ (msp + 400) = vecCap t₁ (msp + 400) := hm₂ _
  have bb := vs₁.bufs.b
  have pre : GrowOnePre 24 8 t₂ := {
    heap := ⟨by rw [hn₂]; exact rc₁.k.ng.heap.lo, by rw [hn₂]; exact rc₁.k.ng.heap.hi⟩
    self := by rw [x10₂]; exact validRange_of (by decide) (by decide) (by decide)
    raw := by
      rw [x10₂]
      simp only [RawVecOk, Buf, p2, c2]
      refine ⟨bb.al, bb.buf.imp_right fun hb' ↦ ⟨?_, ?_⟩⟩
      · have := rc₁.k.a.inv.heap.lo
        simp only [heapStart, heapNext] at hb' this ⊢; omega
      · rw [hn₂]; exact hb'.2
    stack := rtStack_msp hsp₂ (by decide) (by decide)
    selfFree := by
      rw [x10₂]
      exact ⟨Or.inr (by simp only [heapEnd]; decide), by addr_omega []⟩
    selfStack := by rw [x10₂]; simp only [stackLo, hsp₂, growOneStack]; addr_omega [] }
  obtain ⟨t₃, r₃, ⟨hpc₃, hpv, post, hfresh⟩ | hd⟩ :=
    growOneFresh_80011c78.call r₂ (b800009d8_pc h₂) pre
  swap
  · exact ⟨t₃, r₁.trans r₃, Or.inl hd⟩
  have hpc₃' : t₃.pc = 0x800009e4 := by rw [hpc₃, returnAddress, b800009d8_x1 h₂]; decide
  have hsp₃ : t₃.getReg .x2 = msp := (hpv.reg .x2).trans hsp₂
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b800009e4_spec hpc₃' trivial
  have k₄ := b800009e4_keeps h₄
  have hm₄ := b800009e4_mem_same h₄
  have hsp₄ : t₄.getReg .x2 = msp := (k₄ .x2 (by decide)).trans hsp₃
  have pf := post.frame
  have pcap := post.cap
  have pby := post.bytes
  rw [x10₂] at pf pcap pby hfresh
  have hhi₃ := post.heap.hi
  simp only [heapNext, heapEnd] at hhi₃
  have hf : BFrame t₁ t₄ fun a ↦ Within a (msp + 400) 16 ∨
      Within a (stackLo t₂ growOneStack) growOneStack ∨ Within a nextAddr 8 ∨ Fresh t₂ t₃ a :=
    fun a ha ↦ by
      rw [byteAt_eq, byteAt_eq, hm₄, ← hm₂, ← byteAt_eq, ← byteAt_eq]
      exact pf.byte a ha
  have hn₄ : heapNext t₄ = heapNext t₃ := by simp only [heapNext, hm₄]
  have hheap₄ : HeapOk t₄ := ⟨by rw [hn₄]; exact post.heap.lo, by rw [hn₄]; exact post.heap.hi⟩
  have hmono : heapNext t₁ ≤ heapNext t₄ := by rw [hn₄, ← hn₂]; exact post.mono
  have hhi1 := rc₁.k.ng.heap.hi
  have hdc := rc₁.dc
  have hchi := rc₁.chi
  have hh1 := rc₁.h1
  have hmo0 := rc₁.k.ng.mono
  simp only [heapNext, heapEnd] at hhi1 hh1 hmo0
  have hn21 := hn₂
  simp only [heapNext] at hn21
  have hW : ∀ a, (Within a (msp + 400) 16 ∨ Within a (stackLo t₂ growOneStack) growOneStack ∨
      Within a nextAddr 8 ∨ Fresh t₂ t₃ a) →
      Wr (heapNext u₀) D C g.2.2.length a ∧
        ¬ Within a (msp + 424) 24 ∧ ¬ Within a (msp + 448) 24 ∧ ¬ Within a (msp + 240) 24 ∧
        (a.toNat < heapNext u₀ ∨ heapNext t₁ ≤ a.toNat ∨ (Hb ≤ a.toNat ∧ a.toNat < H1) ∨
          (U ≤ a.toNat ∧ a.toNat < U + 2048) ∨
          Within a (vecPtr t₁ (msp + 400)) ((vecCap t₁ (msp + 400)).toNat * 24)) := by
    intro a ha
    simp only [heapNext]
    rcases ha with ha | ha | ha | ⟨ha1, ha2⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha])))), by addr_omega [ha],
        by addr_omega [ha], by addr_omega [ha], Or.inr (Or.inl (by addr_omega [ha, hhi1]))⟩
    · simp only [stackLo, hsp₂, growOneStack] at ha
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha]))))), by addr_omega [ha],
        by addr_omega [ha], by addr_omega [ha], Or.inr (Or.inl (by addr_omega [ha, hhi1]))⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))), by addr_omega [ha],
        by addr_omega [ha], by addr_omega [ha], Or.inr (Or.inl (by addr_omega [ha, hhi1]))⟩
    · simp only [heapNext] at ha1 ha2
      rw [hn21] at ha1
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by simp only [heapEnd]; omega,
        fun h' ↦ by addr_omega [h', ha1, hdc, hchi, hh1],
        fun h' ↦ by addr_omega [h', ha1, hchi, hh1]⟩))))),
        by addr_omega [ha2, hhi₃], by addr_omega [ha2, hhi₃], by addr_omega [ha2, hhi₃],
        Or.inr (Or.inl ha1)⟩
  have hK4 : ∀ c' : Nat, c' % 8 = 0 → c' < 4096 → (c' + 8 ≤ 400 ∨ 416 ≤ c') →
      t₄.getMem (msp + BitVec.ofNat 64 c') = t₁.getMem (msp + BitVec.ofNat 64 c') := fun c' h8 hc' hr ↦
    hf.getMem (by addr_omega [h8, hc']) fun j hj hw ↦ by
      rcases hw with hw | hw | hw | ⟨hw1, hw2⟩
      · rcases hr with hr | hr <;> addr_omega [hw, hj, hc', hr]
      · simp only [stackLo, hsp₂, growOneStack] at hw; addr_omega [hw, hj, hc']
      · addr_omega [hw, hj, hc']
      · simp only [heapNext] at hw2; addr_omega [hw2, hj, hc', hhi₃]
  have l4 : vecLen t₄ (msp + 400) = vecLen t₁ (msp + 400) := hK4 416 (by decide) (by decide) (by omega)
  have p4 : vecPtr t₄ (msp + 400) = vecPtr t₃ (msp + 400) := hm₄ _
  have c4 : vecCap t₄ (msp + 400) = vecCap t₃ (msp + 400) := hm₄ _
  rw [c2] at pcap
  rw [p2, c2] at pby
  have l1t : vecLen t₁ (msp + 400) = vecLen t (msp + 400) := hm₁ _
  have c1t : vecCap t₁ (msp + 400) = vecCap t (msp + 400) := hm₁ _
  have hlc' : (vecLen t₁ (msp + 400)).toNat = (vecCap t₁ (msp + 400)).toNat := by rw [l1t, c1t, hfull]
  have hroom : (vecLen t₄ (msp + 400)).toNat < (vecCap t₄ (msp + 400)).toNat := by
    rw [l4, c4]; omega
  have hn32 : heapNext t₂ = heapNext t₁ := hn₂
  have hU2 := ub.hU2
  have hU1 := ub.hU1
  rw [← hn₁] at hU2
  simp only [heapNext] at hU2
  have hb' := vs₁.vecs.blocks
  simp only at hb'
  have hin : VecIn t₄ (msp + 400) 24 8 (heapNext u₀) (heapNext t₄) := by
    refine ⟨le_of_lt hroom, by rw [p4]; exact hfresh.1, ?_, fun h0 ↦ absurd h0 (by omega)⟩
    rw [p4, c4, hn₄]
    rcases hfresh.2 with h0 | ⟨h1, h2⟩
    · exact Or.inl h0
    · right; rw [hn32] at h1; simp only [heapNext] at h1 h2 ⊢; omega
  have vs₄ := vs₁.setB (l := st.blocks) hf (fun a ha ↦ (hW a ha).2) hmono hheap₄.hi hin
    (by
      simp only [VMiss, p4, c4]
      rcases hfresh.2 with h0 | ⟨h1, _⟩
      · exact ⟨Or.inl h0, Or.inl h0⟩
      · rw [hn32] at h1
        simp only [heapNext] at h1
        exact ⟨Or.inr (Or.inr (Or.inl (by omega))), Or.inr (Or.inr (Or.inl (by omega)))⟩)
    (by
      rw [p4, c4]
      rcases hfresh.2 with h0 | ⟨h1, _⟩
      · exact Or.inr (Or.inl h0)
      · rw [hn32] at h1; exact Or.inr (Or.inr h1))
    (by
      rw [p4, l4]
      have e1 : blocksAt t₄ (vecPtr t₃ (msp + 400)) (vecLen t₁ (msp + 400)).toNat =
          blocksAt t₃ (vecPtr t₃ (msp + 400)) (vecLen t₁ (msp + 400)).toNat := by
        simp only [blocksAt, hm₄]
      have e2 : blocksAt t₂ (vecPtr t₁ (msp + 400)) (vecLen t₁ (msp + 400)).toNat =
          blocksAt t₁ (vecPtr t₁ (msp + 400)) (vecLen t₁ (msp + 400)).toNat := by
        simp only [blocksAt, hm₂]
      rw [e1, blocksAt_of_bytes pby (by omega) hfresh.1 bb.al, e2, hb'])
  have R : ∀ r ∈ ([.x8, .x9, .x18, .x19, .x27] : List Reg), t₄.getReg r = t₁.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact (k₄ _ (by decide)).trans ((hpv.reg _ (by decide)).trans (k₂ _ (by decide)))
  refine ⟨t₄, r₁.trans (r₃.trans r₄), Or.inr ⟨b800009e4_pc h₄,
    rc₁.frame hf (fun a ha ↦ (hW a ha).1) hsp₄ hheap₄ hmono,
    (hK4 24 (by decide) (by decide) (by omega)).trans (by rw [hm₁]; exact ub.m24), vs₄,
    by rw [R .x8 (by simp), k₁ .x8 (by decide)]; exact ub.x8,
    by rw [R .x9 (by simp), k₁ .x9 (by decide)]; exact ub.x9,
    by rw [R .x27 (by simp), k₁ .x27 (by decide)]; exact ub.x27, hroom, ?_, ?_⟩⟩
  · rw [R .x18 (by simp), x18₁]
    exact (hK4 256 (by decide) (by decide) (by omega)).symm
  · rw [R .x19 (by simp), x19₁, l4]

end

/-- `n` `Block`s from `p` and one more. -/
theorem blocksAt_snoc {t t' : MachineState} {p : Word} {n : Nat} {x y z : Word}
    (hk : ∀ j < n, t'.getMem (p + BitVec.ofNat 64 (24 * j)) = t.getMem (p + BitVec.ofNat 64 (24 * j)) ∧
      t'.getMem (p + BitVec.ofNat 64 (24 * j) + 8) = t.getMem (p + BitVec.ofNat 64 (24 * j) + 8) ∧
      t'.getMem (p + BitVec.ofNat 64 (24 * j) + 16) = t.getMem (p + BitVec.ofNat 64 (24 * j) + 16))
    (h0 : t'.getMem (p + BitVec.ofNat 64 (24 * n)) = x)
    (h1 : t'.getMem (p + BitVec.ofNat 64 (24 * n) + 8) = y)
    (h2 : t'.getMem (p + BitVec.ofNat 64 (24 * n) + 16) = z) :
    blocksAt t' p (n + 1) = blocksAt t p n ++ [⟨x.toNat, y.toNat, z.toNat⟩] := by
  unfold blocksAt
  rw [List.range_succ, List.map_append, List.map_singleton, h0, h1, h2]
  congr 1
  apply List.map_congr_left
  intro j hj
  obtain ⟨e0, e1, e2⟩ := hk j (List.mem_range.mp hj)
  rw [e0, e1, e2]

section
variable {s u₀ t : MachineState} {words : List Word} {i L Hb : Nat} {st : Model.NewState}
  {g : GrpSt} {D C : Word} {H1 U : Nat}

/-- `0x800004d0`: the `Block` stored, to `0x80000510`. -/
theorem push_store (h : PS s words u₀ i L Hb st g D C H1 U t) (hpc : t.pc = 0x800004d0)
    (hg : Model.groupRust (blk words i) st.slots st.groupOf = some g) (hsl : g.1.length = 2 ^ 15)
    (hbl : (blk words i).length = L) :
    ∃ v, Reaches Image.code t v ∧ BE s words u₀ i L (stNew words i L g st) v := by
  have rc := h.rc
  have hsp := rc.k.ng.sp
  have hhi := rc.k.ng.heap.hi
  simp only [heapNext, heapEnd] at hhi
  have bb := h.vs.bufs.b
  have mb := h.vs.mb
  have hroom := h.room
  have hm24 : (vecLen t (msp + 400)).toNat * 24 + 24 ≤ (vecCap t (msp + 400)).toNat * 24 := by omega
  obtain ⟨hP1, hP2⟩ := bb.buf.resolve_left (by omega)
  simp only [heapNext] at hP1 hP2
  have hpal := bb.al
  have hP : vecPtr t (msp + 400) = t.getMem (msp + 408) := rfl
  rw [hP] at hP1 hP2 hpal
  simp only [VMiss, Out] at mb
  rw [hP] at mb
  have hEe : t.getMem (msp + 408) + (vecLen t (msp + 400) * 16 + vecLen t (msp + 400) * 8) =
      t.getMem (msp + 408) + BitVec.ofNat 64 (24 * (vecLen t (msp + 400)).toNat) := by
    apply BitVec.eq_of_toNat_eq
    addr_omega [hP2, hm24, hhi]
  have hE : (t.getMem (msp + 408) + BitVec.ofNat 64 (24 * (vecLen t (msp + 400)).toNat)).toNat =
      (t.getMem (msp + 408)).toNat + 24 * (vecLen t (msp + 400)).toNat := by
    addr_omega [hP2, hm24, hhi]
  obtain ⟨v, rv, hv⟩ := Sym.BlockSpec.reaches b800004d0_spec hpc (by
    rv_eval []
    simp only [hsp, h.x19, hEe]
    and_intros
    all_goals first
      | decide
      | (refine (Sym.validAccess_eight _).mpr ⟨Or.inl ⟨?_, ?_⟩, ?_⟩ <;>
          addr_omega [hE, hP1, hP2, hm24, hhi, hpal, rc.k.a.inv.heap.lo])
      | (intro e; have := congrArg BitVec.toNat e; addr_omega [this, hE, hP2, hm24, hhi]))
  have kv := b800004d0_keeps hv
  have hspv : v.getReg .x2 = msp := (kv .x2 (by decide)).trans hsp
  have hf : BFrame t v fun a ↦ Within a (msp + 416) 8 ∨
      Within a (t.getMem (msp + 408) + BitVec.ofNat 64 (24 * (vecLen t (msp + 400)).toNat) + 16) 8 ∨
      Within a (t.getMem (msp + 408) + BitVec.ofNat 64 (24 * (vecLen t (msp + 400)).toNat) + 8) 8 ∨
      Within a (t.getMem (msp + 408) + BitVec.ofNat 64 (24 * (vecLen t (msp + 400)).toNat)) 8 := by
    refine (holds_bframe hv ?_).mono fun a ha ↦ ?_
    · intro w hw
      simp only [b800004d0, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · rv_eval []; rw [hsp]; decide
      · rv_eval []; rw [hsp, h.x19, hEe]; addr_omega [hE, hpal, hP2, hm24, hhi]
      · rv_eval []; rw [hsp, h.x19, hEe]; addr_omega [hE, hpal, hP2, hm24, hhi]
      · rv_eval []; rw [hsp, h.x19, hEe]; addr_omega [hE, hpal, hP2, hm24, hhi]
    · simp only [b800004d0, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
        exists_eq_left] at ha
      rv_eval [] at ha
      rw [hsp, h.x19, hEe] at ha
      exact ha
  have hdc := rc.dc
  have hchi := rc.chi
  have hdlo := rc.dlo
  have hh1 := rc.h1
  simp only [heapNext] at hh1
  have hW : ∀ a, (Within a (msp + 416) 8 ∨
      Within a (t.getMem (msp + 408) + BitVec.ofNat 64 (24 * (vecLen t (msp + 400)).toNat) + 16) 8 ∨
      Within a (t.getMem (msp + 408) + BitVec.ofNat 64 (24 * (vecLen t (msp + 400)).toNat) + 8) 8 ∨
      Within a (t.getMem (msp + 408) + BitVec.ofNat 64 (24 * (vecLen t (msp + 400)).toNat)) 8) →
      Wr (heapNext u₀) D C g.2.2.length a ∧
        ¬ Within a (msp + 424) 24 ∧ ¬ Within a (msp + 448) 24 ∧ ¬ Within a (msp + 240) 24 ∧
        (a.toNat < heapNext u₀ ∨ heapNext t ≤ a.toNat ∨ (Hb ≤ a.toNat ∧ a.toNat < H1) ∨
          (U ≤ a.toNat ∧ a.toNat < U + 2048) ∨
          Within a (vecPtr t (msp + 400)) ((vecCap t (msp + 400)).toNat * 24)) := by
    intro a ha
    simp only [heapNext]
    rw [hP]
    rcases ha with ha | ha | ha | ha
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha])))), by addr_omega [ha],
        by addr_omega [ha], by addr_omega [ha], Or.inr (Or.inl (by addr_omega [ha, hhi]))⟩
    all_goals exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by addr_omega [ha, hE, hP1, hP2, hm24, hhi],
        by simp only [heapEnd]; addr_omega [ha, hE, hP2, hm24, hhi],
        fun h' ↦ by addr_omega [h', ha, hE, mb, hP2, hm24, hdlo, hdc, hchi, hh1],
        fun h' ↦ by addr_omega [h', ha, hE, mb, hP2, hm24, hdlo, hdc, hchi, hh1]⟩))))),
        by addr_omega [ha, hE, hP2, hm24, hhi], by addr_omega [ha, hE, hP2, hm24, hhi],
        by addr_omega [ha, hE, hP2, hm24, hhi],
        Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hE, hP2, hm24]))))⟩
  have hK : ∀ c' : Nat, c' % 8 = 0 → c' < 4096 → c' ≠ 416 →
      v.getMem (msp + BitVec.ofNat 64 c') = t.getMem (msp + BitVec.ofNat 64 c') := fun c' h8 hc' hne ↦
    hf.getMem (by addr_omega [h8, hc']) fun j hj hw ↦ by
      rcases hw with hw | hw | hw | hw
      · addr_omega [hw, hj, hc', h8, hne]
      all_goals addr_omega [hw, hj, hc', hE, hP2, hm24, hhi]
  have hn : heapNext v = heapNext t := by
    simp only [heapNext]
    rw [hf.getMem (a := nextAddr) (by decide) fun j hj hw ↦ by
      rcases hw with hw | hw | hw | hw
      · addr_omega [hw, hj]
      all_goals addr_omega [hw, hj, hE, hP2, hm24, hhi]]
  have hheap : HeapOk v := ⟨by rw [hn]; exact rc.k.ng.heap.lo, by rw [hn]; exact rc.k.ng.heap.hi⟩
  have rc' := rc.frame hf (fun a ha ↦ (hW a ha).1) hspv hheap (le_of_eq hn.symm)
  have pv : vecPtr v (msp + 400) = vecPtr t (msp + 400) := hK 408 (by decide) (by decide) (by decide)
  have cv : vecCap v (msp + 400) = vecCap t (msp + 400) := hK 400 (by decide) (by decide) (by decide)
  have lv : vecLen v (msp + 400) = vecLen t (msp + 400) + 1 := by
    have e := b800004d0_m_x2_416 hv
    rw [hsp, h.x19] at e
    exact e
  have lv' : (vecLen v (msp + 400)).toNat = (vecLen t (msp + 400)).toNat + 1 := by
    rw [lv]; addr_omega [hP2, hm24, hhi]
  -- the `Block`'s fields
  have hfit := rc.k.a.inv.fits
  simp only [inputWords] at hfit
  have hlen := rc.k.a.len
  have hlt := rc.k.lt
  have hwl : (rfold words i L g st g.2.2.length).2.2.length < 2 ^ 31 := by
    have e := congrArg List.length h.vs.vecs.words
    simp only [wordsAt, List.length_map, List.length_range] at e
    rw [← e]; exact h.vs.bufs.w.len_lt (by decide) (by simp only [heapNext, heapEnd]; omega)
  have hbl' : (vecLen t (msp + 240)).toNat = (ufold g st g.2.2.length).2.length := by
    have e := congrArg List.length h.vs.vecs.bytes
    simp only [halvesAt, List.length_map, List.length_range] at e
    exact e
  have m48 := rc.k.bm.m48
  have hl : blocksAt v (vecPtr v (msp + 400)) (vecLen v (msp + 400)).toNat =
      st.blocks ++ [⟨i, (rfold words i L g st g.2.2.length).2.2.length,
        (ufold g st g.2.2.length).2.length⟩] := by
    rw [pv, lv', hP, blocksAt_snoc (t := t) (x := t.getMem (msp + 48)) (y := t.getReg .x9)
      (z := t.getReg .x18)
      (fun j hj ↦ ⟨hf.getMem (by addr_omega [hpal, hj, hP2, hm24, hhi]) fun x hx hw ↦ by
          rcases hw with hw | hw | hw | hw
          · addr_omega [hw, hx, hj, hP2, hm24, hhi]
          all_goals addr_omega [hw, hx, hj, hE, hP2, hm24, hhi],
        hf.getMem (by addr_omega [hpal, hj, hP2, hm24, hhi]) fun x hx hw ↦ by
          rcases hw with hw | hw | hw | hw
          · addr_omega [hw, hx, hj, hP2, hm24, hhi]
          all_goals addr_omega [hw, hx, hj, hE, hP2, hm24, hhi],
        hf.getMem (by addr_omega [hpal, hj, hP2, hm24, hhi]) fun x hx hw ↦ by
          rcases hw with hw | hw | hw | hw
          · addr_omega [hw, hx, hj, hP2, hm24, hhi]
          all_goals addr_omega [hw, hx, hj, hE, hP2, hm24, hhi]⟩)
      (by have e := b800004d0_m3 hv; rw [hsp, h.x19, hEe] at e; exact e)
      (by have e := b800004d0_m2 hv; rw [hsp, h.x19, hEe] at e; exact e)
      (by have e := b800004d0_m1 hv; rw [hsp, h.x19, hEe] at e; exact e), ← hP]
    have e := h.vs.vecs.blocks
    simp only at e
    rw [e, m48, h.x9, h.x18, hbl', BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have vs' := h.vs.setB (l := st.blocks ++ [⟨i, (rfold words i L g st g.2.2.length).2.2.length,
      (ufold g st g.2.2.length).2.length⟩]) hf (fun a ha ↦ (hW a ha).2) (le_of_eq hn.symm) hheap.hi
    ⟨by rw [lv', cv]; omega, by rw [pv]; exact bb.al, by rw [pv, cv, hn]; exact bb.buf,
      by rw [pv, cv]; exact bb.dang⟩
    (by simp only [VMiss, pv, cv]; exact h.vs.mb) (Or.inl ⟨pv, cv⟩) hl
  have hne : g.2.2 ≠ [] := rc.ne
  have bm := rc'.k.bm
  refine ⟨v, rv, ⟨rc.k.a, rc'.k.ng, b800004d0_pc hv, rc.k.lt, rc.k.hL,
    blockNew_eq rc.k.fold hg hne hbl, (kv .x8 (by decide)).trans h.x8, ?_, ?_,
    b800004d0_x22 hv, ?_, ?_, (kv .x27 (by decide)).trans h.x27, bm.m8, bm.m16, bm.m40, bm.m56,
    ⟨vs'.vecs.blocks, vs'.vecs.words, vs'.vecs.positions, vs'.vecs.bytes⟩, vs'.bufs, rc'.go, hsl⟩⟩
  · rw [b800004d0_x15 hv, hsp]; exact rc.k.bm.m64
  · rw [b800004d0_x16 hv, hsp]; exact rc.k.bm.m40
  · rw [b800004d0_x25 hv, hsp]; exact rc.k.bm.m8
  · rw [b800004d0_x26 hv, hsp]; exact h.m24

end

/-- **A block with a nonzero word**, from `group`'s exit to its end. -/
theorem blockFull : BlockFull := by
  intro s words u₀ i L Hb st g t h hpc hf hne
  obtain ⟨t₁, r₁, hd | ⟨C, hpc₁, h₁⟩⟩ := count_phase h hpc hf hne
  · exact ⟨t₁, r₁, Or.inl hd⟩
  obtain ⟨t₂, r₂, hd | ⟨N, H1, hpc₂, h₂⟩⟩ := runs_phase h₁ hpc₁
  · exact ⟨t₂, r₁.trans r₂, Or.inl hd⟩
  obtain ⟨t₃, r₃, hd | ⟨hpc₃, h₃⟩⟩ := place_phase h₂ hpc₂
  · exact ⟨t₃, r₁.trans (r₂.trans r₃), Or.inl hd⟩
  obtain ⟨t₄, r₄, hd | ⟨U, hpc₄, h₄⟩⟩ := bytes_phase h₃ hpc₃
  · exact ⟨t₄, r₁.trans (r₂.trans (r₃.trans r₄)), Or.inl hd⟩
  obtain ⟨t₅, r₅, hd | ⟨hpc₅, h₅⟩⟩ := push_head h₄ hpc₄
  · exact ⟨t₅, r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅))), Or.inl hd⟩
  obtain ⟨v, rv, hv⟩ := push_store h₅ hpc₅ (h.groupRust hf) (h.gslots hf) h.blk_len
  exact ⟨v, r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans rv)))), Or.inr ⟨_, hv⟩⟩

/-- **`Bytecode::new`.** -/
theorem newStage : NewStage := newStage_of blockFull

end Rv64Verifier.Proofs.Main
