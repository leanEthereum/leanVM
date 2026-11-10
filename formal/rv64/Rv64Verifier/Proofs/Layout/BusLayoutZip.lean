import Rv64Verifier.Proofs.Layout.BusLayoutFill

/-!
# `bus_layout`: the offsets and the pairs

From `0x80010bb8` to `0x80010c38`: `stack_offsets` of the sizes (`Q` its buffer), a buffer `R` of
`16 (n + m)` bytes, and the pairs `(size, offset)` written to it.
-/

namespace Rv64Verifier.Layout.BusLayout
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Sym Rv64Verifier.Bus Rv64Verifier.Blocks.F82
  Rv64Verifier.MultilinearContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The sizes, as `busLayoutRust` reads them. -/
def sizesList (s : MachineState) : List ℕ :=
  natsAt s (s.getReg .x11) (s.getReg .x12).toNat ++
    (blocksFrom s (s.getReg .x13) (s.getReg .x14).toNat).map (·.logRows)

/-- Their offsets. -/
def offs (s : MachineState) : List (BitVec 64) := (Model.stackOffsetsRust (sizesList s)).1

/-- The number of sizes. -/
@[rv_addr] def nn (s : MachineState) : Nat := (s.getReg .x12).toNat + (s.getReg .x14).toNat

/-- The pairs' first `k` written to `R`; the sizes still in `P`, the offsets in `Q`, both below
`R`. -/
structure Zip (s u : MachineState) (nx P Q R : Word) (k : Nat) : Prop where
  inv : Inv s u nx
  x8 : u.getReg .x8 = s.getReg .x12
  x9 : u.getReg .x9 = s.getReg .x10
  x19 : u.getReg .x19 = BitVec.ofNat 64 (nn s)
  x20 : (u.getReg .x20).toNat = (Model.stackOffsetsRust (sizesList s)).2
  x21 : u.getReg .x21 = R
  cap : u.getMem (s.getReg .x2 - 96) = BitVec.ofNat 64 (nn s)
  palign : P.toNat % 8 = 0
  qalign : Q.toNat % 8 = 0
  ralign : R.toNat % 8 = 0
  bufs : nn s = 0 ∨ heapNext s ≤ P.toNat ∧ P.toNat + 8 * nn s ≤ R.toNat ∧ Q.toNat + 8 * nn s ≤ R.toNat ∧
    heapNext s ≤ Q.toNat ∧ R.toNat + 16 * nn s ≤ nx.toNat
  sizes : ∀ i < nn s, u.getMem (P + BitVec.ofNat 64 (8 * i)) = srcWord s i
  offsets : ∀ i < nn s, u.getMem (Q + BitVec.ofNat 64 (8 * i)) = (offs s).getD i 0
  words : ∀ i < k, u.getMem (R + BitVec.ofNat 64 (16 * i)) = srcWord s i ∧
    u.getMem (R + BitVec.ofNat 64 (16 * i) + 8) = (offs s).getD i 0
  le : k ≤ nn s
  offsLen : (offs s).length = nn s

theorem Zip.mono {s u v : MachineState} {nx P Q R : Word} {k : Nat} (h : Zip s u nx P Q R k)
    (hpre : BusLayoutPre s) (hm : ∀ a, v.getMem a = u.getMem a)
    (hr : ∀ r ∈ [Reg.x2, .x8, .x9, .x19, .x20, .x21, .x24, .x25, .x26, .x27],
      v.getReg r = u.getReg r) :
    Zip s v nx P Q R k where
  inv := h.inv.same hpre hm hr
  x8 := (hr _ (by decide)).trans h.x8
  x9 := (hr _ (by decide)).trans h.x9
  x19 := (hr _ (by decide)).trans h.x19
  x20 := by rw [hr _ (by decide)]; exact h.x20
  x21 := (hr _ (by decide)).trans h.x21
  cap := (hm _).trans h.cap
  palign := h.palign
  qalign := h.qalign
  ralign := h.ralign
  bufs := h.bufs
  sizes := fun i hi ↦ (hm _).trans (h.sizes i hi)
  offsets := fun i hi ↦ (hm _).trans (h.offsets i hi)
  words := fun i hi ↦ ⟨(hm _).trans (h.words i hi).1, (hm _).trans (h.words i hi).2⟩
  le := h.le
  offsLen := h.offsLen

theorem readWords_getD (u : MachineState) (p : Word) {n i : Nat} (hi : i < n) :
    (u.readWords p n).getD i 0 = u.getMem (p + BitVec.ofNat 64 (8 * i)) := by
  rw [readWords_eq_map]; simp [List.getD_eq_getElem?_getD, hi]

/-- A call whose writes are all at or above `NEXT` keeps what lies below it. -/
theorem keep_below {u v : MachineState} {w : Word → Prop} (hf : ByteFrame u v w)
    (hw : ∀ a, w a → heapNext u ≤ a.toNat) {p : Word} (hp : p.toNat + 8 ≤ heapNext u) :
    v.getMem p = u.getMem p :=
  hf.getMem fun i hi h' ↦ by have := hw _ h'; addr_omega [this, hi, hp]

/-- From `0x80010bb8` through `stack_offsets` and `try_allocate_in` to `0x80010c04`'s branch. -/
theorem offsets (hT : TryAllocZeroedSpec) (hS : StackOffsetsSpec) {s u : MachineState}
    (hpre : BusLayoutPre s) {nx P : Word} (h : Filled s u nx P) :
    ∃ v, Reaches Image.code u v ∧ ((∃ nx' Q R, Zip s v nx' P Q R 0 ∧
      v.pc = (if nn s = 0 then 0x80010c38 else 0x80010c0c) ∧ v.getReg .x18 = P ∧
      v.getReg .x22 = Q) ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  obtain ⟨-, -, hn8, hm48, -, -⟩ := facts hpre
  have hF := h.fill
  have hP8 := hF.align
  have hfit := hF.inv.fits
  have hmono := hF.inv.mono
  have hlo0 := hpre.heap.lo
  have hsp : u.getReg .x2 = s.getReg .x2 - 112 := hF.inv.sp
  obtain ⟨u₁, hr₁, h₁⟩ := BlockSpec.reaches b80010bb8_spec h.pc (by rv_eval [])
  have k₁ := b80010bb8_keeps h₁
  have inv₁ := hF.inv.same hpre (b80010bb8_mem_same h₁) k₁
  have x2₁ : u₁.getReg .x2 = s.getReg .x2 - 112 := (k₁ .x2 (by decide)).trans hsp
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - 104 := by rw [b80010bb8_x10 h₁, hsp]; rv_eval []
  have x11₁ : u₁.getReg .x11 = P := (b80010bb8_x11 h₁).trans hF.x18
  have x12₁ : u₁.getReg .x12 = BitVec.ofNat 64 (nn s) := (b80010bb8_x12 h₁).trans h.x19
  have hN : (BitVec.ofNat 64 (nn s)).toNat = nn s := by addr_omega [hn8, hm48]
  have hn₁ : heapNext u₁ = nx.toNat := by simp only [heapNext, inv₁.next]
  have hsl : stackLo u₁ stackOffsetsStack = s.getReg .x2 - 224 := by
    simp only [stackLo, x2₁, stackOffsetsStack, tryAllocStack, Nat.reduceAdd]; rv_eval []
  have hbuf := hF.buf
  have hpre₁ : StackOffsetsPre u₁ := {
    heap := ⟨by rw [hn₁]; exact Nat.le_trans hlo0 hmono, by rw [hn₁]; exact hfit⟩
    out := by rw [x10₁]; addr_omega [hb]
    sizes := by
      rw [x12₁, x11₁, hN]
      rcases hbuf with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (by addr_omega [h0, hfit, hlo0, hP8])
    stack := hst.sub 112 x2₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by
      rw [x10₁]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    outStack := by rw [x10₁, hsl]; addr_omega [hb]
    sizesFree := by
      rw [x12₁, x11₁, hN]
      rcases hbuf with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨Or.inl (by rw [hn₁]; exact h0.2), by addr_omega [h0, hfit]⟩
    sizesStack := by
      rw [x12₁, x11₁, hN, hsl]
      rcases hbuf with h0 | h0
      · exact Or.inl (by simp only [nn]; omega)
      · addr_omega [h0, hfit, hab, hb]
    sizesOut := by
      rw [x12₁, x11₁, hN, x10₁]
      rcases hbuf with h0 | h0
      · exact Or.inl (by simp only [nn]; omega)
      · addr_omega [h0, hfit, hab, hb] }
  obtain ⟨u₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ := hS.call hr₁ (b80010bb8_pc h₁) hpre₁
  swap
  · exact ⟨u₂, hr₂, Or.inr hdead⟩
  have hsz : sizesAt u₁ = sizesList s := by
    rw [sizesAt, x11₁, x12₁, hN, readWords_eq_map, List.map_map, sizesList, ← sizes_eq]
    exact List.map_congr_left fun i hi ↦ by
      simp only [Function.comp]
      rw [b80010bb8_mem_same h₁, hF.words i (List.mem_range.mp hi)]
  have hfr := hpost₂.frame
  rw [x10₁, hsl] at hfr
  have inv₂ : Inv s u₂ (u₂.getMem nextAddr) := inv₁.step hpre hfr (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (Or.inr (by addr_omega [ha, hb]))
      · exact Or.inl (Or.inr (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inl ha)
      · simp only [Fresh, hn₁] at ha
        exact Or.inr (Or.inr ⟨Nat.le_trans hmono ha.1, ha.2⟩))
    rfl (by have := hpost₂.mono; rw [hn₁] at this; exact this) hpost₂.heap.hi
    fun r hr ↦ hpres₂ r (by unfold calleeSaved; revert hr; revert r; decide)
  have hlen := hpost₂.len
  have hoff := hpost₂.offsets
  have hlog := hpost₂.log
  have hQ := hpost₂.fresh
  simp only [vecLen, vecWords, vecPtr, x10₁, x12₁, hN, hsz] at hlen hoff hlog hQ
  rv_eval [] at hlen hoff hlog hQ
  rw [hlen, hN] at hoff
  obtain ⟨Q, hQd⟩ : ∃ Q, Q = u₂.getMem (s.getReg .x2 - 96) := ⟨_, rfl⟩
  rw [← hQd] at hoff hQ
  have hoffLen : (offs s).length = nn s := by
    rw [offs, ← hoff, readWords_eq_map, List.length_map, List.length_range]
  have hsp₂ : u₂.getReg .x2 = s.getReg .x2 - 112 := (hpres₂.reg .x2).trans x2₁
  have hn₂ : heapNext u₂ = (u₂.getMem nextAddr).toNat := rfl
  have hle₂ : nx.toNat ≤ heapNext u₂ := by have := hpost₂.mono; rwa [hn₁] at this
  have hfit₂ := hpost₂.heap.hi
  -- what lies below `NEXT` at the call stays
  have kb₂ {p : Word} (hp : p.toNat + 8 ≤ nx.toNat) : u₂.getMem p = u.getMem p := by
    rw [keep_below hfr (fun a ha ↦ by
        rcases ha with ha | ha | ha | ha
        · rw [hn₁]; addr_omega [ha, hb, hab, hfit]
        · rw [hn₁]; addr_omega [ha, hb, hab, hfit]
        · rw [hn₁]; addr_omega [ha, hfit]
        · exact ha.1) (by rw [hn₁]; exact hp), b80010bb8_mem_same h₁]
  obtain ⟨u₃, hr₃, h₃⟩ := BlockSpec.reaches b80010bcc_spec
    (by rw [hpc₂, returnAddress_eq, b80010bb8_x1 h₁]; decide) (by
      rv_eval [hsp₂]; valid_access hst.valid [hb])
  have k₃ := b80010bcc_keeps h₃
  have x19₂ : u₂.getReg .x19 = BitVec.ofNat 64 (nn s) :=
    (hpres₂.reg .x19).trans ((k₁ .x19 (by decide)).trans h.x19)
  have hm₃ := b80010bcc_mem_same h₃
  -- `0x80010bd4`: `x19` = the offsets' length, the same
  obtain ⟨u₄, hr₄, h₄⟩ := BlockSpec.reaches b80010bd4_spec
    (b80010bcc_pc_not_taken h₃ (by rw [hsp₂, x19₂]; rv_eval [hlen]; exact Nat.le_refl _))
    (by rv_eval [])
  have k₄ := b80010bd4_keeps h₄
  have x19₄ : u₄.getReg .x19 = BitVec.ofNat 64 (nn s) := by
    rw [b80010bd4_x19 h₄, b80010bcc_x10 h₃, hsp₂]; rv_eval [hlen]
  have hm₄ := b80010bd4_mem_same h₄
  have x2₄ : u₄.getReg .x2 = s.getReg .x2 - 112 := by rw [k₄ .x2 (by decide), k₃ .x2 (by decide), hsp₂]
  have inv₄ := (inv₂.same hpre hm₃ k₃).same hpre hm₄ k₄
  obtain ⟨u₅, hr₅, h₅⟩ := BlockSpec.reaches b80010bd8_spec (b80010bd4_pc h₄) (by
    rv_eval [x2₄]; and_intros <;> valid_access hst.valid [hb])
  have k₅ := b80010bd8_keeps h₅
  have inv₅ := inv₄.same hpre (b80010bd8_mem_same h₅) k₅
  have x2₅ : u₅.getReg .x2 = s.getReg .x2 - 112 := (k₅ .x2 (by decide)).trans x2₄
  have x10₅ : u₅.getReg .x10 = s.getReg .x2 - 104 := by rw [b80010bd8_x10 h₅, x2₄]; rv_eval []
  have x11₅ : u₅.getReg .x11 = BitVec.ofNat 64 (nn s) := (b80010bd8_x11 h₅).trans x19₄
  have x22₅ : u₅.getReg .x22 = Q := by rw [b80010bd8_x22 h₅, x2₄]; rv_eval [hm₄, hm₃, hQd]
  have x20₅ : (u₅.getReg .x20).toNat = (Model.stackOffsetsRust (sizesList s)).2 := by
    rw [b80010bd8_x20 h₅, x2₄]; rv_eval [hm₄, hm₃]; exact hlog
  have hn₅ : heapNext u₅ = heapNext u₂ := by simp only [heapNext, inv₅.next]
  have hsl₅ : stackLo u₅ tryAllocStack = s.getReg .x2 - 160 := by
    simp only [stackLo, tryAllocStack, x2₅]; rv_eval []
  have hpre₅ : TryAllocPre .x13 .x14 u₅ := {
    heap := ⟨by rw [hn₅]; exact Nat.le_trans (Nat.le_trans hlo0 hmono) hle₂, by rw [hn₅]; exact hfit₂⟩
    out := by rw [x10₅]; valid_sub hst.valid [hb]
    align := by rw [b80010bd8_x13 h₅]; decide
    size := by rw [b80010bd8_x14 h₅]; decide
    stack := hst.sub 112 x2₅ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by
      rw [x10₅]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    outStack := by rw [x10₅, hsl₅]; addr_omega [hb] }
  obtain ⟨u₆, hr₆, ⟨hpc₆, hpres₆, hpost₆, -⟩ | hdead⟩ := hT.call hr₅ (b80010bd8_pc h₅) hpre₅
  swap
  · exact ⟨u₆, hr₂.trans (hr₃.trans (hr₄.trans hr₆)), Or.inr hdead⟩
  have hfr₆ := hpost₆.frame
  rw [x10₅, hsl₅] at hfr₆
  have inv₆ : Inv s u₆ (u₆.getMem nextAddr) := inv₅.step hpre hfr₆ (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (Or.inr (by addr_omega [ha, hb]))
      · exact Or.inl (Or.inr (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inl ha)
      · simp only [Fresh, hn₅] at ha
        exact Or.inr (Or.inr ⟨Nat.le_trans (Nat.le_trans hmono hle₂) ha.1, ha.2⟩))
    rfl (by have := hpost₆.mono; rw [hn₅] at this; exact this) hpost₆.heap.hi
    fun r hr ↦ hpres₆ r (by unfold calleeSaved; revert hr; revert r; decide)
  have kb₆ {p : Word} (hp : p.toNat + 8 ≤ heapNext u₂) : u₆.getMem p = u₂.getMem p := by
    rw [keep_below hfr₆ (fun a ha ↦ by
        rcases ha with ha | ha | ha | ha
        · rw [hn₅]; addr_omega [ha, hb, hab, hfit₂]
        · rw [hn₅]; addr_omega [ha, hb, hab, hfit₂]
        · rw [hn₅]; addr_omega [ha, hfit₂]
        · exact ha.1) (by rw [hn₅]; exact hp), b80010bd8_mem_same h₅, hm₄, hm₃]
  have x2₆ : u₆.getReg .x2 = s.getReg .x2 - 112 := (hpres₆.reg .x2).trans x2₅
  obtain ⟨u₇, hr₇, h₇⟩ := BlockSpec.reaches b80010bfc_spec
    (by rw [hpc₆, returnAddress_eq, b80010bd8_x1 h₅]; decide) (by
      rv_eval [x2₆]; valid_access hst.valid [hb])
  rcases eq_or_ne (u₆.getMem (s.getReg .x2 - 104)) 0 with htag | htag
  swap
  · refine ⟨u₇, hr₂.trans (hr₃.trans (hr₄.trans (hr₆.trans hr₇))), Or.inr (dead_of_fetch ?_)⟩
    rw [b80010bfc_pc_taken h₇ (by rv_eval [x2₆]; exact htag)]
    exact Option.isNone_iff_eq_none.mp (by decide +kernel)
  have k₇ := b80010bfc_keeps h₇
  obtain ⟨hcap, hbufR⟩ := hpost₆.ok (by rw [x10₅]; exact htag)
  rw [x10₅, x11₅] at hcap hbufR
  rw [b80010bd8_x14 h₅, b80010bd8_x13 h₅] at hbufR
  rv_eval [] at hcap hbufR
  obtain ⟨R, hRd⟩ : ∃ R, R = u₆.getMem (s.getReg .x2 - 88) := ⟨_, rfl⟩
  rw [← hRd, hN] at hbufR
  simp only [NewBuf, hn₅] at hbufR
  have x2₇ : u₇.getReg .x2 = s.getReg .x2 - 112 := (k₇ .x2 (by decide)).trans x2₆
  obtain ⟨u₈, hr₈, h₈⟩ := BlockSpec.reaches b80010c04_spec
    (b80010bfc_pc_not_taken h₇ (by rv_eval [x2₆]; exact htag)) (by
      rv_eval [x2₇]; valid_access hst.valid [hb])
  have k₈ := b80010c04_keeps h₈
  have hm₇₈ (a : Word) : u₈.getMem a = u₆.getMem a := by
    rw [b80010c04_mem_same h₈, b80010bfc_mem_same h₇]
  have hreg (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x24, .x25, .x26, .x27]) : u₈.getReg r = u.getReg r := by
    rw [k₈ r (by revert hr; revert r; decide), k₇ r (by revert hr; revert r; decide),
      hpres₆ r (by unfold calleeSaved; revert hr; revert r; decide),
      k₅ r (by revert hr; revert r; decide), k₄ r (by revert hr; revert r; decide),
      k₃ r (by revert hr; revert r; decide),
      hpres₂ r (by unfold calleeSaved; revert hr; revert r; decide), k₁ r (by revert hr; revert r; decide)]
  have x19₇ : u₇.getReg .x19 = BitVec.ofNat 64 (nn s) := by
    rw [k₇ .x19 (by decide), hpres₆.reg .x19, k₅ .x19 (by decide), x19₄]
  have x20₈ : u₈.getReg .x20 = u₅.getReg .x20 := by
    rw [k₈ .x20 (by decide), k₇ .x20 (by decide), hpres₆.reg .x20]
  simp only [NewBuf, hn₁] at hQ
  have hnn : nn s = (s.getReg .x12).toNat + (s.getReg .x14).toNat := rfl
  have h6 : heapNext u₆ = (u₆.getMem nextAddr).toNat := rfl
  refine ⟨u₈, hr₂.trans (hr₃.trans (hr₄.trans (hr₆.trans (hr₇.trans hr₈)))), Or.inl
    ⟨u₆.getMem nextAddr, Q, R, {
      inv := (inv₆.same hpre (b80010bfc_mem_same h₇) k₇).same hpre (b80010c04_mem_same h₈) k₈
      x8 := (hreg .x8 (by decide)).trans hF.x8
      x9 := (hreg .x9 (by decide)).trans hF.x9
      x19 := (k₈ .x19 (by decide)).trans x19₇
      x20 := by rw [x20₈]; exact x20₅
      x21 := by rw [b80010c04_x21 h₈, x2₇]; rv_eval [b80010bfc_mem_same h₇, hRd]
      cap := by rw [hm₇₈]; exact hcap
      palign := hP8
      qalign := hQ.1
      ralign := hbufR.1
      bufs := by
        by_cases hz : nn s = 0
        · exact Or.inl hz
        · have hq := hQ.2.resolve_left (by omega)
          have hr := hbufR.2.resolve_left (by omega)
          have hp := hbuf.resolve_left (by omega)
          exact Or.inr (by omega)
      sizes := fun i hi ↦ by
        rw [hm₇₈, kb₆ (by addr_omega [hbuf, hi, hle₂, hfit]), kb₂ (by addr_omega [hbuf, hi, hfit])]
        exact hF.words i hi
      offsets := fun i hi ↦ by
        have hq := hQ.2.resolve_left (by omega)
        rw [hm₇₈, kb₆ (by addr_omega [hq, hi]), ← readWords_getD u₂ Q hi, hoff]
        rfl
      words := fun i hi ↦ absurd hi (Nat.not_lt_zero _)
      le := Nat.zero_le _
      offsLen := hoffLen }, ?_, (hreg .x18 (by decide)).trans hF.x18, by
        rw [k₈ .x22 (by decide), k₇ .x22 (by decide), hpres₆.reg .x22, x22₅]⟩⟩
  by_cases hz : nn s = 0
  · simp only [hz, ↓reduceIte]
    exact b80010c04_pc_taken h₈ (by rw [x19₇, hz]; rfl)
  · simp only [hz, ↓reduceIte]
    exact b80010c04_pc_not_taken h₈ (by
      rw [x19₇]
      intro h0
      apply hz
      have := congrArg BitVec.toNat h0
      rwa [hN] at this)

/-- At the head of the loop that writes pair `k`. -/
structure ZLoop (s u : MachineState) (nx P Q R : Word) (k : Nat) : Prop where
  zip : Zip s u nx P Q R k
  lt : k < nn s
  pc : u.pc = 0x80010c18
  x10 : u.getReg .x10 = R + BitVec.ofNat 64 (16 * k + 8)
  x11 : u.getReg .x11 = R + BitVec.ofNat 64 (16 * nn s + 8)
  x18 : u.getReg .x18 = P + BitVec.ofNat 64 (8 * k)
  x22 : u.getReg .x22 = Q + BitVec.ofNat 64 (8 * k)

theorem zbody {s u : MachineState} (hpre : BusLayoutPre s) {nx P Q R : Word} {k : Nat}
    (h : ZLoop s u nx P Q R k) :
    ∃ v, Reaches Image.code u v ∧ ((ZLoop s v nx P Q R (k + 1) ∧
      (v.getReg .x11).toNat - (v.getReg .x10).toNat < (u.getReg .x11).toNat - (u.getReg .x10).toNat) ∨
      (Zip s v nx P Q R (nn s) ∧ v.pc = 0x80010c38)) := by
  have hb := bounds hpre
  have hZ := h.zip
  have hlt := h.lt
  have hbuf := hZ.bufs.resolve_left (by omega)
  have hfit := hZ.inv.fits
  have hlo0 := hpre.heap.lo
  have hP8 := hZ.palign
  have hQ8 := hZ.qalign
  have hR8 := hZ.ralign
  have x10 := h.x10
  have x11 := h.x11
  have x18 := h.x18
  have x22 := h.x22
  obtain ⟨v, hr, hv⟩ := BlockSpec.reaches b80010c18_spec h.pc (by
    rv_eval [x10, x18, x22]
    and_intros <;> refine Mapped.valid8 (a := 0x20) (n := 0x77ffffe0) (by simp only [Mapped]; decide)
      ?_ ?_ ?_ <;> addr_omega [hbuf, hfit, hlo0, hP8, hQ8, hR8, hlt])
  have k₁ := b80010c18_keeps hv
  have m0 := b80010c18_m_x10_0 hv
  have m8 := b80010c18_m_x10_n8 hv
  rw [x10, x22, hZ.offsets k hlt] at m0
  rw [x10, x18, hZ.sizes k hlt] at m8
  have hfr := b80010c18_frame hv (by rw [x10]; addr_omega [hbuf, hfit, hlt])
  rw [x10] at hfr
  have e8 : R + BitVec.ofNat 64 (16 * k + 8) - 8 = R + BitVec.ofNat 64 (16 * k) := by
    addr_omega [hbuf, hfit, hlt]
  rw [e8] at hfr m8
  have e0 : R + BitVec.ofNat 64 (16 * k + 8) = R + BitVec.ofNat 64 (16 * k) + 8 := by
    addr_omega [hbuf, hfit, hlt]
  rw [e0] at m0
  have keep (a : Word) (ha : a.toNat + 8 ≤ (R + BitVec.ofNat 64 (16 * k)).toNat ∨
      (R + BitVec.ofNat 64 (16 * k)).toNat + 16 ≤ a.toNat) : v.getMem a = u.getMem a :=
    hfr a fun hw ↦ by addr_omega [hw, ha]
  have hZ' : Zip s v nx P Q R (k + 1) := {
    inv := hZ.inv.frame hpre hfr (by addr_omega [hbuf, hfit, hlt, hR8]) (by decide)
      (hv.unaligned (by rv_eval [x10]; and_intros <;> addr_omega [hbuf, hfit, hlt, hR8]))
      (fun a ha ↦ Or.inr (by addr_omega [ha, hbuf, hfit, hlt])) k₁
    x8 := (k₁ .x8 (by decide)).trans hZ.x8
    x9 := (k₁ .x9 (by decide)).trans hZ.x9
    x19 := (k₁ .x19 (by decide)).trans hZ.x19
    x20 := by rw [k₁ .x20 (by decide)]; exact hZ.x20
    x21 := (k₁ .x21 (by decide)).trans hZ.x21
    cap := by rw [keep _ (by addr_omega [hb, hbuf, hfit, hlt])]; exact hZ.cap
    palign := hP8
    qalign := hQ8
    ralign := hR8
    bufs := hZ.bufs
    sizes := fun i hi ↦ by rw [keep _ (by addr_omega [hbuf, hfit, hlt, hi])]; exact hZ.sizes i hi
    offsets := fun i hi ↦ by rw [keep _ (by addr_omega [hbuf, hfit, hlt, hi])]; exact hZ.offsets i hi
    words := fun i hi ↦ by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · rw [keep _ (by addr_omega [hbuf, hfit, hlt, hi']), keep _ (by addr_omega [hbuf, hfit, hlt, hi'])]
        exact hZ.words i hi'
      · exact ⟨m8, m0⟩
    le := by omega
    offsLen := hZ.offsLen }
  have y10 : v.getReg .x10 = R + BitVec.ofNat 64 (16 * (k + 1) + 8) := by
    rw [b80010c18_x10 hv, x10]; addr_omega [hbuf, hfit, hlt]
  have y11 : v.getReg .x11 = u.getReg .x11 := k₁ .x11 (by decide)
  refine ⟨v, hr, ?_⟩
  by_cases hk : k + 1 < nn s
  · refine Or.inl ⟨{
      zip := hZ'
      lt := hk
      pc := b80010c18_pc_taken hv (by rw [x10, x11]; addr_omega [hbuf, hfit, hk])
      x10 := y10
      x11 := y11.trans x11
      x18 := by rw [b80010c18_x18 hv, x18]; addr_omega [hbuf, hfit, hk]
      x22 := by rw [b80010c18_x22 hv, x22]; addr_omega [hbuf, hfit, hk] }, ?_⟩
    rw [y10, y11, x10, x11]
    addr_omega [hbuf, hfit, hk]
  · have hk' : k + 1 = nn s := by omega
    rw [hk'] at hZ'
    exact Or.inr ⟨hZ', b80010c18_pc_not_taken hv (by rw [x10, x11]; addr_omega [hbuf, hfit, hk'])⟩

end Rv64Verifier.Layout.BusLayout
