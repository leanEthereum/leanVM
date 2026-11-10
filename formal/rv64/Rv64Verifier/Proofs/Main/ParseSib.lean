import Rv64Verifier.Proofs.Main.ParseStreamHead

/-!
# A path's siblings

`0x80000d48` reads a digest into `msp + 320` (`Input::digest`), `0x80000d58` copies its 32 bytes
to the next sibling at `s5` (`memcpy`), `0x80000d6c` counts down `s4` (`sib_body`, `sib_loop`):
`h` siblings into the buffer at `Q`, `rep readDigest h`.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode Rv64Verifier.Proofs.End Rv64Verifier.Blocks.F3

/-- What the siblings' loop writes: the digest's buffer, the input slice, the stack and the
siblings' buffer. -/
def Wsib (Q : Word) (h : Nat) (a : Word) : Prop :=
  Within a (msp + 320) 32 ∨ Within a (msp + 88) 16 ∨ Within a (msp - 4096) 4096 ∨
    Within a Q (32 * h)

theorem Wsib.wf {Q : Word} {h B : Nat} (hB : B ≤ Q.toNat) (hQ : Q.toNat + 32 * h ≤ heapEnd)
    {a : Word} (ha : Wsib Q h a) : Wf B a := by
  rcases ha with ha | ha | ha | ha
  · exact Wf.out (by addr_omega [ha])
  · exact Wf.slot (by addr_omega [ha])
  · exact Wf.stack ha
  · simp only [heapEnd] at hQ
    exact Wf.heap (by simp only [Within] at ha; omega) (by simp only [Within, heapEnd] at ha ⊢; omega)

theorem m96 : (msp + 88 + 8 : Word) = msp + 96 := by decide

/-- The siblings' loop at `e` (`0x80000d48`, or `0x80000d78` when done), `c` of the `h` siblings
read, from `kh`, into the buffer at `Q`; `t₀` where it started. -/
structure SbS (u₀ : MachineState) (words : List Word) (Q : Word) (h kh : Nat) (t₀ : MachineState)
    (e : Word) (t : MachineState) (c : Nat) : Prop where
  pg : PG u₀ t
  pc : t.pc = e
  le : c ≤ h
  regs : ∀ r ∈ calleeSaved, r ≠ .x20 → r ≠ .x21 → t.getReg r = t₀.getReg r
  x20 : t.getReg .x20 = BitVec.ofNat 64 (h - c)
  x21 : t.getReg .x21 = Q + BitVec.ofNat 64 (32 * c)
  room : kh + 4 * c ≤ words.length
  ptr : t.getMem (msp + 88) = inputBase + BitVec.ofNat 64 (8 * (kh + 4 * c))
  rest : (t.getMem (msp + 96)).toNat = words.length - (kh + 4 * c)
  read : (rep readDigest c).run (words.drop kh) = some ((List.range c).map fun c' ↦
    digestOfBytes (bytesAt t (Q + BitVec.ofNat 64 (32 * c')) 32), words.drop (kh + 4 * c))
  frame : BFrame t₀ t (Wsib Q h)
  heap : heapNext t = heapNext t₀
  buf : heapNext u₀ ≤ Q.toNat ∧ Q.toNat + 32 * h ≤ heapNext t₀

section
variable {s u₀ t : MachineState} {words : List Word}

theorem readWords_input (h0 : ParseA s words u₀) (hg : PG u₀ t) {k : Nat}
    (hk : k + 4 ≤ words.length) :
    t.readWords (inputBase + BitVec.ofNat 64 (8 * k)) 4 = (words.drop k).take 4 := by
  have hfit := h0.inv.fits
  simp only [inputWords] at hfit
  have hib : inputBase.toNat = 0x10000000 := rfl
  rw [readWords_eq_map]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take, List.length_drop]; omega
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  rw [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
  exact hg.word h0 (j := k + i) (by omega) (by addr_omega [hib, hk, hfit, h1])

/-- One sibling. -/
theorem sib_body (h0 : ParseA s words u₀) {Q : Word} {h kh c : Nat} {t₀ : MachineState}
    (hs : SbS u₀ words Q h kh t₀ 0x80000d48 t c) (hc : c < h) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
      (c + 1 < h ∧ SbS u₀ words Q h kh t₀ 0x80000d48 v (c + 1)) ∨
      (c + 1 = h ∧ SbS u₀ words Q h kh t₀ 0x80000d78 v (c + 1))) := by
  have hg := hs.pg
  have hsp := hg.sp
  have hfit := h0.inv.fits
  simp only [inputWords] at hfit
  have hib : inputBase.toNat = 0x10000000 := rfl
  have hlo0 := h0.inv.heap.lo
  have hhi := hg.heap.hi
  obtain ⟨hQ0, hQh⟩ := hs.buf
  rw [← hs.heap] at hQh
  simp only [heapStart, heapNext, heapEnd] at hlo0 hhi hQ0 hQh
  have hroom := hs.room
  -- `0x80000d48`, `Input::digest`
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b80000d48_spec hs.pc trivial
  have k₁ := b80000d48_keeps h₁
  have m₁ := b80000d48_mem_same h₁
  have hsp₁ : t₁.getReg .x2 = msp := by rw [k₁ .x2 (by decide), hsp]
  have f10 : t₁.getReg .x10 = msp + 320 := by rw [b80000d48_x10 h₁, hsp]
  have f11 : t₁.getReg .x11 = msp + 88 := by rw [b80000d48_x11 h₁, hsp]
  have g88 : t₁.getMem (msp + 88) = inputBase + BitVec.ofNat 64 (8 * (kh + 4 * c)) := by
    rw [m₁, hs.ptr]
  have g96 : t₁.getMem (msp + 88 + 8) = BitVec.ofNat 64 (words.length - (kh + 4 * c)) := by
    rw [m96, m₁]
    apply BitVec.eq_of_toNat_eq
    rw [hs.rest, BitVec.toNat_ofNat]
    omega
  obtain ⟨t₂, r₂, hout⟩ := digest_spec t₁ (b80000d48_pc h₁) {
    out := by rw [f10]; simp only [Runtime.Mapped]; decide
    outAlign := by rw [f10]; decide
    self := by rw [f11]; simp only [Runtime.Mapped]; decide
    selfAlign := by rw [f11]; decide
    stack := stackOk_msp hsp₁ (by decide) (by decide)
    outSelf := by rw [f10, f11]; addr_omega []
    outStack := by rw [f10]; simp only [stackLo, hsp₁]; addr_omega []
    selfStack := by rw [f11]; simp only [stackLo, hsp₁]; addr_omega []
    words := fun h4 ↦ by
      simp only [inputLen, inputPtr, f11] at h4 ⊢
      rw [g96, BitVec.toNat_ofNat] at h4
      rw [g88]
      refine ⟨?_, ?_, ?_⟩
      · simp only [Runtime.Mapped]; rw [BitVec.toNat_add, BitVec.toNat_ofNat, hib]; omega
      · rw [BitVec.toNat_add, BitVec.toNat_ofNat, hib]; omega
      · simp only [stackLo, hsp₁]; addr_omega [hib, hfit, h4] }
  rcases hout with ⟨hpc₂, hpres₂, hp₂⟩ | hd
  swap
  · exact ⟨t₂, r₁.trans r₂, Or.inl hd⟩
  have hsp₂ : t₂.getReg .x2 = msp := (hpres₂.reg .x2).trans hsp₁
  have l4 := hp₂.len
  simp only [inputLen, f11, g96, BitVec.toNat_ofNat] at l4
  have h4 : kh + 4 * c + 4 ≤ words.length := by omega
  have hW₂ : ∀ a, ¬ (Within a (msp + 320) 32 ∨ Within a (msp + 88) 16 ∨ Within a (msp - 96) 96) →
      t₂.getMem a = t₁.getMem a := by
    intro a ha
    exact hp₂.frame a (by rw [f10]; exact fun h' ↦ ha (Or.inl h'))
      (by rw [f11]; exact fun h' ↦ ha (Or.inr (Or.inl h')))
      (by simp only [stackLo, hsp₁, digestStack]; exact fun h' ↦ ha (Or.inr (Or.inr h')))
  have hb₂ : BFrame t₁ t₂ fun a ↦ Within a (msp + 320) 32 ∨ Within a (msp + 88) 16 ∨
      Within a (msp - 96) 96 :=
    BFrame.of_dwords hW₂ fun a ha ↦ by
      rcases ha with ha | ha | ha
      · exact Or.inl (within_of_alignDown (by decide) (by decide) ha)
      · exact Or.inr (Or.inl (within_of_alignDown (by decide) (by decide) ha))
      · exact Or.inr (Or.inr (within_of_alignDown (by decide) (by decide) ha))
  have p₂ : t₂.getMem (msp + 88) = inputBase + BitVec.ofNat 64 (8 * (kh + 4 * (c + 1))) := by
    have e := hp₂.ptr
    simp only [inputPtr, f11] at e
    rw [e, g88]
    addr_omega [hib, hfit, h4]
  have q₂ : (t₂.getMem (msp + 96)).toNat = words.length - (kh + 4 * (c + 1)) := by
    have e := hp₂.rest
    simp only [inputLen, f11] at e
    rw [← m96, e, g96]
    addr_omega [hfit, h4]
  have hwords₂ : t₂.readWords (msp + 320) 4 = (words.drop (kh + 4 * c)).take 4 := by
    have e := hp₂.words
    rw [f10] at e
    simp only [inputPtr, f11, g88] at e
    rw [e, readWords_input h0 (hg.same m₁ hsp₁) h4]
  -- `0x80000d58`, `memcpy`
  have hpc₂' : t₂.pc = 0x80000d58 := by rw [hpc₂, returnAddress, b80000d48_x1 h₁]; decide
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b80000d58_spec hpc₂' trivial
  have k₃ := b80000d58_keeps h₃
  have m₃ := b80000d58_mem_same h₃
  have hsp₃ : t₃.getReg .x2 = msp := by rw [k₃ .x2 (by decide), hsp₂]
  have x21₂ : t₂.getReg .x21 = Q + BitVec.ofNat 64 (32 * c) := by
    rw [hpres₂.reg .x21 (by decide), k₁ .x21 (by decide), hs.x21]
  have e10 : t₃.getReg .x10 = Q + BitVec.ofNat 64 (32 * c) := by rw [b80000d58_x10 h₃, x21₂]
  have e11 : t₃.getReg .x11 = msp + 320 := by rw [b80000d58_x11 h₃, hsp₂]
  have e12 : (t₃.getReg .x12).toNat = 32 := by rw [b80000d58_x12 h₃]; rfl
  obtain ⟨t₄, r₄, hout⟩ := Runtime.memcpy t₃ (b80000d58_pc h₃) {
    dst := by rw [e10, e12]; simp only [Runtime.Mapped]; addr_omega [hQ0, hQh, hhi, hc, hlo0]
    src := by rw [e11, e12]; simp only [Runtime.Mapped]; decide
    apart := by rw [e10, e11, e12]; addr_omega [hQ0, hQh, hhi, hc, hlo0]
    stack := stackOk_msp hsp₃ (by decide) (by decide)
    dstStack := by
      rw [e10, e12]; simp only [stackLo, hsp₃]; addr_omega [hQ0, hQh, hhi, hc, hlo0]
    srcStack := by rw [e11, e12]; simp only [stackLo, hsp₃]; addr_omega [] }
  rcases hout with ⟨hpc₄, hpres₄, hp₄⟩ | hd
  swap
  · exact ⟨t₄, r₁.trans (r₂.trans (r₃.trans r₄)), Or.inl hd⟩
  have hsp₄ : t₄.getReg .x2 = msp := (hpres₄.reg .x2).trans hsp₃
  have hb₄ : BFrame t₃ t₄ fun a ↦ Within a (Q + BitVec.ofNat 64 (32 * c)) 32 ∨
      Within a (msp - 16) 16 :=
    BFrame.mono hp₄.frame.byte fun a ha ↦ by
      rw [e10, e12] at ha; simp only [stackLo, hsp₃, memcpyStack] at ha; exact ha
  have hbytes : bytesAt t₄ (Q + BitVec.ofNat 64 (32 * c)) 32 = bytesAt t₂ (msp + 320) 32 := by
    have e := hp₄.bytes
    rw [e10, e11, e12] at e
    rw [e, bytesAt_same m₃]
  -- `0x80000d6c`
  have hpc₄' : t₄.pc = 0x80000d6c := by rw [hpc₄, returnAddress, b80000d58_x1 h₃]; decide
  obtain ⟨t₅, r₅, h₅⟩ := Sym.BlockSpec.reaches b80000d6c_spec hpc₄' trivial
  have k₅ := b80000d6c_keeps h₅
  have m₅ := b80000d6c_mem_same h₅
  have hsp₅ : t₅.getReg .x2 = msp := by rw [k₅ .x2 (by decide), hsp₄]
  -- the frame of the step
  have hb : BFrame t t₅ fun a ↦ Within a (msp + 320) 32 ∨ Within a (msp + 88) 16 ∨
      Within a (msp - 4096) 4096 ∨ Within a (Q + BitVec.ofNat 64 (32 * c)) 32 := by
    have b1 : BFrame t t₂ fun a ↦ Within a (msp + 320) 32 ∨ Within a (msp + 88) 16 ∨
        Within a (msp - 4096) 4096 ∨ Within a (Q + BitVec.ofNat 64 (32 * c)) 32 :=
      (BFrame.of_same m₁ _).trans hb₂ fun a ha ↦ by
        rcases ha with ha | ha | ha
        · exact Or.inl ha
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha])))
    have b2 := b1.trans (BFrame.of_same m₃ _) fun _ h ↦ h
    have b3 := b2.trans hb₄ fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inr (Or.inr ha))
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha])))
    exact b3.trans (BFrame.of_same m₅ _) fun _ h ↦ h
  have hsub : ∀ a, (Within a (msp + 320) 32 ∨ Within a (msp + 88) 16 ∨
      Within a (msp - 4096) 4096 ∨ Within a (Q + BitVec.ofNat 64 (32 * c)) 32) → Wsib Q h a := by
    intro a ha
    rcases ha with ha | ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (by addr_omega [ha, hc, hQh, hhi])))
  have hnx : heapNext t₅ = heapNext t := by
    have e : t₅.getMem nextAddr = t.getMem nextAddr := hb.getMem (by decide) fun i hi hw ↦ by
      rcases hw with hw | hw | hw | hw <;> addr_omega [hw, hi, hc, hQh, hhi]
    simp only [heapNext, e]
  have hg₅ : PG u₀ t₅ := hg.step hb (fun a ha ↦ Wsib.wf (B := heapNext u₀) (by simp only [heapNext]; omega)
      (by simp only [heapEnd]; omega) (hsub a ha)) hsp₅
    ⟨by rw [hnx]; exact hg.heap.lo, by rw [hnx]; exact hg.heap.hi⟩ (le_of_eq hnx.symm)
  have keepQ : ∀ c' < c, bytesAt t₅ (Q + BitVec.ofNat 64 (32 * c')) 32 =
      bytesAt t (Q + BitVec.ofNat 64 (32 * c')) 32 := by
    intro c' hc'
    exact hb.bytesAt fun i hi hw ↦ by
      rcases hw with hw | hw | hw | hw <;> addr_omega [hw, hi, hc, hc', hQh, hhi, hQ0, hlo0]
  have hnew : digestOfBytes (bytesAt t₅ (Q + BitVec.ofNat 64 (32 * c)) 32) =
      digestOfWords ((words.drop (kh + 4 * c)).take 4) := by
    rw [bytesAt_same m₅, hbytes, digestOfBytes_eq t₂ (by decide), hwords₂]
  have hread : (rep readDigest (c + 1)).run (words.drop kh) = some ((List.range (c + 1)).map
      fun c' ↦ digestOfBytes (bytesAt t₅ (Q + BitVec.ofNat 64 (32 * c')) 32),
      words.drop (kh + 4 * (c + 1))) := by
    rw [rep_step hs.read (readDigest_run (by simp only [List.length_drop]; omega)), List.drop_drop,
      List.range_succ, List.map_append, List.map_singleton, hnew]
    congr 3
    · apply List.map_congr_left
      intro c' hc'
      simp only [List.mem_range] at hc'
      rw [keepQ c' hc']
  have regs₅ : ∀ r ∈ calleeSaved, r ≠ .x20 → r ≠ .x21 → t₅.getReg r = t₀.getReg r := by
    intro r hr h20 h21
    have h5 : r ∈ ([.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15,
        .x16, .x17, .x18, .x19, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31] :
        List Reg) := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | decide | exact absurd rfl h20 | exact absurd rfl h21
    rw [k₅ r h5, hpres₄.reg r hr, k₃ r (mem_of_calleeSaved hr _), hpres₂.reg r hr,
      k₁ r (mem_of_calleeSaved hr _), hs.regs r hr h20 h21]
  have x20₄ : t₄.getReg .x20 = BitVec.ofNat 64 (h - c) := by
    rw [hpres₄.reg .x20 (by decide), k₃ .x20 (by decide), hpres₂.reg .x20 (by decide),
      k₁ .x20 (by decide), hs.x20]
  have x21₄ : t₄.getReg .x21 = Q + BitVec.ofNat 64 (32 * c) := by
    rw [hpres₄.reg .x21 (by decide), k₃ .x21 (by decide), x21₂]
  have mem88 : t₅.getMem (msp + 88) = t₂.getMem (msp + 88) := by
    rw [m₅, hb₄.getMem (by decide) fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hc, hQh, hhi, hQ0, hlo0], m₃]
  have mem96 : t₅.getMem (msp + 96) = t₂.getMem (msp + 96) := by
    rw [m₅, hb₄.getMem (by decide) fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hc, hQh, hhi, hQ0, hlo0], m₃]
  have hS : ∀ e, t₅.pc = e → SbS u₀ words Q h kh t₀ e t₅ (c + 1) := fun e he ↦
    { pg := hg₅
      pc := he
      le := by omega
      regs := regs₅
      x20 := by rw [b80000d6c_x20 h₅, x20₄]; addr_omega [hc, hQh, hhi]
      x21 := by rw [b80000d6c_x21 h₅, x21₄]; addr_omega [hc, hQh, hhi]
      room := by omega
      ptr := by rw [mem88, p₂]
      rest := by rw [mem96, q₂]
      read := hread
      frame := hs.frame.trans hb fun a ha ↦ hsub a ha
      heap := by rw [hnx, hs.heap]
      buf := by rw [← hs.heap]; exact ⟨hQ0, by simp only [heapNext]; omega⟩ }
  have r : Reaches Image.code t t₅ := r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅)))
  by_cases he : c + 1 = h
  · have pc₅ := b80000d6c_pc_not_taken h₅ (by
      rw [x20₄, show h - c = 1 by omega]; rfl)
    exact ⟨t₅, r, Or.inr (Or.inr ⟨he, hS _ pc₅⟩)⟩
  · have pc₅ := b80000d6c_pc_taken h₅ (by rw [x20₄]; addr_omega [hc, he, hQh, hhi])
    exact ⟨t₅, r, Or.inr (Or.inl ⟨by omega, hS _ pc₅⟩)⟩

/-- The siblings' loop. -/
theorem sib_loop (h0 : ParseA s words u₀) {Q : Word} {h kh : Nat} {t₀ : MachineState}
    (hs : SbS u₀ words Q h kh t₀ 0x80000d48 t 0) (hh : 0 < h) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ SbS u₀ words Q h kh t₀ 0x80000d78 v h) := by
  refine Reaches.loop (fun t ↦ ∃ c, c < h ∧ SbS u₀ words Q h kh t₀ 0x80000d48 t c)
    (fun t ↦ (t.getReg .x20).toNat) _ ?_ t ⟨0, hh, hs⟩
  rintro t ⟨c, hc, hsc⟩
  obtain ⟨v, hv, hd | ⟨hl, hsv⟩ | ⟨he, hsv⟩⟩ := sib_body h0 hsc hc
  · exact Or.inl ⟨v, hv, Or.inl hd⟩
  · refine Or.inr ⟨v, hv, ⟨c + 1, hl, hsv⟩, ?_⟩
    have b := hsc.buf.2
    have hhi := hsc.pg.heap.hi
    rw [← hsc.heap] at b
    simp only [heapNext, heapEnd] at b hhi
    rw [hsv.x20, hsc.x20, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · exact Or.inl ⟨v, hv, Or.inr (he ▸ hsv)⟩

end

end Rv64Verifier.Proofs.Main
