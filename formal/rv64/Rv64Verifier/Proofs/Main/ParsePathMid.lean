import Rv64Verifier.Proofs.Main.ParsePath

/-!
# A path's siblings

From the leaf (`PaL`, `0x80000cf0`): a word must be left, the height `h`; `0x80000cf4` moves the
input slice past them and allocates the siblings' buffer (`try_allocate_in`, 32 bytes aligned to
1); `0x80000d34` reads the `h` siblings (`sib_loop`), to `0x80000c44` (`path_mid`, to `AtC44`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode Rv64Verifier.Proofs.End Rv64Verifier.Blocks.F3

/-- At `0x80000c44`, path `j` read: its leaf (`l` words at `L`), its `h` siblings at `Q`. -/
structure AtC44 (u₀ : MachineState) (words : List Word) (P : Word) (npi j k : Nat)
    (t₀ : MachineState) (L : Word) (l : Nat) (Q : Word) (h : Nat) (t : MachineState) : Prop where
  start : PaS u₀ words P npi j k 0x80000c7c t₀
  lt : j < npi
  pg : PG u₀ t
  pc : t.pc = 0x80000c44
  x8 : t.getReg .x8 = words.getD k 0
  x18 : t.getReg .x18 = BitVec.ofNat 64 npi
  x19 : t.getReg .x19 = BitVec.ofNat 64 l
  x23 : t.getReg .x23 = P
  x24 : t.getReg .x24 = BitVec.ofNat 64 j
  x25 : t.getReg .x25 = L
  x26 : t.getReg .x26 = BitVec.ofNat 64 h
  x27 : t.getReg .x27 = Q
  room : k + 3 + l + 4 * h ≤ words.length
  ptr : t.getMem (msp + 88) = inputBase + BitVec.ofNat 64 (8 * (k + 3 + l + 4 * h))
  rest : (t.getMem (msp + 96)).toNat = words.length - (k + 3 + l + 4 * h)
  lread : (readList (BF64.ofBitVec <$> readWord)).run (words.drop (k + 1)) =
    some (((words.drop (k + 2)).take l).map BF64.ofBitVec, words.drop (k + 2 + l))
  sread : (readList readDigest).run (words.drop (k + 2 + l)) = some ((List.range h).map fun c ↦
    digestOfBytes (bytesAt t (Q + BitVec.ofNat 64 (32 * c)) 32), words.drop (k + 3 + l + 4 * h))
  leaf : t.readWords L l = (words.drop (k + 2)).take l
  lbuf : InR L (8 * l) 8 (heapNext t₀) (heapNext t)
  qbuf : InR Q (32 * h) 1 (heapNext t₀) (heapNext t)
  frame : BFrame t₀ t (Wpath (heapNext t₀) (P + BitVec.ofNat 64 (56 * j)))
  mono : heapNext t₀ ≤ heapNext t

theorem allOnes_eq : (0xffffffffffffffff : Word) = BitVec.allOnes 64 := by decide

theorem toNat_one : (1 : Word).toNat = 1 := rfl

theorem toNat_32 : (32 : Word).toNat = 32 := rfl

theorem add_xor_ones (a x : Word) : a + (x ^^^ (0xffffffffffffffff : Word)) = a - x - 1 := by
  rw [allOnes_eq, BitVec.xor_allOnes]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_not, toNat_one]
  omega

/-- Words of a buffer that a frame misses. -/
theorem readWords_bframe {t t' : MachineState} {W : Word → Prop} (hf : BFrame t t' W) {L : Word}
    {l : Nat} (hL8 : L.toNat % 8 = 0) (hW : ∀ a, W a → ¬ Within a L (8 * l))
    (hb : L.toNat + 8 * l ≤ 2 ^ 64) : t'.readWords L l = t.readWords L l := by
  rw [readWords_eq_map, readWords_eq_map]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  exact hf.getMem (by addr_omega [hL8, hi, hb]) fun j hj hw ↦ hW _ hw (by addr_omega [hi, hj, hb])

theorem readWords_same {t t' : MachineState} (hm : ∀ a, t'.getMem a = t.getMem a) (a : Word)
    (n : Nat) : t'.readWords a n = t.readWords a n := by
  rw [readWords_eq_map, readWords_eq_map]
  simp only [hm]

section
variable {s u₀ t : MachineState} {words : List Word}

/-- **A path's siblings.** -/
theorem path_mid (h0 : ParseA s words u₀) {P L : Word} {npi j k l : Nat} {t₀ : MachineState}
    (hp : PaL u₀ words P npi j k t₀ L l t) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ ∃ Q h, AtC44 u₀ words P npi j k t₀ L l Q h v) := by
  have hg := hp.pg
  have hsp := hg.sp
  have hfit := h0.inv.fits
  simp only [inputWords] at hfit
  have hib : inputBase.toNat = 0x10000000 := rfl
  have hhi := hg.heap.hi
  have hlo0 := h0.inv.heap.lo
  simp only [heapStart, heapNext, heapEnd] at hlo0 hhi
  have hin := input_mapped (words := words) (by simp only [inputWords]; exact hfit)
  have hkl := hp.room
  have hm0 := hp.mono
  have hlb := hp.lbuf
  -- `0x80000cf0`: a word left
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b80000cf0_spec hp.pc trivial
  by_cases z : t.getReg .x21 = t.getReg .x19
  · obtain ⟨w, hw, hd⟩ := abort (u := t₁) (by rw [b80000cf0_pc_taken h₁ z]; decide)
    exact ⟨w, r₁.trans hw, Or.inl hd⟩
  have hk3 : k + 3 + l ≤ words.length := by
    rw [hp.x21, hp.x19] at z
    by_contra hc
    exact z (by rw [show words.length - (k + 2) = l by omega])
  have k₁ := b80000cf0_keeps h₁
  have m₁ := b80000cf0_mem_same h₁
  have hsp₁ : t₁.getReg .x2 = msp := by rw [k₁ .x2 (by decide), hsp]
  have x9₁ : t₁.getReg .x9 = inputBase + BitVec.ofNat 64 (8 * (k + 2)) := by
    rw [k₁ .x9 (by decide), hp.x9]
  have x10₁ : t₁.getReg .x10 = BitVec.ofNat 64 (8 * l) := by rw [k₁ .x10 (by decide), hp.x10]
  have ea : t₁.getReg .x9 + t₁.getReg .x10 = inputBase + BitVec.ofNat 64 (8 * (k + 2 + l)) := by
    rw [x9₁, x10₁]; addr_omega [hib, hk3, hfit]
  -- `0x80000cf4`: the height, the slice moved, `try_allocate_in`
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b80000cf4_spec (b80000cf0_pc_not_taken h₁ z) (by
    rv_eval [hsp₁, x9₁, x10₁]
    and_intros <;> first
      | decide
      | valid_in hin [hib, hk3, hfit])
  have k₂ := b80000cf4_keeps h₂
  have hsp₂ : t₂.getReg .x2 = msp := by rw [k₂ .x2 (by decide), hsp₁]
  have hg₁ : PG u₀ t₁ := hg.same m₁ hsp₁
  have hfr₂ := b80000cf4_frame h₂ (by rw [hsp₁]; decide)
  rw [hsp₁] at hfr₂
  have hg₂ : PG u₀ t₂ := hg₁.slotWrite (c := 88) hfr₂ (by decide) (by decide) (by decide)
    (by decide) hsp₂
  set hw := words[k + 2 + l] with hhw
  set h := hw.toNat with hh
  have x26₂ : t₂.getReg .x26 = hw := by
    rw [b80000cf4_x26 h₂, ea]; exact hg₁.word h0 (by omega) rfl
  have p88 : t₂.getMem (msp + 88) = inputBase + BitVec.ofNat 64 (8 * (k + 3 + l)) := by
    have e := b80000cf4_m_x2_88 h₂
    rw [hsp₁, ea] at e
    rw [e]; addr_omega [hib, hk3, hfit]
  have p96 : t₂.getMem (msp + 96) = BitVec.ofNat 64 (words.length - (k + 3 + l)) := by
    have e := b80000cf4_m_x2_96 h₂
    rw [hsp₁, k₁ .x21 (by decide), k₁ .x19 (by decide), hp.x21, hp.x19, add_xor_ones] at e
    rw [e]; addr_omega [hk3, hfit]
  have hn₂ : heapNext t₂ = heapNext t := by
    simp only [heapNext]; rw [hfr₂ _ (by addr_omega []), m₁]
  obtain ⟨w, rw', hd | ⟨pcw, regw, hgw, hfw, hmw, -, bufw⟩⟩ := alloc_call hg₂ (b80000cf4_pc h₂)
    (by rw [b80000cf4_x10 h₂, hsp₁]) (by rw [b80000cf4_x12 h₂]; decide)
    (by rw [b80000cf4_x13 h₂]; decide) (by rw [returnAddress, b80000cf4_x1 h₂]; decide)
    b80000d2c_spec (fun v hv ↦ by rv_eval [hv]; decide)
    (fun _ _ h hc ↦ b80000d2c_pc_taken h hc) (fun _ _ h hc ↦ b80000d2c_pc_not_taken h hc)
    (fun _ _ h ↦ b80000d2c_mem_same h) (fun _ _ h r hr ↦ b80000d2c_keeps h r (mem_of_calleeSaved hr _))
  · exact ⟨w, r₁.trans (r₂.trans rw'), Or.inl hd⟩
  have hspw : w.getReg .x2 = msp := by rw [regw .x2 (by decide), hsp₂]
  rw [b80000cf4_x11 h₂, ea, hg₁.word h0 (by omega) rfl, b80000cf4_x13 h₂, b80000cf4_x12 h₂,
    ← hhw, ← hh] at bufw
  set Q := w.getMem (msp + 336) with hQ
  have w88 : w.getMem (msp + 88) = t₂.getMem (msp + 88) := Wc.keep hfw (by decide) (by decide) (by decide)
  have w96 : w.getMem (msp + 96) = t₂.getMem (msp + 96) := Wc.keep hfw (by decide) (by decide) (by decide)
  have hwh := hgw.heap.hi
  simp only [heapNext, heapEnd] at hwh
  have hQb : 32 * h = 0 ∨ heapNext t ≤ Q.toNat ∧ Q.toNat + 32 * h ≤ heapNext w := by
    rcases bufw.2 with h' | h'
    · left; rw [toNat_32] at h'; omega
    · right; rw [toNat_32, hn₂] at h'; exact ⟨h'.1, by omega⟩
  -- the frame so far
  have hb : BFrame t w fun a ↦ Within a (msp + 88) 16 ∨ Wc (heapNext t₂) a :=
    ((BFrame.of_same m₁ _).trans (BFrame.of_memFrame hfr₂ (by decide) (by decide))
      fun a ha ↦ Or.inl ha).trans hfw fun a ha ↦ Or.inr ha
  have hfrw : BFrame t₀ w (Wpath (heapNext t₀) (P + BitVec.ofNat 64 (56 * j))) := by
    refine hp.frame.trans hb fun a ha ↦ ?_
    rcases ha with ha | ha
    · exact Or.inl ha
    · exact Wpath.of_wc (by rw [hn₂]; exact hm0) ha
  have hlw : w.readWords L l = t.readWords L l := by
    obtain ⟨hL8, hLb⟩ := hlb
    rcases hLb with h' | h'
    · rw [show l = 0 by omega]; rfl
    · refine readWords_bframe hb hL8 (fun a ha hw' ↦ ?_) (by simp only [heapNext] at h' hhi; omega)
      simp only [heapNext] at h' hhi
      rcases ha with ha | ha | ha | ha | ⟨ha1, ha2⟩
      · addr_omega [ha, hw', h', hhi]
      · addr_omega [ha, hw', h', hhi]
      · addr_omega [ha, hw', h', hhi]
      · addr_omega [ha, hw', h', hhi]
      · rw [hn₂] at ha1; simp only [heapNext] at ha1; addr_omega [ha1, hw', h', hhi]
  -- `0x80000d34`
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b80000d34_spec pcw (by rv_eval [hspw, msp]; decide)
  have k₄ := b80000d34_keeps h₄
  have m₄ := b80000d34_mem_same h₄
  have hsp₄ : t₄.getReg .x2 = msp := by rw [k₄ .x2 (by decide), hspw]
  have hg₄ : PG u₀ t₄ := hgw.same m₄ hsp₄
  have hn₄ : heapNext t₄ = heapNext w := by simp only [heapNext, m₄]
  have x27₄ : t₄.getReg .x27 = Q := by rw [b80000d34_x27 h₄, hspw]
  have x26w : w.getReg .x26 = hw := by rw [regw .x26 (by decide), x26₂]
  have R : ∀ r ∈ ([.x8, .x18, .x19, .x23, .x24, .x25] : List Reg), t₄.getReg r = t.getReg r := by
    intro r hr
    rw [k₄ r (mem_of_mem hr _), regw r (mem_of_mem hr _), k₂ r (mem_of_mem hr _),
      k₁ r (mem_of_mem hr _)]
  have hsread : (readList readDigest).run (words.drop (k + 2 + l)) =
      (rep readDigest h).run (words.drop (k + 3 + l)) := by
    rw [drop_cons (show k + 2 + l < words.length by omega), readList_run,
      show k + 2 + l + 1 = k + 3 + l by omega]
  have r : Reaches Image.code t t₄ := r₁.trans (r₂.trans (rw'.trans r₄))
  by_cases hz : w.getReg .x26 = 0
  · -- no siblings
    have h0' : h = 0 := by rw [x26w] at hz; rw [hh, hz]; rfl
    refine ⟨t₄, r, Or.inr ⟨Q, h, ⟨hp.start, hp.lt, hg₄, b80000d34_pc_taken h₄ hz, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, x27₄, by omega, ?_, ?_, hp.lread, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
    · rw [R .x8 (by decide), hp.x8]
    · rw [R .x18 (by decide), hp.x18]
    · rw [R .x19 (by decide), hp.x19]
    · rw [R .x23 (by decide), hp.x23]
    · rw [R .x24 (by decide), hp.x24]
    · rw [R .x25 (by decide), hp.x25]
    · rw [k₄ .x26 (by decide), x26w, ofNat_toNat']
    · rw [m₄, w88, p88, h0']; rfl
    · rw [m₄, w96, p96, h0', BitVec.toNat_ofNat]; omega
    · rw [hsread, h0']; rfl
    · rw [readWords_same m₄, hlw, hp.leaf]
    · rw [hn₄]; exact hlb.mono (le_refl _) (by rw [← hn₂]; exact hmw)
    · rw [hn₄]; exact ⟨Nat.mod_one _, Or.inl (by omega)⟩
    · exact hfrw.trans (BFrame.of_same m₄ _) fun _ h ↦ h
    · rw [hn₄]; rw [← hn₂] at hm0; exact le_trans hm0 hmw
  -- the siblings
  have hpos : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h' | h'
    · exact absurd (by rw [x26w]; exact BitVec.eq_of_toNat_eq (by rw [← hh, h']; rfl)) hz
    · exact h'
  have hQb' : heapNext t ≤ Q.toNat ∧ Q.toNat + 32 * h ≤ heapNext w := hQb.resolve_left (by omega)
  obtain ⟨t₅, r₅, h₅⟩ := Sym.BlockSpec.reaches b80000d40_spec (b80000d34_pc_not_taken h₄ hz) trivial
  have k₅ := b80000d40_keeps h₅
  have m₅ := b80000d40_mem_same h₅
  have hsp₅ : t₅.getReg .x2 = msp := by rw [k₅ .x2 (by decide), hsp₄]
  have hn₅ : heapNext t₅ = heapNext w := by simp only [heapNext, m₅]; exact hn₄
  have hS : SbS u₀ words Q h (k + 3 + l) t₅ 0x80000d48 t₅ 0 := {
    pg := hg₄.same m₅ hsp₅
    pc := b80000d40_pc h₅
    le := Nat.zero_le _
    regs := fun _ _ _ _ ↦ rfl
    x20 := by rw [b80000d40_x20 h₅, k₄ .x26 (by decide), x26w, Nat.sub_zero, ofNat_toNat']
    x21 := by
      rw [b80000d40_x21 h₅, x27₄]
      simp only [heapNext] at hQb'
      addr_omega [hQb', hwh]
    room := by omega
    ptr := by rw [m₅, m₄, w88, p88]; rfl
    rest := by rw [m₅, m₄, w96, p96, BitVec.toNat_ofNat]; omega
    read := by rw [rep_zero]; rfl
    frame := BFrame.refl _ _
    heap := rfl
    buf := ⟨by have := hg.mono; simp only [heapNext] at this hQb' ⊢; omega, by rw [hn₅]; exact hQb'.2⟩ }
  obtain ⟨v, rv, hd | hv⟩ := sib_loop h0 hS hpos
  · exact ⟨v, r.trans (r₅.trans rv), Or.inl hd⟩
  obtain ⟨t₆, r₆, h₆⟩ := Sym.BlockSpec.reaches b80000d78_spec hv.pc trivial
  have k₆ := b80000d78_keeps h₆
  have m₆ := b80000d78_mem_same h₆
  have hsp₆ : t₆.getReg .x2 = msp := by rw [k₆ .x2 (by decide), hv.pg.sp]
  have hn₆ : heapNext t₆ = heapNext w := by
    rw [show heapNext t₆ = heapNext v by simp only [heapNext, m₆], hv.heap, hn₅]
  have R6 : ∀ r ∈ ([.x8, .x18, .x19, .x23, .x24, .x25, .x26, .x27] : List Reg),
      t₆.getReg r = t₄.getReg r := by
    intro r hr
    have h20 : r ≠ .x20 := by intro e; subst e; revert hr; decide
    have h21 : r ≠ .x21 := by intro e; subst e; revert hr; decide
    rw [k₆ r (mem_of_mem hr _), hv.regs r (mem_of_mem hr _) h20 h21, k₅ r (mem_of_mem hr _)]
  have hsub : ∀ a, Wsib Q h a → ¬ Within a L (8 * l) := by
    intro a ha hw'
    obtain ⟨-, hLb⟩ := hlb
    simp only [heapNext] at hQb' hwh
    rcases hLb with h' | h'
    · simp only [Within] at hw'; omega
    · simp only [heapNext] at h'
      rcases ha with ha | ha | ha | ha <;> addr_omega [ha, hw', h', hQb', hwh]
  refine ⟨t₆, r.trans (r₅.trans (rv.trans r₆)), Or.inr ⟨Q, h, ⟨hp.start, hp.lt, hv.pg.same m₆ hsp₆,
    b80000d78_pc h₆, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hv.room, ?_, ?_, hp.lread, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
  · rw [R6 .x8 (by decide), R .x8 (by decide), hp.x8]
  · rw [R6 .x18 (by decide), R .x18 (by decide), hp.x18]
  · rw [R6 .x19 (by decide), R .x19 (by decide), hp.x19]
  · rw [R6 .x23 (by decide), R .x23 (by decide), hp.x23]
  · rw [R6 .x24 (by decide), R .x24 (by decide), hp.x24]
  · rw [R6 .x25 (by decide), R .x25 (by decide), hp.x25]
  · rw [R6 .x26 (by decide), k₄ .x26 (by decide), x26w, ofNat_toNat']
  · rw [R6 .x27 (by decide), x27₄]
  · rw [m₆, hv.ptr]
  · rw [m₆, hv.rest]
  · rw [hsread, hv.read]
    congr 2
    · apply List.map_congr_left
      intro c _
      rw [bytesAt_same m₆]
  · rw [readWords_same m₆, readWords_bframe hv.frame hlb.1 hsub (by
        obtain ⟨-, hLb⟩ := hlb; rcases hLb with h' | h' <;> omega),
      readWords_same m₅, readWords_same m₄, hlw, hp.leaf]
  · rw [hn₆]; exact hlb.mono (le_refl _) (by rw [← hn₂]; exact hmw)
  · rw [hn₆]; exact ⟨Nat.mod_one _, Or.inr ⟨le_trans hm0 hQb'.1, hQb'.2⟩⟩
  · refine (((hfrw.trans (BFrame.of_same m₄ _) fun _ h ↦ h).trans (BFrame.of_same m₅ _)
      fun _ h ↦ h).trans hv.frame fun a ha ↦ ?_).trans (BFrame.of_same m₆ _) fun _ h ↦ h
    have := hg.mono
    simp only [heapNext] at hQb' hwh hm0 this
    rcases ha with ha | ha | ha | ha
    · exact Or.inr (Or.inl (by addr_omega [ha]))
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Wpath.heap (by simp only [heapNext]; addr_omega [ha, hQb', hm0])
        (by simp only [heapEnd]; addr_omega [ha, hQb', hwh])
  · rw [hn₆]; rw [← hn₂] at hm0; exact le_trans hm0 hmw

end

end Rv64Verifier.Proofs.Main
