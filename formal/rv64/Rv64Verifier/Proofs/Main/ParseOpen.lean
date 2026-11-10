import Rv64Verifier.Proofs.Main.ParsePhaseEnd

/-!
# The openings

From `AtB58`: `0x80000b58` reads the phase count `np` and allocates the openings' buffer
(`try_allocate_in`, 24-byte elements), `0x80000b8c` goes to `0x80000d88` for none, else
`0x80000b9c` saves the counts (`openings_stage`, to `PhS` or `AtD88`); `phase_loop` reads the
phases, to `AtD88`.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode Rv64Verifier.Proofs.End Rv64Verifier.Blocks.F3

section
variable {s u₀ t : MachineState} {words : List Word}

/-- **The phases' loop.** -/
theorem phase_loop (h0 : ParseA s words u₀) {k1 : Nat} {S O : Word} {stream : List E}
    {np B1 k : Nat} {phs : List (List Opening)} (h : PhS u₀ words k1 S O stream np B1 t 0 k phs) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨
      ∃ k' phs', AtD88 u₀ words k1 S O stream np B1 v k' phs') := by
  refine Reaches.loop (fun t ↦ ∃ i k phs, PhS u₀ words k1 S O stream np B1 t i k phs)
    (fun t ↦ np - (t.getReg .x8).toNat) _ ?_ t ⟨0, k, phs, h⟩
  rintro t ⟨i, k, phs, hs⟩
  obtain ⟨b, rb, hd | ⟨P, npi, kj, ops, hb⟩⟩ := phase_head h0 hs
  · exact Or.inl ⟨b, rb, Or.inl hd⟩
  obtain ⟨v, rv, ⟨hl, hv⟩ | ⟨he, hv⟩⟩ := phase_bb0 h0 hs hb
  · refine Or.inr ⟨v, rb.trans rv, ⟨i + 1, kj, phs ++ [ops], hv⟩, ?_⟩
    have b := hs.obuf.2.2
    have hhi := hs.pg.heap.hi
    simp only [heapNext, heapEnd] at b hhi
    rw [hv.x8, hs.x8, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · exact Or.inl ⟨v, rb.trans rv, Or.inr ⟨kj, phs ++ [ops], hv⟩⟩

/-- **The openings' buffer.** -/
theorem openings_stage (h0 : ParseA s words u₀) {k : Nat} {S : Word} {stream : List E}
    (h : AtB58 u₀ words t k S stream) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ ∃ O np, (words.getD k 0).toNat = np ∧
      (AtD88 u₀ words (k + 1) S O stream np (heapNext t) v (k + 1) [] ∨
        PhS u₀ words (k + 1) S O stream np (heapNext t) v 0 (k + 1) [])) := by
  have hg := h.pg
  have hsp := hg.sp
  have hfit := h0.inv.fits
  simp only [inputWords] at hfit
  have hib : inputBase.toNat = 0x10000000 := rfl
  have hhi := hg.heap.hi
  simp only [heapNext, heapEnd] at hhi
  have hin := input_mapped (words := words) (by simp only [inputWords]; exact hfit)
  have hk := h.lt
  -- `0x80000b58`: the phase count, `try_allocate_in`
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b80000b58_spec h.pc (by
    rv_eval [hsp, h.x11]
    and_intros <;> first
      | decide
      | valid_in hin [hib, hk, hfit])
  have k₁ := b80000b58_keeps h₁
  have hsp₁ : t₁.getReg .x2 = msp := by rw [k₁ .x2 (by decide), hsp]
  have hfr₁ := b80000b58_frame h₁ (by rw [hsp]; decide)
  rw [hsp] at hfr₁
  have hg₁ : PG u₀ t₁ := hg.slotWrite (c := 88) hfr₁ (by decide) (by decide) (by decide)
    (by decide) hsp₁
  have hn₁ : heapNext t₁ = heapNext t := by
    simp only [heapNext]; rw [hfr₁ _ (by addr_omega [])]
  set npw := words[k] with hnpw
  set np := npw.toNat with hnp
  have x9₁ : t₁.getReg .x9 = npw := by rw [b80000b58_x9 h₁, h.x11]; exact hg.word h0 hk rfl
  have x8₁ : t₁.getReg .x8 = BitVec.ofNat 64 (words.length - (k + 1)) := by
    rw [b80000b58_x8 h₁, h.x10]; addr_omega [hk, hfit]
  have p88 : t₁.getMem (msp + 88) = inputBase + BitVec.ofNat 64 (8 * (k + 1)) := by
    have e := b80000b58_m_x2_88 h₁
    rw [hsp, h.x11] at e
    rw [e]; addr_omega [hib, hk, hfit]
  have p96 : t₁.getMem (msp + 96) = BitVec.ofNat 64 (words.length - (k + 1)) := by
    have e := b80000b58_m_x2_96 h₁
    rw [hsp, h.x10] at e
    rw [e]; addr_omega [hk, hfit]
  obtain ⟨w, rw', hd | ⟨pcw, regw, hgw, hfw, hmw, -, bufw⟩⟩ := alloc_call hg₁ (b80000b58_pc h₁)
    (by rw [b80000b58_x10 h₁, hsp]) (by rw [b80000b58_x12 h₁]; decide)
    (by rw [b80000b58_x13 h₁]; decide) (by rw [returnAddress, b80000b58_x1 h₁]; decide)
    b80000b84_spec (fun v hv ↦ by rv_eval [hv]; decide)
    (fun _ _ h hc ↦ b80000b84_pc_taken h hc) (fun _ _ h hc ↦ b80000b84_pc_not_taken h hc)
    (fun _ _ h ↦ b80000b84_mem_same h) (fun _ _ h r hr ↦ b80000b84_keeps h r (mem_of_calleeSaved hr _))
  · exact ⟨w, r₁.trans rw', Or.inl hd⟩
  have hspw : w.getReg .x2 = msp := by rw [regw .x2 (by decide), hsp₁]
  rw [b80000b58_x11 h₁, h.x11, hg.word h0 hk rfl, b80000b58_x13 h₁, b80000b58_x12 h₁, ← hnpw,
    ← hnp] at bufw
  set O := w.getMem (msp + 336) with hO
  have hww := hgw.heap.hi
  simp only [heapNext, heapEnd] at hww
  have hO8 : O.toNat % 8 = 0 := bufw.1
  have hOb : 24 * np = 0 ∨ heapNext t ≤ O.toNat ∧ O.toNat + 24 * np ≤ heapNext w := by
    rcases bufw.2 with h' | h'
    · left; rw [toNat_24] at h'; omega
    · right; rw [toNat_24, hn₁] at h'; exact ⟨h'.1, by omega⟩
  -- `0x80000b8c`
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b80000b8c_spec pcw (by rv_eval [hspw, msp]; decide)
  have k₃ := b80000b8c_keeps h₃
  have hsp₃ : t₃.getReg .x2 = msp := by rw [k₃ .x2 (by decide), hspw]
  have hfr₃ := b80000b8c_frame h₃ (by rw [hspw]; decide)
  rw [hspw] at hfr₃
  have hg₃ : PG u₀ t₃ := hgw.slotWrite (c := 64) hfr₃ (by decide) (by decide) (by decide)
    (by decide) hsp₃
  have hn₃ : heapNext t₃ = heapNext w := by
    simp only [heapNext]; rw [hfr₃ _ (by addr_omega [])]
  have s64 : t₃.getMem (msp + 64) = O := by
    have e := b80000b8c_m_x2_64 h₃
    rw [hspw] at e
    exact e
  have keep : ∀ c : Nat, c % 8 = 0 → 24 ≤ c → c + 8 ≤ 64 →
      t₃.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) := by
    intro c h8 h1 h2
    rw [hfr₃ _ (by addr_omega [h1, h2]), Wc.keep hfw (by addr_omega [h8, h1, h2])
      (by addr_omega [h1, h2]) (by addr_omega [h1, h2]), hfr₁ _ (by addr_omega [h1, h2])]
  have s40 : t₃.getMem (msp + 40) = S := (keep 40 (by decide) (by decide) (by decide)).trans h.s40
  have k88 : t₃.getMem (msp + 88) = t₁.getMem (msp + 88) := by
    rw [hfr₃ _ (by addr_omega []), Wc.keep hfw (by decide) (by decide) (by decide)]
  have k96 : t₃.getMem (msp + 96) = t₁.getMem (msp + 96) := by
    rw [hfr₃ _ (by addr_omega []), Wc.keep hfw (by decide) (by decide) (by decide)]
  have hb : BFrame t t₃ fun a ↦ Within a (msp + 88) 16 ∨ Wc (heapNext t₁) a ∨
      Within a (msp + 64) 8 :=
    (((BFrame.of_same (fun _ ↦ rfl) _).trans (BFrame.of_memFrame hfr₁ (by decide) (by decide))
      fun a ha ↦ Or.inl ha).trans hfw fun a ha ↦ Or.inr (Or.inl ha)).trans
      (BFrame.of_memFrame hfr₃ (by decide) (by decide)) fun a ha ↦ Or.inr (Or.inr ha)
  have hsval : eListAt t₃ S stream.length = stream := by
    refine Eq.trans ?_ h.val
    obtain ⟨hS8, hSb⟩ := h.buf
    rcases hSb with h' | h'
    · rw [show stream.length = 0 by omega]; rfl
    · simp only [heapNext] at h'
      refine eListAt_bframe hb hS8 (fun x hx hw ↦ ?_) (by omega)
      rcases hx with hx | ⟨hx | hx | hx | ⟨hx1, hx2⟩⟩ | hx
      · addr_omega [hx, hw, h', hhi]
      · addr_omega [hx, hw, h', hhi]
      · addr_omega [hx, hw, h', hhi]
      · addr_omega [hx, hw, h', hhi]
      · rw [hn₁] at hx1; simp only [heapNext, Within] at hx1 hw; omega
      · addr_omega [hx, hw, h', hhi]
  have x18₃ : t₃.getReg .x18 = BitVec.ofNat 64 stream.length := by
    rw [k₃ .x18 (by decide), regw .x18 (by decide), k₁ .x18 (by decide), h.x18]
  have x9₃ : t₃.getReg .x9 = npw := by rw [k₃ .x9 (by decide), regw .x9 (by decide), x9₁]
  have hmono₃ : heapNext t ≤ heapNext t₃ := by rw [hn₃, ← hn₁]; exact hmw
  have hgk : (words.getD k 0).toNat = np := by
    rw [hnp, hnpw, List.getD_eq_getElem _ _ hk]
  have r : Reaches Image.code t t₃ := r₁.trans (rw'.trans r₃)
  by_cases hz : w.getReg .x9 = 0
  · -- no phases
    have hz' : np = 0 := by rw [regw .x9 (by decide), x9₁] at hz; rw [hnp, hz]; rfl
    refine ⟨t₃, r, Or.inr ⟨O, np, hgk, Or.inl ⟨hg₃, b80000b8c_pc_taken h₃ hz, ?_, ?_, x18₃, s40, s64,
      by omega, ?_, hsval, h.buf, hg.mono, hmono₃, ⟨hO8, Or.inl (by omega)⟩,
      fun i hi ↦ absurd hi (by simp)⟩⟩⟩
    · rw [k₃ .x8 (by decide), regw .x8 (by decide), x8₁]
    · rw [x9₃, hz']; exact (ofNat_toNat' _).symm.trans (by rw [← hnp, hz'])
    · rw [hz']; rfl
  -- `0x80000b9c`
  have hpos : 0 < np := by
    rcases Nat.eq_zero_or_pos np with h' | h'
    · exfalso
      apply hz
      rw [regw .x9 (by decide), x9₁]
      exact BitVec.eq_of_toNat_eq (by rw [← hnp, h']; rfl)
    · exact h'
  have hOb' : heapNext t ≤ O.toNat ∧ O.toNat + 24 * np ≤ heapNext w := hOb.resolve_left (by omega)
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b80000b9c_spec (b80000b8c_pc_not_taken h₃ hz) (by
    rv_eval [hsp₃, msp]; decide)
  have k₄ := b80000b9c_keeps h₄
  have hsp₄ : t₄.getReg .x2 = msp := by rw [k₄ .x2 (by decide), hsp₃]
  have hfr₄ := b80000b9c_frame h₄ (by rw [hsp₃]; decide)
  rw [hsp₃] at hfr₄
  have hg₄ : PG u₀ t₄ := hg₃.slotWrite (c := 24) hfr₄ (by decide) (by decide) (by decide)
    (by decide) hsp₄
  have hn₄ : heapNext t₄ = heapNext w := by
    rw [← hn₃]; simp only [heapNext]; rw [hfr₄ _ (by addr_omega [])]
  have m40 : t₄.getMem (msp + 40) = t₃.getMem (msp + 40) :=
    h₄.frame _ (by rv_eval [hsp₃]; decide)
  have mid : ∀ a, ¬ Within a (msp + 24) 40 → t₄.getMem a = t₃.getMem a := hfr₄
  refine ⟨t₄, r.trans r₄, Or.inr ⟨O, np, hgk, Or.inr ⟨hg₄, b80000b9c_pc h₄, hpos, ?_, ?_, ?_, ?_, ?_,
    by omega, ?_, ?_, ?_, ?_, h.buf, hg.mono, ⟨hO8, hOb'.1, by rw [hn₄]; exact hOb'.2⟩,
    fun i hi ↦ absurd hi (by simp)⟩⟩⟩
  · rw [b80000b9c_x8 h₄]; rfl
  · have e := b80000b9c_m_x2_32 h₄
    rw [hsp₃, x18₃] at e
    exact e
  · rw [m40, s40]
  · have e := b80000b9c_m_x2_56 h₄
    rw [hsp₃, x9₃] at e
    rw [e, hnp, ofNat_toNat']
  · rw [mid _ (by addr_omega []), s64]
  · rw [mid _ (by addr_omega []), k88, p88]
  · rw [mid _ (by addr_omega []), k96, p96, BitVec.toNat_ofNat]; omega
  · rw [rep_zero]
  · rw [show eListAt t₄ S stream.length = eListAt t₃ S stream.length from
      eListAt_memFrame hfr₄ (by
        obtain ⟨-, hSb⟩ := h.buf
        rcases hSb with h' | h'
        · exact Or.inl h'
        · simp only [heapNext] at h'; addr_omega [h', hhi])
        (by obtain ⟨-, hSb⟩ := h.buf; rcases hSb with h' | h' <;> (try simp only [heapNext] at h') <;>
          omega)]
    exact hsval

end

end Rv64Verifier.Proofs.Main
