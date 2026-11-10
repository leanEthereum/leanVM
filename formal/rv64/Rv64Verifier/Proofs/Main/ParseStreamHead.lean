import Rv64Verifier.Proofs.Main.ParseStream

/-!
# The stream, from `ParseA`

`0x80000aac` to `0x80000adc`: the stream's length and buffer; then the copy loop, or nothing for
an empty stream; `0x80000b4c` or `0x80000e0c` check a word is left (`stream_stage`, to `AtB58`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode Rv64Verifier.Proofs.End Rv64Verifier.Blocks.F3

/-- At `0x80000b58`: the stream read into `S`, `k` words of the input read, at least one left
(`a0` = how many, `a1` = where). -/
structure AtB58 (u₀ : MachineState) (words : List Word) (t : MachineState) (k : Nat) (S : Word)
    (stream : List E) : Prop where
  pg : PG u₀ t
  pc : t.pc = 0x80000b58
  lt : k < words.length
  x10 : t.getReg .x10 = BitVec.ofNat 64 (words.length - k)
  x11 : t.getReg .x11 = inputBase + BitVec.ofNat 64 (8 * k)
  x18 : t.getReg .x18 = BitVec.ofNat 64 stream.length
  s40 : t.getMem (msp + 40) = S
  read : (readList readScalar).run (words.drop ((words.getD 0 0).toNat + 5)) =
    some (stream, words.drop k)
  buf : InR S (24 * stream.length) 8 (heapNext u₀) (heapNext t)
  val : eListAt t S stream.length = stream

theorem eListAt_memFrame {t t' : MachineState} {lo S : Word} {m n : Nat} (hf : MemFrame t t' lo m)
    (hap : Apart S (24 * n) lo m) (hS : S.toNat + 24 * n ≤ 2 ^ 64) :
    eListAt t' S n = eListAt t S n := by
  unfold eListAt
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  exact hf.eAt (by addr_omega [hap, hi, hS]) (by addr_omega [hi, hS])

theorem drop_cons {words : List Word} {k : Nat} (h : k < words.length) :
    words.drop k = words[k] :: words.drop (k + 1) :=
  List.drop_eq_getElem_cons h

theorem toNat_24 : (24 : Word).toNat = 24 := rfl

section
variable {s u₀ : MachineState} {words : List Word}

/-- **The stream**, to `AtB58`. -/
theorem stream_stage (h0 : ParseA s words u₀) :
    ∃ v, Reaches Image.code u₀ v ∧ (Dead Image.code v ∨ ∃ k S stream, AtB58 u₀ words v k S stream) := by
  have hsp := h0.inv.sp
  have hfit := h0.inv.fits
  simp only [inputWords] at hfit
  have hib : inputBase.toNat = 0x10000000 := rfl
  have hlen := h0.len
  set k0 := (words.getD 0 0).toNat + 5 with hk0
  have hg0 : PG u₀ u₀ := ⟨hsp, h0.inv.heap, le_refl _, BFrame.refl _ _⟩
  have hlo0 := h0.inv.heap.lo
  -- `0x80000aac`: a word left
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b80000aac_spec h0.pc (by rv_eval [hsp, msp]; decide)
  have hm96 : u₀.getMem (msp + 96) = BitVec.ofNat 64 (words.length - k0) := by
    apply BitVec.eq_of_toNat_eq
    rw [h0.rest, BitVec.toNat_ofNat]
    omega
  by_cases hz : u₀.getMem (u₀.getReg .x2 + 96) = 0
  · obtain ⟨w, hw, hd⟩ := abort (u := t₁) (by rw [b80000aac_pc_taken h₁ hz]; decide)
    exact ⟨w, r₁.trans hw, Or.inl hd⟩
  have hk : k0 < words.length := by
    rw [hsp, hm96] at hz
    by_contra hc
    exact hz (by rw [show words.length - k0 = 0 by omega]; rfl)
  have pc₁ := b80000aac_pc_not_taken h₁ hz
  have m₁ := b80000aac_mem_same h₁
  have k₁ := b80000aac_keeps h₁
  have x8₁ : t₁.getReg .x8 = BitVec.ofNat 64 (words.length - k0) := by
    rw [b80000aac_x8 h₁, hsp, hm96]
  have hsp₁ : t₁.getReg .x2 = msp := by rw [k₁ .x2 (by decide), hsp]
  have hg₁ : PG u₀ t₁ := hg0.same m₁ hsp₁
  have g88 : t₁.getMem (msp + 88) = inputBase + BitVec.ofNat 64 (8 * k0) := by rw [m₁, h0.ptr]
  -- `0x80000ab4`: the length, and `try_allocate_in`
  have hin := input_mapped (words := words) (by simp only [inputWords]; exact hfit)
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b80000ab4_spec pc₁ (by
    rv_eval [hsp₁, g88]
    and_intros <;> first
      | decide
      | valid_in hin [hib, hk, hfit])
  have m₂ := b80000ab4_mem_same h₂
  have k₂ := b80000ab4_keeps h₂
  have hsp₂ : t₂.getReg .x2 = msp := by rw [k₂ .x2 (by decide), hsp₁]
  have hg₂ := hg₁.same m₂ hsp₂
  have nw₂ : t₂.getReg .x11 = words[k0] := by
    rw [b80000ab4_x11 h₂, hsp₁, g88]; exact hg₁.word h0 hk rfl
  have x18₂ : t₂.getReg .x18 = words[k0] := by
    rw [b80000ab4_x18 h₂, hsp₁, g88]; exact hg₁.word h0 hk rfl
  have x9₂ : t₂.getReg .x9 = inputBase + BitVec.ofNat 64 (8 * k0) := by
    rw [b80000ab4_x9 h₂, hsp₁, g88]
  have x8₂ : t₂.getReg .x8 = BitVec.ofNat 64 (words.length - k0) := by
    rw [k₂ .x8 (by decide), x8₁]
  obtain ⟨w, rw', hd | ⟨pcw, regw, hgw, -, -, -, bufw⟩⟩ := alloc_call hg₂ (b80000ab4_pc h₂)
    (by rw [b80000ab4_x10 h₂, hsp₁]) (by rw [b80000ab4_x12 h₂]; decide)
    (by rw [b80000ab4_x13 h₂]; decide) (by rw [returnAddress, b80000ab4_x1 h₂]; decide)
    b80000ad4_spec (fun v hv ↦ by rv_eval [hv]; decide)
    (fun _ _ h hc ↦ b80000ad4_pc_taken h hc) (fun _ _ h hc ↦ b80000ad4_pc_not_taken h hc)
    (fun _ _ h ↦ b80000ad4_mem_same h) (fun _ _ h r hr ↦ b80000ad4_keeps h r (mem_of_calleeSaved hr _))
  · exact ⟨w, r₁.trans (r₂.trans rw'), Or.inl hd⟩
  have hspw : w.getReg .x2 = msp := by rw [regw .x2 (by decide), hsp₂]
  rw [nw₂, b80000ab4_x13 h₂, b80000ab4_x12 h₂] at bufw
  set nw := words[k0] with hnw
  set S := w.getMem (msp + 336) with hS
  -- `0x80000adc`
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b80000adc_spec pcw (by rv_eval [hspw, msp]; decide)
  have k₄ := b80000adc_keeps h₄
  have hsp₄ : t₄.getReg .x2 = msp := by rw [k₄ .x2 (by decide), hspw]
  have hfr₄ := b80000adc_frame h₄ (by rw [hspw]; decide)
  rw [hspw] at hfr₄
  have hg₄ : PG u₀ t₄ := hgw.slotWrite (c := 48) hfr₄ (by decide) (by decide) (by decide)
    (by decide) hsp₄
  have x7₄ : t₄.getReg .x7 = S := by rw [b80000adc_x7 h₄, hspw]
  have x11₄ : t₄.getReg .x11 = inputBase + BitVec.ofNat 64 (8 * (k0 + 1)) := by
    rw [b80000adc_x11 h₄, regw .x9 (by decide), x9₂]; addr_omega [hib, hk, hfit]
  have x12₄ : t₄.getReg .x12 = BitVec.ofNat 64 (words.length - k0) - 1 := by
    rw [b80000adc_x12 h₄, regw .x8 (by decide), x8₂]
  have x18₄ : t₄.getReg .x18 = nw := by rw [k₄ .x18 (by decide), regw .x18 (by decide), x18₂]
  have hnx₄ : heapNext t₄ = heapNext w := by
    simp only [heapNext]; rw [hfr₄ _ (by addr_omega [])]
  have hS8 : S.toNat % 8 = 0 := bufw.1
  have hread0 : (readList readScalar).run (words.drop k0) =
      (rep readScalar nw.toNat).run (words.drop (k0 + 1)) := by
    rw [drop_cons hk, readList_run]
  have r : Reaches Image.code u₀ t₄ := r₁.trans (r₂.trans (rw'.trans r₄))
  by_cases hn0 : w.getReg .x18 = 0
  · -- an empty stream: `0x80000e0c`
    rw [regw .x18 (by decide), x18₂] at hn0
    have pc₄ := b80000adc_pc_taken h₄ (by rw [regw .x18 (by decide), x18₂]; exact hn0)
    obtain ⟨t₅, r₅, h₅⟩ := Sym.BlockSpec.reaches b80000e0c_spec pc₄ (by rv_eval [hsp₄, msp]; decide)
    by_cases hz5 : t₄.getReg .x12 = 0
    · obtain ⟨w', hw', hd⟩ := abort (u := t₅) (by rw [b80000e0c_pc_not_taken h₅ hz5]; decide)
      exact ⟨w', r.trans (r₅.trans hw'), Or.inl hd⟩
    have hk1 : k0 + 1 < words.length := by
      rw [x12₄] at hz5
      by_contra hc
      exact hz5 (by rw [show words.length - k0 = 1 by omega]; rfl)
    have k₅ := b80000e0c_keeps h₅
    have hsp₅ : t₅.getReg .x2 = msp := by rw [k₅ .x2 (by decide), hsp₄]
    have hfr₅ := b80000e0c_frame h₅ (by rw [hsp₄]; decide)
    rw [hsp₄] at hfr₅
    have hg₅ : PG u₀ t₅ := hg₄.slotWrite (c := 40) hfr₅
      (by decide) (by decide) (by decide) (by decide) hsp₅
    refine ⟨t₅, r.trans r₅, Or.inr ⟨k0 + 1, S, [], ⟨hg₅, b80000e0c_pc_taken h₅ hz5, hk1, ?_, ?_, ?_,
      ?_, ?_, ⟨hS8, Or.inl rfl⟩, rfl⟩⟩⟩
    · rw [b80000e0c_x10 h₅, x12₄]; addr_omega [hk1, hfit]
    · rw [k₅ .x11 (by decide), x11₄]
    · rw [k₅ .x18 (by decide), x18₄, hn0]; rfl
    · have e := b80000e0c_m_x2_40 h₅
      rw [hsp₄, x7₄] at e
      exact e
    · rw [hread0, hn0]; rfl
  · -- the copy loop
    have hn0' : nw ≠ 0 := by rw [regw .x18 (by decide), x18₂] at hn0; exact hn0
    have pc₄ := b80000adc_pc_not_taken h₄ (by rw [regw .x18 (by decide), x18₂]; exact hn0')
    obtain ⟨t₆, r₆, h₆⟩ := Sym.BlockSpec.reaches b80000af4_spec pc₄ trivial
    have k₆ := b80000af4_keeps h₆
    have m₆ := b80000af4_mem_same h₆
    have hsp₆ : t₆.getReg .x2 = msp := by rw [k₆ .x2 (by decide), hsp₄]
    have hn : 0 < nw.toNat := by
      rcases Nat.eq_zero_or_pos nw.toNat with h' | h'
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h']; rfl)) hn0'
      · exact h'
    have hnx₆ : heapNext t₆ = heapNext w := by simp only [heapNext, m₆]; exact hnx₄
    have hbuf : S.toNat % 8 = 0 ∧ heapNext u₀ ≤ S.toNat ∧ S.toNat + 24 * nw.toNat ≤ heapNext t₆ := by
      rcases bufw.2 with h' | h'
      · rw [toNat_24] at h'; omega
      · have := hg₂.mono
        rw [toNat_24] at h'
        rw [hnx₆]
        exact ⟨hS8, by omega, by omega⟩
    have hL : SLoop u₀ words k0 nw S (t₆.getReg .x10) t₆ 0 := {
      pg := hg₄.same m₆ hsp₆
      pc := b80000af4_pc h₆
      lt := hn
      room := by omega
      x7 := by rw [k₆ .x7 (by decide), x7₄]
      x10 := rfl
      x11 := by rw [k₆ .x11 (by decide), x11₄]
      x12 := by rw [k₆ .x12 (by decide), x12₄]; addr_omega [hk, hfit]
      x13 := by rw [b80000af4_x13 h₆, x7₄]; rfl
      x14 := b80000af4_x14 h₆
      x15 := b80000af4_x15 h₆
      x16 := by rw [b80000af4_x16 h₆, x18₄]; simp
      x18 := by rw [k₆ .x18 (by decide), x18₄]
      read := by simp only [Nat.mul_zero, Nat.add_zero]; rfl
      buf := hbuf }
    have hX : t₆.getReg .x10 =
        BitVec.ofNat 64 (words.length - k0) - 1 - nw - nw * 2 := by
      rw [b80000af4_x10 h₆, x12₄, x18₄]
    obtain ⟨v, rv, hd | he⟩ := stream_loop h0 hL
    · exact ⟨v, r.trans (r₆.trans rv), Or.inl hd⟩
    -- `0x80000b4c`: a word left
    have hgv := he.pg
    have hspv := hgv.sp
    have hroom := he.room
    have hbv := he.buf
    have hhv := hgv.heap.hi
    simp only [heapNext, heapEnd] at hbv hhv
    obtain ⟨t₇, r₇, h₇⟩ := Sym.BlockSpec.reaches b80000b4c_spec he.pc (by rv_eval [hspv, msp]; decide)
    have hXv : v.getReg .x10 = BitVec.ofNat 64 (words.length - (k0 + 1 + 3 * nw.toNat)) := by
      rw [he.x10, hX]; addr_omega [hroom, hfit, hk]
    by_cases hz7 : v.getReg .x10 = 0
    · obtain ⟨w', hw', hd⟩ := abort (u := t₇) (by rw [b80000b4c_pc_taken h₇ hz7]; decide)
      exact ⟨w', r.trans (r₆.trans (rv.trans (r₇.trans hw'))), Or.inl hd⟩
    have hk2 : k0 + 1 + 3 * nw.toNat < words.length := by
      rw [hXv] at hz7
      by_contra hc
      exact hz7 (by rw [show words.length - (k0 + 1 + 3 * nw.toNat) = 0 by omega]; rfl)
    have k₇ := b80000b4c_keeps h₇
    have hsp₇ : t₇.getReg .x2 = msp := by rw [k₇ .x2 (by decide), hspv]
    have hfr₇ := b80000b4c_frame h₇ (by rw [hspv]; decide)
    rw [hspv] at hfr₇
    have hg₇ : PG u₀ t₇ := hgv.slotWrite (c := 40) hfr₇
      (by decide) (by decide) (by decide) (by decide) hsp₇
    have hval : eListAt t₇ S nw.toNat = eListAt v S nw.toNat :=
      eListAt_memFrame hfr₇ (by addr_omega [hbv, hhv]) (by omega)
    have hnx₇ : heapNext t₇ = heapNext v := by
      simp only [heapNext]; rw [hfr₇ _ (by addr_omega [])]
    refine ⟨t₇, r.trans (r₆.trans (rv.trans r₇)), Or.inr ⟨k0 + 1 + 3 * nw.toNat, S,
      eListAt v S nw.toNat, ⟨hg₇, b80000b4c_pc_not_taken h₇ hz7, hk2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
    · rw [k₇ .x10 (by decide), hXv]
    · rw [b80000b4c_x11 h₇, he.x17]
    · rw [k₇ .x18 (by decide), he.x18, eListAt_length, ofNat_toNat']
    · have e := b80000b4c_m_x2_40 h₇
      rw [hspv, he.x7] at e
      exact e
    · rw [hread0, he.read]
    · rw [eListAt_length, hnx₇]
      exact ⟨hbv.1, Or.inr ⟨hbv.2.1, hbv.2.2⟩⟩
    · rw [eListAt_length, hval]

end

end Rv64Verifier.Proofs.Main
