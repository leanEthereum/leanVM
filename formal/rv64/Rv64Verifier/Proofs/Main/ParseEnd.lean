import Rv64Verifier.Proofs.Main.ParseOpen

/-!
# The call of `walk`

From `AtD88`: `0x80000d88` aborts unless every word was read, `0x80000d8c` assembles the `Proof` at
`msp + 272` and calls `walk` (`final_stage`, to `AtWalk`); `parse_rest : ParseRest` puts the
stream, the openings and this together.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode Rv64Verifier.Proofs.End Rv64Verifier.Blocks.F3

/-- A part of `main`'s frame, between the `Bytecode` and `walk`'s result. -/
theorem part_msp {v : MachineState} (hsp : v.getReg .x2 = msp) {c n : Nat} (h1 : 104 ≤ c)
    (h2 : c + n ≤ 320) (h8 : c % 8 = 0) : Part v (msp + 320) (msp + BitVec.ofNat 64 c) n 8 := by
  right
  refine ⟨Or.inr ⟨by addr_omega [h1, h2], by addr_omega [h1, h2]⟩, by addr_omega [h1, h2, h8],
    ⟨Or.inr (by simp only [heapEnd]; addr_omega [h1, h2]), by addr_omega [h1, h2]⟩, ?_,
    by simp only [walkOutSize]; addr_omega [h1, h2]⟩
  simp only [stackLo, hsp, walkStack]; addr_omega [h1, h2]

theorem m280 : (msp + 272 + 8 : Word) = msp + 280 := by decide
theorem m288 : (msp + 272 + 16 : Word) = msp + 288 := by decide
theorem m296 : (msp + 272 + 24 : Word) = msp + 296 := by decide
theorem m304 : (msp + 296 + 8 : Word) = msp + 304 := by decide
theorem m312 : (msp + 296 + 16 : Word) = msp + 312 := by decide

theorem decode_table {words : List Word} (h : (words.getD 0 0).toNat + 1 ≤ words.length) :
    (readList (BF64.ofBitVec <$> readWord)).run words =
      some ((tbl words).map BF64.ofBitVec, words.drop ((words.getD 0 0).toNat + 1)) := by
  match words, h with
  | w0 :: rest, h =>
    simp only [List.getD_cons_zero, List.length_cons] at h ⊢
    rw [readList_run, readWords_rep _ _ _ (by omega)]
    simp only [tbl, List.getD_cons_zero, List.drop_succ_cons, List.drop_zero]

theorem decode_digest {words : List Word} {n : Nat} (h : n + 5 ≤ words.length) :
    readDigest.run (words.drop (n + 1)) =
      some (digestOfWords ((words.drop (n + 1)).take 4), words.drop (n + 5)) := by
  rw [readDigest_run (by simp only [List.length_drop]; omega), List.drop_drop]

section
variable {s u₀ t : MachineState} {words : List Word}

/-- **The `Proof`, and the call of `walk`.** -/
theorem final_stage (h0 : ParseA s words u₀) {kB k : Nat} {S O : Word} {stream : List E}
    {np B1 : Nat} {phs : List (List Opening)}
    (hs : (readList readScalar).run (words.drop ((words.getD 0 0).toNat + 5)) =
      some (stream, words.drop kB))
    (hkB : kB < words.length) (hnp : (words.getD kB 0).toNat = np)
    (h : AtD88 u₀ words (kB + 1) S O stream np B1 t k phs) :
    ∃ v, Reaches Image.code t v ∧ (AtWalk s words v ∨ Dead Image.code v) := by
  have hg := h.pg
  have hsp := hg.sp
  have hfit := h0.inv.fits
  simp only [inputWords] at hfit
  have hlen0 := h0.len
  set N := (words.getD 0 0).toNat with hN
  -- `0x80000d88`: nothing left
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b80000d88_spec h.pc trivial
  by_cases z : t.getReg .x8 ≠ 0
  · obtain ⟨w, hw, hd⟩ := abort (u := t₁) (by rw [b80000d88_pc_taken h₁ z]; decide)
    exact ⟨w, r₁.trans hw, Or.inr hd⟩
  rw [not_not] at z
  have hroom := h.room
  have hkL : k = words.length := by
    rw [h.x8] at z
    have := congrArg BitVec.toNat z
    rw [BitVec.toNat_ofNat] at this
    have : (0 : Word).toNat = 0 := rfl
    omega
  have k₁ := b80000d88_keeps h₁
  have m₁ := b80000d88_mem_same h₁
  have hsp₁ : t₁.getReg .x2 = msp := by rw [k₁ .x2 (by decide), hsp]
  -- `0x80000d8c`: the `Proof`, the call
  obtain ⟨v, r₂, h₂⟩ := Sym.BlockSpec.reaches b80000d8c_spec (b80000d88_pc_not_taken h₁ z) (by
    rv_eval [hsp₁, msp]; decide)
  have k₂ := b80000d8c_keeps h₂
  have hspv : v.getReg .x2 = msp := by rw [k₂ .x2 (by decide), hsp₁]
  have hfr₂ := b80000d8c_frame h₂ (by rw [hsp₁]; decide)
  rw [hsp₁] at hfr₂
  have hfr : MemFrame t v (msp + 272) 48 := fun a ha ↦ by rw [hfr₂ a ha, m₁]
  have hbf : BFrame t v (Within · (msp + 272) 48) := BFrame.of_memFrame hfr (by decide) (by decide)
  have hnv : heapNext v = heapNext t := by simp only [heapNext]; rw [hfr _ (by addr_omega [])]
  have hgv : PG u₀ v := hg.step hbf (fun a ha ↦ Wf.out (by addr_omega [ha])) hspv
    ⟨by rw [hnv]; exact hg.heap.lo, by rw [hnv]; exact hg.heap.hi⟩ (le_of_eq hnv.symm)
  have hinv := hgv.minv h0
  have hhi := hgv.heap.hi
  have hlo0 := h0.inv.heap.lo
  have hb1 := h.b1
  have hb1hi := h.b1hi
  rw [← hnv] at hb1hi
  -- the `Proof`'s header
  have e280 : vecPtr v (msp + 272) = S := by
    have e := b80000d8c_m_x2_280 h₂
    rw [hsp₁, m₁, h.s40] at e
    unfold vecPtr; rw [m280]; exact e
  have e288 : vecLen v (msp + 272) = BitVec.ofNat 64 stream.length := by
    have e := b80000d8c_m_x2_288 h₂
    rw [hsp₁, k₁ .x18 (by decide), h.x18] at e
    unfold vecLen; rw [m288]; exact e
  have e304 : vecPtr v (msp + 272 + 24) = O := by
    have e := b80000d8c_m_x2_304 h₂
    rw [hsp₁, m₁, h.s64] at e
    unfold vecPtr; rw [m296, m304]; exact e
  have e312 : vecLen v (msp + 272 + 24) = BitVec.ofNat 64 np := by
    have e := b80000d8c_m_x2_312 h₂
    rw [hsp₁, k₁ .x9 (by decide), h.x9] at e
    unfold vecLen; rw [m296, m312]; exact e
  obtain ⟨hS8, hSb⟩ := h.sbuf
  obtain ⟨hO8, hOb⟩ := h.obuf
  have hn64 : stream.length < 2 ^ 64 := by
    simp only [heapNext, heapEnd] at hhi hb1hi
    rcases hSb with h' | h' <;> omega
  have hnp64 : np < 2 ^ 64 := by
    simp only [heapNext, heapEnd] at hhi
    rcases hOb with h' | h' <;> (try simp only [heapNext] at h') <;> omega
  have hplen := rep_length h.oread
  have hphv : ∀ i (hi : i < phs.length), PhaseIn v (O + BitVec.ofNat 64 (24 * i)) phs[i]
      (O.toNat + 24 * np) (heapNext v) := by
    intro i hi
    rcases hOb with h' | h'
    · omega
    have hht := hg.heap.hi
    simp only [heapNext, heapEnd] at h' hht
    rw [hnv]
    refine (h.phases i hi).frame hbf (fun x hx ↦ ⟨?_, ?_⟩) (by addr_omega [h', hht, hi, hplen])
      (by addr_omega [hO8, h', hht, hi, hplen]) (by simp only [heapNext]; omega)
    · intro hw; addr_omega [hx, hw, h', hht, hi, hplen]
    · intro hw; simp only [heapNext] at hw; addr_omega [hx, hw, h', hht, hi, hplen]
  have hsv : eListAt v S stream.length = stream := by
    refine Eq.trans ?_ h.sval
    rcases hSb with h' | h'
    · rw [show stream.length = 0 by omega]; rfl
    · simp only [heapNext] at h' hhi hb1hi
      exact eListAt_memFrame hfr (by simp only [heapEnd] at hhi; addr_omega [h', hhi, hb1hi])
        (by simp only [heapEnd] at hhi; omega)
  -- the ghost: the input decodes
  have hd₁ := decode_table (words := words) (by omega)
  have hd₂ := decode_digest (words := words) (n := (words.getD 0 0).toNat) hlen0
  have hk' : words[kB].toNat = np := by rw [← List.getD_eq_getElem _ 0 hkB]; exact hnp
  have hd₄ : (readList (readList readOpening)).run (words.drop kB) = some (phs, []) := by
    rw [drop_cons hkB, readList_run, hk', h.oread, hkL, List.drop_length]
  have hdec := decodeInput_of hd₁ hd₂ hs hd₄
  have hx10 : v.getReg .x10 = msp + 320 := by rw [b80000d8c_x10 h₂, hsp₁]
  have hx11 : v.getReg .x11 = msp + 104 := by rw [b80000d8c_x11 h₂, hsp₁]
  have hx12 : v.getReg .x12 = msp + 240 := by rw [b80000d8c_x12 h₂, hsp₁]
  have hx13 : v.getReg .x13 = msp + 272 := by rw [b80000d8c_x13 h₂, hsp₁]
  have hbufs := hgv.bufs h0
  have hst : heapStart ≤ heapNext u₀ := hlo0
  have hO1 : np = 0 ∨ heapStart ≤ O.toNat + 24 * np := by
    rcases hOb with h' | h'
    · left; omega
    · right; simp only [heapStart, heapNext] at h' hlo0 hb1 ⊢; omega
  refine ⟨v, r₁.trans r₂, Or.inl ⟨hinv, b80000d8c_pc h₂, b80000d8c_x1 h₂, hx10, ?_,
    (tbl words).map BF64.ofBitVec, digestOfWords ((words.drop ((words.getD 0 0).toNat + 1)).take 4),
    { stream, openings := phs }, hdec, ?_, ?_, ?_, ?_⟩⟩
  · refine ⟨hgv.heap, rtStack_msp hspv le_rfl (by decide), hinv.rodata, ?_, ?_, ?_, ?_⟩
    · rw [hx10]
      refine ⟨by simp only [Runtime.Mapped, walkOutSize]; decide, by decide,
        ⟨Or.inr (by decide), by simp only [walkOutSize]; addr_omega []⟩, ?_⟩
      simp only [stackLo, hspv, walkStack, walkOutSize]; addr_omega []
    · rw [hx10, hx11]
      refine ⟨part_msp hspv (c := 104) (by decide) (by decide) (by decide),
        part_of_inR hbufs.blocks le_rfl le_rfl hgv.heap hspv, ?_, ?_, ?_⟩
      · rw [msp_128]; exact part_of_inR hbufs.words le_rfl le_rfl hgv.heap hspv
      · rw [msp_152]; exact part_of_inR hbufs.positions le_rfl le_rfl hgv.heap hspv
      · rw [msp_176]; exact part_of_inR hbufs.bytes le_rfl le_rfl hgv.heap hspv
    · rw [hx10, hx12]; exact part_msp hspv (c := 240) (by decide) (by decide) (by decide)
    · rw [hx10, hx13]
      refine ⟨part_msp hspv (c := 272) (by decide) (by decide) (by decide), ?_, ?_, ?_⟩
      · rw [e280, e288, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
        exact part_of_inR ⟨hS8, hSb⟩ hst hb1hi hgv.heap hspv
      · rw [e304, e312, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnp64]
        exact part_of_inR ⟨hO8, hOb⟩ (le_trans hst hb1) (by rw [hnv]) hgv.heap hspv
      · intro i hi
        rw [e312, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnp64] at hi
        rw [e304]
        rcases hO1 with h' | h'
        · omega
        exact (hphv i (by omega)).mem h' le_rfl hgv.heap hspv
  · rw [List.length_map, tbl_length (by omega)]; omega
  · rw [List.map_map, show BF64.toBitVec ∘ BF64.ofBitVec = id from funext BF64.toBitVec_ofBitVec,
      List.map_id, hx11, hgv.bc h0]
    exact h0.bc
  · have h4 : ((words.drop ((words.getD 0 0).toNat + 1)).take 4).length = 4 := by
      simp only [List.length_take, List.length_drop]; omega
    rw [hx12, hgv.pi h0, h0.pi, digestBytes_ofWords _ h4]
  · rw [hx13]
    simp only [readProof, vecEs, e280, e288, e304, e312, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64,
      Nat.mod_eq_of_lt hnp64, hsv]
    congr 1
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, hplen]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      exact (hphv i h2).val

end

/-- **The stream, the openings and the call of `walk`.** -/
theorem parse_rest : ParseRest := by
  intro s words u₀ h0
  obtain ⟨t₁, r₁, hd | ⟨k, S, stream, h₁⟩⟩ := stream_stage h0
  · exact ⟨t₁, r₁, Or.inr hd⟩
  obtain ⟨t₂, r₂, hd | ⟨O, np, hnp, h₂ | h₂⟩⟩ := openings_stage h0 h₁
  · exact ⟨t₂, r₁.trans r₂, Or.inr hd⟩
  · obtain ⟨v, rv, hv⟩ := final_stage h0 h₁.read h₁.lt hnp h₂
    exact ⟨v, r₁.trans (r₂.trans rv), hv⟩
  obtain ⟨t₃, r₃, hd | ⟨k', phs, h₃⟩⟩ := phase_loop h0 h₂
  · exact ⟨t₃, r₁.trans (r₂.trans r₃), Or.inr hd⟩
  obtain ⟨v, rv, hv⟩ := final_stage h0 h₁.read h₁.lt hnp h₃
  exact ⟨v, r₁.trans (r₂.trans (r₃.trans rv)), hv⟩

end Rv64Verifier.Proofs.Main
