module

public import NativeRustcVmArm.Wire.Decode.Frame
public import LeanVM.Parameters.Field

/-!
# `decode`'s decoded area

What changes leave of the decoded area: a change outside it or in its words from `lo` (`Out`,
`keepB`, `keepP`). The facts the decoder gathers there (`DecF`): the stream's count and words, the
phase count, the phases read; kept by a change past them (`DecF.keep`); the decoded proof at the
end (`DecF.decodedAt`).
-/

namespace NativeRustcVmArm.Wire.Decode

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeVm.Model
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVm.Transcript (DecArea DecodedAt PhaseAt)
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- An address outside the decoded area. -/
def Out (m0 : MachineData) (q : BitVec 64) : Prop :=
  q.toNat < (decA m0).toNat ∨ (decA m0).toNat + 8 * lenW m0 ≤ q.toNat

/-- **The decoder's facts** in the decoded area: the stream's count and words, the phase count,
the phases read. -/
structure DecF (m0 : MachineData) (d : Mem 64) (n : Nat) (ws : List K) (p : Nat)
    (ps : List PhaseOut) : Prop where
  cnt : WordAt d (dw m0 0) n.toUInt64
  words : WordsAt d (dw m0 1) (ws.map K.lane)
  pc : WordAt d (dw m0 (streamEnd (Ln m0))) p.toUInt64
  phases : ∀ j (h : j < ps.length), PhaseAt d (dw m0 (phaseBase (Ln m0) j)) (phaseW ps[j])

end

public section

variable {m0 : MachineData} {B : List UInt8}

theorem phaseBase_le (L : Nat) {j : Nat} (hj : j ≤ wireMaxPhases) :
    phaseBase L j ≤ decodedWords L := by
  unfold decodedWords phaseBase
  have : j * phaseWords ≤ wireMaxPhases * phaseWords := Nat.mul_le_mul_right _ hj
  omega

theorem phaseBase_le_of (L : Nat) {i j : Nat} (h : i ≤ j) : phaseBase L i ≤ phaseBase L j := by
  unfold phaseBase
  have : i * phaseWords ≤ j * phaseWords := Nat.mul_le_mul_right _ h
  omega

theorem phaseBase_add (L j : Nat) : phaseBase L (j + 1) = phaseBase L j + phaseWords := by
  unfold phaseBase; rw [Nat.succ_mul]; omega

section
variable [Labels]

theorem Geo.dw_toNat (G : Geo m0 B) {i : Nat} (hi : i < lenW m0) :
    (Decode.dw m0 i).toNat = (decA m0).toNat + 8 * i := by
  have := G.dNw
  exact NativeRustcVm.toNat_add_ofNat (a := decA m0) (i := 8 * i) (by omega)

/-- The stack is outside the decoded area. -/
theorem Geo.out_stack (G : Geo m0 B) {q : BitVec 64} (h : InRange (base m0 1280) 1280 q) :
    Out m0 q := by
  have hb := G.base_toNat (F := 1280) le_rfl
  have := G.sp
  have hsD := G.sD
  unfold NativeRustcVm.Apart at hsD
  rw [Sym.inRange_iff (by have := m0.regs.SP.toNat_lt; omega), hb] at h
  unfold Out
  omega

/-- The working area is outside the decoded area. -/
theorem Geo.out_work (G : Geo m0 B) {q : BitVec 64} (h : InRange (wk m0) workBytes q) :
    Out m0 q := by
  have hdW := G.dW
  unfold NativeRustcVm.Apart at hdW
  rw [Sym.inRange_iff G.wNw] at h
  unfold Out
  omega

/-- The frame's bytes are outside the decoded area. -/
theorem Geo.out_frame (G : Geo m0 B) {o n : Nat} (hon : o + n ≤ 96) {q : BitVec 64}
    (h : InRange (base m0 96 + BitVec.ofNat 64 o) n q) : Out m0 q := by
  refine G.out_stack ?_
  have hb := G.base_toNat (F := 96) (by omega)
  have hb' := G.base_toNat (F := 1280) le_rfl
  have := G.sp
  have hSP := m0.regs.SP.toNat_lt
  have ho : (base m0 96 + BitVec.ofNat 64 o).toNat = m0.regs.SP.toNat - 96 + o := by
    rw [NativeRustcVm.toNat_add_ofNat (by omega), hb]
  rw [Sym.inRange_iff (by omega), ho] at h
  rw [Sym.inRange_iff (by omega), hb']
  omega

/-- **Bytes of the decoded area kept** by a change outside it or in its bytes from `lo`. -/
theorem Geo.keepB (G : Geo m0 B) {d d' : Mem 64} {R : BitVec 64 → Prop}
    (hs : SameOutside d d' R) {lo nb : Nat}
    (hR : ∀ q, R q → Out m0 q ∨ InRange (Decode.dw m0 lo) nb q) (hlo : 8 * lo + nb ≤ 8 * lenW m0)
    {o : Nat} {bs : List UInt8} (hb : BytesAt d (Decode.dw m0 o) bs)
    (ho : 8 * o + bs.length ≤ 8 * lenW m0) (hd : 8 * lo + nb ≤ 8 * o ∨ 8 * o + bs.length ≤ 8 * lo) :
    BytesAt d' (Decode.dw m0 o) bs := by
  have hD := G.dNw
  refine NativeRustcVm.BytesAt.of_sameOutside hb hs fun i hi hq ↦ ?_
  have ho' := G.dw_toNat (i := o) (by omega)
  have hq' : (Decode.dw m0 o + BitVec.ofNat 64 i).toNat = (decA m0).toNat + 8 * o + i := by
    rw [NativeRustcVm.toNat_add_ofNat (a := Decode.dw m0 o) (i := i) (by omega), ho']
  rcases hR _ hq with h | h
  · unfold Out at h; omega
  · by_cases hn : nb = 0
    · subst hn; unfold InRange at h; omega
    have hl := G.dw_toNat (i := lo) (by omega)
    rw [Sym.inRange_iff (by omega), hl, hq'] at h
    omega

/-- **A phase of the decoded area kept** by a change outside it or in its bytes from `lo`. -/
theorem Geo.keepP (G : Geo m0 B) {d d' : Mem 64} {R : BitVec 64 → Prop}
    (hs : SameOutside d d' R) {lo nb : Nat}
    (hR : ∀ q, R q → Out m0 q ∨ InRange (Decode.dw m0 lo) nb q) (hlo : 8 * lo + nb ≤ 8 * lenW m0)
    {o : Nat} {ph : Array OpeningW} (hb : PhaseAt d (Decode.dw m0 o) ph)
    (ho : o + phaseWords ≤ lenW m0) (hd : 8 * lo + nb ≤ 8 * o ∨ o + phaseWords ≤ lo) :
    PhaseAt d' (Decode.dw m0 o) ph := by
  have hD := G.dNw
  have hA : NativeRustcVm.Transcript.Agree d d' (Decode.dw m0 o) (8 * phaseWords) fun _ ↦ False := by
    intro j hj _
    refine hs _ fun hq ↦ ?_
    have ho' := G.dw_toNat (i := o) (by omega)
    have hq' : (NativeRustcVm.Transcript.off (Decode.dw m0 o) j).toNat =
        (decA m0).toNat + 8 * o + j := by
      rw [NativeRustcVm.toNat_add_ofNat (a := Decode.dw m0 o) (i := j) (by omega), ho']
    rcases hR _ hq with h | h
    · unfold Out at h; omega
    · by_cases hn : nb = 0
      · subst hn; unfold InRange at h; omega
      have hl := G.dw_toNat (i := lo) (by omega)
      rw [Sym.inRange_iff (by omega), hl, hq'] at h
      omega
  have := NativeRustcVm.Transcript.phaseAt_agree (o := 0) hA (by omega)
    (by rw [NativeRustcVm.Transcript.off_zero]; exact hb)
  rwa [NativeRustcVm.Transcript.off_zero] at this

/-- **The decoder's facts kept** by a change outside the decoded area or past the phases read. -/
theorem DecF.keep (G : Geo m0 B) {d d' : Mem 64} {n : Nat} {ws : List K} {p : Nat}
    {ps : List PhaseOut} (h : DecF m0 d n ws p ps) (hws : ws.length = 2 * n)
    (hn : 1 + 2 * n ≤ streamEnd (Ln m0)) (hps : ps.length ≤ wireMaxPhases)
    {R : BitVec 64 → Prop} (hs : SameOutside d d' R) {lo nb : Nat}
    (hR : ∀ q, R q → Out m0 q ∨ InRange (dw m0 lo) nb q) (hlo : 8 * lo + nb ≤ 8 * lenW m0)
    (hpl : phaseBase (Ln m0) ps.length ≤ lo) : DecF m0 d' n ws p ps := by
  have hdw := G.dLe
  have hbl := phaseBase_le (Ln m0) hps
  have hse : streamEnd (Ln m0) + 1 ≤ phaseBase (Ln m0) ps.length := by unfold phaseBase; omega
  have hdn : decodedWords (Ln m0) = phaseBase (Ln m0) wireMaxPhases := rfl
  have l8 := NativeRustcVm.length_wordBytes
  have lw : ((ws.map K.lane).flatMap NativeRustcVm.wordBytes).length = 8 * (2 * n) := by
    rw [NativeRustcVm.length_wordsBytes, List.length_map, hws]
  refine ⟨G.keepB (o := 0) hs hR hlo h.cnt (by rw [l8]; omega) (.inr (by rw [l8]; omega)),
    G.keepB (o := 1) hs hR hlo h.words (by rw [lw]; omega) (.inr (by rw [lw]; omega)),
    G.keepB (o := streamEnd (Ln m0)) hs hR hlo h.pc (by rw [l8]; omega)
      (.inr (by rw [l8]; omega)),
    fun j hj ↦ G.keepP hs hR hlo (h.phases j hj) ?_ (.inr ?_)⟩
  · have := phaseBase_le (Ln m0) (j := j + 1) (by omega)
    rw [phaseBase_add] at this
    omega
  · have := phaseBase_le_of (Ln m0) (show j + 1 ≤ ps.length by omega)
    rw [phaseBase_add] at this
    omega

end

/-- The stream's elements as the decoded area holds them. -/
theorem streamW_getElem (n : Nat) (ws : List K) (i : Nat) (hi : i < (streamW (streamOf n ws)).size) :
    (streamW (streamOf n ws))[i] = ⟨(ws.getD (2 * i) 0).lane, (ws.getD (2 * i + 1) 0).lane⟩ := by
  simp only [streamW, streamOf, List.getElem_toArray, List.getElem_map, List.getElem_range,
    Model.EW.ofE, LeanVM.Parameters.limb_ofLimbs]
  rfl

theorem streamW_size (n : Nat) (ws : List K) : (streamW (streamOf n ws)).size = n := by
  simp [streamW, streamOf]

/-- **The decoded proof** from the decoder's facts. -/
theorem DecF.decodedAt [Labels] (G : Geo m0 B) {d : Mem 64} {n : Nat} {ws : List K} {p : Nat}
    {ps : List PhaseOut} (h : DecF m0 d n ws p ps) (hws : ws.length = 2 * n)
    (hn : n ≤ maxStream (Ln m0)) (hps : ps.length = p) (hp : p ≤ wireMaxPhases) :
    DecodedAt d (area m0) (streamW (streamOf n ws)) (openingsW ps) := by
  have hL := G.l32
  refine ⟨by show Ln m0 < 2 ^ 64; omega, G.dLe, by rw [streamW_size]; exact hn,
    by rw [streamW_size]; exact h.cnt, fun i hi ↦ ?_, by simp [openingsW, hps, hp],
    by simpa [openingsW, hps] using h.pc, fun j hj ↦ ?_⟩
  · rw [streamW_size] at hi
    rw [streamW_getElem, NativeRustcVm.ewAt_iff]
    have hw := h.words
    have h0 := hw.getElem (i := 2 * i) (by simp [hws]; omega)
    have h1 := hw.getElem (i := 2 * i + 1) (by simp [hws]; omega)
    simp only [List.getElem_map] at h0 h1
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega), Option.getD_some,
      Option.getD_some]
    refine ⟨?_, ?_⟩
    · rw [NativeRustcVm.addr_add_add] at h0
      show WordAt d (decA m0 + BitVec.ofNat 64 (8 * (1 + 2 * i))) _
      rwa [show 8 * (1 + 2 * i) = 8 * 1 + 8 * (2 * i) by ring]
    · rw [NativeRustcVm.addr_add_add] at h1
      show WordAt d (decA m0 + BitVec.ofNat 64 (8 * (1 + 2 * i)) + BitVec.ofNat 64 8) _
      rw [NativeRustcVm.addr_add_add]
      rwa [show 8 * (1 + 2 * i) + 8 = 8 * 1 + 8 * (2 * i + 1) by ring]
  · simp only [openingsW, List.size_toArray, List.length_map] at hj
    simpa [openingsW] using h.phases j hj

end

end NativeRustcVmArm.Wire.Decode
