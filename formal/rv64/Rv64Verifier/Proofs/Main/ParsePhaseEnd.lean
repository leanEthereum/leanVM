import Rv64Verifier.Proofs.Main.ParsePhase

/-!
# A phase, stored

`0x80000bb0` writes the phase's `Vec<MerklePath>` to slot `i` of the openings' buffer at `O` and
counts `i` up (`phase_bb0`), back to `0x80000be8` or, after the last, through `0x80000d7c` to
`0x80000d88` (`AtD88`); `phase_loop` is all of them.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Proofs.Bytecode Rv64Verifier.Proofs.End Rv64Verifier.Blocks.F3

theorem mul24 (i : Nat) :
    BitVec.ofNat 64 i * 16 + BitVec.ofNat 64 i * 8 = BitVec.ofNat 64 (24 * i) := by
  apply BitVec.eq_of_toNat_eq
  have h16 : (16 : Word).toNat = 16 := rfl
  have h8 : (8 : Word).toNat = 8 := rfl
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    h16, h8]
  omega

/-- Scalars of a buffer that a frame misses. -/
theorem eListAt_bframe {t t' : MachineState} {W : Word → Prop} (hf : BFrame t t' W) {S : Word}
    {n : Nat} (hS8 : S.toNat % 8 = 0) (hW : ∀ a, W a → ¬ Within a S (24 * n))
    (hb : S.toNat + 24 * n ≤ 2 ^ 64) : eListAt t' S n = eListAt t S n := by
  unfold eListAt
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  unfold eAt
  rw [hf.getMem (by addr_omega [hS8, hi, hb]) fun j hj hw ↦ hW _ hw (by addr_omega [hi, hj, hb]),
    hf.getMem (by addr_omega [hS8, hi, hb]) fun j hj hw ↦ hW _ hw (by addr_omega [hi, hj, hb]),
    hf.getMem (by addr_omega [hS8, hi, hb]) fun j hj hw ↦ hW _ hw (by addr_omega [hi, hj, hb])]

section
variable {s u₀ t : MachineState} {words : List Word}

/-- **A phase stored.** -/
theorem phase_bb0 (h0 : ParseA s words u₀) {k1 : Nat} {S O P : Word} {stream : List E}
    {np B1 i k npi kj : Nat} {phs : List (List Opening)} {ops : List Opening} {b : MachineState}
    (h : PhS u₀ words k1 S O stream np B1 t i k phs) (hb : AtBB0 u₀ words O i k t P npi kj ops b) :
    ∃ v, Reaches Image.code b v ∧
      ((i + 1 < np ∧ PhS u₀ words k1 S O stream np B1 v (i + 1) kj (phs ++ [ops])) ∨
       (i + 1 = np ∧ AtD88 u₀ words k1 S O stream np B1 v kj (phs ++ [ops]))) := by
  have hg := hb.pg
  have hsp := hg.sp
  have hhi := hg.heap.hi
  obtain ⟨hO8, hO1, hOn⟩ := h.obuf
  have hmono := hb.mono
  have hlt := h.lt
  have hb1 := h.b1
  have hlo0 := h0.inv.heap.lo
  simp only [heapStart, heapNext, heapEnd] at hhi hOn hmono hb1 hlo0
  have hOm : Mapped O (24 * np) := by simp only [Mapped]; omega
  have s80 := hb.s80
  have s64 : b.getMem (msp + 64) = O := (hb.slots 64 (by decide) (by decide) (by decide)).trans h.s64
  have s56 : b.getMem (msp + 56) = BitVec.ofNat 64 np :=
    (hb.slots 56 (by decide) (by decide) (by decide)).trans h.s56
  set a := O + BitVec.ofNat 64 (24 * i) with ha
  obtain ⟨v, rv, hv⟩ := Sym.BlockSpec.reaches b80000bb0_spec hb.pc (by
    rv_eval [hsp, s80, s64, mul24]
    and_intros <;> first
      | decide
      | valid_in hOm [hO8, hlt, hOn, hhi]
      | addr_omega [hO8, hlt, hOn, hhi, hb1, hlo0, hO1, hmono])
  have hfr : MemFrame b v a 24 := hv.memFrame (by
    rv_eval [hsp, s80, s64, mul24]; and_intros <;> addr_omega [hO8, hlt, hOn, hhi, hmono, ha])
  have kv := b80000bb0_keeps hv
  have hspv : v.getReg .x2 = msp := by rw [kv .x2 (by decide), hsp]
  have hgv : PG u₀ v := hg.heapWrite hfr (by addr_omega [hO8, hlt, hOn, hhi, hmono, ha]) (by decide)
    (by simp only [heapNext]; addr_omega [hO1, hb1, hlt, hOn, hhi, hmono, ha])
    (by simp only [heapNext]; addr_omega [hlt, hOn, hhi, hmono, ha]) hspv
  have hnv : heapNext v = heapNext b := by
    simp only [heapNext]; rw [hfr _ (by addr_omega [hlt, hOn, hhi, hmono, ha])]
  have hbf : BFrame b v (Within · a 24) :=
    BFrame.of_memFrame hfr (by addr_omega [hO8, hlt, hOn, hhi, hmono, ha]) (by decide)
  have hA : O + (BitVec.ofNat 64 i * 16 + BitVec.ofNat 64 i * 8) = a := by rw [mul24]
  have e8 : vecPtr v a = P := by
    have e := b80000bb0_m1 hv
    rw [hsp, s64, s80, hA, hb.x23] at e
    exact e
  have e16 : vecLen v a = BitVec.ofNat 64 npi := by
    have e := b80000bb0_m0 hv
    rw [hsp, s64, s80, hA, hb.x18] at e
    exact e
  obtain ⟨hP8, hPb⟩ := hb.pbuf
  have hnpi : npi < 2 ^ 64 := by
    rcases hPb with h' | h' <;> (try simp only [heapNext] at h') <;> omega
  -- the whole phase's frame
  have hfrv : BFrame t v (Wph (heapNext t) a) :=
    hb.frame.trans hbf fun x hx ↦ Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hx))))
  have hlen := rep_length h.oread
  have hnew : PhaseIn v a ops (O.toNat + 24 * np) (heapNext v) := by
    refine ⟨?_, ?_, fun j hj ↦ ?_⟩
    · rw [e8, e16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnpi, hnv]
      refine ⟨hP8, hPb.imp (fun h' ↦ by omega) fun h' ↦ ⟨?_, h'.2⟩⟩
      simp only [heapNext] at h' ⊢; omega
    · rw [e16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnpi, hb.len]
    · rw [e8]
      have hj' : j < npi := by rw [← hb.len]; exact hj
      rcases hPb with h' | h'
      · omega
      simp only [heapNext] at h'
      refine ((hb.paths j hj).frame hbf (fun x hx ↦ ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩)
        (by addr_omega [h', hj', hhi]) (by addr_omega [h', hj', hhi, hP8])
        (by simp only [heapNext]; omega)).mono (by omega) (by rw [hnv])
      · addr_omega [hx, hw, h', hj', hhi, hlt, hOn, hmono, ha]
      · simp only [heapNext] at hw; addr_omega [hx, hw, h', hj', hhi, hlt, hOn, hmono, ha]
  have hphases : ∀ i' (hi : i' < (phs ++ [ops]).length), PhaseIn v (O + BitVec.ofNat 64 (24 * i'))
      (phs ++ [ops])[i'] (O.toNat + 24 * np) (heapNext v) := by
    intro i' hi
    simp only [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_or_ge i' phs.length with h1 | h1
    · rw [List.getElem_append_left h1]
      have hiv := h.phases i' h1
      have hmt := hb.mono
      refine (hiv.frame hfrv (fun x hx ↦ ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩)
        (by addr_omega [hlt, hOn, hhi, hmono, h1, hlen]) (by addr_omega [hO8, hlt, hOn, hhi, hmono, h1, hlen])
        (by simp only [heapNext] at hmt ⊢; omega)).mono (le_refl _)
        (by rw [hnv]; exact hb.mono)
      · rcases hx with hx | hx | hx | hx | ⟨hx1, hx2⟩ | hx
        · addr_omega [hx, hw, hlt, hOn, hhi, hmono, h1, hlen, hO1, hb1, hlo0]
        · addr_omega [hx, hw, hlt, hOn, hhi, hmono, h1, hlen]
        · addr_omega [hx, hw, hlt, hOn, hhi, hmono, h1, hlen]
        · addr_omega [hx, hw, hlt, hOn, hhi, hmono, h1, hlen]
        · simp only [heapNext] at hx1; addr_omega [hx1, hw, hlt, hOn, hhi, hmono, h1, hlen, hmono]
        · addr_omega [hx, hw, hlt, hOn, hhi, hmono, h1, hlen, ha]
      · rcases hx with hx | hx | hx | hx | ⟨hx1, hx2⟩ | hx
        · addr_omega [hx, hw, hlt, hOn, hhi, hmono, h1, hlen, hO1, hb1, hlo0]
        · addr_omega [hx, hw, hlt, hOn, hhi, hmono, h1, hlen]
        · addr_omega [hx, hw, hlt, hOn, hhi, hmono, h1, hlen]
        · addr_omega [hx, hw, hlt, hOn, hhi, hmono, h1, hlen]
        · simp only [heapNext] at hx1 hw; omega
        · addr_omega [hx, hw, hlt, hOn, hhi, hmono, h1, hlen, ha]
    · have e : i' = phs.length := by omega
      subst e
      rw [List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
      rw [hlen]
      exact hnew
  have hsval : eListAt v S stream.length = stream := by
    refine Eq.trans ?_ h.sval
    obtain ⟨hS8, hSb⟩ := h.sbuf
    rcases hSb with h' | h'
    · rw [show stream.length = 0 by omega]; rfl
    · refine eListAt_bframe hfrv hS8 (fun x hx hw ↦ ?_) (by omega)
      rcases hx with hx | hx | hx | hx | ⟨hx1, hx2⟩ | hx
      · addr_omega [hx, hw, h', hO1, hb1, hlo0, hhi, hOn, hmono]
      · addr_omega [hx, hw, h', hO1, hb1, hlo0, hhi, hOn, hmono]
      · addr_omega [hx, hw, h', hO1, hb1, hlo0, hhi, hOn, hmono]
      · addr_omega [hx, hw, h', hO1, hb1, hlo0, hhi, hOn, hmono]
      · simp only [heapNext, heapEnd, Within] at hx1 hx2 hw h'; omega
      · addr_omega [hx, hw, h', hO1, ha, hlt, hOn, hhi, hmono]
  have hread := rep_step h.oread hb.read
  have K : ∀ c : Nat, c % 8 = 0 → 24 ≤ c → c + 8 ≤ 72 →
      v.getMem (msp + BitVec.ofNat 64 c) = t.getMem (msp + BitVec.ofNat 64 c) := by
    intro c h8 h1 h2
    rw [hfr _ (by addr_omega [h1, h2, hlt, hOn, hhi, hmono, ha]), hb.slots c h8 h1 h2]
  have m88 : v.getMem (msp + 88) = b.getMem (msp + 88) :=
    hfr _ (by addr_omega [hlt, hOn, hhi, hmono, ha])
  have m96 : v.getMem (msp + 96) = b.getMem (msp + 96) :=
    hfr _ (by addr_omega [hlt, hOn, hhi, hmono, ha])
  have x8v : v.getReg .x8 = BitVec.ofNat 64 (i + 1) := by
    rw [b80000bb0_x8 hv, hsp, s80]; addr_omega [hlt, hOn, hhi]
  have x9v : v.getReg .x9 = BitVec.ofNat 64 np := by rw [b80000bb0_x9 hv, hsp, s56]
  by_cases he : i + 1 = np
  · have pcv := b80000bb0_pc_taken hv (by rw [hsp, s80, s56]; addr_omega [he, hOn, hhi])
    obtain ⟨w, rw', hw⟩ := Sym.BlockSpec.reaches b80000d7c_spec pcv (by rv_eval [hspv, msp]; decide)
    have kw := b80000d7c_keeps hw
    have mw := b80000d7c_mem_same hw
    have hspw : w.getReg .x2 = msp := by rw [kw .x2 (by decide), hspv]
    have hnw : heapNext w = heapNext v := by simp only [heapNext, mw]
    refine ⟨w, rv.trans rw', Or.inr ⟨he, ⟨hgv.same mw hspw, b80000d7c_pc hw, ?_, ?_, ?_, ?_, ?_,
      hb.room, ?_, ?_, h.sbuf, h.b1, ?_, ?_, ?_⟩⟩⟩
    · rw [b80000d7c_x8 hw, hspv, m96]
      apply BitVec.eq_of_toNat_eq
      rw [hb.rest, BitVec.toNat_ofNat]
      have := hb.room
      have hf := h0.inv.fits
      simp only [inputWords] at hf
      omega
    · rw [kw .x9 (by decide), x9v]
    · rw [b80000d7c_x18 hw, hspv]
      exact (K 32 (by decide) (by decide) (by decide)).trans h.s32
    · rw [mw]; exact (K 40 (by decide) (by decide) (by decide)).trans h.s40
    · rw [mw]; exact (K 64 (by decide) (by decide) (by decide)).trans h.s64
    · rw [← he]; exact hread
    · rw [show eListAt w S stream.length = eListAt v S stream.length by
        unfold eListAt eAt; simp only [mw]]
      exact hsval
    · rw [hnw, hnv]; simp only [heapNext]; omega
    · rw [hnw, hnv]
      exact ⟨hO8, Or.inr ⟨hO1, by simp only [heapNext]; omega⟩⟩
    · intro i' hi
      have p := hphases i' hi
      have hlen' : i' < np := by
        simp only [List.length_append, List.length_singleton] at hi; omega
      refine (p.frame (BFrame.of_same mw (fun _ ↦ False)) (fun _ h ↦ h.elim)
        (by addr_omega [hlen', hOn, hhi]) (by addr_omega [hO8, hlen', hOn, hhi])
        (by have := hgv.heap.hi; simp only [heapNext, heapEnd] at this ⊢; omega)).mono
        (le_refl _) (by rw [hnw])
  · have pcv := b80000bb0_pc_not_taken hv (by rw [hsp, s80, s56]; addr_omega [he, hlt, hOn, hhi])
    exact ⟨v, rv, Or.inl ⟨by omega, ⟨hgv, pcv, by omega, x8v,
      (K 32 (by decide) (by decide) (by decide)).trans h.s32,
      (K 40 (by decide) (by decide) (by decide)).trans h.s40,
      (K 56 (by decide) (by decide) (by decide)).trans h.s56,
      (K 64 (by decide) (by decide) (by decide)).trans h.s64,
      hb.room, by rw [m88, hb.ptr], by rw [m96, hb.rest], hread, hsval, h.sbuf, h.b1,
      ⟨hO8, hO1, by rw [hnv]; simp only [heapNext]; omega⟩, hphases⟩⟩⟩

end

end Rv64Verifier.Proofs.Main
