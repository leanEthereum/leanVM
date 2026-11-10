import Rv64Verifier.Proofs.Pcs.VsoFold

/-!
# `verify_stacked_opening`'s level loop: into the fold rounds

`0x8000a190` reads the level's fold count and rate, starts `level_folds` empty; `0x8000a1c8` sets
the rounds' registers.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem ofNat_mul8 (a : ℕ) : BitVec.ofNat 64 a * 8 = BitVec.ofNat 64 (8 * a) := by
  rw [Nat.mul_comm, BitVec.ofNat_mul]; rfl

theorem enter {s : MachineState} {x : LCtx} {h : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} (hpre : VsoPre s) (hh : Head s x h ℓ Wl) :
    ∃ u, Reaches Image.code h u ∧ Rnd s x h u ℓ Wl 0 [] Wl.runningQuad := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hf := hh.facts
  obtain ⟨hwF, hwR⟩ := hh.words hpre
  have hsp := hh.sp
  have hlv := hh.lvl
  have hK := K0_lt s
  have hhs := hpre.heap.lo
  have hend := hf.hend
  have hFp := hf.fp
  have hRp := hf.rp
  have hFr : Region x.FP (8 * (K0 s + 2)) :=
    heap_region (by simp only [heapNext, heapStart] at hhs hFp ⊢; omega)
      (by have := hf.hL; omega) hFp.2.2
  have hRr : Region x.RP (8 * (K0 s + 2)) :=
    heap_region (by simp only [heapNext, heapStart] at hhs hRp ⊢; omega)
      (by have := hf.hL; omega) hRp.2.2
  have e5 : h.getReg .x5 * (8 : Word) = BitVec.ofNat 64 (8 * ℓ) := by
    rw [hh.x5, ofNat_mul8]
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000a190_spec hh.pc (by
    rv_eval [hsp, hh.x9, hh.x10, hh.x5]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hFr (by addr_omega [hlv, hK, hFp, hf.hL, hend])
          (by addr_omega [hlv, hK, hFp, hf.hL, hend]) (by addr_omega [hlv, hK, hFp, hf.hL, hend])
      | exact Region.valid hRr (by addr_omega [hlv, hK, hRp, hf.hL, hend])
          (by addr_omega [hlv, hK, hRp, hf.hL, hend]) (by addr_omega [hlv, hK, hRp, hf.hL, hend])
      | addr_omega [hb, hlv, hK, hFp, hRp, hf.hL, hend])
  have k₁ := b8000a190_keeps h₁
  have X₁ : DFrame h t₁ fun a ↦ Within a (s.getReg .x2 - 856) 8 ∨
      Within a (s.getReg .x2 - 832) 16 ∨ Within a (s.getReg .x2 - 784) 8 ∨
      Within a (s.getReg .x2 - 640) 24 :=
    (holds_dframe h₁).mono fun a ⟨k, hk, hw⟩ ↦ by
      simp only [b8000a190, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rv_eval [hsp] at hw
      all_goals first
        | exact Or.inl (by addr_omega [hw, hb])
        | exact Or.inr (Or.inl (by addr_omega [hw, hb]))
        | exact Or.inr (Or.inr (Or.inl (by addr_omega [hw, hb])))
        | exact Or.inr (Or.inr (Or.inr (by addr_omega [hw, hb])))
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := (k₁ .x2 (by decide)).trans hsp
  have hfc : t₁.getReg .x11 = BitVec.ofNat 64 (fcOf s ℓ) := by
    rw [b8000a190_x11 h₁, hh.x9, e5, hwF]
  have hfc0 : 0 < fcOf s ℓ := by rw [fcOf_eq s hlv]; split <;> omega
  have hfc6 : fcOf s ℓ ≤ 6 := by rw [fcOf_eq s hlv]; split <;> omega
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000a1c8_spec
    (b8000a190_pc_not_taken h₁ (by rw [hh.x9, e5, hwF]; addr_omega [hfc0, hfc6])) (by
      rv_eval [sp₁]; valid_access hst.valid [hb])
  have k₂ := b8000a1c8_keeps h₂
  have X₂ : DFrame t₁ t₂ fun a ↦ Within a (s.getReg .x2 - 792) 8 := by
    have := DFrame.of_memFrame (b8000a1c8_frame h₂ (by rw [sp₁]; addr_omega [hb]))
    rw [sp₁] at this
    exact this.mono fun a ha ↦ by addr_omega [ha, hb]
  have X : DFrame h t₂ fun a ↦ Within a (s.getReg .x2 - 856) 8 ∨
      Within a (s.getReg .x2 - 832) 16 ∨ Within a (s.getReg .x2 - 792) 16 ∨
      Within a (s.getReg .x2 - 640) 24 :=
    (X₁.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))
      · exact Or.inr (Or.inr (Or.inr ha))).trans X₂
      fun a ha ↦ Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))
  have hXs (a : Word) (ha : Within a (s.getReg .x2 - 856) 8 ∨
      Within a (s.getReg .x2 - 832) 16 ∨ Within a (s.getReg .x2 - 792) 16 ∨
      Within a (s.getReg .x2 - 640) 24) : Within a (s.getReg .x2 - 1040) 936 := by
    rcases ha with ha | ha | ha | ha <;> addr_omega [ha, hb]
  have nx : t₂.getMem nextAddr = h.getMem nextAddr := X _ fun i hi hw ↦ by
    have := hXs _ hw; addr_omega [this, hi, hb, hnx]
  have hn : heapNext t₂ = heapNext h := by simp only [heapNext, nx]
  -- the values the blocks store
  have hFv := hh.folds
  have hsm := vec_small hFv.vec hh.heap
  have hL0 : (vecLen h (s.getReg .x2 - 688)).toNat = Wl.folds.length := by
    have := congrArg List.length hFv.elems; rw [vecEs, eListAt_length] at this; exact this
  have hx6 : t₁.getReg .x6 = BitVec.ofNat 64 Wl.folds.length := by
    rw [b8000a190_x6 h₁, hsp, ← hL0, ofNat_toNat']; simp only [vecLen]; rv_eval []
  have kp₂ (y : Word) (hy : Apart y 8 (s.getReg .x2 - 792) 8) (hy' : y.toNat + 8 ≤ 2 ^ 64) :
      t₂.getMem y = t₁.getMem y := X₂ y fun i hi hw ↦ by addr_omega [hy, hy', hi, hw]
  have g (o : Word) (v : Word) (hv : t₁.getMem (h.getReg .x2 + o) = v) (y : Word)
      (hy : s.getReg .x2 - BitVec.ofNat 64 1040 + o = y) (hap : Apart y 8 (s.getReg .x2 - 792) 8)
      (hy' : y.toNat + 8 ≤ 2 ^ 64) : t₂.getMem y = v := by
    rw [kp₂ y hap hy', ← hy, ← hsp, hv]
  have m184 := g _ _ (b8000a190_m_x2_184 h₁) (s.getReg .x2 - 856) (by rv_eval [])
    (by addr_omega [hb]) (by addr_omega [hb])
  have m208 := g _ _ (b8000a190_m_x2_208 h₁) (s.getReg .x2 - 832) (by rv_eval [])
    (by addr_omega [hb]) (by addr_omega [hb])
  have m216 := g _ _ (b8000a190_m_x2_216 h₁) (s.getReg .x2 - 824) (by rv_eval [])
    (by addr_omega [hb]) (by addr_omega [hb])
  have m256 := g _ _ (b8000a190_m_x2_256 h₁) (s.getReg .x2 - 784) (by rv_eval [])
    (by addr_omega [hb]) (by addr_omega [hb])
  have m400 := g _ _ (b8000a190_m_x2_400 h₁) (s.getReg .x2 - 640) (by rv_eval [])
    (by addr_omega [hb]) (by addr_omega [hb])
  have m408 := g _ _ (b8000a190_m_x2_408 h₁) (s.getReg .x2 - 640 + 8) (by rv_eval [])
    (by addr_omega [hb]) (by addr_omega [hb])
  have m416 := g _ _ (b8000a190_m_x2_416 h₁) (s.getReg .x2 - 640 + 16) (by rv_eval [])
    (by addr_omega [hb]) (by addr_omega [hb])
  have m248 : t₂.getMem (s.getReg .x2 - 792) = t₁.getReg .x6 + 1 := by
    have := b8000a1c8_m_x2_248 h₂; rw [sp₁] at this; rv_eval [] at this; exact this
  have lfC : vecCap t₂ (s.getReg .x2 - 640) = 0 := m400
  have lfP : vecPtr t₂ (s.getReg .x2 - 640) = 8 := by rw [vecPtr, m408, hh.x17]
  have lfL : vecLen t₂ (s.getReg .x2 - 640) = 0 := m416
  have hinS (a : Word) (ha : Within a (s.getReg .x2 - 856) 8 ∨
      Within a (s.getReg .x2 - 832) 16 ∨ Within a (s.getReg .x2 - 792) 16 ∨
      Within a (s.getReg .x2 - 640) 24) (lo : Nat) (hlo : heapStart ≤ lo) (n : Nat)
      (hn : lo + n ≤ heapEnd) : ¬ (lo ≤ a.toNat ∧ a.toNat < lo + n) := by
    have := hXs a ha; simp only [heapStart, heapEnd] at hlo hn; addr_omega [this, hb, hlo, hn]
  have hFk := vecE_keep X hFv.vec (fun a ha ↦ by
      refine ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩
      · rcases ha with ha | ha | ha | ha <;> addr_omega [ha, hw, hb]
      · have hr := hFv.vec.raw
        simp only [RawVecOk, Buf] at hr
        rcases hr.2 with h0 | h0
        · simp only [Within] at hw; omega
        · exact hinS a ha _ h0.1 _ (by omega) ⟨hw.1, hw.2⟩)
    (by addr_omega [hb]) (by rw [hn]) hh.heap
  have hq := hh.quad
  have hQk : eListAt t₂ (t₂.getReg .x22) (t₂.getReg .x23).toNat = Wl.runningQuad := by
    rw [← hq.1, k₂ .x22 (by decide), k₂ .x23 (by decide), k₁ .x22 (by decide),
      k₁ .x23 (by decide)]
    rcases hq.2.2 with h0 | h0
    · rw [h0]; rfl
    · have hs0 := hf.hs
      have hQlo : heapStart ≤ (h.getReg .x22).toNat := by
        simp only [heapStart, heapNext] at hhs hs0 h0 ⊢; omega
      exact X.eList (fun y hy hw ↦ hinS y hw _ hQlo _ (by omega) ⟨hy.1, hy.2⟩)
        (Or.inr (by simp only [heapEnd] at hend; omega))
  have r22 : t₂.getReg .x22 = h.getReg .x22 := by rw [k₂ .x22 (by decide), k₁ .x22 (by decide)]
  have r23 : t₂.getReg .x23 = h.getReg .x23 := by rw [k₂ .x23 (by decide), k₁ .x23 (by decide)]
  have hap := hh.apart
  refine ⟨t₂, hr₁.trans hr₂, {
    head := hh
    fr := X.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))))
    heap := ⟨by rw [hn]; exact hh.heap.lo, by rw [hn]; exact hh.heap.hi⟩
    mono := by rw [hn]
    pc := b8000a1c8_pc h₂
    sp := (k₂ .x2 (by decide)).trans sp₁
    x6 := by rw [k₂ .x6 (by decide), hx6]
    x9 := by rw [k₂ .x9 (by decide), k₁ .x9 (by decide), hh.x9]
    x18 := by rw [b8000a1c8_x18 h₂, hx6]; addr_omega [hsm, hL0]
    x19 := by rw [b8000a1c8_x19 h₂, lfP]
    x20 := by rw [b8000a1c8_x20 h₂]; rfl
    x21 := by rw [b8000a1c8_x21 h₂]; rfl
    x25 := by rw [k₂ .x25 (by decide), k₁ .x25 (by decide), hh.x25]
    x26 := by rw [k₂ .x26 (by decide), k₁ .x26 (by decide), hh.x26]
    x27 := by rw [k₂ .x27 (by decide), k₁ .x27 (by decide), hh.x27]
    m184 := by rw [m184, hh.x5]
    m208 := by rw [m208, e5]
    m216 := by rw [m216, hh.x10, e5, hwR]
    m248 := by rw [m248, hx6]; addr_omega [hsm, hL0]
    m256 := by rw [m256, hh.x9, e5, hwF]
    jlt := hfc0
    lfl := rfl
    F := ⟨hFk.1, by rw [hFk.2.1, hFv.elems, List.append_nil], Or.inl ⟨hFk.2.2.1, hFk.2.2.2.1⟩⟩
    LF := ⟨⟨⟨by rw [lfP]; decide, Or.inl (by rw [lfC]; rfl)⟩, by rw [lfL, lfC]⟩,
      by simp only [vecEs, lfL]; rfl, ⟨by rw [lfP]; decide, Or.inl (by rw [lfC]; rfl)⟩⟩
    Q := ⟨hQk, by rw [r22]; exact hq.2.1, Or.inl ⟨r22, r23⟩⟩
    ap := ⟨Or.inr (Or.inl (by rw [lfC]; rfl)),
      by rw [hFk.2.2.1, hFk.2.2.2.1, r22, r23]; exact hap.2.1, Or.inl (by rw [lfC]; rfl)⟩
    value := by
      have hv := hh.value
      rw [levelsFrom_eq s x Wl hlv] at hv
      exact hv.keepStk hpre (hh.invR hpre) X hXs }⟩

end Rv64Verifier.Proofs.Pcs.Vso
