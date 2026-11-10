import Rv64Verifier.Proofs.Pcs.VsoFinalRound

/-!
# `verify_stacked_opening`'s final level: a tail round's challenge pushed

`0x8000b970` keeps the quadratic's value in `s10`, `s11` and `S - 864` and compares the tail
folds' length with their capacity: when full, `grow_one` (`0x8000b988`, back at `0x8000b994`).
`0x8000b998` pushes the challenge from `s0`, `s6`, `s7` and compares the rounds done with `ml`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- Round `i`'s challenge `c` in `s0`, `s6`, `s7`, the quadratic's value at it in `s10`, `s11`,
`S - 864`: at `0x8000b998` with room for `c`, or at `0x8000b988` to grow the tail folds. -/
structure TS (OA : MachineState → Word → Model.TState → Prop) (s : MachineState) (x : LCtx)
    (u v : MachineState) (Wl : Model.Pcs.WhirLocals) (residual : List E) (i : ℕ)
    (q tf : List E) (c : E) : Prop extends TI OA s x u v Wl residual where
  pcr : (v.pc = 0x8000b998 ∧ i < (vecCap v (s.getReg .x2 - 304)).toNat) ∨
    (v.pc = 0x8000b988 ∧ i = (vecCap v (s.getReg .x2 - 304)).toNat)
  ilt : i < mlF s Wl
  tfl : tf.length = i
  x9 : v.getReg .x9 = x.FP
  x18 : v.getReg .x18 = vecPtr v (s.getReg .x2 - 304)
  x19 : v.getReg .x19 = BitVec.ofNat 64 (24 * i)
  x20 : v.getReg .x20 = BitVec.ofNat 64 i
  x21 : v.getReg .x21 = 0xffffffffffffffff
  x24 : v.getReg .x24 = s.getReg .x10
  x25 : v.getReg .x25 = s.getReg .x10 + 8
  m168 : v.getMem (s.getReg .x2 - 872) = BitVec.ofNat 64 (mlF s Wl)
  m224 : v.getMem (s.getReg .x2 - 816) = s.getReg .x10
  tail : TailV s u v tf
  cl : E.ofLimbs (BF64.ofBitVec (v.getReg .x8)) (BF64.ofBitVec (v.getReg .x22))
    (BF64.ofBitVec (v.getReg .x23)) = c
  trg : E.ofLimbs (BF64.ofBitVec (v.getReg .x26)) (BF64.ofBitVec (v.getReg .x27))
    (BF64.ofBitVec (v.getMem (s.getReg .x2 - 864))) = Model.polyEvalRust q c
  value : RunsF OA s v (sampledK (cfgOf s) (basisOf s x) residual Wl (mlF s Wl) i q tf c)

/-- Round `i`'s challenge `c` pushed: at `0x8000b92c` after the last round, at `0x8000b9b8` with
more to come. -/
structure TQ (OA : MachineState → Word → Model.TState → Prop) (s : MachineState) (x : LCtx)
    (u v : MachineState) (Wl : Model.Pcs.WhirLocals) (residual : List E) (i : ℕ)
    (q tf : List E) (c : E) : Prop extends TI OA s x u v Wl residual where
  pcr : (v.pc = 0x8000b92c ∧ i + 1 = mlF s Wl) ∨ (v.pc = 0x8000b9b8 ∧ i + 1 < mlF s Wl)
  tfl : tf.length = i
  x9 : v.getReg .x9 = x.FP
  x12 : v.getReg .x12 = BitVec.ofNat 64 (mlF s Wl)
  x18 : v.getReg .x18 = vecPtr v (s.getReg .x2 - 304)
  x19 : v.getReg .x19 = BitVec.ofNat 64 (24 * i)
  x20 : v.getReg .x20 = BitVec.ofNat 64 (i + 1)
  x21 : v.getReg .x21 = 0xffffffffffffffff
  x24 : v.getReg .x24 = s.getReg .x10
  x25 : v.getReg .x25 = s.getReg .x10 + 8
  m168 : v.getMem (s.getReg .x2 - 872) = BitVec.ofNat 64 (mlF s Wl)
  m224 : v.getMem (s.getReg .x2 - 816) = s.getReg .x10
  tail : TailV s u v (tf ++ [c])
  trg : E.ofLimbs (BF64.ofBitVec (v.getReg .x26)) (BF64.ofBitVec (v.getReg .x27))
    (BF64.ofBitVec (v.getMem (s.getReg .x2 - 864))) = Model.polyEvalRust q c
  value : RunsF OA s v (sampledK (cfgOf s) (basisOf s x) residual Wl (mlF s Wl) i q tf c)

theorem TailV.len {s u v : MachineState} {tf : List E} (h : TailV s u v tf) :
    (vecLen v (s.getReg .x2 - 304)).toNat = tf.length := by
  rw [← h.2.1]; simp only [vecEs, eListAt_length]

theorem ofNat_ne_of_ne {i : ℕ} {w : Word} (hi : i < 2 ^ 64) (h : i ≠ w.toNat) :
    BitVec.ofNat 64 i ≠ w := fun he ↦ h (by rw [← he, BitVec.toNat_ofNat]; omega)

/-- `0x8000b970`. -/
theorem tMove {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
    {u v : MachineState} {Wl : Model.Pcs.WhirLocals} {residual : List E} {i : ℕ} {q tf : List E}
    {c : E} (hpre : VsoPre s) (hp : TP OA s x u v Wl residual i q tf c) :
    ∃ w, Reaches Image.code v w ∧ TS OA s x u w Wl residual i q tf c := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hsp := hp.sp
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000b970_spec hp.pc (by
    rv_eval [hsp]; and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000b970_keeps h₁
  have X₁ : DFrame v t₁ fun a ↦ Within a (s.getReg .x2 - 864) 8 := by
    have := DFrame.of_memFrame (b8000b970_frame h₁ (by rw [hsp]; addr_omega [hb]))
    rw [hsp] at this
    exact this.mono fun a ha ↦ by addr_omega [ha, hb]
  obtain ⟨T₁, n₁⟩ := hp.toTI.stepS hpre X₁ (fun a ha ↦ Or.inl (by addr_omega [ha, hb]))
    (k₁ .x2 (by decide))
  have kw (y : Word) (hy : (s.getReg .x2 - 856).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 104).toNat ∨ (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 864).toNat) : t₁.getMem y = v.getMem y :=
    X₁.word (fun a ha hx ↦ by rcases hy with hy | hy <;> addr_omega [ha, hx, hy, hb])
      (by rcases hy with hy | hy <;> addr_omega [hy, hb])
  have tail₁ : TailV s u t₁ tf := hp.tail.keep hp.heap hp.toTI.fin.su X₁
    (fun a ha hw ↦ by addr_omega [ha, hw, hb])
    (fun a ha ↦ SS.heap hpre (Or.inl (by addr_omega [ha, hb])) hp.heap.hi) (by addr_omega [hb])
    (by simp only [heapNext, n₁]; rfl)
  have hcap : v.getMem (v.getReg .x2 + 736) = vecCap t₁ (s.getReg .x2 - 304) := by
    simp only [vecCap]
    rw [kw _ (Or.inl (by addr_omega [hb])), hsp,
      show s.getReg .x2 - BitVec.ofNat 64 1040 + 736 = s.getReg .x2 - 304 by addr_omega [hb]]
  have hlen := tail₁.len
  have hlc := tail₁.1.len
  have hsm := vec_small tail₁.1 T₁.heap
  rw [hp.tfl] at hlen
  have pcr : (t₁.pc = 0x8000b998 ∧ i < (vecCap t₁ (s.getReg .x2 - 304)).toNat) ∨
      (t₁.pc = 0x8000b988 ∧ i = (vecCap t₁ (s.getReg .x2 - 304)).toNat) := by
    by_cases he : i = (vecCap t₁ (s.getReg .x2 - 304)).toNat
    · exact Or.inr ⟨b8000b970_pc_not_taken h₁ (by
        rw [hp.x20, hcap, he]; simp), he⟩
    · exact Or.inl ⟨b8000b970_pc_taken h₁ (by
        rw [hp.x20, hcap]; exact ofNat_ne_of_ne (by omega) he), by omega⟩
  have e464 : s.getReg .x2 - 464 = v.getReg .x2 + 576 := by rw [hsp]; addr_omega [hb]
  have hpe := hp.pe
  have hch := hp.chal
  unfold eAt at hpe hch
  refine ⟨t₁, r₁, {
    toTI := T₁
    pcr := pcr
    ilt := hp.ilt
    tfl := hp.tfl
    x9 := by rw [k₁ .x9 (by decide), hp.x9]
    x18 := by
      rw [k₁ .x18 (by decide), hp.x18]; simp only [vecPtr]
      exact (kw _ (Or.inl (by addr_omega [hb]))).symm
    x19 := by rw [k₁ .x19 (by decide), hp.x19]
    x20 := by rw [k₁ .x20 (by decide), hp.x20]
    x21 := by rw [k₁ .x21 (by decide), hp.x21]
    x24 := by rw [k₁ .x24 (by decide), hp.x24]
    x25 := by rw [k₁ .x25 (by decide), hp.x25]
    m168 := by rw [kw _ (Or.inr (by addr_omega [hb]))]; exact hp.m168
    m224 := by rw [kw _ (Or.inl (by addr_omega [hb]))]; exact hp.m224
    tail := tail₁
    cl := by
      rw [← hch, k₁ .x8 (by decide), k₁ .x22 (by decide), k₁ .x23 (by decide), ← hp.c0, ← hp.c1,
        ← hp.c2, show s.getReg .x2 - 384 + 8 = s.getReg .x2 - 376 by addr_omega [hb],
        show s.getReg .x2 - 384 + 16 = s.getReg .x2 - 368 by addr_omega [hb]]
    trg := by
      rw [← hpe, b8000b970_x26 h₁, b8000b970_x27 h₁, show s.getReg .x2 - 864 = v.getReg .x2 + 176 by
        rw [hsp]; addr_omega [hb], b8000b970_m_x2_176 h₁, e464,
        show v.getReg .x2 + 576 + 8 = v.getReg .x2 + 584 by addr_omega [hb, hsp],
        show v.getReg .x2 + 576 + 16 = v.getReg .x2 + 592 by addr_omega [hb, hsp]]
    value := hp.value.keep hpre (hp.toTI.inv hpre) X₁ fun a ha ↦ Or.inl (by addr_omega [ha, hb]) }⟩

/-- `0x8000b988`: the tail folds full, `grow_one`, back at `0x8000b994`. -/
theorem tGrow (hG : GrowOneFreshSpec 0x80011c78 24 8)
    {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
    {u v : MachineState} {Wl : Model.Pcs.WhirLocals} {residual : List E} {i : ℕ} {q tf : List E}
    {c : E} (hpre : VsoPre s) (hs : TS OA s x u v Wl residual i q tf c)
    (hpc : v.pc = 0x8000b988) :
    ∃ w, Reaches Image.code v w ∧ (Dead Image.code w ∨
      TS OA s x u w Wl residual i q tf c ∧ w.pc = 0x8000b998) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hab := hst.above
  rw [stackLo_vso] at hab
  have hsp := hs.sp
  have heq : i = (vecCap v (s.getReg .x2 - 304)).toNat := by
    rcases hs.pcr with h | h
    · exact absurd (h.1.symm.trans hpc) (by decide)
    · exact h.2
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000b988_spec hpc trivial
  have k₁ := b8000b988_keeps h₁
  have hm₁ := b8000b988_mem_same h₁
  obtain ⟨T₁, n₁⟩ := hs.toTI.stepS hpre (DFrame.of_same hm₁ (fun _ ↦ False)) (fun _ h ↦ h.elim)
    (k₁ .x2 (by decide))
  have tail₁ : TailV s u t₁ tf := hs.tail.keep hs.heap hs.toTI.fin.su
    (DFrame.of_same hm₁ (fun _ ↦ False)) (fun _ h ↦ h.elim) (fun _ h ↦ h.elim) (by addr_omega [hb])
    (by simp only [heapNext, n₁]; rfl)
  obtain ⟨t₂, r₂, hv₂⟩ := callGrow24 (A := s.getReg .x2 - 304) hG hpre (T₁.inv hpre) T₁.heap
    (b8000b988_pc h₁) (by rw [b8000b988_x10 h₁, hsp]; addr_omega [hb]) (by addr_omega [hb]) tail₁.1
  rcases hv₂ with hd | ⟨hpc₂, hpres₂, hheap₂, hmono₂, X₂, hv₂, he₂, -, hcap₂, hnew₂⟩
  · exact ⟨t₂, r₁.trans r₂, Or.inl hd⟩
  have hhi₂ := hheap₂.hi
  simp only [heapEnd] at hab hhi₂
  have T₂ : TI OA s x u t₂ Wl residual := T₁.trans X₂ (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Nat.le_trans T₁.mono ha.1, ha.2⟩)))))
    hheap₂ hmono₂ (hpres₂ .x2 (by decide))
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := T₂.sp
  have kw (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 304).toNat) : t₂.getMem y = t₁.getMem y :=
    X₂.word (fun a ha hx ↦ by
      rcases hx with hx | hx | hx | hx
      · addr_omega [ha, hx, hy, hb]
      · addr_omega [ha, hx, hy, hb]
      · addr_omega [ha, hx, hy, hb, hnx]
      · simp only [Fresh] at hx; addr_omega [ha, hx.2, hy, hb, hhi₂, hab]) (by addr_omega [hy, hb])
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b8000b994_spec
    (by rw [hpc₂, returnAddress_eq, b8000b988_x1 h₁]; decide)
    (by rv_eval [sp₂]; valid_access hst.valid [hb])
  have k₃ := b8000b994_keeps h₃
  have hm₃ := b8000b994_mem_same h₃
  obtain ⟨T₃, n₃⟩ := T₂.stepS hpre (DFrame.of_same hm₃ (fun _ ↦ False)) (fun _ h ↦ h.elim)
    (k₃ .x2 (by decide))
  have tail₂ : TailV s u t₂ tf := ⟨hv₂, he₂.trans tail₁.2.1, NewBuf.widen hnew₂ T₁.mono⟩
  have tail₃ : TailV s u t₃ tf := tail₂.keep T₂.heap T₂.fin.su
    (DFrame.of_same hm₃ (fun _ ↦ False)) (fun _ h ↦ h.elim) (fun _ h ↦ h.elim) (by addr_omega [hb])
    (by simp only [heapNext, n₃]; rfl)
  have hc₃ : vecCap t₃ (s.getReg .x2 - 304) = vecCap t₂ (s.getReg .x2 - 304) := hm₃ _
  have hc₁ : vecCap t₁ (s.getReg .x2 - 304) = vecCap v (s.getReg .x2 - 304) := hm₁ _
  have hreg (r : Reg) (h3 : t₃.getReg r = t₂.getReg r) (h2 : r ∈ calleeSaved)
      (h1 : t₁.getReg r = v.getReg r) : t₃.getReg r = v.getReg r := by
    rw [h3, hpres₂ r h2, h1]
  have km (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 304).toNat) : t₃.getMem y = v.getMem y := by
    rw [hm₃, kw y hy, hm₁]
  refine ⟨t₃, r₁.trans (r₂.trans r₃), Or.inr ⟨{
    toTI := T₃
    pcr := Or.inl ⟨b8000b994_pc h₃, by rw [hc₃]; rw [hc₁] at hcap₂; omega⟩
    ilt := hs.ilt
    tfl := hs.tfl
    x9 := by rw [hreg .x9 (k₃ .x9 (by decide)) (by decide) (k₁ .x9 (by decide)), hs.x9]
    x18 := by
      rw [b8000b994_x18 h₃, sp₂]; simp only [vecPtr]; rw [hm₃]
      rw [show s.getReg .x2 - BitVec.ofNat 64 1040 + 744 = s.getReg .x2 - 304 + 8 by addr_omega [hb]]
    x19 := by rw [hreg .x19 (k₃ .x19 (by decide)) (by decide) (k₁ .x19 (by decide)), hs.x19]
    x20 := by rw [hreg .x20 (k₃ .x20 (by decide)) (by decide) (k₁ .x20 (by decide)), hs.x20]
    x21 := by rw [hreg .x21 (k₃ .x21 (by decide)) (by decide) (k₁ .x21 (by decide)), hs.x21]
    x24 := by rw [hreg .x24 (k₃ .x24 (by decide)) (by decide) (k₁ .x24 (by decide)), hs.x24]
    x25 := by rw [hreg .x25 (k₃ .x25 (by decide)) (by decide) (k₁ .x25 (by decide)), hs.x25]
    m168 := by rw [km _ (by addr_omega [hb])]; exact hs.m168
    m224 := by rw [km _ (by addr_omega [hb])]; exact hs.m224
    tail := tail₃
    cl := by
      rw [hreg .x8 (k₃ .x8 (by decide)) (by decide) (k₁ .x8 (by decide)),
        hreg .x22 (k₃ .x22 (by decide)) (by decide) (k₁ .x22 (by decide)),
        hreg .x23 (k₃ .x23 (by decide)) (by decide) (k₁ .x23 (by decide))]
      exact hs.cl
    trg := by
      rw [hreg .x26 (k₃ .x26 (by decide)) (by decide) (k₁ .x26 (by decide)),
        hreg .x27 (k₃ .x27 (by decide)) (by decide) (k₁ .x27 (by decide)), km _ (by addr_omega [hb])]
      exact hs.trg
    value := by
      have inv := hs.toTI.inv hpre
      have v₁ := hs.value.keep hpre inv (DFrame.of_same hm₁ (fun _ ↦ False)) fun _ h ↦ h.elim
      have v₂ := v₁.keep hpre (T₁.inv hpre) X₂ fun a ha ↦ by
        rcases ha with ha | ha | ha | ha
        · exact Or.inl (by addr_omega [ha, hb])
        · exact Or.inl (by addr_omega [ha, hb])
        · exact Or.inr (Or.inl ha)
        · simp only [Fresh] at ha
          have := T₁.su
          exact Or.inr (Or.inr (Or.inl ⟨by omega, by simp only [heapEnd]; omega⟩))
      exact v₂.keep hpre (T₂.inv hpre) (DFrame.of_same hm₃ (fun _ ↦ False)) fun _ h ↦ h.elim },
    b8000b994_pc h₃⟩⟩

/-- `0x8000b998`: the challenge pushed. -/
theorem tStore {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
    {u v : MachineState} {Wl : Model.Pcs.WhirLocals} {residual : List E} {i : ℕ} {q tf : List E}
    {c : E} (hpre : VsoPre s) (hs : TS OA s x u v Wl residual i q tf c)
    (hpc : v.pc = 0x8000b998) :
    ∃ w, Reaches Image.code v w ∧ TQ OA s x u w Wl residual i q tf c := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hab := hst.above
  rw [stackLo_vso] at hab
  have hsp := hs.sp
  have hroom : i < (vecCap v (s.getReg .x2 - 304)).toNat := by
    rcases hs.pcr with h | h
    · exact h.2
    · exact absurd (h.1.symm.trans hpc) (by decide)
  obtain ⟨hv, he, hn⟩ := hs.tail
  have hsm := vec_small hv hs.heap
  have hhv := hs.heap.hi
  have hus := hs.toTI.fin.su
  have hhs := hpre.heap.lo
  have hP8 := hn.1
  obtain ⟨hPl, hPh⟩ : heapNext u ≤ (vecPtr v (s.getReg .x2 - 304)).toNat ∧
      (vecPtr v (s.getReg .x2 - 304)).toNat + (vecCap v (s.getReg .x2 - 304)).toNat * 24 ≤
        heapNext v := by
    rcases hn.2 with h0 | h0
    · omega
    · exact h0
  simp only [heapEnd] at hab hhv
  have hPr : Region (vecPtr v (s.getReg .x2 - 304)) ((vecCap v (s.getReg .x2 - 304)).toNat * 24) :=
    heap_region (by simp only [heapStart, heapNext] at hhs hus hPl ⊢; omega)
      (by simp only [heapEnd]; omega) hP8
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000b998_spec hpc (by
    rv_eval [hsp, hs.x18, hs.x19]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hPr (by addr_omega [hroom, hsm, hPh, hhv])
          (by addr_omega [hroom, hsm, hPh, hhv]) (by addr_omega [hroom, hsm, hPh, hhv, hP8])
      | addr_omega [hb, hroom, hsm, hPh, hhv])
  have k₁ := b8000b998_keeps h₁
  have hil : tf.length = i := hs.tfl
  have X : DFrame v t₁ fun a ↦ Within a (s.getReg .x2 - 288) 8 ∨
      Within a (vecPtr v (s.getReg .x2 - 304) + BitVec.ofNat 64 (24 * tf.length)) 24 :=
    (holds_dframe h₁).mono fun a ⟨k, hk, hw⟩ ↦ by
      simp only [b8000b998, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> rv_eval [hsp, hs.x18, hs.x19] at hw
      all_goals first
        | exact Or.inl (by addr_omega [hw, hb])
        | exact Or.inr (by rw [hil]; addr_omega [hw, hroom, hsm, hPh, hhv])
  have nx : t₁.getMem nextAddr = v.getMem nextAddr := X _ fun i hi hw ↦ by
    rcases hw with hw | hw
    · addr_omega [hw, hi, hb, hnx]
    · rw [hil] at hw; addr_omega [hw, hi, hroom, hsm, hPh, hhv, hnx]
  have hn₁ : heapNext t₁ = heapNext v := by simp only [heapNext, nx]
  have m1 := b8000b998_m1 h₁
  have m2 := b8000b998_m2 h₁
  have m3 := b8000b998_m3 h₁
  rw [hs.x18, hs.x19, ← hil] at m1 m2 m3
  have hl : t₁.getMem (s.getReg .x2 - 304 + 16) = BitVec.ofNat 64 (tf.length + 1) := by
    have m := b8000b998_m_x2_752 h₁
    rw [hsp, hs.x20] at m
    rw [show s.getReg .x2 - 304 + 16 = s.getReg .x2 - BitVec.ofNat 64 1040 + 752 by
      addr_omega [hb], m, hil, BitVec.ofNat_add]
    rfl
  have hc : eAt t₁ (vecPtr v (s.getReg .x2 - 304) + BitVec.ofNat 64 (24 * tf.length)) = c := by
    rw [← hs.cl]; unfold eAt; rw [m1, m2, m3]
  have hP := vecE_push hv he X (fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr ha) (by rw [hil]; exact hroom) hl hc (by simp only [heapEnd]; addr_omega [hb, hab])
    (by addr_omega [hb]) hs.heap (by rw [hn₁])
  have T₁ : TI OA s x u t₁ Wl residual := hs.toTI.trans X (fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
      · rw [hil] at ha
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))))
        · addr_omega [ha, hPl, hroom, hsm, hPh, hhv]
        · rw [nx]; simp only [heapNext] at hPh; addr_omega [ha, hroom, hsm, hPh, hhv])
    ⟨by rw [hn₁]; exact hs.heap.lo, by rw [hn₁]; exact hs.heap.hi⟩ (by rw [hn₁])
    (k₁ .x2 (by decide))
  have kw (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 304).toNat) : t₁.getMem y = v.getMem y :=
    X.word (fun a ha hx ↦ by
      rcases hx with hx | hx
      · addr_omega [ha, hx, hy, hb]
      · rw [hil] at hx; addr_omega [ha, hx, hy, hb, hroom, hsm, hPh, hhv, hab])
      (by addr_omega [hy, hb])
  have hml : mlF s Wl < 2 ^ 64 := by have := (s.getReg .x12).isLt; simp only [mlF]; omega
  have hilt := hs.ilt
  have h168 : v.getMem (v.getReg .x2 + 168) = BitVec.ofNat 64 (mlF s Wl) := by
    rw [hsp, show s.getReg .x2 - BitVec.ofNat 64 1040 + 168 = s.getReg .x2 - 872 by
      addr_omega [hb]]; exact hs.m168
  have hx20 : v.getReg .x20 + 1 = BitVec.ofNat 64 (i + 1) := by rw [hs.x20, BitVec.ofNat_add]; rfl
  have hi1 : (BitVec.ofNat 64 (i + 1)).toNat = i + 1 := by rw [BitVec.toNat_ofNat]; omega
  have hm1 : (BitVec.ofNat 64 (mlF s Wl)).toNat = mlF s Wl := by rw [BitVec.toNat_ofNat]; omega
  refine ⟨t₁, r₁, {
    toTI := T₁
    pcr := by
      by_cases hlast : i + 1 = mlF s Wl
      · exact Or.inl ⟨b8000b998_pc_taken h₁ (by rw [h168, hx20, hi1, hm1]; omega), hlast⟩
      · exact Or.inr ⟨b8000b998_pc_not_taken h₁ (by rw [h168, hx20, hi1, hm1]; omega), by omega⟩
    tfl := hs.tfl
    x9 := by rw [k₁ .x9 (by decide), hs.x9]
    x12 := by rw [b8000b998_x12 h₁, h168]
    x18 := by rw [k₁ .x18 (by decide), hs.x18, hP.2.2.1]
    x19 := by rw [k₁ .x19 (by decide), hs.x19]
    x20 := by rw [b8000b998_x20 h₁, hx20]
    x21 := by rw [k₁ .x21 (by decide), hs.x21]
    x24 := by rw [k₁ .x24 (by decide), hs.x24]
    x25 := by rw [k₁ .x25 (by decide), hs.x25]
    m168 := by rw [kw _ (by addr_omega [hb])]; exact hs.m168
    m224 := by rw [kw _ (by addr_omega [hb])]; exact hs.m224
    tail := ⟨hP.1, hP.2.1, by rw [hP.2.2.1, hP.2.2.2]; exact NewBuf.grow hn (by rw [hn₁])⟩
    trg := by
      rw [k₁ .x26 (by decide), k₁ .x27 (by decide), kw _ (by addr_omega [hb])]; exact hs.trg
    value := hs.value.keep hpre (hs.toTI.inv hpre) X fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · rw [hil] at ha
        exact Or.inr (Or.inr (Or.inl ⟨by addr_omega [ha, hPl, hus, hroom, hsm, hPh, hhv],
          by simp only [heapEnd]; addr_omega [ha, hroom, hsm, hPh, hhv]⟩)) }⟩

end Rv64Verifier.Proofs.Pcs.Vso
