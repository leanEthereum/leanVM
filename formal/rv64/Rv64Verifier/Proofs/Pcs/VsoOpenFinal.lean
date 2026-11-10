import Rv64Verifier.Proofs.Pcs.VsoOpen304

/-!
# `verify_stacked_opening`'s level loop: the last level's residual

At the last level `0x8000a37c` keeps the root's bytes `7..31` in the callee-saved registers and
spills (`B37`), calls `next_scalars(2^ml)` into `S - 384`, returns its `Err` (`0x8000a430`,
`0x8000b86c`), and `0x8000a448` reassembles the bytes into the next root's doublewords: at the
last level the next root is the root itself.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The invariant through the opening's steps -/

/-- A step writing only the frame below the saved registers keeps the invariant. -/
theorem InvR.stk {s t v : MachineState} {X : Word → Prop} (hpre : VsoPre s)
    (hinv : InvR s t (t.getMem nextAddr)) (hX : DFrame t v X)
    (hXs : ∀ a, X a → Within a (s.getReg .x2 - 1040) 936) (hsp : v.getReg .x2 = t.getReg .x2) :
    v.getMem nextAddr = t.getMem nextAddr ∧ InvR s v (v.getMem nextAddr) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have e : v.getMem nextAddr = t.getMem nextAddr := hX _ fun i hi hw ↦ by
    have := hXs _ hw; addr_omega [this, hi, hb, hnx]
  refine ⟨e, ?_⟩
  rw [e]
  exact Inv.step' hpre hinv hX (fun a ha ↦ Or.inr (Or.inl (in_stack hpre (by
      have := hXs a ha; addr_omega [this, hb])))) (fun a ha ↦ by
      have := hXs a ha; addr_omega [this, hb]) e (le_refl _) hinv.fits hsp

/-- A transcript callee's frame keeps the invariant. -/
theorem InvR.callT {s t v : MachineState} {o : Word} (hpre : VsoPre s)
    (hinv : InvR s t (t.getMem nextAddr))
    (hX : DFrame t v fun a ↦ Within a o 24 ∨ Within a (s.getReg .x10 + 8) 344 ∨
      Within a (s.getReg .x2 - 2464) 1424 ∨ Within a nextAddr 8 ∨ Fresh t v a)
    (ho : Slot24 s o) (hheap : HeapOk v) (hmono : heapNext t ≤ heapNext v)
    (hsp : v.getReg .x2 = t.getReg .x2) : InvR s v (v.getMem nextAddr) := by
  have hb := bounds hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  simp only [Slot24] at ho
  have hsu : heapNext s ≤ heapNext t := by
    have hn : heapNext t = (t.getMem nextAddr).toNat := rfl
    rw [hn]; exact hinv.mono
  refine Inv.step' hpre hinv hX (fun a ha ↦ ?_) (fun a ha ↦ ?_) rfl hmono hheap.hi hsp
  · rcases ha with ha | ha | ha | ha | ha
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, ho, hb])))
    · exact Or.inl (Or.inl (by simp only [W]; addr_omega [ha, hS]))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inr (Or.inl ha))
    · simp only [Fresh] at ha
      exact Or.inr (Or.inr (Or.inr ⟨by omega, ha.2⟩))
  · rcases ha with ha | ha | ha | ha | ha
    · addr_omega [ha, ho, hb]
    · addr_omega [ha, hS, hIs, hb]
    · addr_omega [ha, hb]
    · obtain ⟨hnx, -⟩ := sfacts hpre; addr_omega [ha, hb, hnx]
    · simp only [Fresh] at ha; have := hheap.hi; addr_omega [ha.2, hb, this]

/-! ## The root's bytes `7..31` -/

/-- A byte of `w`, zero-extended. -/
abbrev zb (w : Word) (j : ℕ) : Word := BitVec.zeroExtend 64 (extractByte w j)

/-- After `0x8000a37c`: the root's bytes `7..31` (of its doublewords `w0`..`w3`) in the
callee-saved registers and the spills from `P + 8`. -/
structure B37 (u : MachineState) (P w0 w1 w2 w3 : Word) : Prop where
  x8 : u.getReg .x8 = zb w3 7
  x18 : u.getReg .x18 = zb w3 3
  x19 : u.getReg .x19 = zb w3 1
  x20 : u.getReg .x20 = zb w2 6
  x21 : u.getReg .x21 = zb w2 4
  x22 : u.getReg .x22 = zb w2 1
  x23 : u.getReg .x23 = zb w2 2
  x24 : u.getReg .x24 = zb w2 0
  x25 : u.getReg .x25 = zb w3 6
  x26 : u.getReg .x26 = zb w3 5
  x27 : u.getReg .x27 = zb w3 2
  m48 : u.getMem (P + 48#64) = zb w1 6
  m56 : u.getMem (P + 56#64) = zb w1 5
  m40 : u.getMem (P + 40#64) = zb w1 4
  m64 : u.getMem (P + 64#64) = zb w1 3
  m24 : u.getMem (P + 24#64) = zb w1 2
  m32 : u.getMem (P + 32#64) = zb w1 1
  m16 : u.getMem (P + 16#64) = zb w1 0
  m72 : u.getMem (P + 72#64) = zb w0 7
  m8 : u.getMem (P + 8#64) = zb w2 5
  m80 : u.getMem (P + 80#64) = zb w2 3
  m88 : u.getMem (P + 88#64) = zb w1 7
  m96 : u.getMem (P + 96#64) = zb w3 4
  m104 : u.getMem (P + 104#64) = zb w3 0
  m120 : u.getMem (P + 120#64) = zb w2 7

theorem b37_of {u t : MachineState} (h : b8000a37c.Holds u t) :
    B37 t (u.getReg .x2) (u.getMem (u.getReg .x16)) (u.getMem (u.getReg .x16 + 8#64))
      (u.getMem (u.getReg .x16 + 16#64)) (u.getMem (u.getReg .x16 + 24#64)) where
  x8 := h.reg_eq .x8 rfl (by rv_eval [])
  x18 := h.reg_eq .x18 rfl (by rv_eval [])
  x19 := h.reg_eq .x19 rfl (by rv_eval [])
  x20 := h.reg_eq .x20 rfl (by rv_eval [])
  x21 := h.reg_eq .x21 rfl (by rv_eval [])
  x22 := h.reg_eq .x22 rfl (by rv_eval [])
  x23 := h.reg_eq .x23 rfl (by rv_eval [])
  x24 := h.reg_eq .x24 rfl (by rv_eval [])
  x25 := h.reg_eq .x25 rfl (by rv_eval [])
  x26 := h.reg_eq .x26 rfl (by rv_eval [])
  x27 := h.reg_eq .x27 rfl (by rv_eval [])
  m48 := h.mem_eq 0 (by decide) (by rv_eval []) (by rv_eval [])
  m56 := h.mem_eq 1 (by decide) (by rv_eval []) (by rv_eval [])
  m40 := h.mem_eq 2 (by decide) (by rv_eval []) (by rv_eval [])
  m64 := h.mem_eq 3 (by decide) (by rv_eval []) (by rv_eval [])
  m24 := h.mem_eq 4 (by decide) (by rv_eval []) (by rv_eval [])
  m32 := h.mem_eq 5 (by decide) (by rv_eval []) (by rv_eval [])
  m16 := h.mem_eq 6 (by decide) (by rv_eval []) (by rv_eval [])
  m72 := h.mem_eq 7 (by decide) (by rv_eval []) (by rv_eval [])
  m8 := h.mem_eq 8 (by decide) (by rv_eval []) (by rv_eval [])
  m80 := h.mem_eq 9 (by decide) (by rv_eval []) (by rv_eval [])
  m88 := h.mem_eq 10 (by decide) (by rv_eval []) (by rv_eval [])
  m96 := h.mem_eq 11 (by decide) (by rv_eval []) (by rv_eval [])
  m104 := h.mem_eq 12 (by decide) (by rv_eval []) (by rv_eval [])
  m120 := h.mem_eq 13 (by decide) (by rv_eval []) (by rv_eval [])

/-- Kept by a step that keeps the callee-saved registers and the spills. -/
theorem B37.keep {u v : MachineState} {P w0 w1 w2 w3 : Word} {X : Word → Prop}
    (h : B37 u P w0 w1 w2 w3) (hr : ∀ r ∈ [Reg.x8, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25,
      .x26, .x27], v.getReg r = u.getReg r) (hX : DFrame u v X)
    (hXm : ∀ a, X a → ¬ Within a (P + 8) 120) (hP : P.toNat + 128 ≤ 2 ^ 64) :
    B37 v P w0 w1 w2 w3 := by
  have k (o : ℕ) (h1 : 8 ≤ o) (h2 : o ≤ 120) : v.getMem (P + BitVec.ofNat 64 o) =
      u.getMem (P + BitVec.ofNat 64 o) :=
    hX _ fun i hi hw ↦ hXm _ hw (by addr_omega [hi, h1, h2, hP])
  exact {
    x8 := by rw [hr .x8 (by decide)]; exact h.x8
    x18 := by rw [hr .x18 (by decide)]; exact h.x18
    x19 := by rw [hr .x19 (by decide)]; exact h.x19
    x20 := by rw [hr .x20 (by decide)]; exact h.x20
    x21 := by rw [hr .x21 (by decide)]; exact h.x21
    x22 := by rw [hr .x22 (by decide)]; exact h.x22
    x23 := by rw [hr .x23 (by decide)]; exact h.x23
    x24 := by rw [hr .x24 (by decide)]; exact h.x24
    x25 := by rw [hr .x25 (by decide)]; exact h.x25
    x26 := by rw [hr .x26 (by decide)]; exact h.x26
    x27 := by rw [hr .x27 (by decide)]; exact h.x27
    m48 := (k 48 (by decide) (by decide)).trans h.m48
    m56 := (k 56 (by decide) (by decide)).trans h.m56
    m40 := (k 40 (by decide) (by decide)).trans h.m40
    m64 := (k 64 (by decide) (by decide)).trans h.m64
    m24 := (k 24 (by decide) (by decide)).trans h.m24
    m32 := (k 32 (by decide) (by decide)).trans h.m32
    m16 := (k 16 (by decide) (by decide)).trans h.m16
    m72 := (k 72 (by decide) (by decide)).trans h.m72
    m8 := (k 8 (by decide) (by decide)).trans h.m8
    m80 := (k 80 (by decide) (by decide)).trans h.m80
    m88 := (k 88 (by decide) (by decide)).trans h.m88
    m96 := (k 96 (by decide) (by decide)).trans h.m96
    m104 := (k 104 (by decide) (by decide)).trans h.m104
    m120 := (k 120 (by decide) (by decide)).trans h.m120 }

/-- `0x8000a448`'s doublewords: the root's bytes `7..14`, `15..22`, `24..31`. -/
theorem a448_words {u v : MachineState} {w0 w1 w2 w3 : Word} (h : b8000a448.Holds u v)
    (hB : B37 u (u.getReg .x2) w0 w1 w2 w3) :
    v.getMem (u.getReg .x2 + 96) = w0 >>> 56 ||| w1 <<< 8 ∧
      v.getMem (u.getReg .x2 + 88) = w1 >>> 56 ||| w2 <<< 8 ∧
      v.getMem (u.getReg .x2 + 104) = w3 := by
  have m96 : v.getMem (u.getReg .x2 + 96) = _ := h.mem_eq 0 (by decide) (by rv_eval []) rfl
  have m88 : v.getMem (u.getReg .x2 + 88) = _ := h.mem_eq 1 (by decide) (by rv_eval []) rfl
  have m104 : v.getMem (u.getReg .x2 + 104) = _ := h.mem_eq 2 (by decide) (by rv_eval []) rfl
  simp only [reduceMem, List.getElem_cons_succ, List.getElem_cons_zero, Sym.E.eval,
    Sym.BinOp.eval, hB.x8, hB.x18, hB.x19, hB.x20, hB.x21,
    hB.x22, hB.x23, hB.x24, hB.x25, hB.x26, hB.x27, hB.m48, hB.m56, hB.m40, hB.m64, hB.m24,
    hB.m32, hB.m16, hB.m72, hB.m8, hB.m80, hB.m88, hB.m96, hB.m104] at m96 m88 m104
  refine ⟨m96.trans ?_, m88.trans ?_, m104.trans ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight, BitVec.zeroExtend_eq_setWidth, getLsbD_extractByte]
    interval_cases i <;> simp

theorem zb7 (w : Word) : zb w 7 = w >>> 56 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.zeroExtend_eq_setWidth,
    getLsbD_extractByte]
  interval_cases i <;> simp

theorem take_succ_sum (l : List ℕ) (i : ℕ) : (l.take (i + 1)).sum = (l.take i).sum + l.getD i 0 := by
  rw [List.take_add_one, List.sum_append]
  cases h : l[i]? <;> simp [List.getD_eq_getElem?_getD, h]

theorem dg0 (u : MachineState) (a : Word) : (digestAt u a)[0].toBitVec = u.getMem a := by
  simp only [digestAt, Vector.getElem_ofFn, UInt64.toBitVec_ofBitVec, Nat.mul_zero, add_ofNat_zero]

theorem dg1 (u : MachineState) (a : Word) : (digestAt u a)[1].toBitVec = u.getMem (a + 8#64) := by
  simp only [digestAt, Vector.getElem_ofFn, UInt64.toBitVec_ofBitVec, Nat.mul_one]

theorem dg2 (u : MachineState) (a : Word) : (digestAt u a)[2].toBitVec = u.getMem (a + 16#64) := by
  simp only [digestAt, Vector.getElem_ofFn, UInt64.toBitVec_ofBitVec, Nat.reduceMul]

theorem dg3 (u : MachineState) (a : Word) : (digestAt u a)[3].toBitVec = u.getMem (a + 24#64) := by
  simp only [digestAt, Vector.getElem_ofFn, UInt64.toBitVec_ofBitVec, Nat.reduceMul]

theorem one_shl_toNat (k : ℕ) : (1#64 <<< (k % 64)).toNat = 2 ^ (k % 64) := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.one_mul,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (Nat.mod_lt _ (by decide)))]

/-- At the last level, the mirror reads the residual, then grinds. -/
theorem afk_last (s : MachineState) (x : LCtx) {ℓ : ℕ} (hl : ℓ = K0 s + 1)
    (W : Model.Pcs.WhirLocals × List E) :
    AFk s x ℓ W = Model.TM.nextScalars (2 ^ (((s.getReg .x12).toNat - W.1.folds.length) % 64)) >>=
      fun r ↦ Model.Pcs.afterCommit (s.getReg .x12).toNat (cfgOf s) (basisOf s x) ℓ (fcOf s ℓ)
        (rtOf s ℓ) (restOf s ℓ) W.1 W.2 (r, []) := by
  obtain ⟨W, lfs⟩ := W
  have hlen : ℓ = (cfgOf s).folds.length - 1 := by
    simp only [cfgOf, Model.Pcs.ladderFolds, List.length_cons, List.length_replicate]; omega
  rw [AFk, Model.Pcs.afterFolds_eq]
  simp only [Model.Pcs.levelOpen, ite_eq_left_of_eq_true _ _ (eq_true hlen), bind_assoc, pure_bind]

/-- At `0x8000a430`, `next_scalars(2^ml)` returned into `S - 384`, from `u` at `0x8000a37c`. -/
structure LastNS (s : MachineState) (x : LCtx) (h t u w : MachineState) (ℓ : ℕ)
    (Wl : Model.Pcs.WhirLocals) (lf q : List E) : Prop where
  at304 : At304 s x h t u ℓ Wl lf q
  pc : w.pc = 0x8000a430
  sp : w.getReg .x2 = s.getReg .x2 - 1040
  inv : InvR s w (w.getMem nextAddr)
  heap : HeapOk w
  mono : heapNext t ≤ heapNext w
  fr : DFrame u w fun a ↦ Within a (s.getReg .x2 - 1032) 104 ∨
    Within a (s.getReg .x2 - 920) 8 ∨ Within a (s.getReg .x2 - 384) 24 ∨
    Within a (s.getReg .x10 + 8) 344 ∨ Within a (s.getReg .x2 - 2464) 1424 ∨
    Within a nextAddr 8 ∨ (heapNext t ≤ a.toNat ∧ a.toNat < heapNext w)
  bytes : B37 w (u.getReg .x2) (u.getMem (s.getReg .x11)) (u.getMem (s.getReg .x11 + 8#64))
    (u.getMem (s.getReg .x11 + 16#64)) (u.getMem (s.getReg .x11 + 24#64))
  x9 : w.getReg .x9 = x.FP
  err : vecCap w (s.getReg .x2 - 384) = errNiche → w.getMem (s.getReg .x2 - 384 + 8) ≠ errNiche
  ok : vecCap w (s.getReg .x2 - 384) ≠ errNiche → VecOk w (s.getReg .x2 - 384) 24 8 ∧
    NewBuf t w (vecPtr w (s.getReg .x2 - 384)) ((vecCap w (s.getReg .x2 - 384)).toNat * 24) 8
  dig : digestAt w (s.getReg .x11) = digestAt u (s.getReg .x11)
  value : vecCap w (s.getReg .x2 - 384) ≠ errNiche →
    RunsC s w ℓ (Model.Pcs.afterCommit (s.getReg .x12).toNat (cfgOf s) (basisOf s x) ℓ
      (fcOf s ℓ) (rtOf s ℓ) (restOf s ℓ) (Model.Pcs.foldSt Wl lf q).1 lf
      (vecEs w (s.getReg .x2 - 384), [])) []

/-- **`0x8000a37c`**: the root's bytes `7..31` kept, `next_scalars(2^ml)` called. -/
theorem lastCall (hNS : NextScalarsSpec) {s : MachineState} {x : LCtx} {h t u : MachineState}
    {ℓ : ℕ} {Wl : Model.Pcs.WhirLocals} {lf q : List E} (hpre : VsoPre s) (hc : Cfg s x.QP x.QL)
    (hnf : Wl.folds.length = ((Model.Pcs.ladderFolds (K0 s + 1)).take ℓ).sum)
    (ha : At304 s x h t u ℓ Wl lf q) (hl : ℓ = K0 s + 1) (hpc : u.pc = 0x8000a37c) :
    ∃ w, Reaches Image.code u w ∧ (FailR s w ∨ LastNS s x h t u w ℓ Wl lf q) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hf := ha.fo
  have hsp : u.getReg .x2 = s.getReg .x2 - 1040 := (ha.regs .x2 (by decide)).trans hf.sp
  have hr := hpre.root
  have hrst := hr.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hR : Region (s.getReg .x11) 32 := by
    rcases hr.region with h0 | h0
    · cases h0
    · exact h0
  have hRb := Region.bounds hR
  have hM := hR.1
  simp only [Mapped] at hM
  have hlvl := hf.head.lvl
  have hlen : (Wl.folds ++ lf).length = ((Model.Pcs.ladderFolds (K0 s + 1)).take (ℓ + 1)).sum := by
    rw [List.length_append, hnf, hf.lfl, take_succ_sum]; rfl
  have hle := folds_le hc hlvl
  rw [← hlen] at hle
  -- the invariant at `t` and `u`
  have inv₀ : InvR s t (t.getMem nextAddr) :=
    FW.inv hpre hf.head hf.fr hf.heap hf.mono (hf.sp.trans hf.head.sp.symm)
  have X₁ := ha.fr
  have hX₁ (a : Word) (hw : Within a (s.getReg .x2 - 928) 8 ∨ Within a (s.getReg .x2 - 912) 8 ∨
      Within a (s.getReg .x2 - 896) 8 ∨ Within a (s.getReg .x2 - 872) 8 ∨
      Within a (s.getReg .x2 - 808) 8 ∨ Within a (s.getReg .x2 - 792) 8 ∨
      Within a (s.getReg .x2 - 616) 32) : Within a (s.getReg .x2 - 1040) 936 := by
    rcases hw with hw | hw | hw | hw | hw | hw | hw <;> addr_omega [hw, hb]
  obtain ⟨nx₁, inv₁⟩ := InvR.stk hpre inv₀ X₁ hX₁ (ha.regs .x2 (by decide))
  -- `0x8000a37c`: the root's bytes `7..31`, then `next_scalars(2^ml)`
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000a37c_spec hpc (by
    rv_eval [hsp, ha.x16]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact validAccess_one (by addr_omega [hM])
      | addr_omega [hRb, hrst, hb])
  have B₂ := b37_of h₂
  rw [ha.x16] at B₂
  have k₂ := b8000a37c_keeps h₂
  have X₂ : DFrame u t₂ fun a ↦ Within a (s.getReg .x2 - 1032) 104 ∨
      Within a (s.getReg .x2 - 920) 8 :=
    (holds_dframe h₂).mono fun a ⟨k, hk, hw⟩ ↦ by
      simp only [b8000a37c, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> rv_eval [hsp] at hw <;> first
        | exact Or.inl (by addr_omega [hw, hb])
        | exact Or.inr (by addr_omega [hw, hb])
  have hsp₂ : t₂.getReg .x2 = u.getReg .x2 := k₂ .x2 (by decide)
  obtain ⟨nx₂, inv₂⟩ := InvR.stk hpre inv₁ X₂ (fun a ha ↦ by
    rcases ha with ha | ha <;> addr_omega [ha, hb]) hsp₂
  have hn₂ : heapNext t₂ = heapNext t := by simp only [heapNext, nx₂, nx₁]
  have hheap₂ : HeapOk t₂ := ⟨by rw [hn₂]; exact hf.heap.lo, by rw [hn₂]; exact hf.heap.hi⟩
  have x11₂ : t₂.getReg .x11 = s.getReg .x10 := by
    rw [b8000a37c_x11 h₂, ha.regs .x27 (by decide), hf.x27]
  have x12₂ : t₂.getReg .x12 = 1#64 <<< ((u.getReg .x13).toNat % 64) :=
    h₂.reg_eq .x12 rfl (by rv_eval [])
  have hml : (u.getReg .x13).toNat = (s.getReg .x12).toNat - (Wl.folds ++ lf).length := by
    rw [ha.x13]; addr_omega [hle]
  obtain ⟨t₃, hr₃, hv₃⟩ := callNextScalars (o := s.getReg .x2 - 384) hNS hpre inv₂ hheap₂
    (b8000a37c_pc h₂) (by rw [b8000a37c_x10 h₂, hsp]; addr_omega [hb]) x11₂ (by simp only [Slot24]; addr_omega [hb])
  rcases hv₃ with hd | ⟨hpc₃, hpres₃, hheap₃, hmono₃, X₃, herr₃, hok₃, hval₃⟩
  · exact ⟨t₃, hr₂.trans hr₃, Or.inl (Or.inl hd)⟩
  have hsp₃ : t₃.getReg .x2 = t₂.getReg .x2 := hpres₃ .x2 (by decide)
  have inv₃ := InvR.callT hpre inv₂ X₃ (by simp only [Slot24]; addr_omega [hb]) hheap₃ hmono₃ hsp₃
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 1040 := by rw [hsp₃, hsp₂, hsp]
  have hhi₃ := hheap₃.hi
  have hrf := hr.free
  simp only [Outside] at hrf
  have hs₂ : heapNext s ≤ heapNext t₂ := inv₂.mono
  have hrs := hpre.rootSponge
  -- the mirror
  have stkNS (a : Word) (ha : Within a (s.getReg .x2 - 1040) 936) : NS s a :=
    Or.inl (by addr_omega [ha, hb])
  have stkR (y : Word) (hy : Within y (s.getReg .x11) 32) (a : Word)
      (ha : Within a (s.getReg .x2 - 1040) 936) (e : y = a) : False := by
    subst e; addr_omega [hy, ha, hrst, hb]
  have V₀ := hf.value.toC
  rw [afk_last s x hl] at V₀
  have V₁ := V₀.keep hpre inv₀ X₁ (fun a ha ↦ stkNS a (hX₁ a ha))
    fun y hy hw ↦ stkR y hy y (hX₁ y hw) rfl
  have V₂ := V₁.keep hpre inv₁ X₂ (fun a ha ↦ stkNS a (by rcases ha with ha | ha <;> addr_omega [ha, hb]))
    fun y hy hw ↦ stkR y hy y (by rcases hw with hw | hw <;> addr_omega [hw, hb]) rfl
  have hn : (t₂.getReg .x12).toNat =
      2 ^ (((s.getReg .x12).toNat - (Model.Pcs.foldSt Wl lf q).1.folds.length) % 64) := by
    rw [x12₂, one_shl_toNat, hml]; rfl
  have d₂₃ : digestAt t₃ (s.getReg .x11) = digestAt t₂ (s.getReg .x11) :=
    digest_keep X₃ (root_bound hpre) fun y hy hw ↦ by
      rcases hw with hw | hw | hw | hw | hw
      · addr_omega [hy, hw, hrst, hb]
      · addr_omega [hy, hw, hrs]
      · addr_omega [hy, hw, hrst, hb]
      · addr_omega [hy, hw, hrf.2]
      · simp only [Fresh] at hw
        rcases hrf.1 with h1 | h1
        · addr_omega [hy, hw.1, h1, hs₂]
        · addr_omega [hy, hw.2, h1, hhi₃]
  refine ⟨t₃, hr₂.trans hr₃, Or.inr {
    at304 := ha
    pc := by rw [hpc₃, returnAddress_eq, b8000a37c_x1 h₂]; decide
    sp := sp₃
    inv := inv₃
    heap := hheap₃
    mono := by omega
    fr := (X₂.mono fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)).trans X₃ fun a ha ↦ by
        rcases ha with ha | ha | ha | ha | ha
        · exact Or.inr (Or.inr (Or.inl ha))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
        · simp only [Fresh] at ha
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, ha.2⟩)))))
    bytes := B₂.keep (fun r hr' ↦ hpres₃ r (by simp only [calleeSaved]; exact mem_of_mem hr' _))
      X₃ (fun a ha hw ↦ by
        rw [hsp] at hw
        rcases ha with ha | ha | ha | ha | ha
        · addr_omega [ha, hw, hb]
        · addr_omega [ha, hw, hb, hIs, hS]
        · addr_omega [ha, hw, hb]
        · addr_omega [ha, hw, hb, hnx]
        · simp only [Fresh] at ha; addr_omega [ha.2, hw, hb, hhi₃]) (by rw [hsp]; addr_omega [hb])
    x9 := by rw [hpres₃ .x9 (by decide), k₂ .x9 (by decide), ha.regs .x9 (by decide), hf.x9]
    err := herr₃
    ok := fun hne ↦ ⟨(hok₃ hne).1, by
      have := (hok₃ hne).2; simp only [NewBuf] at this ⊢; rw [← hn₂]; exact this⟩
    dig := d₂₃.trans (digest_keep X₂ (root_bound hpre) fun y hy hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hy, hw, hrst, hb])
    value := fun herr ↦ V₂.bind (v := t₃) (nx' := []) (vecEs t₃ (s.getReg .x2 - 384)) d₂₃ fun T hT ↦ by
      have hv := hval₃ T hT
      rw [hn] at hv
      cases hrun : (Model.TM.nextScalars (2 ^ (((s.getReg .x12).toNat -
          (Model.Pcs.foldSt Wl lf q).1.folds.length) % 64))).run T with
      | none => rw [hrun] at hv; exact absurd hv herr
      | some p =>
        obtain ⟨xs, T'⟩ := p
        rw [hrun] at hv
        obtain ⟨-, hnew, hT'⟩ := hv
        have hk := Model.Pcs.Keeps.nextScalars _ T xs T' hrun
        exact ⟨T', by rw [← hnew.elems], hT', hk.1, hk.2.2, by rw [hk.2.1, List.append_nil]⟩ }⟩

/-- **`0x8000a430`** and **`0x8000a448`**: the `Err` returned, or the residual and the root's
doublewords in place. -/
theorem lastClose {s : MachineState} {x : LCtx} {h t u t₃ : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf q : List E} (hpre : VsoPre s) (hc : Cfg s x.QP x.QL)
    (hnf : Wl.folds.length = ((Model.Pcs.ladderFolds (K0 s + 1)).take ℓ).sum)
    (hl : ℓ = K0 s + 1) (lw : LastNS s x h t u t₃ ℓ Wl lf q) :
    ∃ v, Reaches Image.code t₃ v ∧ (FailR s v ∨ ∃ res d, Opened s x h t v ℓ Wl lf q res [] d) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have ha := lw.at304
  have hf := ha.fo
  have hsp : u.getReg .x2 = s.getReg .x2 - 1040 := (ha.regs .x2 (by decide)).trans hf.sp
  have hrst := hpre.root.stack
  rw [stackLo_vso, vso_stack] at hrst
  have hlvl := hf.head.lvl
  have hlen : (Wl.folds ++ lf).length = ((Model.Pcs.ladderFolds (K0 s + 1)).take (ℓ + 1)).sum := by
    rw [List.length_append, hnf, hf.lfl, take_succ_sum]; rfl
  have hle := folds_le hc hlvl
  rw [← hlen] at hle
  have inv₃ := lw.inv
  have hheap₃ := lw.heap
  have sp₃ := lw.sp
  have herr₃ := lw.err
  have hok₃ := lw.ok
  -- `0x8000a430`: the `Err` check
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000a430_spec
    lw.pc (by
      rv_eval [sp₃]
      and_intros <;> valid_access hst.valid [hb])
  have k₄ := b8000a430_keeps h₄
  have hm₄ := b8000a430_mem_same h₄
  have inv₄ : InvR s t₄ (t₄.getMem nextAddr) := by
    rw [hm₄]; exact Inv.same' inv₃ hm₄ (k₄ .x2 (by decide))
  have e656 : t₃.getReg .x2 + 656 = s.getReg .x2 - 384 := by addr_omega [hb, sp₃]
  have e664 : t₃.getReg .x2 + 664 = s.getReg .x2 - 384 + 8 := by addr_omega [hb, sp₃]
  have q656 : t₃.getMem (t₃.getReg .x2 + 656) = vecCap t₃ (s.getReg .x2 - 384) := by
    rw [e656]; rfl
  have hr₁₄ := hr₄
  by_cases herr : vecCap t₃ (s.getReg .x2 - 384) = errNiche
  · obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000a444_spec
      (b8000a430_pc_not_taken h₄ (by rw [q656, herr]; rfl)) trivial
    obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000b86c_spec (b8000a444_pc h₅) trivial
    have inv₆ : InvR s t₆ (t₄.getMem nextAddr) := Inv.same' inv₄
      (fun a ↦ by rw [b8000b86c_mem_same h₆, b8000a444_mem_same h₅])
      (by rw [b8000b86c_keeps h₆ .x2 (by decide), b8000a444_keeps h₅ .x2 (by decide)])
    obtain ⟨w, hw, hfw⟩ := fail844 inv₆ (b8000b86c_pc h₆) (by
      rw [b8000b86c_keeps h₆ .x1 (by decide), b8000a444_keeps h₅ .x1 (by decide),
        b8000a430_x1 h₄, e664]
      simpa only [okTag, errNiche] using herr₃ herr)
    exact ⟨w, hr₁₄.trans (hr₅.trans (hr₆.trans hw)), Or.inl hfw⟩
  -- `0x8000a448`: the next root's doublewords
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000a448_spec
    (b8000a430_pc_taken h₄ (by rw [q656]; exact herr)) (by
      rv_eval [(k₄ .x2 (by decide)).trans sp₃]
      and_intros <;> valid_access hst.valid [hb])
  have k₅ := b8000a448_keeps h₅
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 1040 := (k₄ .x2 (by decide)).trans sp₃
  have X₅ : DFrame t₄ t₅ fun a ↦ Within a (s.getReg .x2 - 952) 24 := by
    have := DFrame.of_memFrame (b8000a448_frame h₅ (by rw [sp₄]; addr_omega [hb]))
    rw [sp₄] at this
    exact this.mono fun a ha ↦ by addr_omega [ha, hb]
  obtain ⟨nx₅, inv₅⟩ := InvR.stk hpre inv₄ X₅ (fun a ha ↦ by addr_omega [ha, hb])
    (k₅ .x2 (by decide))
  have sp₅ : t₅.getReg .x2 = s.getReg .x2 - 1040 := (k₅ .x2 (by decide)).trans sp₄
  -- the next root: the root itself
  have hP : (u.getReg .x2).toNat + 128 ≤ 2 ^ 64 := by rw [hsp]; addr_omega [hb]
  have B₃ := lw.bytes
  have B₄ := B₃.keep (fun r hr' ↦ k₄ r (mem_of_mem hr' _)) (DFrame.of_same hm₄ fun _ ↦ False)
    (fun _ h ↦ h.elim) hP
  have e₄ : t₄.getReg .x2 = u.getReg .x2 := (k₄ .x2 (by decide)).trans (sp₃.trans hsp.symm)
  rw [← e₄] at B₄
  obtain ⟨w96, w88, w104⟩ := a448_words h₅ B₄
  -- what `u` .. `t₅` write
  have hhi₃ := hheap₃.hi
  have hn₅ : heapNext t₅ = heapNext t₃ := by simp only [heapNext, nx₅, hm₄]
  have Xu : DFrame u t₅ fun a ↦ Within a (s.getReg .x2 - 1032) 104 ∨
      Within a (s.getReg .x2 - 920) 8 ∨ Within a (s.getReg .x2 - 384) 24 ∨
      Within a (s.getReg .x10 + 8) 344 ∨ Within a (s.getReg .x2 - 2464) 1424 ∨
      Within a nextAddr 8 ∨ (heapNext t ≤ a.toNat ∧ a.toNat < heapNext t₃) :=
    (lw.fr.trans (DFrame.of_same hm₄ fun _ ↦ False) fun _ h ↦ h.elim).trans X₅ fun a ha ↦
      Or.inl (by addr_omega [ha, hb])
  have kU (y : Word) (hy : (s.getReg .x2 - 928).toNat ≤ y.toNat ∧ y.toNat + 8 ≤
      (s.getReg .x2 - 920).toNat ∨ (s.getReg .x2 - 912).toNat ≤ y.toNat ∧ y.toNat + 8 ≤
      (s.getReg .x2 - 384).toNat) : t₅.getMem y = u.getMem y :=
    Xu y fun i hi hw ↦ by
      rcases hw with hw | hw | hw | hw | hw | hw | hw
      · addr_omega [hw, hi, hy, hb]
      · addr_omega [hw, hi, hy, hb]
      · addr_omega [hw, hi, hy, hb]
      · addr_omega [hw, hi, hy, hb, hIs, hS]
      · addr_omega [hw, hi, hy, hb]
      · addr_omega [hw, hi, hy, hb, hnx]
      · addr_omega [hw.2, hi, hy, hb, hhi₃]
  have stkNS (a : Word) (ha : Within a (s.getReg .x2 - 1040) 936) : NS s a :=
    Or.inl (by addr_omega [ha, hb])
  have stkR (y : Word) (hy : Within y (s.getReg .x11) 32) (a : Word)
      (ha : Within a (s.getReg .x2 - 1040) 936) (e : y = a) : False := by
    subst e; addr_omega [hy, ha, hrst, hb]
  have V₄ := (lw.value herr).same (v := t₄) (by simp only [digestAt, hm₄]) fun T hT ↦
    tr_keep hpre inv₃ hT (DFrame.of_same hm₄ fun _ ↦ False) fun _ h ↦ h.elim
  have V₅ := V₄.keep hpre inv₄ X₅ (fun a ha ↦ stkNS a (by addr_omega [ha, hb]))
    fun y hy hw ↦ stkR y hy y (by addr_omega [hw, hb]) rfl
  have hnr : nextRoots s ℓ (digestAt u (s.getReg .x11)) = [] := by
    rw [nextRoots, ite_eq_left_of_eq_true _ _ (eq_true hl)]
  rw [← hnr] at V₅
  -- the residual
  have hok := hok₃ herr
  have hraw := hok.1.raw
  simp only [RawVecOk, Buf] at hraw
  have hl₃ := hok.1.len
  have hnb := hok.2
  simp only [NewBuf] at hnb
  have x1₅ : t₅.getReg .x1 = vecPtr t₃ (s.getReg .x2 - 384) := by
    rw [k₅ .x1 (by decide), b8000a430_x1 h₄]; simp only [vecPtr]; rw [e664]
  have x31₅ : t₅.getReg .x31 = vecLen t₃ (s.getReg .x2 - 384) := by
    have e672 : t₃.getReg .x2 + 672 = s.getReg .x2 - 384 + 16 := by addr_omega [hb, sp₃]
    rw [k₅ .x31 (by decide), b8000a430_x31 h₄]; simp only [vecLen]; rw [e672]
  have X₃₅ : DFrame t₃ t₅ fun a ↦ Within a (s.getReg .x2 - 952) 24 :=
    (DFrame.of_same hm₄ _).trans X₅ fun _ h ↦ h
  have hres : eListAt t₅ (vecPtr t₃ (s.getReg .x2 - 384)) (vecLen t₃ (s.getReg .x2 - 384)).toNat =
      vecEs t₃ (s.getReg .x2 - 384) := X₃₅.eListAt fun i hi hw ↦ by
    rcases hnb.2 with h0 | h0
    · omega
    · addr_omega [hw, hi, h0, hb, hhi₃, hl₃]
  have hdig : digestAt t₅ (s.getReg .x11) = digestAt u (s.getReg .x11) :=
    (digest_keep X₃₅ (root_bound hpre) fun y hy hw ↦ by addr_omega [hy, hw, hrst, hb]).trans lw.dig
  have hmo := lw.mono
  -- the pending claims: none
  have c0 : vecCap t₅ (s.getReg .x2 - 616) = 0 := by
    simp only [vecCap]; rw [kU _ (by addr_omega [hb]), ha.m424]
  have p8 : vecPtr t₅ (s.getReg .x2 - 616) = 8 := by
    have e : s.getReg .x2 - 616 + 8 = s.getReg .x2 - 608 := by addr_omega [hb]
    simp only [vecPtr]; rw [e, kU _ (by addr_omega [hb]), ha.m432]
  have l0 : vecLen t₅ (s.getReg .x2 - 616) = 0 := by
    have e : s.getReg .x2 - 616 + 16 = s.getReg .x2 - 600 := by addr_omega [hb]
    simp only [vecLen]; rw [e, kU _ (by addr_omega [hb]), ha.m440]
  -- the root's doublewords
  have g0 := dg0 u (s.getReg .x11)
  have g1 := dg1 u (s.getReg .x11)
  have g2 := dg2 u (s.getReg .x11)
  have g3 := dg3 u (s.getReg .x11)
  have e96 : s.getReg .x2 - 944 = t₄.getReg .x2 + 96 := by addr_omega [hb, sp₄]
  have e88 : s.getReg .x2 - 952 = t₄.getReg .x2 + 88 := by addr_omega [hb, sp₄]
  have e104 : s.getReg .x2 - 936 = t₄.getReg .x2 + 104 := by addr_omega [hb, sp₄]
  have e120 : s.getReg .x2 - 920 = t₄.getReg .x2 + 120#64 := by addr_omega [hb, sp₄]
  refine ⟨t₅, hr₁₄.trans hr₅, Or.inr ⟨vecEs t₃ (s.getReg .x2 - 384), digestAt u (s.getReg .x11), {
    fo := hf
    fr := ?_
    inv := inv₅
    heap := ⟨by have := hheap₃.lo; omega, by omega⟩
    mono := by omega
    pc := b8000a448_pc h₅
    sp := sp₅
    x9 := by
      rw [k₅ .x9 (by decide), k₄ .x9 (by decide), lw.x9]
    m144 := by rw [kU _ (by addr_omega [hb]), ha.m144]
    m232 := by rw [kU _ (by addr_omega [hb]), ha.m232]
    m112 := by rw [kU _ (by addr_omega [hb]), ha.m112]
    m128 := by rw [kU _ (by addr_omega [hb]), ha.m128]
    m168 := by rw [kU _ (by addr_omega [hb]), ha.m168]; addr_omega [hle]
    m248 := by rw [kU _ (by addr_omega [hb]), ha.m248]
    rsd := ⟨by rw [x1₅, x31₅]; exact hres, by rw [x1₅]; exact hraw.1, by
      rw [x1₅, x31₅]
      rcases hnb.2 with h0 | h0
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, by omega⟩⟩
    pnd := {
      vec := ⟨by simp only [RawVecOk, Buf, p8, c0]; exact ⟨rfl, Or.inl rfl⟩, by rw [l0, c0]⟩
      elems := by rw [l0]; rfl
      intro := fun i hi ↦ by rw [l0] at hi; exact absurd hi (Nat.not_lt_zero _)
      ood := fun i hi ↦ by rw [l0] at hi; exact absurd hi (Nat.not_lt_zero _)
      fresh := fun y hy ↦ by
        rcases hy with hy | ⟨i, hi, -⟩
        · have hc0 : (vecCap t₅ (s.getReg .x2 - 616)).toNat = 0 := by rw [c0]; rfl
          simp only [Within] at hy; omega
        · rw [l0] at hi; exact absurd hi (Nat.not_lt_zero _) }
    root := ⟨by rw [kU _ (by addr_omega [hb]), g0]; exact ha.low,
      by rw [e96, w96, g0, g1], by rw [e88, w88, g1, g2],
      by rw [e120, X₅ _ fun i hi hw ↦ by addr_omega [hw, hi, hb, sp₄], B₄.m120, zb7, g2],
      by rw [e104, w104, g3]⟩
    last := fun _ ↦ hdig.symm
    value := V₅ }⟩⟩
  · exact (ha.fr.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha | ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (Or.inl (ha))
      · exact Or.inr (Or.inr (Or.inl (ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (ha))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ha)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb]))))))).trans Xu fun a ha ↦ by
      rcases ha with ha | ha | ha | ha | ha | ha | ha
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inl (by addr_omega [ha, hb])
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb]))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp only [W]; addr_omega [ha])))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ha)))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ha))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨ha.1, by omega⟩)))))))))))

/-- **The last level's residual**, from `0x8000a37c` to `0x8000a790`, or an `Err`. -/
theorem openLast (hNS : NextScalarsSpec) {s : MachineState} {x : LCtx} {h t u : MachineState}
    {ℓ : ℕ} {Wl : Model.Pcs.WhirLocals} {lf q : List E} (hpre : VsoPre s) (hc : Cfg s x.QP x.QL)
    (hnf : Wl.folds.length = ((Model.Pcs.ladderFolds (K0 s + 1)).take ℓ).sum)
    (ha : At304 s x h t u ℓ Wl lf q) (hl : ℓ = K0 s + 1) (hpc : u.pc = 0x8000a37c) :
    ∃ v, Reaches Image.code u v ∧ (FailR s v ∨ ∃ res d, Opened s x h t v ℓ Wl lf q res [] d) := by
  obtain ⟨w, hr, hw⟩ := lastCall hNS hpre hc hnf ha hl hpc
  rcases hw with hf | lw
  · exact ⟨w, hr, Or.inl hf⟩
  obtain ⟨v, hr', hv⟩ := lastClose hpre hc hnf hl lw
  exact ⟨v, hr.trans hr', hv⟩

end Rv64Verifier.Proofs.Pcs.Vso
