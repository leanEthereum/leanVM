import Rv64Verifier.Proofs.Runtime.CopyBlocks

/-!
# The forward copy, proved once for `memcpy` and `memmove`

`fwd` proves the forward copy (`CopyBlocks.lean`) at any addresses `C` that hold its blocks
(`FwdCode.Ok`): from the state after `sp` drops by 16, with a destination and a source that are
mapped and either apart or the destination not above the source (`FwdPre`), it returns with the
destination holding the source's bytes.

The invariant is `Copied s u k`: the first `k` bytes copied, and nothing written but those and
the stack. Every source byte from `k` on is then still the initial one (`Copied.src`), which is
what a copy that may overlap needs.
-/

namespace Rv64Verifier.Runtime.Forward
open RiscvZkvm.Rv64 Rv64Verifier.Sym
open Rv64Verifier.Runtime.Memcpy (keepE keepE_reg decE tailCE keepC truncate_zeroExtend)
open Rv64Verifier.Runtime.Memcmp (lbu_rd lbu_other)
open Rv64Verifier.Runtime.Memset (and_not7)

/-- `memcpy`'s precondition, the ranges allowed to overlap when the destination is not above the
source. -/
structure FwdPre (s : MachineState) : Prop where
  dst : Mapped (s.getReg .x10) (s.getReg .x12).toNat
  src : Mapped (s.getReg .x11) (s.getReg .x12).toNat
  fwd : (s.getReg .x12).toNat = 0 ∨ (s.getReg .x10).toNat ≤ (s.getReg .x11).toNat ∨
    (s.getReg .x11).toNat + (s.getReg .x12).toNat ≤ (s.getReg .x10).toNat
  stack : StackOk s 16
  dstStack : Apart (s.getReg .x10) (s.getReg .x12).toNat (stackLo s 16) 16
  srcStack : Apart (s.getReg .x11) (s.getReg .x12).toNat (stackLo s 16) 16

/-- The first `k` bytes copied; nothing written but them and the stack. -/
structure Copied (s u : MachineState) (k : Nat) : Prop where
  bytes : ∀ i < k, byteAt u (s.getReg .x10 + BitVec.ofNat 64 i) =
    byteAt s (s.getReg .x11 + BitVec.ofNat 64 i)
  frame : ByteFrame s u fun a ↦ Within a (s.getReg .x10) k ∨ Within a (stackLo s 16) 16

variable {s : MachineState}

theorem FwdPre.sp (h : FwdPre s) : 0x30 ≤ (s.getReg .x2).toNat ∧
    (s.getReg .x2).toNat ≤ 0xc0000008 ∧ (s.getReg .x2).toNat % 16 = 0 := by
  have := h.stack.bounds (by decide) (by decide)
  omega

theorem Copied.zero {u : MachineState} (hm : ∀ a, u.getMem a = s.getMem a) : Copied s u 0 :=
  ⟨fun _ h ↦ absurd h (Nat.not_lt_zero _), ByteFrame.of_same hm _⟩

theorem Copied.same {u v : MachineState} {k : Nat} (h : Copied s u k)
    (hm : ∀ a, v.getMem a = u.getMem a) : Copied s v k :=
  ⟨fun i hi ↦ by rw [← h.bytes i hi]; simp only [byteAt_eq, hm],
    h.frame.trans (ByteFrame.of_same hm _) fun _ h ↦ h⟩

/-- A source byte not yet copied is the initial one. -/
theorem Copied.src {u : MachineState} {k : Nat} (h : Copied s u k) (hp : FwdPre s) {i : Nat}
    (hk : k ≤ i) (hi : i < (s.getReg .x12).toNat) :
    byteAt u (s.getReg .x11 + BitVec.ofNat 64 i) = byteAt s (s.getReg .x11 + BitVec.ofNat 64 i) :=
  h.frame.byte _ fun hw ↦ by
    have hd := hp.dst
    have hs := hp.src
    have hf := hp.fwd
    have hss := hp.srcStack
    rcases hw with hw | hw
    · addr_omega [hw, hd, hs, hf, hk, hi]
    · addr_omega [hw, hs, hss, hi]

/-- A write of the aligned doubleword `B` of the stack. -/
theorem Copied.stack {u v : MachineState} {k : Nat} (h : Copied s u k) (hp : FwdPre s)
    (hk : k ≤ (s.getReg .x12).toNat) {B : Word} (hB : B.toNat % 8 = 0)
    (hB1 : (s.getReg .x2).toNat - 16 ≤ B.toNat) (hB2 : B.toNat + 8 ≤ (s.getReg .x2).toNat)
    (hf : ∀ a, a ≠ B → v.getMem a = u.getMem a) : Copied s v k := by
  have hsp := hp.sp
  have hd := hp.dst
  have hds := hp.dstStack
  have hfr := ByteFrame.of_single hB hf
  refine ⟨fun i hi ↦ ?_, h.frame.trans hfr fun a ha ↦ Or.inr ?_⟩
  · rw [← h.bytes i hi]
    exact hfr.byte _ fun hw ↦ by addr_omega [hw, hd, hds, hB1, hB2, hi, hk]
  · simp only [Within, stackLo] at ha ⊢
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

/-- `m` more bytes copied, from `k` on. -/
theorem Copied.extend {u v : MachineState} {k m : Nat} (h : Copied s u k) (hp : FwdPre s)
    (hkm : k + m ≤ (s.getReg .x12).toNat)
    (hf : ByteFrame u v (Within · (s.getReg .x10 + BitVec.ofNat 64 k) m))
    (hb : ∀ i < m, byteAt v (s.getReg .x10 + BitVec.ofNat 64 (k + i)) =
      byteAt s (s.getReg .x11 + BitVec.ofNat 64 (k + i))) : Copied s v (k + m) := by
  have hd := hp.dst
  simp only [Mapped] at hd
  refine ⟨fun i hi ↦ ?_, (h.frame.mono fun a ha ↦ ?_).trans hf fun a ha ↦ Or.inl ?_⟩
  · by_cases hik : i < k
    · rw [← h.bytes i hik]
      exact hf.byte _ fun hw ↦ by addr_omega [hw, hd, hik, hkm]
    · have := hb (i - k) (by omega)
      rwa [show k + (i - k) = i by omega] at this
  · rcases ha with ha | ha
    · exact Or.inl (by addr_omega [ha, hd, hkm])
    · exact Or.inr ha
  · addr_omega [ha, hd, hkm]

/-! ## The byte loops -/

theorem copy_loop {L : Word} {rt rc rd rs : Reg}
    (hlbu : Image.code.fetch L = some (.base (.LBU rt rs 0))) (hdec : Spec (L + 4) (decE L rc))
    (hsb : Image.code.fetch (L + 8) = some (.base (.SB rd rt 0)))
    (htail : Spec (L + 12) (tailCE L rc rd rs))
    (hr : rt ≠ rc ∧ rt ≠ rd ∧ rt ≠ rs ∧ rc ≠ rd ∧ rc ≠ rs ∧ rd ≠ rs ∧ rt ≠ .x0)
    (hp : FwdPre s) :
    ∀ m u k, u.pc = L → (u.getReg rc).toNat = m → 0 < m →
      u.getReg rd = s.getReg .x10 + BitVec.ofNat 64 k →
      u.getReg rs = s.getReg .x11 + BitVec.ofNat 64 k → k + m ≤ (s.getReg .x12).toNat →
      Copied s u k →
      ∃ v, Reaches Image.code u v ∧ v.pc = L + 24 ∧
        v.getReg rd = s.getReg .x10 + BitVec.ofNat 64 (k + m) ∧
        v.getReg rs = s.getReg .x11 + BitVec.ofNat 64 (k + m) ∧ Copied s v (k + m) ∧
        ∀ r, r ≠ rt → r ≠ rc → r ≠ rd → r ≠ rs → v.getReg r = u.getReg r := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
  have hd := hp.dst
  have hs := hp.src
  have hdm := hd
  have hsm := hs
  simp only [Mapped] at hdm hsm
  have h0 : signExtend12 (0 : BitVec 12) = 0 := rfl
  intro m
  induction m with
  | zero => intro _ _ _ _ h _; omega
  | succ m ih =>
    intro u k hpc hc _ hrd hrs hk hcp
    obtain ⟨u₁, hs₁, hpc₁, hr₁, hm₁⟩ := step_lbu (hpc ▸ hlbu)
      (by rw [h0, Sym.add_zero_lit, hrs]; exact hs.valid (by omega))
    obtain ⟨u₂, hr₂, h₂⟩ := hdec.reaches (by rw [hpc₁, hpc]) trivial
    have k₂ (r : Reg) (hr : r ≠ rc) : u₂.getReg r = u₁.getReg r :=
      keepE_reg h₂ (fun p hp ↦ List.mem_cons_of_mem _ hp) (by simp [hr])
    obtain ⟨u₃, hs₃, hpc₃, hr₃, hb₃, hu₃⟩ := step_sb (code := Image.code) (s := u₂)
      (by rw [h₂.pc]; exact hsb) (by
        rw [h0, Sym.add_zero_lit, k₂ rd (Ne.symm h4), lbu_other hr₁ (Ne.symm h2), hrd]
        exact hd.valid (by omega))
    obtain ⟨u₄, hr₄, h₄⟩ := htail.reaches (by
      rw [hpc₃, h₂.pc]; show L + 8 + 4 = L + 12; rw [BitVec.add_assoc]; rfl) trivial
    have k₄ (r : Reg) (hr1 : r ≠ rd) (hr2 : r ≠ rs) : u₄.getReg r = u₃.getReg r :=
      keepE_reg h₄ (fun p hp ↦ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
        (by simp [hr1, hr2])
    have hm₄ (a : Word) : u₄.getMem a = u₃.getMem a := h₄.frame a (by simp [tailCE])
    have hm₂ (a : Word) : u₂.getMem a = u₁.getMem a := h₂.frame a (by simp [decE])
    have hrt : (u₂.getReg rt).truncate 8 = byteAt s (s.getReg .x11 + BitVec.ofNat 64 k) := by
      rw [k₂ rt h1, lbu_rd hr₁ h7, h0, Sym.add_zero_lit, hrs, truncate_zeroExtend,
        hcp.src hp (Nat.le_refl _) (by omega)]
    have hrd₂ : u₂.getReg rd = s.getReg .x10 + BitVec.ofNat 64 k := by
      rw [k₂ rd (Ne.symm h4), lbu_other hr₁ (Ne.symm h2), hrd]
    rw [h0, Sym.add_zero_lit, hrd₂, hrt] at hb₃
    have hreg (r : Reg) (a1 : r ≠ rt) (a2 : r ≠ rc) (a3 : r ≠ rd) (a4 : r ≠ rs) :
        u₄.getReg r = u.getReg r := by
      rw [k₄ r a3 a4, hr₃, k₂ r a2, lbu_other hr₁ a1]
    have hrd₄ : u₄.getReg rd = s.getReg .x10 + BitVec.ofNat 64 (k + 1) := by
      rw [h₄.2.1 _ (List.mem_cons_self ..)]
      show u₃.getReg rd + 1 = _
      rw [hr₃, hrd₂, BitVec.add_assoc, BitVec.ofNat_add]; rfl
    have hrs₄ : u₄.getReg rs = s.getReg .x11 + BitVec.ofNat 64 (k + 1) := by
      rw [h₄.2.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))]
      show u₃.getReg rs + 1 = _
      rw [hr₃, k₂ rs (Ne.symm h5), lbu_other hr₁ (Ne.symm h3), hrs, BitVec.add_assoc,
        BitVec.ofNat_add]; rfl
    have hrc₃ : u₃.getReg rc = u.getReg rc + 0xffffffffffffffff := by
      rw [hr₃, h₂.2.1 _ (List.mem_cons_self ..)]
      show u₁.getReg rc + _ = _
      rw [lbu_other hr₁ (Ne.symm h1)]
      rfl
    have hbyte (a : Word) : byteAt u₄ a = if a = s.getReg .x10 + BitVec.ofNat 64 k then
        byteAt s (s.getReg .x11 + BitVec.ofNat 64 k) else byteAt u a := by
      have hb : byteAt u₄ a = byteAt u₃ a := by simp only [byteAt_eq, hm₄]
      rw [hb, hb₃]
      split
      · rfl
      · simp only [byteAt_eq, hm₂, hm₁]
    have hcp' : Copied s u₄ (k + 1) := by
      refine hcp.extend hp (by omega) ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩ fun i hi ↦ ?_
      · rw [hbyte, ite_eq_right fun h ↦ ha (by rw [h]; addr_omega [hdm, hk])]
      · rw [hm₄, hu₃ a ha, hm₂, hm₁]
      · rw [hbyte, ite_eq_left (by rw [show i = 0 by omega]; rfl), show i = 0 by omega]; rfl
    have hreach : Reaches Image.code u u₄ := by
      obtain ⟨n₂, hn₂⟩ := hr₂
      obtain ⟨n₄, hn₄⟩ := hr₄
      exact ⟨1 + n₂ + 1 + n₄, ((hs₁.trans hn₂).trans hs₃).trans hn₄⟩
    have pc₄ := h₄.pc
    rv_eval [hrc₃] at pc₄
    have hdec' : (u.getReg rc - 1).toNat = m := by
      rw [BitVec.toNat_sub, hc, show (1 : Word).toNat = 1 from rfl]
      omega
    rcases eq_ite_cases pc₄ with ⟨hne, hpc₄⟩ | ⟨hne, hpc₄⟩
    · have hm0 : m ≠ 0 := by
        intro hz
        simp only [bne_iff_ne, ne_eq] at hne
        exact hne (BitVec.eq_of_toNat_eq (by rw [hdec', hz]; rfl))
      have hc₄ : (u₄.getReg rc).toNat = m := by
        rw [k₄ rc h4 h5, hrc₃, BitVec.toNat_add, hc,
          show (0xffffffffffffffff : Word).toNat = 2 ^ 64 - 1 from rfl]
        omega
      obtain ⟨v, hrv, hpcv, hrdv, hrsv, hcpv, hregv⟩ := ih u₄ (k + 1) hpc₄ hc₄ (by omega) hrd₄
        hrs₄ (by omega) hcp'
      refine ⟨v, hreach.trans hrv, hpcv, by rw [hrdv, show k + 1 + m = k + (m + 1) by omega],
        by rw [hrsv, show k + 1 + m = k + (m + 1) by omega],
        by rw [show k + (m + 1) = k + 1 + m by omega]; exact hcpv,
        fun r a1 a2 a3 a4 ↦ (hregv r a1 a2 a3 a4).trans (hreg r a1 a2 a3 a4)⟩
    · have hm0 : m = 0 := by
        simp only [bne_iff_ne, ne_eq, Classical.not_not] at hne
        rw [← hdec', hne]; rfl
      subst hm0
      exact ⟨u₄, hreach, hpc₄, hrd₄, hrs₄, hcp', hreg⟩

/-- A block's register, pc and memory facts as words of the state it starts from. -/
macro "blk" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [reduceReg, E.eval, BinOp.eval, CmpOp.eval, Addr.eval, add_zero_lit]
    $[$loc]?)

/-- A branch condition of a block as a proposition on `toNat`s or equalities. -/
macro "cond" : tactic =>
  `(tactic| (dsimp only [E.eval, BinOp.eval, CmpOp.eval]; simp only [BitVec.ult, wordToNatLit,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt, beq_iff_eq,
    bne_iff_ne, ne_eq,
    Bool.not_eq_false, Bool.not_eq_false', beq_eq_false_iff_ne, bne_eq_false_iff_eq]))

theorem pcT {x : Expect} {u v : MachineState} (h : x.Holds u v) {op : CmpOp} {a b : E}
    {T F : Word} (hx : x.pc = .ite op a b (.c T) (.c F))
    (hc : op.eval (a.eval u) (b.eval u) = true) : v.pc = T := by
  rw [h.1, hx]; simp only [E.eval, hc, ↓reduceIte]

theorem pcF {x : Expect} {u v : MachineState} (h : x.Holds u v) {op : CmpOp} {a b : E}
    {T F : Word} (hx : x.pc = .ite op a b (.c T) (.c F))
    (hc : op.eval (a.eval u) (b.eval u) = false) : v.pc = F := by
  rw [h.1, hx]; simp only [E.eval, hc, Bool.false_eq_true, ↓reduceIte]

/-! ## The end -/

/-- `ret`: pop the frame and return, every byte copied. -/
theorem ret_ok {C : FwdCode} (hC : C.Ok) {u : MachineState} (hpc : u.pc = C.ret)
    (hx2 : u.getReg .x2 = s.getReg .x2 - 16) (hk : ∀ r ∈ keepC, u.getReg r = s.getReg r)
    (hc : Copied s u (s.getReg .x12).toNat) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧ MemcpyPost s t := by
  obtain ⟨t, hr, h⟩ := hC.ret.reaches hpc trivial
  have k := keepOf h rfl keepC
  have hm := sameOf h rfl
  have e2 := h.reg .x2 rfl
  have p := h.1
  simp only [retE] at p
  blk at e2 p
  refine ⟨t, hr, ?_, fun r hr' ↦ ?_, ⟨(k .x10 (by decide)).trans (hk .x10 (by decide)), ?_, ?_⟩⟩
  · rw [p, hk .x1 (by decide)]
    rfl
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | hr'
    · rw [e2, hx2]; exact BitVec.sub_add_cancel _ _
    · have : r ∈ keepC := by simp only [keepC, List.mem_cons, List.not_mem_nil, or_false]; tauto
      rw [k r this, hk r this]
  · refine bytesAt_eq_iff.mpr fun i hi ↦ ?_
    rw [← hc.bytes i hi]
    simp only [byteAt_eq, hm]
  · exact hc.frame.trans (ByteFrame.of_same hm _) fun _ h ↦ h

/-- After the doublewords, at the tail: `h` bytes before them and `J` of them copied. -/
structure Done (C : FwdCode) (s u : MachineState) (h : Nat) : Prop where
  pc : u.pc = C.tail
  x13 : (u.getReg .x13).toNat =
    (s.getReg .x10).toNat + h + 8 * (((s.getReg .x12).toNat - h) / 8)
  x11 : u.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 h
  x12 : (u.getReg .x12).toNat = (s.getReg .x12).toNat - h
  x15 : (u.getReg .x15).toNat = 8 * (((s.getReg .x12).toNat - h) / 8)
  x2 : u.getReg .x2 = s.getReg .x2 - 16
  keep : ∀ r ∈ keepC, u.getReg r = s.getReg r
  copied : Copied s u (h + 8 * (((s.getReg .x12).toNat - h) / 8))

/-- From the tail: the last bytes, one at a time, and return. -/
theorem tail_ok {C : FwdCode} (hC : C.Ok) (hp : FwdPre s) {u : MachineState} {h : Nat}
    (hd : Done C s u h) (hh : h ≤ (s.getReg .x12).toNat) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧ MemcpyPost s t := by
  have hdm := hp.dst
  have hsm := hp.src
  simp only [Mapped] at hdm hsm
  obtain ⟨u₁, hr₁, h₁⟩ := hC.tail.reaches hd.pc trivial
  have k₁ := keepOf h₁ rfl (.x2 :: .x13 :: keepC)
  have hm₁ := sameOf h₁ rfl
  have e11 := h₁.reg .x11 rfl
  have e12 := h₁.reg .x12 rfl
  blk at e11 e12
  have hk₁ : ∀ r ∈ keepC, u₁.getReg r = s.getReg r :=
    fun r hr ↦ (k₁ r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))).trans (hd.keep r hr)
  have hc₁ := hd.copied.same hm₁
  have hr7 : (u.getReg .x12 &&& 7).toNat = ((s.getReg .x12).toNat - h) % 8 := by
    rw [show u.getReg .x12 &&& 7 = u.getReg .x12 &&& 7#64 from rfl, toNat_and7, hd.x12]
  have hx2₁ : u₁.getReg .x2 = s.getReg .x2 - 16 := (k₁ .x2 (by decide)).trans hd.x2
  have hx13 := hd.x13
  have hx13₁ : u₁.getReg .x13 = u.getReg .x13 := k₁ .x13 (by decide)
  by_cases h0 : ((s.getReg .x12).toNat - h) % 8 = 0
  · rw [show h + 8 * (((s.getReg .x12).toNat - h) / 8) = (s.getReg .x12).toNat by omega] at hc₁
    obtain ⟨t, hr, ht⟩ := ret_ok hC (pcT h₁ rfl (by
      cond; rw [BitVec.toNat_add, hr7, h0]; omega)) hx2₁ hk₁ hc₁
    exact ⟨t, hr₁.trans hr, ht⟩
  · have hx13w : u₁.getReg .x13 =
        s.getReg .x10 + BitVec.ofNat 64 (h + 8 * (((s.getReg .x12).toNat - h) / 8)) := by
      rw [hx13₁]
      apply BitVec.eq_of_toNat_eq
      rw [hx13, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have hx11w : u₁.getReg .x11 =
        s.getReg .x11 + BitVec.ofNat 64 (h + 8 * (((s.getReg .x12).toNat - h) / 8)) := by
      rw [e11, hd.x11]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, hd.x15, BitVec.toNat_add,
        BitVec.toNat_ofNat]
      omega
    obtain ⟨v, hrv, hpcv, -, -, hcv, hregv⟩ := copy_loop hC.lbu2 hC.dec2 hC.sb2 hC.tail2
      (by decide) hp (((s.getReg .x12).toNat - h) % 8) u₁ _
      (pcF h₁ rfl (by cond; rw [BitVec.toNat_add, hr7]; omega))
      (by rw [e12, hr7]) (by omega) hx13w hx11w (by omega) hc₁
    rw [show h + 8 * (((s.getReg .x12).toNat - h) / 8) + ((s.getReg .x12).toNat - h) % 8 =
      (s.getReg .x12).toNat by omega] at hcv
    have hreg (r : Reg) (hr : r ∈ Reg.x2 :: keepC) : v.getReg r = u₁.getReg r :=
      hregv r (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide))
        (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide))
    have hx2v := (hreg .x2 (by decide)).trans hx2₁
    have hkv : ∀ r ∈ keepC, v.getReg r = s.getReg r :=
      fun r hr ↦ (hreg r (List.mem_cons_of_mem _ hr)).trans (hk₁ r hr)
    rcases hC.bytesExit with he | he
    · obtain ⟨t, hr, ht⟩ := ret_ok hC (hpcv.trans he) hx2v hkv hcv
      exact ⟨t, hr₁.trans (hrv.trans hr), ht⟩
    · obtain ⟨w, hrw, hw⟩ := he.reaches hpcv trivial
      have kw := keepOf hw rfl (.x2 :: keepC)
      obtain ⟨t, hr, ht⟩ := ret_ok hC (pcC hw rfl) ((kw .x2 (by decide)).trans hx2v)
        (fun r hr ↦ (kw r (List.mem_cons_of_mem _ hr)).trans (hkv r hr))
        (hcv.same (sameOf hw rfl))
      exact ⟨t, hr₁.trans (hrv.trans (hrw.trans hr)), ht⟩

/-! ## Doublewords, source and destination aligned -/

/-- In the loop at `C.coLoop`, `j` doublewords done after `h` bytes. -/
structure DwInv (C : FwdCode) (s u : MachineState) (h j : Nat) : Prop where
  pc : u.pc = C.coLoop
  x14 : u.getReg .x14 = s.getReg .x10 + BitVec.ofNat 64 (h + 8 * j)
  x16 : u.getReg .x16 = s.getReg .x11 + BitVec.ofNat 64 (h + 8 * j)
  x13 : (u.getReg .x13).toNat =
    (s.getReg .x10).toNat + h + 8 * (((s.getReg .x12).toNat - h) / 8)
  x11 : u.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 h
  x12 : (u.getReg .x12).toNat = (s.getReg .x12).toNat - h
  x15 : (u.getReg .x15).toNat = 8 * (((s.getReg .x12).toNat - h) / 8)
  x2 : u.getReg .x2 = s.getReg .x2 - 16
  lt : h + 8 * j + 8 ≤ (s.getReg .x12).toNat
  ald : ((s.getReg .x10).toNat + h) % 8 = 0
  als : ((s.getReg .x11).toNat + h) % 8 = 0
  keep : ∀ r ∈ keepC, u.getReg r = s.getReg r
  copied : Copied s u (h + 8 * j)

/-- An aligned doubleword stored at `dst + k` from the source's at `src + k`. -/
theorem Copied.dword {u v : MachineState} {k : Nat} (h : Copied s u k) (hp : FwdPre s)
    (hk : k + 8 ≤ (s.getReg .x12).toNat)
    (hd8 : (s.getReg .x10 + BitVec.ofNat 64 k).toNat % 8 = 0)
    (hs8 : (s.getReg .x11 + BitVec.ofNat 64 k).toNat % 8 = 0)
    (hm : v.getMem (s.getReg .x10 + BitVec.ofNat 64 k) = u.getMem (s.getReg .x11 + BitVec.ofNat 64 k))
    (hf : ∀ a, a ≠ s.getReg .x10 + BitVec.ofNat 64 k → v.getMem a = u.getMem a) :
    Copied s v (k + 8) := by
  have hd := hp.dst
  have hs := hp.src
  simp only [Mapped] at hd hs
  refine h.extend hp hk (ByteFrame.of_single hd8 hf) fun i hi ↦ ?_
  rw [← h.src hp (by omega) (by omega), BitVec.ofNat_add, ← BitVec.add_assoc, ← BitVec.add_assoc,
    byteAt_add hd8 hi, byteAt_add hs8 hi, hm]

theorem dw_body {C : FwdCode} (hC : C.Ok) {h : Nat} (hp : FwdPre s) (u : MachineState)
    (hu : ∃ j, DwInv C s u h j) :
    (∃ v, Reaches Image.code u v ∧ Done C s v h) ∨
      (∃ v, Reaches Image.code u v ∧ (∃ j, DwInv C s v h j) ∧
        (v.getReg .x13).toNat - (v.getReg .x14).toNat <
          (u.getReg .x13).toNat - (u.getReg .x14).toNat) := by
  obtain ⟨j, hj⟩ := hu
  have hd := hp.dst
  have hs := hp.src
  have hdm := hd
  have hsm := hs
  simp only [Mapped] at hdm hsm
  have hlt := hj.lt
  have hald := hj.ald
  have hals := hj.als
  have hx14 := hj.x14
  have hx16 := hj.x16
  have hx13 := hj.x13
  have hd8 : (s.getReg .x10 + BitVec.ofNat 64 (h + 8 * j)).toNat % 8 = 0 := by addr_omega [hlt, hdm, hald]
  have hs8 : (s.getReg .x11 + BitVec.ofNat 64 (h + 8 * j)).toNat % 8 = 0 := by addr_omega [hlt, hsm, hals]
  obtain ⟨v, hr, hv⟩ := hC.coLoop.reaches hj.pc (by
    simp only [coLoopE, Oblig.all, Oblig.holds, Addr.eval, E.eval, add_zero_lit, hx14, hx16]
    exact ⟨hd.valid8 (by addr_omega [hlt, hdm]) (by addr_omega [hlt, hdm]) hd8,
      hs.valid8 (by addr_omega [hlt, hsm]) (by addr_omega [hlt, hsm]) hs8⟩)
  have kv := keepOf hv rfl (.x2 :: .x11 :: .x12 :: .x13 :: .x15 :: keepC)
  have hw := memOf hv rfl
  have e14 := hv.reg .x14 rfl
  have e16 := hv.reg .x16 rfl
  blk at hw e14 e16
  rw [hx14, hx16] at hw
  have hcp : Copied s v (h + 8 * (j + 1)) := by
    rw [show h + 8 * (j + 1) = h + 8 * j + 8 by omega]
    exact hj.copied.dword hp (by omega) hd8 hs8 hw fun a ha ↦ frameOf hv rfl a (by
      simp only [Addr.eval, E.eval, add_zero_lit, hx14]; exact ha)
  have hkeep : ∀ r ∈ keepC, v.getReg r = s.getReg r :=
    fun r hr' ↦ (kv r (by simp [hr'])).trans (hj.keep r hr')
  have hx14v : v.getReg .x14 = s.getReg .x10 + BitVec.ofNat 64 (h + 8 * (j + 1)) := by
    rw [e14, hx14]; addr_omega [hlt, hdm]
  have hx16v : v.getReg .x16 = s.getReg .x11 + BitVec.ofNat 64 (h + 8 * (j + 1)) := by
    rw [e16, hx16]; addr_omega [hlt, hsm]
  have hx13v := kv .x13 (by decide)
  have hx2v := kv .x2 (by decide)
  have hx11v := kv .x11 (by decide)
  have hx12v := kv .x12 (by decide)
  have hx15v := kv .x15 (by decide)
  by_cases hlast : h + 8 * (j + 1) + 8 ≤ (s.getReg .x12).toNat
  · refine Or.inr ⟨v, hr, ⟨j + 1, pcT hv rfl ?_, hx14v, hx16v,
      by rw [hx13v]; exact hx13, by rw [hx11v]; exact hj.x11, by rw [hx12v]; exact hj.x12,
      by rw [hx15v]; exact hj.x15, by rw [hx2v]; exact hj.x2, hlast, hald, hals, hkeep, hcp⟩, ?_⟩
    · cond; rw [hx14]; addr_omega [hlast, hlt, hdm, hx13]
    · rw [hx14v, hx13v, hx14]; addr_omega [hlast, hlt, hdm, hx13]
  · have hW : h + 8 * (j + 1) = h + 8 * (((s.getReg .x12).toNat - h) / 8) := by omega
    refine Or.inl ⟨v, hr, ⟨pcF hv rfl ?_, by rw [hx13v]; exact hx13,
      by rw [hx11v]; exact hj.x11, by rw [hx12v]; exact hj.x12, by rw [hx15v]; exact hj.x15,
      by rw [hx2v]; exact hj.x2, hkeep, hW ▸ hcp⟩⟩
    cond; rw [hx14]; addr_omega [hlast, hlt, hdm, hx13]

/-! ## After the head -/

/-- At the shift path's entry: `h` bytes copied up to an aligned destination, the source then
not aligned. -/
structure AtSh (C : FwdCode) (s u : MachineState) (h : Nat) : Prop where
  pc : u.pc = C.sh0
  x11 : u.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 h
  x12 : (u.getReg .x12).toNat = (s.getReg .x12).toNat - h
  x13 : (u.getReg .x13).toNat =
    (s.getReg .x10).toNat + h + 8 * (((s.getReg .x12).toNat - h) / 8)
  x14 : u.getReg .x14 = s.getReg .x10 + BitVec.ofNat 64 h
  x15 : (u.getReg .x15).toNat = 8 * (((s.getReg .x12).toNat - h) / 8)
  x16 : (u.getReg .x16).toNat = ((s.getReg .x11).toNat + h) % 8
  x2 : u.getReg .x2 = s.getReg .x2 - 16
  keep : ∀ r ∈ keepC, u.getReg r = s.getReg r
  copied : Copied s u h
  n16 : 16 ≤ (s.getReg .x12).toNat
  hh : h < 8
  ald : ((s.getReg .x10).toNat + h) % 8 = 0
  als : ((s.getReg .x11).toNat + h) % 8 ≠ 0

/-- The shift path reaches the tail. -/
def ShiftOk (C : FwdCode) : Prop :=
  ∀ s u h, FwdPre s → AtSh C s u h → ∃ v, Reaches Image.code u v ∧ Done C s v h

/-- From `C.setup`, `h` bytes copied up to an aligned destination: the doublewords, then the
rest. -/
theorem setup_ok {C : FwdCode} (hC : C.Ok) (hsh : ShiftOk C) (hp : FwdPre s) {u : MachineState}
    {h : Nat} (hpc : u.pc = C.setup) (hn : 16 ≤ (s.getReg .x12).toNat) (hh : h < 8)
    (hald : ((s.getReg .x10).toNat + h) % 8 = 0)
    (hx11 : u.getReg .x11 = s.getReg .x11) (hx12 : u.getReg .x12 = s.getReg .x12)
    (hx13 : (u.getReg .x13).toNat = h) (hx14 : u.getReg .x14 = s.getReg .x10 + BitVec.ofNat 64 h)
    (hx2 : u.getReg .x2 = s.getReg .x2 - 16) (hk : ∀ r ∈ keepC, u.getReg r = s.getReg r)
    (hc : Copied s u h) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧ MemcpyPost s t := by
  have hdm := hp.dst
  have hsm := hp.src
  simp only [Mapped] at hdm hsm
  have h13 : u.getReg .x13 = BitVec.ofNat 64 h := BitVec.eq_of_toNat_eq (by
    rw [hx13, BitVec.toNat_ofNat]; omega)
  obtain ⟨u₁, hr₁, h₁⟩ := hC.setup.reaches hpc trivial
  have k₁ := keepOf h₁ rfl (.x2 :: .x14 :: keepC)
  have hm₁ := sameOf h₁ rfl
  have e11 := h₁.reg .x11 rfl
  have e12 := h₁.reg .x12 rfl
  have e13 := h₁.reg .x13 rfl
  have e15 := h₁.reg .x15 rfl
  have e16 := h₁.reg .x16 rfl
  blk at e11 e12 e13 e15 e16
  have hsub : (u.getReg .x12 - u.getReg .x13).toNat = (s.getReg .x12).toNat - h := by
    rw [BitVec.toNat_sub, hx12, hx13]; omega
  have hW := and_not7 (u.getReg .x12 - u.getReg .x13)
  rw [hsub] at hW
  have hend : (u₁.getReg .x13).toNat =
      (s.getReg .x10).toNat + h + 8 * (((s.getReg .x12).toNat - h) / 8) := by
    rw [e13, BitVec.toNat_add, hW, hx14, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hsrc : u₁.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 h := by rw [e11, hx11, h13]
  have h16 : (u₁.getReg .x16).toNat = ((s.getReg .x11).toNat + h) % 8 := by
    rw [e16, show (u.getReg .x11 + u.getReg .x13) &&& (7 : Word) =
      (u.getReg .x11 + u.getReg .x13) &&& 7#64 from rfl, toNat_and7, hx11, h13,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hkeep₁ : ∀ r ∈ keepC, u₁.getReg r = s.getReg r :=
    fun r hr ↦ (k₁ r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))).trans (hk r hr)
  have hx2₁ := (k₁ .x2 (by decide)).trans hx2
  have hx14₁ := (k₁ .x14 (by decide)).trans hx14
  have hx12₁ : (u₁.getReg .x12).toNat = (s.getReg .x12).toNat - h := by rw [e12, hsub]
  have hx15₁ : (u₁.getReg .x15).toNat = 8 * (((s.getReg .x12).toNat - h) / 8) := by
    rw [e15, hW]; omega
  by_cases hals : ((s.getReg .x11).toNat + h) % 8 = 0
  · obtain ⟨u₂, hr₂, h₂⟩ := hC.co.reaches (pcT h₁ rfl (by
      cond; apply BitVec.eq_of_toNat_eq; rw [← e16, h16, hals]; rfl)) trivial
    have k₂ := keepOf h₂ rfl (.x2 :: .x11 :: .x12 :: .x13 :: .x14 :: .x15 :: keepC)
    obtain ⟨u₃, hr₃, h₃⟩ := hC.coPre.reaches (pcF h₂ rfl (by
      cond; rw [hx14₁, hend, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)) trivial
    have k₃ := keepOf h₃ rfl (.x2 :: .x11 :: .x12 :: .x13 :: .x14 :: .x15 :: keepC)
    have e16₃ := h₃.reg .x16 rfl
    blk at e16₃
    have hm (a : Word) : u₃.getMem a = u.getMem a :=
      (sameOf h₃ rfl a).trans ((sameOf h₂ rfl a).trans (hm₁ a))
    have kk (r : Reg) (hr : r ∈ Reg.x2 :: Reg.x11 :: Reg.x12 :: Reg.x13 :: Reg.x14 :: Reg.x15 :: keepC) :
        u₃.getReg r = u₁.getReg r := (k₃ r hr).trans (k₂ r hr)
    have hinv : DwInv C s u₃ h 0 := {
      pc := pcC h₃ rfl
      x14 := by rw [kk .x14 (by decide), hx14₁, Nat.mul_zero, Nat.add_zero]
      x16 := by rw [e16₃, k₂ .x11 (by decide), hsrc, Nat.mul_zero, Nat.add_zero]
      x13 := by rw [kk .x13 (by decide), hend]
      x11 := by rw [kk .x11 (by decide), hsrc]
      x12 := by rw [kk .x12 (by decide), hx12₁]
      x15 := by rw [kk .x15 (by decide), hx15₁]
      x2 := by rw [kk .x2 (by decide), hx2₁]
      lt := by omega
      ald := hald
      als := hals
      keep := fun r hr ↦ (kk r (by simp [hr])).trans (hkeep₁ r hr)
      copied := hc.same hm }
    obtain ⟨v, hrv, hdv⟩ := Reaches.loop (fun u ↦ ∃ j, DwInv C s u h j)
      (fun u ↦ (u.getReg .x13).toNat - (u.getReg .x14).toNat) (Done C s · h) (dw_body hC hp) u₃
      ⟨0, hinv⟩
    obtain ⟨t, hr, ht⟩ := tail_ok hC hp hdv (by omega)
    exact ⟨t, hr₁.trans (hr₂.trans (hr₃.trans (hrv.trans hr))), ht⟩
  · obtain ⟨v, hrv, hdv⟩ := hsh s u₁ h hp {
      pc := pcF h₁ rfl (by
        cond; intro h0; apply hals; rw [← h16, e16, h0]; rfl)
      x11 := hsrc
      x12 := hx12₁
      x13 := hend
      x14 := hx14₁
      x15 := hx15₁
      x16 := h16
      x2 := hx2₁
      keep := hkeep₁
      copied := hc.same hm₁
      n16 := hn
      hh := hh
      ald := hald
      als := hals }
    obtain ⟨t, hr, ht⟩ := tail_ok hC hp hdv (by omega)
    exact ⟨t, hr₁.trans (hrv.trans hr), ht⟩

/-! ## The forward copy -/

/-- **The forward copy**, from `C.size` with `sp` already down by 16, given its shift path. -/
theorem fwd_of {C : FwdCode} (hC : C.Ok) (hsh : ShiftOk C) (hp : FwdPre s) {u : MachineState}
    (hpc : u.pc = C.size) (hx2 : u.getReg .x2 = s.getReg .x2 - 16)
    (hk : ∀ r ∈ Reg.x11 :: Reg.x12 :: keepC, u.getReg r = s.getReg r)
    (hm : ∀ a, u.getMem a = s.getMem a) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧ MemcpyPost s t := by
  have hdm := hp.dst
  have hsm := hp.src
  simp only [Mapped] at hdm hsm
  have hc0 : Copied s u 0 := Copied.zero hm
  have hx10 := hk .x10 (by decide)
  have hx11 := hk .x11 (by decide)
  have hx12 := hk .x12 (by decide)
  have hkC : ∀ r ∈ keepC, u.getReg r = s.getReg r := fun r hr ↦ hk r (by simp [hr])
  obtain ⟨u₁, hr₁, h₁⟩ := hC.size.reaches hpc trivial
  have k₁ := keepOf h₁ rfl (.x2 :: .x11 :: .x12 :: keepC)
  have kk₁ (r : Reg) (hr : r ∈ Reg.x11 :: Reg.x12 :: keepC) : u₁.getReg r = s.getReg r :=
    (k₁ r (List.mem_cons_of_mem _ hr)).trans (hk r hr)
  have hc₁ := hc0.same (sameOf h₁ rfl)
  have hx2₁ := (k₁ .x2 (by decide)).trans hx2
  by_cases hsmall : (s.getReg .x12).toNat < 16
  · obtain ⟨u₂, hr₂, h₂⟩ := hC.small.reaches (pcT h₁ rfl (by cond; rw [hx12]; exact hsmall))
      trivial
    have k₂ := keepOf h₂ rfl (.x2 :: .x11 :: .x12 :: keepC)
    have e13 := h₂.reg .x13 rfl
    blk at e13
    have kk₂ (r : Reg) (hr : r ∈ Reg.x11 :: Reg.x12 :: keepC) : u₂.getReg r = s.getReg r :=
      (k₂ r (List.mem_cons_of_mem _ hr)).trans (kk₁ r hr)
    have hx2₂ := (k₂ .x2 (by decide)).trans hx2₁
    have hc₂ := hc₁.same (sameOf h₂ rfl)
    have hkC₂ : ∀ r ∈ keepC, u₂.getReg r = s.getReg r := fun r hr ↦ kk₂ r (by simp [hr])
    by_cases h0 : (s.getReg .x12).toNat = 0
    · obtain ⟨u₃, hr₃, h₃⟩ := hC.jmp.reaches (pcF h₂ rfl (by
        cond; rw [k₁ .x10 (by decide), hk .x10 (by decide), kk₁ .x12 (by decide),
          BitVec.toNat_add, h0]; omega)) trivial
      have k₃ := keepOf h₃ rfl (.x2 :: keepC)
      obtain ⟨t, hr, ht⟩ := ret_ok hC (pcC h₃ rfl) ((k₃ .x2 (by decide)).trans hx2₂)
        (fun r hr ↦ (k₃ r (List.mem_cons_of_mem _ hr)).trans (hkC₂ r hr))
        (h0 ▸ hc₂.same (sameOf h₃ rfl))
      exact ⟨t, hr₁.trans (hr₂.trans (hr₃.trans hr)), ht⟩
    · obtain ⟨v, hrv, hpcv, -, -, hcv, hregv⟩ := copy_loop hC.lbu2 hC.dec2 hC.sb2 hC.tail2
        (by decide) hp (s.getReg .x12).toNat u₂ 0
        (pcT h₂ rfl (by
          cond; rw [k₁ .x10 (by decide), hk .x10 (by decide), kk₁ .x12 (by decide),
            BitVec.toNat_add]; omega))
        (by rw [kk₂ .x12 (by decide)]) (by omega)
        (by rw [e13, k₁ .x10 (by decide), hk .x10 (by decide)]; simp)
        (by rw [kk₂ .x11 (by decide)]; simp) (by omega) hc₂
      rw [Nat.zero_add] at hcv
      have hreg (r : Reg) (hr : r ∈ Reg.x2 :: keepC) : v.getReg r = u₂.getReg r :=
        hregv r (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide))
          (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide))
      have hx2v := (hreg .x2 (by decide)).trans hx2₂
      have hkv : ∀ r ∈ keepC, v.getReg r = s.getReg r :=
        fun r hr ↦ (hreg r (List.mem_cons_of_mem _ hr)).trans (hkC₂ r hr)
      rcases hC.bytesExit with he | he
      · obtain ⟨t, hr, ht⟩ := ret_ok hC (hpcv.trans he) hx2v hkv hcv
        exact ⟨t, hr₁.trans (hr₂.trans (hrv.trans hr)), ht⟩
      · obtain ⟨w, hrw, hw⟩ := he.reaches hpcv trivial
        have kw := keepOf hw rfl (.x2 :: keepC)
        obtain ⟨t, hr, ht⟩ := ret_ok hC (pcC hw rfl) ((kw .x2 (by decide)).trans hx2v)
          (fun r hr ↦ (kw r (List.mem_cons_of_mem _ hr)).trans (hkv r hr))
          (hcv.same (sameOf hw rfl))
        exact ⟨t, hr₁.trans (hr₂.trans (hrv.trans (hrw.trans hr))), ht⟩
  · obtain ⟨u₂, hr₂, h₂⟩ := hC.head.reaches (pcF h₁ rfl (by cond; rw [hx12]; omega)) trivial
    have k₂ := keepOf h₂ rfl (.x2 :: .x11 :: .x12 :: keepC)
    have e13 := h₂.reg .x13 rfl
    have e14 := h₂.reg .x14 rfl
    blk at e13 e14
    have hx10₁ : u₁.getReg .x10 = s.getReg .x10 := kk₁ .x10 (by decide)
    rw [hx10₁] at e13 e14
    have hH : (((0 : Word) - s.getReg .x10) &&& (7 : Word)).toNat =
        (2 ^ 64 - (s.getReg .x10).toNat) % 8 := by
      rw [show ((0 : Word) - s.getReg .x10) &&& (7 : Word) = ((0 : Word) - s.getReg .x10) &&& 7#64
        from rfl, toNat_and7, BitVec.toNat_sub]
      have : (0 : Word).toNat = 0 := rfl
      omega
    have hh8 : (2 ^ 64 - (s.getReg .x10).toNat) % 8 < 8 := Nat.mod_lt _ (by decide)
    have hald : ((s.getReg .x10).toNat + (2 ^ 64 - (s.getReg .x10).toNat) % 8) % 8 = 0 := by omega
    have hx14' : u₂.getReg .x14 =
        s.getReg .x10 + BitVec.ofNat 64 ((2 ^ 64 - (s.getReg .x10).toNat) % 8) := by
      rw [e14]; congr 1; apply BitVec.eq_of_toNat_eq; rw [hH, BitVec.toNat_ofNat]; omega
    have kk₂ (r : Reg) (hr : r ∈ Reg.x11 :: Reg.x12 :: keepC) : u₂.getReg r = s.getReg r :=
      (k₂ r (List.mem_cons_of_mem _ hr)).trans (kk₁ r hr)
    have hx2₂ := (k₂ .x2 (by decide)).trans hx2₁
    have hc₂ := hc₁.same (sameOf h₂ rfl)
    have hkC₂ : ∀ r ∈ keepC, u₂.getReg r = s.getReg r := fun r hr ↦ kk₂ r (by simp [hr])
    by_cases h0 : (2 ^ 64 - (s.getReg .x10).toNat) % 8 = 0
    · exact (setup_ok hC hsh hp (h := 0) (pcT h₂ rfl (by
          cond; rw [hx10₁, BitVec.toNat_add, hH, h0]; omega)) (Nat.le_of_not_lt hsmall)
        (by decide) (by omega) (kk₂ .x11 (by decide)) (kk₂ .x12 (by decide))
        (by rw [e13, hH, h0]) (by rw [hx14', h0]) hx2₂ hkC₂ hc₂).imp
        fun t ⟨hr, ht⟩ ↦ ⟨hr₁.trans (hr₂.trans hr), ht⟩
    · obtain ⟨u₃, hr₃, h₃⟩ := hC.headPre.reaches (pcF h₂ rfl (by
        cond; rw [hx10₁, BitVec.toNat_add, hH]; omega)) trivial
      have k₃ := keepOf h₃ rfl (.x2 :: .x11 :: .x12 :: .x13 :: .x14 :: keepC)
      have e15 := h₃.reg .x15 rfl
      have e16 := h₃.reg .x16 rfl
      have e17 := h₃.reg .x17 rfl
      blk at e15 e16 e17
      obtain ⟨v, hrv, hpcv, -, -, hcv, hregv⟩ := copy_loop hC.lbu1 hC.dec1 hC.sb1 hC.tail1
        (by decide) hp ((2 ^ 64 - (s.getReg .x10).toNat) % 8) u₃ 0
        (pcC h₃ rfl) (by rw [e15, e13, hH]) (by omega)
        (by rw [e16, k₂ .x10 (by decide), hx10₁]; simp)
        (by rw [e17, kk₂ .x11 (by decide)]; simp) (by omega) (hc₂.same (sameOf h₃ rfl))
      rw [Nat.zero_add] at hcv
      have hreg (r : Reg) (hr : r ∈ [Reg.x2, .x11, .x12, .x13, .x14] ++ keepC) :
          v.getReg r = u₃.getReg r :=
        hregv r (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide))
          (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide))
      exact (setup_ok hC hsh hp (hpcv.trans hC.headLoop) (Nat.le_of_not_lt hsmall) hh8 hald
        (by rw [hreg .x11 (by decide), k₃ .x11 (by decide), kk₂ .x11 (by decide)])
        (by rw [hreg .x12 (by decide), k₃ .x12 (by decide), kk₂ .x12 (by decide)])
        (by rw [hreg .x13 (by decide), k₃ .x13 (by decide), e13, hH])
        (by rw [hreg .x14 (by decide), k₃ .x14 (by decide), hx14'])
        (by rw [hreg .x2 (by decide), k₃ .x2 (by decide), hx2₂])
        (fun r hr ↦ (hreg r (List.mem_append_right _ hr)).trans
          ((k₃ r (by simp [hr])).trans (hkC₂ r hr))) hcv).imp
        fun t ⟨hr, ht⟩ ↦ ⟨hr₁.trans (hr₂.trans (hr₃.trans (hrv.trans hr))), ht⟩

end Rv64Verifier.Runtime.Forward
