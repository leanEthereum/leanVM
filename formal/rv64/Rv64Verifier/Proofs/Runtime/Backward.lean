import Rv64Verifier.Proofs.Runtime.BackBlocks
import Rv64Verifier.Proofs.Runtime.ForwardShift

/-!
# `memmove`'s backward copy

From the state after `memmove`'s first block took the backward branch: the destination above the
source (`BwdPre`), copied from the end. The invariant is `BCopied s u k`: the last `k` bytes
copied, nothing written but those and the stack, so every source byte below them is still the
initial one (`BCopied.src`).
-/

namespace Rv64Verifier.Runtime.Backward
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.Runtime.Forward
open Rv64Verifier.Runtime.Memcpy (keepE keepE_reg keepC)
open Rv64Verifier.Runtime.Memset (and_not7)

/-- `memmove`'s precondition when it copies backward: the source not above the destination. -/
structure BwdPre (s : MachineState) : Prop where
  dst : Mapped (s.getReg .x10) (s.getReg .x12).toNat
  src : Mapped (s.getReg .x11) (s.getReg .x12).toNat
  bwd : (s.getReg .x11).toNat ≤ (s.getReg .x10).toNat
  stack : StackOk s 16
  dstStack : Apart (s.getReg .x10) (s.getReg .x12).toNat (stackLo s 16) 16
  srcStack : Apart (s.getReg .x11) (s.getReg .x12).toNat (stackLo s 16) 16

/-- The last `k` bytes copied; nothing written but them and the stack. -/
structure BCopied (s u : MachineState) (k : Nat) : Prop where
  bytes : ∀ i, (s.getReg .x12).toNat - k ≤ i → i < (s.getReg .x12).toNat →
    byteAt u (s.getReg .x10 + BitVec.ofNat 64 i) = byteAt s (s.getReg .x11 + BitVec.ofNat 64 i)
  frame : ByteFrame s u fun a ↦
    Within a (s.getReg .x10 + BitVec.ofNat 64 ((s.getReg .x12).toNat - k)) k ∨
      Within a (stackLo s 16) 16

variable {s : MachineState}

theorem BwdPre.sp (h : BwdPre s) : 0x30 ≤ (s.getReg .x2).toNat ∧
    (s.getReg .x2).toNat ≤ 0xc0000008 ∧ (s.getReg .x2).toNat % 16 = 0 := by
  have := h.stack.bounds (by decide) (by decide)
  omega

theorem BwdPre.buf (hp : BwdPre s) :
    (s.getReg .x2 - 8).toNat = (s.getReg .x2).toNat - 8 ∧ (s.getReg .x2).toNat % 16 = 0 ∧
    ((0x20 ≤ (s.getReg .x2).toNat - 8 ∧ (s.getReg .x2).toNat ≤ 0x78000000) ∨
      (0xa0000000 ≤ (s.getReg .x2).toNat - 8 ∧ (s.getReg .x2).toNat ≤ 0xc0000000)) := by
  have hb := hp.stack.bounds (by decide) (by decide)
  have hv := (validAccess_eight _).mp (hp.stack.valid 1 (by decide))
  simp only [stackLo, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] at hv hb
  have hsp := hp.sp
  refine ⟨by rw [BitVec.toNat_sub]; simp; omega, hsp.2.2, ?_⟩
  omega

theorem BCopied.zero {u : MachineState} (hm : ∀ a, u.getMem a = s.getMem a) : BCopied s u 0 :=
  ⟨fun _ h1 h2 ↦ by omega, ByteFrame.of_same hm _⟩

theorem BCopied.same {u v : MachineState} {k : Nat} (h : BCopied s u k)
    (hm : ∀ a, v.getMem a = u.getMem a) : BCopied s v k :=
  ⟨fun i h1 h2 ↦ by rw [← h.bytes i h1 h2]; simp only [byteAt_eq, hm],
    h.frame.trans (ByteFrame.of_same hm _) fun _ h ↦ h⟩

/-- A source byte below the copied ones is the initial one. -/
theorem BCopied.src {u : MachineState} {k : Nat} (h : BCopied s u k) (hp : BwdPre s)
    (hk : k ≤ (s.getReg .x12).toNat) {i : Nat} (hi : i < (s.getReg .x12).toNat - k) :
    byteAt u (s.getReg .x11 + BitVec.ofNat 64 i) = byteAt s (s.getReg .x11 + BitVec.ofNat 64 i) :=
  h.frame.byte _ fun hw ↦ by
    have hd := hp.dst
    have hs := hp.src
    have hb := hp.bwd
    have hss := hp.srcStack
    rcases hw with hw | hw
    · addr_omega [hw, hd, hs, hb, hk, hi]
    · addr_omega [hw, hs, hss, hi, hk]

/-- A write of the aligned doubleword `B` of the stack. -/
theorem BCopied.stack {u v : MachineState} {k : Nat} (h : BCopied s u k) (hp : BwdPre s)
    {B : Word} (hB : B.toNat % 8 = 0)
    (hB1 : (s.getReg .x2).toNat - 16 ≤ B.toNat) (hB2 : B.toNat + 8 ≤ (s.getReg .x2).toNat)
    (hf : ∀ a, a ≠ B → v.getMem a = u.getMem a) : BCopied s v k := by
  have hsp := hp.sp
  have hd := hp.dst
  have hds := hp.dstStack
  have hfr := ByteFrame.of_single hB hf
  refine ⟨fun i h1 h2 ↦ ?_, h.frame.trans hfr fun a ha ↦ Or.inr ?_⟩
  · rw [← h.bytes i h1 h2]
    exact hfr.byte _ fun hw ↦ by addr_omega [hw, hd, hds, hB1, hB2, h2]
  · simp only [Within, stackLo] at ha ⊢
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

/-- `m` more bytes copied, below the last `k`. -/
theorem BCopied.extend {u v : MachineState} {k m : Nat} (h : BCopied s u k) (hp : BwdPre s)
    (hkm : k + m ≤ (s.getReg .x12).toNat)
    (hf : ByteFrame u v (Within · (s.getReg .x10 +
      BitVec.ofNat 64 ((s.getReg .x12).toNat - (k + m))) m))
    (hb : ∀ i < m, byteAt v (s.getReg .x10 +
        BitVec.ofNat 64 ((s.getReg .x12).toNat - (k + m) + i)) =
      byteAt s (s.getReg .x11 + BitVec.ofNat 64 ((s.getReg .x12).toNat - (k + m) + i))) :
    BCopied s v (k + m) := by
  have hd := hp.dst
  simp only [Mapped] at hd
  refine ⟨fun i h1 h2 ↦ ?_, (h.frame.mono fun a ha ↦ ?_).trans hf fun a ha ↦ Or.inl ?_⟩
  · by_cases hik : (s.getReg .x12).toNat - k ≤ i
    · rw [← h.bytes i hik h2]
      exact hf.byte _ fun hw ↦ by addr_omega [hw, hd, hik, hkm, h2]
    · have := hb (i - ((s.getReg .x12).toNat - (k + m))) (by omega)
      rwa [show (s.getReg .x12).toNat - (k + m) + (i - ((s.getReg .x12).toNat - (k + m))) = i by
        omega] at this
  · rcases ha with ha | ha
    · exact Or.inl (by addr_omega [ha, hd, hkm])
    · exact Or.inr ha
  · addr_omega [ha, hd, hkm]

/-- A sub-doubleword store of `V` at `Q`, of width `w`: the bytes from `Q` are `V`'s, no other
byte changes. -/
theorem store_frame {u v : MachineState} {sk : StoreKind} {Q V : Word}
    (hw : sk.width = 1 ∨ sk.width = 2 ∨ sk.width = 4) (hQ : Q.toNat % sk.width = 0)
    (hm : v.getMem (Q &&& 0xfffffffffffffff8) =
      sk.merge (u.getMem (Q &&& 0xfffffffffffffff8)) (Q &&& 7).toNat V)
    (hf : ∀ x, x ≠ Q &&& 0xfffffffffffffff8 → v.getMem x = u.getMem x) :
    ByteFrame u v (Within · Q sk.width) ∧
      ∀ j < sk.width, byteAt v (Q + BitVec.ofNat 64 j) = extractByte V j := by
  have h8 : Q.toNat % 8 + sk.width ≤ 8 := by rcases hw with hw | hw | hw <;> rw [hw] at hQ ⊢ <;> omega
  rw [mask_eq] at hm hf
  refine ⟨⟨fun a ha ↦ ?_, fun a ha ↦ hf a fun h ↦ ha (by rw [h, toNat_alignDown]; omega)⟩,
    fun j hj ↦ ?_⟩
  · rw [byteAt_eq, byteAt_eq]
    by_cases hk : a &&& ~~~7#64 = Q &&& ~~~7#64
    · rw [hk, hm, extractByte_store sk _ _ hQ (Nat.mod_lt _ (by decide)), ite_eq_right]
      intro hin
      apply ha
      have h1 := congrArg BitVec.toNat hk
      rw [toNat_alignDown, toNat_alignDown] at h1
      simp only [Within]
      omega
    · rw [hf _ hk]
  · have hal := alignDown_add (p := Q) (j := j) (by omega)
    rw [byteAt_eq, hal.1, hm, extractByte_store sk _ _ hQ (Nat.mod_lt _ (by decide)), hal.2,
      ite_eq_left (by omega)]
    congr 1
    omega

/-! ## The byte loops -/

/-- A byte loop copying down: `m` more bytes below the last `k`. -/
theorem bloop {L F : Word} {rd rs rt rt' rl : Reg} (hS : Spec L (bloopE rd rs rt rt' rl L F))
    (hr : rl ≠ rd ∧ rl ≠ rs ∧ rl ≠ rt ∧ rl ≠ rt') (hp : BwdPre s) :
    ∀ m u k, u.pc = L →
      u.getReg rd = s.getReg .x10 + BitVec.ofNat 64 ((s.getReg .x12).toNat - k) →
      u.getReg rs = s.getReg .x11 + BitVec.ofNat 64 ((s.getReg .x12).toNat - k) - 1 →
      u.getReg rl = s.getReg .x10 + BitVec.ofNat 64 ((s.getReg .x12).toNat - k - m) → 0 < m →
      k + m ≤ (s.getReg .x12).toNat → BCopied s u k →
      ∃ v, Reaches Image.code u v ∧ v.pc = F ∧ BCopied s v (k + m) ∧
        ∀ x, x ≠ rd → x ≠ rs → x ≠ rt → x ≠ rt' → v.getReg x = u.getReg x := by
  obtain ⟨h1, h2, h3, h4⟩ := hr
  have hd := hp.dst
  have hs := hp.src
  simp only [Mapped] at hd hs
  intro m
  induction m with
  | zero => intro _ _ _ _ _ _ h _; omega
  | succ m ih =>
    intro u k hpc hrd hrs hrl _ hk hcp
    have hQ : u.getReg rd + 0xffffffffffffffff =
        s.getReg .x10 + BitVec.ofNat 64 ((s.getReg .x12).toNat - (k + 1)) := by
      rw [hrd, add_neg_lit, show (0 : Word) - 0xffffffffffffffff = 1 by decide]
      addr_omega [hd, hk]
    have hP : u.getReg rs = s.getReg .x11 +
        BitVec.ofNat 64 ((s.getReg .x12).toNat - (k + 1)) + BitVec.ofNat 64 0 := by
      rw [hrs]; addr_omega [hs, hk]
    obtain ⟨v, hrv, hv⟩ := hS.reaches hpc (by
      simp only [bloopE, Oblig.all, Oblig.holds, Addr.eval, E.eval, add_zero_lit, hQ, hP]
      exact ⟨valid_of (by decide) (by addr_omega [hd, hk]) (Nat.mod_one _),
        valid_of (by decide) (by addr_omega [hs, hk]) (Nat.mod_one _)⟩)
    have hm := memOf hv rfl
    have hf (x : Word) (hx : x ≠ (u.getReg rd + 0xffffffffffffffff) &&& 0xfffffffffffffff8) :
        v.getMem x = u.getMem x := frameOf hv rfl x (by blk; exact hx)
    blk at hm
    rw [hQ] at hm hf
    obtain ⟨hfr, hbyte⟩ := store_frame (sk := .b) (by decide) (Nat.mod_one _) hm hf
    have hkeep (x : Reg) (a1 : x ≠ rd) (a2 : x ≠ rs) (a3 : x ≠ rt) (a4 : x ≠ rt') :
        v.getReg x = u.getReg x :=
      keepE_reg hv (fun p hp ↦ List.mem_append_right _ hp) (by simp [a1, a2, a3, a4])
    have hcp' : BCopied s v (k + 1) := by
      refine hcp.extend hp (by omega) hfr fun i hi ↦ ?_
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0
      have hb0 := hbyte 0 (by decide)
      rw [BitVec.add_zero] at hb0
      rw [Nat.add_zero, Nat.add_zero, hb0, extractByte_load .bu u (Nat.mod_one _) (by decide), hP,
        BitVec.add_zero, BitVec.add_zero, hcp.src hp (by omega) (by omega)]
    have e_rd : v.getReg rd = u.getReg rd + 0xffffffffffffffff :=
      hv.2.1 _ (List.mem_append_left _ (List.mem_cons_self ..))
    have e_rs : v.getReg rs = u.getReg rs + 0xffffffffffffffff :=
      hv.2.1 _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..))))
    have hrl' := hkeep rl h1 h2 h3 h4
    by_cases hm0 : m = 0
    · subst hm0
      refine ⟨v, hrv, pcF hv rfl ?_, hcp', hkeep⟩
      cond
      rw [hQ, hrl]
      addr_omega [hd, hk]
    · obtain ⟨w, hrw, hpcw, hcw, hkw⟩ := ih v (k + 1) (pcT hv rfl (by
          cond; rw [hQ, hrl]; addr_omega [hd, hk, hm0]))
        (by rw [e_rd, hQ]) (by rw [e_rs, hrs, add_neg_lit,
          show (0 : Word) - 0xffffffffffffffff = 1 by decide]; addr_omega [hs, hk])
        (by rw [hrl', hrl]; congr 2; omega) (by omega) (by omega) hcp'
      exact ⟨w, hrv.trans hrw, hpcw, by rw [show k + (m + 1) = k + 1 + m by omega]; exact hcw,
        fun x a1 a2 a3 a4 ↦ (hkw x a1 a2 a3 a4).trans (hkeep x a1 a2 a3 a4)⟩

/-! ## The end -/

theorem add_zero_sub (x y : Word) : x + (0 - y) = x - y := by bv_omega

theorem neg1 (x : Word) : x + 0xffffffffffffffff = x - 1 := by
  rw [add_neg_lit, show (0 : Word) - 0xffffffffffffffff = 1 by decide]

/-- `ret`: pop the frame and return, every byte copied. -/
theorem bret {u : MachineState} (hpc : u.pc = 0x8001260c)
    (hx2 : u.getReg .x2 = s.getReg .x2 - 16) (hk : ∀ r ∈ keepC, u.getReg r = s.getReg r)
    (hc : BCopied s u (s.getReg .x12).toNat) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧ MemcpyPost s t := by
  obtain ⟨t, hr, h⟩ := mm_ret.reaches hpc trivial
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
    rw [← hc.bytes i (by omega) hi]
    simp only [byteAt_eq, hm]
  · have := hc.frame.trans (ByteFrame.of_same hm _) fun _ h ↦ h
    rwa [Nat.sub_self, BitVec.add_zero] at this

/-- From `0x800125e8`: the `N - k` bytes below the last `k`, one at a time, then return. -/
theorem btail_ok (hp : BwdPre s) {u : MachineState} {k : Nat} (hpc : u.pc = 0x800125e8)
    (hk : k ≤ (s.getReg .x12).toNat)
    (h17 : u.getReg .x17 = s.getReg .x10 + BitVec.ofNat 64 ((s.getReg .x12).toNat - k))
    (h12 : u.getReg .x12 = BitVec.ofNat 64 ((s.getReg .x12).toNat - k))
    (h14 : u.getReg .x14 = s.getReg .x11 + BitVec.ofNat 64 ((s.getReg .x12).toNat - k))
    (hx2 : u.getReg .x2 = s.getReg .x2 - 16) (hkp : ∀ r ∈ keepC, u.getReg r = s.getReg r)
    (hc : BCopied s u k) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧ MemcpyPost s t := by
  have hd := hp.dst
  have hs := hp.src
  simp only [Mapped] at hd hs
  obtain ⟨u₁, r₁, h₁⟩ := mm_btail.reaches hpc trivial
  have k₁ := keepOf h₁ rfl (.x2 :: .x12 :: .x14 :: .x17 :: keepC)
  have e11 := h₁.reg .x11 rfl
  blk at e11
  have hd' : u.getReg .x17 - u.getReg .x12 = s.getReg .x10 := by
    rw [h17, h12]; addr_omega [hd, hk]
  have hm₁ := sameOf h₁ rfl
  have hk₁ : ∀ r ∈ keepC, u₁.getReg r = s.getReg r := fun r hr ↦ (k₁ r (by simp [hr])).trans (hkp r hr)
  have hx2₁ := (k₁ .x2 (by decide)).trans hx2
  by_cases h0 : (s.getReg .x12).toNat - k = 0
  · obtain ⟨t, hr, ht⟩ := bret (pcT h₁ rfl (by cond; rw [hd', h17, h0]; simp)) hx2₁ hk₁
      (by rw [show (s.getReg .x12).toNat = k by omega]; exact hc.same hm₁)
    exact ⟨t, r₁.trans hr, ht⟩
  · obtain ⟨u₂, r₂, h₂⟩ := mm_btpre.reaches (pcF h₁ rfl (by
      cond; rw [hd', h17]; addr_omega [hd, hk, h0])) trivial
    have k₂ := keepOf h₂ rfl (.x2 :: .x11 :: .x12 :: .x17 :: keepC)
    have e14 := h₂.reg .x14 rfl
    blk at e14
    obtain ⟨v, rv, pcv, hcv, hkv⟩ := bloop mm_btloop (by decide) hp ((s.getReg .x12).toNat - k)
      u₂ k (pcC h₂ rfl) (by rw [k₂ .x17 (by decide), k₁ .x17 (by decide), h17])
      (by rw [e14, k₁ .x14 (by decide), h14, neg1])
      (by rw [k₂ .x11 (by decide), e11, hd']; simp) (by omega) (by omega)
      (hc.same fun a ↦ (sameOf h₂ rfl a).trans (hm₁ a))
    rw [show k + ((s.getReg .x12).toNat - k) = (s.getReg .x12).toNat by omega] at hcv
    have hreg (r : Reg) (hr : r ∈ Reg.x2 :: keepC) : v.getReg r = u₁.getReg r := by
      rw [hkv r (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide))
        (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide)),
        k₂ r (by simp at hr ⊢; tauto)]
    obtain ⟨t, hr, ht⟩ := bret pcv (by rw [hreg .x2 (by decide), hx2₁])
      (fun r hr ↦ (hreg r (by simp [hr])).trans (hk₁ r hr)) hcv
    exact ⟨t, r₁.trans (r₂.trans (rv.trans hr)), ht⟩

/-- At `0x800125dc`, after the doublewords: the head's `hb` bytes and `J` doublewords below them
copied. -/
structure BDone (s u : MachineState) (hb : Nat) : Prop where
  pc : u.pc = 0x800125dc
  x13 : u.getReg .x13 = s.getReg .x10 + BitVec.ofNat 64 ((s.getReg .x12).toNat - hb)
  x16 : u.getReg .x16 = 0 - BitVec.ofNat 64 (8 * (((s.getReg .x12).toNat - hb) / 8))
  x14 : u.getReg .x14 = s.getReg .x11 + BitVec.ofNat 64 ((s.getReg .x12).toNat - hb)
  x15 : (u.getReg .x15).toNat = (s.getReg .x12).toNat - hb
  x2 : u.getReg .x2 = s.getReg .x2 - 16
  keep : ∀ r ∈ keepC, u.getReg r = s.getReg r
  copied : BCopied s u (hb + 8 * (((s.getReg .x12).toNat - hb) / 8))
  le : hb ≤ (s.getReg .x12).toNat

theorem tailb_ok (hp : BwdPre s) {u : MachineState} {hb : Nat} (hd : BDone s u hb) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧ MemcpyPost s t := by
  have hdm := hp.dst
  have hsm := hp.src
  simp only [Mapped] at hdm hsm
  have hle := hd.le
  obtain ⟨u₁, r₁, h₁⟩ := mm_tailb.reaches hd.pc trivial
  have k₁ := keepOf h₁ rfl (.x2 :: keepC)
  have e12 := h₁.reg .x12 rfl
  have e14 := h₁.reg .x14 rfl
  have e17 := h₁.reg .x17 rfl
  blk at e12 e14 e17
  have h7 := hd.x15
  exact (btail_ok hp (k := hb + 8 * (((s.getReg .x12).toNat - hb) / 8)) (pcC h₁ rfl) (by omega)
    (by rw [e17, hd.x13, hd.x16, add_zero_sub]; addr_omega [hdm, hle])
    (by
      rw [e12]; apply BitVec.eq_of_toNat_eq
      rw [show (7 : Word) = 7#64 from rfl, toNat_and7, h7, BitVec.toNat_ofNat]; omega)
    (by rw [e14, hd.x14, hd.x16, add_zero_sub]; addr_omega [hsm, hle])
    ((k₁ .x2 (by decide)).trans hd.x2) (fun r hr ↦ (k₁ r (by simp [hr])).trans (hd.keep r hr))
    (hd.copied.same (sameOf h₁ rfl))).imp fun t ⟨hr, ht⟩ ↦ ⟨r₁.trans hr, ht⟩

/-- After the head: `hb` bytes copied down to the destination end's multiple of 8. -/
structure B4 (s u : MachineState) (hb : Nat) : Prop where
  x14 : u.getReg .x14 = s.getReg .x11 + BitVec.ofNat 64 ((s.getReg .x12).toNat - hb)
  x15 : (u.getReg .x15).toNat = (s.getReg .x12).toNat - hb
  x13 : u.getReg .x13 = s.getReg .x10 + BitVec.ofNat 64 ((s.getReg .x12).toNat - hb)
  x16 : u.getReg .x16 = 0 - BitVec.ofNat 64 (8 * (((s.getReg .x12).toNat - hb) / 8))
  x7 : u.getReg .x7 = s.getReg .x10 + BitVec.ofNat 64 (((s.getReg .x12).toNat - hb) % 8)
  x6 : (u.getReg .x6).toNat = ((s.getReg .x11).toNat + ((s.getReg .x12).toNat - hb)) % 8
  x5 : u.getReg .x5 = 0 - BitVec.ofNat 64 hb
  x17 : u.getReg .x17 = s.getReg .x10 + s.getReg .x12
  x12 : u.getReg .x12 = s.getReg .x12
  x11 : u.getReg .x11 = s.getReg .x11
  x2 : u.getReg .x2 = s.getReg .x2 - 16
  keep : ∀ r ∈ keepC, u.getReg r = s.getReg r
  copied : BCopied s u hb
  n16 : 16 ≤ (s.getReg .x12).toNat
  hb8 : hb < 8
  hbdef : hb = ((s.getReg .x10).toNat + (s.getReg .x12).toNat) % 8

/-- The shifting path, from `0x800122f8`, reaches the tail. -/
def BShiftOk : Prop :=
  ∀ s u hb, BwdPre s → B4 s u hb → u.pc = 0x800122f8 → (u.getReg .x6).toNat ≠ 0 →
    ∃ v, Reaches Image.code u v ∧ BDone s v hb

theorem neg8 (x : Word) : x + 0xfffffffffffffff8 = x - 8 := by
  rw [add_neg_lit, show (0 : Word) - 0xfffffffffffffff8 = 8 by decide]

def coR : List Reg := [.x2, .x7, .x13, .x14, .x15, .x16] ++ keepC

/-- In the aligned loop at `0x800124d8`, from the state `w` after the head, `j` doublewords below
the head copied. -/
structure BCo (s w u : MachineState) (hb j : Nat) : Prop where
  pc : u.pc = 0x800124d8
  x12 : u.getReg .x12 = s.getReg .x10 + BitVec.ofNat 64 ((s.getReg .x12).toNat - hb - 8 * j)
  x11 : u.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 ((s.getReg .x12).toNat - hb - 8 * j - 8)
  lt : hb + 8 * j + 8 ≤ (s.getReg .x12).toNat
  keep : ∀ x ∈ coR, u.getReg x = w.getReg x
  copied : BCopied s u (hb + 8 * j)

theorem bco_body (hp : BwdPre s) {w : MachineState} {hb : Nat} (hw : B4 s w hb)
    (hc0 : ((s.getReg .x11).toNat + ((s.getReg .x12).toNat - hb)) % 8 = 0) (u : MachineState)
    (hu : ∃ j, BCo s w u hb j) :
    (∃ v, Reaches Image.code u v ∧ BDone s v hb) ∨
      (∃ v, Reaches Image.code u v ∧ (∃ j, BCo s w v hb j) ∧
        (v.getReg .x12).toNat < (u.getReg .x12).toNat) := by
  obtain ⟨j, hj⟩ := hu
  have hdm := hp.dst
  have hsm := hp.src
  simp only [Mapped] at hdm hsm
  have hlt := hj.lt
  have hbd := hw.hbdef
  have h8 := hw.hb8
  have hx12 := hj.x12
  have hx11 := hj.x11
  have hD : u.getReg .x12 + 0xfffffffffffffff8 =
      s.getReg .x10 + BitVec.ofNat 64 ((s.getReg .x12).toNat - hb - 8 * j - 8) := by
    rw [neg8, hx12]; addr_omega [hdm, hlt]
  have hD8 : (s.getReg .x10 + BitVec.ofNat 64 ((s.getReg .x12).toNat - hb - 8 * j - 8)).toNat % 8
      = 0 := by addr_omega [hdm, hlt, hbd, h8]
  have hS8 : (s.getReg .x11 + BitVec.ofNat 64 ((s.getReg .x12).toNat - hb - 8 * j - 8)).toNat % 8
      = 0 := by addr_omega [hsm, hlt, hc0]
  obtain ⟨v, hr, hv⟩ := mm_bcoloop.reaches hj.pc (by
    simp only [bcoloopE, Oblig.all, Oblig.holds, Addr.eval, E.eval, add_zero_lit, hD, hx11]
    exact ⟨valid_of (by decide) (by addr_omega [hdm, hlt]) hD8,
      valid_of (by decide) (by addr_omega [hsm, hlt]) hS8⟩)
  have k := keepOf hv rfl coR
  have hm := memOf hv rfl
  have e11 := hv.reg .x11 rfl
  have e12 := hv.reg .x12 rfl
  blk at hm e11 e12
  rw [hD, hx11] at hm
  have hcp : BCopied s v (hb + 8 * j + 8) := by
    refine hj.copied.extend hp (by omega) ?_ fun i hi ↦ ?_
    · rw [show (s.getReg .x12).toNat - (hb + 8 * j + 8) = (s.getReg .x12).toNat - hb - 8 * j - 8
        by omega]
      exact ByteFrame.of_single hD8 fun x hx ↦ frameOf hv rfl x (by
        simp only [Addr.eval, E.eval]; rw [hD]; exact hx)
    · have e (x : Word) : x + BitVec.ofNat 64 ((s.getReg .x12).toNat - (hb + 8 * j + 8) + i) =
          x + BitVec.ofNat 64 ((s.getReg .x12).toNat - hb - 8 * j - 8) + BitVec.ofNat 64 i := by
        rw [show (s.getReg .x12).toNat - (hb + 8 * j + 8) = (s.getReg .x12).toNat - hb - 8 * j - 8
          by omega, BitVec.ofNat_add, BitVec.add_assoc]
      rw [e, e, byteAt_add hD8 hi, hm, ← byteAt_add hS8 hi, BitVec.add_assoc, ← BitVec.ofNat_add,
        hj.copied.src hp (by omega) (by omega)]
  have hx7 : u.getReg .x7 = s.getReg .x10 + BitVec.ofNat 64 (((s.getReg .x12).toNat - hb) % 8) :=
    (hj.keep .x7 (by decide)).trans hw.x7
  by_cases hlast : hb + 8 * j + 16 ≤ (s.getReg .x12).toNat
  · have hcp' : BCopied s v (hb + 8 * (j + 1)) := by
      rw [show hb + 8 * (j + 1) = hb + 8 * j + 8 by omega]; exact hcp
    refine Or.inr ⟨v, hr, ⟨j + 1, pcT hv rfl ?_, ?_, ?_, by omega,
      fun x hx ↦ (k x hx).trans (hj.keep x hx), hcp'⟩, ?_⟩
    · cond; rw [hx7, hD]; addr_omega [hdm, hlast]
    · rw [e12, neg8, hx12]; addr_omega [hdm, hlast]
    · rw [e11, neg8, hx11]; addr_omega [hsm, hlast]
    · rw [e12, neg8, hx12]; addr_omega [hdm, hlast]
  · obtain ⟨t, hrt, ht⟩ := mm_coj.reaches (pcF hv rfl (by
      cond; rw [hx7, hD]; addr_omega [hdm, hlast, hlt])) trivial
    have kt := keepOf ht rfl coR
    have kk (x : Reg) (hx : x ∈ coR) : t.getReg x = w.getReg x :=
      (kt x hx).trans ((k x hx).trans (hj.keep x hx))
    refine Or.inl ⟨t, hr.trans hrt, pcC ht rfl, by rw [kk .x13 (by decide), hw.x13],
      by rw [kk .x16 (by decide), hw.x16], by rw [kk .x14 (by decide), hw.x14],
      by rw [kk .x15 (by decide), hw.x15], by rw [kk .x2 (by decide), hw.x2],
      fun x hx ↦ (kk x (by simp [coR, hx])).trans (hw.keep x hx), ?_, by omega⟩
    rw [show hb + 8 * (((s.getReg .x12).toNat - hb) / 8) = hb + 8 * j + 8 by omega]
    exact hcp.same (sameOf ht rfl)

/-- From `0x800122dc`, after the head: the doublewords, then the rest. -/
theorem b4_ok (hsh : BShiftOk) (hp : BwdPre s) {u : MachineState} {hb : Nat}
    (hpc : u.pc = 0x800122dc) (hn : 16 ≤ (s.getReg .x12).toNat)
    (hbd : hb = ((s.getReg .x10).toNat + (s.getReg .x12).toNat) % 8)
    (hx14 : u.getReg .x14 = s.getReg .x11 + s.getReg .x12)
    (hx5 : u.getReg .x5 = 0 - BitVec.ofNat 64 hb) (hx15 : (u.getReg .x15).toNat = hb)
    (hx13 : u.getReg .x13 = s.getReg .x10 + BitVec.ofNat 64 ((s.getReg .x12).toNat - hb))
    (hx17 : u.getReg .x17 = s.getReg .x10 + s.getReg .x12)
    (hx12 : u.getReg .x12 = s.getReg .x12) (hx11 : u.getReg .x11 = s.getReg .x11)
    (hx2 : u.getReg .x2 = s.getReg .x2 - 16) (hk : ∀ r ∈ keepC, u.getReg r = s.getReg r)
    (hc : BCopied s u hb) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧ MemcpyPost s t := by
  have hdm := hp.dst
  have hsm := hp.src
  simp only [Mapped] at hdm hsm
  have hb8 : hb < 8 := by omega
  obtain ⟨w, rw', hw⟩ := mm_b4.reaches hpc trivial
  have k := keepOf hw rfl (.x2 :: .x5 :: .x11 :: .x12 :: .x13 :: .x17 :: keepC)
  have e6 := hw.reg .x6 rfl
  have e7 := hw.reg .x7 rfl
  have e14 := hw.reg .x14 rfl
  have e15 := hw.reg .x15 rfl
  have e16 := hw.reg .x16 rfl
  blk at e6 e7 e14 e15 e16
  have hsub : (u.getReg .x12 - u.getReg .x15).toNat = (s.getReg .x12).toNat - hb := by
    rw [BitVec.toNat_sub, hx12, hx15]; omega
  have hW := and_not7 (u.getReg .x12 - u.getReg .x15)
  rw [hsub] at hW
  have hW' : u.getReg .x12 - u.getReg .x15 &&& 0xfffffffffffffff8 =
      BitVec.ofNat 64 (8 * (((s.getReg .x12).toNat - hb) / 8)) :=
    BitVec.eq_of_toNat_eq (by rw [hW, BitVec.toNat_ofNat]; omega)
  have h14 : u.getReg .x14 + u.getReg .x5 =
      s.getReg .x11 + BitVec.ofNat 64 ((s.getReg .x12).toNat - hb) := by
    rw [hx14, hx5, add_zero_sub]; addr_omega [hsm, hb8, hn]
  have hB4 : B4 s w hb := {
    x14 := by rw [e14, h14]
    x15 := by rw [e15, hsub]
    x13 := by rw [k .x13 (by decide), hx13]
    x16 := by rw [e16, hW']
    x7 := by rw [e7, hx13, hW']; addr_omega [hdm, hn]
    x6 := by
      rw [e6, h14, show (7 : Word) = 7#64 from rfl, toNat_and7]
      addr_omega [hsm, hn]
    x5 := by rw [k .x5 (by decide), hx5]
    x17 := by rw [k .x17 (by decide), hx17]
    x12 := by rw [k .x12 (by decide), hx12]
    x11 := by rw [k .x11 (by decide), hx11]
    x2 := by rw [k .x2 (by decide), hx2]
    keep := fun r hr ↦ (k r (by simp [hr])).trans (hk r hr)
    copied := hc.same (sameOf hw rfl)
    n16 := hn
    hb8 := hb8
    hbdef := hbd }
  by_cases hc0 : ((s.getReg .x11).toNat + ((s.getReg .x12).toNat - hb)) % 8 = 0
  · have he6 : w.getReg .x6 = 0 := BitVec.eq_of_toNat_eq (by rw [hB4.x6, hc0]; rfl)
    obtain ⟨u₁, r₁, h₁⟩ := mm_bco.reaches (pcT hw rfl (by cond; rw [← e6, he6])) trivial
    have k₁ := keepOf h₁ rfl coR
    obtain ⟨u₂, r₂, h₂⟩ := mm_bcopre.reaches (pcF h₁ rfl (by
      cond; rw [hB4.x7, hB4.x13]; addr_omega [hdm, hn, hb8, (s.getReg .x12).isLt])) trivial
    have k₂ := keepOf h₂ rfl coR
    have e11 := h₂.reg .x11 rfl
    have e12 := h₂.reg .x12 rfl
    blk at e11 e12
    have hco : BCo s w u₂ hb 0 := {
      pc := pcC h₂ rfl
      x12 := by rw [e12, k₁ .x13 (by decide), hB4.x13]; simp
      x11 := by
        have h15 : w.getReg .x15 = BitVec.ofNat 64 ((s.getReg .x12).toNat - hb) :=
          BitVec.eq_of_toNat_eq (by rw [hB4.x15, BitVec.toNat_ofNat]; omega)
        have k11 := keepOf h₁ rfl [.x11]
        rw [e11, neg8, k₁ .x15 (by decide), k11 .x11 (by decide), hB4.x11, h15]
        addr_omega [hsm, hn, hb8, (s.getReg .x12).isLt]
      lt := by omega
      keep := fun x hx ↦ (k₂ x hx).trans (k₁ x hx)
      copied := (hB4.copied.same (sameOf h₁ rfl)).same (sameOf h₂ rfl) }
    obtain ⟨v, rv, hv⟩ := Reaches.loop (code := Image.code) (fun u ↦ ∃ j, BCo s w u hb j)
      (fun u ↦ (u.getReg .x12).toNat) (BDone s · hb) (bco_body hp hB4 hc0) u₂ ⟨0, hco⟩
    obtain ⟨t, rt, ht⟩ := tailb_ok hp hv
    exact ⟨t, rw'.trans (r₁.trans (r₂.trans (rv.trans rt))), ht⟩
  · obtain ⟨v, rv, hv⟩ := hsh s w hb hp hB4 (pcF hw rfl (by
      cond; intro h0; apply hc0; rw [← hB4.x6, e6, h0]; rfl)) (by rw [hB4.x6]; exact hc0)
    obtain ⟨t, rt, ht⟩ := tailb_ok hp hv
    exact ⟨t, rw'.trans (rv.trans rt), ht⟩

/-- **The backward copy**, from `0x80012298`, given its shifting path. -/
theorem bwd_of (hsh : BShiftOk) (hp : BwdPre s) {u : MachineState} (hpc : u.pc = 0x80012298)
    (hx2 : u.getReg .x2 = s.getReg .x2 - 16)
    (hk : ∀ r ∈ Reg.x11 :: Reg.x12 :: keepC, u.getReg r = s.getReg r)
    (hm : ∀ a, u.getMem a = s.getMem a) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧ MemcpyPost s t := by
  have hdm := hp.dst
  have hsm := hp.src
  simp only [Mapped] at hdm hsm
  have hc0 : BCopied s u 0 := BCopied.zero hm
  have hx11 := hk .x11 (by decide)
  have hx12 := hk .x12 (by decide)
  have hx10 := hk .x10 (by decide)
  have hkC : ∀ r ∈ keepC, u.getReg r = s.getReg r := fun r hr ↦ hk r (by simp [hr])
  obtain ⟨u₁, r₁, h₁⟩ := mm_b1.reaches hpc trivial
  have k₁ := keepOf h₁ rfl (.x2 :: .x11 :: .x12 :: keepC)
  have e14 := h₁.reg .x14 rfl
  have e17 := h₁.reg .x17 rfl
  blk at e14 e17
  rw [hx11, hx12] at e14
  rw [hx10, hx12] at e17
  have kk₁ (r : Reg) (hr : r ∈ Reg.x11 :: Reg.x12 :: keepC) : u₁.getReg r = s.getReg r :=
    (k₁ r (List.mem_cons_of_mem _ hr)).trans (hk r hr)
  have hx2₁ := (k₁ .x2 (by decide)).trans hx2
  have hc₁ := hc0.same (sameOf h₁ rfl)
  have hkC₁ : ∀ r ∈ keepC, u₁.getReg r = s.getReg r := fun r hr ↦ kk₁ r (by simp [hr])
  have hN : s.getReg .x12 = BitVec.ofNat 64 (s.getReg .x12).toNat := by simp
  by_cases hsmall : (s.getReg .x12).toNat < 16
  · exact (btail_ok hp (k := 0) (pcT h₁ rfl (by cond; rw [hx12]; exact hsmall))
      (by omega) (by rw [e17, Nat.sub_zero, ← hN]) (by rw [kk₁ .x12 (by decide), Nat.sub_zero, ← hN])
      (by rw [e14, Nat.sub_zero, ← hN]) hx2₁ hkC₁ hc₁).imp
      fun t ⟨hr, ht⟩ ↦ ⟨r₁.trans hr, ht⟩
  · obtain ⟨u₂, r₂, h₂⟩ := mm_b2.reaches (pcF h₁ rfl (by
      cond; rw [hx12]; omega)) trivial
    have k₂ := keepOf h₂ rfl (.x2 :: .x11 :: .x12 :: .x14 :: .x17 :: keepC)
    have e5 := h₂.reg .x5 rfl
    have e13 := h₂.reg .x13 rfl
    have e15 := h₂.reg .x15 rfl
    blk at e5 e13 e15
    have k17 := k₂ .x17 (by decide)
    have h7 : u₁.getReg .x17 &&& 7 =
        BitVec.ofNat 64 (((s.getReg .x10).toNat + (s.getReg .x12).toNat) % 8) := by
      apply BitVec.eq_of_toNat_eq
      rw [show (7 : Word) = 7#64 from rfl, toNat_and7, e17, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have hm8 : u₁.getReg .x17 &&& 0xfffffffffffffff8 = s.getReg .x10 + BitVec.ofNat 64
        ((s.getReg .x12).toNat - ((s.getReg .x10).toNat + (s.getReg .x12).toNat) % 8) := by
      apply BitVec.eq_of_toNat_eq
      rw [and_not7, e17, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have hx2₂ := (k₂ .x2 (by decide)).trans hx2₁
    have kk₂ (r : Reg) (hr : r ∈ Reg.x11 :: Reg.x12 :: keepC) : u₂.getReg r = s.getReg r :=
      (k₂ r (by simp at hr ⊢; tauto)).trans (kk₁ r hr)
    have hc₂ := hc₁.same (sameOf h₂ rfl)
    have hb4 := fun {u : MachineState} (hpc : u.pc = 0x800122dc) ↦ b4_ok hsh hp
      (hb := ((s.getReg .x10).toNat + (s.getReg .x12).toNat) % 8) hpc (Nat.le_of_not_lt hsmall) rfl
    by_cases h0 : ((s.getReg .x10).toNat + (s.getReg .x12).toNat) % 8 = 0
    · obtain ⟨t, hr, ht⟩ := hb4 (u := u₂) (pcT h₂ rfl (by
          cond; rw [hm8, e17, h0]; simp)) (by rw [k₂ .x14 (by decide), e14, hN])
        (by rw [e5, h7, h0]) (by rw [e15, h7, BitVec.toNat_ofNat]; omega) (by rw [e13, hm8])
        (by rw [k17, e17, hN]) (kk₂ .x12 (by decide)) (kk₂ .x11 (by decide)) hx2₂
        (fun r hr ↦ kk₂ r (by simp [hr])) (by rw [h0]; exact hc₂)
      exact ⟨t, r₁.trans (r₂.trans hr), ht⟩
    · obtain ⟨u₃, r₃, h₃⟩ := mm_b3.reaches (pcF h₂ rfl (by
        cond; rw [hm8, e17]; addr_omega [hdm, h0, hsmall])) trivial
      have k₃ := keepOf h₃ rfl (.x2 :: .x5 :: .x11 :: .x12 :: .x13 :: .x14 :: .x15 :: .x17 :: keepC)
      have e6 := h₃.reg .x6 rfl
      have e16 := h₃.reg .x16 rfl
      blk at e6 e16
      obtain ⟨v, rv, pcv, hcv, hkv⟩ := bloop mm_hloop (by decide) hp
        (((s.getReg .x10).toNat + (s.getReg .x12).toNat) % 8) u₃ 0 (pcC h₃ rfl)
        (by rw [e6, k17, e17]; simp)
        (by rw [e16, kk₂ .x11 (by decide), kk₂ .x12 (by decide), neg1]; simp)
        (by rw [k₃ .x13 (by decide), e13, hm8]; simp) (by omega) (by omega) (hc₂.same (sameOf h₃ rfl))
      rw [Nat.zero_add] at hcv
      have kv (r : Reg) (hr : r ∈ Reg.x2 :: Reg.x5 :: Reg.x11 :: Reg.x12 :: Reg.x13 :: Reg.x14 ::
          Reg.x15 :: Reg.x17 :: keepC) : v.getReg r = u₂.getReg r :=
        (hkv r (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide))
          (ne_of_mem_of_not_mem hr (by decide)) (ne_of_mem_of_not_mem hr (by decide))).trans
          (k₃ r hr)
      obtain ⟨t, hr, ht⟩ := hb4 (u := v) pcv (by rw [kv .x14 (by decide), k₂ .x14 (by decide), e14, hN])
        (by rw [kv .x5 (by decide), e5, h7])
        (by rw [kv .x15 (by decide), e15, h7, BitVec.toNat_ofNat]; omega)
        (by rw [kv .x13 (by decide), e13, hm8])
        (by rw [kv .x17 (by decide), k17, e17, hN]) (by rw [kv .x12 (by decide), kk₂ .x12 (by decide)])
        (by rw [kv .x11 (by decide), kk₂ .x11 (by decide)]) (by rw [kv .x2 (by decide), hx2₂])
        (fun r hr ↦ (kv r (by simp [hr])).trans (kk₂ r (by simp [hr]))) hcv
      exact ⟨t, r₁.trans (r₂.trans (r₃.trans (rv.trans hr))), ht⟩

end Rv64Verifier.Runtime.Backward
