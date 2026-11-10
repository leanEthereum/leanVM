import Rv64Verifier.Proofs.Runtime.Backward

/-!
# `memmove`'s backward shifting path

When the source is not aligned once the destination end is (its byte position `c`, `0 < c < 8`):
the buffer gets the low `c` bytes of the source's aligned doubleword at the top (`chainA`), each
destination doubleword down is two aligned source doublewords shifted together (`sloop_body`),
and the lowest gets the buffer refilled with the source's bytes from its start up to the next
multiple of 8 (`chainB`, `sfin_ok`). The mirror of `ForwardShift.lean`.
-/

namespace Rv64Verifier.Runtime.Backward
open RiscvZkvm.Rv64 Rv64Verifier.Sym Rv64Verifier.Runtime.Forward
open Rv64Verifier.Runtime.Memcpy (keepE keepE_reg keepC)

variable {s : MachineState}

/-- The common facts of the backward shifting path, from `w` at `0x800122f8`; `K` bytes below
the head, `c` the source's byte position at their end. -/
structure BCtx (s w : MachineState) (hb K c : Nat) : Prop where
  pre : BwdPre s
  b4 : B4 s w hb
  hK : K = (s.getReg .x12).toNat - hb
  hc : c = ((s.getReg .x11).toNat + K) % 8
  hc0 : c ≠ 0

theorem BCtx.bounds {w : MachineState} {hb K c : Nat} (hx : BCtx s w hb K c) :
    0 < c ∧ c < 8 ∧ hb < 8 ∧ 9 ≤ K ∧ K + hb = (s.getReg .x12).toNat ∧
      ((s.getReg .x10).toNat + K) % 8 = 0 ∧ (s.getReg .x2 - 8).toNat % 8 = 0 := by
  have := hx.b4.hb8
  have := hx.b4.n16
  have := hx.b4.hbdef
  have := hx.hK
  have := hx.hc
  have := hx.hc0
  have hb := hx.pre.buf
  omega

theorem BCtx.x6 {w : MachineState} {hb K c : Nat} (hx : BCtx s w hb K c) :
    w.getReg .x6 = BitVec.ofNat 64 c :=
  BitVec.eq_of_toNat_eq (by
    rw [hx.b4.x6, BitVec.toNat_ofNat, hx.hc, hx.hK]; have := hx.bounds; omega)

theorem BCtx.x14 {w : MachineState} {hb K c : Nat} (hx : BCtx s w hb K c) :
    (w.getReg .x14).toNat % 8 = c := by
  have hsm := hx.pre.src
  simp only [Mapped] at hsm
  have := hx.bounds
  rw [hx.b4.x14, BitVec.toNat_add, BitVec.toNat_ofNat, hx.hc, hx.hK]
  omega

/-! ## The first buffer fill -/

def qbR : List Reg := [.x2, .x5, .x6, .x7, .x11, .x12, .x13, .x14, .x15, .x16, .x17] ++ keepC

/-- In the first fill: `q` bytes of the source's aligned doubleword at `r + K - c` in the
buffer. -/
structure QB (s w u : MachineState) (hb K c q : Nat) : Prop where
  x29 : u.getReg .x29 = s.getReg .x11 + BitVec.ofNat 64 (K - c)
  keep : ∀ x ∈ qbR, u.getReg x = w.getReg x
  copied : BCopied s u hb
  buf : ∀ i < q, extractByte (u.getMem (s.getReg .x2 - 8)) i =
    byteAt s (s.getReg .x11 + BitVec.ofNat 64 (K - c) + BitVec.ofNat 64 i)

theorem QB.src {w u : MachineState} {hb K c q : Nat} (hx : BCtx s w hb K c)
    (hu : QB s w u hb K c q) {i : Nat} (hi : i < c) :
    byteAt u (s.getReg .x11 + BitVec.ofNat 64 (K - c) + BitVec.ofNat 64 i) =
      byteAt s (s.getReg .x11 + BitVec.ofNat 64 (K - c) + BitVec.ofNat 64 i) := by
  have hb := hx.bounds
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hu.copied.src hx.pre (by omega) (by omega)

theorem QB.of_same {w u v : MachineState} {hb K c q : Nat} (hu : QB s w u hb K c q)
    (hk : ∀ x ∈ Reg.x29 :: qbR, v.getReg x = u.getReg x) (hm : ∀ x, v.getMem x = u.getMem x) :
    QB s w v hb K c q :=
  ⟨(hk .x29 (by decide)).trans hu.x29, fun x hx ↦ (hk x (by simp [hx])).trans (hu.keep x hx),
    hu.copied.same hm,
    fun i hi ↦ by rw [hm]; exact hu.buf i hi⟩

theorem QB.step {w u v : MachineState} {hb K c q wd : Nat} (hx : BCtx s w hb K c)
    (hu : QB s w u hb K c q) (hq : q + wd ≤ c)
    (hk : ∀ x ∈ Reg.x29 :: qbR, v.getReg x = u.getReg x)
    (hf : ∀ x, x ≠ s.getReg .x2 - 8 → v.getMem x = u.getMem x)
    (hbuf : ∀ i < 8, extractByte (v.getMem (s.getReg .x2 - 8)) i = if q ≤ i ∧ i < q + wd then
      byteAt u (s.getReg .x11 + BitVec.ofNat 64 (K - c) + BitVec.ofNat 64 q +
        BitVec.ofNat 64 (i - q)) else extractByte (u.getMem (s.getReg .x2 - 8)) i) :
    QB s w v hb K c (q + wd) := by
  have hb' := hx.bounds
  refine ⟨(hk .x29 (by decide)).trans hu.x29, fun x hx' ↦ (hk x (by simp [hx'])).trans (hu.keep x hx'),
    hu.copied.stack hx.pre hb'.2.2.2.2.2.2 (by have := hx.pre.buf; omega)
      (by have := hx.pre.buf; omega) hf, fun i hi ↦ ?_⟩
  have := buf_step (s := s) (a := 0) (p := q) (q := q) (wd := wd) (by omega)
    (S := s.getReg .x11 + BitVec.ofNat 64 (K - c)) (fun j hj ↦ by
      rw [BitVec.add_assoc (s.getReg .x11 + _), ← BitVec.ofNat_add]
      exact hu.src hx (by omega))
    (fun i _ h2 ↦ by rw [Nat.sub_zero]; exact hu.buf i (by omega)) hbuf (by omega) i
    (Nat.zero_le _)
    (by omega)
  rwa [Nat.sub_zero] at this

theorem sb0_step {w : MachineState} {hb K c : Nat} (hx : BCtx s w hb K c) (hpc : w.pc = 0x800122f8) :
    ∃ v, Reaches Image.code w v ∧ QB s w v hb K c 0 ∧
      v.getReg .x29 = s.getReg .x11 + BitVec.ofNat 64 (K - c) ∧ v.getReg .x28 = 0 ∧
      (4 ≤ c → v.pc = 0x8001253c) ∧ (c < 4 → v.pc = 0x8001230c) := by
  have hb := hx.bounds
  have hB := hx.pre.buf
  have hsm := hx.pre.src
  simp only [Mapped] at hsm
  have hw := hx.b4
  have hx2 : w.getReg .x2 + 8 = s.getReg .x2 - 8 := by rw [hw.x2]; addr_omega [hB]
  obtain ⟨v, hr, hv⟩ := mm_sb0.reaches hpc (by
    simp only [sb0E, Oblig.all, Oblig.holds, Addr.eval, E.eval, hx2]
    exact valid_of (by decide) (by addr_omega [hB]) (by omega))
  have k := keepOf hv rfl qbR
  have e28 := hv.reg .x28 rfl
  have e29 := hv.reg .x29 rfl
  blk at e28 e29
  have hf (x : Word) (hx' : x ≠ s.getReg .x2 - 8) : v.getMem x = w.getMem x :=
    frameOf hv rfl x (by simp only [Addr.eval, E.eval, hx2]; exact hx')
  have hK := hx.hK
  have h29 : v.getReg .x29 = s.getReg .x11 + BitVec.ofNat 64 (K - c) := by
    rw [e29, hw.x14, hx.x6, ← hK]; addr_omega [hsm, hb]
  refine ⟨v, hr, ⟨h29, k, hw.copied.stack hx.pre hb.2.2.2.2.2.2 (by omega) (by omega) hf,
    fun i hi ↦ absurd hi (Nat.not_lt_zero _)⟩, h29, e28, fun hc ↦ pcT hv rfl ?_,
    fun hc ↦ pcF hv rfl ?_⟩
  · cond; rw [hx.x6]; simp only [BitVec.toNat_ofNat]; omega
  · cond; rw [hx.x6]; simp only [BitVec.toNat_ofNat]; omega

theorem sbw_step {w : MachineState} {hb K c : Nat} (hx : BCtx s w hb K c) {u : MachineState}
    (hpc : u.pc = 0x8001253c) (hu : QB s w u hb K c 0)
    (h29 : u.getReg .x29 = s.getReg .x11 + BitVec.ofNat 64 (K - c)) (h4 : 4 ≤ c) :
    ∃ v, Reaches Image.code u v ∧ QB s w v hb K c 4 ∧ v.getReg .x29 = u.getReg .x29 ∧
      v.getReg .x28 = 4 ∧ ((w.getReg .x14 &&& 2) = 0 → v.pc = 0x80012314) ∧
      ((w.getReg .x14 &&& 2) ≠ 0 → v.pc = 0x80012550) := by
  have hb := hx.bounds
  have hB := hx.pre.buf
  have hsm := hx.pre.src
  simp only [Mapped] at hsm
  have hc := hx.hc
  have hx2 : u.getReg .x2 + 8 = s.getReg .x2 - 8 + BitVec.ofNat 64 0 := by
    rw [hu.keep .x2 (by decide), hx.b4.x2]; addr_omega [hB]
  obtain ⟨v, hr, hv⟩ := mm_sbw.reaches hpc (by
    simp only [sbwE, Oblig.all, Oblig.holds, Addr.eval, E.eval, add_zero_lit, hx2, h29]
    exact ⟨valid_of (by decide) (by addr_omega [hB]) (by addr_omega [hB]),
      valid_of (by decide) (by addr_omega [hsm, hb, h4]) (by addr_omega [hsm, hb, hc])⟩)
  have k := keepOf hv rfl (.x29 :: qbR)
  have hm := memOf hv rfl
  have e28 := hv.reg .x28 rfl
  blk at hm e28
  rw [hx2] at hm
  have hbuf := fun i (hi : i < 8) ↦ buf_update (lk := .w) (sk := .w) rfl hb.2.2.2.2.2.2
    (q := 0) (by omega) (by simp only [StoreKind.width]; addr_omega [hB])
    (by simp only [StoreKind.width]; rw [h29]; addr_omega [hsm, hb, hc]) hm hi
  have hf (x : Word) (hx' : x ≠ s.getReg .x2 - 8) : v.getMem x = u.getMem x :=
    frameOf hv rfl x (by
      simp only [Addr.eval, E.eval, BinOp.eval, add_zero_lit, hx2,
        (key_eq (q := 0) hb.2.2.2.2.2.2 (by omega)).1]
      exact hx')
  have hx14 : u.getReg .x14 = w.getReg .x14 := hu.keep .x14 (by decide)
  refine ⟨v, hr, hu.step (q := 0) (wd := 4) hx (by omega) k hf
    (fun i hi ↦ ?_), k .x29 (by decide), e28, fun hc ↦ pcT hv rfl (by cond; rw [hx14]; exact hc),
    fun hc ↦ pcF hv rfl (by cond; rw [hx14]; exact hc)⟩
  rw [hbuf i hi, h29, BitVec.add_zero]
  rfl

theorem sbh_step {w : MachineState} {hb K c q : Nat} (hx : BCtx s w hb K c) {u : MachineState}
    (hpc : u.pc = 0x80012550) (hu : QB s w u hb K c q)
    (h29 : u.getReg .x29 = s.getReg .x11 + BitVec.ofNat 64 (K - c))
    (h28 : u.getReg .x28 = BitVec.ofNat 64 q) (hal : q % 2 = 0) (h8 : q + 2 ≤ c) :
    ∃ v, Reaches Image.code u v ∧ QB s w v hb K c (q + 2) ∧ v.getReg .x29 = u.getReg .x29 ∧
      v.getReg .x28 = BitVec.ofNat 64 (q + 2) ∧ ((w.getReg .x14 &&& 1) ≠ 0 → v.pc = 0x8001231c) ∧
      ((w.getReg .x14 &&& 1) = 0 → v.pc = 0x80012570) := by
  have hb := hx.bounds
  have hB := hx.pre.buf
  have hsm := hx.pre.src
  simp only [Mapped] at hsm
  have hc := hx.hc
  have hQ : (u.getReg .x2 + 8 ||| u.getReg .x28) = s.getReg .x2 - 8 + BitVec.ofNat 64 q := by
    rw [hu.keep .x2 (by decide), hx.b4.x2, h28, show s.getReg .x2 - 16 + 8 = s.getReg .x2 - 8 by
      addr_omega [hB], or_eq_add hb.2.2.2.2.2.2 (by rw [BitVec.toNat_ofNat]; omega)]
  have hP : u.getReg .x29 + u.getReg .x28 = s.getReg .x11 + BitVec.ofNat 64 (K - c) +
      BitVec.ofNat 64 q := by rw [h29, h28]
  obtain ⟨v, hr, hv⟩ := mm_sbh.reaches hpc (by
    simp only [sbhE, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, add_zero_lit, hQ, hP]
    exact ⟨valid_of (by decide) (by addr_omega [hB, h8, hb]) (by addr_omega [hB, hal, h8, hb]),
      valid_of (by decide) (by addr_omega [hsm, hb, h8])
        (by addr_omega [hsm, hb, hc, hal, h8])⟩)
  have k := keepOf hv rfl (.x29 :: qbR)
  have hm := memOf hv rfl
  have e28 := hv.reg .x28 rfl
  blk at hm e28
  rw [hQ, hP] at hm
  have hbuf := fun i (hi : i < 8) ↦ buf_update (lk := .h) (sk := .h) rfl hb.2.2.2.2.2.2
    (q := q) (by omega) (by simp only [StoreKind.width]; addr_omega [hB, hal, h8, hb])
    (by simp only [StoreKind.width]; addr_omega [hsm, hb, hc, hal, h8]) hm hi
  have hf (x : Word) (hx' : x ≠ s.getReg .x2 - 8) : v.getMem x = u.getMem x :=
    frameOf hv rfl x (by
      simp only [Addr.eval, E.eval, BinOp.eval, add_zero_lit, hQ,
        (key_eq (q := q) hb.2.2.2.2.2.2 (by omega)).1]
      exact hx')
  have hx14 : u.getReg .x14 = w.getReg .x14 := hu.keep .x14 (by decide)
  refine ⟨v, hr, hu.step (wd := 2) hx h8 k hf hbuf,
    k .x29 (by decide), by rw [e28, h28, addw2 (by omega)],
    fun hc ↦ pcT hv rfl (by cond; rw [hx14]; exact hc),
    fun hc ↦ pcF hv rfl (by cond; rw [hx14]; exact hc)⟩

theorem sbb_step {w : MachineState} {hb K c q : Nat} (hx : BCtx s w hb K c) {u : MachineState}
    (hpc : u.pc = 0x8001231c) (hu : QB s w u hb K c q)
    (h29 : u.getReg .x29 = s.getReg .x11 + BitVec.ofNat 64 (K - c))
    (h28 : u.getReg .x28 = BitVec.ofNat 64 q) (h8 : q + 1 ≤ c) :
    ∃ v, Reaches Image.code u v ∧ QB s w v hb K c (q + 1) ∧ v.pc = 0x80012330 := by
  have hb := hx.bounds
  have hB := hx.pre.buf
  have hsm := hx.pre.src
  simp only [Mapped] at hsm
  have hQ : (u.getReg .x2 + 8 ||| u.getReg .x28) = s.getReg .x2 - 8 + BitVec.ofNat 64 q := by
    rw [hu.keep .x2 (by decide), hx.b4.x2, h28, show s.getReg .x2 - 16 + 8 = s.getReg .x2 - 8 by
      addr_omega [hB], or_eq_add hb.2.2.2.2.2.2 (by rw [BitVec.toNat_ofNat]; omega)]
  have hP : u.getReg .x29 + u.getReg .x28 = s.getReg .x11 + BitVec.ofNat 64 (K - c) +
      BitVec.ofNat 64 q := by rw [h29, h28]
  obtain ⟨v, hr, hv⟩ := mm_sbb.reaches hpc (by
    simp only [sbbE, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, add_zero_lit, hQ, hP]
    exact ⟨valid_of (by decide) (by addr_omega [hB, h8, hb]) (Nat.mod_one _),
      valid_of (by decide) (by addr_omega [hsm, hb, h8]) (Nat.mod_one _)⟩)
  have k := keepOf hv rfl (.x29 :: qbR)
  have hm := memOf hv rfl
  blk at hm
  rw [hQ, hP] at hm
  have hbuf := fun i (hi : i < 8) ↦ buf_update (lk := .bu) (sk := .b) rfl hb.2.2.2.2.2.2
    (q := q) (by omega) (Nat.mod_one _) (Nat.mod_one _) hm hi
  have hf (x : Word) (hx' : x ≠ s.getReg .x2 - 8) : v.getMem x = u.getMem x :=
    frameOf hv rfl x (by
      simp only [Addr.eval, E.eval, BinOp.eval, add_zero_lit, hQ,
        (key_eq (q := q) hb.2.2.2.2.2.2 (by omega)).1]
      exact hx')
  exact ⟨v, hr, hu.step (wd := 1) hx h8 k hf hbuf, pcC hv rfl⟩

theorem st2_step {w : MachineState} {hb K c q : Nat} {u : MachineState}
    (hpc : u.pc = 0x8001230c) (hu : QB s w u hb K c q) :
    ∃ v, Reaches Image.code u v ∧ QB s w v hb K c q ∧ v.getReg .x29 = u.getReg .x29 ∧
      v.getReg .x28 = u.getReg .x28 ∧ ((w.getReg .x14 &&& 2) ≠ 0 → v.pc = 0x80012550) ∧
      ((w.getReg .x14 &&& 2) = 0 → v.pc = 0x80012314) := by
  obtain ⟨v, hr, hv⟩ := mm_st2.reaches hpc trivial
  have k := keepOf hv rfl (.x28 :: .x29 :: qbR)
  have hx14 : u.getReg .x14 = w.getReg .x14 := hu.keep .x14 (by decide)
  exact ⟨v, hr, hu.of_same (fun r hr ↦ k r (by simp at hr ⊢; tauto)) (sameOf hv rfl),
    k .x29 (by decide), k .x28 (by decide), fun hc ↦ pcT hv rfl (by cond; rw [hx14]; exact hc),
    fun hc ↦ pcF hv rfl (by cond; rw [hx14]; exact hc)⟩

theorem st1_step {w : MachineState} {hb K c q : Nat} {u : MachineState}
    (hpc : u.pc = 0x80012314) (hu : QB s w u hb K c q) :
    ∃ v, Reaches Image.code u v ∧ QB s w v hb K c q ∧ v.getReg .x29 = u.getReg .x29 ∧
      v.getReg .x28 = u.getReg .x28 ∧ ((w.getReg .x14 &&& 1) = 0 → v.pc = 0x80012330) ∧
      ((w.getReg .x14 &&& 1) ≠ 0 → v.pc = 0x8001231c) := by
  obtain ⟨v, hr, hv⟩ := mm_st1.reaches hpc trivial
  have k := keepOf hv rfl (.x28 :: .x29 :: qbR)
  have hx14 : u.getReg .x14 = w.getReg .x14 := hu.keep .x14 (by decide)
  exact ⟨v, hr, hu.of_same (fun r hr ↦ k r (by simp at hr ⊢; tauto)) (sameOf hv rfl),
    k .x29 (by decide), k .x28 (by decide), fun hc ↦ pcT hv rfl (by cond; rw [hx14]; exact hc),
    fun hc ↦ pcF hv rfl (by cond; rw [hx14]; exact hc)⟩

theorem sbj_step {w : MachineState} {hb K c q : Nat} {u : MachineState}
    (hpc : u.pc = 0x80012570) (hu : QB s w u hb K c q) :
    ∃ v, Reaches Image.code u v ∧ QB s w v hb K c q ∧ v.pc = 0x80012330 := by
  obtain ⟨v, hr, hv⟩ := mm_sbj.reaches hpc trivial
  exact ⟨v, hr, hu.of_same (keepOf hv rfl _) (sameOf hv rfl), pcC hv rfl⟩

/-- The first buffer fill: the low `c` bytes of the source's aligned doubleword at the top. -/
theorem chainA {w : MachineState} {hb K c : Nat} (hx : BCtx s w hb K c)
    (hpc : w.pc = 0x800122f8) :
    ∃ v, Reaches Image.code w v ∧ QB s w v hb K c c ∧ v.pc = 0x80012330 := by
  have hb := hx.bounds
  have b2 := and_low hx.x14 (c := 2) (by decide)
  have b1 := and_low hx.x14 (c := 1) (by decide)
  obtain ⟨u, r₀, hu, h29, h28, hqw, hqt2⟩ := sb0_step hx hpc
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨
    c = 6 ∨ c = 7 := by omega
  · obtain ⟨u₁, r₁, p₁, x29₁, x28₁, -, f₁⟩ := st2_step (hqt2 (by decide)) hu
    obtain ⟨u₂, r₂, p₂, x29₂, x28₂, -, f₂⟩ := st1_step (f₁ (by rw [b2]; decide)) p₁
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := sbb_step hx (f₂ (by rw [b1]; decide)) p₂
      (by rw [x29₂, x29₁, h29]) (by rw [x28₂, x28₁, h28]; rfl) (by decide)
    exact ⟨u₃, r₀.trans (r₁.trans (r₂.trans r₃)), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, x29₁, x28₁, t₁, -⟩ := st2_step (hqt2 (by decide)) hu
    obtain ⟨u₂, r₂, p₂, -, -, -, f₂⟩ := sbh_step hx (t₁ (by rw [b2]; decide)) p₁
      (by rw [x29₁, h29]) (by rw [x28₁, h28]; rfl) (by decide) (by decide)
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := sbj_step (f₂ (by rw [b1]; decide)) p₂
    exact ⟨u₃, r₀.trans (r₁.trans (r₂.trans r₃)), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, x29₁, x28₁, t₁, -⟩ := st2_step (hqt2 (by decide)) hu
    obtain ⟨u₂, r₂, p₂, x29₂, x28₂, t₂, -⟩ := sbh_step hx (t₁ (by rw [b2]; decide)) p₁
      (by rw [x29₁, h29]) (by rw [x28₁, h28]; rfl) (by decide) (by decide)
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := sbb_step hx (t₂ (by rw [b1]; decide)) p₂
      (by rw [x29₂, x29₁, h29]) x28₂ (by decide)
    exact ⟨u₃, r₀.trans (r₁.trans (r₂.trans r₃)), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, x29₁, x28₁, t₁, -⟩ := sbw_step hx (hqw (by decide)) hu h29 (by decide)
    obtain ⟨u₂, r₂, p₂, -, -, t₂, -⟩ := st1_step (t₁ (by rw [b2]; decide)) p₁
    exact ⟨u₂, r₀.trans (r₁.trans r₂), p₂, t₂ (by rw [b1]; decide)⟩
  · obtain ⟨u₁, r₁, p₁, x29₁, x28₁, t₁, -⟩ := sbw_step hx (hqw (by decide)) hu h29 (by decide)
    obtain ⟨u₂, r₂, p₂, x29₂, x28₂, -, f₂⟩ := st1_step (t₁ (by rw [b2]; decide)) p₁
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := sbb_step hx (f₂ (by rw [b1]; decide)) p₂
      (by rw [x29₂, x29₁, h29]) (by rw [x28₂, x28₁]; rfl) (by decide)
    exact ⟨u₃, r₀.trans (r₁.trans (r₂.trans r₃)), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, x29₁, x28₁, -, f₁⟩ := sbw_step hx (hqw (by decide)) hu h29 (by decide)
    obtain ⟨u₂, r₂, p₂, -, -, -, f₂⟩ := sbh_step hx (f₁ (by rw [b2]; decide)) p₁
      (by rw [x29₁, h29]) (by rw [x28₁]; rfl) (by decide) (by decide)
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := sbj_step (f₂ (by rw [b1]; decide)) p₂
    exact ⟨u₃, r₀.trans (r₁.trans (r₂.trans r₃)), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, x29₁, x28₁, -, f₁⟩ := sbw_step hx (hqw (by decide)) hu h29 (by decide)
    obtain ⟨u₂, r₂, p₂, x29₂, x28₂, t₂, -⟩ := sbh_step hx (f₁ (by rw [b2]; decide)) p₁
      (by rw [x29₁, h29]) (by rw [x28₁]; rfl) (by decide) (by decide)
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := sbb_step hx (t₂ (by rw [b1]; decide)) p₂
      (by rw [x29₂, x29₁, h29]) x28₂ (by decide)
    exact ⟨u₃, r₀.trans (r₁.trans (r₂.trans r₃)), p₃, pc₃⟩

/-! ## Doublewords shifted together, down -/

def lsR : List Reg := [.x2, .x5, .x6, .x13, .x14, .x15, .x16] ++ keepC

/-- The registers `0x80012330` keeps. -/
def seR : List Reg := [.x2, .x5, .x6, .x11, .x12, .x13, .x14, .x15, .x16, .x17] ++ keepC

theorem seR_sub : ∀ x ∈ seR, x ∈ qbR := by decide
theorem lsR_sub : ∀ x ∈ lsR, x ∈ seR := by decide

/-- In the loop at `0x80012350`, `j` doublewords below the head stored: `x28` holds the source's
doubleword whose low `c` bytes end the next one. -/
structure LS (s w u : MachineState) (hb K c j : Nat) : Prop where
  x17 : u.getReg .x17 = s.getReg .x10 + BitVec.ofNat 64 (K + hb - 8 * j)
  x29 : u.getReg .x29 = s.getReg .x11 + BitVec.ofNat 64 (K + hb - c - 8 * j)
  x28 : ∀ i < c, extractByte (u.getReg .x28) i =
    byteAt s (s.getReg .x11 + BitVec.ofNat 64 (K - c - 8 * j + i))
  x7 : u.getReg .x7 = w.getReg .x6 <<< ((3 : Word).toNat % 64)
  x12 : u.getReg .x12 = (0 - u.getReg .x7) &&& 56
  x30 : u.getReg .x30 = s.getReg .x10 + BitVec.ofNat 64 (K % 8 + 8)
  keep : ∀ x ∈ lsR, u.getReg x = w.getReg x
  copied : BCopied s u (hb + 8 * j)
  lt : 8 * j + 16 ≤ K

/-- At `0x80012578`, all doublewords but the lowest stored: `x28` holds the source's doubleword
whose low `c` bytes end the lowest one. -/
structure SA (s w u : MachineState) (hb K c : Nat) : Prop where
  x11 : u.getReg .x11 = s.getReg .x10 + BitVec.ofNat 64 (K % 8 + 8)
  x29 : u.getReg .x29 = s.getReg .x11 + BitVec.ofNat 64 (K % 8 + 8 - c)
  x28 : ∀ i < c, extractByte (u.getReg .x28) i =
    byteAt s (s.getReg .x11 + BitVec.ofNat 64 (K % 8 + 8 - c + i))
  x7 : u.getReg .x7 = w.getReg .x6 <<< ((3 : Word).toNat % 64)
  keep : ∀ x ∈ lsR, u.getReg x = w.getReg x
  copied : BCopied s u (hb + 8 * (K / 8 - 1))

theorem se_step {w : MachineState} {hb K c : Nat} (hx : BCtx s w hb K c) {u : MachineState}
    (hpc : u.pc = 0x80012330) (hu : QB s w u hb K c c) :
    (K < 16 → ∃ v, Reaches Image.code u v ∧ SA s w v hb K c ∧ v.pc = 0x80012578) ∧
    (16 ≤ K → ∃ v, Reaches Image.code u v ∧ v.pc = 0x80012350 ∧ LS s w v hb K c 0) := by
  have hb := hx.bounds
  have hB := hx.pre.buf
  have hdm := hx.pre.dst
  have hsm := hx.pre.src
  simp only [Mapped] at hdm hsm
  have hw := hx.b4
  have hK := hx.hK
  have hx2 : u.getReg .x2 + 8 = s.getReg .x2 - 8 := by
    rw [hu.keep .x2 (by decide), hw.x2]; addr_omega [hB]
  obtain ⟨v, hr, hv⟩ := mm_se.reaches hpc (by
    simp only [seE, Oblig.all, Oblig.holds, Addr.eval, E.eval, hx2]
    exact valid_of (by decide) (by addr_omega [hB]) (by omega))
  have k := keepOf hv rfl (.x29 :: seR)
  have e7 := hv.reg .x7 rfl
  have e28 := hv.reg .x28 rfl
  have e30 := hv.reg .x30 rfl
  blk at e7 e28 e30
  rw [hx2] at e28
  have kk (x : Reg) (hx' : x ∈ seR) : v.getReg x = w.getReg x :=
    (k x (List.mem_cons_of_mem _ hx')).trans (hu.keep x (seR_sub x hx'))
  have hx7 : u.getReg .x7 = s.getReg .x10 + BitVec.ofNat 64 (K % 8) := by
    rw [hu.keep .x7 (by decide), hw.x7, hK]
  have hx13 : v.getReg .x13 = s.getReg .x10 + BitVec.ofNat 64 K := by
    rw [kk .x13 (by decide), hw.x13, hK]
  have h7 : v.getReg .x7 = w.getReg .x6 <<< ((3 : Word).toNat % 64) := by
    rw [e7, hu.keep .x6 (by decide)]
  have h30 : v.getReg .x30 = s.getReg .x10 + BitVec.ofNat 64 (K % 8 + 8) := by
    rw [e30, hx7]; addr_omega [hdm, hb]
  have h28 (i : Nat) (hi : i < c) : extractByte (v.getReg .x28) i =
      byteAt s (s.getReg .x11 + BitVec.ofNat 64 (K - c + i)) := by
    rw [e28, hu.buf i hi, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hcp := hu.copied.same (sameOf hv rfl)
  refine ⟨fun hJ ↦ ?_, fun hJ ↦ ?_⟩
  · obtain ⟨z, rz, hz⟩ := mm_slskip.reaches (pcT hv rfl (by
      cond; rw [hx7, hu.keep .x13 (by decide), hw.x13, hK]; addr_omega [hdm, hb, hJ])) trivial
    have kz := keepOf hz rfl (.x7 :: .x28 :: .x29 :: lsR)
    have kz' (x : Reg) (hx' : x ∈ lsR) : z.getReg x = w.getReg x :=
      (kz x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx')))).trans
        (kk x (lsR_sub x hx'))
    have e11 := hz.reg .x11 rfl
    blk at e11
    have hJ1 : K / 8 - 1 = 0 := by omega
    refine ⟨z, hr.trans rz, ⟨?_, ?_, fun i hi ↦ ?_, by rw [kz .x7 (by decide), h7], kz',
      by rw [hJ1, Nat.mul_zero, Nat.add_zero]; exact hcp.same (sameOf hz rfl)⟩, pcC hz rfl⟩
    · rw [e11, hx13]; congr 2; omega
    · rw [kz .x29 (by decide), k .x29 (by decide), hu.x29]; congr 2; omega
    · rw [kz .x28 (by decide), h28 i hi]; congr 3; omega
  · obtain ⟨z, rz, hz⟩ := mm_slpre.reaches (pcF hv rfl (by
      cond; rw [hx7, hu.keep .x13 (by decide), hw.x13, hK]; addr_omega [hdm, hb, hJ])) trivial
    have kz := keepOf hz rfl (.x7 :: .x17 :: .x28 :: .x30 :: lsR)
    have kz' (x : Reg) (hx' : x ∈ lsR) : z.getReg x = w.getReg x :=
      (kz x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ hx'))))).trans (kk x (lsR_sub x hx'))
    have e12 := hz.reg .x12 rfl
    have e29 := hz.reg .x29 rfl
    blk at e12 e29
    have hx12 : v.getReg .x12 = s.getReg .x12 := by rw [kk .x12 (by decide), hw.x12]
    have hx11 : v.getReg .x11 = s.getReg .x11 := by rw [kk .x11 (by decide), hw.x11]
    have hx6 : v.getReg .x6 = BitVec.ofNat 64 c := by rw [kk .x6 (by decide), hx.x6]
    refine ⟨z, hr.trans rz, pcC hz rfl, ⟨?_, ?_, fun i hi ↦ ?_, by rw [kz .x7 (by decide), h7],
      by rw [e12, kz .x7 (by decide)], by rw [kz .x30 (by decide), h30], kz',
      by rw [Nat.mul_zero, Nat.add_zero]; exact hcp.same (sameOf hz rfl), by omega⟩⟩
    · rw [kz .x17 (by decide), kk .x17 (by decide), hw.x17]; addr_omega [hdm, hb]
    · rw [e29, hx11, hx12, hx6]; addr_omega [hsm, hb]
    · rw [kz .x28 (by decide), h28 i hi, Nat.mul_zero, Nat.sub_zero]

set_option maxHeartbeats 1000000 in
theorem sloop_body {w : MachineState} {hb K c : Nat} (hx : BCtx s w hb K c) (u : MachineState)
    (hu : ∃ j, u.pc = 0x80012350 ∧ LS s w u hb K c j) :
    (∃ v, Reaches Image.code u v ∧ v.pc = 0x80012578 ∧ SA s w v hb K c) ∨
    (∃ v, Reaches Image.code u v ∧ (∃ j, v.pc = 0x80012350 ∧ LS s w v hb K c j) ∧
      (v.getReg .x17).toNat < (u.getReg .x17).toNat) := by
  obtain ⟨j, hpc, hj⟩ := hu
  have hbs := hx.bounds
  have hdm := hx.pre.dst
  have hsm := hx.pre.src
  simp only [Mapped] at hdm hsm
  have hc := hx.hc
  have hlt := hj.lt
  have hx5 : u.getReg .x5 = 0 - BitVec.ofNat 64 hb := (hj.keep .x5 (by decide)).trans hx.b4.x5
  have hD : u.getReg .x17 + u.getReg .x5 + 0xfffffffffffffff8 =
      s.getReg .x10 + BitVec.ofNat 64 (K - 8 * j - 8) := by
    rw [hj.x17, hx5, add_zero_sub, neg8]; addr_omega [hdm, hbs, hlt]
  have hS : u.getReg .x29 + u.getReg .x5 + 0xfffffffffffffff8 =
      s.getReg .x11 + BitVec.ofNat 64 (K - c - 8 * j - 8) := by
    rw [hj.x29, hx5, add_zero_sub, neg8]; addr_omega [hsm, hbs, hlt]
  have hD8 : (s.getReg .x10 + BitVec.ofNat 64 (K - 8 * j - 8)).toNat % 8 = 0 := by
    addr_omega [hdm, hbs, hlt]
  have hS8 : (s.getReg .x11 + BitVec.ofNat 64 (K - c - 8 * j - 8)).toNat % 8 = 0 := by
    addr_omega [hsm, hbs, hlt, hc]
  obtain ⟨v, hr, hv⟩ := mm_sloop.reaches hpc (by
    simp only [sloopE, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, hD, hS]
    exact ⟨valid_of (by decide) (by addr_omega [hdm, hbs, hlt]) hD8,
      valid_of (by decide) (by addr_omega [hsm, hbs, hlt]) hS8⟩)
  have k := keepOf hv rfl (.x7 :: .x12 :: .x30 :: lsR)
  have hm := memOf hv rfl
  have e11 := hv.reg .x11 rfl
  have e17 := hv.reg .x17 rfl
  have e28 := hv.reg .x28 rfl
  have e29 := hv.reg .x29 rfl
  blk at hm e11 e17 e28 e29
  have hsh := shamt_of (a := c) hbs.1 hbs.2.1
  rw [← hx.x6, ← hj.x7, ← hj.x12] at hsh
  rw [hD, hS, hsh.1, hsh.2] at hm
  rw [hS] at e28
  have hM (i : Nat) (hi : i < 8) : extractByte (u.getMem (s.getReg .x11 +
      BitVec.ofNat 64 (K - c - 8 * j - 8))) i =
      byteAt s (s.getReg .x11 + BitVec.ofNat 64 (K - c - 8 * j - 8 + i)) := by
    rw [← byteAt_add hS8 hi, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hj.copied.src hx.pre (by omega) (by omega)
  have hcp : BCopied s v (hb + 8 * j + 8) := by
    refine hj.copied.extend hx.pre (by omega) ?_ fun i hi ↦ ?_
    · rw [show (s.getReg .x12).toNat - (hb + 8 * j + 8) = K - 8 * j - 8 by omega]
      exact ByteFrame.of_single hD8 fun x hx' ↦ frameOf hv rfl x (by blk; rw [hD]; exact hx')
    · have e (x : Word) : x + BitVec.ofNat 64 ((s.getReg .x12).toNat - (hb + 8 * j + 8) + i) =
          x + BitVec.ofNat 64 (K - 8 * j - 8) + BitVec.ofNat 64 i := by
        rw [show (s.getReg .x12).toNat - (hb + 8 * j + 8) = K - 8 * j - 8 by omega,
          BitVec.ofNat_add, BitVec.add_assoc]
      rw [e, e, byteAt_add hD8 hi, hm, extractByte_shift _ _ hbs.1 hbs.2.1 hi,
        BitVec.add_assoc (s.getReg .x11), ← BitVec.ofNat_add]
      split
      · rw [hM _ (by omega)]; congr 3; omega
      · rw [hj.x28 _ (by omega)]; congr 3; omega
  have hk2 (x : Reg) (hx' : x ∈ lsR) : v.getReg x = w.getReg x :=
    (k x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx')))).trans
      (hj.keep x hx')
  have h17 : v.getReg .x17 = s.getReg .x10 + BitVec.ofNat 64 (K + hb - 8 * (j + 1)) := by
    rw [e17, hj.x17, neg8]; addr_omega [hdm, hbs, hlt]
  have h29 : v.getReg .x29 = s.getReg .x11 + BitVec.ofNat 64 (K + hb - c - 8 * (j + 1)) := by
    rw [e29, hj.x29, neg8]; addr_omega [hsm, hbs, hlt]
  have h11 : v.getReg .x11 = s.getReg .x10 + BitVec.ofNat 64 (K - 8 * (j + 1)) := by
    rw [e11, hj.x17, neg8, hx5, add_zero_sub]; addr_omega [hdm, hbs, hlt]
  have h28 (i : Nat) (hi : i < c) : extractByte (v.getReg .x28) i =
      byteAt s (s.getReg .x11 + BitVec.ofNat 64 (K - c - 8 * (j + 1) + i)) := by
    rw [e28, hM i (by omega)]
    congr 3
  have hcp' : BCopied s v (hb + 8 * (j + 1)) := by
    rw [show hb + 8 * (j + 1) = hb + 8 * j + 8 by omega]; exact hcp
  have hcond : u.getReg .x17 + 0xfffffffffffffff8 + u.getReg .x5 =
      s.getReg .x10 + BitVec.ofNat 64 (K - 8 * j - 8) := by
    rw [hj.x17, neg8, hx5, add_zero_sub]; addr_omega [hdm, hbs, hlt]
  by_cases hlast : 8 * (j + 1) + 16 ≤ K
  · refine Or.inr ⟨v, hr, ⟨j + 1, pcT hv rfl ?_, ⟨h17, h29, h28,
      by rw [k .x7 (by decide), hj.x7], by rw [k .x12 (by decide), k .x7 (by decide), hj.x12],
      by rw [k .x30 (by decide), hj.x30], hk2, hcp', hlast⟩⟩, ?_⟩
    · cond; rw [hj.x30, hcond]; addr_omega [hdm, hbs, hlast]
    · rw [h17, hj.x17]; addr_omega [hdm, hbs, hlt]
  · have hl2 : K < 8 * (j + 1) + 16 := by omega
    obtain ⟨z, rz, hz⟩ := mm_slafter.reaches (pcF hv rfl (by
      cond; rw [hj.x30, hcond]; addr_omega [hdm, hbs, hl2, hlt])) trivial
    have kz := keepOf hz rfl (.x7 :: .x11 :: .x28 :: lsR)
    have ez := hz.reg .x29 rfl
    blk at ez
    have hJ : K / 8 - 1 = j + 1 := by omega
    refine Or.inl ⟨z, hr.trans rz, pcC hz rfl, ⟨?_, ?_, fun i hi ↦ ?_,
      by rw [kz .x7 (by decide), k .x7 (by decide), hj.x7],
      fun x hx' ↦ (kz x (by simp [hx'])).trans (hk2 x hx'),
      by rw [hJ]; exact hcp'.same (sameOf hz rfl)⟩⟩
    · rw [kz .x11 (by decide), h11]; congr 2; omega
    · rw [ez, h29, hk2 .x5 (by decide), hx.b4.x5, add_zero_sub]; addr_omega [hsm, hbs, hlt, hJ, hl2]
    · rw [kz .x28 (by decide), h28 i hi]; congr 3; omega

/-! ## The second buffer fill and the lowest doubleword -/

def sbR : List Reg := [.x2, .x7, .x11, .x13, .x14, .x15, .x16, .x28] ++ keepC

/-- In the second fill, from `z` at `0x80012578`: `p` bytes of the source from the lowest
doubleword's start in the buffer, from its byte `c` on. -/
structure PB (s z u : MachineState) (hb K c p : Nat) : Prop where
  x17 : u.getReg .x17 = s.getReg .x2 - 8 + BitVec.ofNat 64 c
  x29 : u.getReg .x29 = BitVec.ofNat 64 (8 - c)
  keep : ∀ x ∈ sbR, u.getReg x = z.getReg x
  copied : BCopied s u (hb + 8 * (K / 8 - 1))
  buf : ∀ i, c ≤ i → i < c + p → extractByte (u.getMem (s.getReg .x2 - 8)) i =
    byteAt s (s.getReg .x11 + BitVec.ofNat 64 (K % 8) + BitVec.ofNat 64 (i - c))

theorem PB.src {w z u : MachineState} {hb K c p : Nat} (hx : BCtx s w hb K c)
    (hu : PB s z u hb K c p) {j : Nat} (hj : j < 8) :
    byteAt u (s.getReg .x11 + BitVec.ofNat 64 (K % 8) + BitVec.ofNat 64 j) =
      byteAt s (s.getReg .x11 + BitVec.ofNat 64 (K % 8) + BitVec.ofNat 64 j) := by
  have hb := hx.bounds
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hu.copied.src hx.pre (by omega) (by omega)

theorem PB.of_same {z u v : MachineState} {hb K c p : Nat} (hu : PB s z u hb K c p)
    (hk : ∀ x ∈ Reg.x17 :: Reg.x29 :: sbR, v.getReg x = u.getReg x)
    (hm : ∀ x, v.getMem x = u.getMem x) : PB s z v hb K c p :=
  ⟨by rw [hk .x17 (by decide), hu.x17], by rw [hk .x29 (by decide), hu.x29],
    fun x hx ↦ (hk x (by simp [hx])).trans (hu.keep x hx), hu.copied.same hm,
    fun i h1 h2 ↦ by rw [hm]; exact hu.buf i h1 h2⟩

theorem sa_step {w z : MachineState} {hb K c : Nat} (hx : BCtx s w hb K c)
    (hpc : z.pc = 0x80012578) (hz : SA s w z hb K c) :
    ∃ v, Reaches Image.code z v ∧ PB s z v hb K c 0 ∧
      v.getReg .x5 = s.getReg .x11 + BitVec.ofNat 64 (K % 8) ∧ v.getReg .x12 = 0 ∧
      ((BitVec.ofNat 64 (8 - c) &&& 1) ≠ 0 → v.pc = 0x80012680) ∧
      ((BitVec.ofNat 64 (8 - c) &&& 1) = 0 → v.pc = 0x800125a0) := by
  have hbs := hx.bounds
  have hB := hx.pre.buf
  have hsm := hx.pre.src
  simp only [Mapped] at hsm
  have hx2 : z.getReg .x2 + 8 = s.getReg .x2 - 8 := by
    rw [hz.keep .x2 (by decide), hx.b4.x2]; addr_omega [hB]
  have hx6 : z.getReg .x6 = BitVec.ofNat 64 c := (hz.keep .x6 (by decide)).trans hx.x6
  obtain ⟨v, hr, hv⟩ := mm_sa.reaches hpc (by
    simp only [saE, Oblig.all, Oblig.holds, Addr.eval, E.eval, hx2]
    exact valid_of (by decide) (by addr_omega [hB]) (by omega))
  have k := keepOf hv rfl sbR
  have e5 := hv.reg .x5 rfl
  have e12 := hv.reg .x12 rfl
  have e17 := hv.reg .x17 rfl
  have e29 := hv.reg .x29 rfl
  have e6 := hv.reg .x6 rfl
  blk at e5 e12 e17 e29 e6
  have h8c : (8 : Word) - BitVec.ofNat 64 c = BitVec.ofNat 64 (8 - c) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [wordToNatLit]
    omega
  have h29 : v.getReg .x29 = BitVec.ofNat 64 (8 - c) := by rw [e29, hx6, h8c]
  have hf (x : Word) (hx' : x ≠ s.getReg .x2 - 8) : v.getMem x = z.getMem x :=
    frameOf hv rfl x (by simp only [Addr.eval, E.eval, hx2]; exact hx')
  refine ⟨v, hr, ⟨by rw [e17, hx2, or_eq_add hbs.2.2.2.2.2.2 (by rw [hx6, BitVec.toNat_ofNat]; omega),
    hx6], h29, k, hz.copied.stack hx.pre hbs.2.2.2.2.2.2 (by omega) (by omega) hf,
    fun i h1 h2 ↦ by omega⟩, ?_, e12, fun hc ↦ pcT hv rfl ?_, fun hc ↦ pcF hv rfl ?_⟩
  · rw [e5, hz.x29, hx6, neg8]; addr_omega [hsm, hbs]
  · cond; rw [hx6, h8c]; exact hc
  · cond; rw [hx6, h8c]; exact hc

theorem sab_step {w z : MachineState} {hb K c : Nat} (hx : BCtx s w hb K c) {u : MachineState}
    (hpc : u.pc = 0x80012680) (hu : PB s z u hb K c 0)
    (h5 : u.getReg .x5 = s.getReg .x11 + BitVec.ofNat 64 (K % 8)) :
    ∃ v, Reaches Image.code u v ∧ PB s z v hb K c 1 ∧ v.getReg .x5 = u.getReg .x5 ∧
      v.getReg .x12 = 1 ∧ ((BitVec.ofNat 64 (8 - c) &&& 2) = 0 → v.pc = 0x800125a8) ∧
      ((BitVec.ofNat 64 (8 - c) &&& 2) ≠ 0 → v.pc = 0x80012694) := by
  have hbs := hx.bounds
  have hB := hx.pre.buf
  have hsm := hx.pre.src
  simp only [Mapped] at hsm
  obtain ⟨v, hr, hv⟩ := mm_sab.reaches hpc (by
    simp only [sabE, Oblig.all, Oblig.holds, Addr.eval, E.eval, add_zero_lit, hu.x17, h5]
    exact ⟨valid_of (by decide) (by addr_omega [hB, hbs]) (Nat.mod_one _),
      valid_of (by decide) (by addr_omega [hsm, hbs]) (Nat.mod_one _)⟩)
  have k := keepOf hv rfl (.x5 :: .x17 :: .x29 :: sbR)
  have hm := memOf hv rfl
  have e12 := hv.reg .x12 rfl
  blk at hm e12
  rw [hu.x17] at hm
  have hbuf := fun i (hi : i < 8) ↦ buf_update (lk := .bu) (sk := .b) rfl hbs.2.2.2.2.2.2 (q := c)
    (by omega) (Nat.mod_one _) (Nat.mod_one _) hm hi
  have hf (x : Word) (hx' : x ≠ s.getReg .x2 - 8) : v.getMem x = u.getMem x :=
    frameOf hv rfl x (by blk; rw [hu.x17, (key_eq hbs.2.2.2.2.2.2 hbs.2.1).1]; exact hx')
  have hkk : ∀ x ∈ Reg.x17 :: Reg.x29 :: sbR, v.getReg x = u.getReg x :=
    fun x hx' ↦ k x (List.mem_cons_of_mem _ hx')
  refine ⟨v, hr, ⟨by rw [hkk .x17 (by decide), hu.x17], by rw [hkk .x29 (by decide), hu.x29],
    fun x hx' ↦ (hkk x (by simp [hx'])).trans (hu.keep x hx'),
    hu.copied.stack hx.pre hbs.2.2.2.2.2.2 (by omega) (by omega) hf, ?_⟩, k .x5 (by decide),
    e12, fun hc ↦ pcT hv rfl (by cond; rw [hu.x29]; exact hc),
    fun hc ↦ pcF hv rfl (by cond; rw [hu.x29]; exact hc)⟩
  refine buf_step (p := 0) (by omega) (fun j hj ↦ ?_) hu.buf hbuf (by simp [StoreKind.width]; omega)
  have hw1 : StoreKind.b.width = 1 := rfl
  rw [h5, show j = 0 by omega]
  exact hu.src hx (by omega)

theorem sah_step {w z : MachineState} {hb K c p : Nat} (hx : BCtx s w hb K c) {u : MachineState}
    (hpc : u.pc = 0x80012694) (hu : PB s z u hb K c p)
    (h5 : u.getReg .x5 = s.getReg .x11 + BitVec.ofNat 64 (K % 8))
    (h12 : u.getReg .x12 = BitVec.ofNat 64 p) (hal : (c + p) % 2 = 0) (h8 : c + p + 2 ≤ 8) :
    ∃ v, Reaches Image.code u v ∧ PB s z v hb K c (p + 2) ∧ v.getReg .x5 = u.getReg .x5 ∧
      v.getReg .x12 = BitVec.ofNat 64 (p + 2) ∧
      ((BitVec.ofNat 64 (8 - c) &&& 4) ≠ 0 → v.pc = 0x800125b0) ∧
      ((BitVec.ofNat 64 (8 - c) &&& 4) = 0 → v.pc = 0x800126b0) := by
  have hbs := hx.bounds
  have hB := hx.pre.buf
  have hsm := hx.pre.src
  simp only [Mapped] at hsm
  have hc := hx.hc
  have hq : u.getReg .x17 + u.getReg .x12 = s.getReg .x2 - 8 + BitVec.ofNat 64 (c + p) := by
    rw [hu.x17, h12, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hP : u.getReg .x5 + u.getReg .x12 =
      s.getReg .x11 + BitVec.ofNat 64 (K % 8) + BitVec.ofNat 64 p := by rw [h5, h12]
  obtain ⟨v, hr, hv⟩ := mm_sah.reaches hpc (by
    simp only [sahE, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, add_zero_lit, hq, hP]
    exact ⟨valid_of (by decide) (by addr_omega [hB, hbs, h8]) (by addr_omega [hB, hbs, hal, h8]),
      valid_of (by decide) (by addr_omega [hsm, hbs, h8])
        (by addr_omega [hsm, hbs, hc, hal, h8])⟩)
  have k := keepOf hv rfl (.x5 :: .x17 :: .x29 :: sbR)
  have hm := memOf hv rfl
  have e12 := hv.reg .x12 rfl
  blk at hm e12
  rw [hq, hP] at hm
  have hbuf := fun i (hi : i < 8) ↦ buf_update (lk := .h) (sk := .h) rfl hbs.2.2.2.2.2.2
    (q := c + p) (by omega) (by simp only [StoreKind.width]; addr_omega [hB, hbs, hal, h8])
    (by simp only [StoreKind.width]; addr_omega [hsm, hbs, hc, hal, h8]) hm hi
  have hf (x : Word) (hx' : x ≠ s.getReg .x2 - 8) : v.getMem x = u.getMem x :=
    frameOf hv rfl x (by blk; rw [hq, (key_eq hbs.2.2.2.2.2.2 (by omega)).1]; exact hx')
  have hkk : ∀ x ∈ Reg.x17 :: Reg.x29 :: sbR, v.getReg x = u.getReg x :=
    fun x hx' ↦ k x (List.mem_cons_of_mem _ hx')
  refine ⟨v, hr, ⟨by rw [hkk .x17 (by decide), hu.x17], by rw [hkk .x29 (by decide), hu.x29],
    fun x hx' ↦ (hkk x (by simp [hx'])).trans (hu.keep x hx'),
    hu.copied.stack hx.pre hbs.2.2.2.2.2.2 (by omega) (by omega) hf, ?_⟩, k .x5 (by decide),
    by rw [e12, h12, addw2 (by omega)], fun hc ↦ pcT hv rfl (by cond; rw [hu.x29]; exact hc),
    fun hc ↦ pcF hv rfl (by cond; rw [hu.x29]; exact hc)⟩
  refine buf_step (p := p) rfl (fun j hj ↦ ?_) hu.buf hbuf (by omega)
  rw [BitVec.add_assoc (s.getReg .x11 + _), ← BitVec.ofNat_add]
  exact hu.src hx (by omega)

theorem saw_step {w z : MachineState} {hb K c p : Nat} (hx : BCtx s w hb K c) {u : MachineState}
    (hpc : u.pc = 0x800125b0) (hu : PB s z u hb K c p)
    (h5 : u.getReg .x5 = s.getReg .x11 + BitVec.ofNat 64 (K % 8))
    (h12 : u.getReg .x12 = BitVec.ofNat 64 p) (hal : (c + p) % 4 = 0) (h8 : c + p + 4 ≤ 8) :
    ∃ v, Reaches Image.code u v ∧ PB s z v hb K c (p + 4) ∧ v.pc = 0x800125c0 := by
  have hbs := hx.bounds
  have hB := hx.pre.buf
  have hsm := hx.pre.src
  simp only [Mapped] at hsm
  have hc := hx.hc
  have hq : u.getReg .x17 + u.getReg .x12 = s.getReg .x2 - 8 + BitVec.ofNat 64 (c + p) := by
    rw [hu.x17, h12, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hP : u.getReg .x5 + u.getReg .x12 =
      s.getReg .x11 + BitVec.ofNat 64 (K % 8) + BitVec.ofNat 64 p := by rw [h5, h12]
  obtain ⟨v, hr, hv⟩ := mm_saw.reaches hpc (by
    simp only [sawE, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, add_zero_lit, hq, hP]
    exact ⟨valid_of (by decide) (by addr_omega [hB, hbs, h8]) (by addr_omega [hB, hbs, hal, h8]),
      valid_of (by decide) (by addr_omega [hsm, hbs, h8])
        (by addr_omega [hsm, hbs, hc, hal, h8])⟩)
  have k := keepOf hv rfl (.x17 :: .x29 :: sbR)
  have hm := memOf hv rfl
  blk at hm
  rw [hq, hP] at hm
  have hbuf := fun i (hi : i < 8) ↦ buf_update (lk := .w) (sk := .w) rfl hbs.2.2.2.2.2.2
    (q := c + p) (by omega) (by simp only [StoreKind.width]; addr_omega [hB, hbs, hal, h8])
    (by simp only [StoreKind.width]; addr_omega [hsm, hbs, hc, hal, h8]) hm hi
  have hf (x : Word) (hx' : x ≠ s.getReg .x2 - 8) : v.getMem x = u.getMem x :=
    frameOf hv rfl x (by blk; rw [hq, (key_eq hbs.2.2.2.2.2.2 (by omega)).1]; exact hx')
  refine ⟨v, hr, ⟨by rw [k .x17 (by decide), hu.x17], by rw [k .x29 (by decide), hu.x29],
    fun x hx' ↦ (k x (by simp [hx'])).trans (hu.keep x hx'),
    hu.copied.stack hx.pre hbs.2.2.2.2.2.2 (by omega) (by omega) hf, ?_⟩, pcC hv rfl⟩
  refine buf_step (p := p) rfl (fun j hj ↦ ?_) hu.buf hbuf (by omega)
  rw [BitVec.add_assoc (s.getReg .x11 + _), ← BitVec.ofNat_add]
  exact hu.src hx (by omega)

theorem sat2_step {z u : MachineState} {hb K c p : Nat} (hpc : u.pc = 0x800125a0)
    (hu : PB s z u hb K c p) :
    ∃ v, Reaches Image.code u v ∧ PB s z v hb K c p ∧ v.getReg .x5 = u.getReg .x5 ∧
      v.getReg .x12 = u.getReg .x12 ∧ ((BitVec.ofNat 64 (8 - c) &&& 2) ≠ 0 → v.pc = 0x80012694) ∧
      ((BitVec.ofNat 64 (8 - c) &&& 2) = 0 → v.pc = 0x800125a8) := by
  obtain ⟨v, hr, hv⟩ := mm_sat2.reaches hpc trivial
  have k := keepOf hv rfl (.x5 :: .x12 :: .x17 :: .x29 :: sbR)
  exact ⟨v, hr, hu.of_same (fun x hx ↦ k x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
    (sameOf hv rfl), k .x5 (by decide), k .x12 (by decide),
    fun hc ↦ pcT hv rfl (by cond; rw [hu.x29]; exact hc),
    fun hc ↦ pcF hv rfl (by cond; rw [hu.x29]; exact hc)⟩

theorem sat4_step {z u : MachineState} {hb K c p : Nat} (hpc : u.pc = 0x800125a8)
    (hu : PB s z u hb K c p) :
    ∃ v, Reaches Image.code u v ∧ PB s z v hb K c p ∧ v.getReg .x5 = u.getReg .x5 ∧
      v.getReg .x12 = u.getReg .x12 ∧ ((BitVec.ofNat 64 (8 - c) &&& 4) = 0 → v.pc = 0x800125c0) ∧
      ((BitVec.ofNat 64 (8 - c) &&& 4) ≠ 0 → v.pc = 0x800125b0) := by
  obtain ⟨v, hr, hv⟩ := mm_sat4.reaches hpc trivial
  have k := keepOf hv rfl (.x5 :: .x12 :: .x17 :: .x29 :: sbR)
  exact ⟨v, hr, hu.of_same (fun x hx ↦ k x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
    (sameOf hv rfl), k .x5 (by decide), k .x12 (by decide),
    fun hc ↦ pcT hv rfl (by cond; rw [hu.x29]; exact hc),
    fun hc ↦ pcF hv rfl (by cond; rw [hu.x29]; exact hc)⟩

theorem saj_step {z u : MachineState} {hb K c p : Nat} (hpc : u.pc = 0x800126b0)
    (hu : PB s z u hb K c p) :
    ∃ v, Reaches Image.code u v ∧ PB s z v hb K c p ∧ v.pc = 0x800125c0 := by
  obtain ⟨v, hr, hv⟩ := mm_saj.reaches hpc trivial
  exact ⟨v, hr, hu.of_same (keepOf hv rfl _) (sameOf hv rfl), pcC hv rfl⟩

/-- The second buffer fill: the source's bytes from the lowest doubleword's start. -/
theorem chainB {w z : MachineState} {hb K c : Nat} (hx : BCtx s w hb K c)
    (hpc : z.pc = 0x80012578) (hz : SA s w z hb K c) :
    ∃ v, Reaches Image.code z v ∧ PB s z v hb K c (8 - c) ∧ v.pc = 0x800125c0 := by
  have hbs := hx.bounds
  obtain ⟨u₀, r₀, p₀, x5₀, x12₀, t₀, f₀⟩ := sa_step hx hpc hz
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨
    c = 6 ∨ c = 7 := by omega
  · obtain ⟨u₁, r₁, p₁, x5₁, x12₁, -, f₁⟩ := sab_step hx (t₀ (by decide)) p₀ x5₀
    obtain ⟨u₂, r₂, p₂, x5₂, x12₂, t₂, -⟩ := sah_step hx (f₁ (by decide)) p₁ (by rw [x5₁, x5₀])
      x12₁ (by decide) (by decide)
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := saw_step hx (t₂ (by decide)) p₂ (by rw [x5₂, x5₁, x5₀]) x12₂
      (by decide) (by decide)
    exact ⟨u₃, r₀.trans (r₁.trans (r₂.trans r₃)), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, x5₁, x12₁, t₁, -⟩ := sat2_step (f₀ (by decide)) p₀
    obtain ⟨u₂, r₂, p₂, x5₂, x12₂, t₂, -⟩ := sah_step hx (t₁ (by decide)) p₁ (by rw [x5₁, x5₀])
      (by rw [x12₁, x12₀]; rfl) (by decide) (by decide)
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := saw_step hx (t₂ (by decide)) p₂ (by rw [x5₂, x5₁, x5₀]) x12₂
      (by decide) (by decide)
    exact ⟨u₃, r₀.trans (r₁.trans (r₂.trans r₃)), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, x5₁, x12₁, t₁, -⟩ := sab_step hx (t₀ (by decide)) p₀ x5₀
    obtain ⟨u₂, r₂, p₂, x5₂, x12₂, -, f₂⟩ := sat4_step (t₁ (by decide)) p₁
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := saw_step hx (f₂ (by decide)) p₂ (by rw [x5₂, x5₁, x5₀])
      (by rw [x12₂, x12₁]; rfl) (by decide) (by decide)
    exact ⟨u₃, r₀.trans (r₁.trans (r₂.trans r₃)), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, x5₁, x12₁, -, f₁⟩ := sat2_step (f₀ (by decide)) p₀
    obtain ⟨u₂, r₂, p₂, x5₂, x12₂, -, f₂⟩ := sat4_step (f₁ (by decide)) p₁
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := saw_step hx (f₂ (by decide)) p₂ (by rw [x5₂, x5₁, x5₀])
      (by rw [x12₂, x12₁, x12₀]; rfl) (by decide) (by decide)
    exact ⟨u₃, r₀.trans (r₁.trans (r₂.trans r₃)), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, x5₁, x12₁, -, f₁⟩ := sab_step hx (t₀ (by decide)) p₀ x5₀
    obtain ⟨u₂, r₂, p₂, -, -, -, f₂⟩ := sah_step hx (f₁ (by decide)) p₁ (by rw [x5₁, x5₀])
      x12₁ (by decide) (by decide)
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := saj_step (f₂ (by decide)) p₂
    exact ⟨u₃, r₀.trans (r₁.trans (r₂.trans r₃)), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, x5₁, x12₁, t₁, -⟩ := sat2_step (f₀ (by decide)) p₀
    obtain ⟨u₂, r₂, p₂, -, -, -, f₂⟩ := sah_step hx (t₁ (by decide)) p₁ (by rw [x5₁, x5₀])
      (by rw [x12₁, x12₀]; rfl) (by decide) (by decide)
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := saj_step (f₂ (by decide)) p₂
    exact ⟨u₃, r₀.trans (r₁.trans (r₂.trans r₃)), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, -, -, t₁, -⟩ := sab_step hx (t₀ (by decide)) p₀ x5₀
    obtain ⟨u₂, r₂, p₂, -, -, t₂, -⟩ := sat4_step (t₁ (by decide)) p₁
    exact ⟨u₂, r₀.trans (r₁.trans r₂), p₂, t₂ (by decide)⟩

set_option maxHeartbeats 1000000 in
theorem sfin_step {w z : MachineState} {hb K c : Nat} (hx : BCtx s w hb K c) (hz : SA s w z hb K c)
    {u : MachineState} (hpc : u.pc = 0x800125c0) (hu : PB s z u hb K c (8 - c)) :
    ∃ v, Reaches Image.code u v ∧ BDone s v hb := by
  have hbs := hx.bounds
  have hB := hx.pre.buf
  have hdm := hx.pre.dst
  simp only [Mapped] at hdm
  have hw := hx.b4
  have hK := hx.hK
  have hx2 : u.getReg .x2 + 8 = s.getReg .x2 - 8 := by
    rw [hu.keep .x2 (by decide), hz.keep .x2 (by decide), hw.x2]; addr_omega [hB]
  have hD : u.getReg .x11 + 0xfffffffffffffff8 = s.getReg .x10 + BitVec.ofNat 64 (K % 8) := by
    rw [hu.keep .x11 (by decide), hz.x11, neg8]; addr_omega [hdm, hbs]
  have hD8 : (s.getReg .x10 + BitVec.ofNat 64 (K % 8)).toNat % 8 = 0 := by addr_omega [hdm, hbs]
  obtain ⟨v, hr, hv⟩ := mm_sfin.reaches hpc (by
    simp only [sfinE, Oblig.all, Oblig.holds, Addr.eval, E.eval, hx2, hD]
    exact ⟨valid_of (by decide) (by addr_omega [hdm, hbs]) hD8,
      valid_of (by decide) (by addr_omega [hB]) (by omega)⟩)
  have k := keepOf hv rfl lsR
  have hm := memOf hv rfl
  blk at hm
  have hsh := shamt_of (a := c) hbs.1 hbs.2.1
  rw [← hx.x6, ← hz.x7, ← hu.keep .x7 (by decide)] at hsh
  rw [hD, hx2, hsh.1, hsh.2, hu.keep .x28 (by decide)] at hm
  have hcp : BCopied s v (hb + 8 * (K / 8 - 1) + 8) := by
    refine hu.copied.extend hx.pre (by omega) ?_ fun i hi ↦ ?_
    · rw [show (s.getReg .x12).toNat - (hb + 8 * (K / 8 - 1) + 8) = K % 8 by omega]
      exact ByteFrame.of_single hD8 fun x hx' ↦ frameOf hv rfl x (by blk; rw [hD]; exact hx')
    · have e (x : Word) : x + BitVec.ofNat 64
          ((s.getReg .x12).toNat - (hb + 8 * (K / 8 - 1) + 8) + i) =
          x + BitVec.ofNat 64 (K % 8) + BitVec.ofNat 64 i := by
        rw [show (s.getReg .x12).toNat - (hb + 8 * (K / 8 - 1) + 8) = K % 8 by omega,
          BitVec.ofNat_add, BitVec.add_assoc]
      rw [e, e, byteAt_add hD8 hi, hm, extractByte_shift _ _ hbs.1 hbs.2.1 hi]
      split
      · rw [hu.buf (i + c) (by omega) (by omega), Nat.add_sub_cancel]
      · rw [hz.x28 _ (by omega), BitVec.add_assoc (s.getReg .x11), ← BitVec.ofNat_add]
        congr 3
        omega
  have kk (x : Reg) (hx' : x ∈ lsR) (hx'' : x ∈ sbR) : v.getReg x = w.getReg x :=
    (k x hx').trans ((hu.keep x hx'').trans (hz.keep x hx'))
  refine ⟨v, hr, ⟨pcC hv rfl, by rw [kk .x13 (by decide) (by decide), hw.x13],
    by rw [kk .x16 (by decide) (by decide), hw.x16], by rw [kk .x14 (by decide) (by decide),
      hw.x14], by rw [kk .x15 (by decide) (by decide), hw.x15],
    by rw [kk .x2 (by decide) (by decide), hw.x2],
    fun x hx' ↦ (kk x (by simp [lsR, hx']) (by simp [sbR, hx'])).trans (hw.keep x hx'), ?_,
    by omega⟩⟩
  rw [← hK, show hb + 8 * (K / 8) = hb + 8 * (K / 8 - 1) + 8 by omega]
  exact hcp

/-- **The backward shifting path** reaches the tail. -/
theorem bshift_ok : BShiftOk := by
  intro s w hb hp hw hpc h6
  have hx : BCtx s w hb ((s.getReg .x12).toNat - hb)
      (((s.getReg .x11).toNat + ((s.getReg .x12).toNat - hb)) % 8) :=
    ⟨hp, hw, rfl, rfl, by rw [← hw.x6]; exact h6⟩
  have hbs := hx.bounds
  obtain ⟨u₁, r₁, p₁, pc₁⟩ := chainA hx hpc
  obtain ⟨hS, hL⟩ := se_step hx pc₁ p₁
  obtain ⟨z, rz, hz, pcz⟩ : ∃ z, Reaches Image.code u₁ z ∧
      SA s w z hb ((s.getReg .x12).toNat - hb)
        (((s.getReg .x11).toNat + ((s.getReg .x12).toNat - hb)) % 8) ∧ z.pc = 0x80012578 := by
    by_cases hJ : (s.getReg .x12).toNat - hb < 16
    · exact hS hJ
    · obtain ⟨u₂, r₂, pc₂, p₂⟩ := hL (by omega)
      obtain ⟨z, rz, pcz, hz⟩ := Reaches.loop (code := Image.code)
        (fun u ↦ ∃ j, u.pc = 0x80012350 ∧ LS s w u hb ((s.getReg .x12).toNat - hb)
          (((s.getReg .x11).toNat + ((s.getReg .x12).toNat - hb)) % 8) j)
        (fun u ↦ (u.getReg .x17).toNat)
        (fun v ↦ v.pc = 0x80012578 ∧ SA s w v hb ((s.getReg .x12).toNat - hb)
          (((s.getReg .x11).toNat + ((s.getReg .x12).toNat - hb)) % 8))
        (sloop_body hx) u₂ ⟨0, pc₂, p₂⟩
      exact ⟨z, r₂.trans rz, hz, pcz⟩
  obtain ⟨u₃, r₃, p₃, pc₃⟩ := chainB hx pcz hz
  obtain ⟨v, rv, hv⟩ := sfin_step hx hz pc₃ p₃
  exact ⟨v, r₁.trans (rz.trans (r₃.trans rv)), hv⟩

end Rv64Verifier.Runtime.Backward
