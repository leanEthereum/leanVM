import Rv64Verifier.Proofs.Runtime.Forward

/-!
# The forward copy's shifting path

When the source is not aligned once the destination is (its byte position `a`, `0 < a < 8`), the
forward copy fills an 8-byte stack buffer with the source's bytes up to its next multiple of 8,
by a byte, a halfword and a word load at any alignment, as the bits of `8 - a` say (`chain1`),
then stores each destination doubleword from two aligned source doublewords shifted together
(`loop_body`), the last one with the buffer refilled by the next doubleword's first `a` bytes
(`chain2`, `fin_ok`).
-/

namespace Rv64Verifier.Runtime.Forward
open RiscvZkvm.Rv64 Rv64Verifier.Sym
open Rv64Verifier.Runtime.Memcpy (keepE keepE_reg keepC)

variable {s : MachineState}

/-! ## Words -/

/-- A small access in one of the data windows, aligned to its width, is valid. -/
theorem valid_of {a : Word} {w : Nat} (hw : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8)
    (hz : (0x20 ≤ a.toNat ∧ a.toNat + w ≤ 0x78000000) ∨
      (0xa0000000 ≤ a.toNat ∧ a.toNat + w ≤ 0xc0000000)) (hal : a.toNat % w = 0) :
    validAccess w a = true := by
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp only [validAccess, isValidByteAccess, isValidHalfwordAccess, isValidMemAccess,
      isValidDwordAccess, isValidMemAddr_eq, isAligned2, isAligned4, isAligned8, MEM_START, MEM_END,
      INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] <;> omega

/-- The stack buffer, `sp - 8` on entry, is an aligned doubleword of a data window. -/
theorem FwdPre.buf (hp : FwdPre s) :
    (s.getReg .x2 - 8).toNat = (s.getReg .x2).toNat - 8 ∧ (s.getReg .x2).toNat % 16 = 0 ∧
    ((0x20 ≤ (s.getReg .x2).toNat - 8 ∧ (s.getReg .x2).toNat ≤ 0x78000000) ∨
      (0xa0000000 ≤ (s.getReg .x2).toNat - 8 ∧ (s.getReg .x2).toNat ≤ 0xc0000000)) := by
  have hb := hp.stack.bounds (by decide) (by decide)
  have hv := (validAccess_eight _).mp (hp.stack.valid 1 (by decide))
  simp only [stackLo, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] at hv hb
  have hsp := hp.sp
  refine ⟨by rw [BitVec.toNat_sub]; simp; omega, hsp.2.2, ?_⟩
  omega

/-- The doubleword of `B + q` is `B`. -/
theorem key_eq {B : Word} (hB : B.toNat % 8 = 0) {q : Nat} (hq : q < 8) :
    (B + BitVec.ofNat 64 q) &&& 0xfffffffffffffff8 = B ∧ (B + BitVec.ofNat 64 q &&& 7).toNat = q := by
  have h := alignDown_add (p := B) (j := q) (by omega)
  refine ⟨?_, ?_⟩
  · rw [mask_eq, h.1]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_alignDown]; omega
  · rw [show (7 : Word) = 7#64 from rfl, toNat_and7, h.2]; omega

/-- A block that loads `w` bytes at `P` and stores them at `B + q`, in the aligned doubleword `B`:
that doubleword's bytes after. -/
theorem buf_update {u v : MachineState} {lk : LoadKind} {sk : StoreKind}
    (hwid : lk.width = sk.width) {B P : Word} {q : Nat} (hB : B.toNat % 8 = 0) (hq8 : q < 8)
    (hq : (B + BitVec.ofNat 64 q).toNat % sk.width = 0) (hP : P.toNat % sk.width = 0)
    (hm : v.getMem ((B + BitVec.ofNat 64 q) &&& 0xfffffffffffffff8) =
      sk.merge (u.getMem ((B + BitVec.ofNat 64 q) &&& 0xfffffffffffffff8))
        (B + BitVec.ofNat 64 q &&& 7).toNat
        (lk.fromWord (u.getMem (P &&& 0xfffffffffffffff8)) (P &&& 7).toNat))
    {i : Nat} (hi : i < 8) :
    extractByte (v.getMem B) i = if q ≤ i ∧ i < q + sk.width then
      byteAt u (P + BitVec.ofNat 64 (i - q)) else extractByte (u.getMem B) i := by
  have hk := key_eq hB hq8
  have h8 := (alignDown_add (p := B) (j := q) (by omega)).2
  rw [hk.1] at hm
  rw [hm, extractByte_copy lk sk u _ hwid hP hq hi, h8, show (B.toNat + q) % 8 = q by omega]

/-- `addiw r, r, 2` on a small `r`. -/
theorem addw2 {p : Nat} (hp : p < 8) :
    (wordResult .add ((BitVec.ofNat 64 p).truncate 32) ((2 : Word).truncate 32)).signExtend 64 =
      BitVec.ofNat 64 (p + 2) := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨
    p = 5 ∨ p = 6 ∨ p = 7 := by omega
  all_goals decide

/-- The shift amounts: `8a` and `64 - 8a`. -/
theorem shamt_of {a : Nat} (h1 : 0 < a) (h8 : a < 8) :
    (BitVec.ofNat 64 a <<< ((3 : Word).toNat % 64)).toNat % 64 = 8 * a ∧
      ((0 - BitVec.ofNat 64 a <<< ((3 : Word).toNat % 64)) &&& (56 : Word)).toNat % 64 =
        64 - 8 * a := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
    a = 6 ∨ a = 7 := by omega
  all_goals decide

/-- `wd` more source bytes from `S + p` put in the buffer `B` at `a + p`. -/
theorem buf_step {u v : MachineState} {B P S : Word} {a p q wd : Nat} (hq : q = a + p)
    (hP : ∀ j < wd, byteAt u (P + BitVec.ofNat 64 j) = byteAt s (S + BitVec.ofNat 64 (p + j)))
    (hold : ∀ i, a ≤ i → i < a + p →
      extractByte (u.getMem B) i = byteAt s (S + BitVec.ofNat 64 (i - a)))
    (hb : ∀ i < 8, extractByte (v.getMem B) i = if q ≤ i ∧ i < q + wd then
      byteAt u (P + BitVec.ofNat 64 (i - q)) else extractByte (u.getMem B) i)
    (h8 : a + p + wd ≤ 8) :
    ∀ i, a ≤ i → i < a + (p + wd) →
      extractByte (v.getMem B) i = byteAt s (S + BitVec.ofNat 64 (i - a)) := by
  intro i h1 h2
  rw [hb i (by omega)]
  by_cases hin : q ≤ i ∧ i < q + wd
  · rw [ite_eq_left hin, hP _ (by omega)]
    congr 3
    omega
  · rw [ite_eq_right hin]
    exact hold i h1 (by omega)

/-! ## The first buffer fill -/

/-- The registers the shifting path keeps throughout. -/
def shR : List Reg := [.x2, .x11, .x12, .x13, .x14, .x15, .x16] ++ keepC

/-- In the first buffer fill, from the shifting path's entry `w`: `p` of the source's next
`8 - a` bytes in the buffer `sp - 8`, from its byte `a` on. -/
structure PL (s w u : MachineState) (h a p : Nat) : Prop where
  x5 : u.getReg .x5 = s.getReg .x2 - 8 + BitVec.ofNat 64 a
  keep : ∀ r ∈ shR, u.getReg r = w.getReg r
  copied : Copied s u h
  buf : ∀ i, a ≤ i → i < a + p → extractByte (u.getMem (s.getReg .x2 - 8)) i =
    byteAt s (s.getReg .x11 + BitVec.ofNat 64 h + BitVec.ofNat 64 (i - a))

/-- The common facts of the shifting path. -/
structure ShCtx (C : FwdCode) (s w : MachineState) (h a : Nat) : Prop where
  pre : FwdPre s
  atSh : AtSh C s w h
  ha : a = ((s.getReg .x11).toNat + h) % 8

theorem ShCtx.bounds {C : FwdCode} {w : MachineState} {h a : Nat} (hx : ShCtx C s w h a) :
    0 < a ∧ a < 8 ∧ h < 8 ∧ 16 ≤ (s.getReg .x12).toNat ∧
      (s.getReg .x2 - 8).toNat % 8 = 0 := by
  have := hx.atSh.als
  have := hx.atSh.hh
  have := hx.atSh.n16
  have := hx.ha
  have hb := hx.pre.buf
  omega

/-- A source byte at `src + h + j`, `j < 8`, not yet copied, is the initial one. -/
theorem PL.src {C : FwdCode} {w u : MachineState} {h a p : Nat} (hx : ShCtx C s w h a)
    (hu : PL s w u h a p) {j : Nat} (hj : j < 8) :
    byteAt u (s.getReg .x11 + BitVec.ofNat 64 h + BitVec.ofNat 64 j) =
      byteAt s (s.getReg .x11 + BitVec.ofNat 64 h + BitVec.ofNat 64 j) := by
  have hb := hx.bounds
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hu.copied.src hx.pre (by omega) (by omega)

theorem pb_step {C : FwdCode} (hC : C.Ok) {w : MachineState} {h a : Nat} (hx : ShCtx C s w h a)
    {u : MachineState} (hpc : u.pc = C.pb) (hu : PL s w u h a 0) :
    ∃ v, Reaches Image.code u v ∧ PL s w v h a 1 ∧ v.getReg .x17 = 1 ∧
      v.getReg .x6 = u.getReg .x6 ∧ ((u.getReg .x6 &&& 2) = 0 → v.pc = C.pt4) ∧
      ((u.getReg .x6 &&& 2) ≠ 0 → v.pc = C.ph) := by
  have hb := hx.bounds
  have hB := hx.pre.buf
  have hsm := hx.pre.src
  simp only [Mapped] at hsm
  have hx11 : u.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 h :=
    (hu.keep .x11 (by decide)).trans hx.atSh.x11
  have ha := hx.ha
  obtain ⟨v, hr, hv⟩ := hC.pb.reaches hpc (by
    simp only [pbE, Oblig.all, Oblig.holds, Addr.eval, E.eval, add_zero_lit, hu.x5, hx11]
    exact ⟨valid_of (by decide) (by addr_omega [hB, hb]) (Nat.mod_one _),
      valid_of (by decide) (by addr_omega [hsm, hb]) (Nat.mod_one _)⟩)
  have k := keepOf hv rfl (.x5 :: .x6 :: shR)
  have hm := memOf hv rfl
  have e17 := hv.reg .x17 rfl
  blk at hm e17
  rw [hu.x5] at hm
  have hbuf := fun i (hi : i < 8) ↦ buf_update (lk := .bu) (sk := .b) rfl hb.2.2.2.2 (q := a)
    (by omega) (Nat.mod_one _) (Nat.mod_one _) hm hi
  have hf (x : Word) (hx' : x ≠ s.getReg .x2 - 8) : v.getMem x = u.getMem x :=
    frameOf hv rfl x (by blk; rw [hu.x5, (key_eq hb.2.2.2.2 hb.2.1).1]; exact hx')
  refine ⟨v, hr, ⟨by rw [k .x5 (by decide), hu.x5], fun r hr ↦ (k r (by simp [hr])).trans
    (hu.keep r hr), hu.copied.stack hx.pre (by omega) hb.2.2.2.2 (by omega) (by omega) hf, ?_⟩,
    e17, k .x6 (by decide), fun hc ↦ pcT hv rfl (by cond; exact hc),
    fun hc ↦ pcF hv rfl (by cond; exact hc)⟩
  refine buf_step (p := 0) (by omega) (fun j hj ↦ ?_) hu.buf hbuf (by simp [StoreKind.width]; omega)
  rw [hx11, show j = 0 by simp [StoreKind.width] at hj; omega]
  exact hu.src hx (by omega)

theorem ph_step {C : FwdCode} (hC : C.Ok) {w : MachineState} {h a p : Nat} (hx : ShCtx C s w h a)
    {u : MachineState} (hpc : u.pc = C.ph) (hu : PL s w u h a p)
    (h17 : u.getReg .x17 = BitVec.ofNat 64 p) (hal : (a + p) % 2 = 0) (h8 : a + p + 2 ≤ 8) :
    ∃ v, Reaches Image.code u v ∧ PL s w v h a (p + 2) ∧
      v.getReg .x17 = BitVec.ofNat 64 (p + 2) ∧ v.getReg .x6 = u.getReg .x6 &&& 4 ∧
      ((u.getReg .x6 &&& 4) ≠ 0 → v.pc = C.pw) ∧ ((u.getReg .x6 &&& 4) = 0 → v.pc = C.pj) := by
  have hb := hx.bounds
  have hB := hx.pre.buf
  have hsm := hx.pre.src
  simp only [Mapped] at hsm
  have hx11 : u.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 h :=
    (hu.keep .x11 (by decide)).trans hx.atSh.x11
  have ha := hx.ha
  have hq : u.getReg .x5 + u.getReg .x17 = s.getReg .x2 - 8 + BitVec.ofNat 64 (a + p) := by
    rw [hu.x5, h17, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hP : u.getReg .x11 + u.getReg .x17 =
      s.getReg .x11 + BitVec.ofNat 64 h + BitVec.ofNat 64 p := by rw [hx11, h17]
  obtain ⟨v, hr, hv⟩ := hC.ph.reaches hpc (by
    simp only [phE, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, add_zero_lit, hq, hP]
    exact ⟨valid_of (by decide) (by addr_omega [hB, hb, h8]) (by addr_omega [hB, hb, hal, h8]),
      valid_of (by decide) (by addr_omega [hsm, hb, h8]) (by addr_omega [hsm, hb, ha, hal, h8])⟩)
  have k := keepOf hv rfl (.x5 :: shR)
  have hm := memOf hv rfl
  have e17 := hv.reg .x17 rfl
  have e6 := hv.reg .x6 rfl
  blk at hm e17 e6
  rw [hq, hP] at hm
  have hbuf := fun i (hi : i < 8) ↦ buf_update (lk := .h) (sk := .h) rfl hb.2.2.2.2
    (q := a + p) (by omega) (by simp only [StoreKind.width]; addr_omega [hB, hb, hal, h8])
    (by simp only [StoreKind.width]; addr_omega [hsm, hb, ha, hal, h8]) hm hi
  have hf (x : Word) (hx' : x ≠ s.getReg .x2 - 8) : v.getMem x = u.getMem x :=
    frameOf hv rfl x (by blk; rw [hq, (key_eq hb.2.2.2.2 (by omega)).1]; exact hx')
  refine ⟨v, hr, ⟨by rw [k .x5 (by decide), hu.x5], fun r hr ↦ (k r (by simp [hr])).trans
    (hu.keep r hr), hu.copied.stack hx.pre (by omega) hb.2.2.2.2 (by omega) (by omega) hf, ?_⟩,
    by rw [e17, h17, addw2 (by omega)], e6, fun hc ↦ pcT hv rfl (by cond; exact hc),
    fun hc ↦ pcF hv rfl (by cond; exact hc)⟩
  refine buf_step (p := p) rfl (fun j hj ↦ ?_) hu.buf hbuf (by omega)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hu.src hx (by omega)

theorem pw_step {C : FwdCode} (hC : C.Ok) {w : MachineState} {h a p : Nat} (hx : ShCtx C s w h a)
    {u : MachineState} (hpc : u.pc = C.pw) (hu : PL s w u h a p)
    (h17 : u.getReg .x17 = BitVec.ofNat 64 p) (hal : (a + p) % 4 = 0) (h8 : a + p + 4 ≤ 8) :
    ∃ v, Reaches Image.code u v ∧ PL s w v h a (p + 4) ∧ v.pc = C.pe := by
  have hb := hx.bounds
  have hB := hx.pre.buf
  have hsm := hx.pre.src
  simp only [Mapped] at hsm
  have hx11 : u.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 h :=
    (hu.keep .x11 (by decide)).trans hx.atSh.x11
  have ha := hx.ha
  have hq : u.getReg .x5 + u.getReg .x17 = s.getReg .x2 - 8 + BitVec.ofNat 64 (a + p) := by
    rw [hu.x5, h17, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hP : u.getReg .x11 + u.getReg .x17 =
      s.getReg .x11 + BitVec.ofNat 64 h + BitVec.ofNat 64 p := by rw [hx11, h17]
  obtain ⟨v, hr, hv⟩ := hC.pw.reaches hpc (by
    simp only [pwE, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, add_zero_lit, hq, hP]
    exact ⟨valid_of (by decide) (by addr_omega [hB, hb, h8]) (by addr_omega [hB, hb, hal, h8]),
      valid_of (by decide) (by addr_omega [hsm, hb, h8]) (by addr_omega [hsm, hb, ha, hal, h8])⟩)
  have k := keepOf hv rfl (.x5 :: shR)
  have hm := memOf hv rfl
  blk at hm
  rw [hq, hP] at hm
  have hbuf := fun i (hi : i < 8) ↦ buf_update (lk := .w) (sk := .w) rfl hb.2.2.2.2
    (q := a + p) (by omega) (by simp only [StoreKind.width]; addr_omega [hB, hb, hal, h8])
    (by simp only [StoreKind.width]; addr_omega [hsm, hb, ha, hal, h8]) hm hi
  have hf (x : Word) (hx' : x ≠ s.getReg .x2 - 8) : v.getMem x = u.getMem x :=
    frameOf hv rfl x (by blk; rw [hq, (key_eq hb.2.2.2.2 (by omega)).1]; exact hx')
  refine ⟨v, hr, ⟨by rw [k .x5 (by decide), hu.x5], fun r hr ↦ (k r (by simp [hr])).trans
    (hu.keep r hr), hu.copied.stack hx.pre (by omega) hb.2.2.2.2 (by omega) (by omega) hf, ?_⟩,
    pcC hv rfl⟩
  refine buf_step (p := p) rfl (fun j hj ↦ ?_) hu.buf hbuf (by omega)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hu.src hx (by omega)

/-- A block that changes no register of the path's invariant and writes nothing. -/
theorem PL.of_same {w u v : MachineState} {h a p : Nat} (hu : PL s w u h a p)
    (hk : ∀ r ∈ Reg.x5 :: shR, v.getReg r = u.getReg r) (hm : ∀ x, v.getMem x = u.getMem x) :
    PL s w v h a p :=
  ⟨by rw [hk .x5 (by decide), hu.x5], fun r hr ↦ (hk r (by simp [hr])).trans (hu.keep r hr),
    hu.copied.same hm, fun i h1 h2 ↦ by rw [hm]; exact hu.buf i h1 h2⟩

theorem pt2_step {C : FwdCode} (hC : C.Ok) {w : MachineState} {h a p : Nat}
    {u : MachineState} (hpc : u.pc = C.pt2) (hu : PL s w u h a p) :
    ∃ v, Reaches Image.code u v ∧ PL s w v h a p ∧ v.getReg .x17 = u.getReg .x17 ∧
      v.getReg .x6 = u.getReg .x6 ∧ ((u.getReg .x6 &&& 2) ≠ 0 → v.pc = C.ph) ∧
      ((u.getReg .x6 &&& 2) = 0 → v.pc = C.pt4) := by
  obtain ⟨v, hr, hv⟩ := hC.pt2.reaches hpc trivial
  have k := keepOf hv rfl (.x5 :: .x6 :: .x17 :: shR)
  exact ⟨v, hr, hu.of_same (fun r hr ↦ k r (by simp at hr ⊢; tauto)) (sameOf hv rfl),
    k .x17 (by decide), k .x6 (by decide), fun hc ↦ pcT hv rfl (by cond; exact hc),
    fun hc ↦ pcF hv rfl (by cond; exact hc)⟩

theorem pt4_step {C : FwdCode} (hC : C.Ok) {w : MachineState} {h a p : Nat}
    {u : MachineState} (hpc : u.pc = C.pt4) (hu : PL s w u h a p) :
    ∃ v, Reaches Image.code u v ∧ PL s w v h a p ∧ v.getReg .x17 = u.getReg .x17 ∧
      ((u.getReg .x6 &&& 4) = 0 → v.pc = C.pe) ∧ ((u.getReg .x6 &&& 4) ≠ 0 → v.pc = C.pw) := by
  obtain ⟨v, hr, hv⟩ := hC.pt4.reaches hpc trivial
  have k := keepOf hv rfl (.x5 :: .x17 :: shR)
  exact ⟨v, hr, hu.of_same (fun r hr ↦ k r (by simp at hr ⊢; tauto)) (sameOf hv rfl),
    k .x17 (by decide),
    fun hc ↦ pcT hv rfl (by cond; exact hc), fun hc ↦ pcF hv rfl (by cond; exact hc)⟩

theorem pj_step {C : FwdCode} (hC : C.Ok) {w : MachineState} {h a p : Nat}
    {u : MachineState} (hpc : u.pc = C.pj) (hu : PL s w u h a p) :
    ∃ v, Reaches Image.code u v ∧ PL s w v h a p ∧ v.pc = C.pe := by
  obtain ⟨v, hr, hv⟩ := hC.pj.reaches hpc trivial
  exact ⟨v, hr, hu.of_same (keepOf hv rfl _) (sameOf hv rfl), pcC hv rfl⟩

theorem sh0_step {C : FwdCode} (hC : C.Ok) {w : MachineState} {h a : Nat}
    (hx : ShCtx C s w h a) :
    ∃ v, Reaches Image.code w v ∧ PL s w v h a 0 ∧ v.getReg .x17 = 0 ∧
      v.getReg .x6 = BitVec.ofNat 64 (8 - a) ∧
      ((BitVec.ofNat 64 (8 - a) &&& 1) ≠ 0 → v.pc = C.pb) ∧
      ((BitVec.ofNat 64 (8 - a) &&& 1) = 0 → v.pc = C.pt2) := by
  have hb := hx.bounds
  have hB := hx.pre.buf
  have ha := hx.ha
  have hw := hx.atSh
  have hx2 : w.getReg .x2 + 8 = s.getReg .x2 - 8 := by rw [hw.x2]; addr_omega [hB]
  have hx16 : w.getReg .x16 = BitVec.ofNat 64 a :=
    BitVec.eq_of_toNat_eq (by rw [hw.x16, BitVec.toNat_ofNat]; omega)
  obtain ⟨v, hr, hv⟩ := hC.sh0.reaches hw.pc (by
    simp only [sh0E, Oblig.all, Oblig.holds, Addr.eval, E.eval, hx2]
    exact valid_of (by decide) (by addr_omega [hB]) (by omega))
  have k := keepOf hv rfl shR
  have e5 := hv.reg .x5 rfl
  have e6 := hv.reg .x6 rfl
  have e17 := hv.reg .x17 rfl
  blk at e5 e6 e17
  have h6 : v.getReg .x6 = BitVec.ofNat 64 (8 - a) := by
    rw [e6, hx16]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [wordToNatLit]
    omega
  have hf (x : Word) (hx' : x ≠ s.getReg .x2 - 8) : v.getMem x = w.getMem x :=
    frameOf hv rfl x (by simp only [Addr.eval, E.eval, hx2]; exact hx')
  refine ⟨v, hr, ⟨?_, k, hw.copied.stack hx.pre (by omega) hb.2.2.2.2 (by omega) (by omega) hf,
    fun i h1 h2 ↦ by omega⟩, e17, h6, fun hc ↦ pcT hv rfl (by
      cond; rw [← e6, h6]; exact hc), fun hc ↦ pcF hv rfl (by
      cond; rw [← e6, h6]; exact hc)⟩
  rw [e5, hx2, or_eq_add hb.2.2.2.2 (by rw [hw.x16]; omega), hx16]

/-- The first buffer fill: from the shifting path's entry to `C.pe`, the source's next `8 - a`
bytes in the buffer. -/
theorem chain1 {C : FwdCode} (hC : C.Ok) {w : MachineState} {h a : Nat}
    (hx : ShCtx C s w h a) :
    ∃ v, Reaches Image.code w v ∧ PL s w v h a (8 - a) ∧ v.pc = C.pe := by
  have hb := hx.bounds
  obtain ⟨u₀, r₀, p₀, x17₀, x6₀, t₀, f₀⟩ := sh0_step hC hx
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
    a = 6 ∨ a = 7 := by omega
  · obtain ⟨u₁, r₁, p₁, x17₁, x6₁, -, f₁⟩ := pb_step hC hx (t₀ (by decide)) p₀
    obtain ⟨u₂, r₂, p₂, x17₂, -, t₂, -⟩ := ph_step hC hx (f₁ (by rw [x6₀]; decide)) p₁ x17₁
      (by decide) (by decide)
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := pw_step hC hx (t₂ (by rw [x6₁, x6₀]; decide)) p₂ x17₂ (by decide)
      (by decide)
    exact ⟨u₃, r₀.trans (r₁.trans (r₂.trans r₃)), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, x17₁, x6₁, t₁, -⟩ := pt2_step hC (f₀ (by decide)) p₀
    obtain ⟨u₂, r₂, p₂, x17₂, -, t₂, -⟩ := ph_step hC hx (t₁ (by rw [x6₀]; decide)) p₁
      (by rw [x17₁, x17₀]; rfl) (by decide) (by decide)
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := pw_step hC hx (t₂ (by rw [x6₁, x6₀]; decide)) p₂ x17₂ (by decide)
      (by decide)
    exact ⟨u₃, r₀.trans (r₁.trans (r₂.trans r₃)), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, x17₁, x6₁, t₁, -⟩ := pb_step hC hx (t₀ (by decide)) p₀
    obtain ⟨u₂, r₂, p₂, x17₂, -, f₂⟩ := pt4_step hC (t₁ (by rw [x6₀]; decide)) p₁
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := pw_step hC hx (f₂ (by rw [x6₁, x6₀]; decide)) p₂
      (by rw [x17₂, x17₁]; rfl) (by decide) (by decide)
    exact ⟨u₃, r₀.trans (r₁.trans (r₂.trans r₃)), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, x17₁, x6₁, -, f₁⟩ := pt2_step hC (f₀ (by decide)) p₀
    obtain ⟨u₂, r₂, p₂, x17₂, -, f₂⟩ := pt4_step hC (f₁ (by rw [x6₀]; decide)) p₁
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := pw_step hC hx (f₂ (by rw [x6₁, x6₀]; decide)) p₂
      (by rw [x17₂, x17₁, x17₀]; rfl) (by decide) (by decide)
    exact ⟨u₃, r₀.trans (r₁.trans (r₂.trans r₃)), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, x17₁, x6₁, -, f₁⟩ := pb_step hC hx (t₀ (by decide)) p₀
    obtain ⟨u₂, r₂, p₂, -, x6₂, -, f₂⟩ := ph_step hC hx (f₁ (by rw [x6₀]; decide)) p₁ x17₁
      (by decide) (by decide)
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := pj_step hC (f₂ (by rw [x6₁, x6₀]; decide)) p₂
    exact ⟨u₃, r₀.trans (r₁.trans (r₂.trans r₃)), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, x17₁, x6₁, t₁, -⟩ := pt2_step hC (f₀ (by decide)) p₀
    obtain ⟨u₂, r₂, p₂, -, -, -, f₂⟩ := ph_step hC hx (t₁ (by rw [x6₀]; decide)) p₁
      (by rw [x17₁, x17₀]; rfl) (by decide) (by decide)
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := pj_step hC (f₂ (by rw [x6₁, x6₀]; decide)) p₂
    exact ⟨u₃, r₀.trans (r₁.trans (r₂.trans r₃)), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, -, x6₁, t₁, -⟩ := pb_step hC hx (t₀ (by decide)) p₀
    obtain ⟨u₂, r₂, p₂, -, t₂, -⟩ := pt4_step hC (t₁ (by rw [x6₀]; decide)) p₁
    exact ⟨u₂, r₀.trans (r₁.trans r₂), p₂, t₂ (by rw [x6₁, x6₀]; decide)⟩

/-! ## Doublewords shifted together -/

/-- The registers the loop keeps. -/
def shR2 : List Reg := [.x2, .x11, .x12, .x13, .x15, .x16] ++ keepC

/-- After `j` destination doublewords: `x5` holds the source's doubleword from which the next
one's first `8 - a` bytes come, at its bytes `a` on; `x7` is that doubleword's address. -/
structure LI (s w u : MachineState) (h a j : Nat) : Prop where
  x14 : u.getReg .x14 = s.getReg .x10 + BitVec.ofNat 64 (h + 8 * j)
  x7 : u.getReg .x7 = s.getReg .x11 + BitVec.ofNat 64 (h + 8 * j) - BitVec.ofNat 64 a
  x17 : u.getReg .x17 = w.getReg .x16 <<< ((3 : Word).toNat % 64)
  x5 : ∀ i, a ≤ i → i < 8 → extractByte (u.getReg .x5) i =
    byteAt s (s.getReg .x11 + BitVec.ofNat 64 (h + 8 * j + (i - a)))
  keep : ∀ r ∈ shR2, u.getReg r = w.getReg r
  copied : Copied s u (h + 8 * j)

theorem ShCtx.x16 {C : FwdCode} {w : MachineState} {h a : Nat} (hx : ShCtx C s w h a) :
    w.getReg .x16 = BitVec.ofNat 64 a :=
  BitVec.eq_of_toNat_eq (by rw [hx.atSh.x16, BitVec.toNat_ofNat]; have := hx.ha; omega)

theorem ShCtx.shamt {C : FwdCode} {w : MachineState} {h a : Nat} (hx : ShCtx C s w h a) :
    (w.getReg .x16 <<< ((3 : Word).toNat % 64)).toNat % 64 = 8 * a ∧
      ((0 - w.getReg .x16 <<< ((3 : Word).toNat % 64)) &&& (56 : Word)).toNat % 64 = 64 - 8 * a := by
  have hb := hx.bounds
  rw [hx.x16]
  exact shamt_of hb.1 hb.2.1

theorem pe_step {C : FwdCode} (hC : C.Ok) {w : MachineState} {h a : Nat} (hx : ShCtx C s w h a)
    {u : MachineState} (hpc : u.pc = C.pe) (hu : PL s w u h a (8 - a)) :
    ∃ v, Reaches Image.code u v ∧ LI s w v h a 0 ∧
      ((s.getReg .x12).toNat - h < 16 → v.pc = C.after) ∧
      (16 ≤ (s.getReg .x12).toNat - h → v.pc = C.lpre) := by
  have hb := hx.bounds
  have hB := hx.pre.buf
  have hdm := hx.pre.dst
  have hsm := hx.pre.src
  simp only [Mapped] at hdm hsm
  have hw := hx.atSh
  have hx2 : u.getReg .x2 + 8 = s.getReg .x2 - 8 := by
    rw [hu.keep .x2 (by decide), hw.x2]; addr_omega [hB]
  obtain ⟨v, hr, hv⟩ := hC.pe.reaches hpc (by
    simp only [peE, Oblig.all, Oblig.holds, Addr.eval, E.eval, hx2]
    exact valid_of (by decide) (by addr_omega [hB]) (by omega))
  have k := keepOf hv rfl (.x14 :: shR2)
  have e5 := hv.reg .x5 rfl
  have e7 := hv.reg .x7 rfl
  have e17 := hv.reg .x17 rfl
  blk at e5 e7 e17
  rw [hx2] at e5
  have hx14 : u.getReg .x14 = s.getReg .x10 + BitVec.ofNat 64 h :=
    (hu.keep .x14 (by decide)).trans hw.x14
  have hx13 : (u.getReg .x13).toNat =
      (s.getReg .x10).toNat + h + 8 * (((s.getReg .x12).toNat - h) / 8) :=
    by rw [hu.keep .x13 (by decide), hw.x13]
  have hk2 : ∀ r ∈ shR2, v.getReg r = w.getReg r := fun r hr ↦
    (k r (List.mem_cons_of_mem _ hr)).trans (hu.keep r (by simp [shR, shR2] at hr ⊢; tauto))
  refine ⟨v, hr, ⟨by rw [k .x14 (by decide), hx14]; simp, ?_, ?_, fun i h1 h2 ↦ ?_, hk2,
    hu.copied.same (sameOf hv rfl)⟩, fun hc ↦ pcT hv rfl ?_, fun hc ↦ pcF hv rfl ?_⟩
  · rw [e7, hu.keep .x11 (by decide), hu.keep .x16 (by decide), hw.x11, hx.x16]; simp
  · rw [e17, hu.keep .x16 (by decide)]
  · rw [e5, hu.buf i h1 (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
    simp
  · cond; rw [hx14, hx13]; addr_omega [hdm, hb, hc]
  · cond; rw [hx14, hx13]; addr_omega [hdm, hb, hc]

/-- One doubleword of the loop at `C.loop`. -/
theorem loop_body {C : FwdCode} (hC : C.Ok) {w : MachineState} {h a : Nat}
    (hx : ShCtx C s w h a) (u : MachineState)
    (hu : ∃ j, u.pc = C.loop ∧ LI s w u h a j ∧ u.getReg .x6 = (0 - u.getReg .x17) &&& 56 ∧
      h + 8 * j + 16 ≤ (s.getReg .x12).toNat) :
    (∃ v, Reaches Image.code u v ∧ v.pc = C.after ∧
      LI s w v h a (((s.getReg .x12).toNat - h) / 8 - 1)) ∨
    (∃ v, Reaches Image.code u v ∧ (∃ j, v.pc = C.loop ∧ LI s w v h a j ∧
      v.getReg .x6 = (0 - v.getReg .x17) &&& 56 ∧ h + 8 * j + 16 ≤ (s.getReg .x12).toNat) ∧
      (v.getReg .x13).toNat - (v.getReg .x14).toNat <
        (u.getReg .x13).toNat - (u.getReg .x14).toNat) := by
  obtain ⟨j, hpc, hj, hx6, hlt⟩ := hu
  have hb := hx.bounds
  have hdm := hx.pre.dst
  have hsm := hx.pre.src
  simp only [Mapped] at hdm hsm
  have ha := hx.ha
  have hw := hx.atSh
  have hx7 := hj.x7
  have hx14 := hj.x14
  have hx13 : (u.getReg .x13).toNat =
      (s.getReg .x10).toNat + h + 8 * (((s.getReg .x12).toNat - h) / 8) := by
    rw [hj.keep .x13 (by decide), hw.x13]
  have hald := hw.ald
  have hS : u.getReg .x7 + 8 =
      s.getReg .x11 + BitVec.ofNat 64 (h + 8 * (j + 1) - a) := by
    rw [hx7]; addr_omega [hsm, hb, hlt]
  have hS8 : (s.getReg .x11 + BitVec.ofNat 64 (h + 8 * (j + 1) - a)).toNat % 8 = 0 := by
    addr_omega [hsm, hb, hlt, ha]
  have hD8 : (s.getReg .x10 + BitVec.ofNat 64 (h + 8 * j)).toNat % 8 = 0 := by
    addr_omega [hdm, hb, hlt, hald]
  obtain ⟨v, hr, hv⟩ := hC.loop.reaches hpc (by
    simp only [loopE, Oblig.all, Oblig.holds, Addr.eval, E.eval, add_zero_lit, hx14, hS]
    exact ⟨valid_of (by decide) (by addr_omega [hdm, hb, hlt]) hD8,
      valid_of (by decide) (by addr_omega [hsm, hb, hlt]) hS8⟩)
  have k := keepOf hv rfl (.x6 :: .x17 :: shR2)
  have hm := memOf hv rfl
  have e5 := hv.reg .x5 rfl
  have e7 := hv.reg .x7 rfl
  have e14 := hv.reg .x14 rfl
  blk at hm e5 e7 e14
  have hsh := hx.shamt
  rw [← hj.x17, ← hx6] at hsh
  rw [hS, hsh.1, hsh.2, BitVec.or_comm, hx14] at hm
  rw [hS] at e5
  -- the source doubleword just loaded, byte by byte
  have hM (i : Nat) (hi : i < 8) : extractByte (u.getMem (s.getReg .x11 +
      BitVec.ofNat 64 (h + 8 * (j + 1) - a))) i =
      byteAt s (s.getReg .x11 + BitVec.ofNat 64 (h + 8 * (j + 1) - a + i)) := by
    rw [← byteAt_add hS8 hi, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hj.copied.src hx.pre (by omega) (by omega)
  have hcp : Copied s v (h + 8 * j + 8) := by
    refine hj.copied.extend hx.pre (by omega) (ByteFrame.of_single hD8 fun x hx' ↦
      frameOf hv rfl x (by simp only [Addr.eval, E.eval, add_zero_lit, hx14]; exact hx'))
      fun i hi ↦ ?_
    rw [show s.getReg .x10 + BitVec.ofNat 64 (h + 8 * j + i) =
      s.getReg .x10 + BitVec.ofNat 64 (h + 8 * j) + BitVec.ofNat 64 i by
        rw [BitVec.ofNat_add, BitVec.add_assoc], byteAt_add hD8 hi, hm,
      extractByte_shift _ _ hb.1 hb.2.1 hi]
    split
    · rw [hj.x5 (i + a) (by omega) (by omega)]
      congr 3
      omega
    · rw [hM _ (by omega)]
      congr 3
      omega
  have hk2 : ∀ r ∈ shR2, v.getReg r = w.getReg r :=
    fun r hr ↦ (k r (by simp [hr])).trans (hj.keep r hr)
  have hli : LI s w v h a (j + 1) := {
    x14 := by rw [e14, hx14]; addr_omega [hdm, hb, hlt]
    x7 := by rw [e7, hx7]; addr_omega [hsm, hb, hlt]
    x17 := (k .x17 (by decide)).trans hj.x17
    x5 := fun i h1 h2 ↦ by
      rw [e5, hM i h2]
      congr 3
      omega
    keep := hk2
    copied := by rw [show h + 8 * (j + 1) = h + 8 * j + 8 by omega]; exact hcp }
  have hx13v : v.getReg .x13 = u.getReg .x13 := k .x13 (by decide)
  by_cases hlast : h + 8 * (j + 1) + 16 ≤ (s.getReg .x12).toNat
  · refine Or.inr ⟨v, hr, ⟨j + 1, pcT hv rfl ?_, hli, ?_, hlast⟩, ?_⟩
    · cond; rw [hx14, hx13]; addr_omega [hdm, hb, hlt, hlast]
    · rw [k .x6 (by decide), k .x17 (by decide), hx6]
    · rw [hx13v, hli.x14, hx14]; addr_omega [hdm, hb, hlt, hx13, hlast]
  · refine Or.inl ⟨v, hr, pcF hv rfl ?_, ?_⟩
    · cond; rw [hx14, hx13]; addr_omega [hdm, hb, hlt, hlast]
    · rw [show ((s.getReg .x12).toNat - h) / 8 - 1 = j + 1 by omega]; exact hli

theorem lpre_step {C : FwdCode} (hC : C.Ok) {w : MachineState} {h a : Nat} {u : MachineState}
    (hpc : u.pc = C.lpre) (hu : LI s w u h a 0) :
    ∃ v, Reaches Image.code u v ∧ v.pc = C.loop ∧ LI s w v h a 0 ∧
      v.getReg .x6 = (0 - v.getReg .x17) &&& 56 := by
  obtain ⟨v, hr, hv⟩ := hC.lpre.reaches hpc trivial
  have k := keepOf hv rfl (.x5 :: .x7 :: .x14 :: .x17 :: shR2)
  have e6 := hv.reg .x6 rfl
  blk at e6
  have hm := sameOf hv rfl
  refine ⟨v, hr, pcC hv rfl, ⟨by rw [k .x14 (by decide), hu.x14], by rw [k .x7 (by decide), hu.x7],
    by rw [k .x17 (by decide), hu.x17], fun i h1 h2 ↦ by rw [k .x5 (by decide), hu.x5 i h1 h2],
    fun r hr ↦ (k r (by simp [hr])).trans (hu.keep r hr), hu.copied.same hm⟩, ?_⟩
  rw [e6, k .x17 (by decide)]

/-! ## The last doubleword -/

def shR3 : List Reg := [.x2, .x11, .x12, .x13, .x15] ++ keepC

/-- In the second buffer fill, `J` destination doublewords in all: the last one's first `8 - a`
bytes in `x5` from byte `a` on, and `q` bytes of the source's doubleword at `S2` in the buffer. -/
structure QL (s w u : MachineState) (h a J q : Nat) : Prop where
  x14 : u.getReg .x14 = s.getReg .x10 + BitVec.ofNat 64 (h + 8 * (J - 1))
  x17 : u.getReg .x17 = w.getReg .x16 <<< ((3 : Word).toNat % 64)
  x5 : ∀ i, a ≤ i → i < 8 → extractByte (u.getReg .x5) i =
    byteAt s (s.getReg .x11 + BitVec.ofNat 64 (h + 8 * (J - 1) + (i - a)))
  keep : ∀ r ∈ shR3, u.getReg r = w.getReg r
  copied : Copied s u (h + 8 * (J - 1))
  buf : ∀ i < q, extractByte (u.getMem (s.getReg .x2 - 8)) i =
    byteAt s (s.getReg .x11 + BitVec.ofNat 64 (h + 8 * J - a) + BitVec.ofNat 64 i)

/-- `x &&& c` for `c` within the low three bits, from `x`'s byte position. -/
theorem and_low {x : Word} {a : Nat} (ha : x.toNat % 8 = a) {c : Word} (hc : 7 &&& c = c) :
    x &&& c = BitVec.ofNat 64 a &&& c := by
  rw [← hc, ← BitVec.and_assoc, ← BitVec.and_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [show (7 : Word) = 7#64 from rfl, toNat_and7, toNat_and7, ha, BitVec.toNat_ofNat]
  omega

theorem ShCtx.x11 {C : FwdCode} {w : MachineState} {h a : Nat} (hx : ShCtx C s w h a) :
    (w.getReg .x11).toNat % 8 = a := by
  have hsm := hx.pre.src
  simp only [Mapped] at hsm
  rw [hx.atSh.x11, hx.ha, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := hx.atSh.hh
  omega

theorem after_step {C : FwdCode} (hC : C.Ok) {w : MachineState} {h a : Nat}
    (hx : ShCtx C s w h a) {u : MachineState} (hpc : u.pc = C.after)
    (hu : LI s w u h a (((s.getReg .x12).toNat - h) / 8 - 1)) :
    ∃ v, Reaches Image.code u v ∧ QL s w v h a (((s.getReg .x12).toNat - h) / 8) 0 ∧
      v.getReg .x7 = s.getReg .x11 + BitVec.ofNat 64 (h + 8 * (((s.getReg .x12).toNat - h) / 8) - a) ∧
      v.getReg .x6 = 0 ∧ (4 ≤ a → v.pc = C.qw) ∧ (a < 4 → v.pc = C.qt2) := by
  have hb := hx.bounds
  have hB := hx.pre.buf
  have hsm := hx.pre.src
  simp only [Mapped] at hsm
  have hw := hx.atSh
  have hx2 : u.getReg .x2 + 8 = s.getReg .x2 - 8 := by
    rw [hu.keep .x2 (by decide), hw.x2]; addr_omega [hB]
  obtain ⟨v, hr, hv⟩ := hC.after.reaches hpc (by
    simp only [afterE, Oblig.all, Oblig.holds, Addr.eval, E.eval, hx2]
    exact valid_of (by decide) (by addr_omega [hB]) (by omega))
  have k := keepOf hv rfl (.x5 :: .x14 :: .x17 :: shR2)
  have e6 := hv.reg .x6 rfl
  have e7 := hv.reg .x7 rfl
  blk at e6 e7
  have hf (x : Word) (hx' : x ≠ s.getReg .x2 - 8) : v.getMem x = u.getMem x :=
    frameOf hv rfl x (by simp only [Addr.eval, E.eval, hx2]; exact hx')
  have hx16 : u.getReg .x16 = BitVec.ofNat 64 a := (hu.keep .x16 (by decide)).trans hx.x16
  have hk3 : ∀ r ∈ shR3, v.getReg r = w.getReg r := fun r hr ↦
    (k r (by simp [shR3, shR2] at hr ⊢; tauto)).trans (hu.keep r (by simp [shR3, shR2] at hr ⊢; tauto))
  refine ⟨v, hr, ⟨by rw [k .x14 (by decide), hu.x14], by rw [k .x17 (by decide), hu.x17],
    fun i h1 h2 ↦ by rw [k .x5 (by decide), hu.x5 i h1 h2], hk3, hu.copied.stack hx.pre (by omega) hb.2.2.2.2 (by omega) (by omega) hf,
    fun i hi ↦ absurd hi (Nat.not_lt_zero _)⟩, ?_, e6, fun hc ↦ pcT hv rfl ?_,
    fun hc ↦ pcF hv rfl ?_⟩
  · rw [e7, hu.x7]; addr_omega [hsm, hb]
  · cond; rw [hx16]; simp only [BitVec.toNat_ofNat]; omega
  · cond; rw [hx16]; simp only [BitVec.toNat_ofNat]; omega

/-- The common facts of the second buffer fill. -/
structure QCtx (C : FwdCode) (s w : MachineState) (h a J : Nat) : Prop extends ShCtx C s w h a where
  hJ : J = ((s.getReg .x12).toNat - h) / 8

theorem QCtx.bounds {C : FwdCode} {w : MachineState} {h a J : Nat} (hx : QCtx C s w h a J) :
    1 ≤ J ∧ h + 8 * J ≤ (s.getReg .x12).toNat := by
  have := hx.hJ
  have := hx.toShCtx.bounds
  omega

/-- A source byte of the doubleword at `S2` before its byte `a` is the initial one. -/
theorem QL.src {C : FwdCode} {w u : MachineState} {h a J q : Nat} (hx : QCtx C s w h a J)
    (hu : QL s w u h a J q) {i : Nat} (hi : i < a) :
    byteAt u (s.getReg .x11 + BitVec.ofNat 64 (h + 8 * J - a) + BitVec.ofNat 64 i) =
      byteAt s (s.getReg .x11 + BitVec.ofNat 64 (h + 8 * J - a) + BitVec.ofNat 64 i) := by
  have hb := hx.toShCtx.bounds
  have hJ := hx.bounds
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hu.copied.src hx.pre (by omega) (by omega)

theorem QL.of_same {w u v : MachineState} {h a J q : Nat} (hu : QL s w u h a J q)
    (hk : ∀ r ∈ Reg.x5 :: Reg.x14 :: Reg.x17 :: shR3, v.getReg r = u.getReg r)
    (hm : ∀ x, v.getMem x = u.getMem x) : QL s w v h a J q :=
  ⟨by rw [hk .x14 (by decide), hu.x14], by rw [hk .x17 (by decide), hu.x17],
    fun i h1 h2 ↦ by rw [hk .x5 (by decide), hu.x5 i h1 h2],
    fun r hr ↦ (hk r (by simp [hr])).trans (hu.keep r hr), hu.copied.same hm,
    fun i hi ↦ by rw [hm]; exact hu.buf i hi⟩

/-- A store of `wd` source bytes from `S2 + q` at the buffer's byte `q`: the buffer after. -/
theorem QL.step {C : FwdCode} {w u v : MachineState} {h a J q wd : Nat} (hx : QCtx C s w h a J)
    (hu : QL s w u h a J q) (hq : q + wd ≤ a)
    (hk : ∀ r ∈ Reg.x5 :: Reg.x14 :: Reg.x17 :: shR3, v.getReg r = u.getReg r)
    (hf : ∀ x, x ≠ s.getReg .x2 - 8 → v.getMem x = u.getMem x)
    (hb : ∀ i < 8, extractByte (v.getMem (s.getReg .x2 - 8)) i = if q ≤ i ∧ i < q + wd then
      byteAt u (s.getReg .x11 + BitVec.ofNat 64 (h + 8 * J - a) + BitVec.ofNat 64 q +
        BitVec.ofNat 64 (i - q)) else extractByte (u.getMem (s.getReg .x2 - 8)) i) :
    QL s w v h a J (q + wd) := by
  have hb' := hx.toShCtx.bounds
  have hJ := hx.bounds
  refine ⟨by rw [hk .x14 (by decide), hu.x14], by rw [hk .x17 (by decide), hu.x17],
    fun i h1 h2 ↦ by rw [hk .x5 (by decide), hu.x5 i h1 h2],
    fun r hr ↦ (hk r (by simp [hr])).trans (hu.keep r hr),
    hu.copied.stack hx.pre (by omega) hb'.2.2.2.2 (by have := hx.pre.buf; omega)
      (by have := hx.pre.buf; omega) hf, fun i hi ↦ ?_⟩
  have := buf_step (s := s) (a := 0) (p := q) (q := q) (wd := wd) (by omega)
    (S := s.getReg .x11 + BitVec.ofNat 64 (h + 8 * J - a)) (fun j hj ↦ by
      rw [BitVec.add_assoc (s.getReg .x11 + _), ← BitVec.ofNat_add]
      exact hu.src hx (by omega))
    (fun i _ h2 ↦ by rw [Nat.sub_zero]; exact hu.buf i (by omega)) hb (by omega) i (Nat.zero_le _)
    (by omega)
  rwa [Nat.sub_zero] at this

theorem qw_step {C : FwdCode} (hC : C.Ok) {w : MachineState} {h a J : Nat}
    (hx : QCtx C s w h a J) {u : MachineState} (hpc : u.pc = C.qw) (hu : QL s w u h a J 0)
    (h7 : u.getReg .x7 = s.getReg .x11 + BitVec.ofNat 64 (h + 8 * J - a)) (h4 : 4 ≤ a) :
    ∃ v, Reaches Image.code u v ∧ QL s w v h a J 4 ∧ v.getReg .x7 = u.getReg .x7 ∧
      v.getReg .x6 = 4 ∧ ((w.getReg .x11 &&& 2) = 0 → v.pc = C.qt1) ∧
      ((w.getReg .x11 &&& 2) ≠ 0 → v.pc = C.qh) := by
  have hb := hx.toShCtx.bounds
  have hJ := hx.bounds
  have hB := hx.pre.buf
  have hsm := hx.pre.src
  simp only [Mapped] at hsm
  have ha := hx.ha
  have hx2 : u.getReg .x2 + 8 = s.getReg .x2 - 8 + BitVec.ofNat 64 0 := by
    rw [hu.keep .x2 (by decide), hx.atSh.x2]; addr_omega [hB]
  obtain ⟨v, hr, hv⟩ := hC.qw.reaches hpc (by
    simp only [qwE, Oblig.all, Oblig.holds, Addr.eval, E.eval, add_zero_lit, hx2, h7]
    exact ⟨valid_of (by decide) (by addr_omega [hB]) (by addr_omega [hB]),
      valid_of (by decide) (by addr_omega [hsm, hb, hJ, h4]) (by addr_omega [hsm, hb, hJ, ha])⟩)
  have k := keepOf hv rfl (.x5 :: .x7 :: .x14 :: .x17 :: shR3)
  have hm := memOf hv rfl
  have e6 := hv.reg .x6 rfl
  blk at hm e6
  rw [hx2] at hm
  have hbuf := fun i (hi : i < 8) ↦ buf_update (lk := .w) (sk := .w) rfl hb.2.2.2.2
    (q := 0) (by omega) (by simp only [StoreKind.width]; addr_omega [hB])
    (by simp only [StoreKind.width]; rw [h7]; addr_omega [hsm, hb, hJ, ha]) hm hi
  have hf (x : Word) (hx' : x ≠ s.getReg .x2 - 8) : v.getMem x = u.getMem x :=
    frameOf hv rfl x (by
      simp only [Addr.eval, E.eval, BinOp.eval, add_zero_lit, hx2, (key_eq (q := 0) hb.2.2.2.2 (by omega)).1]
      exact hx')
  have hx11 : u.getReg .x11 = w.getReg .x11 := hu.keep .x11 (by decide)
  refine ⟨v, hr, hu.step (q := 0) (wd := 4) hx (by omega) (fun r hr ↦ k r (by simp at hr ⊢; tauto)) hf
    (fun i hi ↦ ?_), k .x7 (by decide), e6, fun hc ↦ pcT hv rfl (by cond; rw [hx11]; exact hc),
    fun hc ↦ pcF hv rfl (by cond; rw [hx11]; exact hc)⟩
  rw [hbuf i hi, h7, BitVec.add_zero]
  rfl

theorem qh_step {C : FwdCode} (hC : C.Ok) {w : MachineState} {h a J q : Nat}
    (hx : QCtx C s w h a J) {u : MachineState} (hpc : u.pc = C.qh) (hu : QL s w u h a J q)
    (h7 : u.getReg .x7 = s.getReg .x11 + BitVec.ofNat 64 (h + 8 * J - a))
    (h6 : u.getReg .x6 = BitVec.ofNat 64 q) (hal : q % 2 = 0) (h8 : q + 2 ≤ a) :
    ∃ v, Reaches Image.code u v ∧ QL s w v h a J (q + 2) ∧ v.getReg .x7 = u.getReg .x7 ∧
      v.getReg .x6 = BitVec.ofNat 64 (q + 2) ∧ ((w.getReg .x11 &&& 1) ≠ 0 → v.pc = C.qb) ∧
      ((w.getReg .x11 &&& 1) = 0 → v.pc = C.qj) := by
  have hb := hx.toShCtx.bounds
  have hJ := hx.bounds
  have hB := hx.pre.buf
  have hsm := hx.pre.src
  simp only [Mapped] at hsm
  have ha := hx.ha
  have hQ : (u.getReg .x2 + 8 ||| u.getReg .x6) = s.getReg .x2 - 8 + BitVec.ofNat 64 q := by
    rw [hu.keep .x2 (by decide), hx.atSh.x2, h6, show s.getReg .x2 - 16 + 8 = s.getReg .x2 - 8 by
      addr_omega [hB], or_eq_add hb.2.2.2.2 (by rw [BitVec.toNat_ofNat]; omega)]
  have hP : u.getReg .x7 + u.getReg .x6 = s.getReg .x11 + BitVec.ofNat 64 (h + 8 * J - a) +
      BitVec.ofNat 64 q := by rw [h7, h6]
  obtain ⟨v, hr, hv⟩ := hC.qh.reaches hpc (by
    simp only [qhE, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, add_zero_lit, hQ, hP]
    exact ⟨valid_of (by decide) (by addr_omega [hB, h8, hb]) (by addr_omega [hB, hal, h8, hb]),
      valid_of (by decide) (by addr_omega [hsm, hb, hJ, h8])
        (by addr_omega [hsm, hb, hJ, ha, hal, h8])⟩)
  have k := keepOf hv rfl (.x5 :: .x7 :: .x14 :: .x17 :: shR3)
  have hm := memOf hv rfl
  have e6 := hv.reg .x6 rfl
  blk at hm e6
  rw [hQ, hP] at hm
  have hbuf := fun i (hi : i < 8) ↦ buf_update (lk := .h) (sk := .h) rfl hb.2.2.2.2
    (q := q) (by omega) (by simp only [StoreKind.width]; addr_omega [hB, hal, h8, hb])
    (by simp only [StoreKind.width]; addr_omega [hsm, hb, hJ, ha, hal, h8]) hm hi
  have hf (x : Word) (hx' : x ≠ s.getReg .x2 - 8) : v.getMem x = u.getMem x :=
    frameOf hv rfl x (by
      simp only [Addr.eval, E.eval, BinOp.eval, add_zero_lit, hQ,
        (key_eq (q := q) hb.2.2.2.2 (by omega)).1]
      exact hx')
  have hx11 : u.getReg .x11 = w.getReg .x11 := hu.keep .x11 (by decide)
  refine ⟨v, hr, hu.step (wd := 2) hx h8 (fun r hr ↦ k r (by simp at hr ⊢; tauto)) hf hbuf,
    k .x7 (by decide), by rw [e6, h6, addw2 (by omega)],
    fun hc ↦ pcT hv rfl (by cond; rw [hx11]; exact hc),
    fun hc ↦ pcF hv rfl (by cond; rw [hx11]; exact hc)⟩

theorem qb_step {C : FwdCode} (hC : C.Ok) {w : MachineState} {h a J q : Nat}
    (hx : QCtx C s w h a J) {u : MachineState} (hpc : u.pc = C.qb) (hu : QL s w u h a J q)
    (h7 : u.getReg .x7 = s.getReg .x11 + BitVec.ofNat 64 (h + 8 * J - a))
    (h6 : u.getReg .x6 = BitVec.ofNat 64 q) (h8 : q + 1 ≤ a) :
    ∃ v, Reaches Image.code u v ∧ QL s w v h a J (q + 1) ∧ v.pc = C.fin := by
  have hb := hx.toShCtx.bounds
  have hJ := hx.bounds
  have hB := hx.pre.buf
  have hsm := hx.pre.src
  simp only [Mapped] at hsm
  have hQ : (u.getReg .x2 + 8 ||| u.getReg .x6) = s.getReg .x2 - 8 + BitVec.ofNat 64 q := by
    rw [hu.keep .x2 (by decide), hx.atSh.x2, h6, show s.getReg .x2 - 16 + 8 = s.getReg .x2 - 8 by
      addr_omega [hB], or_eq_add hb.2.2.2.2 (by rw [BitVec.toNat_ofNat]; omega)]
  have hP : u.getReg .x7 + u.getReg .x6 = s.getReg .x11 + BitVec.ofNat 64 (h + 8 * J - a) +
      BitVec.ofNat 64 q := by rw [h7, h6]
  obtain ⟨v, hr, hv⟩ := hC.qb.reaches hpc (by
    simp only [qbE, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, add_zero_lit, hQ, hP]
    exact ⟨valid_of (by decide) (by addr_omega [hB, h8, hb]) (Nat.mod_one _),
      valid_of (by decide) (by addr_omega [hsm, hb, hJ, h8]) (Nat.mod_one _)⟩)
  have k := keepOf hv rfl (.x5 :: .x14 :: .x17 :: shR3)
  have hm := memOf hv rfl
  blk at hm
  rw [hQ, hP] at hm
  have hbuf := fun i (hi : i < 8) ↦ buf_update (lk := .bu) (sk := .b) rfl hb.2.2.2.2
    (q := q) (by omega) (Nat.mod_one _) (Nat.mod_one _) hm hi
  have hf (x : Word) (hx' : x ≠ s.getReg .x2 - 8) : v.getMem x = u.getMem x :=
    frameOf hv rfl x (by
      simp only [Addr.eval, E.eval, BinOp.eval, add_zero_lit, hQ,
        (key_eq (q := q) hb.2.2.2.2 (by omega)).1]
      exact hx')
  exact ⟨v, hr, hu.step (wd := 1) hx h8 k hf hbuf, pcC hv rfl⟩

theorem qt2_step {C : FwdCode} (hC : C.Ok) {w : MachineState} {h a J q : Nat}
    {u : MachineState} (hpc : u.pc = C.qt2) (hu : QL s w u h a J q) :
    ∃ v, Reaches Image.code u v ∧ QL s w v h a J q ∧ v.getReg .x7 = u.getReg .x7 ∧
      v.getReg .x6 = u.getReg .x6 ∧ ((w.getReg .x11 &&& 2) ≠ 0 → v.pc = C.qh) ∧
      ((w.getReg .x11 &&& 2) = 0 → v.pc = C.qt1) := by
  obtain ⟨v, hr, hv⟩ := hC.qt2.reaches hpc trivial
  have k := keepOf hv rfl (.x5 :: .x6 :: .x7 :: .x14 :: .x17 :: shR3)
  have hx11 : u.getReg .x11 = w.getReg .x11 := hu.keep .x11 (by decide)
  exact ⟨v, hr, hu.of_same (fun r hr ↦ k r (by simp at hr ⊢; tauto)) (sameOf hv rfl),
    k .x7 (by decide), k .x6 (by decide), fun hc ↦ pcT hv rfl (by cond; rw [hx11]; exact hc),
    fun hc ↦ pcF hv rfl (by cond; rw [hx11]; exact hc)⟩

theorem qt1_step {C : FwdCode} (hC : C.Ok) {w : MachineState} {h a J q : Nat}
    {u : MachineState} (hpc : u.pc = C.qt1) (hu : QL s w u h a J q) :
    ∃ v, Reaches Image.code u v ∧ QL s w v h a J q ∧ v.getReg .x7 = u.getReg .x7 ∧
      v.getReg .x6 = u.getReg .x6 ∧ ((w.getReg .x11 &&& 1) = 0 → v.pc = C.fin) ∧
      ((w.getReg .x11 &&& 1) ≠ 0 → v.pc = C.qb) := by
  obtain ⟨v, hr, hv⟩ := hC.qt1.reaches hpc trivial
  have k := keepOf hv rfl (.x5 :: .x6 :: .x7 :: .x14 :: .x17 :: shR3)
  have hx11 : u.getReg .x11 = w.getReg .x11 := hu.keep .x11 (by decide)
  exact ⟨v, hr, hu.of_same (fun r hr ↦ k r (by simp at hr ⊢; tauto)) (sameOf hv rfl),
    k .x7 (by decide), k .x6 (by decide), fun hc ↦ pcT hv rfl (by cond; rw [hx11]; exact hc),
    fun hc ↦ pcF hv rfl (by cond; rw [hx11]; exact hc)⟩

theorem qj_step {C : FwdCode} (hC : C.Ok) {w : MachineState} {h a J q : Nat}
    {u : MachineState} (hpc : u.pc = C.qj) (hu : QL s w u h a J q) :
    ∃ v, Reaches Image.code u v ∧ QL s w v h a J q ∧ v.pc = C.fin := by
  obtain ⟨v, hr, hv⟩ := hC.qj.reaches hpc trivial
  exact ⟨v, hr, hu.of_same (keepOf hv rfl _) (sameOf hv rfl), pcC hv rfl⟩

/-- The second buffer fill: the source's next `a` bytes. -/
theorem chain2 {C : FwdCode} (hC : C.Ok) {w : MachineState} {h a J : Nat}
    (hx : QCtx C s w h a J) {u : MachineState} (hu : QL s w u h a J 0)
    (h7 : u.getReg .x7 = s.getReg .x11 + BitVec.ofNat 64 (h + 8 * J - a))
    (h6 : u.getReg .x6 = 0) (hqw : 4 ≤ a → u.pc = C.qw) (hqt2 : a < 4 → u.pc = C.qt2) :
    ∃ v, Reaches Image.code u v ∧ QL s w v h a J a ∧ v.pc = C.fin := by
  have hb := hx.toShCtx.bounds
  have h11 := hx.toShCtx.x11
  have b2 := and_low h11 (c := 2) (by decide)
  have b1 := and_low h11 (c := 1) (by decide)
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
    a = 6 ∨ a = 7 := by omega
  · obtain ⟨u₁, r₁, p₁, x7₁, x6₁, -, f₁⟩ := qt2_step hC (hqt2 (by decide)) hu
    obtain ⟨u₂, r₂, p₂, x7₂, x6₂, -, f₂⟩ := qt1_step hC (f₁ (by rw [b2]; decide)) p₁
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := qb_step hC hx (f₂ (by rw [b1]; decide)) p₂
      (by rw [x7₂, x7₁, h7]) (by rw [x6₂, x6₁, h6]; rfl) (by decide)
    exact ⟨u₃, r₁.trans (r₂.trans r₃), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, x7₁, x6₁, t₁, -⟩ := qt2_step hC (hqt2 (by decide)) hu
    obtain ⟨u₂, r₂, p₂, -, -, -, f₂⟩ := qh_step hC hx (t₁ (by rw [b2]; decide)) p₁
      (by rw [x7₁, h7]) (by rw [x6₁, h6]; rfl) (by decide) (by decide)
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := qj_step hC (f₂ (by rw [b1]; decide)) p₂
    exact ⟨u₃, r₁.trans (r₂.trans r₃), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, x7₁, x6₁, t₁, -⟩ := qt2_step hC (hqt2 (by decide)) hu
    obtain ⟨u₂, r₂, p₂, x7₂, x6₂, t₂, -⟩ := qh_step hC hx (t₁ (by rw [b2]; decide)) p₁
      (by rw [x7₁, h7]) (by rw [x6₁, h6]; rfl) (by decide) (by decide)
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := qb_step hC hx (t₂ (by rw [b1]; decide)) p₂
      (by rw [x7₂, x7₁, h7]) x6₂ (by decide)
    exact ⟨u₃, r₁.trans (r₂.trans r₃), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, x7₁, x6₁, t₁, -⟩ := qw_step hC hx (hqw (by decide)) hu h7 (by decide)
    obtain ⟨u₂, r₂, p₂, -, -, t₂, -⟩ := qt1_step hC (t₁ (by rw [b2]; decide)) p₁
    exact ⟨u₂, r₁.trans r₂, p₂, t₂ (by rw [b1]; decide)⟩
  · obtain ⟨u₁, r₁, p₁, x7₁, x6₁, t₁, -⟩ := qw_step hC hx (hqw (by decide)) hu h7 (by decide)
    obtain ⟨u₂, r₂, p₂, x7₂, x6₂, -, f₂⟩ := qt1_step hC (t₁ (by rw [b2]; decide)) p₁
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := qb_step hC hx (f₂ (by rw [b1]; decide)) p₂
      (by rw [x7₂, x7₁, h7]) (by rw [x6₂, x6₁]; rfl) (by decide)
    exact ⟨u₃, r₁.trans (r₂.trans r₃), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, x7₁, x6₁, -, f₁⟩ := qw_step hC hx (hqw (by decide)) hu h7 (by decide)
    obtain ⟨u₂, r₂, p₂, -, -, -, f₂⟩ := qh_step hC hx (f₁ (by rw [b2]; decide)) p₁
      (by rw [x7₁, h7]) (by rw [x6₁]; rfl) (by decide) (by decide)
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := qj_step hC (f₂ (by rw [b1]; decide)) p₂
    exact ⟨u₃, r₁.trans (r₂.trans r₃), p₃, pc₃⟩
  · obtain ⟨u₁, r₁, p₁, x7₁, x6₁, -, f₁⟩ := qw_step hC hx (hqw (by decide)) hu h7 (by decide)
    obtain ⟨u₂, r₂, p₂, x7₂, x6₂, t₂, -⟩ := qh_step hC hx (f₁ (by rw [b2]; decide)) p₁
      (by rw [x7₁, h7]) (by rw [x6₁]; rfl) (by decide) (by decide)
    obtain ⟨u₃, r₃, p₃, pc₃⟩ := qb_step hC hx (t₂ (by rw [b1]; decide)) p₂
      (by rw [x7₂, x7₁, h7]) x6₂ (by decide)
    exact ⟨u₃, r₁.trans (r₂.trans r₃), p₃, pc₃⟩

theorem fin_step {C : FwdCode} (hC : C.Ok) {w : MachineState} {h a J : Nat}
    (hx : QCtx C s w h a J) {u : MachineState} (hpc : u.pc = C.fin) (hu : QL s w u h a J a) :
    ∃ v, Reaches Image.code u v ∧ Done C s v h := by
  have hb := hx.toShCtx.bounds
  have hJ := hx.bounds
  have hB := hx.pre.buf
  have hdm := hx.pre.dst
  simp only [Mapped] at hdm
  have hw := hx.atSh
  have hald := hw.ald
  have hx2 : u.getReg .x2 + 8 = s.getReg .x2 - 8 := by
    rw [hu.keep .x2 (by decide), hw.x2]; addr_omega [hB]
  have hx14 := hu.x14
  have hD8 : (s.getReg .x10 + BitVec.ofNat 64 (h + 8 * (J - 1))).toNat % 8 = 0 := by
    addr_omega [hdm, hb, hJ, hald]
  obtain ⟨v, hr, hv⟩ := hC.fin.reaches hpc (by
    simp only [finE, Oblig.all, Oblig.holds, Addr.eval, E.eval, add_zero_lit, hx2, hx14]
    exact ⟨valid_of (by decide) (by addr_omega [hdm, hb, hJ]) hD8,
      valid_of (by decide) (by addr_omega [hB]) (by omega)⟩)
  have k := keepOf hv rfl shR3
  have hm := memOf hv rfl
  blk at hm
  have hsh := hx.toShCtx.shamt
  rw [← hu.x17] at hsh
  rw [hx2, hx14, hsh.1, hsh.2, BitVec.or_comm] at hm
  have hcp : Copied s v (h + 8 * (J - 1) + 8) := by
    refine hu.copied.extend hx.pre (by omega) (ByteFrame.of_single hD8 fun x hx' ↦
      frameOf hv rfl x (by simp only [Addr.eval, E.eval, add_zero_lit, hx14]; exact hx'))
      fun i hi ↦ ?_
    rw [show s.getReg .x10 + BitVec.ofNat 64 (h + 8 * (J - 1) + i) =
      s.getReg .x10 + BitVec.ofNat 64 (h + 8 * (J - 1)) + BitVec.ofNat 64 i by
        rw [BitVec.ofNat_add, BitVec.add_assoc], byteAt_add hD8 hi, hm,
      extractByte_shift _ _ hb.1 hb.2.1 hi]
    split
    · rw [hu.x5 (i + a) (by omega) (by omega)]
      congr 3
      omega
    · rw [hu.buf _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 3
      omega
  have kk (r : Reg) (hr : r ∈ shR3) : v.getReg r = w.getReg r := (k r hr).trans (hu.keep r hr)
  have hJ' := hx.hJ
  refine ⟨v, hr, ⟨pcC hv rfl, by rw [kk .x13 (by decide), hw.x13],
    by rw [kk .x11 (by decide), hw.x11], by rw [kk .x12 (by decide), hw.x12],
    by rw [kk .x15 (by decide), hw.x15], by rw [kk .x2 (by decide), hw.x2],
    fun r hr ↦ (kk r (by simp [shR3, hr])).trans (hw.keep r hr), ?_⟩⟩
  rw [← hJ', show h + 8 * J = h + 8 * (J - 1) + 8 by omega]
  exact hcp

/-- **The shifting path** reaches the tail with every destination doubleword stored. -/
theorem shift_ok {C : FwdCode} (hC : C.Ok) : ShiftOk C := by
  intro s w h hp hw
  have hx : ShCtx C s w h (((s.getReg .x11).toNat + h) % 8) := ⟨hp, hw, rfl⟩
  have hb := hx.bounds
  have hq : QCtx C s w h (((s.getReg .x11).toNat + h) % 8) (((s.getReg .x12).toNat - h) / 8) :=
    ⟨hx, rfl⟩
  obtain ⟨u₁, r₁, p₁, pc₁⟩ := chain1 hC hx
  obtain ⟨u₂, r₂, p₂, a₂, l₂⟩ := pe_step hC hx pc₁ p₁
  obtain ⟨u₃, r₃, pc₃, p₃⟩ : ∃ u₃, Reaches Image.code u₂ u₃ ∧ u₃.pc = C.after ∧
      LI s w u₃ h (((s.getReg .x11).toNat + h) % 8) (((s.getReg .x12).toNat - h) / 8 - 1) := by
    by_cases hJ : (s.getReg .x12).toNat - h < 16
    · refine ⟨u₂, Reaches.refl _, a₂ hJ, ?_⟩
      rw [show ((s.getReg .x12).toNat - h) / 8 - 1 = 0 by omega]
      exact p₂
    · obtain ⟨u₃, r₃, pc₃, p₃, x6₃⟩ := lpre_step hC (l₂ (by omega)) p₂
      obtain ⟨v, rv, pcv, pv⟩ := Reaches.loop (code := Image.code) (fun u ↦ ∃ j, u.pc = C.loop ∧
          LI s w u h (((s.getReg .x11).toNat + h) % 8) j ∧
          u.getReg .x6 = (0 - u.getReg .x17) &&& 56 ∧ h + 8 * j + 16 ≤ (s.getReg .x12).toNat)
        (fun u ↦ (u.getReg .x13).toNat - (u.getReg .x14).toNat)
        (fun v ↦ v.pc = C.after ∧
          LI s w v h (((s.getReg .x11).toNat + h) % 8) (((s.getReg .x12).toNat - h) / 8 - 1))
        (loop_body hC hx) u₃ ⟨0, pc₃, p₃, x6₃, by omega⟩
      exact ⟨v, r₃.trans rv, pcv, pv⟩
  obtain ⟨u₄, r₄, p₄, x7₄, x6₄, qw₄, qt₄⟩ := after_step hC hx pc₃ p₃
  obtain ⟨u₅, r₅, p₅, pc₅⟩ := chain2 hC hq p₄ x7₄ x6₄ qw₄ qt₄
  obtain ⟨v, rv, hv⟩ := fin_step hC hq pc₅ p₅
  exact ⟨v, r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans rv)))), hv⟩

end Rv64Verifier.Runtime.Forward
