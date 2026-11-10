import Rv64Verifier.Proofs.Bytecode.EvalSum

/-!
# `Bytecode::evaluate`: a word's sum into its buckets, on the machine

From `AInv` at `0x80011150`, the eight blocks of `EvalAdd.lean`'s header, then the next word
(`WInv`) or the block's buckets (`Mid`).
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Model Rv64Verifier.Blocks.F84
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

variable {e : Env}

theorem wf_succ (e : Env) {i j : Nat} (h1 : (e.st i).wordsStart ≤ j) (h2 : j < e.bc.words.length) :
    e.wf i (j + 1 - (e.st i).wordsStart) =
      wordStepRust e.lowW e.bc.positions (e.wf i (j - (e.st i).wordsStart)) (e.wd j) := by
  rw [Env.wf, take_drop_succ _ h1 h2, List.foldl_append, Env.wd, List.getD_eq_getElem _ _ h2]
  rfl

/-- The bucket of byte `k` of `w`. -/
theorem byteIdx (w : Word) (k : Nat) (hk : k < 8) :
    256 * k + ((toLeBytes w).getD k 0).toNat < 2048 := by
  have := toLeBytes_lt w k; omega

theorem idx0 (w : Word) : (w &&& 255).toNat = 256 * 0 + ((toLeBytes w).getD 0 0).toNat := by
  rw [toNat_and255, toNat_toLeBytes w (by decide)]; simp

/-- Byte `k` of `w` plus `256 k`, as `slli`, `srli`, `addiw` compute it. -/
theorem idxMid (w : Word) (k : Nat) (hk : 1 ≤ k ∧ k < 7) (c : Word) (hc : c.toNat = 256 * k) :
    ((wordResult .add (((w * BitVec.ofNat 64 (2 ^ (56 - 8 * k))) >>> 56).truncate 32)
      (c.truncate 32)).signExtend 64).toNat = 256 * k + ((toLeBytes w).getD k 0).toNat := by
  have h := toNat_mul_shr w k (by omega)
  rw [toNat_addw _ _ (by rw [h, hc]; omega), h, hc, toNat_toLeBytes w (by omega)]
  omega

theorem idx3 (w : Word) :
    ((wordResult .add ((((wordResult .srl (w.truncate 32) ((24 : Word).truncate 32)).signExtend
      64)).truncate 32) ((768 : Word).truncate 32)).signExtend 64).toNat =
      256 * 3 + ((toLeBytes w).getD 3 0).toNat := by
  have h := toNat_srlw24 w
  rw [toNat_addw _ _ (by rw [h]; simp only [Sym.wordToNatLit]; omega), h,
    toNat_toLeBytes w (by decide)]
  simp only [Sym.wordToNatLit]; omega

theorem idx7 (w : Word) :
    ((wordResult .add ((w >>> 56).truncate 32) ((1792 : Word).truncate 32)).signExtend 64).toNat =
      256 * 7 + ((toLeBytes w).getD 7 0).toNat := by
  have h := toNat_shr56 w
  rw [toNat_addw _ _ (by rw [h]; simp only [Sym.wordToNatLit]; omega), h,
    toNat_toLeBytes w (by decide)]
  simp only [Sym.wordToNatLit]; omega

/-- The bounds check after a bucket's index: not taken. -/
theorem geu_fall {a b x y : Word} (h : a.toNat < b.toNat) :
    (if (!a.ult b) = true then x else y) = y := by
  simp [BitVec.ult, h]

/-- One bucket's addition, as a block does it, in the mirror's terms. -/
theorem upd (he : EnvOk e) {u u' : MachineState} {ir : Reg} {k : Nat} (hk : k < 8) {w : Word}
    {sum : E} (hidx : (u.getReg ir).toNat = 256 * k + ((toLeBytes w).getD k 0).toNat)
    (h20 : u.getReg .x20 = e.bk) (hsum : (u.getReg .x16, u.getReg .x15, u.getReg .x14) = limbs sum)
    (m2 : u'.getMem (u.getReg .x20 + (u.getReg ir * 16 + u.getReg ir * 8)) =
      u.getMem (u.getReg .x20 + (u.getReg ir * 16 + u.getReg ir * 8)) ^^^ u.getReg .x16)
    (m1 : u'.getMem (u.getReg .x20 + (u.getReg ir * 16 + u.getReg ir * 8) + 8) =
      u.getMem (u.getReg .x20 + (u.getReg ir * 16 + u.getReg ir * 8) + 8) ^^^ u.getReg .x15)
    (m0 : u'.getMem (u.getReg .x20 + (u.getReg ir * 16 + u.getReg ir * 8) + 16) =
      u.getMem (u.getReg .x20 + (u.getReg ir * 16 + u.getReg ir * 8) + 16) ^^^ u.getReg .x14)
    (hfr : ∀ a, ¬ Within a (e.bk + (u.getReg ir * 16 + u.getReg ir * 8)) 24 →
      u'.getMem a = u.getMem a) :
    eListAt u' e.bk 2048 = addStep w sum k (eListAt u e.bk 2048) ∧
      ∀ a, ¬ Within a e.bk 49152 → u'.getMem a = u.getMem a := by
  have hb := he.bkIn
  have hh := he.heapL.hi
  simp only [heapNext, heapEnd] at hb hh
  have hi : (u.getReg ir).toNat < 2048 := by rw [hidx]; exact byteIdx w k hk
  rw [h20] at m0 m1 m2
  refine ⟨?_, fun a ha ↦ hfr a ?_⟩
  · rw [bucket_update he hi hsum m2 m1 m0 hfr, addStep, hidx]
  · rw [mul24]; addr_omega [ha, hi, hb, hh]

/-- The registers the bucket blocks keep. -/
def bkKeep : List Reg := [.x2, .x9, .x11, .x12, .x13, .x14, .x15, .x16, .x18, .x19, .x20, .x21, .x23]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- Bucket 0, and bucket 1's index. -/
theorem bucket0 (he : EnvOk e) {u : MachineState} {w : Word} {sum : E}
    (hpc : u.pc = 0x80011158) (hidx : (u.getReg .x5).toNat = 256 * 0 + ((toLeBytes w).getD 0 0).toNat)
    (h20 : u.getReg .x20 = e.bk) (h21 : u.getReg .x21 = 2048) (h17 : u.getReg .x17 = w)
    (hsum : (u.getReg .x16, u.getReg .x15, u.getReg .x14) = limbs sum) :
    ∃ u', Reaches Image.code u u' ∧ u'.pc = 0x8001119c ∧
      (u'.getReg .x5).toNat = 256 * 1 + ((toLeBytes w).getD 1 0).toNat ∧
      eListAt u' e.bk 2048 = addStep w sum 0 (eListAt u e.bk 2048) ∧
      (∀ a, ¬ Within a e.bk 49152 → u'.getMem a = u.getMem a) ∧
      (∀ r ∈ bkKeep, u'.getReg r = u.getReg r) ∧ u'.getReg .x17 = w := by
  have hb := he.bkIn
  have hh := he.heapL.hi
  have hlo := he.pre.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hb hh hlo
  have hbm : Mapped e.bk 49152 := by simp only [Mapped]; omega
  have hba := hb.2.2
  have hlt : (u.getReg .x5).toNat < 2048 := by rw [hidx]; exact byteIdx w 0 (by decide)
  obtain ⟨u', hr, h⟩ := Sym.BlockSpec.reaches b80011158_spec hpc (by
    rv_eval [h20, mul24]
    and_intros <;> valid_in hbm [hbm, hba, hlt])
  have kk := b80011158_keeps h
  obtain ⟨L, F⟩ := upd he (by decide : 0 < 8) hidx h20 hsum (b80011158_m2 h) (b80011158_m1 h) (b80011158_m0 h)
    (fun a ha' ↦ h.frame a (by rv_eval [h20, mul24]; and_intros <;> addr_omega [ha', hlt, hb]))
  have r := h.reg .x5 rfl
  have p := h.pc
  rv_eval [] at r p
  have i : (u'.getReg .x5).toNat = 256 * 1 + ((toLeBytes w).getD 1 0).toNat := by
    rw [r, h17]; exact idxMid w 1 ⟨by decide, by decide⟩ 256 rfl
  refine ⟨u', hr, ?_, i, L, F, fun r hr ↦ kk r (mem_of_mem hr _), (kk .x17 (by decide)).trans h17⟩
  rw [p]
  apply geu_fall
  rw [← r, i, h21]; have := byteIdx w 1 (by decide); simp only [Sym.wordToNatLit]; omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- Bucket 1, and bucket 2's index. -/
theorem bucket1 (he : EnvOk e) {u : MachineState} {w : Word} {sum : E}
    (hpc : u.pc = 0x8001119c) (hidx : (u.getReg .x5).toNat = 256 * 1 + ((toLeBytes w).getD 1 0).toNat)
    (h20 : u.getReg .x20 = e.bk) (h21 : u.getReg .x21 = 2048) (h17 : u.getReg .x17 = w)
    (hsum : (u.getReg .x16, u.getReg .x15, u.getReg .x14) = limbs sum) :
    ∃ u', Reaches Image.code u u' ∧ u'.pc = 0x800111e0 ∧
      (u'.getReg .x5).toNat = 256 * 2 + ((toLeBytes w).getD 2 0).toNat ∧
      eListAt u' e.bk 2048 = addStep w sum 1 (eListAt u e.bk 2048) ∧
      (∀ a, ¬ Within a e.bk 49152 → u'.getMem a = u.getMem a) ∧
      (∀ r ∈ bkKeep, u'.getReg r = u.getReg r) ∧ u'.getReg .x17 = w := by
  have hb := he.bkIn
  have hh := he.heapL.hi
  have hlo := he.pre.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hb hh hlo
  have hbm : Mapped e.bk 49152 := by simp only [Mapped]; omega
  have hba := hb.2.2
  have hlt : (u.getReg .x5).toNat < 2048 := by rw [hidx]; exact byteIdx w 1 (by decide)
  obtain ⟨u', hr, h⟩ := Sym.BlockSpec.reaches b8001119c_spec hpc (by
    rv_eval [h20, mul24]
    and_intros <;> valid_in hbm [hbm, hba, hlt])
  have kk := b8001119c_keeps h
  obtain ⟨L, F⟩ := upd he (by decide : 1 < 8) hidx h20 hsum (b8001119c_m2 h) (b8001119c_m1 h) (b8001119c_m0 h)
    (fun a ha' ↦ h.frame a (by rv_eval [h20, mul24]; and_intros <;> addr_omega [ha', hlt, hb]))
  have r := h.reg .x5 rfl
  have p := h.pc
  rv_eval [] at r p
  have i : (u'.getReg .x5).toNat = 256 * 2 + ((toLeBytes w).getD 2 0).toNat := by
    rw [r, h17]; exact idxMid w 2 ⟨by decide, by decide⟩ 512 rfl
  refine ⟨u', hr, ?_, i, L, F, fun r hr ↦ kk r (mem_of_mem hr _), (kk .x17 (by decide)).trans h17⟩
  rw [p]
  apply geu_fall
  rw [← r, i, h21]; have := byteIdx w 2 (by decide); simp only [Sym.wordToNatLit]; omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- Bucket 2, and bucket 3's index. -/
theorem bucket2 (he : EnvOk e) {u : MachineState} {w : Word} {sum : E}
    (hpc : u.pc = 0x800111e0) (hidx : (u.getReg .x5).toNat = 256 * 2 + ((toLeBytes w).getD 2 0).toNat)
    (h20 : u.getReg .x20 = e.bk) (h21 : u.getReg .x21 = 2048) (h17 : u.getReg .x17 = w)
    (hsum : (u.getReg .x16, u.getReg .x15, u.getReg .x14) = limbs sum) :
    ∃ u', Reaches Image.code u u' ∧ u'.pc = 0x80011220 ∧
      (u'.getReg .x5).toNat = 256 * 3 + ((toLeBytes w).getD 3 0).toNat ∧
      eListAt u' e.bk 2048 = addStep w sum 2 (eListAt u e.bk 2048) ∧
      (∀ a, ¬ Within a e.bk 49152 → u'.getMem a = u.getMem a) ∧
      (∀ r ∈ bkKeep, u'.getReg r = u.getReg r) ∧ u'.getReg .x17 = w := by
  have hb := he.bkIn
  have hh := he.heapL.hi
  have hlo := he.pre.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hb hh hlo
  have hbm : Mapped e.bk 49152 := by simp only [Mapped]; omega
  have hba := hb.2.2
  have hlt : (u.getReg .x5).toNat < 2048 := by rw [hidx]; exact byteIdx w 2 (by decide)
  obtain ⟨u', hr, h⟩ := Sym.BlockSpec.reaches b800111e0_spec hpc (by
    rv_eval [h20, mul24]
    and_intros <;> valid_in hbm [hbm, hba, hlt])
  have kk := b800111e0_keeps h
  obtain ⟨L, F⟩ := upd he (by decide : 2 < 8) hidx h20 hsum (b800111e0_m2 h) (b800111e0_m1 h) (b800111e0_m0 h)
    (fun a ha' ↦ h.frame a (by rv_eval [h20, mul24]; and_intros <;> addr_omega [ha', hlt, hb]))
  have r := h.reg .x5 rfl
  have p := h.pc
  rv_eval [] at r p
  have i : (u'.getReg .x5).toNat = 256 * 3 + ((toLeBytes w).getD 3 0).toNat := by
    rw [r, h17]; exact idx3 w
  refine ⟨u', hr, ?_, i, L, F, fun r hr ↦ kk r (mem_of_mem hr _), (kk .x17 (by decide)).trans h17⟩
  rw [p]
  apply geu_fall
  rw [← r, i, h21]; have := byteIdx w 3 (by decide); simp only [Sym.wordToNatLit]; omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- Bucket 3, and bucket 4's index. -/
theorem bucket3 (he : EnvOk e) {u : MachineState} {w : Word} {sum : E}
    (hpc : u.pc = 0x80011220) (hidx : (u.getReg .x5).toNat = 256 * 3 + ((toLeBytes w).getD 3 0).toNat)
    (h20 : u.getReg .x20 = e.bk) (h21 : u.getReg .x21 = 2048) (h17 : u.getReg .x17 = w)
    (hsum : (u.getReg .x16, u.getReg .x15, u.getReg .x14) = limbs sum) :
    ∃ u', Reaches Image.code u u' ∧ u'.pc = 0x80011264 ∧
      (u'.getReg .x5).toNat = 256 * 4 + ((toLeBytes w).getD 4 0).toNat ∧
      eListAt u' e.bk 2048 = addStep w sum 3 (eListAt u e.bk 2048) ∧
      (∀ a, ¬ Within a e.bk 49152 → u'.getMem a = u.getMem a) ∧
      (∀ r ∈ bkKeep, u'.getReg r = u.getReg r) ∧ u'.getReg .x17 = w := by
  have hb := he.bkIn
  have hh := he.heapL.hi
  have hlo := he.pre.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hb hh hlo
  have hbm : Mapped e.bk 49152 := by simp only [Mapped]; omega
  have hba := hb.2.2
  have hlt : (u.getReg .x5).toNat < 2048 := by rw [hidx]; exact byteIdx w 3 (by decide)
  obtain ⟨u', hr, h⟩ := Sym.BlockSpec.reaches b80011220_spec hpc (by
    rv_eval [h20, mul24]
    and_intros <;> valid_in hbm [hbm, hba, hlt])
  have kk := b80011220_keeps h
  obtain ⟨L, F⟩ := upd he (by decide : 3 < 8) hidx h20 hsum (b80011220_m2 h) (b80011220_m1 h) (b80011220_m0 h)
    (fun a ha' ↦ h.frame a (by rv_eval [h20, mul24]; and_intros <;> addr_omega [ha', hlt, hb]))
  have r := h.reg .x5 rfl
  have p := h.pc
  rv_eval [] at r p
  have i : (u'.getReg .x5).toNat = 256 * 4 + ((toLeBytes w).getD 4 0).toNat := by
    rw [r, h17]; exact idxMid w 4 ⟨by decide, by decide⟩ 1024 rfl
  refine ⟨u', hr, ?_, i, L, F, fun r hr ↦ kk r (mem_of_mem hr _), (kk .x17 (by decide)).trans h17⟩
  rw [p]
  apply geu_fall
  rw [← r, i, h21]; have := byteIdx w 4 (by decide); simp only [Sym.wordToNatLit]; omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- Bucket 4, and bucket 5's index. -/
theorem bucket4 (he : EnvOk e) {u : MachineState} {w : Word} {sum : E}
    (hpc : u.pc = 0x80011264) (hidx : (u.getReg .x5).toNat = 256 * 4 + ((toLeBytes w).getD 4 0).toNat)
    (h20 : u.getReg .x20 = e.bk) (h21 : u.getReg .x21 = 2048) (h17 : u.getReg .x17 = w)
    (hsum : (u.getReg .x16, u.getReg .x15, u.getReg .x14) = limbs sum) :
    ∃ u', Reaches Image.code u u' ∧ u'.pc = 0x800112a8 ∧
      (u'.getReg .x5).toNat = 256 * 5 + ((toLeBytes w).getD 5 0).toNat ∧
      eListAt u' e.bk 2048 = addStep w sum 4 (eListAt u e.bk 2048) ∧
      (∀ a, ¬ Within a e.bk 49152 → u'.getMem a = u.getMem a) ∧
      (∀ r ∈ bkKeep, u'.getReg r = u.getReg r) ∧ u'.getReg .x17 = w := by
  have hb := he.bkIn
  have hh := he.heapL.hi
  have hlo := he.pre.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hb hh hlo
  have hbm : Mapped e.bk 49152 := by simp only [Mapped]; omega
  have hba := hb.2.2
  have hlt : (u.getReg .x5).toNat < 2048 := by rw [hidx]; exact byteIdx w 4 (by decide)
  obtain ⟨u', hr, h⟩ := Sym.BlockSpec.reaches b80011264_spec hpc (by
    rv_eval [h20, mul24]
    and_intros <;> valid_in hbm [hbm, hba, hlt])
  have kk := b80011264_keeps h
  obtain ⟨L, F⟩ := upd he (by decide : 4 < 8) hidx h20 hsum (b80011264_m2 h) (b80011264_m1 h) (b80011264_m0 h)
    (fun a ha' ↦ h.frame a (by rv_eval [h20, mul24]; and_intros <;> addr_omega [ha', hlt, hb]))
  have r := h.reg .x5 rfl
  have p := h.pc
  rv_eval [] at r p
  have i : (u'.getReg .x5).toNat = 256 * 5 + ((toLeBytes w).getD 5 0).toNat := by
    rw [r, h17]; exact idxMid w 5 ⟨by decide, by decide⟩ 1280 rfl
  refine ⟨u', hr, ?_, i, L, F, fun r hr ↦ kk r (mem_of_mem hr _), (kk .x17 (by decide)).trans h17⟩
  rw [p]
  apply geu_fall
  rw [← r, i, h21]; have := byteIdx w 5 (by decide); simp only [Sym.wordToNatLit]; omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- Bucket 5, and bucket 6's index. -/
theorem bucket5 (he : EnvOk e) {u : MachineState} {w : Word} {sum : E}
    (hpc : u.pc = 0x800112a8) (hidx : (u.getReg .x5).toNat = 256 * 5 + ((toLeBytes w).getD 5 0).toNat)
    (h20 : u.getReg .x20 = e.bk) (h21 : u.getReg .x21 = 2048) (h17 : u.getReg .x17 = w)
    (hsum : (u.getReg .x16, u.getReg .x15, u.getReg .x14) = limbs sum) :
    ∃ u', Reaches Image.code u u' ∧ u'.pc = 0x800112ec ∧
      (u'.getReg .x5).toNat = 256 * 6 + ((toLeBytes w).getD 6 0).toNat ∧
      eListAt u' e.bk 2048 = addStep w sum 5 (eListAt u e.bk 2048) ∧
      (∀ a, ¬ Within a e.bk 49152 → u'.getMem a = u.getMem a) ∧
      (∀ r ∈ bkKeep, u'.getReg r = u.getReg r) ∧ u'.getReg .x17 = w := by
  have hb := he.bkIn
  have hh := he.heapL.hi
  have hlo := he.pre.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hb hh hlo
  have hbm : Mapped e.bk 49152 := by simp only [Mapped]; omega
  have hba := hb.2.2
  have hlt : (u.getReg .x5).toNat < 2048 := by rw [hidx]; exact byteIdx w 5 (by decide)
  obtain ⟨u', hr, h⟩ := Sym.BlockSpec.reaches b800112a8_spec hpc (by
    rv_eval [h20, mul24]
    and_intros <;> valid_in hbm [hbm, hba, hlt])
  have kk := b800112a8_keeps h
  obtain ⟨L, F⟩ := upd he (by decide : 5 < 8) hidx h20 hsum (b800112a8_m2 h) (b800112a8_m1 h) (b800112a8_m0 h)
    (fun a ha' ↦ h.frame a (by rv_eval [h20, mul24]; and_intros <;> addr_omega [ha', hlt, hb]))
  have r := h.reg .x5 rfl
  have p := h.pc
  rv_eval [] at r p
  have i : (u'.getReg .x5).toNat = 256 * 6 + ((toLeBytes w).getD 6 0).toNat := by
    rw [r, h17]; exact idxMid w 6 ⟨by decide, by decide⟩ 1536 rfl
  refine ⟨u', hr, ?_, i, L, F, fun r hr ↦ kk r (mem_of_mem hr _), (kk .x17 (by decide)).trans h17⟩
  rw [p]
  apply geu_fall
  rw [← r, i, h21]; have := byteIdx w 6 (by decide); simp only [Sym.wordToNatLit]; omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- Bucket 6, and bucket 7's index. -/
theorem bucket6 (he : EnvOk e) {u : MachineState} {w : Word} {sum : E}
    (hpc : u.pc = 0x800112ec) (hidx : (u.getReg .x5).toNat = 256 * 6 + ((toLeBytes w).getD 6 0).toNat)
    (h20 : u.getReg .x20 = e.bk) (h21 : u.getReg .x21 = 2048) (h17 : u.getReg .x17 = w)
    (hsum : (u.getReg .x16, u.getReg .x15, u.getReg .x14) = limbs sum) :
    ∃ u', Reaches Image.code u u' ∧ u'.pc = 0x8001132c ∧
      (u'.getReg .x17).toNat = 256 * 7 + ((toLeBytes w).getD 7 0).toNat ∧
      eListAt u' e.bk 2048 = addStep w sum 6 (eListAt u e.bk 2048) ∧
      (∀ a, ¬ Within a e.bk 49152 → u'.getMem a = u.getMem a) ∧
      (∀ r ∈ bkKeep, u'.getReg r = u.getReg r) := by
  have hb := he.bkIn
  have hh := he.heapL.hi
  have hlo := he.pre.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hb hh hlo
  have hbm : Mapped e.bk 49152 := by simp only [Mapped]; omega
  have hba := hb.2.2
  have hlt : (u.getReg .x5).toNat < 2048 := by rw [hidx]; exact byteIdx w 6 (by decide)
  obtain ⟨u', hr, h⟩ := Sym.BlockSpec.reaches b800112ec_spec hpc (by
    rv_eval [h20, mul24]
    and_intros <;> valid_in hbm [hbm, hba, hlt])
  have kk := b800112ec_keeps h
  obtain ⟨L, F⟩ := upd he (by decide : 6 < 8) hidx h20 hsum (b800112ec_m2 h) (b800112ec_m1 h) (b800112ec_m0 h)
    (fun a ha' ↦ h.frame a (by rv_eval [h20, mul24]; and_intros <;> addr_omega [ha', hlt, hb]))
  have r := h.reg .x17 rfl
  have p := h.pc
  rv_eval [] at r p
  have i : (u'.getReg .x17).toNat = 256 * 7 + ((toLeBytes w).getD 7 0).toNat := by
    rw [r, h17]; exact idx7 w
  refine ⟨u', hr, ?_, i, L, F, fun r hr ↦ kk r (mem_of_mem hr _)⟩
  rw [p]
  apply geu_fall
  rw [← r, i, h21]; have := byteIdx w 7 (by decide); simp only [Sym.wordToNatLit]; omega

set_option maxHeartbeats 2000000 in
/-- Bucket 7, then the next word or the block's end. -/
theorem bucket7 (he : EnvOk e) {u : MachineState} {w : Word} {sum : E}
    (hpc : u.pc = 0x8001132c)
    (hidx : (u.getReg .x17).toNat = 256 * 7 + ((toLeBytes w).getD 7 0).toNat)
    (h20 : u.getReg .x20 = e.bk)
    (hsum : (u.getReg .x16, u.getReg .x15, u.getReg .x14) = limbs sum) :
    ∃ u', Reaches Image.code u u' ∧
      u'.pc = (if u.getReg .x13 + 16 ≠ u.getReg .x12 then 0x800110d0 else 0x8001136c) ∧
      eListAt u' e.bk 2048 = addStep w sum 7 (eListAt u e.bk 2048) ∧
      (∀ a, ¬ Within a e.bk 49152 → u'.getMem a = u.getMem a) ∧
      u'.getReg .x13 = u.getReg .x13 + 16 ∧ u'.getReg .x6 = u.getReg .x19 ∧
      ∀ r ∈ [Reg.x2, .x9, .x11, .x12, .x18, .x19, .x20, .x21, .x23], u'.getReg r = u.getReg r := by
  have hb := he.bkIn
  have hh := he.heapL.hi
  have hlo := he.pre.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hb hh hlo
  have hbm : Mapped e.bk 49152 := by simp only [Mapped]; omega
  have hba := hb.2.2
  have hlt : (u.getReg .x17).toNat < 2048 := by rw [hidx]; exact byteIdx w 7 (by decide)
  obtain ⟨u', hr, h⟩ := Sym.BlockSpec.reaches b8001132c_spec hpc (by
    rv_eval [h20, mul24]
    and_intros <;> valid_in hbm [hbm, hba, hlt])
  have kk := b8001132c_keeps h
  obtain ⟨L, F⟩ := upd he (by decide : 7 < 8) hidx h20 hsum (b8001132c_m2 h) (b8001132c_m1 h)
    (b8001132c_m0 h)
    (fun a ha' ↦ h.frame a (by rv_eval [h20, mul24]; and_intros <;> addr_omega [ha', hlt, hb]))
  refine ⟨u', hr, ?_, L, F, b8001132c_x13 h, b8001132c_x6 h, fun r hr ↦ kk r (mem_of_mem hr _)⟩
  by_cases hc : u.getReg .x13 + 16 ≠ u.getReg .x12
  · rw [b8001132c_pc_taken h hc, ite_eq_left_of_eq_true _ _ (eq_true hc)]
  · rw [b8001132c_pc_not_taken h (not_not.mp hc), ite_eq_right_of_eq_false _ _ (eq_false hc)]

end Rv64Verifier.Proofs.Bytecode.Eval
