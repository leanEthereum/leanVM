module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Step
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Fx
public import NativeRustcX64.Spec.Mem

/-!
# `verify_keccak`: callees' footprints (x86-64)

Ranges in `verify_keccak`'s stack with the return address (`InStk`: the frame, a callee's stack,
its stack arguments) are apart from what the precondition's footprint keeps apart from that stack
(`sep_stk`). A stack argument a block pushed (`stackArg_of`). `memcpy` within the frame
(`cpPre`), and what it copies (`Img`: byte images, copied from the AArch64 proof's `Img`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.KeccakGkr.SeqZ NativeVm.Model
open NativeRustcVm.Transcript (DecArea TStateAt)
open NativeRustcVm.KeccakGkr (off ClaimAt)

/-- A side goal on numbers and literals. -/
macro "nd" : tactic => `(tactic| first | decide | (simp only [rsz] <;> omega) | (dsimp only <;> omega))

@[expose] public section

/-- The `n` bytes from `A` are in `verify_keccak`'s stack with its return address. -/
def InStk [Labels] (m0 : MachineData) (A : BitVec 64) (n : Nat) : Prop :=
  (stackBelow m0 verifyKeccakStack).toNat ≤ A.toNat ∧
    A.toNat + n ≤ (stackBelow m0 verifyKeccakStack).toNat + (verifyKeccakStack + 8)

/-- The `n` bytes from `p` in `d` are at `q` in `d'`. -/
def Img (d : Mem 64) (p : BitVec 64) (d' : Mem 64) (q : BitVec 64) (n : Nat) : Prop :=
  ∀ j < n, ∀ b, d.get? (p + BitVec.ofNat 64 j) = some b → d'.get? (q + BitVec.ofNat 64 j) = some b

end

public section

section
variable [Labels] {m0 mc : MachineData} {a : DecArea} {inst : Array EW} {wr : Nat → Bool}
  {oc : Nat}

theorem sep_stk {A B : BitVec 64} {n k : Nat} (hA : InStk m0 A n)
    (hB : Sep B.toNat k (stackBelow m0 verifyKeccakStack).toNat (verifyKeccakStack + 8)) :
    Sep A.toNat n B.toNat k := by
  unfold InStk at hA; unfold Sep at *; omega

theorem sep_stk' {A B : BitVec 64} {n k : Nat} (hA : InStk m0 A n)
    (hB : Sep B.toNat k (stackBelow m0 verifyKeccakStack).toNat (verifyKeccakStack + 8)) :
    Sep B.toNat k A.toNat n := by
  unfold InStk at hA; unfold Sep at *; omega

theorem stk_frame (c : Ctx a inst m0) {o n : Nat} (h : o + n ≤ 3352) : InStk m0 (off (fb m0) o) n := by
  have e := off_fb c (o := o) (by omega)
  have hK := c.K
  have := c.sp
  have := vk_eq
  unfold InStk
  rw [e]
  omega

theorem stk_callee (c : Ctx a inst m0) (ca : CallAt m0 wr oc mc) {N : Nat}
    (hN : 3344 - oc + N ≤ verifyKeccakStack) : InStk m0 (stackBelow mc N) (N + 8) := by
  have hb := ca.sb c hN
  have hK := c.K
  have := c.sp
  have := ca.oc8
  have := vk_eq
  unfold InStk
  rw [hb]
  omega

theorem stk_args (c : Ctx a inst m0) (ca : CallAt m0 wr oc mc) {j : Nat} (h : oc + 8 + 8 * j ≤ 3352) :
    InStk m0 (rspOf mc + 8#64) (8 * j) := by
  have hr := ca.rsp c
  have hK := c.K
  have := c.sp
  have := c.top
  have := vk_eq
  have e : (rspOf mc + 8#64).toNat = (rspOf mc).toNat + 8 := by
    rw [BitVec.toNat_add, show (8#64).toNat = 8 from rfl]; omega
  unfold InStk
  rw [e, hr]
  omega

/-- RSP at the frame's offset `oc`, from a block's result. -/
theorem rsp_of {env : Env} {S : SState} (hm : Match env S mc)
    (hb : env.regions[0]? = some (fb m0, 3368)) (hsp : S.reg .rsp = some (.ptr 0 (oc : Int)))
    (hoc : oc ≤ 3344) : rspOf mc = stackBelow m0 (3344 - oc) := by
  show mc.regs.get64 .rsp = _
  rw [hm.regs .rsp _ hsp, Sym.eval, Env.base_eq hb, BitVec.ofInt_natCast]
  exact NativeRustcVmX64.KeccakGkr.off_stackBelow hoc

omit [Labels] in
/-- The stack arguments' address as a frame offset. -/
theorem args_eq' (hsp : rspOf mc = stackBelow m0 (3344 - oc)) (hoc : oc ≤ 3344) :
    rspOf mc + 8#64 = off (fb m0) (oc + 8) := by
  rw [hsp]
  rw [← NativeRustcVmX64.KeccakGkr.off_stackBelow (m0 := m0) (F := 3344) (o := oc) (by omega),
    NativeRustcVm.Transcript.off_add]

theorem args_eq (ca : CallAt m0 wr oc mc) : rspOf mc + 8#64 = off (fb m0) (oc + 8) :=
  args_eq' ca.sp (by have := ca.oc8; omega)

/-- The stack arguments are mapped and in range. -/
theorem argsOk (c : Ctx a inst m0) (h : LayZ m0 3344 3368 verifyKeccakStack (rsOf m0))
    (ca : CallAt m0 wr oc mc) {j : Nat} (hj : oc + 8 + 8 * j ≤ 3368) : ArgsOk mc j := by
  have hr := ca.rsp c
  have := c.sp
  have := c.top
  refine ⟨?_, by omega⟩
  rw [args_eq ca]
  exact NativeRustcVmX64.Transcript.mapped_off (NativeRustcVm.Transcript.Mapped.keeps h.map ca.kept)
    (by omega)

/-- **A stack argument** a block wrote at the frame's offset `oc + 8 + 8 i`. -/
theorem stackArg_of {env : Env} {S : SState}
    (hm : Match env S mc) (hb : env.regions[0]? = some (fb m0, 3368))
    (hsp : S.reg .rsp = some (.ptr 0 (oc : Int))) (hoc : oc ≤ 3344) {i : Nat}
    (hi : oc + 16 + 8 * i ≤ 3368) {v : Sym}
    (hw : ∀ t < 8, findWrite 0 (oc + 8 + 8 * i + t) S.mem = some (v, t)) :
    stackArg mc i = v.eval env := by
  have h := NativeRustcVmX64.Transcript.wordAt_write hm hb (by omega) hw
  unfold stackArg
  have e : rspOf mc + BitVec.ofNat 64 (8 + 8 * i) = off (fb m0) (oc + 8 + 8 * i) := by
    rw [show off (fb m0) (oc + 8 + 8 * i) = off (fb m0) (oc + 8) + BitVec.ofNat 64 (8 * i) from
      (NativeRustcVm.Transcript.off_add _ _ _).symm, ← args_eq' (rsp_of hm hb hsp hoc) hoc,
      BitVec.add_assoc,
      ← BitVec.ofNat_add]
  rw [e, NativeRustcVm.wordOf_of_wordAt h]

/-- Two frame ranges apart. -/
theorem sepFF (c : Ctx a inst m0) {o1 n1 o2 n2 : Nat} (h1 : o1 + n1 ≤ 3368) (h2 : o2 + n2 ≤ 3368)
    (hp1 : 0 < n1) (hp2 : 0 < n2) (h : o1 + n1 ≤ o2 ∨ o2 + n2 ≤ o1) :
    Sep (off (fb m0) o1).toNat n1 (off (fb m0) o2).toNat n2 := by
  rw [off_fb c (by omega), off_fb c (by omega)]; unfold Sep; omega

/-- A frame range and a range apart from the stack. -/
theorem sepFX (c : Ctx a inst m0) {o n : Nat} (h : o + n ≤ 3352) {B : BitVec 64} {k : Nat}
    (hB : Sep B.toNat k (stackBelow m0 verifyKeccakStack).toNat (verifyKeccakStack + 8)) :
    Sep (off (fb m0) o).toNat n B.toNat k :=
  sep_stk (stk_frame c h) hB

/-- A callee's stack and a frame range above its RSP. -/
theorem sepSF (c : Ctx a inst m0) (ca : CallAt m0 wr oc mc) {N : Nat}
    (hN : 3344 - oc + N ≤ verifyKeccakStack) {o n : Nat} (ho : oc + 8 ≤ o) (hn : o + n ≤ 3368)
    (hn0 : 0 < n) :
    Sep (stackBelow mc N).toNat (N + 8) (off (fb m0) o).toNat n := by
  have hb := ca.sb c hN
  have := ca.oc8
  have := c.sp
  rw [hb, off_fb c (by omega)]
  unfold Sep
  omega

/-- The frame range at `o` is mapped at a call. -/
theorem mapF (h : LayZ m0 3344 3368 verifyKeccakStack (rsOf m0)) (ca : CallAt m0 wr oc mc)
    {o n : Nat} (hn : o + n ≤ 3368) : NativeRustcVm.Mapped mc.dmem (off (fb m0) o) n :=
  NativeRustcVmX64.Transcript.mapped_off (NativeRustcVm.Transcript.Mapped.keeps h.map ca.kept) hn

/-- Region `i`'s range at `o` is mapped at a call. -/
theorem mapR (h : LayZ m0 3344 3368 verifyKeccakStack (rsOf m0)) (ca : CallAt m0 wr oc mc)
    {i o n : Nat} (h1 : 1 ≤ i) (h4 : i ≤ 4) (hn : o + n ≤ rsz i) :
    NativeRustcVm.Mapped mc.dmem (off (ob m0 i) o) n :=
  NativeRustcVmX64.Transcript.mapped_off
    (NativeRustcVm.Transcript.Mapped.keeps (ob_mapped h h1 h4) ca.kept) hn

theorem nwF (c : Ctx a inst m0) {o n : Nat} (hn : o + n ≤ 3368) :
    (off (fb m0) o).toNat + n ≤ 2 ^ 64 := by
  by_cases h0 : n = 0
  · subst h0; exact Nat.le_of_lt (BitVec.isLt _)
  · rw [off_fb c (by omega)]; have := c.top; have := c.sp; have := vk_eq; omega

theorem nwR (c : Ctx a inst m0) {i o n : Nat} (h1 : 1 ≤ i) (h4 : i ≤ 4) (hn : o + n ≤ rsz i) :
    (off (ob m0 i) o).toNat + n ≤ 2 ^ 64 := by
  by_cases h0 : n = 0
  · subst h0; exact Nat.le_of_lt (BitVec.isLt _)
  have hw := ob_W c h1 h4
  rw [toNat_add_ofNat _ _ (by omega)]
  omega

/-- Region `i`'s range at `o` as a number. -/
theorem offR (c : Ctx a inst m0) {i o : Nat} (h1 : 1 ≤ i) (h4 : i ≤ 4) (ho : o < rsz i) :
    (off (ob m0 i) o).toNat = (ob m0 i).toNat + o := by
  have hw := ob_W c h1 h4
  exact toNat_add_ofNat _ _ (by omega)

/-- Region `i`'s range and a range the region is apart from. -/
theorem sepRX (c : Ctx a inst m0) {i o n : Nat} (h1 : 1 ≤ i) (h4 : i ≤ 4) (hn : o + n ≤ rsz i)
    (hn0 : 0 < n) {B : Nat} {k : Nat} (hB : Sep (ob m0 i).toNat (rsz i) B k) :
    Sep (off (ob m0 i) o).toNat n B k := by
  rw [offR c h1 h4 (by omega)]
  unfold Sep at *; omega

/-- Two ranges of different regions. -/
theorem sepRR (c : Ctx a inst m0) {i o n j p l : Nat} (h1 : 1 ≤ i) (h4 : i ≤ 4) (hn : o + n ≤ rsz i)
    (hn0 : 0 < n) (h1' : 1 ≤ j) (h4' : j ≤ 4) (hl : p + l ≤ rsz j) (hl0 : 0 < l) (hij : i ≠ j) :
    Sep (off (ob m0 i) o).toNat n (off (ob m0 j) p).toNat l := by
  have := ob_sep c h1 h4 h1' h4' hij
  rw [offR c h1 h4 (by omega), offR c h1' h4' (by omega)]
  unfold Sep at *; omega

/-- Region `i`'s range and a range apart from the stack. -/
theorem sepRF (c : Ctx a inst m0) {i o n : Nat} (h1 : 1 ≤ i) (h4 : i ≤ 4) (hn : o + n ≤ rsz i)
    (hn0 : 0 < n) {A : BitVec 64} {k : Nat} (hA : InStk m0 A k) :
    Sep (off (ob m0 i) o).toNat n A.toNat k := by
  have hS := ob_S c h1 h4
  have hK := c.K
  have := vk_eq
  have := c.sp
  rw [offR c h1 h4 (by omega)]
  unfold InStk at hA; unfold Sep; omega

end

/-! ## Byte images -/

section
variable {d d' d'' : Mem 64} {p q r : BitVec 64} {n : Nat}

theorem Img.trans (h : Img d p d' q n) (h' : Img d' q d'' r n) : Img d p d'' r n :=
  fun j hj b hb ↦ h' j hj b (h j hj b hb)

theorem Img.sub (h : Img d p d' q n) {o k : Nat} (hk : o + k ≤ n) :
    Img d (p + BitVec.ofNat 64 o) d' (q + BitVec.ofNat 64 o) k := fun j hj b hb ↦ by
  rw [NativeRustcVm.addr_add_add] at hb ⊢; exact h _ (by omega) b hb

theorem Img.append {n1 n2 : Nat} (h1 : Img d p d' q n1)
    (h2 : Img d (p + BitVec.ofNat 64 n1) d' (q + BitVec.ofNat 64 n1) n2) :
    Img d p d' q (n1 + n2) := fun j hj b hb ↦ by
  by_cases hj1 : j < n1
  · exact h1 j hj1 b hb
  · have := h2 (j - n1) (by omega) b
      (by rw [NativeRustcVm.addr_add_add, show n1 + (j - n1) = j by omega]; exact hb)
    rwa [NativeRustcVm.addr_add_add, show n1 + (j - n1) = j by omega] at this

/-- **Bytes copied by `memcpy`** as an image. -/
theorem Img.of_bytesOf {src dst : BitVec 64}
    (hcp : NativeRustcVm.BytesAt d' dst (NativeRustcX64.bytesOf d src n)) : Img d src d' dst n :=
  fun j hj b hb ↦ by
    have := hcp j (by simp [NativeRustcX64.bytesOf]; omega)
    rw [this]
    simp only [NativeRustcX64.bytesOf, List.getElem_map, List.getElem_range]
    rw [hb]; rfl

/-- **Unchanged bytes** as an image. -/
theorem Img.of_same (h : NativeRustcVm.Layout.Same d d' p n) : Img d p d' p n :=
  fun j hj b hb ↦ by rw [h j hj]; exact hb

/-- **One word written alike.** -/
theorem Img.of_word {w : UInt64} (h : NativeRustcVm.WordAt d p w)
    (h' : NativeRustcVm.WordAt d' q w) : Img d p d' q 8 := fun j hj b hb ↦ by
  have e := h j (by rw [NativeRustcVm.length_wordBytes]; exact hj)
  have e' := h' j (by rw [NativeRustcVm.length_wordBytes]; exact hj)
  rw [hb] at e
  rw [e', ← e]

theorem Img.bytesAt (h : Img d p d' q n) {o : Nat} {bs : List UInt8}
    (hb : NativeRustcVm.BytesAt d (p + BitVec.ofNat 64 o) bs) (hle : o + bs.length ≤ n) :
    NativeRustcVm.BytesAt d' (q + BitVec.ofNat 64 o) bs := fun i hi ↦ by
  have := hb i hi
  rw [NativeRustcVm.addr_add_add] at this ⊢
  exact h _ (by omega) _ this

theorem Img.bytesAt0 (h : Img d p d' q n) {bs : List UInt8} (hb : NativeRustcVm.BytesAt d p bs)
    (hle : bs.length ≤ n) : NativeRustcVm.BytesAt d' q bs := by
  have := h.bytesAt (o := 0) (by rw [NativeRustcVm.addr_add_zero]; exact hb) (by omega)
  rwa [NativeRustcVm.addr_add_zero] at this

theorem Img.bufEWAt (h : Img d p d' q n) {o N : Nat} {xs : List EW}
    (hb : NativeRustcVm.BufEWAt d (p + BitVec.ofNat 64 o) N xs) (hle : o + 8 + 16 * N ≤ n) :
    NativeRustcVm.BufEWAt d' (q + BitVec.ofNat 64 o) N xs := by
  obtain ⟨hl, hw, he⟩ := hb
  refine ⟨hl, h.bytesAt hw (by rw [NativeRustcVm.length_wordBytes]; omega), ?_⟩
  have e : ∀ x : BitVec 64, x + BitVec.ofNat 64 o + 8#64 = x + BitVec.ofNat 64 (o + 8) := fun x ↦
    NativeRustcVm.addr_add_add _ _ _
  rw [e] at he ⊢
  exact h.bytesAt he (by rw [NativeRustcVm.length_ewsBytes]; omega)

/-- **A claim but its bit weights** moves with its 768 bytes. -/
theorem ClaimAt.img {c : KeccakClaimW} (h : ClaimAt d p c) (hi : Img d p d' q 768) :
    ClaimAt d' q c :=
  ⟨hi.bytesAt0 h.1 (by rw [NativeRustcVm.length_ewBytes]; omega), hi.bufEWAt h.2.1 (by decide),
    hi.bufEWAt h.2.2 (by decide)⟩

/-- Elements move with their bytes. -/
theorem Img.ewsAt (h : Img d p d' q n) {xs : List EW} (hb : NativeRustcVm.EWsAt d p xs)
    (hle : 16 * xs.length ≤ n) : NativeRustcVm.EWsAt d' q xs :=
  h.bytesAt0 hb (by rw [NativeRustcVm.length_ewsBytes]; omega)

end

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak
