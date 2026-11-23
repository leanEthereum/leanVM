module

public import NativeRustcVmArm.Sumcheck.Common
public import NativeRustcVmArm.Spec.Sumcheck

/-!
# Calls from a frame on the transcript

A function entered in `m0` with `N` bytes of stack (its callees' included), holding the `TState`
at `t` with its decoded area `a`, whose frame is `F` bytes below the entry's SP (`Ctx`). In a
state `m` at its frame (`At`: SP `F` bytes down, the entry's bytes kept, the round constants'
bytes the same), a callee with `Nc` bytes of stack, `F + Nc ≤ N`, gets its `StackOk`, `RcAt`,
`TStateOk`, `SpongeOk` (`Ctx.stackOk`, …), and a range of the frame is an `OutOk` output
(`Ctx.outOk`) and apart from the callee's stack (`Ctx.apart_frame`).
-/

namespace NativeRustcVmArm.Sumcheck

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Transcript NativeVm.Model

@[expose] public section

/-- The function's context: its stack, the round constants, the `TState` and its area apart from
the stack and each other, a frame of `F ≤ N` bytes (a multiple of `16`). -/
structure Ctx [Labels] (m0 : MachineData) (t : BitVec 64) (a : DecArea) (N F : Nat) : Prop where
  stack : StackOk m0 N
  rc : RcAt m0 N
  tok : TStateOk m0 t a N
  fp : Footprint m0.dmem t a
  le : F ≤ N
  al : F % 16 = 0

/-- The frame's address. -/
def frAt (m0 : MachineData) (F : Nat) : BitVec 64 := m0.regs.SP.toBitVec - BitVec.ofNat 64 F

/-- The state `m` at the frame: SP `F` bytes down, the entry's bytes kept, the round constants'
bytes the same. -/
structure At [Labels] (m0 : MachineData) (F : Nat) (m : MachineData) : Prop where
  sp : m.regs.SP.toBitVec = frAt m0 F
  kept : Kept m0.dmem m.dmem
  rc : ∀ p, InRange rcAddr 192 p → m.dmem.get? p = m0.dmem.get? p

end

public section

variable [Labels] {m0 m : MachineData} {t : BitVec 64} {a : DecArea} {N F Nc : Nat}

namespace Ctx

theorem spN (c : Ctx m0 t a N F) : N ≤ m0.regs.SP.toNat := c.stack.2.1

theorem stk (c : Ctx m0 t a N F) : (stackBelow m0 N).toNat = m0.regs.SP.toNat - N :=
  toNat_stackBelow c.spN

omit [Labels] in
theorem sp_lt (m : MachineData) : m.regs.SP.toNat < 2 ^ 64 := m.regs.SP.toBitVec.isLt

theorem fr (c : Ctx m0 t a N F) : (frAt m0 F).toNat = m0.regs.SP.toNat - F :=
  NativeRustcVm.toNat_sub_ofNat (by have := c.spN; have := c.le; show F ≤ m0.regs.SP.toNat; omega)

theorem spN' (c : Ctx m0 t a N F) (h : At m0 F m) : m.regs.SP.toNat = m0.regs.SP.toNat - F := by
  show m.regs.SP.toBitVec.toNat = _
  rw [h.sp, c.fr]

theorem stackOk (c : Ctx m0 t a N F) (h : At m0 F m) (hle : F + Nc ≤ N) : StackOk m Nc :=
  StackOk.sub c.stack h.sp c.al hle h.kept

theorem rcAt (c : Ctx m0 t a N F) (h : At m0 F m) (hle : F + Nc ≤ N) : RcAt m Nc :=
  RcAt.sub c.rc h.sp hle c.spN h.rc

/-- A range apart from the function's stack is apart from the callee's. -/
theorem apart (c : Ctx m0 t a N F) (h : At m0 F m) (hle : F + Nc ≤ N) {x : BitVec 64} {n : Nat}
    (hx : Apart x n (stackBelow m0 N) N) : Apart x n (stackBelow m Nc) Nc :=
  Apart.stack_sub hx h.sp hle c.spN

theorem tstateOk (c : Ctx m0 t a N F) (h : At m0 F m) (hle : F + Nc ≤ N) :
    TStateOk m t a Nc :=
  ⟨c.apart h hle c.tok.1, c.apart h hle c.tok.2.1, c.tok.2.2⟩

/-- A range of the frame is apart from the callee's stack. -/
theorem apart_frame (c : Ctx m0 t a N F) (h : At m0 F m) (hle : F + Nc ≤ N) {o n : Nat}
    (hon : o + n ≤ F) : Apart (frAt m0 F + BitVec.ofNat 64 o) n (stackBelow m Nc) Nc := by
  have := c.spN; have := c.le
  have hs := c.spN' h
  have hl := sp_lt m0
  refine apart_above ?_ (by rw [hs]; omega)
  rw [NativeRustcVm.toNat_add_ofNat (by rw [c.fr]; omega), c.fr, hs]
  omega

/-- A range of the frame as numbers. -/
theorem frame_toNat (c : Ctx m0 t a N F) {o : Nat} (ho : o ≤ F) :
    (frAt m0 F + BitVec.ofNat 64 o).toNat = m0.regs.SP.toNat - F + o := by
  have := c.spN; have := c.le
  have hl := sp_lt m0
  rw [NativeRustcVm.toNat_add_ofNat (by rw [c.fr]; omega), c.fr]

/-- A range of the frame is apart from what is apart from the function's stack. -/
theorem apart_of_stack (c : Ctx m0 t a N F) {x : BitVec 64} {n o k : Nat} (hok : o + k ≤ F)
    (hx : Apart x n (stackBelow m0 N) N) : Apart (frAt m0 F + BitVec.ofNat 64 o) k x n := by
  have := c.spN; have := c.le
  unfold Apart at hx ⊢
  rw [c.stk] at hx
  rw [c.frame_toNat (by omega)]
  omega

/-- A range of the frame is data memory at the entry. -/
theorem mapped_frame0 (c : Ctx m0 t a N F) {o n : Nat} (hon : o + n ≤ F) :
    Mapped m0.dmem (frAt m0 F + BitVec.ofNat 64 o) n := by
  have := c.spN; have := c.le
  intro i hi
  have e : frAt m0 F + BitVec.ofNat 64 o + BitVec.ofNat 64 i =
      m0.regs.SP.toBitVec - BitVec.ofNat 64 N + BitVec.ofNat 64 (N - F + o + i) := by
    rw [NativeRustcVm.addr_add_add]
    apply BitVec.eq_of_toNat_eq
    have e1 : (m0.regs.SP.toBitVec - BitVec.ofNat 64 N).toNat = m0.regs.SP.toNat - N := c.stk
    have hl := sp_lt m0
    rw [c.frame_toNat (by omega), NativeRustcVm.toNat_add_ofNat (by rw [e1]; omega), e1]
    omega
  rw [e]
  exact c.stack.2.2 _ (by omega)

/-- A range of the frame is data memory. -/
theorem mapped_frame (c : Ctx m0 t a N F) (h : At m0 F m) {o n : Nat} (hon : o + n ≤ F) :
    Mapped m.dmem (frAt m0 F + BitVec.ofNat 64 o) n :=
  fun i hi ↦ h.kept _ (c.mapped_frame0 hon i hi)

theorem noWrap_frame (c : Ctx m0 t a N F) {o n : Nat} (hon : o + n ≤ F) :
    NoWrap (frAt m0 F + BitVec.ofNat 64 o) n := by
  have := c.spN; have := c.le
  unfold NoWrap
  rw [c.frame_toNat (by omega)]
  have hl := sp_lt m0
  omega

theorem mapped_fr (c : Ctx m0 t a N F) (h : At m0 F m) : Mapped m.dmem (frAt m0 F) F := by
  have := c.mapped_frame (o := 0) (n := F) h (by omega)
  rwa [NativeRustcVm.addr_add_zero] at this

theorem noWrap_fr (c : Ctx m0 t a N F) : NoWrap (frAt m0 F) F := by
  have := c.noWrap_frame (o := 0) (n := F) (by omega)
  rwa [NativeRustcVm.addr_add_zero] at this

/-- **A range of the frame as an output** of a callee. -/
theorem outOk (c : Ctx m0 t a N F) (h : At m0 F m) (hle : F + Nc ≤ N) {o n : Nat}
    (hon : o + n ≤ F) : OutOk m t a (frAt m0 F + BitVec.ofNat 64 o) n Nc :=
  ⟨c.mapped_frame h hon, c.noWrap_frame hon, c.apart_of_stack hon c.tok.1,
    c.apart_of_stack hon c.tok.2.1, c.apart_frame h hle hon, c.apart_of_stack hon c.rc.2.2⟩

/-- **The sponge** of the `TState` for a callee. -/
theorem spongeOk (c : Ctx m0 t a N F) (h : At m0 F m) (hle : F + Nc ≤ N) :
    SpongeOk m t Nc := by
  have ht := c.fp.1
  have hsz : (⟨t, tstateBytes⟩ : NativeRustcVm.Region).size = 760 := rfl
  refine ⟨fun i hi ↦ h.kept _ (ht.1 i (by unfold spongeBytes at hi; omega)),
    NativeRustcVm.NoWrap.mono ht.2 (by unfold spongeBytes; omega),
    c.apart h hle (NativeRustcVm.Apart.mono c.tok.1 (Nat.le_refl _)
      (by unfold spongeBytes tstateBytes; omega) (Nat.le_refl _) (Nat.le_refl _)),
    NativeRustcVm.Apart.mono c.tok.2.2 (Nat.le_refl _) (by unfold spongeBytes tstateBytes; omega)
      (Nat.le_refl _) (Nat.le_refl _)⟩

/-- The callee's stack is in the function's. -/
theorem inRange_stack (c : Ctx m0 t a N F) (h : At m0 F m) (hle : F + Nc ≤ N) {p : BitVec 64}
    (hp : InRange (stackBelow m Nc) Nc p) : InRange (stackBelow m0 N) N p := by
  have := c.spN
  have hs := c.spN' h
  have hl := sp_lt m0
  have e : (stackBelow m Nc).toNat = m.regs.SP.toNat - Nc := toNat_stackBelow (by omega)
  rw [Sym.inRange_iff (by rw [e]; omega), e] at hp
  rw [Sym.inRange_iff (by rw [c.stk]; omega), c.stk]
  omega

/-- The frame is in the function's stack. -/
theorem inRange_frame (c : Ctx m0 t a N F) {p : BitVec 64} (hp : InRange (frAt m0 F) F p) :
    InRange (stackBelow m0 N) N p := by
  have := c.spN; have := c.le
  have hl := sp_lt m0
  rw [Sym.inRange_iff (by rw [c.fr]; omega), c.fr] at hp
  rw [Sym.inRange_iff (by rw [c.stk]; omega), c.stk]
  omega

/-- An output apart from the function's stack is one of a callee's. -/
theorem outOk_sub (c : Ctx m0 t a N F) (h : At m0 F m) (hle : F + Nc ≤ N) {o : BitVec 64}
    {n : Nat} (ho : OutOk m0 t a o n N) : OutOk m t a o n Nc :=
  ⟨fun i hi ↦ h.kept _ (ho.1 i hi), ho.2.1, ho.2.2.1, ho.2.2.2.1, c.apart h hle ho.2.2.2.2.1,
    ho.2.2.2.2.2⟩

/-- A state at the frame from the changes since the entry, apart from the round constants. -/
theorem at_of (_c : Ctx m0 t a N F) {R : BitVec 64 → Prop}
    (hR : ∀ p, R p → ¬ InRange rcAddr 192 p) (hs : SameOutside m0.dmem m.dmem R)
    (hk : Kept m0.dmem m.dmem) (hsp : m.regs.SP.toBitVec = frAt m0 F) : At m0 F m :=
  ⟨hsp, hk, fun p hp ↦ hs p fun h ↦ hR p h hp⟩

/-- The round constants are apart from the function's stack. -/
theorem not_rc_stack (c : Ctx m0 t a N F) {p : BitVec 64} (hp : InRange (stackBelow m0 N) N p) :
    ¬ InRange rcAddr 192 p :=
  NativeRustcVm.Apart.not_inRange c.rc.2.2.symm
    (by unfold NativeRustcVm.NoWrap; rw [c.stk]; have := c.spN; have := sp_lt m0; omega)
    c.rc.2.1 hp

/-- The round constants are apart from the `TState`. -/
theorem not_rc_tstate (c : Ctx m0 t a N F) {p : BitVec 64} (hp : InRange t tstateBytes p) :
    ¬ InRange rcAddr 192 p :=
  NativeRustcVm.Apart.not_inRange c.tok.2.2 c.fp.1.2 c.rc.2.1 hp

end Ctx

end

end NativeRustcVmArm.Sumcheck
