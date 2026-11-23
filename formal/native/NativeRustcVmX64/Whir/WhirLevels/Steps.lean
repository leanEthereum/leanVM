module

public import NativeRustcVmX64.Whir.WhirLevels.Basic
public import NativeRustcVmX64.Got

/-!
# `whir_levels`: blocks, calls, conditions (x86-64)

`Ctx.blk`: a body block (in `frameEnv`, writing the frame below offset `hi`) keeps the frame and
changes only those bytes; the `TState`, the state, the frame's words across it (`Ctx.ts_blk`,
`Ctx.ws_blk`, `keepW`). `Ctx.call`: a callee whose changes are its stack below the frame and the
outputs keeps the frame and its bytes. `Frame.tail`: the registers restored before the tail call,
RSP the entry's. The exits' conditions (`c1_eval`, `c3_eval`, `c4_eval`, `c6_eval`) and `b4`'s
`μ` (`v9_eval`).
The entry's loader slots remain unchanged across these writes (`Ctx.got_bytes`); `Ctx.got_call`
transports their separation to ordinary calls and the final tail call.
-/

namespace NativeRustcVmX64.Whir.Levels.WL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck

public section

theorem apart_sub {a b : BitVec 64} {n m o k : Nat} (h : NativeRustcVm.Apart a n b m)
    (hnw : NativeRustcVm.NoWrap a n) (hk : o + k ≤ n) :
    NativeRustcVm.Apart (a + BitVec.ofNat 64 o) k b m := by
  unfold NativeRustcVm.NoWrap at hnw
  have := NativeRustcVm.toNat_add_ofNat_le (a := a) (i := o) (by omega)
  unfold NativeRustcVm.Apart at h ⊢
  omega

theorem noWrap_sub {a : BitVec 64} {n o k : Nat} (hnw : NativeRustcVm.NoWrap a n)
    (hk : o + k ≤ n) : NativeRustcVm.NoWrap (a + BitVec.ofNat 64 o) k :=
  NativeRustcVm.NoWrap.sub hnw hk

theorem whirIn_sub {m : MachineData} {x : BitVec 64} {n N o k : Nat} (h : WhirIn m x n N)
    (hk : o + k ≤ n) : WhirIn m (x + BitVec.ofNat 64 o) k N :=
  ⟨⟨fun i hi ↦ by rw [NativeRustcVm.addr_add_add]; exact h.1.1 _ (by omega),
    noWrap_sub h.1.2 hk⟩, apart_sub h.2 h.1.2 hk⟩

theorem outOk_sub [Labels] {m : MachineData} {t : BitVec 64} {a : DecArea} {x : BitVec 64}
    {n N o k : Nat} (h : OutOk m t a x n N) (hk : o + k ≤ n) :
    OutOk m t a (x + BitVec.ofNat 64 o) k N :=
  ⟨fun i hi ↦ by rw [NativeRustcVm.addr_add_add]; exact h.1 _ (by omega), noWrap_sub h.2.1 hk,
    apart_sub h.2.2.1 h.2.1 hk, apart_sub h.2.2.2.1 h.2.1 hk, apart_sub h.2.2.2.2.1 h.2.1 hk,
    apart_sub h.2.2.2.2.2 h.2.1 hk⟩

theorem whirOut_sub [Labels] {m : MachineData} {t : BitVec 64} {a : DecArea} {x : BitVec 64}
    {n N o k : Nat} (h : WhirOut m t a x n N) (hk : o + k ≤ n) :
    WhirOut m t a (x + BitVec.ofNat 64 o) k N :=
  ⟨outOk_sub h.1 hk, fun t' ↦ apart_sub (h.2 t') h.1.2.1 hk⟩

theorem level_le {len k : Nat} (hk : k < len) : levelBytes * k + levelBytes ≤ levelBytes * len := by
  have := Nat.mul_le_mul_left levelBytes (show k + 1 ≤ len by omega)
  rw [Nat.mul_succ] at this
  exact this

/-- `ret`'s address in a state with the same RSP and the same bytes at it. -/
theorem retOf_congr {m m' : MachineData} (hsp : rspOf m' = rspOf m)
    (hmap : NativeRustcVm.Mapped m.dmem (rspOf m) 8)
    (hb : ∀ j < 8, m'.dmem.get? (rspOf m + BitVec.ofNat 64 j) =
      m.dmem.get? (rspOf m + BitVec.ofNat 64 j)) : retOf m' = retOf m := by
  have hget : ∀ j < 8, m.dmem.get? (rspOf m + BitVec.ofNat 64 j) =
      some ((m.dmem.get? (rspOf m + BitVec.ofNat 64 j)).getD 0) := fun j hj ↦ by
    have := hmap j hj
    revert this
    cases m.dmem.get? (rspOf m + BitVec.ofNat 64 j) <;> simp
  unfold retOf
  rw [hsp, loadInt_of_get? _ _ 8 _ fun j hj ↦ (hb j hj).trans (hget j hj),
    loadInt_of_get? _ _ 8 _ hget]

/-- **The tail call's epilogue**: the registers restored, RSP the entry's. -/
theorem Frame.tail [Labels] {m0 d d' : MachineData} {o : Nat} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState} (hf : Frame m0 112 slots o d)
    (hwf : (frameEnv m0 d 112 rest vars ret).WF)
    (hm : Match (frameEnv m0 d 112 rest vars ret) S d') (hS : TailOk S) :
    Saved m0 d' ∧ rspOf d' = rspOf m0 ∧ d'.dmem = d.dmem := by
  obtain ⟨hl, hk, hsp, hmem, -⟩ := hS
  have hslot : ∀ p ∈ slots, reg d' p.2 = reg m0 p.2 := by
    intro p hp
    unfold slotsLoaded at hl
    rw [List.all_eq_true] at hl
    have := hm.regs p.2 _ (by simpa using hl p hp)
    rw [Sym.eval, load_ofMachine (o := p.1) rfl (hf.slot p hp)] at this
    exact this
  have hd : d'.dmem = d.dmem := hm.dmem_eq hwf hmem
  refine ⟨⟨fun r hr ↦ ?_, by rw [hd]; exact hf.kept⟩, ?_, hd⟩
  · cases hs : slots.any (·.2 == r)
    · have := hm.regs r _ (keepsOthers_spec hk hr hs)
      rw [Sym.eval, Env.ofMachine_regs] at this
      exact this.trans (hf.regs r hr hs)
    · obtain ⟨p, hp, hpr⟩ := List.any_eq_true.mp hs
      rw [← Reg64.eq_of_beq hpr]
      exact hslot p hp
  · show d'.regs.get64 .rsp = _
    rw [hm.regs .rsp _ hsp]
    exact (eval_ptr0 (F := 112) 112).trans off_frame_F

/-! ## Conditions -/

section
variable [Labels] (env : Env)

theorem c1_eval (h : env.regs .r12 ≠ 0) : c1.eval env = false := by
  simp only [c1, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
    BitVec.and_self]
  simpa using h

theorem c3_eval : c3.eval env = decide ((env.regs .rax).toNat % 256 = 0) := by
  simp only [c3, SBool.eval, Sym.eval]
  exact testAl_eq _

theorem c6_eval : c6.eval env = !decide ((env.regs .rax).toNat % 256 = 0) := by
  simp only [c6, SBool.eval, Sym.eval]
  rw [testAl_eq]

theorem c4_eval {k n : Nat} (hk : k < n) (hn : n < 2 ^ 32)
    (h13 : env.regs .r13 = BitVec.ofNat 64 k - 1#64)
    (h48 : env.load 0 48 8 = 1#64 - BitVec.ofNat 64 n) :
    c4.eval env = decide (k + 1 = n) := by
  simp only [c4, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, h13, h48]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat,
    show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl]
  constructor <;> intro h <;> omega

theorem v9_eval {x y : BitVec 64} (hx : env.load 0 56 8 = x) (hy : env.load 1 16 8 = y) :
    (v9.eval env).toNat = x.toNat - y.toNat := by
  simp only [v9, Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, hx, hy]
  split
  · rename_i h
    simp only [Bool.not_eq_true', BitVec.ult, decide_eq_false_iff_not, Nat.not_lt] at h
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact h)]
  · rename_i h
    simp only [Bool.not_eq_true, Bool.not_eq_false', BitVec.ult, decide_eq_true_eq] at h
    simp
    omega

end

section
variable [Labels] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat} {o : Nat}

namespace Ctx

variable (c : Ctx a s0 levels ba b claim m0 rate)
include c

/-- Stack and output writes leave both loader slots unchanged. -/
theorem got_bytes {d : MachineData} (hs : Sm m0 d) :
    ∀ l ∈ ["memcpy", "memset"], ∀ i < 8,
      d.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
        m0.dmem.get? (gotAddr l + BitVec.ofNat 64 i) := by
  have hg := c.got.areas (areas' := [(tA m0, tstateBytes), (pA m0, whirBytes)])
    (by intro ar har; simp only [List.mem_cons, List.not_mem_nil, or_false] at har
        rcases har with rfl | rfl <;> simp)
  apply NativeRustcVmX64.GotAt.unchanged_vm hg c.stack
  · intro ar har
    simp only [List.mem_cons, List.not_mem_nil, or_false] at har
    rcases har with rfl | rfl
    · exact c.ts0.footprint.1.2
    · exact c.pout.1.2.1
  · intro q hq
    apply hs q
    rintro (hst | hp | ht)
    · exact hq (.inl hst)
    · exact hq (.inr ⟨(pA m0, whirBytes), by simp, hp⟩)
    · exact hq (.inr ⟨(tA m0, tstateBytes), by simp, ht⟩)

/-- Ordinary and tail callees use contained stack and input/output areas. -/
theorem got_call {d : MachineData} {F N : Nat} (hat : At m0 F d) (hs : Sm m0 d)
    (hle : F + N ≤ whirLevelsStack) {areas : List (BitVec 64 × Nat)}
    {symbols : List Label} (hlabels : symbols.Sublist ["memcpy", "memset"])
    (hcover : ∀ ar ∈ areas, ∃ b ∈ (stackBelow m0 whirLevelsStack, whirLevelsStack + 8) ::
      ([(tA m0, tstateBytes), (a.words, 8 * a.len), (pA m0, whirBytes),
        (lvA m0, levelBytes * levels.length), (rspOf m0 + 8#64, 8)] ++ rodataAreas),
      b.1.toNat ≤ ar.1.toNat ∧ ar.1.toNat + ar.2 ≤ b.1.toNat + b.2) :
    GotAt d N areas symbols := by
  have hsb : stackBelow d N = stackBelow m0 (F + N) :=
    stackBelow_callee hat.sp (by have := c.hN; omega)
  have hd := stackBelow_toNat (m := m0) (n := F + N) (by have := c.hN; omega)
  apply NativeRustcVmX64.GotAt.callee (c.got.symbols hlabels)
    (fun l hl i hi ↦ c.got_bytes hs l (hlabels.subset hl) i hi) _ _ hcover <;>
    rw [hsb, hd, c.stk_toNat] <;> have := c.hN <;> omega

/-- A local argument word is protected by the caller's stack separation. -/
theorem got_loc {areas : List (BitVec 64 × Nat)} {j n : Nat} (hjn : j + n ≤ 120) :
    ∃ b ∈ (stackBelow m0 whirLevelsStack, whirLevelsStack + 8) :: areas,
      b.1.toNat ≤ (off (fa m0) j).toNat ∧
        (off (fa m0) j).toNat + n ≤ b.1.toNat + b.2 := by
  have hj : (fa m0).toNat + j < 2 ^ 64 := by
    rw [c.fa_toNat]
    have := c.hN
    have := frame_le
    have := c.sp16
    omega
  refine ⟨(stackBelow m0 whirLevelsStack, whirLevelsStack + 8), by simp, ?_, ?_⟩ <;>
    rw [toNat_off hj, c.fa_toNat, c.stk_toNat] <;>
    have := c.hN <;> have := frame_le <;> omega

/-- A single level is contained in the protected level array. -/
theorem got_level {k : Nat} (hk : k < levels.length) :
    ∃ b ∈ (stackBelow m0 whirLevelsStack, whirLevelsStack + 8) ::
      ([(tA m0, tstateBytes), (a.words, 8 * a.len), (pA m0, whirBytes),
        (lvA m0, levelBytes * levels.length), (rspOf m0 + 8#64, 8)] ++ rodataAreas),
      b.1.toNat ≤ (lvA m0 + BitVec.ofNat 64 (levelBytes * k)).toNat ∧
        (lvA m0 + BitVec.ofNat 64 (levelBytes * k)).toNat + levelBytes ≤ b.1.toNat + b.2 := by
  have hle := level_le hk
  have hnw : (lvA m0).toNat + levelBytes * levels.length ≤ 2 ^ 64 := c.lin.1.2
  have hadd := NativeRustcVm.toNat_add_ofNat (a := lvA m0) (i := levelBytes * k)
    (by have : 0 < levelBytes := by decide
        omega)
  refine ⟨(lvA m0, levelBytes * levels.length), by simp, ?_⟩
  change (lvA m0).toNat ≤ (lvA m0 + BitVec.ofNat 64 (levelBytes * k)).toNat ∧
    (lvA m0 + BitVec.ofNat 64 (levelBytes * k)).toNat + levelBytes ≤
      (lvA m0).toNat + levelBytes * levels.length
  rw [hadd]
  constructor <;> omega

/-- The frame's region below offset `hi ≤ 112` is in the stack. -/
theorem frame_stack {hi : Nat} (hhi : hi ≤ 112) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (fa m0) hi q) :
    NativeRustcVm.InRange (stackBelow m0 whirLevelsStack) whirLevelsStack q :=
  c.sctx.inRange_frame (inRange_mono hq hhi)

/-- The frame's region misses the `TState`, its area and the state. -/
theorem frame_not {hi : Nat} (hhi : hi ≤ 112) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (fa m0) hi q) :
    ¬NativeRustcVm.InRange (tA m0) tstateBytes q ∧ ¬NativeRustcVm.InRange a.words (8 * a.len) q ∧
      ¬NativeRustcVm.InRange (pA m0) whirBytes q :=
  ⟨(c.sctx.stack_not_t (c.frame_stack hhi hq)).1, (c.sctx.stack_not_t (c.frame_stack hhi hq)).2,
    fun hp ↦ c.outs_not_frame (Or.inl hp) (inRange_mono hq (by omega))⟩

/-- The frame's environment is well formed with regions `rest` apart from the frame. -/
theorem wf {d : MachineData} (hk : Kept m0.dmem d.dmem) {rest : List (BitVec 64 × Nat)}
    {ret : BitVec 64}
    (hrest : ∀ x ∈ rest, NativeRustcVm.Mapped d.dmem x.1 x.2 ∧ NativeRustcVm.NoWrap x.1 x.2)
    (hap : ((fa m0, 120) :: rest).Pairwise fun x y ↦ NativeRustcVm.Apart x.1 x.2 y.1 y.2) :
    (frameEnv m0 d 112 rest (fun _ ↦ 0) ret).WF :=
  frame_wf (c.frame_ok hk) hrest hap

/-- **A body block** keeps the frame; it writes the frame below offset `hi`. -/
theorem blk {d d' : MachineData} {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} {S : SState}
    {o' : Nat} (hf : Fr m0 o d) (hwf : (frameEnv m0 d 112 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (frameEnv m0 d 112 rest (fun _ ↦ 0) ret) S d')
    (hmid : MidOk 112 o' slots S = true) {hi : Nat} (hhi : hi ≤ 112)
    (hw : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ hi) :
    Fr m0 o' d' ∧ NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (fa m0) hi) := by
  have hs : NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (fa m0) hi) :=
    sameOutside_low hwf hm (r := 0) rfl (by omega) hw
  refine ⟨⟨Frame.of_block hf.frame hwf hm hmid slots_le, NativeRustcVm.SameOutside.mono
    (hf.same.trans hs) fun q hq ↦ ?_⟩, hs⟩
  rcases hq with hq | hq
  · exact hq
  · exact Or.inl (c.frame_stack hhi hq)

/-- The `TState` across a change of the frame. -/
theorem ts_frame {d d' : MachineData} {hi : Nat} (hhi : hi ≤ 112) (hk : Kept d.dmem d'.dmem)
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (fa m0) hi)) {s : TState}
    (ht : TStateAt d.dmem (tA m0) a s) : TStateAt d'.dmem (tA m0) a s :=
  ht.frame hk (fun _ hq ↦ ⟨(c.frame_not hhi hq).1, (c.frame_not hhi hq).2.1⟩) hs

/-- The state's bytes across a change of the frame. -/
theorem same_frame {d d' : MachineData} {hi : Nat} (hhi : hi ≤ 112)
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (fa m0) hi)) :
    NativeRustcVm.Layout.Same d.dmem d'.dmem (pA m0) whirBytes :=
  NativeRustcVm.Layout.Same.of_sameOutside hs fun j hj hq ↦ (c.frame_not hhi hq).2.2
    (NativeRustcVm.inRange_add hj (by unfold whirBytes; omega))

/-- **A call** whose changes are its stack below the frame and the outputs keeps the frame and
its bytes. -/
theorem call {d d' : MachineData} (hf : Fr m0 0 d) {N' : Nat} (hle : 112 + N' ≤ whirLevelsStack)
    (hsv : Saved d d') (hrsp : rspOf d' = rspOf d + 8#64) {rs : List NativeRustcVm.Region}
    (hrs : ∀ q, NativeRustcVm.InAny rs q → outs m0 q) (hch : ChangesIn d d' N' rs) :
    Fr m0 8 d' ∧ ∀ j < 120, d'.dmem.get? (off (fa m0) j) = d.dmem.get? (off (fa m0) j) := by
  have hat := c.at_call hf
  have hR : ∀ q, (NativeRustcVm.InAny rs q ∨
      NativeRustcVm.InRange (stackBelow d N') N' q) →
      ¬NativeRustcVm.InRange (stackBelow m0 112) (112 + 8) q := fun q hq ↦ by
    rcases hq with hq | hq
    · exact fun h ↦ c.outs_not_frame (hrs q hq) (inRange_mono h (by omega))
    · exact (c.sctx.inRange_callee hat hle hq).2
  refine ⟨⟨Frame.call hf.frame hsv hrsp hch hR c.sctx.noWrap_frame slots_le,
    NativeRustcVm.SameOutside.mono (hf.same.trans hch) fun q hq ↦ ?_⟩, fun j hj ↦ hch _ ?_⟩
  · rcases hq with (hq | hq) | (hq | hq)
    · exact Or.inl hq
    · exact Or.inr hq
    · exact Or.inr (hrs q hq)
    · exact Or.inl (c.sctx.inRange_callee hat hle hq).1
  · have := c.sctx.noWrap_frame
    unfold NativeRustcVm.NoWrap at this
    exact fun h ↦ hR _ h (inRange_off_self hj (by omega))

/-- The `TState` across a call. -/
theorem ts_call {d d' : MachineData} (hf : Fr m0 0 d) {N' : Nat}
    (hle : 112 + N' ≤ whirLevelsStack) (hsv : Saved d d') {rs : List NativeRustcVm.Region}
    (hrs : ∀ q, NativeRustcVm.InAny rs q → ¬NativeRustcVm.InRange (tA m0) tstateBytes q ∧
      ¬NativeRustcVm.InRange a.words (8 * a.len) q)
    (hch : ChangesIn d d' N' rs) {s : TState} (ht : TStateAt d.dmem (tA m0) a s) :
    TStateAt d'.dmem (tA m0) a s := by
  have hat := c.at_call hf
  refine ht.frame hsv.2 (fun q hq ↦ ?_) hch
  rcases hq with hq | hq
  · exact hrs q hq
  · exact c.sctx.stack_not_t (c.sctx.inRange_callee hat hle hq).1

end Ctx

end

end

end NativeRustcVmX64.Whir.Levels.WL
