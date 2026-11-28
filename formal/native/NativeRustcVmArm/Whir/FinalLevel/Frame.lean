module

public import NativeRustcVmArm.Whir.FinalLevel.Exit
public import NativeRustcVmArm.Whir.MathFrame

/-!
# `final_level`: calls and blocks in the frame

`Ctx.call`: a call from a state of the frame writing its stack, the frame's bytes `[lo, lo + n)`
(below the slots) and the outputs. The frame's bytes kept by such a call (`Ctx.same_call`) and by
a block whose writes miss them (`Ctx.same_block`); the `TState` kept by a block writing the frame
alone (`Ctx.ts_block`); a block writing the frame below the slots keeps the frame
(`Ctx.fr_block`). The frame's bytes as a callee's input (`Ctx.locIn`, `Ctx.locSlice`) and apart
from an input (`Ctx.apart_loc`). `roundsOf_of_roundsAt`: the rounds read back.
-/

namespace NativeRustcVmArm.Whir.FinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.FinalLevel
open NativeRustcVmArm.Transcript (known_ptr load_ofMachine wordAt_write)

public section

theorem roundsOf_succ (d : Mem 64) (p : BitVec 64) (n : Nat) :
    roundsOf d p (n + 1) =
      ⟨NativeRustcVm.ewOf d p, NativeRustcVm.ewOf d (p + BitVec.ofNat 64 16)⟩ ::
      roundsOf d (p + BitVec.ofNat 64 32) n := by
  unfold roundsOf
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  refine List.cons_eq_cons.mpr ⟨by simp, List.map_congr_left fun i _ ↦ ?_⟩
  simp only [Function.comp, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 4 <;> omega

/-- The rounds read back. -/
theorem roundsOf_of_roundsAt {d : Mem 64} {p : BitVec 64} {rs : List FoldRoundW}
    (h : RoundsAt d p rs) : roundsOf d p rs.length = rs := by
  induction rs generalizing p with
  | nil => rfl
  | cons r rs ih =>
    unfold RoundsAt at h
    rw [show roundEWs (r :: rs) = r.alpha :: r.beta :: roundEWs rs from rfl, ewsAt_cons,
      ewsAt_cons, off_off] at h
    obtain ⟨ha, hb, hr⟩ := h
    rw [List.length_cons, roundsOf_succ, NativeRustcVm.ewOf_of_ewAt ha,
      show p + BitVec.ofNat 64 16 = off p 16 from rfl, NativeRustcVm.ewOf_of_ewAt hb,
      show p + BitVec.ofNat 64 32 = off p (16 + 16) from rfl, ih hr]

/-! ## Branch conditions -/

section
variable [Labels] {env : Env}

/-- `cbz w0` on a verdict. -/
theorem cbz_ok {b : Bool} (h : env.regs .X0 = (okWord b).toBitVec) :
    SBool.eval env (.cmp .eq .W32 (.reg .X0) (.lit 0)) = !b := by
  sym_simp; rw [h]; cases b <;> decide

/-- `tbz w0, #0` on a verdict. -/
theorem tbz_ok {b : Bool} (h : env.regs .X0 = (okWord b).toBitVec) :
    SBool.eval env (.not (.bit .W32 (.reg .X0) 0)) = !b := by
  sym_simp; rw [h]; cases b <;> decide

/-- `cbz x8` on a word loaded from the frame. -/
theorem cbz_load {o : Nat} {v : UInt64} (h : env.load 0 o 8 = v.toBitVec) :
    SBool.eval env (.cmp .eq .W64 (.load 0 o 8) (.lit 0)) = (v == 0) := by
  sym_simp; rw [h, toBitVec_beq_zero]
  by_cases hv : v = 0 <;> simp [hv]

end

section
variable [Labels] {a : DecArea} {s0 : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData}

namespace Ctx

variable (c : Ctx a s0 level ba b w rounds m0)
include c

/-- The frame's byte `o` as a number. -/
theorem loc_nat {o : Nat} (ho : o ≤ 2672) : (loc m0 o).toNat = m0.regs.SP.toNat - 2672 + o :=
  loc_toNat (by have := c.hN'; omega) ho

/-- An input apart from the entry's stack is apart from the frame's bytes. -/
theorem apart_loc {x : BitVec 64} {n o len : Nat} (h : WhirIn m0 x n finalLevelStack)
    (hol : o + len ≤ 2672) : Apart x n (loc m0 o) len := by
  have h2 := h.2
  have hN := c.hN'
  unfold OffStack Apart at h2
  rw [toNat_stackBelow c.hN, stack_eq] at h2
  unfold Apart
  rw [c.loc_nat (by omega)]
  omega

/-- The frame's bytes `[o, o + n)` for a callee using `N'` bytes below the frame. -/
theorem locIn {st : MachineData} (hf : FFr m0 st) {N' : Nat} (hle : 2672 + N' ≤ finalLevelStack)
    {o n : Nat} (hon : o + n ≤ 2672) : WhirIn st (loc m0 o) n N' :=
  have h := c.localOk' hf hle hon
  ⟨⟨h.1, h.2.1⟩, h.2.2.2.2.1⟩

/-- A slice of the frame for a callee. -/
theorem locSlice {st : MachineData} (hf : FFr m0 st) {N' : Nat}
    (hle : 2672 + N' ≤ finalLevelStack) {o : Nat} {n : UInt64} (hon : o + 16 * n.toNat ≤ 2672) :
    SliceOk st (UInt64.ofBitVec (loc m0 o)) n N' :=
  c.locIn hf hle hon

/-- The frame's bytes `[o, o + len)` kept by a call writing `[lo, lo + n)` of it, its stack and
the outputs. -/
theorem same_call {st : MachineData} (hf : FFr m0 st) {N' : Nat}
    (hle : 2672 + N' ≤ finalLevelStack) {d' : Mem 64} {lo n : Nat}
    (hs : SameOutside st.dmem d' fun q ↦
      InRange (stackBelow st N') N' q ∨ InRange (loc m0 lo) n q ∨ outs m0 q)
    {o len : Nat} (hol : o + len ≤ 2672) (hd : o + len ≤ lo ∨ lo + n ≤ o) (hln : lo + n ≤ 2672) :
    NativeRustcVm.Layout.Same st.dmem d' (loc m0 o) len := by
  have hN := c.hN'
  have hsp := m0.regs.SP.toNat_lt
  refine NativeRustcVm.Layout.Same.of_sameOutside hs fun j hj hq ↦ ?_
  have hq0 : (loc m0 o + BitVec.ofNat 64 j).toNat = m0.regs.SP.toNat - 2672 + o + j := by
    rw [NativeRustcVm.toNat_add_ofNat (by rw [c.loc_nat (o := o) (by omega)]; omega),
      c.loc_nat (o := o) (by omega)]
  have hN2 := c.hN
  rcases hq with hq | hq | hq
  · have hb := base_toNat (m0 := m0) (F := 2672 + N') (by omega)
    have hnw : NoWrap (base m0 (2672 + N')) N' := by unfold NoWrap; rw [hb]; omega
    rw [stackBelow_eq hf.sp (N' := N') (by omega)] at hq
    have := (Sym.inRange_iff hnw).mp hq
    rw [hb, hq0] at this
    omega
  · have hlo : NoWrap (loc m0 lo) n := by unfold NoWrap; rw [c.loc_nat (o := lo) (by omega)]; omega
    have := (Sym.inRange_iff hlo).mp hq
    rw [c.loc_nat (o := lo) (by omega), hq0] at this
    omega
  · refine c.outs_not_frame (F := 2672) (by rw [stack_eq]; decide) hq ?_
    rw [Sym.inRange_iff (base_noWrap (by omega)), hq0, base_toNat (by omega)]
    omega

omit c in
/-- The frame's bytes `[o, o + len)` kept by a block whose writes miss them. -/
theorem same_block {st st' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (fenv m0 st rs) S st') (hwf : (fenv m0 st rs).WF) {o len : Nat}
    (hmiss : missFrame S o len = true) (hol : o + len ≤ 2672) :
    NativeRustcVm.Layout.Same st.dmem st'.dmem (loc m0 o) len := by
  have hnw := hwf.noWrap 0 (base m0 2672) 2672 rfl
  refine NativeRustcVm.Layout.Same.of_sameOutside (hm.sameOutside hwf)
    fun i hi ⟨w, hw, b', sz, hb', h1, h2⟩ ↦ ?_
  rw [NativeRustcVm.addr_add_add, NativeRustcVm.toNat_add_ofNat (by omega)]
    at h1 h2
  simp only [missAt, List.all_eq_true] at hmiss
  have := hmiss w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    bne_iff_ne, ne_eq] at this
  rcases this with ⟨hr, hd⟩ | ⟨hr, hsz⟩
  · rw [hr] at hb'
    cases hb'
    omega
  · split at hsz
    · rename_i sz' al hreg
      obtain ⟨b'', hb'', -⟩ := hm.regions _ _ _ hreg
      rw [hb'] at hb''
      cases hb''
      have := hwf.disjoint w.r 0 b' (base m0 2672) sz 2672 hr hb' rfl
      simp only [decide_eq_true_eq] at hsz
      omega
    · cases hsz

/-- **The `TState` kept** by a block writing the frame alone. -/
theorem ts_block {st st' : MachineData} {rs : List (BitVec 64 × Nat)} {S : SState} {s : TState}
    (hm : Match (fenv m0 st rs) S st') (hwf : (fenv m0 st rs).WF)
    (hS : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 2672) (hts : TStateAt st.dmem (tA m0) a s) :
    TStateAt st'.dmem (tA m0) a s := by
  have hN := c.hN
  have hfp := c.ts0.footprint
  refine hts.frame (hm.kept hwf) (fun q hq ↦ ?_) (NativeRustcVm.SameOutside.mono
    (hm.sameOutside hwf) fun q hq ↦ written_r0 hwf rfl hS hq)
  have hs := frame_sub hN (by rw [stack_eq]; decide) hq
  exact ⟨fun ht ↦ NativeRustcVm.Apart.not_inRange c.tok.1 c.tnw (base_noWrap hN) ht hs,
    fun hd ↦ NativeRustcVm.Apart.not_inRange c.tok.2.1 hfp.2.1.2 (base_noWrap hN) hd hs⟩

/-- **A block writing the frame below the slots** keeps the frame. -/
theorem fr_block {st st' : MachineData} {rs : List (BitVec 64 × Nat)} {S S' : SState}
    (hf : FFr m0 st) (hm : Match (fenv m0 st rs) S st) (hm' : Match (fenv m0 st rs) S' st')
    (hwf : (fenv m0 st rs).WF) (hsp : S'.sp = S.sp)
    (hS : ∀ w ∈ S'.mem, w.r = 0 ∧ w.off + w.n ≤ 2576) : FFr m0 st' :=
  Fr.ofBlockW hf hm hm' hwf rfl hsp (fun _ h ↦ by cases h) rfl (by rw [stack_eq]; decide) c.hN
    slots_le fun w hw ↦ .inl ⟨(hS w hw).1, by have := (hS w hw).2; omega, fun p hp ↦ .inl (by
      have := (hS w hw).2; have := slots_ge p hp; omega)⟩

end Ctx

end

section
variable [Host] {a : DecArea} {s0 : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData}

/-- **A call** writing its stack, the frame's bytes `[lo, lo + n)` and the outputs. -/
theorem Ctx.call (c : Ctx a s0 level ba b w rounds m0) {st : MachineState} (hf : FFr m0 st.data)
    {l : Label} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} {N' lo n : Nat} {next : Int64}
    {R : MachineState → Prop} (hle : 2672 + N' ≤ finalLevelStack) (hlo : lo + n ≤ 2576)
    (hspec : Spec (Labels.label l) P Q) (hpc : st.pc = Labels.label l ∧ retOf st.data = next)
    (hP : P st.data)
    (hQ : ∀ m', Q st.data m' → SameOutside st.data.dmem m'.dmem (fun q ↦
      InRange (stackBelow st.data N') N' q ∨ InRange (loc m0 lo) n q ∨ outs m0 q) ∧
        Saved st.data m')
    (cont : ∀ m2, FFr m0 m2 → Q st.data m2 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st :=
  Fr.leafIn hf c.hN hle (by omega) (fun _ h ↦ by cases h)
    (fun p hp ↦ ⟨slots_le p hp, .inr (by have := slots_ge p hp; omega)⟩)
    (fun q hq ↦ c.outs_not_frame (by rw [stack_eq]; decide) hq) hspec hpc hP hQ cont

end

end

end NativeRustcVmArm.Whir.FinalLevel
