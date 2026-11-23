module

public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Whir.FoldRound.Exit

/-!
# `fold_round`: what calls keep, `read_scalar`

The state kept by changes in the entry's stack, the output and the `TState` (`ws_keep`), a
callee's stack inside the entry's (`stack_sub`); `read_scalar` into the frame's `Option<EW>` at 88
(`rs_call`); the tag and the element read back (`tag8`, `tag4`, `elem0`, `elem1`).
-/

namespace NativeRustcVmArm.Whir.FoldRound

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.FoldRound

public section

section
variable [Labels] {a : DecArea} {s : TState} {w : WhirStateW} {m0 : MachineData}

/-- The entry's stack, the output, the `TState`: what calls and blocks write before the end. -/
@[expose] def Away (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (stackBelow m0 foldRoundStack) foldRoundStack q ∨ InRange (oA m0) 40 q ∨
    InRange (tA m0) tstateBytes q

/-- **The state kept** by changes away from it. -/
theorem ws_keep (h : FoldRoundPre a s w m0) {d d' : Mem 64} (hws : WhirStateAt d (pA m0) w)
    {R : BitVec 64 → Prop} (hs : SameOutside d d' R) (hR : ∀ q, R q → Away m0 q) :
    WhirStateAt d' (pA m0) w := by
  have hN := pre_hN h
  obtain ⟨-, hts, -, -, ⟨hpo, -⟩, ⟨hoo, -⟩, hap⟩ := h
  have hnp : NoWrap (pA m0) stateBytes := hpo.2.1
  have hnt : NoWrap (tA m0) tstateBytes := hts.footprint.1.2
  refine hws.agree (NativeRustcVmArm.Whir.agree_of_sameOutside hs fun j hj _ hq ↦ ?_)
  have hin : InRange (pA m0) stateBytes (off (pA m0) j) :=
    NativeRustcVm.Transcript.inRange_off_self hj (by unfold NoWrap at hnp; omega)
  rcases hR _ hq with hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange hpo.2.2.2.2.1 hnp (base_noWrap hN) hin hq
  · exact NativeRustcVm.Apart.not_inRange (NativeRustcVm.Apart.symm hap) hnp hoo.2.1 hin hq
  · exact NativeRustcVm.Apart.not_inRange hpo.2.2.1 hnp hnt hin hq

/-- A callee's stack below the frame is in the entry's. -/
theorem stack_sub (h : FoldRoundPre a s w m0) {st : MachineData} (hf : FFr m0 st) {N' : Nat}
    (hle : 208 + N' ≤ foldRoundStack) {q : BitVec 64}
    (hq : InRange (stackBelow st N') N' q) :
    InRange (stackBelow m0 foldRoundStack) foldRoundStack q := by
  have hN := pre_hN h
  rw [stackBelow_eq hf.sp (by omega)] at hq
  have e1 := base_toNat (m0 := m0) (F := 208 + N') (by omega)
  have e2 := base_toNat (m0 := m0) (F := foldRoundStack) hN
  have := m0.regs.SP.toNat_lt
  rw [Sym.inRange_iff (by omega)] at hq
  rw [show stackBelow m0 foldRoundStack = base m0 foldRoundStack from rfl,
    Sym.inRange_iff (by omega)]
  omega

/-- The frame is in the entry's stack. -/
theorem frame_away (h : FoldRoundPre a s w m0) {q : BitVec 64}
    (hq : InRange (base m0 208) 208 q) : Away m0 q :=
  .inl (frame_sub (pre_hN h) (by rw [stack_eq]; decide) hq)

/-- The frame is apart from the `TState` and its decoded area. -/
theorem frame_not_t (h : FoldRoundPre a s w m0) {q : BitVec 64}
    (hq : InRange (base m0 208) 208 q) :
    ¬InRange (tA m0) tstateBytes q ∧ ¬InRange a.words (8 * a.len) q := by
  have hN := pre_hN h
  have hs := frame_sub hN (by rw [stack_eq]; decide) hq
  have htok := h.1.2.2.2.1
  have hfp := h.2.1.footprint
  have hnt : NoWrap (tA m0) tstateBytes := hfp.1.2
  have hnd : NoWrap a.words (8 * a.len) := hfp.2.1.2
  exact ⟨fun ht ↦ NativeRustcVm.Apart.not_inRange htok.1 hnt (base_noWrap hN) ht hs,
    fun hd ↦ NativeRustcVm.Apart.not_inRange htok.2.1 hnd (base_noWrap hN) hd hs⟩

/-- The `Option<EW>`'s bytes are in the frame. -/
theorem loc88_frame (h : FoldRoundPre a s w m0) {q : BitVec 64}
    (hq : InRange (loc m0 88) 24 q) : InRange (base m0 208) 208 q :=
  NativeRustcVm.InRange.of_sub hq (base_noWrap (by
    have := pre_hN h; rw [stack_eq] at this; omega)) (by decide)

/-! ## Reading back the `Option<EW>` -/

omit [Labels] in
theorem tag8 {env : Env} (hb0 : env.base 0 = base m0 208) {r : Option EW}
    (ht : OptEWAt env.mem0 (loc m0 88) r) :
    env.load 0 88 8 = BitVec.ofNat 64 (if r.isSome then 1 else 0) := by
  cases r with
  | none => rw [load_word (by rw [hb0]; exact ht)]; rfl
  | some x => rw [load_word (by rw [hb0]; exact ht.1)]; rfl

omit [Labels] in
theorem tag4 {env : Env} (hb0 : env.base 0 = base m0 208) {r : Option EW}
    (ht : OptEWAt env.mem0 (loc m0 88) r) :
    env.load 0 88 4 = BitVec.ofNat 64 (if r.isSome then 1 else 0) := by
  have key : ∀ v : UInt64, NativeRustcVm.WordAt env.mem0 (loc m0 88) v →
      env.load 0 88 4 = BitVec.ofInt 64 (Int.ofBytes ((NativeRustcVm.wordBytes v).take 4)) :=
    fun v hv ↦ Env.load_of_bytesAt (by simp [NativeRustcVm.length_wordBytes])
      (by rw [hb0]; exact NativeRustcVm.BytesAt.take hv 4)
  cases r with
  | none => rw [key 0 ht]; decide
  | some x => rw [key 1 ht.1]; simp only [Option.isSome_some, ↓reduceIte]; decide

omit [Labels] in
theorem elem0 {env : Env} (hb0 : env.base 0 = base m0 208) {x : EW}
    (ht : OptEWAt env.mem0 (loc m0 88) (some x)) : env.load 0 96 8 = x.c0.toBitVec := by
  have := ht.2.left (bs := NativeRustcVm.wordBytes x.c0)
  rw [load_word (v := x.c0) (by
    rw [hb0, show base m0 208 + BitVec.ofNat 64 96 = off (loc m0 88) 8 by
      rw [off, NativeRustcVm.addr_add_add]]
    exact this)]

omit [Labels] in
theorem elem1 {env : Env} (hb0 : env.base 0 = base m0 208) {x : EW}
    (ht : OptEWAt env.mem0 (loc m0 88) (some x)) : env.load 0 104 8 = x.c1.toBitVec := by
  have := ht.2.right (bs := NativeRustcVm.wordBytes x.c0)
  rw [NativeRustcVm.length_wordBytes] at this
  rw [load_word (v := x.c1) (by
    rw [hb0, show base m0 208 + BitVec.ofNat 64 104 = off (loc m0 88) 8 + BitVec.ofNat 64 8 by
      rw [off, NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add]]
    exact this)]

end

/-! ## `read_scalar` -/

section
variable [Host] {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData}

/-- **`read_scalar`** into the frame's `Option<EW>` at 88, from the `TState`'s state `s`. -/
theorem rs_call (h : FoldRoundPre a s0 w m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    {st : MachineState} {next : Int64} {R : MachineState → Prop} (hb : Base w m0 st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel ∧ retOf st.data = next)
    (hx0 : st.data.regs.X0.toBitVec = loc m0 88) (hx1 : st.data.regs.X1 = m0.regs.X1)
    {s : TState} (hts : TStateAt st.data.dmem (tA m0) a s)
    (cont : ∀ m2, Base w m0 m2 → OptEWAt m2.dmem (loc m0 88) ((readScalar.run s).map (·.1)) →
      NextAt m2.dmem (tA m0) a (readScalar.run s) →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (fun q ↦ InRange (loc m0 88) 24 q ∨
        InRange (tA m0) tstateBytes q ∨
        InRange (stackBelow st.data readScalarStack) readScalarStack q) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have c := ctx h
  have hle : 208 + readScalarStack ≤ foldRoundStack := by decide
  have ht1 : st.data.regs.X1.toBitVec = tA m0 := by rw [hx1]
  have hpre : ReadScalarPre a s st.data := by
    refine ⟨c.stackOk hb.fr hle, c.rcAt hb.fr hle, ?_, ?_, ?_⟩
    · show TStateAt st.data.dmem st.data.regs.X1.toBitVec a s
      rw [ht1]; exact hts
    · show TStateOk st.data st.data.regs.X1.toBitVec a readScalarStack
      rw [ht1]; exact c.tstateOk hb.fr hle
    · show OutOk st.data st.data.regs.X1.toBitVec a st.data.regs.X0.toBitVec 24 readScalarStack
      rw [ht1, hx0]; exact c.localOk hb.fr hle (by decide)
  refine Fr.callW hb.fr (pre_hN h) hle (fun _ h ↦ by cases h) slots_le c.frame_outs (o := 88)
    (n := 24) (by decide) (by decide)
    (spec_with (hrs s) fun m ↦ m.regs.X0.toBitVec = loc m0 88 ∧ m.regs.X1.toBitVec = tA m0)
    (fun m m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.1.2.2.1 fun q hq' ↦ by
      obtain ⟨-, h0, h1⟩ := hq
      rcases hq' with hq' | hq' | hq'
      · rw [h0] at hq'; exact .inr (.inl hq')
      · rw [h1] at hq'; exact .inr (.inr (.inr (.inr hq')))
      · exact .inl hq', hq.1.2.2.2⟩) hpc ⟨hpre, hx0, ht1⟩ fun m2 hf2 hq hcs ↦ ?_
  obtain ⟨⟨hopt, hnext, hs, -⟩, -, -⟩ := hq
  simp only [hx0, ht1] at hopt hnext hs
  refine cont m2 ⟨hf2, ?_, ?_, ?_, ?_⟩ hopt hnext hcs (NativeRustcVm.SameOutside.mono hs
    fun q hq ↦ by rcases hq with hq | hq | hq <;> simp_all)
  · exact (hcs .X19 rfl).trans hb.x19
  · exact (hcs .X20 rfl).trans hb.x20
  · exact (hcs .X23 rfl).trans hb.x23
  · refine ws_keep h hb.ws hs fun q hq ↦ ?_
    rcases hq with hq | hq | hq
    · exact frame_away h (loc88_frame h hq)
    · exact .inr (.inr hq)
    · exact .inl (stack_sub h hb.fr hle hq)

end

end

end NativeRustcVmArm.Whir.FoldRound
