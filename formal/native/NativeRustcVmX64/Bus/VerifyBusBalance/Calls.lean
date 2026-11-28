module

public import NativeRustcVmX64.Bus.VerifyBusBalance.Common

/-!
# `verify_bus_balance`'s callees, its locals (x86-64)

A callee entered with RSP at the frame's offset `c` (its return address at `[c, c + 8)`) using
`Nc` bytes below it, `5520 - c + Nc ≤ NN`:

- `cal_stack`, `cal_rc`, `cal_ro`, `cal_tok`, `cal_out`, `cal_local`, `cal_in`: its stack, the
  round constants, the read-only data, the `TState`, an output, a local of the frame from
  `c + 8` as an output, an input;
- `callF`: the call (`Gkr.Fr.call`), its changes in its stack, the outputs and a local.

The locals kept, by intervals (`KeepIv`): through a block (`keepIv_block`, its writes in the
frame between `lo` and `hi`), through a call (`keepIv_call`).
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus NativeRustcVm.Layout

/-! ## Numbers -/

public section

variable {m0 : MachineData}

theorem rsp_ge (hS : StackOk m0 NN) : NN ≤ (rspOf m0).toNat := hS.1
theorem rsp_top (hS : StackOk m0 NN) : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hS.2.1

theorem nn_eq : NN = 5520 + accumulateSideStack := by decide

/-- A range of the frame as an interval. -/
theorem inR_loc (hS : StackOk m0 NN) {j n : Nat} (hjn : j + n ≤ 5528) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (loc m0 j) n q) :
    (rspOf m0).toNat - 5520 + j ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - 5520 + j + n := by
  have := rsp_ge hS
  have := rsp_top hS
  have := N_ge
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; exact absurd hq (by unfold NativeRustcVm.InRange; omega)
  rw [inRange_toNat (by rw [loc_toNat hS (by omega)]; omega), loc_toNat hS (by omega)] at hq
  exact hq

/-- The frame's byte `j` in a range of the frame. -/
theorem loc_inR (hS : StackOk m0 NN) {j o n : Nat} (h1 : o ≤ j) (h2 : j < o + n)
    (hon : o + n ≤ 5528) : NativeRustcVm.InRange (loc m0 o) n (loc m0 j) := by
  have := rsp_ge hS
  have := rsp_top hS
  have := N_ge
  rw [inRange_toNat (by rw [loc_toNat hS (by omega)]; omega), loc_toNat hS (by omega),
    loc_toNat hS (by omega)]
  omega

/-- A callee's stack, RSP at the frame's offset `c`, as an interval. -/
theorem callee_iv (hS : StackOk m0 NN) {c Nc : Nat} {st : MachineData}
    (hsp : rspOf st = loc m0 c) (hc : c ≤ 5520) (hle : 5520 - c + Nc ≤ NN) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow st Nc) Nc q) :
    (rspOf m0).toNat - 5520 + c - Nc ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - 5520 + c := by
  have := rsp_ge hS
  have := rsp_top hS
  have := N_ge
  have hsp' : (rspOf st).toNat = (rspOf m0).toNat - 5520 + c := by
    rw [hsp, loc_toNat hS (by omega)]
  have hcb : (stackBelow st Nc).toNat = (rspOf m0).toNat - 5520 + c - Nc := by
    rw [stackBelow_toNat (by omega), hsp']
  rcases Nat.eq_zero_or_pos Nc with h0 | h0
  · subst h0; exact absurd hq (by unfold NativeRustcVm.InRange; omega)
  rw [inRange_toNat (by rw [hcb]; omega), hcb] at hq
  omega

/-- Two ranges of the frame apart. -/
theorem loc_apart (hS : StackOk m0 NN) {o n o' n' : Nat} (h1 : o + n ≤ 5520) (h2 : o' + n' ≤ 5520)
    (hd : o + n ≤ o' ∨ o' + n' ≤ o) : NativeRustcVm.Apart (loc m0 o) n (loc m0 o') n' := by
  have := rsp_ge hS
  have := rsp_top hS
  have := N_ge
  unfold NativeRustcVm.Apart
  rw [loc_toNat hS (by omega), loc_toNat hS (by omega)]
  omega

/-- What is apart from the stack is apart from a range of the frame. -/
theorem apart_loc (hS : StackOk m0 NN) {x : BitVec 64} {n : Nat}
    (hx : NativeRustcVm.Apart x n (stackBelow m0 NN) (NN + 8)) {j l : Nat} (hjl : j + l ≤ 5520) :
    NativeRustcVm.Apart x n (loc m0 j) l := by
  have := rsp_ge hS
  have := rsp_top hS
  have := N_ge
  unfold NativeRustcVm.Apart at hx ⊢
  rw [stackBelow_toNat (rsp_ge hS)] at hx
  rw [loc_toNat hS (by omega)]
  omega

/-- A range of the frame is not a byte apart from the stack. -/
theorem not_loc (hS : StackOk m0 NN) {x : BitVec 64} {n : Nat}
    (hx : NativeRustcVm.Apart x n (stackBelow m0 NN) (NN + 8)) (hxn : NativeRustcVm.NoWrap x n)
    {j l : Nat} (hjl : j + l ≤ 5520) {q : BitVec 64} (hq : NativeRustcVm.InRange x n q) :
    ¬ NativeRustcVm.InRange (loc m0 j) l q := fun h' ↦ by
  have := inR_loc hS (by omega) h'
  have := rsp_ge hS
  have := N_ge
  unfold NativeRustcVm.Apart at hx
  rw [stackBelow_toNat (rsp_ge hS)] at hx
  rw [inRange_toNat hxn] at hq
  omega

end

/-! ## A callee's facts -/

public section
variable [Labels] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

/-- The entry's context, for a frame of `F'` bytes. -/
theorem ctxF (h : VerifyBusBalancePre a s0 L m0) {F' : Nat} (hF : F' ≤ NN) :
    Ctx m0 (reg m0 .rdi) a NN F' :=
  ⟨pre_stack h, pre_rc h, pre_tok h, (pre_ts h).footprint, hF⟩

/-- **The read-only data kept** where the memory changed in the stack and the outputs. -/
theorem ro_keep (h : VerifyBusBalancePre a s0 L m0) {d : Mem 64}
    (hs : NativeRustcVm.SameOutside m0.dmem d
      (fun q ↦ NativeRustcVm.InRange (stackBelow m0 NN) NN q ∨ outs m0 q))
    (t : NativeRustcVm.Data.Item) : NativeRustcVm.BytesAt d (rodataAddr t) t.bytes := by
  have hR := pre_ro h
  have hsb := noWrap_stackBelow (pre_stack h)
  refine NativeRustcVm.BytesAt.of_sameOutside (hR t).1 hs fun i hi hq ↦ ?_
  rcases hq with hq | hq | hq | hq
  · exact (hR t).2.2.not_inRange_add (hR t).2.1 hsb hi (inRange_mono hq (by omega))
  · exact ((pre_tR h) t).symm.not_inRange_add (hR t).2.1 (pre_ts h).footprint.1.2 hi hq
  · exact ((pre_busR h) t).symm.not_inRange_add (hR t).2.1 (pre_bus h).2.1 hi hq
  · exact ((pre_clR h) t).symm.not_inRange_add (hR t).2.1 (pre_cl h).2.1 hi hq

section
variable (h : VerifyBusBalancePre a s0 L m0) {c Nc : Nat} {d : MachineData} (fr : St m0 c d)
  (hc : c ≤ 5472) (hle : 5520 - c + Nc ≤ NN)
include h fr hc hle

omit hle in
theorem cal_at : At m0 (5520 - c) d := fr.at_ (ctx h) (by omega) (outs_not_rc h)

theorem cal_stack : StackOk d Nc := (ctxF h (by omega)).stackOk (cal_at h fr hc) hle
theorem cal_rc : RcAt d Nc := (ctxF h (by omega)).rcAt (cal_at h fr hc) hle
theorem cal_tok : TStateOk d (reg m0 .rdi) a Nc :=
  (ctxF h (by omega)).tstateOk (cal_at h fr hc) hle

/-- Pass just the slots reached by a callee, with the caller's preserved bytes. -/
theorem cal_got {symbols : List Label} (hs : symbols.Sublist ["memcpy", "memset"])
    {areas : List (BitVec 64 × Nat)}
    (ha : ∀ l ∈ ["memcpy", "memset"], ∀ b ∈ areas, Apart (gotAddr l) 8 b.1 b.2) :
    GotAt d Nc areas symbols :=
  got_callee ((pre_got h).symbols hs)
    (fun l hl => got_same h fr l (hs.subset hl))
    (cal_at h fr hc).sp (pre_stack h).1 hle
    (fun l hl => ha l (hs.subset hl))

theorem cal_out {o : BitVec 64} {n : Nat} (ho : OutOk m0 (reg m0 .rdi) a o n NN) :
    OutOk d (reg m0 .rdi) a o n Nc :=
  (ctxF h (by omega)).outOk (cal_at h fr hc) hle ho

theorem cal_local {j n : Nat} (hj : c + 8 ≤ j) (hjn : j + n ≤ 5520) :
    OutOk d (reg m0 .rdi) a (loc m0 j) n Nc := by
  have e : loc m0 j = off (stackBelow m0 (5520 - c)) (j - c) := by
    rw [← off_fb (pre_stack h) N_ge (show c ≤ 5520 by omega), off_off]
    congr 1
    omega
  rw [e]
  exact (ctxF h (by omega)).outOk_frame (cal_at h fr hc) hle (by omega) (by omega)

theorem cal_localIn {j n : Nat} (hj : c + 8 ≤ j) (hjn : j + n ≤ 5520) :
    InOk d (loc m0 j) n Nc :=
  have ho := cal_local h fr hc hle hj hjn
  ⟨⟨ho.1, ho.2.1⟩, ho.2.2.2.2.1⟩

theorem cal_in {x : BitVec 64} {n : Nat} (hx : InOk m0 x n NN) : InOk d x n Nc :=
  ⟨⟨Mapped.keeps hx.1.1 fr.frame.kept, hx.1.2⟩,
    apart_callee hx.2 (cal_at h fr hc).sp (rsp_ge (pre_stack h)) hle⟩

theorem cal_ro : RodataAt d Nc := fun t ↦
  ⟨ro_keep h fr.same t, ((pre_ro h) t).2.1,
    apart_callee ((pre_ro h) t).2.2 (cal_at h fr hc).sp (rsp_ge (pre_stack h)) hle⟩

end

end

/-! ## Calls -/

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

/-- **A call from the frame** at offset `c`: the callee's contract, its changes in its stack below
`c`, the outputs and `len` bytes of the frame at `lo`. -/
theorem callF (h : VerifyBusBalancePre a s0 L m0) {c Nc lo len : Nat} (hc : c ≤ 5472)
    (hle : 5520 - c + Nc ≤ NN) (hlo : lo + len ≤ 5472) {X : BitVec 64 → Prop}
    (hX : ∀ q, X q → outs m0 q ∨ NativeRustcVm.InRange (loc m0 lo) len q)
    {l : Label} {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    (hspec : Spec (Labels.label l) P Q) {st : MachineState} {next : Int64}
    {R : MachineState → Prop} (fr : St m0 c st.data)
    (hpc : st.pc = Labels.label l ∧ retOf st.data = next) (hP : P st.data)
    (hQ : ∀ m', Q st.data m' → NativeRustcVm.SameOutside st.data.dmem m'.dmem
      (fun q ↦ NativeRustcVm.InRange (stackBelow st.data Nc) Nc q ∨ X q) ∧ Saved st.data m')
    (cont : ∀ m2 : MachineData, St m0 (c + 8) m2 → Q st.data m2 →
      NativeRustcVm.SameOutside st.data.dmem m2.dmem
        (fun q ↦ NativeRustcVm.InRange (stackBelow st.data Nc) Nc q ∨ X q) →
      (∀ r, calleeSaved r = true → m2.regs.get64 r = st.data.regs.get64 r) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st :=
  Fr.call (pre_stack h) N_ge (by omega) hle (slots_call hc hlo) (by omega) (outs_not_frame h) hX
    hspec fr hpc hP hQ cont

end

/-! ## Locals kept, by intervals -/

public section

/-- The byte `j` is in one of the intervals `[lo, hi)`. -/
@[expose] def InIv (ivs : List (Nat × Nat)) (j : Nat) : Prop := ∃ p ∈ ivs, p.1 ≤ j ∧ j < p.2

/-- The frame's bytes in the intervals the same. -/
@[expose] def KeepIv (ivs : List (Nat × Nat)) (m0 : MachineData) (d d' : Mem 64) : Prop :=
  ∀ j, InIv ivs j → Same d d' (loc m0 j) 1

variable {ivs : List (Nat × Nat)} {m0 : MachineData}

theorem KeepIv.trans {d d' d'' : Mem 64} (h : KeepIv ivs m0 d d') (h' : KeepIv ivs m0 d' d'') :
    KeepIv ivs m0 d d'' := fun j hj ↦ (h j hj).trans (h' j hj)

theorem KeepIv.rfl' {d d' : Mem 64} (h : d' = d) : KeepIv ivs m0 d d' := fun _ _ _ _ ↦ by rw [h]

/-- **`n` bytes at `o` kept**, within the interval `[lo, hi)`. -/
theorem KeepIv.sameIn {d d' : Mem 64} (h : KeepIv ivs m0 d d') {lo hi : Nat} (hm : (lo, hi) ∈ ivs)
    {o n : Nat} (h1 : lo ≤ o) (h2 : o + n ≤ hi) : Same d d' (loc m0 o) n := fun j hj ↦ by
  have := h (o + j) ⟨(lo, hi), hm, by simp only; omega, by simp only; omega⟩ 0 (by omega)
  rw [off_add, Nat.add_zero] at this
  rw [show loc m0 o + BitVec.ofNat 64 j = off (fb m0) (o + j) from off_add _ _ _]
  exact this

theorem inIv_lt {B : Nat} (h : ivs.all (fun p ↦ decide (p.2 ≤ B)) = true) {j : Nat}
    (hj : InIv ivs j) : j < B := by
  obtain ⟨p, hp, h1, h2⟩ := hj
  have := List.all_eq_true.mp h p hp
  simp only [decide_eq_true_eq] at this
  omega

theorem inIv_ge {c : Nat} (h : ivs.all (fun p ↦ decide (c ≤ p.1)) = true) {j : Nat}
    (hj : InIv ivs j) : c ≤ j := by
  obtain ⟨p, hp, h1, h2⟩ := hj
  have := List.all_eq_true.mp h p hp
  simp only [decide_eq_true_eq] at this
  omega

theorem inIv_apart {o n : Nat} (h : ivs.all (fun p ↦ decide (p.2 ≤ o) || decide (o + n ≤ p.1)) = true)
    {j : Nat} (hj : InIv ivs j) : j < o ∨ o + n ≤ j := by
  obtain ⟨p, hp, h1, h2⟩ := hj
  have := List.all_eq_true.mp h p hp
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  omega

theorem W0.reg0 {S : SState} {lo hi : Nat} (h : W0 lo hi S) :
    ∀ w ∈ S.mem, w.r = 0 → lo ≤ w.off ∧ w.off + w.n ≤ hi := fun w hw _ ↦
  ⟨(h w hw).2.1, (h w hw).2.2⟩

theorem W01.reg0 {S : SState} {lo hi lo1 n : Nat} (h : W01 lo hi lo1 n S) :
    ∀ w ∈ S.mem, w.r = 0 → lo ≤ w.off ∧ w.off + w.n ≤ hi := fun w hw hr ↦ by
  rcases h w hw with h' | h'
  · exact ⟨h'.2.1, h'.2.2⟩
  · omega

/-- **A block's changes keep the intervals**: its writes in the frame between `lo` and `hi`. -/
theorem keepIv_block [Labels] {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} {S : SState}
    {d d' : MachineData} (hwf : (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret) S d') (hin : writesIn S = true)
    {lo hi : Nat} (hw : ∀ w ∈ S.mem, w.r = 0 → lo ≤ w.off ∧ w.off + w.n ≤ hi)
    (hlt : ivs.all (fun p ↦ decide (p.2 ≤ 5520)) = true)
    (hd : ivs.all (fun p ↦ decide (p.2 ≤ lo) || decide (hi ≤ p.1)) = true) :
    KeepIv ivs m0 d.dmem d'.dmem := fun j hj ↦
  keepB hwf hm hin (by have := inIv_lt hlt hj; omega) fun w hw' hr ↦ by
    obtain ⟨p, hp, h1, h2⟩ := hj
    have := List.all_eq_true.mp hd p hp
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    have := hw w hw' hr
    omega

/-- **A block's changes keep the intervals**: each of its writes in the frame apart from them. -/
theorem keepIv_block' [Labels] {rest : List (BitVec 64 × Nat)} {ret : BitVec 64} {S : SState}
    {d d' : MachineData} (hwf : (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret).WF)
    (hm : Match (frameEnv m0 d 5520 rest (fun _ ↦ 0) ret) S d') (hin : writesIn S = true)
    (hlt : ivs.all (fun p ↦ decide (p.2 ≤ 5520)) = true)
    (hd : (S.mem.all fun w ↦ w.r != 0 ||
      ivs.all (fun p ↦ decide (w.off + w.n ≤ p.1) || decide (p.2 ≤ w.off))) = true) :
    KeepIv ivs m0 d.dmem d'.dmem := fun j hj ↦
  keepB hwf hm hin (by have := inIv_lt hlt hj; omega) fun w hw' hr ↦ by
    obtain ⟨p, hp, h1, h2⟩ := hj
    have := List.all_eq_true.mp hd w hw'
    simp only [hr, bne_self_eq_false, Bool.false_or, List.all_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at this
    have := this p hp
    omega

/-- The frame's byte `j` outside a range of it. -/
theorem loc_notIn (hS : StackOk m0 NN) {lo len j : Nat} (hj : j < 5528) (hl : lo + len ≤ 5528)
    (hd : j < lo ∨ lo + len ≤ j) : ¬ NativeRustcVm.InRange (loc m0 lo) len (loc m0 j) := fun h ↦ by
  have := inR_loc hS hl h
  rw [loc_toNat hS hj] at this
  have := rsp_ge hS
  have := N_ge
  omega

/-- **A call's changes keep the intervals**: below its RSP at the frame's offset `c` and `X`,
apart from them. -/
theorem keepIv_call (hS : StackOk m0 NN) {c Nc : Nat} {st m2 : MachineData}
    (hsp : rspOf st = loc m0 c) (hc : c ≤ 5520) (hle : 5520 - c + Nc ≤ NN) {X : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside st.dmem m2.dmem
      (fun q ↦ NativeRustcVm.InRange (stackBelow st Nc) Nc q ∨ X q))
    (hlt : ivs.all (fun p ↦ decide (p.2 ≤ 5520)) = true)
    (hge : ivs.all (fun p ↦ decide (c ≤ p.1)) = true)
    (hX : ∀ j, InIv ivs j → ¬ X (loc m0 j)) : KeepIv ivs m0 st.dmem m2.dmem := fun j hj ↦
  keepC hS hsp hc hle hs (inIv_ge hge hj) (by have := inIv_lt hlt hj; omega) fun i hi ↦ by
    rw [show i = 0 by omega, Nat.add_zero]; exact hX j hj

end

end NativeRustcVmX64.Bus.VerifyBusBalance
