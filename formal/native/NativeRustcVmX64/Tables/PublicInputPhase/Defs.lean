module

public import NativeRustcVmX64.Tables.PublicInputPhase.Exec
public import NativeRustcVmX64.Bus.GkrCommon
public import NativeRustcVmX64.Spec.Tables
public import NativeRustcVm.Tables.Same
public import NativeRustcVmX64.Tables.Common

/-!
# `public_input_phase`'s frame (x86-64)

The frame (`Bus.Gkr.Fr`, `F = 608`) with the outputs the `TState` (RDI) and the claims (RCX,
`outs`). A callee entered with RSP at the frame's offset `0` uses `Nc` bytes below it,
`608 + Nc ≤ publicInputPhaseStack`: its stack, an input (`readIn_call`), a local of the frame from
offset `8` (`local_out`); a local kept (`local_keep`); an input kept (`same_in`); the `TState` kept
across changes apart from it (`tstate_keep`). The model's run (`run_eq`), the point (`pt`).
-/

namespace NativeRustcVmX64.Tables.PublicInputPhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Tables
open NativeRustcVmX64.Bus.Gkr (Fr off_fb)
open NativeRustcVm.Layout (LayoutWAt layoutBytes Same ClaimsWAt claimsBytes claimCap)
open LeanVM.Protocol.Verifier (memory0 memory1)

@[expose] public section

/-- The stack. -/
abbrev N : Nat := publicInputPhaseStack

/-- The outputs: the `TState` (RDI) and the claims (RCX). -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (reg m0 .rdi) tstateBytes q ∨ NativeRustcVm.InRange (reg m0 .rcx) claimsBytes q

/-- The written regions. -/
def wsOf (m0 : MachineData) : List NativeRustcVm.Region :=
  [⟨reg m0 .rdi, tstateBytes⟩, ⟨reg m0 .rcx, claimsBytes⟩]

/-- The frame. -/
abbrev St (m0 : MachineData) (o : Nat) (d : MachineData) : Prop := Fr m0 608 N slots (outs m0) o d

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 608

/-- The memory placement's variable count. -/
abbrev vcOf (L : LayoutW) : Nat := (L.placement memory0).variableCount

/-- The point: the challenge, then `n - 1` zeros. -/
def pt (ch : EW) (n : Nat) : Array EW := #[ch] ++ Array.replicate (n - 1) 0

end

public section

theorem N_ge : 608 ≤ N := by decide
theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 608 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide
theorem slots_hi : ∀ p ∈ slots, 560 ≤ p.1 := by decide

/-- **The model's run**: the challenge, the two claims at the point `pt`. -/
theorem run_eq (L : LayoutW) (pub : Vector UInt64 4) (s : TState) :
    (publicInputPhase L pub).run s = some (#[
      ⟨memory0, pt s.sponge.squeeze.1 (vcOf L),
        multilinearEval #[EW.ofK pub[0], EW.ofK pub[2]] #[s.sponge.squeeze.1]⟩,
      ⟨memory1, pt s.sponge.squeeze.1 (vcOf L),
        multilinearEval #[EW.ofK pub[1], EW.ofK pub[3]] #[s.sponge.squeeze.1]⟩],
      { s with sponge := s.sponge.squeeze.2 }) := by
  simp [publicInputPhase, sampleChallenge, pt]

theorem pt_max (ch : EW) (v : Nat) : pt ch (max v 1) = pt ch v := by
  unfold pt
  congr 2
  omega

theorem push_push (cs : Array ColumnClaimW) (x y : ColumnClaimW) :
    (cs.push x).push y = cs ++ #[x, y] := by
  apply Array.toList_inj.mp
  simp

section
variable [Labels] {a : DecArea} {s : TState} {L : LayoutW} {pub : Vector UInt64 4}
  {cs : Array ColumnClaimW} {m0 : MachineData}

theorem pre_parts (h : PublicInputPhasePre a s L pub cs m0) :
    StackOk m0 N ∧ RcAt m0 N ∧ TStateAt m0.dmem (reg m0 .rdi) a s ∧
      TStateOk m0 (reg m0 .rdi) a N ∧ OutOk m0 (reg m0 .rdi) a (reg m0 .rcx) claimsBytes N ∧
      ClaimsWAt m0.dmem (reg m0 .rcx) cs ∧
      ReadIn m0 (reg m0 .rsi) layoutBytes N (wsOf m0) ∧ LayoutWAt m0.dmem (reg m0 .rsi) L ∧
      vcOf L ≤ 31 ∧ ReadIn m0 (reg m0 .rdx) 32 N (wsOf m0) ∧
      NativeRustcVm.WordsAt m0.dmem (reg m0 .rdx) pub.toList := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, _⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem got (h : PublicInputPhasePre a s L pub cs m0) :
    GotAt m0 N [(reg m0 .rdi, tstateBytes), (a.words, 8 * a.len),
      (reg m0 .rcx, claimsBytes), (reg m0 .rsi, layoutBytes), (reg m0 .rdx, 32),
      (rcAddr, 192)] ["memcpy"] :=
  h.2.2.2.2.2.2.2.2.2.2.2

theorem ctx (h : PublicInputPhasePre a s L pub cs m0) {F : Nat} (hF : F ≤ N) :
    Ctx m0 (reg m0 .rdi) a N F :=
  let p := pre_parts h
  ⟨p.1, p.2.1, p.2.2.2.1, p.2.2.1.footprint, hF⟩

theorem outs_not_frame (h : PublicInputPhasePre a s L pub cs m0) {q : BitVec 64} (hq : outs m0 q) :
    ¬NativeRustcVm.InRange (fb m0) (608 + 8) q := by
  have p := pre_parts h
  have c := ctx h N_ge
  have hfr : NativeRustcVm.NoWrap (fb m0) (608 + 8) := c.noWrap_frame
  rcases hq with hq | hq
  · exact NativeRustcVm.Apart.not_inRange (apart_frame p.2.2.2.1.1 c.spN N_ge)
      p.2.2.1.footprint.1.2 hfr hq
  · exact NativeRustcVm.Apart.not_inRange (apart_frame p.2.2.2.2.1.2.2.2.2.1 c.spN N_ge)
      p.2.2.2.2.1.2.1 hfr hq

theorem outs_not_rc (h : PublicInputPhasePre a s L pub cs m0) {q : BitVec 64} (hq : outs m0 q) :
    ¬NativeRustcVm.InRange rcAddr 192 q := by
  have c := ctx h N_ge
  rcases hq with hq | hq
  · exact c.not_rc_tstate hq
  · exact c.out_not_rc (pre_parts h).2.2.2.2.1 hq

/-- **An input kept** in the frame's states. -/
theorem same_in (h : PublicInputPhasePre a s L pub cs m0) {o : Nat} {d : MachineData}
    (fr : St m0 o d) {x : BitVec 64} {n : Nat} (hx : ReadIn m0 x n N (wsOf m0)) :
    Same m0.dmem d.dmem x n := by
  have c := ctx h N_ge
  obtain ⟨⟨-, hnw⟩, hO, hW⟩ := hx
  intro j hj
  refine fr.same _ fun hq ↦ ?_
  rcases hq with hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange_add hO hnw c.noWrap_stack hj (inRange_mono hq (by omega))
  · exact NativeRustcVm.Apart.not_inRange_add (hW ⟨reg m0 .rdi, tstateBytes⟩ (by simp [wsOf])) hnw
      (pre_parts h).2.2.1.footprint.1.2 hj hq
  · exact NativeRustcVm.Apart.not_inRange_add (hW ⟨reg m0 .rcx, claimsBytes⟩ (by simp [wsOf]))
      hnw (pre_parts h).2.2.2.2.1.2.1 hj hq

/-- At a call from the frame's base. -/
theorem at_call (h : PublicInputPhasePre a s L pub cs m0) {d : MachineData} (fr : St m0 0 d) :
    At m0 608 d := by
  have := fr.at_ (ctx h N_ge) (Nat.zero_le _) (fun _ hq ↦ outs_not_rc h hq)
  rwa [Nat.sub_zero] at this

theorem got_call (h : PublicInputPhasePre a s L pub cs m0) {Nc : Nat} {d : MachineData}
    (fr : St m0 0 d) (hle : 608 + Nc ≤ N) {areas : List (BitVec 64 × Nat)}
    (ha : ∀ l ∈ ["memcpy"], ∀ b ∈ areas, Apart (gotAddr l) 8 b.1 b.2) :
    GotAt d Nc areas ["memcpy"] := by
  have p := pre_parts h
  refine got_callee (got h) (got_keep (got h) p.1
    (writes := [(reg m0 .rdi, tstateBytes), (reg m0 .rcx, claimsBytes)])
    (by intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl <;> simp)
    (by
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact p.2.2.1.footprint.1.2
      · exact p.2.2.2.2.1.2.1)
    (by
      intro q hq
      apply fr.same q
      rintro (hs | ht | hc)
      · exact hq (Or.inr hs)
      · exact hq (Or.inl ⟨(reg m0 .rdi, tstateBytes), by simp, ht⟩)
      · exact hq (Or.inl ⟨(reg m0 .rcx, claimsBytes), by simp, hc⟩)))
    (at_call h fr).sp p.1.1 hle ha

/-- **An input for a callee** at the frame's base. -/
theorem readIn_call (h : PublicInputPhasePre a s L pub cs m0) {d : MachineData} (fr : St m0 0 d)
    {Nc : Nat} (hle : 608 + Nc ≤ N) {x : BitVec 64} {n : Nat} (hx : ReadIn m0 x n N (wsOf m0)) :
    ReadIn d x n Nc (wsOf m0) :=
  ⟨⟨Mapped.keeps hx.1.1 fr.frame.kept, hx.1.2⟩, (ctx h N_ge).apart (at_call h fr) hle hx.2.1, hx.2.2⟩

/-- **The `TState` kept** where the memory changed apart from it and its area. -/
theorem tstate_keep (h : PublicInputPhasePre a s L pub cs m0) {d d' : DataMem}
    {R : BitVec 64 → Prop} {s' : TState} (hts : TStateAt d (reg m0 .rdi) a s') (hk : Kept d d')
    (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ q, R q → NativeRustcVm.InRange (stackBelow m0 N) N q ∨
      NativeRustcVm.InRange (reg m0 .rcx) claimsBytes q) :
    TStateAt d' (reg m0 .rdi) a s' := by
  have c := ctx h N_ge
  have ho := (pre_parts h).2.2.2.2.1
  refine hts.frame hk (fun q hq ↦ ?_) hs
  rcases hR q hq with hq' | hq'
  · exact c.stack_not_t hq'
  · exact c.out_not_t ho hq'

/-- **A local of the frame from offset `8`** as an output of a callee at the frame's base. -/
theorem local_out (h : PublicInputPhasePre a s L pub cs m0) {d : MachineData} (hat : At m0 608 d)
    {Nc : Nat} (hle : 608 + Nc ≤ N) {o n : Nat} (ho : 8 ≤ o) (hon : o + n ≤ 608) :
    OutOk d (reg m0 .rdi) a (off (fb m0) o) n Nc :=
  (ctx h N_ge).outOk_frame hat hle ho hon

/-- **A local kept** across a callee's changes in its stack and elsewhere. -/
theorem local_keep (h : PublicInputPhasePre a s L pub cs m0) {d d' : MachineData}
    (hat : At m0 608 d) {Nc : Nat} (hle : 608 + Nc ≤ N) {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ NativeRustcVm.InRange (stackBelow d Nc) Nc q ∨ R q)) {o n : Nat} (ho : 8 ≤ o)
    (hon : o + n ≤ 608) (hR : ∀ q, R q → ¬NativeRustcVm.InRange (off (fb m0) o) n q) :
    ∀ j < n, d'.dmem.get? (off (fb m0) o + BitVec.ofNat 64 j) =
      d.dmem.get? (off (fb m0) o + BitVec.ofNat 64 j) := by
  have hO := local_out h hat hle ho hon
  have hnw : NativeRustcVm.NoWrap (stackBelow d Nc) (Nc + 8) :=
    noWrap_stackBelow ((ctx h N_ge).stackOk hat hle)
  intro j hj
  refine hs _ fun hq ↦ hq.elim (fun hq ↦ ?_) fun hq ↦ hR _ hq ?_
  · exact NativeRustcVm.Apart.not_inRange_add hO.2.2.2.2.1 hO.2.1 hnw hj (inRange_mono hq (by omega))
  · exact NativeRustcVm.inRange_add hj (by have := hO.2.1; unfold NoWrap at this; omega)

/-- The frame below its return address is in the stack. -/
theorem frame_in (h : PublicInputPhasePre a s L pub cs m0) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (fb m0) 608 q) : NativeRustcVm.InRange (stackBelow m0 N) N q :=
  (ctx h N_ge).inRange_frame hq

/-- A callee's stack is in the function's. -/
theorem callee_in (h : PublicInputPhasePre a s L pub cs m0) {d : MachineData} (hat : At m0 608 d)
    {Nc : Nat} (hle : 608 + Nc ≤ N) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow d Nc) Nc q) :
    NativeRustcVm.InRange (stackBelow m0 N) N q :=
  ((ctx h N_ge).inRange_callee hat hle hq).1

/-- The frame's environment of a state of the frame is well formed. -/
theorem wfF (h : PublicInputPhasePre a s L pub cs m0) {o : Nat} {d : MachineData}
    (fr : St m0 o d) {vars : Nat → BitVec 64} {ret : BitVec 64} :
    (frameEnv m0 d 608 [] vars ret).WF :=
  frame_wf ⟨Mapped.keeps (frame_mapped (pre_parts h).1 N_ge) fr.frame.kept,
    frame_noWrap (pre_parts h).1 N_ge⟩ (by simp) (List.pairwise_singleton _ _)

/-- A state of the frame at offset `o` in its frame's environment. -/
theorem matchF {o : Nat} {d : MachineData} (fr : St m0 o d) {vars : Nat → BitVec 64}
    {ret : BitVec 64} : Match (frameEnv m0 d 608 [] vars ret) (stO o) d :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨fr.frame.sp.trans (eval_ptr0 o).symm, trivial⟩ trivial trivial
    trivial

end

end

end NativeRustcVmX64.Tables.PublicInputPhase
