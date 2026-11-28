module

public import NativeRustcVmX64.Sumcheck.Layer.Exec
public import NativeRustcVmX64.Sumcheck.Loop

/-!
# `sumcheck` with `verify_layer`'s closure: the frame, the entry, the exits (x86-64)

The 192-byte frame (`FrG`, `SF`): the output's address at `16`, the point's at `24`, `|pt|` at
`32` (`Words`), `eq` at `40`, the message at `64`, the pushed registers from `144`. The stack
arguments (the slots' address, `n`) and the point are kept (`arg_keep`, `pt_keep`). The
precondition with `n` named (`LPre`). The loop's head `.L2` after `i < n` rounds (`Inv`: R12 the
`TState`, RBP the message, R13 `16 i`, R14 `i`, RBX the slots' end, RAX, RCX the claim,
`Rounds`); `.L8` after the last (`Done`).
`entry_spec`: `b0`, `b1` to the head, or to `.L8` without slots; `exit_done` (`b11`, `b13`): the
claim at the output; `exit_fail` (`b12`, `b13`): `None`.
-/

namespace NativeRustcVmX64.Sumcheck.Layer

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SumcheckOfVerifyLayer
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Sumcheck

@[expose] public section

/-- The frame: 192 bytes below the entry's RSP. -/
abbrev fG (m0 : MachineData) : BitVec 64 := stackBelow m0 192

/-- The stack arguments' address. -/
abbrev argsG (m0 : MachineData) : BitVec 64 := rspOf m0 + 8#64

/-- The `TState`, the output, the point, the slots at the entry; the count `3`. -/
abbrev tG (m0 : MachineData) : BitVec 64 := reg m0 .rsi
abbrev outG (m0 : MachineData) : BitVec 64 := reg m0 .rdi
abbrev ptG (m0 : MachineData) : BitVec 64 := reg m0 .r8
abbrev slG (m0 : MachineData) : BitVec 64 := stackArg m0 0
abbrev cntG (_m0 : MachineData) : Nat := 3

/-- The precondition, the slots' count `n` named. -/
def LPre [Labels] (a : DecArea) (s : TState) (pt : Array EW) (n : Nat) (m0 : MachineData) : Prop :=
  SumcheckLayerPre a s pt m0 ∧ (stackArg m0 1).toNat = n

/-- The postcondition. -/
abbrev LPost [Labels] (a : DecArea) (s : TState) (pt : Array EW) (_n : Nat) (m0 m : MachineData) :
    Prop :=
  SumcheckLayerPost a s pt m0 m

/-- The claim in RAX, RCX. -/
abbrev claimR (m : MachineData) : EW := ⟨.ofBitVec (reg m .rax), .ofBitVec (reg m .rcx)⟩

/-- The loop's frame. -/
abbrev FrG [Labels] (m0 : MachineData) (n o : Nat) (m : MachineData) : Prop :=
  SF m0 (tG m0) (slG m0) n sumcheckLayerStack 192 slots o m

/-- The model's run after `i` rounds. -/
abbrev RoundsG (a : DecArea) (s : TState) (pt : Array EW) (m0 : MachineData) (d : Mem 64)
    (i : Nat) (c : EW) : Prop :=
  Rounds d (tG m0) a (slG m0) (claimArg m0) (cntG m0) (fun j ↦ pt[j]?) s i c

/-- The frame's words: the output's and the point's addresses, the point's size. -/
structure Words (m0 : MachineData) (d : Mem 64) : Prop where
  out : NativeRustcVm.WordAt d (off (fG m0) 16) (UInt64.ofBitVec (outG m0))
  p : NativeRustcVm.WordAt d (off (fG m0) 24) (UInt64.ofBitVec (ptG m0))
  sz : NativeRustcVm.WordAt d (off (fG m0) 32) (UInt64.ofBitVec (reg m0 .r9))

/-- **The loop's invariant** at `.L2`, `i < n` rounds done. -/
structure Inv [Labels] (a : DecArea) (s : TState) (pt : Array EW) (n : Nat) (m0 : MachineData)
    (i : Nat) (m : MachineData) : Prop where
  fr : FrG m0 n 8 m
  lt : i < n
  w : Words m0 m.dmem
  r12 : reg m .r12 = tG m0
  rbp : reg m .rbp = off (fG m0) 64
  r13 : reg m .r13 = BitVec.ofNat 64 (16 * i)
  r14 : reg m .r14 = BitVec.ofNat 64 i
  rbx : reg m .rbx = off (slG m0) (16 * n)
  run : RoundsG a s pt m0 m.dmem i (claimR m)

/-- At `.L8`: every round done. -/
structure Done [Labels] (a : DecArea) (s : TState) (pt : Array EW) (n : Nat) (m0 : MachineData)
    (m : MachineData) : Prop where
  fr : FrG m0 n 8 m
  out : NativeRustcVm.WordAt m.dmem (off (fG m0) 16) (UInt64.ofBitVec (outG m0))
  run : RoundsG a s pt m0 m.dmem n (claimR m)

/-- The body's environment: the frame, the stack arguments. -/
abbrev envB (m0 m : MachineData) (ret : BitVec 64) : Env :=
  frameEnv m0 m 192 [(argsG m0, 16)] (fun _ ↦ 0) ret

/-- The environment of a block with one more region `x` of `l` bytes. -/
abbrev envX (m0 m : MachineData) (x : BitVec 64) (l : Nat) (ret : BitVec 64) : Env :=
  frameEnv m0 m 192 [(x, l)] (fun _ ↦ 0) ret

end

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 192 := by decide

theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide

theorem Keeps.reg {S : SState} {rs : List Reg64} (h : Keeps S rs = true) {r : Reg64} (hr : r ∈ rs) :
    S.reg r = some (.reg r) := by
  simp only [Keeps, List.all_eq_true, beq_iff_eq] at h
  exact h r hr

/-- `x <<< 4` is `16 x`. -/
theorem shl4 (x : BitVec 64) :
    BinOp.apply .shl .W64 x (BitVec.ofNat 64 4) = BitVec.ofNat 64 (16 * x.toNat) := by
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [show shiftCount .W64 (BitVec.ofNat 64 4) = 4 by decide]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mul_comm]

theorem add16_off (sl : BitVec 64) (i : Nat) :
    BinOp.apply .add .W64 (BitVec.ofNat 64 16) (off sl (16 * i)) = off sl (16 * (i + 1)) := by
  simp only [BinOp.apply, low_W64, ext_W64, off]
  rw [BitVec.add_comm, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]

/-- The word `8 + j` above the entry's RSP, through the frame. -/
theorem frame_arg (m0 : MachineData) (j : Nat) :
    stackBelow m0 192 + BitVec.ofNat 64 (192 + 8 + j) = argsG m0 + BitVec.ofNat 64 j := by
  have := frame_add (m0 := m0) 192 (8 + j)
  rw [show 192 + (8 + j) = 192 + 8 + j by omega] at this
  rw [show stackBelow m0 192 + BitVec.ofNat 64 (192 + 8 + j) = off (stackBelow m0 192) (192 + 8 + j)
    from rfl, this, BitVec.ofNat_add, BitVec.add_assoc]

section
variable [Labels] {a : DecArea} {s : TState} {pt : Array EW} {n : Nat} {m0 : MachineData}

theorem geo (h : LPre a s pt n m0) :
    Geo a s m0 (tG m0) (outG m0) (slG m0) (cntG m0) n sumcheckLayerStack 192 slots 144 :=
  by obtain ⟨h, rfl⟩ := h; exact ⟨h.2.1, by unfold sumcheckLayerStack; omega, by decide, by decide⟩

/-- The stack arguments' aliases, in a body environment. -/
theorem argAl_ok (d : MachineData) (ret : BitVec 64) :
    AllOf (fun p ↦ p.1.eval (envB m0 d ret) = (envB m0 d ret).base p.2.1 + BitVec.ofInt 64 p.2.2)
      argAl :=
  ⟨frame_arg m0 0, frame_arg m0 8, trivial⟩

/-- The stack arguments are apart from what the loop changes. -/
theorem not_args (h : LPre a s pt n m0) {q : BitVec 64}
    (hq : LChg m0 sumcheckLayerStack (tG m0) (slG m0) n q) :
    ¬ NativeRustcVm.InRange (argsG m0) 16 q := by
  have g := geo h
  obtain ⟨h, rfl⟩ := h
  have hrd := args_readable h.1 (by omega)
  rcases hq with hq | hq | hq
  · exact fun ha ↦ not_inRange_of_apart (args_apart g.ok.1 h.1 (by omega) le_rfl)
      g.ctx.noWrap_stack hrd.2 (inRange_mono hq (by omega)) ha
  · exact not_inRange_of_apart h.2.2.2.2.2.2.2.2.1 g.ctx.fp.1.2 hrd.2 hq
  · exact not_inRange_of_apart h.2.2.2.2.2.2.2.2.2 g.slOk.2.1 hrd.2 hq

/-- **The stack arguments kept.** -/
theorem arg_keep (h : LPre a s pt n m0) {o : Nat} {d : MachineData}
    (hf : FrG m0 n o d) {i : Nat} (hi : i < 2) :
    NativeRustcVm.WordAt d.dmem (off (argsG m0) (8 * i)) (UInt64.ofBitVec (stackArg m0 i)) := by
  have hrd := args_readable h.1.1 (by omega)
  have hnw := hrd.2
  unfold NativeRustcVm.NoWrap at hnw
  refine NativeRustcVm.BytesAt.of_sameOutside (stackArg_wordAt h.1.1 hi) hf.same fun j hj hq ↦
    not_args h hq ?_
  rw [NativeRustcVm.length_wordBytes] at hj
  rw [off_add]
  exact inRange_off_self (by omega) (by omega)

/-- **The point kept.** -/
theorem pt_keep (h : LPre a s pt n m0) {o : Nat} {d : MachineData}
    (hf : FrG m0 n o d) : NativeRustcVm.EWsAt d.dmem (ptG m0) pt.toList := by
  have g := geo h
  obtain ⟨⟨-, -, -, hpt, hnw, hst, hat, has, -⟩, rfl⟩ := h
  refine NativeRustcVm.BytesAt.of_sameOutside hpt hf.same fun j hj hq ↦ ?_
  rw [NativeRustcVm.length_ewsBytes, Array.length_toList] at hj
  have hin : NativeRustcVm.InRange (ptG m0) (16 * pt.size) (ptG m0 + BitVec.ofNat 64 j) := by
    have : (ptG m0).toNat + 16 * pt.size ≤ 2 ^ 64 := hnw
    exact inRange_off_self (b := ptG m0) hj (by omega)
  rcases hq with hq | hq | hq
  · exact not_inRange_of_apart hst hnw g.ctx.noWrap_stack hin (inRange_mono hq (by omega))
  · exact not_inRange_of_apart hat hnw g.ctx.fp.1.2 hin hq
  · exact not_inRange_of_apart has hnw g.slOk.2.1 hin hq

theorem wf_envB (h : LPre a s pt n m0) {o : Nat} {m : MachineData} (hf : FrG m0 n o m)
    (ret : BitVec 64) : (envB m0 m ret).WF := by
  have g := geo h
  have hrd := args_readable h.1.1 (by omega)
  refine frame_wf ⟨g.ctx.mapped_frame hf.frame.kept, g.ctx.noWrap_frame⟩ (fun x hx ↦ ?_)
    (List.pairwise_pair.mpr (args_apart g.ok.1 h.1.1 (by omega) g.ctx.le))
  rw [List.mem_singleton] at hx
  subst hx
  exact ⟨Mapped.keeps hrd.1 hf.frame.kept, hrd.2⟩

theorem match_bodyS {m : MachineData} (hf : FrG m0 n 8 m) (ret : BitVec 64) :
    Match (envB m0 m ret) bodyS m :=
  match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.frame.rsp_eval, trivial⟩ trivial trivial
    (argAl_ok m ret)

/-- A region `x` apart from the stack, mapped and not wrapping: a block's second region. -/
theorem wf_envX (h : LPre a s pt n m0) {o : Nat} {m : MachineData} (hf : FrG m0 n o m)
    {x : BitVec 64} {l : Nat} (hm : NativeRustcVm.Mapped m.dmem x l) (hnw : NativeRustcVm.NoWrap x l)
    (hA : NativeRustcVm.Apart x l (stackBelow m0 sumcheckLayerStack) (sumcheckLayerStack + 8))
    (ret : BitVec 64) : (envX m0 m x l ret).WF := by
  have g := geo h
  refine frame_wf ⟨g.ctx.mapped_frame hf.frame.kept, g.ctx.noWrap_frame⟩ (fun y hy ↦ ?_)
    (List.pairwise_pair.mpr (Apart.symm' (apart_frame hA g.ctx.spN g.ctx.le)))
  rw [List.mem_singleton] at hy
  subst hy
  exact ⟨hm, hnw⟩

theorem match_outS {m : MachineData} (hf : FrG m0 n 8 m)
    (hout : NativeRustcVm.WordAt m.dmem (off (fG m0) 16) (UInt64.ofBitVec (outG m0))) :
    Match (envX m0 m (outG m0) 24 0) outS m := by
  have hal : (Sym.load 0 16 8).eval (envX m0 m (outG m0) 24 0) =
      (envX m0 m (outG m0) 24 0).base 1 + BitVec.ofInt 64 0 := by
    rw [ofInt_zero64, BitVec.add_zero]
    exact load_ofMachine (o := 16) rfl hout
  exact match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.frame.rsp_eval, trivial⟩ trivial trivial
    ⟨hal, trivial⟩

end

variable [Host] {a : DecArea} {s : TState} {pt : Array EW} {n : Nat} {m0 : MachineData} {k : Nat}

/-- **The exits' common end**: after `b13`, the registers restored, the postcondition. -/
theorem exit_post (hpre : LPre a s pt n m0) {m : MachineData} (hf : FrG m0 n 8 m)
    {S' : SState} {st : MachineState} (hm' : Match (envX m0 m (outG m0) 24 0) S' st.data)
    (hepi : EpiOk 192 slots S' = true) (hW : ∀ w ∈ S'.mem, w.r = 1 ∧ w.off + w.n ≤ 24)
    (hpc : PcOk (envX m0 m (outG m0) 24 0) (.ret (.load 0 192 8)) 0 st)
    {r : Option ((Array EW × EW) × TState)}
    (hr : r = (sumcheckFn (claimArg m0) (cntG m0) (fun j ↦ pt[j]?) n).run s)
    (hxs : ∀ xs c s', r = some ((xs, c), s') →
      xs.toList.length ≤ n ∧ NativeRustcVm.EWsAt m.dmem (slG m0) xs.toList)
    (hts : NextAt m.dmem (tG m0) a r)
    (ho : OptEWAt st.data.dmem (outG m0) (r.map (·.1.2))) :
    st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ LPost a s pt n m0 st.data := by
  have g := geo hpre
  have hwf := wf_envX hpre hf (Mapped.keeps g.outOk.1 hf.frame.kept) g.outOk.2.1 g.outOk.2.2.2.2.1 0
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hf.frame hwf hm' hepi
  simp only [PcOk, Sym.eval] at hpc
  have hs : NativeRustcVm.SameOutside m.dmem st.data.dmem (NativeRustcVm.InRange (outG m0) 24) :=
    sameOutside_region hwf hm' (r := 1) rfl fun w hw ↦ ⟨(hW w hw).1, Nat.zero_le _, (hW w hw).2⟩
  have hosl : ∀ q, NativeRustcVm.InRange (outG m0) 24 q →
      ¬ NativeRustcVm.InRange (slG m0) (16 * n) q := fun q hq ↦
    not_inRange_of_apart g.ok.2.2.2.2.2.2.2.2.1 g.outOk.2.1 g.slOk.2.1 hq
  refine ⟨hpc.trans (hf.frame.load_ret g.ok.1 (by unfold sumcheckLayerStack; omega)), hrsp, ?_⟩
  unfold LPost SumcheckLayerPost
  dsimp only
  rw [hpre.2, ← hr]
  refine ⟨⟨ho, fun xs c s' h ↦ g.sl_keep hs hosl (hxs xs c s' h).1 (hxs xs c s' h).2,
    fun x s' h ↦ (hts x s' h).frame (hm'.kept hwf) (fun q hq ↦ g.ctx.out_not_t g.outOk hq) hs⟩,
    NativeRustcVm.SameOutside.mono (hf.same.trans hs) fun q hq ↦ ?_, hsv⟩
  rcases hq with (hq | hq | hq) | hq
  · exact Or.inr (Or.inr (Or.inr hq))
  · exact Or.inr (Or.inr (Or.inl hq))
  · exact Or.inr (Or.inl hq)
  · exact Or.inl hq

/-- **`b11`, `b13`**: every round done, the claim into the output, the exit. -/
theorem exit_done (hp : Placed code k) (hpre : LPre a s pt n m0) {m : MachineData}
    (hd : Done a s pt n m0 m) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
        LPost a s pt n m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b11Offset)⟩ := by
  have g := geo hpre
  obtain ⟨xs, sn, hrun, hsz, hxs, hts⟩ := hd.run
  have hwf := wf_envX hpre hd.fr (Mapped.keeps g.outOk.1 hd.fr.frame.kept) g.outOk.2.1 g.outOk.2.2.2.2.1 0
  refine exec_then (infix_of b11_in_code (by simp [b11]) hp) exit_b11 hwf nofun
    (match_outS hd.fr hd.out) fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  rw [hp.label NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.label_9_at] at hpc1
  refine exec_at (infix_of b13_in_code (by simp [b13]) hp) exit_b13a hwf nofun hpc1 hm1
    fun st2 hm2 hpc2 ↦ Eventually.done _ ?_
  obtain ⟨hepi, hW, hW0, hW8, hW16⟩ := ok_b13a
  refine exit_post hpre hd.fr hm2 hepi hW hpc2 hrun.symm
    (fun xs' c s' h ↦ by cases h; exact ⟨by simp [hsz], hxs⟩)
    (fun x s' h ↦ by cases h; exact hts) ?_
  have w0 := wordAt_written hm2 (r := 1) (o := 0) rfl (by omega) hW0 (w := 1) rfl
  have w8 := wordAt_written hm2 (r := 1) (o := 8) rfl (by omega) hW8 (w := (claimR m).c0) rfl
  have w16 := wordAt_written hm2 (r := 1) (o := 16) rfl (by omega) hW16 (w := (claimR m).c1) rfl
  rw [off_zero] at w0
  refine ⟨w0, ewAt_iff.mpr ⟨w8, ?_⟩⟩
  rw [off_off]
  exact w16

/-- **`b12`, `b13`**: a rejected round, `None` into the output, the exit. -/
theorem exit_fail (hp : Placed code k) (hpre : LPre a s pt n m0) {m : MachineData}
    (hf : FrG m0 n 8 m)
    (hout : NativeRustcVm.WordAt m.dmem (off (fG m0) 16) (UInt64.ofBitVec (outG m0)))
    (hnone : (sumcheckFn (claimArg m0) (cntG m0) (fun j ↦ pt[j]?) n).run s = none) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
        LPost a s pt n m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b12Offset)⟩ := by
  have g := geo hpre
  have hwf := wf_envX hpre hf (Mapped.keeps g.outOk.1 hf.frame.kept) g.outOk.2.1 g.outOk.2.2.2.2.1 0
  refine exec_then (infix_of b12_in_code (by simp [b12]) hp) exit_b12 hwf nofun
    (match_outS hf hout) fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  refine exec_at (infix_of b13_in_code (by simp [b13]) hp) exit_b13b hwf nofun
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b12_next)) hm1 fun st2 hm2 hpc2 ↦ Eventually.done _ ?_
  obtain ⟨hepi, hW, hW0⟩ := ok_b13b
  refine exit_post hpre hf hm2 hepi hW hpc2 (r := none) hnone.symm (fun _ _ _ h ↦ (nomatch h))
    (fun _ _ h ↦ (nomatch h)) ?_
  have w0 := wordAt_written hm2 (r := 1) (o := 0) rfl (by omega) hW0 (w := 0) rfl
  rw [off_zero] at w0
  exact w0

/-- **The entry**: `b0` pushes the registers and zeroes the message; without slots at `.L8`,
else `b1` and the loop's head with no round done. -/
theorem entry_spec (hp : Placed code k) (hpre : LPre a s pt n m0) :
    Eventually (step1 Host.exe)
      (fun st ↦ (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b11Offset) ∧ Done a s pt n m0 st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b2Offset) ∧ Inv a s pt n m0 0 st.data))
      ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b0Offset)⟩ := by
  have g := geo hpre
  have hst := g.ok.1
  have hle : 192 ≤ sumcheckLayerStack := by unfold sumcheckLayerStack; omega
  have hrd := args_readable hpre.1.1 (by omega)
  have hwf : (envB m0 m0 0).WF := by
    refine frame_wf ⟨frame_mapped hst hle, frame_noWrap hst hle⟩ (fun x hx ↦ ?_)
      (List.pairwise_pair.mpr (args_apart hst hpre.1.1 (by omega) hle))
    rw [List.mem_singleton] at hx
    subst hx
    exact hrd
  have hm : Match (envB m0 m0 0) entryS m0 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial (argAl_ok m0 0)
  have hn : (envB m0 m0 0).load 1 8 8 = stackArg m0 1 :=
    load_ofMachine (r := 1) (o := 8) rfl (stackArg_wordAt hpre.1.1 (i := 1) (by omega))
  have hsl : (envB m0 m0 0).load 1 0 8 = stackArg m0 0 :=
    load_ofMachine (r := 1) (o := 0) rfl (stackArg_wordAt hpre.1.1 (i := 0) (by omega))
  have hn2 : (stackArg m0 1).toNat = n := hpre.2
  have hts0 := g.ok.2.2.1
  -- The frame and the `TState` after the prologue's writes.
  have hpro : ∀ {S : SState} {d : MachineData}, Match (envB m0 m0 0) S d →
      ProOk 192 8 slots S = true → (∀ w ∈ S.mem, w.r = 0) →
      FrG m0 n 8 d ∧ NativeRustcVm.SameOutside m0.dmem d.dmem (NativeRustcVm.InRange (fG m0) 192) := by
    intro S d hmS hP hall
    have hs : NativeRustcVm.SameOutside m0.dmem d.dmem (NativeRustcVm.InRange (fG m0) 192) :=
      sameOutside_low hwf hmS (r := 0) rfl (hi := 192) (by omega) fun w hw ↦
        ⟨hall w hw, belowRet_spec (belowRet_of_pro hP) w hw (hall w hw)⟩
    exact ⟨⟨Frame.of_prologue Frame.entry hwf hmS hP slots_le slots_cs,
      NativeRustcVm.SameOutside.mono hs fun q hq ↦ Or.inl (g.ctx.inRange_frame hq)⟩, hs⟩
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf nofun hm
    fun st0 hm0 hpc0 ↦ ?_
  obtain ⟨hP0, hall0, hW16_0, -, -, hrax0, hrcx0⟩ := ok_b0
  obtain ⟨hfr0, hs0⟩ := hpro hm0 hP0 hall0
  have hc0 : c0.eval (envB m0 m0 0) = decide (n = 0) := by
    simp only [c0, SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
      BitVec.and_self, hn]
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, hn2]
    rfl
  simp only [PcOk, hc0] at hpc0
  have hclaim0 : claimR st0.data = claimArg m0 := by
    show (⟨_, _⟩ : EW) = ⟨_, _⟩
    rw [show reg st0.data .rax = reg m0 .rdx from hm0.regs .rax _ hrax0,
      show reg st0.data .rcx = reg m0 .rcx from hm0.regs .rcx _ hrcx0]
  by_cases h0 : n = 0
  · simp only [h0, decide_true, ite_true] at hpc0
    refine .done _ (Or.inl ⟨hpc0.trans (hp.label NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.label_8_at), hfr0,
      wordAt_written hm0 (r := 0) (o := 16) rfl (by omega) hW16_0 rfl, ?_⟩)
    rw [hclaim0, h0]
    exact rounds_zero (g.t_keep hs0 (hm0.kept hwf) (fun q hq ↦ Or.inl (g.ctx.inRange_frame hq)) hts0)
  · simp only [h0, decide_false, Bool.false_eq_true, ite_false] at hpc0
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf nofun
      (hpc0.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b0_next)) hm0 fun st1 hm1 hpc1 ↦ ?_
    obtain ⟨hP1, hall1, hW16, hW24, hW32, hrax1, hrcx1, hrbx1, hrbp1, hr12, hr13, hr14⟩ := ok_b1
    obtain ⟨hfr1, hs1⟩ := hpro hm1 hP1 hall1
    simp only [PcOk] at hpc1
    have hclaim1 : claimR st1.data = claimArg m0 := by
      show (⟨_, _⟩ : EW) = ⟨_, _⟩
      rw [show reg st1.data .rax = reg m0 .rdx from hm1.regs .rax _ hrax1,
        show reg st1.data .rcx = reg m0 .rcx from hm1.regs .rcx _ hrcx1]
    refine .done _ (Or.inr ⟨hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.b1_next), hfr1,
      Nat.pos_of_ne_zero h0,
      ⟨wordAt_written hm1 (r := 0) (o := 16) rfl (by omega) hW16 rfl,
        wordAt_written hm1 (r := 0) (o := 24) rfl (by omega) hW24 rfl,
        wordAt_written hm1 (r := 0) (o := 32) rfl (by omega) hW32 rfl⟩,
      hm1.regs .r12 _ hr12, (hm1.regs .rbp _ hrbp1).trans (eval_ptr0 64),
      hm1.regs .r13 _ hr13, hm1.regs .r14 _ hr14, ?_, ?_⟩)
    · rw [show reg st1.data .rbx = _ from hm1.regs .rbx _ hrbx1]
      simp only [Sym.eval, hn, hsl, shl4]
      simp only [BinOp.apply, low_W64, ext_W64, hn2]
    · rw [hclaim1]
      exact rounds_zero (g.t_keep hs1 (hm1.kept hwf) (fun q hq ↦ Or.inl (g.ctx.inRange_frame hq))
        hts0)

end

end NativeRustcVmX64.Sumcheck.Layer
