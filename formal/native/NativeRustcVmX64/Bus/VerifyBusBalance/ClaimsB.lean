module

public import NativeRustcVmX64.Bus.VerifyBusBalance.Share
public import NativeRustcVmX64.Bus.VerifyBusBalance.LoopExec
public import NativeRustcVmX64.Code.Vm.PushClaim.Names

/-!
# `verify_bus_balance`'s claims, the bytecode point's zeroing (x86-64)

`ClSt cs`: a state of the body between the pushes, `cs` the claims pushed (`ShareMem`, the
registers, the `TState`, the claims). `pcCall`: `push_claim` from it.

From `b28` (`k + NativeRustcVmX64.Vm.VerifyBusBalance.b28Offset`), the first claim pushed: `b28` to `b34` check each `push_claim` and push
the next three; `b35` to `b37` zero the bytecode point (17 rounds, `loop_spec`); then the bytecode
share (`claimsB_spec`).
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus NativeRustcVm.Layout

public section

/-- **Between the pushes.** -/
structure ClSt (a : DecArea) (L : LayoutW) (m0 : MachineData) (w pt tv mem : Array EW)
    (beta mf bf : EW) (s3 : TState) (cs : Array ColumnClaimW) (d : MachineData) : Prop where
  fr : St m0 104 d
  sm : ShareMem m0 L w pt tv mem beta mf bf d.dmem
  xbx : reg d .rbx = reg m0 .rdi
  x13 : reg d .r13 = L.logBytecode.toUInt64.toBitVec
  x14 : reg d .r14 = reg m0 .rsi
  x15 : reg d .r15 = reg m0 .r9
  xbp : reg d .rbp = (min L.logMemory pt.size).toUInt64.toBitVec
  x12 : reg d .r12 = (min L.logBytecode pt.size).toUInt64.toBitVec
  ts : TStateAt d.dmem (reg m0 .rdi) a s3
  cl : ClaimsWAt d.dmem (reg m0 .r9) cs

/-- The registers `ClSt` names. -/
abbrev clRegs : List Reg64 := [.rbx, .rbp, .r12, .r13, .r14, .r15]

theorem ClSt.regs {a : DecArea} {L : LayoutW} {m0 : MachineData} {w pt tv mem : Array EW}
    {beta mf bf : EW} {s3 : TState} {cs cs' : Array ColumnClaimW} {d d' : MachineData}
    (A : ClSt a L m0 w pt tv mem beta mf bf s3 cs d) (fr : St m0 104 d')
    (sm : ShareMem m0 L w pt tv mem beta mf bf d'.dmem) (hr : ∀ r ∈ clRegs, reg d' r = reg d r)
    (hts : TStateAt d'.dmem (reg m0 .rdi) a s3) (hcl : ClaimsWAt d'.dmem (reg m0 .r9) cs') :
    ClSt a L m0 w pt tv mem beta mf bf s3 cs' d' :=
  ⟨fr, sm, (hr .rbx (by simp)).trans A.xbx, (hr .r13 (by simp)).trans A.x13,
    (hr .r14 (by simp)).trans A.x14, (hr .r15 (by simp)).trans A.x15,
    (hr .rbp (by simp)).trans A.xbp, (hr .r12 (by simp)).trans A.x12, hts, hcl⟩

theorem clRegs_cs : ∀ r ∈ clRegs, calleeSaved r = true ∧ r ∈ cs ∧ r ∈ nsp := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, by simp [cs], by simp [nsp]⟩

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- **`push_claim(claims, id, 1800, j, v)`** from the frame, RSP at `96`. -/
theorem pcCall (h : VerifyBusBalancePre a s0 L m0)
    (hpc : ∀ cs, Spec (Labels.label NativeRustcVmX64.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    {st : MachineState} {next : Int64} {R : MachineState → Prop} (fr : St m0 96 st.data)
    (hpc0 : st.pc = Labels.label NativeRustcVmX64.Vm.PushClaim.entryLabel ∧ retOf st.data = next)
    {w pt tv mem : Array EW} {beta mf bf : EW} {s3 : TState} {cs : Array ColumnClaimW}
    (sm : ShareMem m0 L w pt tv mem beta mf bf st.data.dmem)
    (hts : TStateAt st.data.dmem (reg m0 .rdi) a s3)
    (hcl : ClaimsWAt st.data.dmem (reg m0 .r9) cs) (hcs : cs.size < claimCap)
    (xdi : reg st.data .rdi = reg m0 .r9) (xdx : reg st.data .rdx = loc m0 1800) {j : Nat}
    (hj : j ≤ 30) (xcx : reg st.data .rcx = (min j pt.size).toUInt64.toBitVec)
    {id : Nat} {v : EW} (xsi : (reg st.data .rsi).toNat = id)
    (xv : ewArg (reg st.data .r8) (reg st.data .r9) = v)
    (cont : ∀ m2, St m0 104 m2 → ShareMem m0 L w pt tv mem beta mf bf m2.dmem →
      TStateAt m2.dmem (reg m0 .rdi) a s3 → boolRet m2 = 1 →
      ClaimsWAt m2.dmem (reg m0 .r9) (cs.push ⟨id, pt.extract 0 j, v⟩) →
      (∀ r, calleeSaved r = true → m2.regs.get64 r = st.data.regs.get64 r) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st := by
  have hS := pre_stack h
  have psz := sm.tail.psz
  have hc := pre_cl h
  have hle : 5520 - 96 + pushClaimStack ≤ NN := le_pc
  have ncx : (min j pt.size).toUInt64.toBitVec.toNat = min j pt.size := by
    rw [UInt64.toNat_toBitVec]
    exact UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have hsp : rspOf st.data = loc m0 96 := fr.frame.sp
  refine callF h (c := 96) (Nc := pushClaimStack) (lo := 0) (len := 0)
    (X := NativeRustcVm.InRange (reg m0 .r9) claimsBytes) (by omega) hle (by omega)
    (fun q hq ↦ .inl (.inr (.inr hq))) (hpc cs) fr hpc0 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ ?_, hq.2.2⟩)
    fun m2 fr2 hq2 hs2 hcs2 ↦ ?_
  · unfold PushClaimPre
    rw [xdi, xdx, xcx]
    have hco := cal_out h fr (by omega) hle hc
    refine ⟨cal_stack h fr (by omega) hle, hcl, ⟨hco.1, hco.2.1⟩, hco.2.2.2.2.1, ?_, ?_⟩
    · unfold SliceOk; rw [ncx]; exact cal_localIn h fr (by omega) hle (by omega) (by omega)
    · rw [ncx]; exact apart_loc hS hc.2.2.2.2.1 (by omega)
  · rw [xdi] at hq'
    exact hq'.elim .inr .inl
  · obtain ⟨h2a, -, hsv⟩ := hq2
    rw [xdi, xdx, xcx, ncx] at h2a
    simp only [show cs.size < claimCap ∧ min j pt.size ≤ pointCap from
      ⟨hcs, by unfold pointCap; omega⟩, and_self, ↓reduceIte] at h2a
    obtain ⟨hal, hcl2⟩ := h2a
    rw [xsi, xv, show slice st.data (loc m0 1800) (min j pt.size).toUInt64.toBitVec =
      pt.extract 0 j from slice_prefix sm.tail.hpt psz j] at hcl2
    have hX : ∀ q, NativeRustcVm.InRange (stackBelow st.data pushClaimStack) pushClaimStack q ∨
        NativeRustcVm.InRange (reg m0 .r9) claimsBytes q →
        NativeRustcVm.InRange (stackBelow m0 NN) NN q ∨
          NativeRustcVm.InRange (reg m0 .r9) claimsBytes q := fun q hq ↦
      hq.elim (fun h' ↦ .inl (callee_stack hS hsp (by omega) hle h')) .inr
    refine cont m2 fr2 (sm.of_keep (keepIv_call hS hsp (by omega) hle hs2 (by decide) (by decide)
      fun j' hj' hq ↦ ?_)) (ts_keep h hsv.2 hs2 (fun q hq ↦ (hX q hq).elim .inl
        fun h' ↦ .inr (.inr h')) hts) hal hcl2 hcs2
    exact not_loc hS hc.2.2.2.2.1 hc.2.1 (j := j') (l := 1)
      (by have := inIv_lt (B := 5472) (by decide) hj'; omega) hq
      (loc_inR hS (by omega) (by omega) (by have := inIv_lt (B := 5472) (by decide) hj'; omega))

/-- **A push block and its `push_claim`**: `push_claim(claims, id, point, j, v)` with `j` in
`rc`, `v` the words at `o8`, `o9`. -/
theorem pushBlk (h : VerifyBusBalancePre a s0 L m0)
    (hpc : ∀ cs, Spec (Labels.label NativeRustcVmX64.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    {bX : List Directive} {j id o8 o9 : Nat} {rc : Reg64}
    (hin : bX.IsInfixAt Host.prog (k + j)) (hlen : bX.length = 7)
    (hx : exec bX (fS 104) = some (after bX (fS 104),
      .call NativeRustcVmX64.Vm.PushClaim.entryLabel))
    (hok : Mid 96 (after bX (fS 104)) ∧ W0 96 104 (after bX (fS 104)) ∧
      (after bX (fS 104)).reg .rdi = some (.reg .r15) ∧
      (after bX (fS 104)).reg .rsi = some (.lit id) ∧
      (after bX (fS 104)).reg .rdx = some (.load 0 104 8) ∧
      (after bX (fS 104)).reg .rcx = some (.reg rc) ∧
      (after bX (fS 104)).reg .r8 = some (.load 0 o8 8) ∧
      (after bX (fS 104)).reg .r9 = some (.load 0 o9 8) ∧ Keeps cs (after bX (fS 104)))
    {w pt tv mem : Array EW} {beta mf bf : EW} {s3 : TState} {cs : Array ColumnClaimW}
    {d : MachineData} (A : ClSt a L m0 w pt tv mem beta mf bf s3 cs d) (hcs : cs.size < claimCap)
    {J : Nat} (hJ : J ≤ 30) (hrc : reg d rc = (min J pt.size).toUInt64.toBitVec) {v : EW}
    (h8 : NativeRustcVm.WordAt d.dmem (loc m0 o8) v.c0)
    (h9 : NativeRustcVm.WordAt d.dmem (loc m0 o9) v.c1) (hid : id < 2 ^ 64)
    (cont : ∀ m2, ClSt a L m0 w pt tv mem beta mf bf s3 (cs.push ⟨id, pt.extract 0 J, v⟩) m2 →
      boolRet m2 = 1 → Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨m2, Host.addrOf (k + j + 7)⟩) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨d, Host.addrOf (k + j)⟩ := by
  have hS := pre_stack h
  have hwf := wf0 h A.fr.frame.kept (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + j + bX.length)).toBitVec)
  refine exec_then hin hx hwf (fun _ _ ↦ rfl) (match_fS A.fr) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid, hw, hrdi, hrsi, hrdx, hrcx, hr8, hr9, hk⟩ := hok
  have fr1 : St m0 96 st1.data := St.blk A.fr hS hwf hm1 hmid fun q hq ↦ wr0 hS hw (by omega) hq
  have hin1 := writesIn_of_mid hmid
  have hs1 := blk_same hS hwf hm1 hw (by omega)
  have sm1 := A.sm.of_keep (keepIv_block hwf hm1 hin1 (W0.reg0 hw) (by decide) (by decide))
  have hts1 := ts_keep h (hm1.kept hwf) hs1 (fun q hq ↦ .inl (frame_stack hS hq)) A.ts
  have hcl1 := (tc_keep h (hm1.kept hwf) hs1 (fun q hq ↦ .inl (frame_stack hS hq)) A.ts A.cl).2
  have ld : ∀ {o : Nat} {x : UInt64}, NativeRustcVm.WordAt d.dmem (loc m0 o) x →
      (frameEnv m0 d 5520 [] (fun _ ↦ 0) (Host.addrOf (k + j + bX.length)).toBitVec).load 0 o 8 =
        x.toBitVec := fun hw ↦ load_loc hw
  simp only [PcOk] at hpc1
  rw [hlen] at hpc1
  refine pcCall h hpc fr1 hpc1 sm1 hts1 hcl1 hcs ((hm1.regs .rdi _ hrdi).trans A.x15)
    ((hm1.regs .rdx _ hrdx).trans (ld A.sm.tail.w104)) hJ ((hm1.regs .rcx _ hrcx).trans hrc)
    (by
      rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hrsi]
      show (BitVec.ofNat 64 id).toNat = id
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hid)
    (by
      rw [show reg st1.data .r8 = _ from hm1.regs .r8 _ hr8,
        show reg st1.data .r9 = _ from hm1.regs .r9 _ hr9]
      show ewArg ((frameEnv m0 d 5520 [] (fun _ ↦ 0) (Host.addrOf (k + j + bX.length)).toBitVec).load 0 o8 8)
        ((frameEnv m0 d 5520 [] (fun _ ↦ 0) (Host.addrOf (k + j + bX.length)).toBitVec).load 0 o9 8) = v
      rw [ld h8, ld h9]
      rfl)
    fun m2 fr2 sm2 hts2 hal hcl2 hcs2 ↦ cont m2 (A.regs fr2 sm2 (fun r hr ↦
      (hcs2 r (clRegs_cs r hr).1).trans (hk.reg hm1 (clRegs_cs r hr).2.1)) hts2 hcl2) hal

/-- A test after a push: AL = `1`. -/
theorem pushTest (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0) {bX : List Directive}
    {j : Nat} (hin : bX.IsInfixAt Host.prog (k + j)) (hlen : bX.length = 2)
    (hx : exec bX (fS 104) = some (after bX (fS 104), .cond alZ lF))
    (hok : TestOk (after bX (fS 104))) {w pt tv mem : Array EW} {beta mf bf : EW}
    {s3 : TState} {cs : Array ColumnClaimW} {d : MachineData}
    (A : ClSt a L m0 w pt tv mem beta mf bf s3 cs d) (hal : boolRet d = 1)
    (cont : ∀ d', ClSt a L m0 w pt tv mem beta mf bf s3 cs d' →
      Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨d', Host.addrOf (k + j + 2)⟩) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨d, Host.addrOf (k + j)⟩ :=
  test_spec hp h hin hlen hx hok A.fr (fun hc ↦ by rw [alZ_false hal] at hc; cases hc)
    fun d' fr' hd hk _ ↦ cont d' (A.regs fr' (hd ▸ A.sm) (fun r hr ↦ hk r (clRegs_cs r hr).2.2)
      (hd ▸ A.ts) (hd ▸ A.cl))

omit [Host] in
/-- An element of the memory's scalars by its words. -/
theorem mem_words {d : Mem 64} {mem : Array EW}
    (h : NativeRustcVm.EWsAt d (loc m0 216) mem.toList) (hs : mem.size = 2) {i : Nat} (hi : i < 2) :
    NativeRustcVm.WordAt d (loc m0 (216 + 16 * i)) (mem.getD i 0).c0 ∧
      NativeRustcVm.WordAt d (loc m0 (216 + 16 * i + 8)) (mem.getD i 0).c1 := by
  have := NativeRustcVm.ewsAt_getElem h (i := i) (by rw [Array.length_toList, hs]; exact hi)
  rw [NativeRustcVm.ewAt_iff] at this
  have e : mem.toList[i]'(by rw [Array.length_toList, hs]; exact hi) = mem.getD i 0 := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega : i < mem.size)]
  rw [e] at this
  have e1 : loc m0 216 + BitVec.ofNat 64 (16 * i) = loc m0 (216 + 16 * i) := by
    show off (off (fb m0) 216) (16 * i) = _
    rw [off_off]
  have e2 : loc m0 (216 + 16 * i) + 8#64 = loc m0 (216 + 16 * i + 8) := by
    show off (off (fb m0) (216 + 16 * i)) 8 = _
    rw [off_off]
  rw [e1] at this
  rw [e2] at this
  exact this

end

end NativeRustcVmX64.Bus.VerifyBusBalance
