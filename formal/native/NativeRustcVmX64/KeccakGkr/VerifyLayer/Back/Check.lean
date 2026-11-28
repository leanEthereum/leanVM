module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Back.Plain
public import NativeVm.Math.Keccak.Facts
public import NativeRustcVmX64.Code.Vm.Dot.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqKernel.Names

/-!
# `verify_layer` on x86-64: the second check

From `C4` (`b57`, code index `533`): the local equality kernel into the scratch at `107520`
(`eq_kernel`, `b57`, `b58`), its first 1600 entries against the claim's bit weights (`dot`, `b59`),
`κ t₀ + (κ + t₁) t₂` and its product with the dot (three `EW::mul`, `b60` to `b62`), the
comparison with the plain sumcheck's claim (`b63`, `b64`): at `b65` (`591`) with `C5`: `check`.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.VerifyLayer
open NativeRustcVmX64.Sumcheck (Ctx At testAl_eq)
open NativeRustcVm.Transcript (tstateBytes DecArea TStateAt off)
open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- The three values' words the rest reads. -/
def twl (t : Array EW) : List (Nat × UInt64) :=
  [(72, (t.getD 1 0).c1), (104, (t.getD 2 0).c1), (112, (t.getD 2 0).c0), (184, (t.getD 1 0).c0),
    (192, (t.getD 0 0).c0), (200, (t.getD 0 0).c1)]

/-- **After the second check** (`b65`, code index `591`): the local equality kernel in the scratch
at `107520` (its address at the frame's `56`), the values' words. -/
structure C5 (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (ch : EW) (pt lp t : Array EW)
    (s5 : TState) (d : MachineData) : Prop where
  body : Body m0 (wFront m0) 24 d
  ts : TStateAt d.dmem (tA m0) a s5
  fw : FWs m0 d.dmem (wl3 m0 c ch)
  mu : NativeRustcVm.BufEWAt d.dmem (off (stackBelow m0 2016) 1704) 16
    (keccakInstanceWeights ch).toList
  hpt : NativeRustcVm.EWsAt d.dmem (off (stackBelow m0 2016) 1224) pt.toList
  psz : pt.size = c.point.size
  lsz : lp.size = 11
  eq : NativeRustcVm.EWsAt d.dmem (sA m0 + BitVec.ofNat 64 107520) (eqKernel lp).toList
  w56 : NativeRustcVm.WordAt d.dmem (off (stackBelow m0 2016) 56)
    (.ofBitVec (sA m0 + BitVec.ofNat 64 107520))
  tw : FWs m0 d.dmem (twl t)
  r12 : reg d .r12 = tA m0
  r15 : reg d .r15 = sA m0

end

public section

theorem eqK_len {lp : Array EW} (h : lp.size = 11) : (eqKernel lp).toList.length = 2048 := by
  rw [Array.length_toList, NativeVm.Math.Keccak.eqKernel_size, h]
  decide

theorem cmpB (x y : UInt64) :
    CmpOp.apply .eq .W64 x.toBitVec y.toBitVec = (x == y) := by
  rw [eq64, beq_tbv]

structure CheckKeep (m0 : MachineData) (a : DecArea) (c : KeccakClaimW) (ch : EW)
    (pt lp : Array EW) (s5 : TState) (L : List (Nat × UInt64)) (d : MachineData) : Prop where
  body : Body m0 (wFront m0) 24 d
  ts : TStateAt d.dmem (tA m0) a s5
  fw : FWs m0 d.dmem L
  mu : NativeRustcVm.BufEWAt d.dmem (off (stackBelow m0 2016) 1704) 16
    (keccakInstanceWeights ch).toList
  hpt : NativeRustcVm.EWsAt d.dmem (off (stackBelow m0 2016) 1224) pt.toList
  psz : pt.size = c.point.size
  lsz : lp.size = 11
  eq : NativeRustcVm.EWsAt d.dmem (sA m0 + BitVec.ofNat 64 107520) (eqKernel lp).toList

theorem CheckKeep.blk [Labels] {m0 d d' : MachineData} {a : DecArea} {s s5 : TState}
    {c : KeccakClaimW} {ch : EW} {pt lp : Array EW} {L L' : List (Nat × UInt64)}
    (hpre : VerifyLayerPre a s c m0) (h : CheckKeep m0 a c ch pt lp s5 L d)
    {ret : BitVec 64} {S : SState}
    (hwf : (envB m0 d [] (fun _ ↦ 0) ret).WF)
    (hm : Match (envB m0 d [] (fun _ ↦ 0) ret) S d')
    (hb : Body m0 (wFront m0) 24 d')
    (h0 : S.mem.all (fun w ↦ w.r == 0) = true) (hbr : belowRet 2016 S = true)
    (hin : writesIn S = true) (hmiss : missB 1224 744 S = true)
    (hf : FWs m0 d'.dmem L') : CheckKeep m0 a c ch pt lp s5 L' d' := by
  have hfr := frSame_blk hwf hm hin (show 1224 + 744 ≤ 2024 by decide) hmiss
  exact ⟨hb, ts_blk0 hpre hwf hm h0 hbr h.ts, hf,
    (hfr.sub (o' := 1704) (n' := 264) (by decide) (by decide)).buf h.mu,
    (hfr.sub (o' := 1224) (n' := 480) (by decide) (by decide)).ews h.hpt
      (by rw [Array.length_toList, h.psz]; have := (claimPt hpre (fun _ h ↦ h) h.body).1; omega),
    h.psz, h.lsz, scr_blk0E hpre hwf hm h0 hbr (by decide)
      (by rw [eqK_len h.lsz]; decide) h.eq⟩

theorem CheckKeep.call [Labels] {m0 mc d' : MachineData} {a : DecArea} {s s5 : TState}
    {c : KeccakClaimW} {ch : EW} {pt lp : Array EW} {L L' : List (Nat × UInt64)}
    (hpre : VerifyLayerPre a s c m0) {d : MachineData}
    (h : CheckKeep m0 a c ch pt lp s5 L d)
    {ret : BitVec 64} {S : SState}
    (hwf : (envB m0 d [] (fun _ ↦ 0) ret).WF)
    (hm : Match (envB m0 d [] (fun _ ↦ 0) ret) S mc)
    (hb : Body m0 (wFront m0) 16 mc)
    (h0 : S.mem.all (fun w ↦ w.r == 0) = true) (hbr : belowRet 2016 S = true)
    (hin : writesIn S = true) (hmiss : missB 1224 744 S = true)
    (hf : FWs m0 mc.dmem L') {Sk : Nat} (hSk : 2000 + Sk ≤ 3232)
    (hsv : Saved mc d') (hrsp : rspOf d' = rspOf mc + 8#64)
    (hso : SameOutside mc.dmem d'.dmem (InRange (stackBelow mc Sk) Sk))
    (hL : ∀ q ∈ L', 24 ≤ q.1 ∧ q.1 + 8 ≤ 2024) :
    CheckKeep m0 a c ch pt lp s5 L' d' := by
  obtain ⟨hb', hfr', hts'⟩ := hb.leaf hpre (wFront_outs hpre) hSk hsv hrsp hso
  have hfr := (frSame_blk hwf hm hin (show 1224 + 744 ≤ 2024 by decide) hmiss).trans
    (hfr'.sub (by decide) (by decide))
  exact ⟨hb', hts' _ (ts_blk0 hpre hwf hm h0 hbr h.ts),
    hf.keepIn hfr' (fun q hq ↦ by have := hL q hq; omega),
    (hfr.sub (o' := 1704) (n' := 264) (by decide) (by decide)).buf h.mu,
    (hfr.sub (o' := 1224) (n' := 480) (by decide) (by decide)).ews h.hpt
      (by rw [Array.length_toList, h.psz]; have := (claimPt hpre (fun _ h ↦ h) h.body).1; omega),
    h.psz, h.lsz,
    scr_call hpre (wFront_outs hpre) hb hSk
      (NativeRustcVm.SameOutside.mono hso fun _ hq ↦ Or.inl hq)
      (X := fun _ ↦ False) (by decide) (by rw [eqK_len h.lsz]; decide)
      (fun _ hq ↦ hq.elim)
      (scr_blk0E hpre hwf hm h0 hbr (by decide) (by rw [eqK_len h.lsz]; decide) h.eq)⟩

theorem FWs.append {m0 : MachineData} {d : DataMem} {L L' : List (Nat × UInt64)}
    (h : FWs m0 d L) (h' : FWs m0 d L') : FWs m0 d (L ++ L') :=
  fun q hq ↦ (List.mem_append.mp hq).elim (h q) (h' q)

theorem fw_bounds {L : List (Nat × UInt64)} {os : List Nat} (hos : L.map Prod.fst = os)
    (h : os.all (fun o ↦ decide (24 ≤ o ∧ o + 8 ≤ 2024)) = true) :
    ∀ q ∈ L, 24 ≤ q.1 ∧ q.1 + 8 ≤ 2024 := by
  intro q hq
  have := List.all_eq_true.mp h q.1 (hos ▸ List.mem_map_of_mem hq)
  simpa using this

end

public section

variable [Host] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData} {k : Nat}

/-- **The second check**, from `b57` to `b65`. -/
theorem check (hp : Placed code k) (hpre : VerifyLayerPre a s c m0)
    (hek : Spec (Labels.label NativeRustcVmX64.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost)
    (hdot : Spec (Labels.label NativeRustcVmX64.Vm.Dot.entryLabel) DotPre DotPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {ch : EW} {pt lp t : Array EW} {val : EW} {s5 : TState} {d : MachineData}
    (h : C4 m0 a c ch pt lp t val s5 d)
    (hrun : runL s c m0 = (if checkB c (kap ch) lp t val then rest6 ch pt lp t s5 else none))
    (cont : ∀ d', C5 m0 a c ch pt lp t s5 d' → runL s c m0 = rest6 ch pt lp t s5 →
      Eventually (step1 Host.exe) (Goal a s c m0) ⟨d', Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b65Offset)⟩) :
    Eventually (step1 Host.exe) (Goal a s c m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b57Offset)⟩ := by
  have g := geo_of hpre
  have hWo := wFront_outs hpre
  have hS := pre_stack hpre
  have cx := ctx hpre (F := 2000) (by decide)
  have hN := g.hN; have htop := g.top; have hss := g.hss; have hs := g.hs
  have eL := eqK_len h.lsz
  -- `b57`: `eq_kernel(local point, 11, scratch.eq, 2048)`.
  have hwf := wf0 hS h.body (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b57Offset + b57.length)).toBitVec)
  have hm : Match (envB m0 d [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b57Offset + b57.length)).toBitVec)
      (fr 24) d :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨h.body.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 16) g h.body hwf (blk hp b57_in_code (by simp [b57])) e57
    (fun _ _ ↦ rfl) hm (by decide +kernel) (hex0 (by decide +kernel)) fun st hm1 hpc1 hb1 _ ↦ ?_
  have hts1 := ts_blk0 hpre hwf hm1 (by decide +kernel) (by decide +kernel) h.ts
  have hfw1 : FWs m0 st.data.dmem (wl3 m0 c ch) :=
    FWs.blkO (os := [32, 40, 48, 64, 80, 96, 120, 128, 224]) rfl hwf hm1 (by decide +kernel)
      (by decide +kernel) h.fw
  have hfr1 := frSame_blk (o := 64) (n := 1960) hwf hm1 (by decide +kernel) (by decide)
    (by decide +kernel)
  have hE : BinOp.apply .add .W64 (reg d .r15) (BitVec.ofNat 64 107520) =
      sA m0 + BitVec.ofNat 64 107520 := by rw [add64, h.r15]
  have hw56 : NativeRustcVm.WordAt st.data.dmem (off (stackBelow m0 2016) 56)
      (.ofBitVec (sA m0 + BitVec.ofNat 64 107520)) :=
    fwW hm1 rfl rfl (by decide) (by decide +kernel) (by exact hE)
  have hrdx1 : reg st.data .rdx = sA m0 + BitVec.ofNat 64 107520 :=
    (hm1.regs .rdx _ rfl).trans hE
  have hrdi1 : reg st.data .rdi = off (stackBelow m0 2016) 296 :=
    (hm1.regs .rdi _ rfl).trans (eval_ptr0 296)
  have hrsi1 : reg st.data .rsi = BitVec.ofNat 64 11 := hm1.regs .rsi _ rfl
  have hrcx1 : reg st.data .rcx = BitVec.ofNat 64 2048 := hm1.regs .rcx _ rfl
  have hk1 : ∀ r ∈ [Reg64.r12, .r14, .rbx, .r15], reg st.data r = reg d r :=
    keepR_regs hm1 (by decide +kernel) fun _ ↦ rfl
  have hlp1 := (hfr1.sub (o' := 296) (n' := 176) (by decide) (by decide)).ews h.hlp
    (by rw [Array.length_toList, h.lsz])
  have hat1 := hb1.at_ hpre hWo (by decide)
  have hA := frArea hpre hWo hb1 (Sk := eqKernelStack) (by decide) (o := 296) (n := 176)
    (by decide) (by decide)
  have hSc := scrArea hpre hWo hb1 (Sk := eqKernelStack) (by decide) (o := 107520) (n := 32768)
    (by decide) (by decide)
  have f296 : (off (stackBelow m0 2016) 296).toNat = (rspOf m0).toNat - 2016 + 296 :=
    g.fa (by decide)
  have s107 : (sA m0 + BitVec.ofNat 64 107520).toNat = (sA m0).toNat + 107520 := g.sa (by decide)
  have hfb := g.fbN
  have h11 : (BitVec.ofNat 64 11).toNat = 11 := rfl
  have h2048 : (BitVec.ofNat 64 2048).toNat = 2048 := rfl
  refine call_then hpc1 hek ⟨cx.stackOk hat1 (by decide), by rw [hrsi1]; decide,
    by rw [hrdi1, hrsi1]; exact ⟨⟨hA.1, hA.2.1⟩, hA.2.2.2.2.1⟩,
    by rw [hrdx1, hrcx1]; exact ⟨⟨hSc.1, hSc.2.1⟩, hSc.2.2⟩, ?_⟩ fun st2 hpc2 hrsp2 hq2 ↦ ?_
  · rw [hrdi1, hrsi1, hrdx1, hrcx1, h11, h2048]
    unfold NativeRustcX64.Apart
    rw [f296, s107]
    omega
  obtain ⟨hres, hch, hsv⟩ := hq2
  rw [hrsi1, hrcx1, hrdx1, hrdi1, h11, h2048] at hres
  simp only [show 2 ^ 11 ≤ 2048 from by decide, ↓reduceIte] at hres
  obtain ⟨hrax2, -, hker⟩ := hres
  rw [slice_of hlp1 (by rw [h11, h.lsz])] at hker
  rw [hrdx1, hrcx1, h2048] at hch
  have hso : SameOutside st.data.dmem st2.data.dmem (fun q ↦
      InRange (stackBelow st.data eqKernelStack) eqKernelStack q ∨
        InRange (sA m0 + BitVec.ofNat 64 107520) (16 * 2048) q) :=
    NativeRustcVm.SameOutside.mono hch fun q hq ↦ hq.elim Or.inr Or.inl
  have hb2 : Body m0 (wFront m0) 24 st2.data :=
    Body.callX hpre hWo hb1 hsv hrsp2 (by decide) hso fun q hq ↦
      .inl (scr_wFront hpre (by decide) (by decide) hq)
  have hts2 := ts_callX hpre hWo hb1 hsv.2 (by decide) hso
    (fun q hq ↦ scr_not_t hpre (by decide) hq) hts1
  have hfr2 : FrSame m0 st.data.dmem st2.data.dmem 24 2000 :=
    frSame_call g hb1 (by decide) hso (by decide) (by decide) fun q hq ↦
      scr_not_fr hpre (by decide) hq (by decide)
  have hcs2 := hsv.1
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2 hb2 hts2 hfr2 hcs2 hrax2 hker
  subst hpc2
  -- `b58`: the kernel exists.
  rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b57Offset + b57.length = k + NativeRustcVmX64.Vm.VerifyLayer.b58Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b57_next]]
  have hwf3 := wf0 hS hb2 (vars := fun _ ↦ 0) (ret := 0)
  have hm3 : Match (envB m0 d2 [] (fun _ ↦ 0) 0) (fr 24) d2 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb2.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 24) g hb2 hwf3 (blk hp b58_in_code (by simp [b58])) e58 nofun hm3
    (by decide +kernel) (hex0 (by decide +kernel)) fun st3 hm4 hpc4 hb4 _ ↦ ?_
  simp only [PcOk] at hpc4
  rw [show (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.lit 1)) (.lit 0)).eval
      (envB m0 d2 [] (fun _ ↦ 0) 0) = false by
    simp only [SBool.eval, Sym.eval]
    rw [show (envB m0 d2 [] (fun _ ↦ 0) 0).regs .rax = reg d2 .rax from rfl, hrax2]
    exact test_al1] at hpc4
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc4
  have hd4 : st3.data.dmem = d2.dmem := hm4.dmem_eq hwf3 rfl
  have hk4 : ∀ r ∈ [Reg64.r12, .r14, .rbx, .r15], reg st3.data r = reg d2 r :=
    keepR_regs hm4 (by decide +kernel) fun _ ↦ rfl
  obtain ⟨d3, pc3⟩ := st3
  simp only at hpc4 hb4 hd4 hk4
  subst hpc4
  have hr15_3 : reg d3 .r15 = sA m0 :=
    (hk4 .r15 (by simp)).trans ((hcs2 .r15 rfl).trans ((hk1 .r15 (by simp)).trans h.r15))
  have hr14_3 : reg d3 .r14 = val.c0.toBitVec :=
    (hk4 .r14 (by simp)).trans ((hcs2 .r14 rfl).trans ((hk1 .r14 (by simp)).trans h.r14))
  have hrbx_3 : reg d3 .rbx = val.c1.toBitVec :=
    (hk4 .rbx (by simp)).trans ((hcs2 .rbx rfl).trans ((hk1 .rbx (by simp)).trans h.rbx))
  have hfw3 : FWs m0 d3.dmem (wl3 m0 c ch) := by
    rw [hd4]; exact FWs.keepR (os := [32, 40, 48, 64, 80, 96, 120, 128, 224]) rfl hfr2
      (by decide +kernel) hfw1
  have hfrA : FrSame m0 d.dmem d3.dmem 64 1960 := by
    rw [hd4]; exact hfr1.trans (hfr2.sub (by decide) (by decide))
  have ht3 := (hfrA.sub (o' := 136) (n' := 48) (by decide) (by decide)).ews h.ht
    (by rw [Array.length_toList, h.tsz])
  have heq3 : NativeRustcVm.EWsAt d3.dmem (sA m0 + BitVec.ofNat 64 107520) (eqKernel lp).toList :=
    by rw [hd4]; exact hker
  -- `b59`: the values loaded, `dot(eq[..1600], weights)`.
  rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b58Offset + b58.length = k + NativeRustcVmX64.Vm.VerifyLayer.b59Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b58_next]]
  have hwf5 := wf0 hS hb4 (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b59Offset + b59.length)).toBitVec)
  have hm5 : Match (envB m0 d3 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b59Offset + b59.length)).toBitVec)
      (fr 24) d3 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hb4.rsp, trivial⟩ trivial trivial trivial
  have tL0 := ewsLoad (ex := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b59Offset + b59.length)).toBitVec) ht3 (i := 0) (by rw [h.tsz]; decide)
    (o0 := 136) (o1 := 144) rfl rfl
  have tL1 := ewsLoad (ex := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b59Offset + b59.length)).toBitVec) ht3 (i := 1) (by rw [h.tsz]; decide)
    (o0 := 152) (o1 := 160) rfl rfl
  have tL2 := ewsLoad (ex := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b59Offset + b59.length)).toBitVec) ht3 (i := 2) (by rw [h.tsz]; decide)
    (o0 := 168) (o1 := 176) rfl rfl
  refine Body.blk (o' := 16) g hb4 hwf5 (blk hp b59_in_code (by simp [b59])) e59
    (fun _ _ ↦ rfl) hm5 (by decide +kernel) (hex0 (by decide +kernel)) fun st5 hm6 hpc6 hb6 _ ↦ ?_
  have hts6 := ts_blk0 hpre hwf5 hm6 (by decide +kernel) (by decide +kernel)
    (by rw [hd4]; exact hts2)
  have hfw6 : FWs m0 st5.data.dmem (wl3 m0 c ch) :=
    FWs.blkO (os := [32, 40, 48, 64, 80, 96, 120, 128, 224]) rfl hwf5 hm6 (by decide +kernel)
      (by decide +kernel) hfw3
  have hL59 : FWs m0 st5.data.dmem
      [(72, (t.getD 1 0).c1), (104, (t.getD 2 0).c1), (112, (t.getD 2 0).c0)] := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact fwW hm6 (o := 72) (v := .load 0 160 8) rfl rfl (by decide) (by decide +kernel) tL1.2
    · exact fwW hm6 (o := 104) (v := .load 0 176 8) rfl rfl (by decide) (by decide +kernel) tL2.2
    · exact fwW hm6 (o := 112) (v := .load 0 168 8) rfl rfl (by decide) (by decide +kernel) tL2.1
  have hfr6 := frSame_blk (o := 120) (n := 1904) hwf5 hm6 (by decide +kernel) (by decide)
    (by decide +kernel)
  have heq6 := scr_blk0E hpre hwf5 hm6 (by decide +kernel) (by decide +kernel) (o := 107520)
    (by decide) (by rw [eL]; decide) heq3
  have hr12_6 : reg st5.data .r12 = (t.getD 0 0).c0.toBitVec := (hm6.regs .r12 _ rfl).trans tL0.1
  have hr13_6 : reg st5.data .r13 = (t.getD 0 0).c1.toBitVec := (hm6.regs .r13 _ rfl).trans tL0.2
  have hrbp_6 : reg st5.data .rbp = (t.getD 1 0).c0.toBitVec := (hm6.regs .rbp _ rfl).trans tL1.1
  have hk6 : ∀ r ∈ [Reg64.r14, .rbx, .r15], reg st5.data r = reg d3 r :=
    keepR_regs hm6 (by decide +kernel) fun _ ↦ rfl
  have hrdi6 : reg st5.data .rdi = sA m0 + BitVec.ofNat 64 107520 := by
    rw [show reg st5.data .rdi = _ from hm6.regs .rdi _ rfl]
    show BinOp.apply .add .W64 (reg d3 .r15) (BitVec.ofNat 64 107520) = _
    rw [add64, hr15_3]
  have hrdx6 : reg st5.data .rdx = sA m0 + BitVec.ofNat 64 25600 := by
    rw [show reg st5.data .rdx = _ from hm6.regs .rdx _ rfl]
    simp only [Sym.eval]
    rw [fload8 (hfw3 (120, .ofBitVec (sA m0 + 25600#64)) (by fw_mem))]
  have hrsi6 : reg st5.data .rsi = BitVec.ofNat 64 1600 := hm6.regs .rsi _ rfl
  have hrcx6 : reg st5.data .rcx = BitVec.ofNat 64 1600 := hm6.regs .rcx _ rfl
  have hat6 := hb6.at_ hpre hWo (by decide)
  have hD1 := scrArea hpre hWo hb6 (Sk := dotStack) (by decide) (o := 107520) (n := 25600)
    (by decide) (by decide)
  have hD2 := scrArea hpre hWo hb6 (Sk := dotStack) (by decide) (o := 25600) (n := 25600)
    (by decide) (by decide)
  have hwts := Body.weights hpre (fun _ h ↦ h) hb6
  refine leafX hpre hWo (Sk := dotStack) (by decide) hdot
    (fun _ _ hq ↦ ⟨changes_stk hq.2.1, hq.2.2⟩) hpc6 hb6
    ⟨cx.stackOk hat6 (by decide), by rw [hrdi6, hrsi6]; exact ⟨⟨hD1.1, hD1.2.1⟩, hD1.2.2⟩,
      by rw [hrdx6, hrcx6]; exact ⟨⟨hD2.1, hD2.2.1⟩, hD2.2.2⟩⟩
    fun d7 hq7 hb7 hfr7 hts7 hcs7 hso7 ↦ ?_
  have hdot7 : ewArg (reg d7 .rax) (reg d7 .rdx) =
      dot ((eqKernel lp).extract 0 keccakBits) c.weights := by
    have := hq7.1
    rw [hrdi6, hrsi6, hrdx6, hrcx6, slice_of (ews_extract 1600 heq6) (by
        rw [Array.size_extract, NativeVm.Math.Keccak.eqKernel_size, h.lsz]; rfl),
      slice_of hwts.2 (by rw [hwts.1]; rfl)] at this
    exact this
  -- `b60`: `κ t₀`.
  rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b59Offset + b59.length = k + NativeRustcVmX64.Vm.VerifyLayer.b60Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b59_next]]
  let vdot := dot ((eqKernel lp).extract 0 keccakBits) c.weights
  let L7 := wl3 m0 c ch ++
    [(56, .ofBitVec (sA m0 + BitVec.ofNat 64 107520)),
      (72, (t.getD 1 0).c1), (104, (t.getD 2 0).c1), (112, (t.getD 2 0).c0)]
  have hf7 : FWs m0 d7.dmem L7 := by
    apply FWs.append
    · exact FWs.keepR (os := [32, 40, 48, 64, 80, 96, 120, 128, 224]) rfl hfr7
        (by decide +kernel) hfw6
    · have h56' := (hfr2.sub (o' := 56) (n' := 8) (by decide) (by decide)).word hw56 (by decide)
      have h56'' : NativeRustcVm.WordAt d3.dmem (off (stackBelow m0 2016) 56)
          (.ofBitVec (sA m0 + BitVec.ofNat 64 107520)) := by rw [hd4]; exact h56'
      have h56''' := (frSame_blk (o := 56) (n := 8) hwf5 hm6 (by decide +kernel)
        (by decide) (by decide +kernel)).word h56'' (by decide)
      apply FWs.keepR (os := [56, 72, 104, 112]) rfl hfr7 (by decide +kernel)
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact h56'''
      · exact hL59 _ (by fw_mem)
      · exact hL59 _ (by fw_mem)
      · exact hL59 _ (by fw_mem)
  have hfrAll := (hfrA.sub (o' := 1224) (n' := 744) (by decide) (by decide)).trans
    ((hfr6.sub (by decide) (by decide)).trans (hfr7.sub (by decide) (by decide)))
  have hk7 : CheckKeep m0 a c ch pt lp s5 L7 d7 :=
    ⟨hb7, hts7 _ hts6, hf7,
      (hfrAll.sub (o' := 1704) (n' := 264) (by decide) (by decide)).buf h.mu,
      (hfrAll.sub (o' := 1224) (n' := 480) (by decide) (by decide)).ews h.hpt
        (by rw [Array.length_toList, h.psz]; have := (claimPt hpre (fun _ h ↦ h) h.body).1; omega),
      h.psz, h.lsz,
      scr_call hpre hWo hb6 (Sk := dotStack) (by decide)
        (NativeRustcVm.SameOutside.mono hso7 fun _ hq ↦ Or.inl hq)
        (X := fun _ ↦ False) (by decide) (by rw [eL]; decide) (fun _ hq ↦ hq.elim) heq6⟩
  have h12_7 := (hcs7 .r12 rfl).trans hr12_6
  have h13_7 := (hcs7 .r13 rfl).trans hr13_6
  have hbp_7 := (hcs7 .rbp rfl).trans hrbp_6
  have h14_7 := (hcs7 .r14 rfl).trans ((hk6 .r14 (by simp)).trans hr14_3)
  have hbx_7 := (hcs7 .rbx rfl).trans ((hk6 .rbx (by simp)).trans hrbx_3)
  have h15_7 := (hcs7 .r15 rfl).trans ((hk6 .r15 (by simp)).trans hr15_3)
  have hwf8 := wf0 hS hk7.body (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b60Offset + b60.length)).toBitVec)
  have hm8 : Match (envB m0 d7 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b60Offset + b60.length)).toBitVec)
      (fr 24) d7 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hk7.body.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 16) g hk7.body hwf8 (blk hp b60_in_code (by simp [b60])) e60
    (fun _ _ ↦ rfl) hm8 (by decide +kernel) (hex0 (by decide +kernel)) fun st8 hm9 hpc9 hb9 _ ↦ ?_
  have hkap0 := hf7 (32, (kap ch).c0) (by apply List.mem_append_left; fw_mem)
  have hkap1 := hf7 (48, (kap ch).c1) (by apply List.mem_append_left; fw_mem)
  have hA9 : ewArg (reg st8.data .rdi) (reg st8.data .rsi) = kap ch := by
    rw [show reg st8.data .rdi = _ from hm9.regs .rdi _ rfl,
      show reg st8.data .rsi = _ from hm9.regs .rsi _ rfl]
    simp only [Sym.eval]
    rw [fload8 hkap0, fload8 hkap1, ewArg_ew]
  have hB9 : ewArg (reg st8.data .rdx) (reg st8.data .rcx) = t.getD 0 0 := by
    rw [show reg st8.data .rdx = _ from hm9.regs .rdx _ rfl,
      show reg st8.data .rcx = _ from hm9.regs .rcx _ rfl]
    change ewArg (reg d7 .r12) (reg d7 .r13) = _
    rw [h12_7, h13_7, ewArg_ew]
  let L9 := L7 ++ [(216, vdot.c0), (208, vdot.c1), (88, val.c0), (24, val.c1),
    (192, (t.getD 0 0).c0), (200, (t.getD 0 0).c1)]
  have hf9 : FWs m0 st8.data.dmem L9 := by
    apply FWs.append
    · exact FWs.blkO (os := [32, 40, 48, 64, 80, 96, 120, 128, 224, 56, 72, 104, 112])
        rfl hwf8 hm9 (by decide +kernel) (by decide +kernel) hf7
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
      · exact fwW hm9 (o := 216) (v := .reg .rax) rfl rfl (by decide) (by decide +kernel) (ewArg_c0 hdot7)
      · exact fwW hm9 (o := 208) (v := .reg .rdx) rfl rfl (by decide) (by decide +kernel) (ewArg_c1 hdot7)
      · exact fwW hm9 (o := 88) (v := .reg .r14) rfl rfl (by decide) (by decide +kernel) h14_7
      · exact fwW hm9 (o := 24) (v := .reg .rbx) rfl rfl (by decide) (by decide +kernel) hbx_7
      · exact fwW hm9 (o := 192) (v := .reg .r12) rfl rfl (by decide) (by decide +kernel) h12_7
      · exact fwW hm9 (o := 200) (v := .reg .r13) rfl rfl (by decide) (by decide +kernel) h13_7
  have hr14_9 : reg st8.data .r14 = (kap ch).c0.toBitVec :=
    (hm9.regs .r14 _ rfl).trans (fload8 hkap0)
  have hrbx_9 : reg st8.data .rbx = (kap ch).c1.toBitVec :=
    (hm9.regs .rbx _ rfl).trans (fload8 hkap1)
  have hbp9 : reg st8.data .rbp = (t.getD 1 0).c0.toBitVec :=
    (hm9.regs .rbp _ rfl).trans hbp_7
  have h15_9 : reg st8.data .r15 = sA m0 := (hm9.regs .r15 _ rfl).trans h15_7
  refine call_then hpc9 hmul (cx.stackOk (hb9.at_ hpre hWo (by decide)) (by decide))
    fun st10 hpc10 hrsp10 hq10 ↦ ?_
  have hm10 := mulE hq10
  rw [hA9, hB9] at hm10
  have hk10 := hk7.call hpre hwf8 hm9 hb9 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hf9 (Sk := ewMulStack) (by decide)
    hq10.2.2.2 hrsp10 hq10.2.2.1
    (fw_bounds (os := [32, 40, 48, 64, 80, 96, 120, 128, 224, 56, 72, 104, 112,
      216, 208, 88, 24, 192, 200]) rfl (by decide +kernel))
  have h14_10 := (hq10.2.2.2.1 .r14 rfl).trans hr14_9
  have hbx_10 := (hq10.2.2.2.1 .rbx rfl).trans hrbx_9
  have hbp10 := (hq10.2.2.2.1 .rbp rfl).trans hbp9
  have h15_10 := (hq10.2.2.2.1 .r15 rfl).trans h15_9
  obtain ⟨d10, pc10⟩ := st10
  simp only at hpc10 hm10 hk10 h14_10 hbx_10 hbp10 h15_10
  subst hpc10
  rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b60Offset + b60.length = k + NativeRustcVmX64.Vm.VerifyLayer.b61Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b60_next]]
  have hwf11 := wf0 hS hk10.body (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b61Offset + b61.length)).toBitVec)
  have hm11 : Match (envB m0 d10 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b61Offset + b61.length)).toBitVec)
      (fr 24) d10 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hk10.body.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 16) g hk10.body hwf11 (blk hp b61_in_code (by simp [b61])) e61
    (fun _ _ ↦ rfl) hm11 (by decide +kernel) (hex0 (by decide +kernel)) fun st11 hm12 hpc12 hb12 _ ↦ ?_
  have hw72 := hk10.fw (72, (t.getD 1 0).c1)
    (by apply List.mem_append_left; apply List.mem_append_right; fw_mem)
  have hw104 := hk10.fw (104, (t.getD 2 0).c1)
    (by apply List.mem_append_left; apply List.mem_append_right; fw_mem)
  have hw112 := hk10.fw (112, (t.getD 2 0).c0)
    (by apply List.mem_append_left; apply List.mem_append_right; fw_mem)
  have hw24 := hk10.fw (24, val.c1) (by apply List.mem_append_right; fw_mem)
  have hA12 : ewArg (reg st11.data .rdi) (reg st11.data .rsi) = kap ch + t.getD 1 0 := by
    rw [show reg st11.data .rdi = _ from hm12.regs .rdi _ rfl,
      show reg st11.data .rsi = _ from hm12.regs .rsi _ rfl]
    simp only [Sym.eval, NativeRustcVmX64.Arrays.xor_eval]
    change ewArg (d10.regs.get64 .r14 ^^^ d10.regs.get64 .rbp)
      (d10.regs.get64 .rbx ^^^ (envB m0 d10 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b61Offset + b61.length)).toBitVec).load 0 72 8) = _
    rw [fload8 hw72, h14_10, hbx_10, hbp10, NativeRustcVmX64.Arrays.ewArg_xor,
      ewArg_ew, ewArg_ew]
  have hB12 : ewArg (reg st11.data .rdx) (reg st11.data .rcx) = t.getD 2 0 := by
    rw [show reg st11.data .rdx = _ from hm12.regs .rdx _ rfl,
      show reg st11.data .rcx = _ from hm12.regs .rcx _ rfl]
    simp only [Sym.eval]
    rw [fload8 hw112, fload8 hw104, ewArg_ew]
  let L12 := L9 ++ [(184, (t.getD 1 0).c0)]
  have hf12 : FWs m0 st11.data.dmem L12 := by
    apply FWs.append
    · exact FWs.blkO (os := [32, 40, 48, 64, 80, 96, 120, 128, 224, 56, 72, 104, 112,
        216, 208, 88, 24, 192, 200]) rfl hwf11 hm12 (by decide +kernel) (by decide +kernel) hk10.fw
    · intro q hq
      have : q = (184, (t.getD 1 0).c0) := by simpa using hq
      subst q
      exact fwW hm12 (o := 184) (v := .reg .rbp) rfl rfl (by decide) (by decide +kernel) hbp10
  have hp12 : ewArg (reg st11.data .r12) (reg st11.data .r13) = kap ch * t.getD 0 0 := by
    rw [show reg st11.data .r12 = _ from hm12.regs .r12 _ rfl,
      show reg st11.data .r13 = _ from hm12.regs .r13 _ rfl]
    exact hm10
  have hbx12 : reg st11.data .rbx = val.c1.toBitVec :=
    (hm12.regs .rbx _ rfl).trans (fload8 hw24)
  have h15_12 : reg st11.data .r15 = sA m0 := (hm12.regs .r15 _ rfl).trans h15_10
  refine call_then hpc12 hmul (cx.stackOk (hb12.at_ hpre hWo (by decide)) (by decide))
    fun st13 hpc13 hrsp13 hq13 ↦ ?_
  have hm13 := mulE hq13
  rw [hA12, hB12] at hm13
  have hk13 := hk10.call hpre hwf11 hm12 hb12 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hf12 (Sk := ewMulStack) (by decide)
    hq13.2.2.2 hrsp13 hq13.2.2.1
    (fw_bounds (os := [32, 40, 48, 64, 80, 96, 120, 128, 224, 56, 72, 104, 112,
      216, 208, 88, 24, 192, 200, 184]) rfl (by decide +kernel))
  have hp13 : ewArg (reg st13.data .r12) (reg st13.data .r13) = kap ch * t.getD 0 0 := by
    change ewArg (st13.data.regs.get64 .r12) (st13.data.regs.get64 .r13) = _
    rw [hq13.2.2.2.1 .r12 rfl, hq13.2.2.2.1 .r13 rfl]
    exact hp12
  have hbx13 := (hq13.2.2.2.1 .rbx rfl).trans hbx12
  have h15_13 := (hq13.2.2.2.1 .r15 rfl).trans h15_12
  obtain ⟨d13, pc13⟩ := st13
  simp only at hpc13 hm13 hk13 hp13 hbx13 h15_13
  subst hpc13
  rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b61Offset + b61.length = k + NativeRustcVmX64.Vm.VerifyLayer.b62Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b61_next]]
  have hwf14 := wf0 hS hk13.body (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b62Offset + b62.length)).toBitVec)
  have hm14 : Match (envB m0 d13 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyLayer.b62Offset + b62.length)).toBitVec)
      (fr 24) d13 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hk13.body.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 16) g hk13.body hwf14 (blk hp b62_in_code (by simp [b62])) e62
    (fun _ _ ↦ rfl) hm14 (by decide +kernel) (hex0 (by decide +kernel)) fun st14 hm15 hpc15 hb15 _ ↦ ?_
  have hw216 := hk13.fw (216, vdot.c0)
    (by apply List.mem_append_left; apply List.mem_append_right; fw_mem)
  have hw208 := hk13.fw (208, vdot.c1)
    (by apply List.mem_append_left; apply List.mem_append_right; fw_mem)
  have hw40 := hk13.fw (40, .ofBitVec (tA m0))
    (by apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left; fw_mem)
  have hA15 : ewArg (reg st14.data .rdi) (reg st14.data .rsi) = vdot := by
    rw [show reg st14.data .rdi = _ from hm15.regs .rdi _ rfl,
      show reg st14.data .rsi = _ from hm15.regs .rsi _ rfl]
    simp only [Sym.eval]
    rw [fload8 hw216, fload8 hw208, ewArg_ew]
  have hB15 : ewArg (reg st14.data .rdx) (reg st14.data .rcx) =
      kap ch * t.getD 0 0 + (kap ch + t.getD 1 0) * t.getD 2 0 := by
    rw [show reg st14.data .rdx = _ from hm15.regs .rdx _ rfl,
      show reg st14.data .rcx = _ from hm15.regs .rcx _ rfl]
    simp only [Sym.eval, NativeRustcVmX64.Arrays.xor_eval]
    rw [NativeRustcVmX64.Arrays.ewArg_xor]
    change ewArg (reg d13 .r12) (reg d13 .r13) + ewArg (reg d13 .rax) (reg d13 .rdx) = _
    rw [hp13, hm13]
  have hf15 := FWs.blkO (os := [32, 40, 48, 64, 80, 96, 120, 128, 224, 56, 72, 104, 112,
      216, 208, 88, 24, 192, 200, 184]) rfl hwf14 hm15 (by decide +kernel)
      (by decide +kernel) hk13.fw
  have h12_15 : reg st14.data .r12 = tA m0 := (hm15.regs .r12 _ rfl).trans (fload8 hw40)
  have hbx15 : reg st14.data .rbx = val.c1.toBitVec := (hm15.regs .rbx _ rfl).trans hbx13
  have h15_15 : reg st14.data .r15 = sA m0 := (hm15.regs .r15 _ rfl).trans h15_13
  refine call_then hpc15 hmul (cx.stackOk (hb15.at_ hpre hWo (by decide)) (by decide))
    fun st16 hpc16 hrsp16 hq16 ↦ ?_
  have hm16 := mulE hq16
  rw [hA15, hB15] at hm16
  have hk16 := hk13.call hpre hwf14 hm15 hb15 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hf15 (Sk := ewMulStack) (by decide)
    hq16.2.2.2 hrsp16 hq16.2.2.1
    (fw_bounds (os := [32, 40, 48, 64, 80, 96, 120, 128, 224, 56, 72, 104, 112,
      216, 208, 88, 24, 192, 200, 184]) rfl (by decide +kernel))
  have h12_16 := (hq16.2.2.2.1 .r12 rfl).trans h12_15
  have hbx16 := (hq16.2.2.2.1 .rbx rfl).trans hbx15
  have h15_16 := (hq16.2.2.2.1 .r15 rfl).trans h15_15
  obtain ⟨d16, pc16⟩ := st16
  simp only at hpc16 hm16 hk16 h12_16 hbx16 h15_16
  subst hpc16
  rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b62Offset + b62.length = k + NativeRustcVmX64.Vm.VerifyLayer.b63Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b62_next]]
  have hcB : checkB c (kap ch) lp t val =
      ((UInt64.ofBitVec (reg d16 .rax) == val.c0) &&
        (UInt64.ofBitVec (reg d16 .rdx) == val.c1)) := by
    unfold checkB
    rw [← hm16, ew_beq]
    rfl
  have hwf17 := wf0 hS hk16.body (vars := fun _ ↦ 0) (ret := 0)
  have hm17 : Match (envB m0 d16 [] (fun _ ↦ 0) 0) (fr 24) d16 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hk16.body.rsp, trivial⟩ trivial trivial trivial
  refine Body.blk (o' := 24) g hk16.body hwf17 (blk hp b63_in_code (by simp [b63])) e63 nofun
    hm17 (by decide +kernel) (hex0 (by decide +kernel)) fun st17 hm18 hpc18 hb18 _ ↦ ?_
  have hd18 : st17.data.dmem = d16.dmem := hm18.dmem_eq hwf17 rfl
  have hregs18 : ∀ r, reg st17.data r = reg d16 r := by
    have hh := keepR_regs hm18 (d := d16)
      (rs := [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15])
      (by decide +kernel) (fun _ ↦ rfl)
    intro r
    by_cases hr : r = .rsp
    · subst r; exact hb18.fr.sp.trans hk16.body.fr.sp.symm
    · exact hh r (by cases r <;> simp at hr ⊢)
  have hw88 := hk16.fw (88, val.c0)
    (by apply List.mem_append_left; apply List.mem_append_right; fw_mem)
  simp only [PcOk] at hpc18
  rw [show (SBool.not (SBool.cmp .eq .W64 (.reg .rax) (.load 0 88 8))).eval
      (envB m0 d16 [] (fun _ ↦ 0) 0) = !(UInt64.ofBitVec (reg d16 .rax) == val.c0) by
    simp only [SBool.eval, Sym.eval]
    rw [fload8 hw88]
    exact congrArg Bool.not (cmpB (UInt64.ofBitVec (reg d16 .rax)) val.c0)] at hpc18
  obtain ⟨d18, pc18⟩ := st17
  simp only at hpc18 hb18 hd18 hregs18
  cases hb0 : (UInt64.ofBitVec (reg d16 .rax) == val.c0) with
  | false =>
    simp only [hb0, Bool.not_false, ↓reduceIte] at hpc18
    rw [lbl hp b86_in_code rfl] at hpc18
    subst hpc18
    exact exit49 hp hpre hWo hb18 (by rw [hrun, hcB, hb0]; rfl)
  | true =>
    simp only [hb0, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc18
    subst hpc18
    rw [show k + NativeRustcVmX64.Vm.VerifyLayer.b63Offset + b63.length = k + NativeRustcVmX64.Vm.VerifyLayer.b64Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyLayer.b63_next]]
    have hwf19 := wf0 hS hb18 (vars := fun _ ↦ 0) (ret := 0)
    have hm19 : Match (envB m0 d18 [] (fun _ ↦ 0) 0) (fr 24) d18 :=
      match_ofMachine ⟨rfl, trivial⟩ ⟨hb18.rsp, trivial⟩ trivial trivial trivial
    refine Body.blk (o' := 24) g hb18 hwf19 (blk hp b64_in_code (by simp [b64])) e64 nofun
      hm19 (by decide +kernel) (hex0 (by decide +kernel)) fun st19 hm20 hpc20 hb20 _ ↦ ?_
    have hd20 : st19.data.dmem = d16.dmem := (hm20.dmem_eq hwf19 rfl).trans hd18
    have hregs20 : ∀ r, reg st19.data r = reg d16 r := by
      have hh := keepR_regs hm20 (d := d18)
        (rs := [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15])
        (by decide +kernel) (fun _ ↦ rfl)
      intro r
      apply Eq.trans (b := reg d18 r) _ (hregs18 r)
      by_cases hr : r = .rsp
      · subst r; exact hb20.fr.sp.trans hb18.fr.sp.symm
      · exact hh r (by cases r <;> simp at hr ⊢)
    simp only [PcOk] at hpc20
    rw [show (SBool.not (SBool.cmp .eq .W64 (.reg .rdx) (.reg .rbx))).eval
        (envB m0 d18 [] (fun _ ↦ 0) 0) = !(UInt64.ofBitVec (reg d16 .rdx) == val.c1) by
      simp only [SBool.eval, Sym.eval]
      change Bool.not (CmpOp.apply .eq .W64 (reg d18 .rdx) (reg d18 .rbx)) =
        Bool.not (UInt64.ofBitVec (reg d16 .rdx) == val.c1)
      rw [hregs18 .rdx, hregs18 .rbx, show reg d16 .rbx = val.c1.toBitVec from hbx16]
      exact congrArg Bool.not (cmpB (UInt64.ofBitVec (reg d16 .rdx)) val.c1)] at hpc20
    obtain ⟨d20, pc20⟩ := st19
    simp only at hpc20 hb20 hd20 hregs20
    cases hb1 : (UInt64.ofBitVec (reg d16 .rdx) == val.c1) with
    | false =>
      simp only [hb1, Bool.not_false, ↓reduceIte] at hpc20
      rw [lbl hp b86_in_code rfl] at hpc20
      subst hpc20
      exact exit49 hp hpre hWo hb20 (by rw [hrun, hcB, hb0, hb1]; rfl)
    | true =>
      simp only [hb1, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc20
      subst hpc20
      refine cont d20 ⟨hb20, by rw [hd20]; exact hk16.ts, ?_,
        by rw [hd20]; exact hk16.mu, by rw [hd20]; exact hk16.hpt,
        h.psz, h.lsz, by rw [hd20]; exact hk16.eq, ?_, ?_,
        (hregs20 .r12).trans h12_16, (hregs20 .r15).trans h15_16⟩
        (by rw [hrun, hcB, hb0, hb1]; rfl)
      · rw [hd20]
        exact fun q hq ↦ hk16.fw q (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ hq)))
      · rw [hd20]
        exact hk16.fw (56, .ofBitVec (sA m0 + BitVec.ofNat 64 107520))
          (by apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right; fw_mem)
      · rw [hd20]
        intro q hq
        simp only [twl, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hk16.fw (72, (t.getD 1 0).c1) (by apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right; fw_mem)
        · exact hk16.fw (104, (t.getD 2 0).c1) (by apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right; fw_mem)
        · exact hk16.fw (112, (t.getD 2 0).c0) (by apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right; fw_mem)
        · exact hk16.fw (184, (t.getD 1 0).c0) (by apply List.mem_append_right; fw_mem)
        · exact hk16.fw (192, (t.getD 0 0).c0) (by apply List.mem_append_left; apply List.mem_append_right; fw_mem)
        · exact hk16.fw (200, (t.getD 0 0).c1) (by apply List.mem_append_left; apply List.mem_append_right; fw_mem)

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
