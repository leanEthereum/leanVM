module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Ar
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

/-!
# `verify_keccak`'s copies (x86-64)

`cpStep`: a block ending in a call of `memcpy` (RSP at the frame's offset `48`), from `D`'s `n`
bytes of the source `Sr`: what was at `Sr` at the call is at `D` after it (`Img`), the change of
memory the block's writes, the frame below RSP and `D`'s bytes.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak
open NativeVm.Model
open NativeRustcVm.Transcript (DecArea TStateAt)
open NativeRustcVm.KeccakGkr (off)

public section

section
variable [Labels] {m0 mc : MachineData} {a : DecArea} {inst : Array EW} {wr : Nat → Bool}
  {oc : Nat}

/-- A frame range above RSP misses the return address's slot. -/
theorem apF (c : Ctx a inst m0) (ca : CallAt m0 wr oc mc) {o n : Nat} (ho : oc + 8 ≤ o)
    (hn : o + n ≤ 3368) (hn0 : 0 < n) : NativeRustcVm.Apart (off (fb m0) o) n (rspOf mc) 8 := by
  have hr := ca.rsp c
  have := c.sp
  have := ca.oc8
  show _ ∨ _
  rw [off_fb c (by omega), hr]
  omega

/-- A region's range misses the return address's slot. -/
theorem apR (c : Ctx a inst m0) (ca : CallAt m0 wr oc mc) {i o n : Nat} (h1 : 1 ≤ i) (h4 : i ≤ 4)
    (hn : o + n ≤ rsz i) (hn0 : 0 < n) : NativeRustcVm.Apart (off (ob m0 i) o) n (rspOf mc) 8 := by
  have hr := ca.rsp c
  have := c.sp
  have := ca.oc8
  have := vk_eq
  have hS := ob_S c h1 h4
  show _ ∨ _
  rw [offR c h1 h4 (by omega), hr]
  omega

end

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

/-- **A block and `memcpy`.** -/
theorem cpStep (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) {wr : Nat → Bool}
    {T S T' S' : SState} {vals vals' : Nat → BitVec 64} {o : Nat} {st : MachineState}
    {srcRs : List (BitVec 64 × Nat)}
    (hat : At m0 k o wr T vals st) {ds : List Directive} (hds : ds.IsInfixAt code o) (hne : ds ≠ [])
    (hrun : exec ds S = some (S', .call NativeRustcVmX64.Vm.Memcpy.entryLabel)) (hw0 : frameW S' = true)
    (hsp : S'.reg .rsp = some (.ptr 0 48)) {D Sr : BitVec 64} {n : Nat}
    (hdi : ∀ mc, Match (envZ m0 st.data 3344 3368 srcRs vals
      (Host.addrOf (k + (o + ds.length))).toBitVec) S' mc → reg mc .rdi = D)
    (hsi : ∀ mc, Match (envZ m0 st.data 3344 3368 srcRs vals
      (Host.addrOf (k + (o + ds.length))).toBitVec) S' mc → reg mc .rsi = Sr)
    (hdx : S'.reg .rdx = some (.lit n)) (hn : n < 2 ^ 64)
    (hD : ∀ mc, CallAt m0 wr 48 mc → NativeRustcVm.Mapped mc.dmem D n ∧
      NativeRustcVm.NoWrap D n ∧ NativeRustcVm.Apart D n (rspOf mc) 8)
    (hS : ∀ mc, CallAt m0 wr 48 mc → NativeRustcVm.Mapped mc.dmem Sr n ∧ NativeRustcVm.NoWrap Sr n)
    (hDS : NativeRustcVm.Apart D n Sr n)
    {Lc : List (Nat × Nat)} {Oc : List (Nat × Nat × Nat)}
    (hR : ∀ q, InRange D n q → ChgR m0 Lc Oc q)
    (hLc : okL Lc = true) (hOc : okO Oc = true) (hwO : wrO wr Oc = true)
    (htm : tplMiss 48 Lc T' = true)
    (hok : tplOk T' = true) (hrspT : T'.reg .rsp = some (.ptr 0 56))
    {L LW : List (Nat × Sym)} (hL : rlinksOf true S' T' noRsp = some L)
    (hLW : wlinks S' T'.mem = some LW)
    (hvals : ∀ ret, ∀ p ∈ L ++ LW,
      p.2.eval (envZ m0 st.data 3344 3368 srcRs vals ret) = vals' p.1)
    (hrax : T'.reg .rax = some (.reg .rax)) (hrdx : T'.reg .rdx = some (.reg .rdx))
    (hsz : T'.regions = sizes) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hal : T'.aliases = []) (hbd : T'.bounds = [])
    {R : MachineState → Prop}
    (cont : ∀ st' mc, At m0 k (o + ds.length) wr T' vals' st' →
      Match (envZ m0 st.data 3344 3368 srcRs vals
        (Host.addrOf (k + (o + ds.length))).toBitVec) S' mc →
      Img mc.dmem Sr st'.data.dmem D n →
      Chg m0 st.data.dmem mc.dmem (wsL S') [] →
      Chg m0 mc.dmem st'.data.dmem ((0, 48) :: Lc) Oc →
      Chg m0 st.data.dmem st'.data.dmem (wsL S' ++ (0, 48) :: Lc) Oc →
      Kept st.data.dmem st'.data.dmem → Eventually (step1 Host.exe) R st') (hknown : T'.known = [] := by rfl) 
    (hm : ∀ ret, Match (envZ m0 st.data 3344 3368 srcRs vals ret) S st.data := by
      exact hat.2.mt)
    (hwfS : ∀ ret, (envZ m0 st.data 3344 3368 srcRs vals ret).WF := by
      intro ret; exact (lay_of hpre).wf hat.2.kept) :
    Eventually (step1 Host.exe) R st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  have hdxN : ∀ mc : MachineData, reg mc .rdx = (Sym.lit n).eval
      (envZ m0 st.data 3344 3368 srcRs vals
        (Host.addrOf (k + (o + ds.length))).toBitVec) → (reg mc .rdx).toNat = n := by
    intro mc e
    rw [e]
    show (BitVec.ofNat 64 n).toNat = n
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  refine stepC (hknown := hknown) (hwfS := hwfS) (T' := T') (vals' := vals') hp c h hat hds hne hrun hm hw0 (oc := 48)
    (by decide) hsp hmemcpy (Sk := 0) (by rw [vk_eq]; decide)
    (fun mc hmc hk hsk hso hrsp _ _ ↦ ?_) (Lc := Lc) (Oc := Oc) (fun mc m' hmc hq ↦ ?_) hLc hOc hwO
    htm hok hrspT hL hLW hvals (fun i hi ↦ nomatch tregE hrax hi)
    (fun i hi ↦ nomatch tregE hrdx hi) hsz hfl hlab (fun _ _ x r o h' ↦ by rw [hal] at h'; cases h')
    hbd fun st' hpc' hB' ⟨mc, hmc, hrsp, hq, hch⟩ hc hk ↦ ?_
  · have ca : CallAt m0 wr 48 mc := ⟨hrsp, by decide, hk, hso⟩
    obtain ⟨hDm, hDw, hDr⟩ := hD mc ca
    obtain ⟨hSm, hSw⟩ := hS mc ca
    unfold MemcpyPre
    dsimp only
    rw [hdi mc hmc, hsi mc hmc, hdxN mc (hmc.regs .rdx _ hdx)]
    exact ⟨hsk, hDm, hSm, hDw, hSw, hDS, hDr⟩
  · obtain ⟨-, -, hso, hsv⟩ := hq
    rw [hdi mc hmc, hdxN mc (hmc.regs .rdx _ hdx)] at hso
    exact chgQ hso (fun q hq ↦ .inr (hR q hq)) hsv
  · obtain ⟨-, hcp, hso, hsv⟩ := hq
    rw [hdi mc hmc, hsi mc hmc, hdxN mc (hmc.regs .rdx _ hdx)] at hcp
    rw [hdi mc hmc, hdxN mc (hmc.regs .rdx _ hdx)] at hso
    have hcall := chg_call (L := Lc) (O := Oc) c hrsp (by decide) (by rw [vk_eq]; decide)
      (chgQ (Sk := 0) hso (fun q hq ↦ .inr (hR q hq)) hsv).1
    exact cont st' mc ⟨hpc', hB'⟩ hmc (Img.of_bytesOf hcp) hch hcall hc hk

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak
