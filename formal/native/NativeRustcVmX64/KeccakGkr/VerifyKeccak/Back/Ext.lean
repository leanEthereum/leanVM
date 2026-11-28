module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.Word
public import NativeRustcVmX64.Code.Vm.BufEW36Extend.Names
public import NativeRustcVmX64.Code.Vm.VerifyKeccak.Names

/-!
# `verify_keccak`: extending the frame's output point (x86-64)

`extStep`: a block ending in `Buf<EW, 36>::extend` of the frame's buffer at `408` (RSP at the
frame's offset `48`) by `n` elements `ys` at `Sr` that fit, then `test %al; je .LVerifyKeccak_31`
(never taken): the buffer holds its elements then `ys`.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea TStateAt)
open NativeRustcVm.KeccakGkr (off)

public section

theorem okL_append (l1 l2 : List (Nat × Nat)) : okL (l1 ++ l2) = (okL l1 && okL l2) :=
  List.all_append

theorem coverL_append (l1 l2 L : List (Nat × Nat)) :
    coverL (l1 ++ l2) L = (coverL l1 L && coverL l2 L) :=
  List.all_append

theorem toUInt64_toNat_of {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simp only [Nat.toUInt64]
  exact Nat.mod_eq_of_lt h

/-- The entries of a `Buf<EW, N>`. -/
theorem bufEWOf_of {d : Mem 64} {p : BitVec 64} {N : Nat} {xs : List EW}
    (h : NativeRustcVm.BufEWAt d p N xs) (hN : N < 2 ^ 60) : NativeRustcVm.bufEWOf d p = xs := by
  obtain ⟨hl, hw, he⟩ := h
  unfold NativeRustcVm.bufEWOf
  rw [NativeRustcVm.wordOf_of_wordAt hw, toUInt64_toNat_of (by omega)]
  exact NativeRustcVm.ewsOf_of_ewsAt he

/-- A slice of elements in memory. -/
theorem slice_of {m : MachineData} {p : BitVec 64} {n : BitVec 64} {ys : List EW}
    (h : NativeRustcVm.EWsAt m.dmem p ys) (hn : n.toNat = ys.length) : slice m p n = ys.toArray := by
  unfold slice
  rw [hn, NativeRustcVm.ewsOf_of_ewsAt h]

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

/-- **An extension of the frame's buffer** and its verdict. -/
theorem extStep (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36))
    {wr : Nat → Bool} {T T' S' S2 : SState} {vals : Nat → BitVec 64}
    {ds dt : List Directive} {p0 : Nat} (hds : ds.IsInfixAt code p0) (hne : ds ≠ [])
    (hrun : exec ds T = some (S', .call NativeRustcVmX64.Vm.BufEW36Extend.entryLabel)) (hw0 : frameW S' = true)
    (hokS : okL (wsL S') = true)
    (hcov : coverL (wsL S') [(0, 152), (408, 584), (3296, 48)] = true)
    (hsp : S'.reg .rsp = some (.ptr 0 48)) (hdi : S'.reg .rdi = some (.ptr 0 408))
    (htm : tplMiss 48 [(408, 584)] T' = true) (hok : tplOk T' = true)
    (hrspT : T'.reg .rsp = some (.ptr 0 ((48 + 8 : Nat) : Int)))
    (hax : T'.reg .rax = some (.reg .rax)) (hdx' : T'.reg .rdx = some (.reg .rdx))
    {L LW : List (Nat × Sym)} (hL : rlinksOf true S' T' noRsp = some L)
    (hLW : wlinks S' T'.mem = some LW) (hvl : varLinks (L ++ LW) = true)
    (hsz : T'.regions = sizes) (hfl : T'.flags = atomFlags) (hlab : T'.labels = [])
    (hal : T'.aliases = []) (hbd : T'.bounds = [])
    (hdt : dt.IsInfixAt code (p0 + ds.length)) (hnet : dt ≠ [])
    (hrt : exec dt T' = some (S2, .cond (.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax))
      (.lit 0)) NativeRustcVmX64.Vm.VerifyKeccak.label_31))
    (hw2 : frameW S2 = true) (hok2 : okL (wsL S2) = true)
    (hcov2 : coverL (wsL S2) [(0, 152), (408, 584), (3296, 48)] = true)
    (hmiss2 : missL (wsL S2) 408 584 = true)
    {L2 LW2 : List (Nat × Sym)} (hL2 : rlinks false S2 T' = some L2)
    (hLW2 : wlinks S2 T'.mem = some LW2) (hvl2 : varLinks (L2 ++ LW2) = true)
    {st : MachineState} (hat : At m0 k p0 wr T vals st)
    {Sr : BitVec 64} {n : Nat} {xs ys : List EW}
    (hsi : ∀ mc, Match (envZ m0 st.data 3344 3368 (rsOf m0) vals
      (Host.addrOf (k + (p0 + ds.length))).toBitVec) S' mc → reg mc .rsi = Sr)
    (hdx : ∀ mc, Match (envZ m0 st.data 3344 3368 (rsOf m0) vals
      (Host.addrOf (k + (p0 + ds.length))).toBitVec) S' mc → (reg mc .rdx).toNat = n)
    (hsrc : ∀ mc, Match (envZ m0 st.data 3344 3368 (rsOf m0) vals
      (Host.addrOf (k + (p0 + ds.length))).toBitVec) S' mc →
      Chg m0 st.data.dmem mc.dmem (wsL S') [] →
      NativeRustcVm.BufEWAt mc.dmem (off (fb m0) 408) 36 xs ∧
        NativeRustcVm.EWsAt mc.dmem Sr ys ∧ ys.length = n)
    (hsr : ∀ mc, Match (envZ m0 st.data 3344 3368 (rsOf m0) vals
      (Host.addrOf (k + (p0 + ds.length))).toBitVec) S' mc → CallAt m0 wr 48 mc →
      Readable mc Sr (16 * n) ∧ Apart (off (fb m0) 408) (8 + 16 * 36) Sr (16 * n) ∧
        OffStack mc Sr (16 * n) bufEWExtendStack)
    (hfit : xs.length + n ≤ 36) {R : MachineState → Prop}
    (cont : ∀ st', At m0 k (p0 + ds.length + dt.length) wr T' vals st' →
      NativeRustcVm.BufEWAt st'.data.dmem (off (fb m0) 408) 36 (xs ++ ys) →
      Chg m0 st.data.dmem st'.data.dmem [(0, 152), (408, 584), (3296, 48)] [] →
      Kept st.data.dmem st'.data.dmem → Eventually (step1 Host.exe) R st') (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) R st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  refine stepC (hknown := hknown) (T' := T') (vals' := vals) hp c h hat hds hne hrun hat.2.mt hw0 (oc := 48)
    (by decide) hsp hext (Sk := bufEWExtendStack) (by rw [vk_eq]; decide)
    (fun mc hmc hk hsk hso hrsp hch hkk ↦ ?_) (Lc := [(408, 584)]) (Oc := [])
    (fun mc m' hmc hq ↦ ?_) (by decide) rfl rfl htm hok hrspT hL hLW
    (fun _ ↦ varLinks_eval hvl _) (fun i hi ↦ nomatch tregE hax hi)
    (fun i hi ↦ nomatch tregE hdx' hi) hsz hfl hlab
    (fun _ _ _ _ _ hx ↦ by simp [hal] at hx) hbd
    fun st1 hpc1 hB1 ⟨mc, hmc, hrsp, hq, hch⟩ hc1 hk1 ↦ ?_
  · have ca : CallAt m0 wr 48 mc := ⟨hrsp, by decide, hk, hso⟩
    have rdi : reg mc .rdi = off (fb m0) 408 := (hmc.regs .rdi _ hdi).trans (ev_frame 408)
    obtain ⟨hbuf, -, -⟩ := hsrc mc hmc hch
    obtain ⟨hrd, hap, hos⟩ := hsr mc hmc ca
    unfold BufEWExtendPre
    rw [rdi, hsi mc hmc, hdx mc hmc]
    refine ⟨hsk, ?_, ⟨mapF h ca (by decide), nwF c (by decide)⟩, hrd, hap, ?_, hos⟩
    · rw [NativeRustcVm.wordOf_of_wordAt hbuf.2.1, toUInt64_toNat_of (by have := hbuf.1; omega)]
      exact hbuf.1
    · exact (sepSF0 c ca (by rw [vk_eq]; decide) (by decide) (by decide)).symm
  · have rdi : reg mc .rdi = off (fb m0) 408 := (hmc.regs .rdi _ hdi).trans (ev_frame 408)
    obtain ⟨-, hso, hsv⟩ := hq
    exact chgQ hso (fun q h ↦ h.elim (fun h ↦ .inr (inR_frame rdi List.mem_cons_self h)) .inl)
      hsv
  have rdi : reg mc .rdi = off (fb m0) 408 := (hmc.regs .rdi _ hdi).trans (ev_frame 408)
  obtain ⟨hbuf, hys, hlen⟩ := hsrc mc hmc hch
  obtain ⟨hres, -, -⟩ := hq
  rw [rdi, hsi mc hmc, NativeRustcVm.wordOf_of_wordAt hbuf.2.1,
    toUInt64_toNat_of (by have := hbuf.1; omega), bufEWOf_of hbuf (by decide),
    slice_of hys ((hdx mc hmc).trans hlen.symm), hdx mc hmc] at hres
  simp only [hfit, ↓reduceIte] at hres
  obtain ⟨hal1, hbuf1⟩ := hres
  -- The verdict.
  refine stepJ (hknown := hknown) (T' := T') (vals' := vals) (o := p0 + ds.length) hp c h ⟨hpc1, hB1⟩ hdt hnet hrt
    nofun (hB1.mt 0) hw2 hL2 hLW2 (varLinks_eval hvl2 _) hok hsz hfl hlab
    (fun _ _ _ _ _ hx ↦ by simp [hal] at hx) hbd fun st2 hpc2 hB2 _ hc2 hk2 ↦ ?_
  simp only [PcOk] at hpc2
  rw [alCond] at hpc2
  have h1 : (reg st1.data .rax).toNat % 256 = 1 := hal1
  simp only [show (envZ m0 st1.data 3344 3368 (rsOf m0) vals 0).regs .rax = reg st1.data .rax
    from rfl, h1, show ¬(1 = 0) from by decide, decide_false, Bool.false_eq_true, ↓reduceIte]
    at hpc2
  refine cont st2 ⟨hpc2, hB2⟩
    (NativeRustcVm.Layout.BufEWAt.of_same hbuf1 (Chg.frame c hc2 hok2 rfl hmiss2 (by decide))
      (by decide)) ?_ (NativeRustcVmX64.Transcript.kept_trans hk1 hk2)
  refine Chg.mono c (hc1.trans hc2) ?_ rfl (by decide) (by decide) ?_ rfl
  · rw [okL_append, okL_append, hokS, hok2]; rfl
  · rw [coverL_append, coverL_append, hcov, hcov2]; rfl

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
