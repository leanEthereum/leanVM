module

public import NativeRustcVmX64.Ring.Target.Steps
public import NativeRustcVmX64.Ring.Target.Values
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EWSqIter.Names
public import NativeRustcVmX64.Code.Vm.PolyEval.Names

/-!
# `ring_target`: the turns' steps (x86-64)

In the turns' layout (`rsC`: `f` region `1`, through R12's variable `10`), with the images' copy
as the invariant (`CAt`): a block and its call of `EW::sq_iter` (`sqS`), `EW::mul` (`mulS`),
`poly_eval` over the copy (`polyS`); `f`'s words (`fl0`, `fl1`), the aliases (`keyOk`, `noKeys`),
the links' values (`vtac`).
-/

namespace NativeRustcVmX64.Ring.Target

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingTarget

@[expose] public section

/-- The turns' layout. -/
abbrev rsC (m0 : MachineData) : List (BitVec 64 × Nat) := [(fA m0, 128)]

end

public section

variable {m0 : MachineData} {E : Nat → EW}

/-- `f`'s words are the entry's in every state between blocks. -/
theorem fword [Labels] (hpre : RingTargetPre m0) {T : SState} {vals : Nat → BitVec 64}
    {m : MachineData} (hB : Bnd m0 2352 NT (rsC m0) noWr T vals m) {o : Nat} (ho : o + 8 ≤ 128) :
    NativeRustcVm.wordOf m.dmem (fA m0 + BitVec.ofNat 64 o) =
      NativeRustcVm.wordOf m0.dmem (fA m0 + BitVec.ofNat 64 o) := by
  refine NativeRustcVm.wordOf_congr fun i hi ↦ ?_
  rw [NativeRustcVm.addr_add]
  refine hB.same _ fun hin ↦ hin.elim (fun h1 ↦ ?_) fun ⟨j, e, he, _⟩ ↦ by cases he
  exact NativeRustcVm.Apart.not_inRange_add hpre.2.2.1.2 hpre.2.2.1.1.2
    (noWrap_stackBelow hpre.1) (show o + i < 16 * 8 by omega) (inRange_le h1 (Nat.le_add_right _ _))

theorem fl0 [Labels] (hpre : RingTargetPre m0) (hG : Good m0 E) {T : SState}
    {vals : Nat → BitVec 64} {m : MachineData} (hB : Bnd m0 2352 NT (rsC m0) noWr T vals m)
    {p o : Nat} (hp : p < 8) (ho : o = 16 * p) {ret : BitVec 64} :
    (envS m0 m 2352 (rsC m0) vals ret).load 1 o 8 = c0 (E p) := by
  rw [load_eq_wordOf, show (envS m0 m 2352 (rsC m0) vals ret).base 1 = fA m0 from rfl,
    Env.ofMachine_mem0, fword hpre hB (by omega), hG.f p hp, ho]
  rfl

theorem fl1 [Labels] (hpre : RingTargetPre m0) (hG : Good m0 E) {T : SState}
    {vals : Nat → BitVec 64} {m : MachineData} (hB : Bnd m0 2352 NT (rsC m0) noWr T vals m)
    {p o : Nat} (hp : p < 8) (ho : o = 16 * p + 8) {ret : BitVec 64} :
    (envS m0 m 2352 (rsC m0) vals ret).load 1 o 8 = c1 (E p) := by
  rw [load_eq_wordOf, show (envS m0 m 2352 (rsC m0) vals ret).base 1 = fA m0 from rfl,
    Env.ofMachine_mem0, fword hpre hB (by omega), hG.f p hp, ho, ← NativeRustcVm.addr_add]
  rfl

theorem keyOk [Labels] {T : SState} {vals : Nat → BitVec 64} (hT : T.aliases = fKey)
    (h10 : vals 10 = fA m0) {m : MachineData} {ret : BitVec 64} :
    AliasesOk T (envS m0 m 2352 (rsC m0) vals ret) := by
  intro x r o hx
  rw [hT] at hx
  simp only [fKey, List.lookup] at hx
  split at hx
  · rename_i heq
    rw [beq_iff_eq] at heq
    subst heq
    cases hx
    show vals 10 = fA m0 + BitVec.ofInt 64 0
    rw [h10]
    simp
  · cases hx

theorem noKeys [Labels] {T : SState} (hT : T.aliases = []) {env : Env} : AliasesOk T env := by
  intro x r o hx
  rw [hT] at hx
  cases hx

end

/-- The links' values: what `rfl` closes, then `f`'s words. -/
syntax "vtac " term:max term:max term:max : tactic

macro_rules
  | `(tactic| vtac $hpre $hG $hB) => `(tactic|
    ((simp only [List.cons_append, List.nil_append, List.forall_mem_cons, Sym.eval,
      NativeRustcVmX64.Field.Lin.xor_apply]) <;> and_intros <;>
      (first
        | rfl
        | exact fun _ h ↦ nomatch h
        | exact fl0 $hpre $hG $hB (by decide) (by decide)
        | exact fl1 $hpre $hG $hB (by decide) (by decide))))

public section

variable {m0 : MachineData} {E : Nat → EW} [Host] {k : Nat}

omit [Host] in
theorem geoT [Labels] (hpre : RingTargetPre m0) : NativeRustcVmX64.Field.Geo m0 2352 NT :=
  ⟨hpre.1, by decide, by decide⟩

/-- **A block and its call of `EW::sq_iter`.** -/
theorem sqS (hp : Placed code k) (hpre : RingTargetPre m0)
    (hsq : Spec (Labels.label NativeRustcVmX64.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost) (_hG : Good m0 E)
    {ds : List Directive} {off off' : Nat} (hds : ds.IsInfixAt code off) (hne : ds ≠ [])
    (hoff : off + ds.length = off') {T T' S' : SState} {vals vals' : Nat → BitVec 64}
    (hrun : exec ds T = some (S', .call NativeRustcVmX64.Vm.EWSqIter.entryLabel))
    (hwr : S'.mem.all (writeOk 2352 ((2352 + 8) :: (rsC m0).map Prod.snd) noWr) = true)
    (hsp : S'.reg .rsp = some (.ptr 0 0)) (hmiss : missOk 1280 2304 S' = true)
    {L LW : List (Nat × Sym)} (hL : rlinks true S' T' = some L) (hLW : wlinks S' T'.mem = some LW)
    (hvals : ∀ m, Bnd m0 2352 NT (rsC m0) noWr T vals m → ∀ ret, ∀ p ∈ L ++ LW,
      p.2.eval (envS m0 m 2352 (rsC m0) vals ret) = vals' p.1)
    (hres : ∀ {m : MachineData} {ret : BitVec 64} (mc m' : MachineData),
      Match (envS m0 m 2352 (rsC m0) vals ret) S' mc → EWSqIterPost mc m' →
      reg m' .rax = vals' 6 ∧ reg m' .rdx = vals' 7)
    (hrax : T'.reg .rax = some (.var 6)) (hrdx : T'.reg .rdx = some (.var 7))
    (hsz : T'.regions = (2352 + 8) :: (rsC m0).map Prod.snd) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hal : ∀ m' ret, AliasesOk T' (envS m0 m' 2352 (rsC m0) vals' ret))
    (hbd : T'.bounds = []) {st : MachineState}
    (h : At m0 k off (rsC m0) T vals (CAt m0) st) (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) (At m0 k off' (rsC m0) T' vals' (CAt m0)) st :=
  cstep (hknown := hknown) hp (layC hpre) hds hne hoff hrun hwr hsp hsq (S := ewSqIterStack) (by decide)
    (fun _ _ _ _ _ _ hs ↦ hs) (fun _ _ hq ↦ ⟨hq.2.2.1, hq.2.2.2⟩) hL hLW hvals hrax hrdx
    (fun _ _ _ mc m' hm hq ↦ hres mc m' hm hq)
    (fun _ _ _ hB hI hm hsp hq ↦ cAt_call (geoT hpre) ((layC hpre).wf hB.kept) hmiss hm hI hsp
      (by decide) hq.2.2.1) hsz hfl hlab hal hbd h

/-- **A block and its call of `EW::mul`.** -/
theorem mulS (hp : Placed code k) (hpre : RingTargetPre m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (_hG : Good m0 E)
    {ds : List Directive} {off off' : Nat} (hds : ds.IsInfixAt code off) (hne : ds ≠ [])
    (hoff : off + ds.length = off') {T T' S' : SState} {vals vals' : Nat → BitVec 64}
    (hrun : exec ds T = some (S', .call NativeRustcVmX64.Vm.EWMul.entryLabel))
    (hwr : S'.mem.all (writeOk 2352 ((2352 + 8) :: (rsC m0).map Prod.snd) noWr) = true)
    (hsp : S'.reg .rsp = some (.ptr 0 0)) (hmiss : missOk 1280 2304 S' = true)
    {L LW : List (Nat × Sym)} (hL : rlinks true S' T' = some L) (hLW : wlinks S' T'.mem = some LW)
    (hvals : ∀ m, Bnd m0 2352 NT (rsC m0) noWr T vals m → ∀ ret, ∀ p ∈ L ++ LW,
      p.2.eval (envS m0 m 2352 (rsC m0) vals ret) = vals' p.1)
    (hres : ∀ {m : MachineData} {ret : BitVec 64} (mc m' : MachineData),
      Match (envS m0 m 2352 (rsC m0) vals ret) S' mc → EWMulPost mc m' →
      reg m' .rax = vals' 6 ∧ reg m' .rdx = vals' 7)
    (hrax : T'.reg .rax = some (.var 6)) (hrdx : T'.reg .rdx = some (.var 7))
    (hsz : T'.regions = (2352 + 8) :: (rsC m0).map Prod.snd) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hal : ∀ m' ret, AliasesOk T' (envS m0 m' 2352 (rsC m0) vals' ret))
    (hbd : T'.bounds = []) {st : MachineState}
    (h : At m0 k off (rsC m0) T vals (CAt m0) st) (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) (At m0 k off' (rsC m0) T' vals' (CAt m0)) st :=
  cstep (hknown := hknown) hp (layC hpre) hds hne hoff hrun hwr hsp hmul (S := ewMulStack) (by decide)
    (fun _ _ _ _ _ _ hs ↦ hs) (fun _ _ hq ↦ ⟨hq.2.2.1, hq.2.2.2⟩) hL hLW hvals hrax hrdx
    (fun _ _ _ mc m' hm hq ↦ hres mc m' hm hq)
    (fun _ _ _ hB hI hm hsp hq ↦ cAt_call (geoT hpre) ((layC hpre).wf hB.kept) hmiss hm hI hsp
      (by decide) hq.2.2.1) hsz hfl hlab hal hbd h

omit [Host] in
/-- `Changes` with no output: the stack only. -/
theorem changes0 {m m' : MachineData} {S : Nat} (h : Changes m m' S 0 0) :
    SameOutside m.dmem m'.dmem (InRange (stackBelow m S) S) :=
  fun q hq ↦ h q fun h' ↦ h'.elim (fun h0 ↦ by unfold InRange at h0; omega) hq

omit [Host] in
/-- The copy at the call: the elements `poly_eval` reads. -/
theorem copy_at [Labels] (hpre : RingTargetPre m0) {T S' : SState} {vals : Nat → BitVec 64}
    {m mc : MachineData} {ret : BitVec 64} (hB : Bnd m0 2352 NT (rsC m0) noWr T vals m)
    (hI : CAt m0 m) (hmiss : missOk 1280 2304 S' = true)
    (hm : Match (envS m0 m 2352 (rsC m0) vals ret) S' mc) : CAt m0 mc := by
  refine NativeRustcVm.BytesAt.of_sameOutside hI (R := Written (envS m0 m 2352 (rsC m0) vals ret) S')
    (fun q hq ↦ hm.get?_mem0 ((layC hpre).wf hB.kept) hq) fun i hi hR ↦ ?_
  rw [NativeRustcVm.length_ewsBytes, Array.length_toList, imgs_size] at hi
  rw [NativeRustcVm.addr_add] at hR
  exact not_written_mid (geoT hpre) hmiss (j := 1280 + i) (by omega) (by omega) (by omega) hR

/-- **A block and its call of `poly_eval`** over the images' copy. -/
theorem polyS (hp : Placed code k) (hpre : RingTargetPre m0)
    (hpoly : Spec (Labels.label NativeRustcVmX64.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost) (_hG : Good m0 E)
    {ds : List Directive} {off off' : Nat} (hds : ds.IsInfixAt code off) (hne : ds ≠ [])
    (hoff : off + ds.length = off') {T T' S' : SState} {vals vals' : Nat → BitVec 64}
    (hrun : exec ds T = some (S', .call NativeRustcVmX64.Vm.PolyEval.entryLabel))
    (hwr : S'.mem.all (writeOk 2352 ((2352 + 8) :: (rsC m0).map Prod.snd) noWr) = true)
    (hsp : S'.reg .rsp = some (.ptr 0 0)) (hmiss : missOk 1280 2304 S' = true)
    (hrdi : S'.reg .rdi = some (.ptr 0 1280)) (hrsi : S'.reg .rsi = some (.lit 64))
    {L LW : List (Nat × Sym)} (hL : rlinks true S' T' = some L) (hLW : wlinks S' T'.mem = some LW)
    (hvals : ∀ m, Bnd m0 2352 NT (rsC m0) noWr T vals m → ∀ ret, ∀ p ∈ L ++ LW,
      p.2.eval (envS m0 m 2352 (rsC m0) vals ret) = vals' p.1)
    (hres : ∀ {m : MachineData} {ret : BitVec 64} (mc m' : MachineData),
      Match (envS m0 m 2352 (rsC m0) vals ret) S' mc →
      slice mc (reg mc .rdi) (reg mc .rsi) = imgs m0 → PolyEvalPost mc m' →
      reg m' .rax = vals' 6 ∧ reg m' .rdx = vals' 7)
    (hrax : T'.reg .rax = some (.var 6)) (hrdx : T'.reg .rdx = some (.var 7))
    (hsz : T'.regions = (2352 + 8) :: (rsC m0).map Prod.snd) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hal : ∀ m' ret, AliasesOk T' (envS m0 m' 2352 (rsC m0) vals' ret))
    (hbd : T'.bounds = []) {st : MachineState}
    (h : At m0 k off (rsC m0) T vals (CAt m0) st) (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) (At m0 k off' (rsC m0) T' vals' (CAt m0)) st := by
  have g := geoT hpre
  have hb := g.base
  have hs := g.sp
  have ht := g.top
  have e1 : ∀ {m mc : MachineData} {ret : BitVec 64},
      Match (envS m0 m 2352 (rsC m0) vals ret) S' mc →
      reg mc .rdi = stackBelow m0 2352 + BitVec.ofNat 64 1280 ∧ reg mc .rsi = BitVec.ofNat 64 64 :=
    fun hm ↦ ⟨(hm.regs .rdi _ hrdi).trans (by
      show stackBelow m0 2352 + BitVec.ofInt 64 1280 = _
      rfl), hm.regs .rsi _ hrsi⟩
  have hsl : ∀ {m mc : MachineData} {ret : BitVec 64},
      Bnd m0 2352 NT (rsC m0) noWr T vals m → CAt m0 m →
      Match (envS m0 m 2352 (rsC m0) vals ret) S' mc →
      slice mc (reg mc .rdi) (reg mc .rsi) = imgs m0 := by
    intro m mc ret hB hI hm
    have hC := copy_at hpre hB hI hmiss hm
    have h64 : (reg mc .rsi).toNat = (imgs m0).toList.length := by
      rw [(e1 hm).2, Array.length_toList, imgs_size]; rfl
    unfold slice
    rw [h64, (e1 hm).1, NativeRustcVm.ewsOf_of_ewsAt hC]
  refine cstep (hknown := hknown) hp (layC hpre) hds hne hoff hrun hwr hsp hpoly (S := polyEvalStack) (by decide)
    (fun m mc hB _ hm hk hso ↦ ?_) (fun _ _ hq ↦ ⟨changes0 hq.2.1, hq.2.2⟩) hL hLW hvals hrax hrdx
    (fun _ hB hI mc m' hm hq ↦ hres mc m' hm (hsl hB hI hm) hq)
    (fun _ _ _ hB hI hm hsp hq ↦ cAt_call g ((layC hpre).wf hB.kept) hmiss hm hI hsp
      (by decide) (changes0 hq.2.1)) hsz hfl hlab hal hbd h
  refine ⟨hso, ?_, ?_⟩
  · rw [(e1 hm).2]; decide
  · have hsp' : rspOf mc = stackBelow m0 2352 := by
      show mc.regs.get64 .rsp = _
      rw [hm.regs .rsp _ hsp]
      show stackBelow m0 2352 + BitVec.ofInt 64 0 = _
      simp
    have hq : (stackBelow m0 2352 + BitVec.ofNat 64 1280).toNat = (rspOf m0).toNat - 2352 + 1280 :=
      g.addr (by omega)
    have h64 : (reg mc .rsi).toNat = 64 := by rw [(e1 hm).2]; rfl
    have hs' : 2576 ≤ (rspOf m0).toNat := hs
    unfold SliceOk
    rw [(e1 hm).1, h64]
    refine ⟨⟨fun i hi ↦ ?_, by unfold NoWrap; rw [hq]; rw [nt_eq] at hs; omega⟩, ?_⟩
    · rw [NativeRustcVm.addr_add]
      exact hk _ (g.mapped (by rw [g.addr (by omega), nt_eq]; omega) (by rw [g.addr (by omega)]; omega))
    · unfold OffStack Apart
      rw [NativeRustcVmX64.Transcript.stackBelow_callee hsp' (by simp only [polyEvalStack, ewMulStack]; omega),
        stackBelow_toNat (by simp only [polyEvalStack, ewMulStack]; omega), hq]
      simp only [polyEvalStack, ewMulStack]
      omega

end

end NativeRustcVmX64.Ring.Target
