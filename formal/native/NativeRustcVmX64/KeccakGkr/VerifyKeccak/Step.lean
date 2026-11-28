module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Chg
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Run3
public import NativeRustcVmX64.KeccakGkr.Common
public import NativeRustcVmX64.Sumcheck.Common

/-!
# `verify_keccak`'s steps (x86-64)

`stepJ`: a block without a call from the template `T` (or a state `S` the machine matches) to the
template `T'`; `stepC`: a block ending in a call and the call, the callee's outputs `ChgR m0 Lc Oc`;
both give the change of memory (`Chg`). `failG`: from `NativeRustcVmX64.Vm.VerifyKeccak.label_31` (a failed check) to the
return with AL `0`, the model's `none`; `okG`: from `b71` (the last `extend` done) to the return
with AL `1`.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model
open NativeRustcVm.Transcript (DecArea TStateAt)

@[expose] public section

/-- The template's registers and words are the template `tM`'s (RSP at `56`, the pushes). -/
def toM (T : SState) : Bool :=
  match rlinks false T tM, wlinks T tM.mem with
  | some L, some LW => (L ++ LW).all fun p ↦ p.2 == .var p.1
  | _, _ => false

/-- A block's writes: in the frame below its pushes' top. -/
def frameW (S : SState) : Bool := S.mem.all fun w ↦ w.r == 0 && decide (w.off + w.n ≤ 3344)

/-- Links whose values are the variables themselves. -/
def varLinks (L : List (Nat × Sym)) : Bool := L.all fun p ↦ p.2 == .var p.1

end

/-- The values a block leaves: each link's symbolic value, evaluated (no return address). -/
macro "vtacJ" : tactic => `(tactic|
  ((simp only [List.cons_append, List.nil_append, List.forall_mem_cons]) <;> (try and_intros) <;>
    (first | rfl | exact fun _ h ↦ nomatch h)))

/-- `vtacJ` for every return address. -/
macro "vtacC" : tactic => `(tactic| (intro _ <;> vtacJ))

public section

theorem vars_vv [Labels] {m0 d : MachineData} {rs : List (BitVec 64 × Nat)} {V : Vs}
    {ret : BitVec 64} (i : Nat) : (envZ m0 d 3344 3368 rs (vv m0 V) ret).vars i = vv m0 V i := rfl

theorem vv32 [Labels] {m0 : MachineData} {V : Vs} : vv m0 V 32 = 3#64 := rfl

/-- A template's register: its value. -/
theorem tregE {T : SState} {r : Reg64} {v : Sym} (hT : T.reg r = some v) {i : Nat}
    (hi : T.reg r = some (.var i)) : v = .var i :=
  Option.some.inj (hT.symm.trans hi)

/-- `test %al, %al`: zero exactly when AL is. -/
theorem alCond [Labels] (env : Env) :
    (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)).eval env =
      decide ((env.regs .rax).toNat % 256 = 0) := by
  simp only [SBool.eval, Sym.eval]
  exact NativeRustcVmX64.Sumcheck.testAl_eq _

/-- A tag word's low half against `1`. -/
theorem tag32 [Labels] {env : Env} {o : Nat} {w : UInt64} (hw : w = 0 ∨ w = 1)
    (h : NativeRustcVm.WordAt env.mem0 (env.base 0 + BitVec.ofNat 64 o) w) :
    (SBool.not (.cmp .eq .W32 (.load 0 o 4) (.lit 1))).eval env = (w != 1) := by
  simp only [SBool.eval, Sym.eval]
  rw [NativeRustcVmX64.Transcript.load4_of_tag hw h]
  rcases hw with rfl | rfl <;> rfl

/-- A tag word's low byte against `0`. -/
theorem tag8 [Labels] {env : Env} {o : Nat} {w : UInt64} (hw : w = 0 ∨ w = 1)
    (h : NativeRustcVm.WordAt env.mem0 (env.base 0 + BitVec.ofNat 64 o) w) :
    (SBool.cmp .eq .W8 (.load 0 o 1) (.lit 0)).eval env = (w == 0) := by
  simp only [SBool.eval, Sym.eval]
  rw [NativeRustcVmX64.Transcript.load1_of_tag hw h]
  rcases hw with rfl | rfl <;> rfl

theorem al_trunc (x : BitVec 64) : (UnOp.apply .trunc .W32 x).toNat % 256 = x.toNat % 256 := by
  simp only [UnOp.apply, ext, low, BitVec.toNat_setWidth]
  show x.toNat % 2 ^ 32 % 2 ^ 64 % 256 = _
  omega

theorem varLinks_eval [Labels] {L : List (Nat × Sym)} (h : varLinks L = true) (env : Env) :
    ∀ p ∈ L, p.2.eval env = env.vars p.1 := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  rw [beq_iff_eq] at this
  rw [this]
  rfl

theorem sizes_eq [Labels] (m0 : MachineData) : 3368 :: (rsOf m0).map Prod.snd = sizes := rfl

theorem frameW_ok {S : SState} (h : frameW S = true) {F : Nat} (hF : 3344 ≤ F) {sz : List Nat}
    {wr : Nat → Bool} : S.mem.all (writeOk F sz wr) = true := by
  refine List.all_eq_true.mpr fun w hw ↦ ?_
  have := List.all_eq_true.mp h w hw
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  simp only [writeOk, this.1, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    true_and]
  exact .inl (by omega)

theorem frameW_r0 {S : SState} (h : frameW S = true) : S.mem.all (fun w ↦ w.r == 0) = true := by
  refine List.all_eq_true.mpr fun w hw ↦ ?_
  have := List.all_eq_true.mp h w hw
  simp only [Bool.and_eq_true] at this
  exact this.1

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

/-- **A block without a call.** -/
theorem stepJ (hp : Placed code k) (c : Ctx a inst m0)
    (h : LayZ m0 3344 3368 verifyKeccakStack (rsOf m0)) {wr : Nat → Bool}
    {T S T' S' : SState} {vals vals' : Nat → BitVec 64} {o : Nat} {st : MachineState}
    (hat : At m0 k o wr T vals st) {ds : List Directive} (hds : ds.IsInfixAt code o) (hne : ds ≠ [])
    {x : Exit} (hrun : exec ds S = some (S', x)) (hx : ∀ l, x ≠ .call l)
    (hm : Match (envZ m0 st.data 3344 3368 (rsOf m0) vals 0) S st.data)
    (hw0 : frameW S' = true)
    {L LW : List (Nat × Sym)} (hL : rlinks false S' T' = some L)
    (hLW : wlinks S' T'.mem = some LW)
    (hvals : ∀ p ∈ L ++ LW, p.2.eval (envZ m0 st.data 3344 3368 (rsOf m0) vals 0) = vals' p.1)
    (hok : tplOk T' = true) (hsz : T'.regions = sizes) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hal : ∀ m' ret, AliasesOk T' (envZ m0 m' 3344 3368 (rsOf m0) vals' ret))
    (hbd : T'.bounds = []) {R : MachineState → Prop}
    (cont : ∀ st', PcOk (envZ m0 st.data 3344 3368 (rsOf m0) vals 0) x
        (Host.addrOf (k + (o + ds.length))) st' →
      BndZ m0 3344 3368 verifyKeccakStack (rsOf m0) wr T' vals' st'.data →
      Match (envZ m0 st.data 3344 3368 (rsOf m0) vals 0) S' st'.data →
      Chg m0 st.data.dmem st'.data.dmem (wsL S') [] → Kept st.data.dmem st'.data.dmem →
      Eventually (step1 Host.exe) R st') (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) R st := by
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hB⟩ := hat
  simp only at hpc hB hm hvals cont
  subst hpc
  rw [← sizes_eq m0] at hsz
  have hwr := frameW_ok hw0 (F := 3344) (sz := 3368 :: (rsOf m0).map Prod.snd) (wr := wr) le_rfl
  have h0 := frameW_r0 hw0
  refine jumpZ (hknown := hknown) h hB (hds.trans hp.1 hne) hrun hm hx hwr hL hLW hvals hok hsz hfl hlab hal
    (fun _ _ _ _ hx ↦ by rw [hbd] at hx; cases hx) fun st' hpc' hB' hm' ↦ ?_
  exact cont st' (by rw [← Nat.add_assoc]; exact hpc') hB' hm' (chg_block c hm' (h.wf hB.kept) hwr h0)
    (hm'.kept (h.wf hB.kept))

/-- **A block ending in a call, and the call.** -/
theorem stepC (hp : Placed code k) (c : Ctx a inst m0)
    (h : LayZ m0 3344 3368 verifyKeccakStack (rsOf m0)) {wr : Nat → Bool}
    {T S T' S' : SState} {vals vals' : Nat → BitVec 64} {o : Nat} {st : MachineState}
    {srcRs : List (BitVec 64 × Nat)}
    (hat : At m0 k o wr T vals st) {ds : List Directive} (hds : ds.IsInfixAt code o) (hne : ds ≠ [])
    {l : Label} (hrun : exec ds S = some (S', .call l))
    (hm : ∀ ret, Match (envZ m0 st.data 3344 3368 srcRs vals ret) S st.data)
    (hw0 : frameW S' = true)
    {oc : Nat} (hoc : oc + 8 ≤ 3344) (hsp : S'.reg .rsp = some (.ptr 0 (oc : Int)))
    {P : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    (hspec : Spec (Labels.label l) P Q) {Sk : Nat} (hS : 3344 - oc + Sk ≤ verifyKeccakStack)
    (hP : ∀ mc, Match (envZ m0 st.data 3344 3368 srcRs vals
        (Host.addrOf (k + (o + ds.length))).toBitVec) S' mc →
      Kept m0.dmem mc.dmem → StackOk mc Sk →
      SameOutside m0.dmem mc.dmem
        (fun q ↦ InRange (stackBelow m0 verifyKeccakStack) verifyKeccakStack q ∨
          outsOf (rsOf m0) wr q) →
      rspOf mc = stackBelow m0 (3344 - oc) →
      Chg m0 st.data.dmem mc.dmem (wsL S') [] → Kept st.data.dmem mc.dmem → P mc)
    {Lc : List (Nat × Nat)} {Oc : List (Nat × Nat × Nat)}
    (hQ : ∀ mc m', Match (envZ m0 st.data 3344 3368 srcRs vals
        (Host.addrOf (k + (o + ds.length))).toBitVec) S' mc → Q mc m' →
      SameOutside mc.dmem m'.dmem (fun q ↦ InRange (stackBelow mc Sk) Sk q ∨ ChgR m0 Lc Oc q) ∧
        Saved mc m')
    (hLc : okL Lc = true) (hOc : okO Oc = true) (hwO : wrO wr Oc = true)
    (htm : tplMiss oc Lc T' = true)
    (hok : tplOk T' = true) (hrspT : T'.reg .rsp = some (.ptr 0 ((oc + 8 : Nat) : Int)))
    {L LW : List (Nat × Sym)} (hL : rlinksOf true S' T' noRsp = some L)
    (hLW : wlinks S' T'.mem = some LW)
    (hvals : ∀ ret, ∀ p ∈ L ++ LW,
      p.2.eval (envZ m0 st.data 3344 3368 srcRs vals ret) = vals' p.1)
    (hrax : ∀ i, T'.reg .rax = some (.var i) → ∀ mc m' : MachineData,
      Match (envZ m0 st.data 3344 3368 srcRs vals
        (Host.addrOf (k + (o + ds.length))).toBitVec) S' mc → Q mc m' →
      reg m' .rax = vals' i)
    (hrdx : ∀ i, T'.reg .rdx = some (.var i) → ∀ mc m' : MachineData,
      Match (envZ m0 st.data 3344 3368 srcRs vals
        (Host.addrOf (k + (o + ds.length))).toBitVec) S' mc → Q mc m' →
      reg m' .rdx = vals' i)
    (hsz : T'.regions = sizes) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hal : ∀ m' ret, AliasesOk T' (envZ m0 m' 3344 3368 (rsOf m0) vals' ret))
    (hbd : T'.bounds = []) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = Host.addrOf (k + (o + ds.length)) →
      BndZ m0 3344 3368 verifyKeccakStack (rsOf m0) wr T' vals' st'.data →
      (∃ mc, Match (envZ m0 st.data 3344 3368 srcRs vals
          (Host.addrOf (k + (o + ds.length))).toBitVec) S' mc ∧
        rspOf mc = stackBelow m0 (3344 - oc) ∧ Q mc st'.data ∧
        Chg m0 st.data.dmem mc.dmem (wsL S') []) →
      Chg m0 st.data.dmem st'.data.dmem (wsL S' ++ (0, oc) :: Lc) Oc →
      Kept st.data.dmem st'.data.dmem → Eventually (step1 Host.exe) R st') (hknown : T'.known = [] := by rfl)  
    (hwfS : ∀ ret, (envZ m0 st.data 3344 3368 srcRs vals ret).WF := by
      intro ret; exact h.wf hat.2.kept) :
    Eventually (step1 Host.exe) R st := by
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hB⟩ := hat
  simp only at hpc hB hm hvals cont hP hrax hrdx hQ
  subst hpc
  rw [← sizes_eq m0] at hsz
  have hwr := frameW_ok hw0 (F := 3344) (sz := 3368 :: (rsOf m0).map Prod.snd) (wr := wr) le_rfl
  have h0 := frameW_r0 hw0
  have hwf := hwfS (Host.addrOf (k + o + ds.length)).toBitVec
  have hsrcWritten : ∀ {q}, Written (envZ m0 d 3344 3368 srcRs vals
      (Host.addrOf (k + o + ds.length)).toBitVec) S' q →
      InRange (stackBelow m0 verifyKeccakStack) verifyKeccakStack q ∨ outsOf (rsOf m0) wr q := by
    intro q ⟨w, hw, b, sz, hb, h1, h2⟩
    have hr : w.r = 0 := by simpa using List.all_eq_true.mp h0 w hw
    apply h.written (m := d) (vals := vals)
      (ret := (Host.addrOf (k + o + ds.length)).toBitVec) hwr
    refine ⟨w, hw, b, sz, ?_, h1, h2⟩
    rw [hr] at hb ⊢
    exact hb
  have hds' : ds.IsInfixAt Host.prog (k + o) := hds.trans hp.1 hne
  have hra : k + (o + ds.length) = k + o + ds.length := by omega
  rw [hra] at hP hrax hrdx cont hQ
  refine callZ (hknown := hknown) (hwfS := hwf) (hwrites := hsrcWritten) (W := fun _ ↦ ChgR m0 Lc Oc) h hB hds' hrun (hm _) hoc hsp hspec hS
    (fun mc hmc hk hsk hso hrsp ↦ hP mc hmc hk hsk hso hrsp (chg_block c hmc hwf hwr h0)
      (hmc.kept hwf))
    (fun mc m' hmc hq ↦ hQ mc m' hmc hq) (fun _ _ q hq ↦ ChgR.wo c hLc hOc hwO hq) hok hrspT hL hLW
    (hvals _) hrax hrdx (fun _ _ j v t _ hf ↦ ChgR.wt c hLc hOc htm hf) hsz hfl hlab hal
    (fun _ _ _ _ hx ↦ by rw [hbd] at hx; cases hx) fun st' hpc' hB' ⟨mc, hmc, hrsp, hq, hso⟩ ↦ ?_
  have hc1 : Chg m0 d.dmem mc.dmem (wsL S') [] := chg_block c hmc hwf hwr h0
  have hc2 := chg_call c hrsp (by omega) hS (hQ mc st'.data hmc hq).1
  refine cont st' hpc' hB' ⟨mc, hmc, hrsp, hq, hc1⟩ ?_
    (NativeRustcVmX64.Transcript.kept_trans (hmc.kept hwf) (hQ mc st'.data hmc hq).2.2)
  have := hc1.trans hc2
  simpa using this

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak
