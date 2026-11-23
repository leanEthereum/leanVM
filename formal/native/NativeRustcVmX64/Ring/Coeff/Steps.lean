module

public import NativeRustcVmX64.Ring.Coeff.Lay
public import NativeRustcVmX64.Field.LinSound
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EWSqIter.Names

/-!
# `ring_coefficients`: a turn's blocks (x86-64)

Turn `p` from its head (`b1`, its start state `m`, the template `tH` with `hv p`) through the
row's 8 products (`b1` to `b9`, `EW::mul`), the Frobenius images of `G` (`b9` to `b16`,
`EW::sq_iter`) and the loop's test (`b17`): `turn_body` ends at `b17`'s exit in `tRn` with
`bv p 17`, in turn `p`'s layout (`TAt`).
-/

namespace NativeRustcVmX64.Ring.Coeff

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingCoefficients

/-- The values a block leaves: each link's symbolic value, evaluated; what `rfl` does not close is
left. -/
macro "vtacR" : tactic => `(tactic|
  (intro ret
   simp only [List.cons_append, List.nil_append, List.forall_mem_cons, Sym.eval,
    NativeRustcVmX64.Field.Lin.xor_apply]
   and_intros
   all_goals (first | rfl | exact fun _ h ↦ nomatch h | skip)))

@[expose] public section

variable [Host]

/-- Turn `p` (from the state `m`) before the block at `off`: the template `T` with `vals`. -/
def TAt (m0 m : MachineData) (p k off : Nat) (T : SState) (vals : Nat → BitVec 64)
    (st : MachineState) : Prop :=
  st.pc = Host.addrOf (k + off) ∧ Bnd (own m0 m) 176 NC (rsP m0 p) wrRow T vals st.data

end

public section

variable [Host] {k : Nat} {m0 m : MachineData} {p : Nat}

omit [Host] in
/-- The aliases of the loop's templates hold in turn `p`, while RBP is `16 p`. -/
theorem keys_ok [Labels] {vals : Nat → BitVec 64} (h13 : vals 13 = oA m0)
    (h8 : vals 8 = BitVec.ofNat 64 (16 * p)) (h28 : vals 28 = fA m0) {T : SState}
    (hT : T.aliases = keys) (m' : MachineData) (ret : BitVec 64) :
    AliasesOk T (envS (own m0 m) m' 176 (rsP m0 p) vals ret) := by
  intro x r o hx
  rw [hT] at hx
  simp only [keys, List.lookup, rowKey, fKey] at hx
  split at hx
  · rename_i heq
    rw [beq_iff_eq] at heq
    subst heq
    cases hx
    rw [eval_mkAdd64, eval_mkBin]
    simp only [Sym.eval, NativeRustcVmX64.Field.Lin.mul_apply]
    show vals 13 + vals 8 * BitVec.ofNat 64 8 =
      oA m0 + BitVec.ofNat 64 (128 * p) + BitVec.ofInt 64 0
    rw [h13, h8, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, ← BitVec.ofNat_mul]
    congr 2
    omega
  · split at hx
    · rename_i heq
      rw [beq_iff_eq] at heq
      subst heq
      cases hx
      rw [eval_mkAdd64, eval_mkBin]
      simp only [Sym.eval, NativeRustcVmX64.Field.Lin.mul_apply]
      show vals 28 + vals 8 * BitVec.ofNat 64 1 =
        fA m0 + BitVec.ofNat 64 (16 * p) + BitVec.ofInt 64 0
      rw [h28, h8, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
        show BitVec.ofNat 64 1 = 1#64 from rfl, BitVec.mul_one]
    · cases hx

omit [Host] in
/-- A state of turn `p`'s frame is one of `Mem`. -/
theorem Mem.of_bnd [Labels] (h : P m0) (hM : Mem m0 m) (hpl : p < 8) {T : SState} {vals : Nat → BitVec 64}
    {d : MachineData} (hB : Bnd (own m0 m) 176 NC (rsP m0 p) wrRow T vals d) : Mem m0 d := by
  refine ⟨fun q hq ↦ (hB.same q fun hin ↦ hq ?_).trans (hM.same q hq),
    fun q hq ↦ hB.kept q (hM.kept q hq)⟩
  rcases hin with hin | ⟨i, e, hwr, he, hin⟩
  · exact .inl hin
  · right
    cases i with
    | zero =>
      simp only [rsP, List.getElem?_cons_zero, Option.some.injEq] at he
      subst he
      have how := h.ow
      unfold NoWrap at how
      have hr : (oA m0 + BitVec.ofNat 64 (128 * p)).toNat = (oA m0).toNat + 128 * p :=
        toNat_add_ofNat _ _ (by omega)
      simp only at hin
      rw [Sym.inRange_iff (by rw [hr]; omega), hr] at hin
      rw [Sym.inRange_iff (by omega)]
      omega
    | succ i => simp [wrRow] at hwr

omit [Host] in
/-- `f`'s words through region 2 in turn `p`. -/
theorem fload [Labels] (h : P m0) {m' : MachineData} (hM : Mem m0 m') (hp : p < 8)
    {vals : Nat → BitVec 64} (ret : BitVec 64) :
    (Sym.load 2 0 8).eval (envS (own m0 m) m' 176 (rsP m0 p) vals ret) = c0 (fE m0 p) ∧
      (Sym.load 2 8 8).eval (envS (own m0 m) m' 176 (rsP m0 p) vals ret) = c1 (fE m0 p) := by
  simp only [Sym.eval]
  rw [load_eq_wordOf, load_eq_wordOf, fE_c0, fE_c1]
  constructor
  · rw [show (envS (own m0 m) m' 176 (rsP m0 p) vals ret).base 2 =
      fA m0 + BitVec.ofNat 64 (16 * p) from rfl, addr_add, Env.ofMachine_mem0]
    exact congrArg UInt64.toBitVec (fword h hM (by omega))
  · rw [show (envS (own m0 m) m' 176 (rsP m0 p) vals ret).base 2 =
      fA m0 + BitVec.ofNat 64 (16 * p) from rfl, addr_add, Env.ofMachine_mem0]
    exact congrArg UInt64.toBitVec (fword h hM (by omega))

/-- **A block and its call of `EW::mul`.** -/
theorem mstep (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (h : P m0) (hM : Mem m0 m) (hpl : p < 8) {ds : List Directive} {off off' : Nat}
    (hds : ds.IsInfixAt code off) (hne : ds ≠ []) (hoff : off + ds.length = off')
    {T T' S' : SState} {vals vals' : Nat → BitVec 64}
    (hrun : exec ds T = some (S', .call NativeRustcVmX64.Vm.EWMul.entryLabel))
    (hwr : S'.mem.all (writeOk 176 [184, 128, 16] wrRow) = true)
    (hsp : S'.reg .rsp = some (.ptr 0 0))
    {L LW : List (Nat × Sym)} (hL : rlinks true S' T' = some L) (hLW : wlinks S' T'.mem = some LW)
    (hvals : ∀ m', Mem m0 m' → ∀ ret, ∀ q ∈ L ++ LW,
      q.2.eval (envS (own m0 m) m' 176 (rsP m0 p) vals ret) = vals' q.1)
    (hres : ∀ m', Mem m0 m' → ∀ ret mc,
      (∀ r v, S'.reg r = some v → reg mc r = v.eval (envS (own m0 m) m' 176 (rsP m0 p) vals ret)) →
      mulRes mc = (vals' 6, vals' 7))
    (hrax : T'.reg .rax = some (.var 6)) (hrdx : T'.reg .rdx = some (.var 7))
    (hsz : T'.regions = [184, 128, 16]) (hfl : T'.flags = atomFlags) (hlab : T'.labels = [])
    (hal : ∀ m' ret, AliasesOk T' (envS (own m0 m) m' 176 (rsP m0 p) vals' ret))
    (hbd : T'.bounds = []) {st : MachineState}
    (hA : TAt m0 m p k off T vals st) (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) (TAt m0 m p k off' T' vals') st := by
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hB⟩ := hA
  simp only at hpc hB
  subst hpc
  refine mulStep (hknown := hknown) (lay h hM hpl) hmul (by decide) hB (hds.trans hp.1 hne) hrun hwr hsp hL hLW
    (hvals d (Mem.of_bnd h hM hpl hB)) (fun i hi mc hR ↦ ?_) (fun i hi mc hR ↦ ?_) hsz hfl hlab hal
    hbd
    fun st hpc' hB' ↦ .done _ ⟨by rw [hpc', Nat.add_assoc, hoff], hB'⟩
  · rw [hrax] at hi
    cases hi
    rw [hres d (Mem.of_bnd h hM hpl hB) _ mc hR]
  · rw [hrdx] at hi
    cases hi
    rw [hres d (Mem.of_bnd h hM hpl hB) _ mc hR]

/-- **A block and its call of `EW::sq_iter`.** -/
theorem sstep (hp : Placed code k)
    (hsq : Spec (Labels.label NativeRustcVmX64.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost)
    (h : P m0) (hM : Mem m0 m) (hpl : p < 8) {ds : List Directive} {off off' : Nat}
    (hds : ds.IsInfixAt code off) (hne : ds ≠ []) (hoff : off + ds.length = off')
    {T T' S' : SState} {vals vals' : Nat → BitVec 64}
    (hrun : exec ds T = some (S', .call NativeRustcVmX64.Vm.EWSqIter.entryLabel))
    (hwr : S'.mem.all (writeOk 176 [184, 128, 16] wrRow) = true)
    (hsp : S'.reg .rsp = some (.ptr 0 0))
    {L LW : List (Nat × Sym)} (hL : rlinks true S' T' = some L) (hLW : wlinks S' T'.mem = some LW)
    (hvals : ∀ m', Mem m0 m' → ∀ ret, ∀ q ∈ L ++ LW,
      q.2.eval (envS (own m0 m) m' 176 (rsP m0 p) vals ret) = vals' q.1)
    (hres : ∀ m', Mem m0 m' → ∀ ret mc,
      (∀ r v, S'.reg r = some v → reg mc r = v.eval (envS (own m0 m) m' 176 (rsP m0 p) vals ret)) →
      sqRes mc = (vals' 6, vals' 7))
    (hrax : T'.reg .rax = some (.var 6)) (hrdx : T'.reg .rdx = some (.var 7))
    (hsz : T'.regions = [184, 128, 16]) (hfl : T'.flags = atomFlags) (hlab : T'.labels = [])
    (hal : ∀ m' ret, AliasesOk T' (envS (own m0 m) m' 176 (rsP m0 p) vals' ret))
    (hbd : T'.bounds = []) {st : MachineState}
    (hA : TAt m0 m p k off T vals st) (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) (TAt m0 m p k off' T' vals') st := by
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hB⟩ := hA
  simp only at hpc hB
  subst hpc
  refine sqStep (hknown := hknown) (lay h hM hpl) hsq (by decide) hB (hds.trans hp.1 hne) hrun hwr hsp hL hLW
    (hvals d (Mem.of_bnd h hM hpl hB)) (fun i hi mc hR ↦ ?_) (fun i hi mc hR ↦ ?_) hsz hfl hlab hal
    hbd
    fun st hpc' hB' ↦ .done _ ⟨by rw [hpc', Nat.add_assoc, hoff], hB'⟩
  · rw [hrax] at hi
    cases hi
    rw [hres d (Mem.of_bnd h hM hpl hB) _ mc hR]
  · rw [hrdx] at hi
    cases hi
    rw [hres d (Mem.of_bnd h hM hpl hB) _ mc hR]

omit [Host] in
/-- `EW::sq_iter`'s result for a count `8` and an element given by its limbs. -/
theorem sqRes_of [Labels] {env : Env} {S' : SState} {mc : MachineData}
    (hR : ∀ r v, S'.reg r = some v → reg mc r = v.eval env) {a0 a1 : Sym}
    (h8 : S'.reg .rdi = some (.lit 8)) (h0 : S'.reg .rsi = some a0) (h1 : S'.reg .rdx = some a1)
    {x : EW} (hx0 : a0.eval env = x.c0.toBitVec) (hx1 : a1.eval env = x.c1.toBitVec) :
    sqRes mc = ((frobenius8 x 1).c0.toBitVec, (frobenius8 x 1).c1.toBitVec) := by
  unfold sqRes
  rw [hR _ _ h8, hR _ _ h0, hR _ _ h1, hx0, hx1]
  rfl

end

end NativeRustcVmX64.Ring.Coeff
