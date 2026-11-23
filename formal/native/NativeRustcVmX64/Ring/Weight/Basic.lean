module

public import NativeRustcVmX64.Ring.Weight.Exec
public import NativeRustcVmX64.Ring.Weight.Model
public import NativeRustcVmX64.Ring.Stack
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `ring_weight`: its layout, its values, its steps (x86-64)

From the entry state `m0` (`out` RDI, `r` RSI, RDX, `r'` RCX, R8, the coefficients R9): the frame
(`672` bytes below RSP), a window of an argument (`lay1`; the blocks read an argument as region
`1`), the template variables' values (`vv`: the pushed registers, the arguments, a pair `x` in
RAX, RDX, the coefficient's offset `16 k`, the total `t`, a spilled pair `s`), the powers in the
frame (`SlotsAt`).

- `At`: before the block at an offset, the template and an invariant of the machine state.
- `Bnd.sw`: the same state under a template with the same registers and writes, in other windows.
- `jfall`, `jjump`, `jcond`: a block without a call; `mstep`: a block and its call of `EW::mul`.
- The powers kept by a block missing them (`slots_keep`), stored by one (`slot_new`), kept by a
  callee (`slots_callee`), loaded (`slot_c0`, `slot_c1`); an argument's words (`win_load`).
-/

namespace NativeRustcVmX64.Ring.Weight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmX64.Vm.RingWeight
open NativeRustcVmX64.Transcript (after)

@[expose] public section

abbrev NW : Nat := ringWeightStack

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 672

/-- `|r|`, `|r'|`, the product's factors. -/
abbrev nR (m0 : MachineData) : Nat := (reg m0 .rdx).toNat
abbrev nQ (m0 : MachineData) : Nat := (reg m0 .r8).toNat
abbrev mn (m0 : MachineData) : Nat := min (nR m0) (nQ m0)

/-- `r`, `r'`, the coefficients. -/
abbrev rL (m0 : MachineData) : Array EW := slice m0 (reg m0 .rsi) (reg m0 .rdx)
abbrev qL (m0 : MachineData) : Array EW := slice m0 (reg m0 .rcx) (reg m0 .r8)
abbrev cL (m0 : MachineData) : Array EW := arr m0 (reg m0 .r9) coeffCount

/-- The total and the powers after `k` coefficients. -/
abbrev A (m0 : MachineData) (k : Nat) : EW × Array EW := accW (rL m0) (qL m0) (cL m0) k

abbrev c0 (x : EW) : BitVec 64 := x.c0.toBitVec
abbrev c1 (x : EW) : BitVec 64 := x.c1.toBitVec

/-- The variables' values. -/
def vv (m0 : MachineData) (x : EW) (k : Nat) (t s : EW) : Nat → BitVec 64
  | 0 => reg m0 .rbp
  | 1 => reg m0 .r15
  | 2 => reg m0 .r14
  | 3 => reg m0 .r13
  | 4 => reg m0 .r12
  | 5 => reg m0 .rbx
  | 6 => c0 x
  | 7 => c1 x
  | 8 => reg m0 .rdi
  | 9 => reg m0 .r9
  | 10 => reg m0 .rsi
  | 11 => reg m0 .rdx
  | 12 => reg m0 .rcx
  | 13 => reg m0 .r8
  | 14 => BitVec.ofNat 64 (16 * nR m0)
  | 15 => fb m0 + BitVec.ofNat 64 (48 + 16 * nR m0)
  | 16 => BitVec.ofNat 64 (mn m0)
  | 17 => BitVec.ofNat 64 (16 * mn m0)
  | 19 => BitVec.ofNat 64 (16 * k)
  | 20 => c0 t
  | 21 => c1 t
  | 23 => c1 s
  | 24 => c0 s
  | 25 => BitVec.ofNat 64 (nR m0 / 2 * 2)
  | _ => 0

-- `vv`'s equation lemmas, generated here once rather than in each importer that unfolds it.
attribute [local simp] vv

abbrev noWr : Nat → Bool := fun _ ↦ false

/-- The output, region `1` at the exit. -/
abbrev oWr : Nat → Bool := fun r ↦ r == 1

/-- The address of power `l`. -/
abbrev slotA (m0 : MachineData) (l : Nat) : BitVec 64 := fb m0 + BitVec.ofNat 64 (48 + 16 * l)

/-- Powers `l < c` hold `f l`. -/
def SlotsAt (m0 d : MachineData) (f : Nat → EW) (c : Nat) : Prop :=
  ∀ l < c, NativeRustcVm.EWAt d.dmem (slotA m0 l) (f l)

section
variable [Host]

/-- Before the block at `off`, in the windows `rs`. -/
def At (m0 : MachineData) (k off : Nat) (rs : List (BitVec 64 × Nat)) (wr : Nat → Bool)
    (T : SState) (vals : Nat → BitVec 64) (I : MachineData → Prop) (st : MachineState) : Prop :=
  st.pc = Host.addrOf (k + off) ∧ Bnd m0 672 NW rs wr T vals st.data ∧ I st.data

end

end

public section

variable {m0 : MachineData}

theorem ev_var [Labels] {m : MachineData} {F : Nat} {rs : List (BitVec 64 × Nat)}
    {vals : Nat → BitVec 64} {ret : BitVec 64} (i : Nat) :
    (Sym.var i).eval (envS m0 m F rs vals ret) = vals i := rfl

theorem ev_lit [Labels] {env : Env} (n : Nat) : (Sym.lit n).eval env = BitVec.ofNat 64 n := rfl

theorem ev_reg [Labels] {m : MachineData} {F : Nat} {rs : List (BitVec 64 × Nat)}
    {vals : Nat → BitVec 64} {ret : BitVec 64} (r : Reg64) :
    (Sym.reg r).eval (envS m0 m F rs vals ret) = m.regs.get64 r := rfl

/-! ## The checks -/

theorem JOk.spec {ds : List Directive} {T T' : SState} {x : Exit} {sizes : List Nat}
    {wr : Nat → Bool} {L LW : List (Nat × Sym)} (h : JOk ds T T' x sizes wr L LW = true) :
    exec ds T = some (after ds T, x) ∧ (after ds T).mem.all (writeOk 672 sizes wr) = true ∧
      rlinks false (after ds T) T' = some L ∧ wlinks (after ds T) T'.mem = some LW := by
  simp only [JOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem COk.spec {ds : List Directive} {T T' : SState} {sizes : List Nat}
    {L LW : List (Nat × Sym)} (h : COk ds T T' sizes L LW = true) :
    exec ds T = some (after ds T, .call NativeRustcVmX64.Vm.EWMul.entryLabel) ∧
      (after ds T).mem.all (writeOk 672 sizes fun _ ↦ false) = true ∧
      (after ds T).reg .rsp = some (.ptr 0 0) ∧
      rlinks true (after ds T) T' = some L ∧ wlinks (after ds T) T'.mem = some LW := by
  simp only [COk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem storeOk.spec {S : SState} {o : Nat} {a b : Sym} (h : storeOk S o a b = true) :
    ∀ u < 8, findWrite 0 (o + u) S.mem = some (a, u) ∧ findWrite 0 (o + 8 + u) S.mem = some (b, u) := by
  intro u hu
  have := List.all_eq_true.mp h u (List.mem_range.mpr hu)
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this

/-! ## Layouts -/

/-- The frame alone. -/
theorem lay0 (hst : StackOk m0 NW) : Lay m0 672 NW [] :=
  ⟨hst, by decide, by decide, trivial, List.Pairwise.nil⟩

/-- A window of an argument off the stack. -/
theorem lay1 (hst : StackOk m0 NW) {a : BitVec 64} {n : Nat} (hr : Readable m0 a n)
    (hs : OffStack m0 a n NW) {o s : Nat} (hos : o + s ≤ n) :
    Lay m0 672 NW [(a + BitVec.ofNat 64 o, s)] := by
  obtain ⟨hm, hw, hap⟩ := range_rest hr.1 hr.2 hs (o := o) (by omega)
  refine ⟨hst, by decide, by decide, ⟨⟨fun j hj ↦ hm j (by omega), ?_, ?_⟩, trivial⟩,
    List.pairwise_singleton _ _⟩
  · show NoWrap (a + BitVec.ofNat 64 o) s
    unfold NoWrap at hw ⊢; omega
  · show Apart (a + BitVec.ofNat 64 o) s (stackBelow m0 NW) (NW + 8)
    unfold Apart at hap ⊢; omega

/-! ## Switching templates -/

theorem Bnd.switch [Labels] {F N : Nat} {rs rs' : List (BitVec 64 × Nat)} {wr wr' : Nat → Bool}
    {T T' : SState} {vals vals' : Nat → BitVec 64} {m : MachineData}
    (hB : Bnd m0 F N rs wr T vals m) (hok : tplOk T' = true) {L LW : List (Nat × Sym)}
    (hL : rlinks false T T' = some L) (hLW : wlinks T T'.mem = some LW)
    (hvals : ∀ p ∈ L ++ LW, p.2.eval (envS m0 m F rs vals 0) = vals' p.1)
    (hsz : T'.regions = (F + 8) :: rs'.map Prod.snd) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hbd : T'.bounds = [])
    (hal : ∀ ret, AliasesOk T' (envS m0 m F rs' vals' ret))
    (hwr : ∀ q, outsOf rs wr q → outsOf rs' wr' q) (hknown : T'.known = [] := by rfl) :
    Bnd m0 F N rs' wr' T' vals' m :=
  ⟨fun ret ↦ match_links (hknown := hknown) (hB.mt 0) hok hL hLW (fun _ ↦ rfl) rfl rfl rfl hvals hfl
      (regions_envS hsz) hlab (fun _ _ h ↦ by rw [hbd] at h; cases h) (hal ret),
    fun q hq ↦ hB.same q fun h ↦ hq (h.elim .inl fun h' ↦ .inr (hwr q h')),
    hB.kept⟩

/-- **The same state under a template with the same registers and writes**, in other windows. -/
theorem Bnd.sw [Labels] {F N : Nat} {rs rs' : List (BitVec 64 × Nat)} {wr wr' : Nat → Bool}
    {T T' : SState} {vals : Nat → BitVec 64} {m : MachineData}
    (hB : Bnd m0 F N rs wr T vals m) (hok : SwOk T T' = true)
    (hsz : T'.regions = (F + 8) :: rs'.map Prod.snd)
    (hal : ∀ ret, AliasesOk T' (envS m0 m F rs' vals ret))
    (hwr : ∀ q, outsOf rs wr q → outsOf rs' wr' q) (hknown : T'.known = [] := by rfl) :
    Bnd m0 F N rs' wr' T' vals m := by
  unfold SwOk at hok
  simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hok
  obtain ⟨⟨⟨⟨htpl, hfl⟩, hlab⟩, hbd⟩, hl⟩ := hok
  revert hl
  cases hL : rlinks false T T' with
  | none => intro hl; cases hl
  | some L =>
    cases hLW : wlinks T T'.mem with
    | none => intro hl; cases hl
    | some LW =>
      intro hl
      refine Bnd.switch (hknown := hknown) hB htpl hL hLW (fun p hp ↦ ?_) hsz hfl hlab hbd hal hwr
      have := List.all_eq_true.mp hl p hp
      rw [beq_iff_eq] at this
      rw [this]
      rfl

theorem noAl [Labels] {T : SState} (hT : T.aliases = []) {env : Env} : AliasesOk T env := by
  intro x r o hx
  rw [hT] at hx
  cases hx

/-- A template's only alias. -/
theorem oneAl [Labels] {T : SState} {x : Sym} {r : Nat} {o : Int} (hT : T.aliases = [(x, r, o)])
    {env : Env} (h : x.eval env = env.base r + BitVec.ofInt 64 o) : AliasesOk T env := by
  intro x' r' o' hx
  rw [hT] at hx
  simp only [List.lookup] at hx
  split at hx
  · rename_i heq
    rw [beq_iff_eq] at heq
    subst heq
    cases hx
    exact h
  · cases hx

theorem outs_noWr {rs rs' : List (BitVec 64 × Nat)} {wr' : Nat → Bool} :
    ∀ q, outsOf rs noWr q → outsOf rs' wr' q := fun _ ⟨_, _, h, _⟩ ↦ by cases h

/-! ## Steps -/

section
variable [Host] {k : Nat}

/-- **A block falling through.** -/
theorem jfall (hp : Placed code k) {rs : List (BitVec 64 × Nat)} {wr : Nat → Bool}
    (h : Lay m0 672 NW rs) {ds : List Directive} {off next : Nat} (hds : ds.IsInfixAt code off)
    (hne : ds ≠ []) (hnext : off + ds.length = next) {T T' : SState} {vals vals' : Nat → BitVec 64}
    {L LW : List (Nat × Sym)}
    (hok : JOk ds T T' .fall ((672 + 8) :: rs.map Prod.snd) wr L LW = true)
    {I I' : MachineData → Prop}
    (hvals : ∀ m, Bnd m0 672 NW rs wr T vals m → I m → ∀ ret, ∀ p ∈ L ++ LW,
      p.2.eval (envS m0 m 672 rs vals ret) = vals' p.1)
    (hsz : T'.regions = (672 + 8) :: rs.map Prod.snd) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hal : ∀ m' ret, AliasesOk T' (envS m0 m' 672 rs vals' ret))
    (hbd : T'.bounds = [])
    (hI : ∀ m m', Bnd m0 672 NW rs wr T vals m → I m →
      Match (envS m0 m 672 rs vals 0) (after ds T) m' → I' m')
    {st : MachineState} (hA : At m0 k off rs wr T vals I st) (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) (At m0 k next rs wr T' vals' I') st := by
  obtain ⟨hrun, hwr, hL, hLW⟩ := JOk.spec hok
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hB, hId⟩ := hA
  simp only at hpc hB hId
  subst hpc
  exact jumpStep (hknown := hknown) h hB (hds.trans hp.1 hne) hrun (fun _ h ↦ by cases h) hwr hL hLW
    (hvals d hB hId) hsz hfl hlab hal (fun _ _ _ _ h ↦ by rw [hbd] at h; cases h)
    fun st' hpc hB' hm ↦ .done _ ⟨by rw [hpc, Nat.add_assoc, hnext], hB', hI d st'.data hB hId hm⟩

/-- **A block ending in a jump** to the block at `off'`. -/
theorem jjump (hp : Placed code k) {rs : List (BitVec 64 × Nat)} {wr : Nat → Bool}
    (h : Lay m0 672 NW rs) {ds : List Directive} {off off' : Nat} (hds : ds.IsInfixAt code off)
    (hne : ds ≠ []) {l : Label} (hl : Labels.label l = Host.addrOf (k + off'))
    {T T' : SState} {vals vals' : Nat → BitVec 64} {L LW : List (Nat × Sym)}
    (hok : JOk ds T T' (.jump l) ((672 + 8) :: rs.map Prod.snd) wr L LW = true)
    {I I' : MachineData → Prop}
    (hvals : ∀ m, Bnd m0 672 NW rs wr T vals m → I m → ∀ ret, ∀ p ∈ L ++ LW,
      p.2.eval (envS m0 m 672 rs vals ret) = vals' p.1)
    (hsz : T'.regions = (672 + 8) :: rs.map Prod.snd) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hal : ∀ m' ret, AliasesOk T' (envS m0 m' 672 rs vals' ret))
    (hbd : T'.bounds = [])
    (hI : ∀ m m', Bnd m0 672 NW rs wr T vals m → I m →
      Match (envS m0 m 672 rs vals 0) (after ds T) m' → I' m')
    {st : MachineState} (hA : At m0 k off rs wr T vals I st) (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) (At m0 k off' rs wr T' vals' I') st := by
  obtain ⟨hrun, hwr, hL, hLW⟩ := JOk.spec hok
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hB, hId⟩ := hA
  simp only at hpc hB hId
  subst hpc
  exact jumpStep (hknown := hknown) h hB (hds.trans hp.1 hne) hrun (fun _ h ↦ by cases h) hwr hL hLW
    (hvals d hB hId) hsz hfl hlab hal (fun _ _ _ _ h ↦ by rw [hbd] at h; cases h)
    fun st' hpc hB' hm ↦ .done _ ⟨by simp only [PcOk] at hpc; rw [hpc, hl], hB',
      hI d st'.data hB hId hm⟩

/-- **A block ending in a conditional branch** to the block at `off'`, its condition `b`. -/
theorem jcond (hp : Placed code k) {rs : List (BitVec 64 × Nat)} {wr : Nat → Bool}
    (h : Lay m0 672 NW rs) {ds : List Directive} {off off' next : Nat} (hds : ds.IsInfixAt code off)
    (hne : ds ≠ []) (hnext : off + ds.length = next) {l : Label}
    (hl : Labels.label l = Host.addrOf (k + off'))
    {T T' : SState} {vals vals' : Nat → BitVec 64} {c : SBool} {L LW : List (Nat × Sym)}
    (hok : JOk ds T T' (.cond c l) ((672 + 8) :: rs.map Prod.snd) wr L LW = true)
    {I I' : MachineData → Prop} {b : Bool}
    (hc : ∀ m, Bnd m0 672 NW rs wr T vals m → I m → c.eval (envS m0 m 672 rs vals 0) = b)
    (hvals : ∀ m, Bnd m0 672 NW rs wr T vals m → I m → ∀ ret, ∀ p ∈ L ++ LW,
      p.2.eval (envS m0 m 672 rs vals ret) = vals' p.1)
    (hsz : T'.regions = (672 + 8) :: rs.map Prod.snd) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hal : ∀ m' ret, AliasesOk T' (envS m0 m' 672 rs vals' ret))
    (hbd : T'.bounds = [])
    (hI : ∀ m m', Bnd m0 672 NW rs wr T vals m → I m →
      Match (envS m0 m 672 rs vals 0) (after ds T) m' → I' m')
    {st : MachineState} (hA : At m0 k off rs wr T vals I st) (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe)
      (At m0 k (if b then off' else next) rs wr T' vals' I') st := by
  obtain ⟨hrun, hwr, hL, hLW⟩ := JOk.spec hok
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hB, hId⟩ := hA
  simp only at hpc hB hId
  subst hpc
  refine jumpStep (hknown := hknown) h hB (hds.trans hp.1 hne) hrun (fun _ h ↦ by cases h) hwr hL hLW
    (hvals d hB hId) hsz hfl hlab hal (fun _ _ _ _ h ↦ by rw [hbd] at h; cases h)
    fun st' hpc hB' hm ↦ .done _ ⟨?_, hB', hI d st'.data hB hId hm⟩
  simp only [PcOk, hc d hB hId] at hpc
  rw [hpc]
  cases b
  · simp [Nat.add_assoc, hnext]
  · simp [hl]

/-- **A block and its call of `EW::mul`**, the product in RAX, RDX (`hres`), the invariant
carried through the block and the callee (`hI`). -/
theorem mstep (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {rs : List (BitVec 64 × Nat)} (h : Lay m0 672 NW rs) {ds : List Directive} {off next : Nat}
    (hds : ds.IsInfixAt code off) (hne : ds ≠ []) (hnext : off + ds.length = next) {T T' : SState}
    {vals vals' : Nat → BitVec 64} {L LW : List (Nat × Sym)}
    (hok : COk ds T T' ((672 + 8) :: rs.map Prod.snd) L LW = true)
    {I I' : MachineData → Prop}
    (hvals : ∀ m, Bnd m0 672 NW rs noWr T vals m → I m → ∀ ret, ∀ p ∈ L ++ LW,
      p.2.eval (envS m0 m 672 rs vals ret) = vals' p.1)
    (hrax : T'.reg .rax = some (.var 6)) (hrdx : T'.reg .rdx = some (.var 7))
    (hres : ∀ m, Bnd m0 672 NW rs noWr T vals m → I m → ∀ (mc : MachineData) ret,
      Match (envS m0 m 672 rs vals ret) (after ds T) mc →
      (mulRes mc).1 = vals' 6 ∧ (mulRes mc).2 = vals' 7)
    (hsz : T'.regions = (672 + 8) :: rs.map Prod.snd) (hfl : T'.flags = atomFlags)
    (hlab : T'.labels = []) (hal : ∀ m' ret, AliasesOk T' (envS m0 m' 672 rs vals' ret))
    (hbd : T'.bounds = [])
    (hI : ∀ m mc m', Bnd m0 672 NW rs noWr T vals m → I m →
      (∃ ret, Match (envS m0 m 672 rs vals ret) (after ds T) mc) → rspOf mc = fb m0 →
      SameOutside mc.dmem m'.dmem (InRange (stackBelow mc ewMulStack) ewMulStack) → I' m')
    {st : MachineState} (hA : At m0 k off rs noWr T vals I st) (hknown : T'.known = [] := by rfl) :
    Eventually (step1 Host.exe) (At m0 k next rs noWr T' vals' I') st := by
  obtain ⟨hrun, hwr, hsp, hL, hLW⟩ := COk.spec hok
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hB, hId⟩ := hA
  simp only at hpc hB hId
  subst hpc
  refine callStep (hknown := hknown) h hB (hds.trans hp.1 hne) hrun hwr hsp hmul (S := ewMulStack) (by decide)
    (fun _ _ _ h ↦ h) (W := fun _ ↦ False)
    (fun _ _ hq ↦ ⟨fun p hp ↦ hq.2.2.1 p fun h ↦ hp (.inl h), hq.2.2.2⟩) (fun _ h ↦ h.elim)
    hL hLW (hvals d hB hId)
    (fun i hi mc m' hm hq ↦ by
      rw [hrax] at hi; cases hi
      exact hq.1.trans (hres d hB hId mc _ hm).1)
    (fun i hi mc m' hm hq ↦ by
      rw [hrdx] at hi; cases hi
      exact hq.2.1.trans (hres d hB hId mc _ hm).2)
    (fun _ _ _ _ _ _ _ _ _ _ _ h ↦ h) hsz hfl hlab hal
    (fun _ _ _ _ hx ↦ by rw [hbd] at hx; cases hx)
    fun st hpc' hB' ⟨mc, hm, hsp', hq⟩ ↦ .done _ ⟨by rw [hpc', Nat.add_assoc, hnext], hB',
      hI d mc st.data hB hId ⟨_, hm⟩ hsp' hq.2.2.1⟩

/-- **Switching templates** at a block's start. -/
theorem At.sw {off : Nat} {rs rs' : List (BitVec 64 × Nat)} {wr wr' : Nat → Bool}
    {T T' : SState} {vals : Nat → BitVec 64} {I : MachineData → Prop} {st : MachineState}
    (hA : At m0 k off rs wr T vals I st) (hok : SwOk T T' = true)
    (hsz : T'.regions = (672 + 8) :: rs'.map Prod.snd)
    (hal : ∀ m ret, AliasesOk T' (envS m0 m 672 rs' vals ret))
    (hwr : ∀ q, outsOf rs wr q → outsOf rs' wr' q) (hknown : T'.known = [] := by rfl) :
    At m0 k off rs' wr' T' vals I st :=
  ⟨hA.1, Bnd.sw (hknown := hknown) hA.2.1 hok hsz (hal st.data) hwr, hA.2.2⟩

end

/-! ## The powers -/

theorem slotA_eq (l j : Nat) : slotA m0 l + BitVec.ofNat 64 j =
    stackBelow m0 672 + BitVec.ofNat 64 (48 + 16 * l + j) :=
  NativeRustcVm.addr_add _ _ _

/-- A frame byte from `lo` to `hi` no write of a block covers. -/
theorem not_written [Labels] {rs : List (BitVec 64 × Nat)} {vals : Nat → BitVec 64} (hst : StackOk m0 NW) {m : MachineData} {ret : BitVec 64} {S : SState}
    {lo hi : Nat} (hS : missR lo hi S = true) {j : Nat} (h1 : lo ≤ j) (h2 : j < hi)
    (hhi : hi ≤ 680) :
    ¬Written (envS m0 m 672 rs vals ret) S (stackBelow m0 672 + BitVec.ofNat 64 j) := by
  rintro ⟨w, hw, b, sz, hb, hw1, hw2⟩
  simp only [missR, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
    decide_eq_true_eq] at hS
  obtain ⟨hr, hok⟩ := hS w hw
  rw [hr] at hb
  simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  have g : NativeRustcVmX64.Field.Geo m0 672 NW := ⟨hst, by decide, by decide⟩
  rw [g.addr (by omega)] at hw1 hw2
  rw [g.base] at hw1 hw2
  omega

section
variable [Labels] {rs : List (BitVec 64 × Nat)} {vals : Nat → BitVec 64}

/-- **Powers kept** by a block whose writes miss powers `lo` to `hi`. -/
theorem slots_keep (hst : StackOk m0 NW) {m m' : MachineData} {ret : BitVec 64} {S : SState}
    (hwf : (envS m0 m 672 rs vals ret).WF) (hm : Match (envS m0 m 672 rs vals ret) S m')
    {f : Nat → EW} {c lo hi : Nat} (hc : c ≤ 36) (hlo : lo ≤ 36) (h : SlotsAt m0 m f c)
    (h1 : missR 48 (48 + 16 * lo) S = true) (h2 : missR (48 + 16 * hi) 624 S = true) :
    ∀ l < c, (l < lo ∨ hi ≤ l) → NativeRustcVm.EWAt m'.dmem (slotA m0 l) (f l) := by
  intro l hl hlh
  refine NativeRustcVm.BytesAt.of_sameOutside (h l hl) (R := Written (envS m0 m 672 rs vals ret) S)
    (fun q hq ↦ hm.get?_mem0 hwf hq) fun j hj hR ↦ ?_
  rw [NativeRustcVm.length_ewBytes] at hj
  rw [slotA_eq] at hR
  rcases hlh with hlh | hlh
  · exact not_written hst h1 (j := 48 + 16 * l + j) (by omega) (by omega) (by omega) hR
  · exact not_written hst h2 (j := 48 + 16 * l + j) (by omega) (by omega) (by omega) hR

/-- **All powers kept** by a block whose writes miss them. -/
theorem slotsAt_keep (hst : StackOk m0 NW) {m m' : MachineData} {ret : BitVec 64} {S : SState}
    (hwf : (envS m0 m 672 rs vals ret).WF) (hm : Match (envS m0 m 672 rs vals ret) S m')
    {f : Nat → EW} {c : Nat} (hc : c ≤ 36) (h : SlotsAt m0 m f c)
    (hS : missR 48 624 S = true) : SlotsAt m0 m' f c := fun l hl ↦
  NativeRustcVm.BytesAt.of_sameOutside (h l hl) (R := Written (envS m0 m 672 rs vals ret) S)
    (fun q hq ↦ hm.get?_mem0 hwf hq) fun j hj hR ↦ by
      rw [NativeRustcVm.length_ewBytes] at hj
      rw [slotA_eq] at hR
      exact not_written hst hS (j := 48 + 16 * l + j) (by omega) (by omega) (by omega) hR

/-- **A power stored** by a block: its two words. -/
theorem slot_new {m m' : MachineData} {ret : BitVec 64} {S : SState}
    (hm : Match (envS m0 m 672 rs vals ret) S m') {l : Nat} (hl : l < 36) {a b : Sym}
    (hs : storeOk S (48 + 16 * l) a b = true) :
    NativeRustcVm.EWAt m'.dmem (slotA m0 l)
      ⟨UInt64.ofBitVec (a.eval (envS m0 m 672 rs vals ret)),
        UInt64.ofBitVec (b.eval (envS m0 m 672 rs vals ret))⟩ := by
  have w0 := NativeRustcVmX64.Transcript.wordAt_write hm (r := 0) (o := 48 + 16 * l) rfl
    (by omega) fun u hu ↦ (storeOk.spec hs u hu).1
  have w1 := NativeRustcVmX64.Transcript.wordAt_write hm (r := 0) (o := 48 + 16 * l + 8) rfl
    (by omega) fun u hu ↦ (storeOk.spec hs u hu).2
  refine NativeRustcVm.ewAt_iff.mpr ⟨w0, ?_⟩
  rw [NativeRustcVm.addr_add_add]
  exact w1

omit [Labels] in
/-- **Power `l` loaded**, limb `0`. -/
theorem slot_c0 {m : MachineData} {ret : BitVec 64} {f : Nat → EW} {c l : Nat}
    (h : SlotsAt m0 m f c) (hl : l < c) :
    (envS m0 m 672 rs vals ret).load 0 (48 + 16 * l) 8 = c0 (f l) := by
  rw [load_eq_wordOf]
  exact congrArg UInt64.toBitVec
    (NativeRustcVm.wordOf_of_wordAt (NativeRustcVm.ewAt_iff.mp (h l hl)).1)

omit [Labels] in
/-- **Power `l` loaded**, limb `1`. -/
theorem slot_c1 {m : MachineData} {ret : BitVec 64} {f : Nat → EW} {c l : Nat}
    (h : SlotsAt m0 m f c) (hl : l < c) :
    (envS m0 m 672 rs vals ret).load 0 (56 + 16 * l) 8 = c1 (f l) := by
  rw [load_eq_wordOf]
  have h1 := (NativeRustcVm.ewAt_iff.mp (h l hl)).2
  rw [show slotA m0 l + 8#64 = slotA m0 l + BitVec.ofNat 64 8 from rfl,
    NativeRustcVm.addr_add_add, show 48 + 16 * l + 8 = 56 + 16 * l by omega] at h1
  exact congrArg UInt64.toBitVec (NativeRustcVm.wordOf_of_wordAt h1)

end

/-- **Powers kept by a callee** below the frame. -/
theorem slots_callee (hst : StackOk m0 NW) {mc m' : MachineData} (hsp : rspOf mc = fb m0)
    (hq : SameOutside mc.dmem m'.dmem (InRange (stackBelow mc ewMulStack) ewMulStack))
    {f : Nat → EW} {c : Nat} (hc : c ≤ 36) (h : SlotsAt m0 mc f c) : SlotsAt m0 m' f c := by
  intro l hl
  refine NativeRustcVm.BytesAt.of_sameOutside (h l hl) hq fun j hj hR ↦ ?_
  rw [NativeRustcVm.length_ewBytes] at hj
  rw [slotA_eq] at hR
  exact not_callee hst hsp (by decide) (j := 48 + 16 * l + j) (by omega) hR

/-! ## The arguments -/

/-- **A word of an argument's window**, the entry's. -/
theorem win_load [Labels] (hst : StackOk m0 NW) {a : BitVec 64} {n : Nat} (hr : Readable m0 a n)
    (hs : OffStack m0 a n NW) {o s : Nat} {T : SState} {vals : Nat → BitVec 64}
    {m : MachineData} (hB : Bnd m0 672 NW [(a + BitVec.ofNat 64 o, s)] noWr T vals m) {j : Nat}
    (hj : o + j + 8 ≤ n) {ret : BitVec 64} :
    (envS m0 m 672 [(a + BitVec.ofNat 64 o, s)] vals ret).load 1 j 8 =
      (NativeRustcVm.wordOf m0.dmem (a + BitVec.ofNat 64 (o + j))).toBitVec := by
  rw [load_eq_wordOf, show (envS m0 m 672 [(a + BitVec.ofNat 64 o, s)] vals ret).base 1 =
    a + BitVec.ofNat 64 o from rfl, Env.ofMachine_mem0, NativeRustcVm.addr_add]
  refine congrArg UInt64.toBitVec (NativeRustcVm.wordOf_congr fun i hi ↦ ?_)
  rw [NativeRustcVm.addr_add]
  refine hB.same _ fun h ↦ h.elim (fun h1 ↦ ?_) fun ⟨_, _, hw', _⟩ ↦ by cases hw'
  exact NativeRustcVm.Apart.not_inRange_add hs hr.2 (noWrap_stackBelow hst)
    (show o + j + i < n by omega) (inRange_le h1 (Nat.le_add_right _ _))

theorem getD_slice (m : MachineData) (a n : BitVec 64) {i : Nat} (hi : i < n.toNat) :
    (slice m a n).getD i 0 = NativeRustcVm.ewOf m.dmem (a + BitVec.ofNat 64 (16 * i)) := by
  simp [slice, Array.getD, hi]

theorem getD_arr (m : MachineData) (a : BitVec 64) {n i : Nat} (hi : i < n) :
    (arr m a n).getD i 0 = NativeRustcVm.ewOf m.dmem (a + BitVec.ofNat 64 (16 * i)) := by
  simp [arr, Array.getD, hi]

/-- An element's limbs, as words. -/
theorem ew_words (d : DataMem) (a : BitVec 64) (i : Nat) :
    (NativeRustcVm.wordOf d (a + BitVec.ofNat 64 (16 * i))).toBitVec =
        c0 (NativeRustcVm.ewOf d (a + BitVec.ofNat 64 (16 * i))) ∧
      (NativeRustcVm.wordOf d (a + BitVec.ofNat 64 (16 * i + 8))).toBitVec =
        c1 (NativeRustcVm.ewOf d (a + BitVec.ofNat 64 (16 * i))) := by
  refine ⟨rfl, ?_⟩
  show _ = (NativeRustcVm.wordOf d (a + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 8)).toBitVec
  rw [NativeRustcVm.addr_add_add]

end

end NativeRustcVmX64.Ring.Weight
