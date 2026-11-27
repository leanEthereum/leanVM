module

public import NativeRustcArm.Host
public import NativeRustcArm.ElfHost

/-!
# Contracts of rustc's AArch64 functions

A function's contract `Spec entry P Q`: from its entry, in a state satisfying `P`, the machine
inevitably returns to the link register (X30, where `bl` left the return address), in a state that
`Q` relates to the one it was entered in. A call site applies its callee's contract
(`Spec.apply`) where the symbolic executor leaves it at the callee's entry with the return address
in X30 (`retOf_bl`).

A label's address is its first `.label` directive's (`label_eq_addrOf`), the way Kraken resolves
branch targets (`Executable.labels`).

The memory predicates: `Mapped d a n`, the `n` bytes from `a` are data memory; `BytesAt d a bs`,
they hold `bs`; `SameOutside d d' R`, `d'` agrees with `d` outside the addresses `R` holds.

`Mathlib.Data.BitVec` supplies the ring instances used by address arithmetic proofs.
-/



namespace NativeRustcArm

@[expose] public section

/-- Where `ret` (`RET X30`) goes from `m`. -/
def retOf (m : MachineData) : Int64 := Int64.ofInt (m.regs.X30.toBitVec.toInt)

/-- **A function's contract**: from `entry`, in any state `m` satisfying `P`, the machine
inevitably reaches the return address `retOf m` in a state `m'` with `Q m m'`. -/
def Spec [NativeRustcArm.Host] (entry : Int64) (P : MachineData → Prop)
    (Q : MachineData → MachineData → Prop) : Prop :=
  ∀ m, P m → Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = retOf m ∧ Q m st.data)
    ⟨m, entry⟩

/-- The registers AAPCS64 asks a procedure to preserve besides SP: X19 to X29. -/
def calleeSaved : XReg → Bool
  | .X19 | .X20 | .X21 | .X22 | .X23 | .X24 | .X25 | .X26 | .X27 | .X28 | .X29 => true
  | _ => false

/-- Every byte of data memory in `d` still is in `d'` (Kraken's stores never unmap one). -/
def Kept (d d' : DataMem) : Prop := ∀ p, (d.get? p).isSome → (d'.get? p).isSome

/-- What a procedure keeps: `m'` holds the callee-saved registers and SP of `m`, and every byte of
data memory of `m`. -/
def Saved (m m' : MachineData) : Prop :=
  (∀ r, calleeSaved r = true → m'.regs.getXReg r = m.regs.getXReg r) ∧ m'.regs.SP = m.regs.SP ∧
    Kept m.dmem m'.dmem

/-- The `n` bytes from `a` are data memory. -/
def Mapped (d : DataMem) (a : BitVec 64) (n : Nat) : Prop :=
  ∀ i < n, (d.get? (a + BitVec.ofNat 64 i)).isSome

/-- The bytes from `a` are `bs`. -/
def BytesAt (d : DataMem) (a : BitVec 64) (bs : List UInt8) : Prop :=
  ∀ i (h : i < bs.length), d.get? (a + BitVec.ofNat 64 i) = some bs[i]

/-- The address `p` is one of the `n` bytes from `a`. -/
def InRange (a : BitVec 64) (n : Nat) (p : BitVec 64) : Prop := (p - a).toNat < n

/-- `d'` agrees with `d` at every address outside `R`. -/
def SameOutside (d d' : DataMem) (R : BitVec 64 → Prop) : Prop :=
  ∀ p, ¬ R p → d'.get? p = d.get? p

/-- The stack below SP: SP 16-byte aligned, and the `n` bytes below it data memory that does not
wrap around. -/
def StackOk (m : MachineData) (n : Nat) : Prop :=
  m.regs.SP.toNat % 16 = 0 ∧ n ≤ m.regs.SP.toNat ∧
    Mapped m.dmem (m.regs.SP.toBitVec - BitVec.ofNat 64 n) n

section
variable [NativeRustcArm.Host]

/-- Directive `d` of a function placed at `k`, its `j`th: if a label, the first of that name in
the program is it. -/
def labelFirst (k j : Nat) : Directive → Prop
  | .label l => NativeRustcArm.Host.prog.findIdx? (· = .label l) = some (k + j)
  | _ => True

instance (k j : Nat) : (d : Directive) → Decidable (labelFirst k j d)
  | .label _ => inferInstanceAs (Decidable (_ = some (k + j)))
  | .instr _ => isTrue trivial
  | .byteArray _ => isTrue trivial
  | .word _ _ => isTrue trivial

/-- A function's code `F` sits in the program from directive `k`, and each of its labels is the
first of that name in the program, so that a branch to it lands in `F`. -/
def Placed (F : List Directive) (k : Nat) : Prop :=
  F.IsInfixAt NativeRustcArm.Host.prog k ∧ ∀ j (h : j < F.length), labelFirst k j F[j]

instance (F : List Directive) (k : Nat) : Decidable (Placed F k) :=
  inferInstanceAs (Decidable (F.IsPrefix (NativeRustcArm.Host.prog.drop k) ∧
    ∀ j (h : j < F.length), labelFirst k j F[j]))

end

/-- **A function's contract** under a multi-section AArch64 `ElfHost`. -/
def ElfSpec [ElfHost] (entry : Int64) (P : MachineData → Prop)
    (Q : MachineData → MachineData → Prop) : Prop :=
  ∀ m, P m → Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = retOf m ∧ Q m st.data) ⟨m, entry⟩

/-- A function's code `F` sits in section `sec` of `ElfHost` from directive `k`, and every label
in `F` resolves in `Labels` to its section-computed address `ElfHost.addrOf sec (k + j)`. -/
def PlacedIn [ElfHost] (F : List Directive) (sec k : Nat) : Prop :=
  F.IsInfixAt (ElfHost.sectionProg sec) k ∧
  ∀ j (h : j < F.length), ∀ l, F[j] = .label l → label l = ElfHost.addrOf sec (k + j)

end

public section

theorem retOf_ofInt (a : Int64) (m : MachineData) (h : m.regs.X30 = UInt64.ofBitVec
    (BitVec.ofInt 64 a.toInt)) : retOf m = a := by
  simp [retOf, h]

/-- Where `bl` sends the return address: `retOf` of the state after it is the instruction after
the `bl`. -/
theorem retOf_bl (a : Int64) (m : MachineData) :
    retOf { m with regs := m.regs.setRegOrZr RegOrZr.X30 (BitVec.ofInt 64 a.toInt) } = a := by
  simp [retOf, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]

variable [NativeRustcArm.Host]

/-- A call site: the machine at the callee's entry, in a state satisfying the callee's
precondition, inevitably reaches the return address it holds, in a state the callee's
postcondition relates to it. -/
theorem Spec.apply {entry : Int64} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} (h : Spec entry P Q) {s : MachineState}
    (hpc : s.pc = entry) (hP : P s.data) :
    Eventually (step1 NativeRustcArm.Host.exe) (fun st ↦ st.pc = retOf s.data ∧ Q s.data st.data) s := by
  obtain ⟨m, pc⟩ := s
  subst hpc
  exact h m hP

/-- Sequencing: what inevitably reaches `p`, from where each state of `p` inevitably reaches `q`,
inevitably reaches `q`. -/
theorem Eventually.bind {p q : MachineState → Prop} {s : MachineState}
    (h : Eventually (step1 NativeRustcArm.Host.exe) p s)
    (k : ∀ s', p s' → Eventually (step1 NativeRustcArm.Host.exe) q s') :
    Eventually (step1 NativeRustcArm.Host.exe) q s :=
  eventually_trans _ p q s h k

/-- Weakening the goal. -/
theorem Eventually.mono {p q : MachineState → Prop} {s : MachineState}
    (h : Eventually (step1 NativeRustcArm.Host.exe) p s) (k : ∀ s', p s' → q s') :
    Eventually (step1 NativeRustcArm.Host.exe) q s :=
  eventually_weaken _ p q s k h

/-! ## Labels -/

theorem withAddresses_directive (i : Nat) :
    (NativeRustcArm.Host.exe.withAddresses[i]?).map (·.directive) = NativeRustcArm.Host.prog[i]? := by
  rw [Kraken.Executable.getElem?_withAddresses_eq, NativeRustcArm.Host.exe_getElem?]
  cases NativeRustcArm.Host.prog[i]? <;> rfl

omit [NativeRustcArm.Host] in
private theorem findSome?_label {l : Label} :
    ∀ (L : List (Kraken.Addressable (Kraken.Directive Instr ConstExpr))) (k : Nat),
      L.findIdx? (·.directive = .label l) = some k →
      L.findSome? (fun x ↦ if x.directive = .label l then some x.addr else none) =
        (L[k]?).map (·.addr)
  | [], k, h => by simp at h
  | x :: L, k, h => by
    rw [List.findIdx?_cons] at h
    by_cases hx : x.directive = .label l
    · simp only [hx, decide_true] at h
      cases h
      simp [hx]
    · simp only [hx, decide_false] at h
      cases hj : L.findIdx? (·.directive = .label l) with
      | none => simp [hj] at h
      | some j =>
        simp only [hj, Option.map_some, Bool.false_eq_true, ite_false, Option.some.injEq] at h
        subst h
        simp [hx, findSome?_label L j hj]

/-- **A label's address**: the address of the first `.label l` directive. -/
theorem label_eq_addrOf {l : Label} {k : Nat}
    (h : NativeRustcArm.Host.prog.findIdx? (· = .label l) = some k) :
    label l = NativeRustcArm.Host.addrOf k := by
  have hlen : NativeRustcArm.Host.exe.withAddresses.length = NativeRustcArm.Host.prog.length := by
    have := congrArg List.length
      (Kraken.Executable.withAddresses_map_snd NativeRustcArm.Host.exe.program NativeRustcArm.Host.exe.startAddr)
    simpa [NativeRustcArm.Host.exe, Kraken.Layout.apply] using this
  have hidx : NativeRustcArm.Host.exe.withAddresses.findIdx? (·.directive = .label l) = some k := by
    rw [List.findIdx?_eq_some_iff_getElem] at h ⊢
    obtain ⟨hk, hkl, hpre⟩ := h
    refine ⟨hlen ▸ hk, ?_, fun j hj ↦ ?_⟩
    · have := withAddresses_directive k
      rw [List.getElem?_eq_getElem (hlen ▸ hk), List.getElem?_eq_getElem hk] at this
      simp only [Option.map_some, Option.some.injEq] at this
      simpa [this] using hkl
    · have := withAddresses_directive j
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at this
      simp only [Option.map_some, Option.some.injEq] at this
      simpa [this] using hpre j hj
  show (NativeRustcArm.Host.exe.withAddresses.findSome?
    (fun x ↦ if x.directive = .label l then some x.addr else none)).getD (-1) = _
  have := findSome?_label NativeRustcArm.Host.exe.withAddresses k hidx
  rw [this, Kraken.Executable.getElem?_withAddresses_eq]
  have hk : k < NativeRustcArm.Host.exe.program.length := by
    rw [List.findIdx?_eq_some_iff_getElem] at hidx
    have := hidx.1
    rw [hlen] at this
    simpa [NativeRustcArm.Host.exe, Kraken.Layout.apply] using this
  rw [List.getElem?_eq_getElem hk]
  rfl

/-- A label of a placed function is at its directive's address. -/
theorem Placed.label {F : List Directive} {k : Nat} (h : Placed F k) {j : Nat} {l : Label}
    (hj : F[j]? = some (.label l)) : label l = NativeRustcArm.Host.addrOf (k + j) := by
  obtain ⟨hjl, hF⟩ := List.getElem?_eq_some_iff.mp hj
  have := h.2 j hjl
  rw [hF] at this
  exact label_eq_addrOf this

omit [NativeRustcArm.Host] in
/-- A label of a section-placed function is at its directive's address. -/
theorem PlacedIn.label [ElfHost] {F : List Directive} {sec k : Nat} (h : PlacedIn F sec k)
    {j : Nat} {l : Label} (hj : F[j]? = some (.label l)) : label l = ElfHost.addrOf sec (k + j) := by
  obtain ⟨hjl, hF⟩ := List.getElem?_eq_some_iff.mp hj
  exact h.2 j hjl l hF

omit [NativeRustcArm.Host] in
/-- Applying an `ElfSpec` at a call site. -/
theorem ElfSpec.apply [ElfHost] {entry : Int64} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} (h : ElfSpec entry P Q) {s : MachineState}
    (hpc : s.pc = entry) (hP : P s.data) :
    Eventually (elfStep1 ElfHost.exe) (fun st ↦ st.pc = retOf s.data ∧ Q s.data st.data) s := by
  obtain ⟨m, pc⟩ := s
  subst hpc
  exact h m hP

omit [NativeRustcArm.Host] in
theorem Eventually.bind_elf [ElfHost] {p q : MachineState → Prop} {s : MachineState}
    (h : Eventually (elfStep1 ElfHost.exe) p s)
    (k : ∀ s', p s' → Eventually (elfStep1 ElfHost.exe) q s') :
    Eventually (elfStep1 ElfHost.exe) q s :=
  eventually_trans _ p q s h k

omit [NativeRustcArm.Host] in
theorem Eventually.mono_elf [ElfHost] {p q : MachineState → Prop} {s : MachineState}
    (h : Eventually (elfStep1 ElfHost.exe) p s) (k : ∀ s', p s' → q s') :
    Eventually (elfStep1 ElfHost.exe) q s :=
  eventually_weaken _ p q s k h

omit [NativeRustcArm.Host] in
/-- Single-section `Placed` embeds into section 0 of `Host.toElfHost`. -/
theorem Placed.toPlacedIn [h : NativeRustcArm.Host] {F : List Directive} {k : Nat} (hp : Placed F k) :
    @PlacedIn (Host.toElfHost h) F 0 k := by
  refine ⟨hp.1, fun j hj l hF => ?_⟩
  have hlab := hp.label (by rw [List.getElem?_eq_getElem hj, hF])
  change (@instLabelsElfHost (Host.toElfHost h)).label l = @ElfHost.addrOf (Host.toElfHost h) 0 (k + j)
  rw [toElfHost_labels h, toElfHost_addrOf h (k + j)]
  exact hlab

omit [NativeRustcArm.Host] in
/-- An `ElfSpec` over `Host.toElfHost` yields a legacy `Spec` over `Host`. -/
theorem ElfSpec.toSpec [h : NativeRustcArm.Host]
    {entry : [Labels] → Int64} {P : [Labels] → MachineData → Prop}
    {Q : [Labels] → MachineData → MachineData → Prop}
    (hs : @ElfSpec (Host.toElfHost h) (@entry (@instLabelsElfHost (Host.toElfHost h)))
      (@P (@instLabelsElfHost (Host.toElfHost h))) (@Q (@instLabelsElfHost (Host.toElfHost h)))) :
    Spec (@entry _) (@P _) (@Q _) := by
  intro m hP
  have hL : @instLabelsElfHost (Host.toElfHost h) = (inferInstance : Labels) := toElfHost_labels h
  have h1 := hs m (by rwa [hL])
  rw [elfStep1_toElfHost h] at h1
  rwa [hL] at h1

end

end NativeRustcArm
