module

public import NativeRustcVmX64.Whir.GlueLevel.Exec
public import NativeRustcVmX64.Spec.Whir
public import NativeRustcVm.Transcript.Frame

/-!
# `glue_level`'s layout and values (x86-64)

From the entry state `m0` (the state `s` at RDI): the arrays (`rsOf`, eight parts of the state:
the claim, the `α`s, the glued claims' count, the two new glued claims' headers and buffers), the
layout `lay` (`LayA`, the 64 bytes of stack arguments above the return address), and the values
the templates' variables take (`V`): the entry's pushed registers, the call results, `λ`, the
claim, the products `λ · oodValue`, `λ²`, `λ² · batched`, the counts.
-/

namespace NativeRustcVmX64.Whir.GlueLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.Whir.Rows
open NativeVm.Model NativeRustcVm.Whir
open NativeRustcVm.Transcript (off off_off off_zero toNat_off)

@[expose] public section

/-- The state's address. -/
abbrev pOf (m0 : MachineData) : BitVec 64 := reg m0 .rdi

/-- The first new glued claim's offset. -/
abbrev o1 (n : Nat) : Nat := 512 + 6064 * n
/-- The second's. -/
abbrev o2 (n : Nat) : Nat := 512 + 6064 * (n + 1)

/-- The arrays' offsets in the state and sizes. -/
def offs (n : Nat) : List (Nat × Nat) :=
  [(0, 16), (16, 488), (504, 8), (o1 n, 40), (o1 n + 40, 488), (o2 n, 40), (o2 n + 528, 1848),
    (o2 n + 2376, 3688)]

/-- The arrays. -/
def rsOf (s : WhirStateW) (m0 : MachineData) : List (BitVec 64 × Nat) :=
  (offs s.glued.size).map fun e ↦ (off (pOf m0) e.1, e.2)

/-- `λ`. -/
abbrev lamOf (m0 : MachineData) : EW := ewArg (reg m0 .rsi) (reg m0 .rdx)
/-- The out-of-domain value. -/
abbrev oodOf (m0 : MachineData) : EW := ewArg (stackArg m0 0) (stackArg m0 1)
/-- The batched value. -/
abbrev batOf (m0 : MachineData) : EW := ewArg (stackArg m0 6) (stackArg m0 7)

/-- A limb's bits. -/
abbrev c0 (x : EW) : BitVec 64 := x.c0.toBitVec
/-- A limb's bits. -/
abbrev c1 (x : EW) : BitVec 64 := x.c1.toBitVec

/-- `λ · oodValue`. -/
abbrev mul1 (m0 : MachineData) : EW := lamOf m0 * oodOf m0
/-- `λ²`. -/
abbrev l2 (m0 : MachineData) : EW := lamOf m0 * lamOf m0
/-- `λ² · batched`. -/
abbrev cc2 (m0 : MachineData) : EW := l2 m0 * batOf m0

/-- The variables' values (`x6`, `x7` the last call's result). -/
def V (s : WhirStateW) (m0 : MachineData) (x6 x7 : BitVec 64) : Nat → BitVec 64 := fun i ↦
  ([reg m0 .rbp, reg m0 .r15, reg m0 .r14, reg m0 .r13, reg m0 .r12, reg m0 .rbx, x6, x7,
    reg m0 .rsi, reg m0 .rdx, c0 s.claim, c1 s.claim, reg m0 .rcx, reg m0 .r8, reg m0 .r9,
    c0 (mul1 m0) ^^^ c0 s.claim, c1 (mul1 m0) ^^^ c1 s.claim, c1 (l2 m0), c0 (l2 m0),
    BitVec.ofNat 64 s.glued.size, c0 (cc2 m0) ^^^ (c0 (mul1 m0) ^^^ c0 s.claim),
    c1 (cc2 m0) ^^^ (c1 (mul1 m0) ^^^ c1 s.claim), BitVec.ofNat 64 s.alphas.size, 0#64,
    BitVec.ofNat 64 s.glued.size + BitVec.ofNat 64 1,
    (BitVec.ofNat 64 s.glued.size + BitVec.ofNat 64 1) * BitVec.ofNat 64 6064, BitVec.ofNat 64 1,
    BitVec.ofNat 64 s.glued.size + BitVec.ofNat 64 1 + BitVec.ofNat 64 1] :
    List (BitVec 64)).getD i 0

/-- The writable arrays: all but the `α`s. -/
abbrev wrAll : Nat → Bool := fun r ↦ r != 2

end

public section

variable {s : WhirStateW} {m0 : MachineData}

theorem allOf_of_forall {α : Type} {P : α → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, P a) → AllOf P l
  | [], _ => trivial
  | a :: _, h => ⟨h a List.mem_cons_self, allOf_of_forall fun b hb ↦ h b (List.mem_cons_of_mem _ hb)⟩

theorem offs_le (n : Nat) (hn : n + 2 ≤ gluedCap) :
    ∀ e ∈ offs n, 0 < e.2 ∧ e.1 + e.2 ≤ stateBytes := by
  have : n ≤ 8 := by unfold gluedCap at hn; omega
  simp only [offs, o1, o2, List.mem_cons, List.not_mem_nil, or_false, stateBytes]
  rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only <;> omega

theorem offs_sorted (n : Nat) : (offs n).Pairwise fun a b ↦ a.1 + a.2 ≤ b.1 := by
  simp only [offs, o1, o2, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
    implies_true]
  and_intros <;> omega

/-- Parts of a non-wrapping area at offsets `o`, `o'`, one before the other, are apart. -/
theorem apart_offs {p : BitVec 64} {N o n o' n' : Nat} (hp : NoWrap p N) (hn : 0 < n)
    (hn' : 0 < n') (h1 : o + n ≤ N) (h2 : o' + n' ≤ N) (h : o + n ≤ o' ∨ o' + n' ≤ o) :
    Apart (off p o) n (off p o') n' := by
  unfold NoWrap at hp
  unfold Apart
  rw [toNat_off (by omega), toNat_off (by omega)]
  omega

/-- A part of a non-wrapping area. -/
theorem noWrap_off {p : BitVec 64} {N o n : Nat} (hp : NoWrap p N) (hn : 0 < n)
    (h : o + n ≤ N) : NoWrap (off p o) n := by
  unfold NoWrap at *
  rw [toNat_off (by omega)]
  omega

theorem mapped_off {d : DataMem} {p : BitVec 64} {N o n : Nat} (hp : Mapped d p N)
    (h : o + n ≤ N) : Mapped d (off p o) n := fun i hi ↦ by
  rw [NativeRustcVm.Transcript.off_add]
  exact hp _ (by omega)

/-- A part of an area apart from another. -/
theorem apart_off_of {p a : BitVec 64} {N o n m : Nat} (hp : NoWrap p N) (hn : 0 < n)
    (h : o + n ≤ N) (ha : Apart p N a m) : Apart (off p o) n a m := by
  unfold NoWrap Apart at *
  rw [toNat_off (by omega)]
  omega

theorem stackBelow_glue (hok : StackOk m0 glueLevelStack) :
    (stackBelow m0 glueLevelStack).toNat = (rspOf m0).toNat - 240 :=
  NativeRustcVmX64.Field.stackBelow_toNat' hok.1

theorem rsp8_toNat (hargs : ArgsOk m0 8) : (rspOf m0 + 8#64).toNat = (rspOf m0).toNat + 8 := by
  have := hargs.2
  rw [BitVec.toNat_add, show (8#64).toNat = 8 from rfl]
  omega

/-- **The layout.** -/
theorem lay (hpre : GlueLevelPre s m0) : LayA m0 96 64 glueLevelStack (rsOf s m0) := by
  obtain ⟨hstk, hargs, -, hcap, -, -, -, -, ⟨⟨hpm, hpnw⟩, hpst⟩, -, -, -, hpa, -, -, -⟩ := hpre
  have htop : (rspOf m0).toNat + 8 + 64 ≤ 2 ^ 64 := hargs.2
  refine ⟨hstk, by decide, by decide, htop, hargs.1, allOf_of_forall ?_, ?_⟩
  · intro e he
    obtain ⟨⟨o, n⟩, ho, rfl⟩ := List.mem_map.mp he
    obtain ⟨hpos, hle⟩ := offs_le _ hcap _ ho
    simp only at hpos hle ⊢
    refine ⟨mapped_off hpm hle, noWrap_off hpnw hpos hle, ?_⟩
    have h1 := apart_off_of hpnw hpos hle hpst
    have h2 := apart_off_of hpnw hpos hle hpa
    have hs := stackBelow_glue hstk
    have hr := rsp8_toNat hargs
    have hS := hstk.1
    unfold Apart at h1 h2 ⊢
    simp only [pOf] at h1 h2 ⊢
    unfold glueLevelStack ewMulStack at *
    omega
  · refine List.pairwise_map.mpr ((offs_sorted _).imp_of_mem fun {a b} ha hb hab ↦ ?_)
    exact apart_offs hpnw (offs_le _ hcap a ha).1 (offs_le _ hcap b hb).1
      (offs_le _ hcap a ha).2 (offs_le _ hcap b hb).2 (.inl hab)

end

end NativeRustcVmX64.Whir.GlueLevel
