import Rv64Verifier.Proofs.Layout.Repr
import Rv64Verifier.Proofs.Field.Contracts

/-!
# Contracts of the layout functions

Statements only: `Proofs/Layout/*.lean` prove them, each taking its callees' contracts (these, and
the runtime's and the field's) as hypotheses. A contract says what the function computes when it
returns, as the mirror in `Model/Layout.lean` (`Model.LayoutMirror`) computes it on the values its
arguments hold (`Repr.lean`); a panic is a trap, a dead end, and an allocation that fails halts.

Each states the bytes below `sp` it may use, its callees' included (`*Stack`), and the memory it
may change: what it writes, the stack, `NEXT` and what it allocates (`Fresh`). A new value's buffers
are fresh (`NewBuf`), so a caller keeps them apart from what it already holds.
-/

namespace Rv64Verifier.Layout
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Model.LayoutMirror

/-! ## `Form::term`, at `0x800050a8` -/

@[rv_addr] def termStack : Nat := 80

/-- `a0` = where the `Form` goes, `a1` = the monomial, `a2` = the coefficient. -/
structure TermPre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s termStack
  out : ValidMemRange (s.getReg .x10) 3
  mono : ValidMemRange (s.getReg .x11) 3
  coeff : ValidMemRange (s.getReg .x12) 3
  monoOk : MonoOk s (s.getReg .x11)
  outFree : Outside s (s.getReg .x10) 24
  monoNext : Apart (s.getReg .x11) 24 nextAddr 8
  coeffNext : Apart (s.getReg .x12) 24 nextAddr 8
  outStack : Apart (s.getReg .x10) 24 (stackLo s termStack) termStack
  monoStack : Apart (s.getReg .x11) 24 (stackLo s termStack) termStack
  coeffStack : Apart (s.getReg .x12) 24 (stackLo s termStack) termStack

/-- What every constructor of a `Form` at `out` ensures: a sound `Form`, its buffer allocated by the
call, and memory changed only at `out`, the `n` bytes below `sp`, `NEXT` and what it allocates. -/
structure NewForm (s t : MachineState) (out : Word) (n : Nat) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  ok : FormOk t out
  fresh : NewBuf s t (vecPtr t out) (48 * (vecCap t out).toNat) 8
  frame : DFrame s t fun a ↦ Within a out 24 ∨ Within a (stackLo s n) n ∨ Within a nextAddr 8 ∨
    Fresh s t a

/-- `Form::term(monomial, coefficient)`. -/
def TermSpec : Prop := FunSpec Image.code 0x800050a8 TermPre fun s t ↦
  NewForm s t (s.getReg .x10) termStack ∧
    formOf t (s.getReg .x10) = .term (monoOf s (s.getReg .x11)) (eAt s (s.getReg .x12))

/-! ## `col`, at `0x80004b34`, and `prod`, at `0x80005138` -/

/-- Their 96-byte frames, and `pow`'s stack below (deeper than `term`'s). -/
@[rv_addr] def colStack : Nat := 96 + powStack

/-- `a0` = where the `Form` goes. `pow` reads `.rodata`. -/
structure ColPre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s colStack
  out : ValidMemRange (s.getReg .x10) 3
  outFree : Outside s (s.getReg .x10) 24
  outStack : Apart (s.getReg .x10) 24 (stackLo s colStack) colStack
  rodata : RodataOk s

/-- `col(index, exponent)`: `a1` = the index, `a2` = the exponent. -/
def ColSpec : Prop := FunSpec Image.code 0x80004b34 ColPre fun s t ↦
  NewForm s t (s.getReg .x10) colStack ∧
    formOf t (s.getReg .x10) = colRust (s.getReg .x11).toNat (s.getReg .x12).toNat

/-- `prod(a, b, exponent)`: `a1`, `a2` = the columns, `a3` = the exponent. -/
def ProdSpec : Prop := FunSpec Image.code 0x80005138 ColPre fun s t ↦
  NewForm s t (s.getReg .x10) colStack ∧
    formOf t (s.getReg .x10) =
      prodRust (s.getReg .x11).toNat (s.getReg .x12).toNat (s.getReg .x13).toNat

/-! ## `Form::evaluate`, at `0x80010924` -/

/-- Its 144-byte frame, and `mul`'s stack below it. -/
@[rv_addr] def evaluateStack : Nat := 144 + Contracts.mulStack

/-- `a0` = where the value goes, `a1`/`a2` = the form's terms (a slice), `a3`/`a4` = the row (a
slice of `E`). `mul` reads `.rodata`. -/
structure EvaluatePre (s : MachineState) : Prop where
  out : ValidMemRange (s.getReg .x10) 3
  terms : ValidMemRange (s.getReg .x11) (6 * (s.getReg .x12).toNat)
  column : ValidMemRange (s.getReg .x13) (3 * (s.getReg .x14).toNat)
  stack : StackOk s evaluateStack
  outStack : Apart (s.getReg .x10) 24 (stackLo s evaluateStack) evaluateStack
  termsStack : Apart (s.getReg .x11) (48 * (s.getReg .x12).toNat) (stackLo s evaluateStack)
    evaluateStack
  columnStack : Apart (s.getReg .x13) (24 * (s.getReg .x14).toNat) (stackLo s evaluateStack)
    evaluateStack
  rodata : RodataOk s
  stackRodata : Apart (stackLo s evaluateStack) evaluateStack rodataBase rodataSize

/-- The form's value at the row; memory changes only at `out` and on the stack. -/
structure EvaluatePost (s t : MachineState) : Prop where
  value : eAt t (s.getReg .x10) =
    FormRust.evaluate ⟨termsOf s (s.getReg .x11) (s.getReg .x12).toNat⟩
      (eListAt s (s.getReg .x13) (s.getReg .x14).toNat)
  frame : ∀ a, ¬ Within a (s.getReg .x10) 24 →
    ¬ Within a (stackLo s evaluateStack) evaluateStack → t.getMem a = s.getMem a

def EvaluateSpec : Prop := FunSpec Image.code 0x80010924 EvaluatePre EvaluatePost

/-! ## `Form::add_scaled`, at `0x800119cc` -/

/-- Its 144-byte frame, and `mul`'s stack below it (deeper than `grow_one`'s). -/
@[rv_addr] def addScaledStack : Nat := 144 + Contracts.mulStack

/-- `a0` = `self`, a `Form`; `a1`/`a2` = `other`'s terms (a slice); `a3` = the weight. The loop
writes `self`'s header and buffer, so neither holds an argument; `grow_one` allocates, so no
argument is in the free heap. `mul` reads `.rodata`. -/
structure AddScaledPre (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s addScaledStack
  self : ValidMemRange (s.getReg .x10) 3
  ok : FormOk s (s.getReg .x10)
  other : ValidMemRange (s.getReg .x11) (6 * (s.getReg .x12).toNat)
  otherTags : ∀ i < (s.getReg .x12).toNat,
    MonoOk s (s.getReg .x11 + BitVec.ofNat 64 (48 * i))
  weight : ValidMemRange (s.getReg .x13) 3
  rodata : RodataOk s
  selfFree : Outside s (s.getReg .x10) 24
  otherFree : Outside s (s.getReg .x11) (48 * (s.getReg .x12).toNat)
  weightFree : Outside s (s.getReg .x13) 24
  selfStack : Apart (s.getReg .x10) 24 (stackLo s addScaledStack) addScaledStack
  otherStack : Apart (s.getReg .x11) (48 * (s.getReg .x12).toNat) (stackLo s addScaledStack)
    addScaledStack
  weightStack : Apart (s.getReg .x13) 24 (stackLo s addScaledStack) addScaledStack
  selfOther : Apart (s.getReg .x10) 24 (s.getReg .x11) (48 * (s.getReg .x12).toNat)
  selfWeight : Apart (s.getReg .x10) 24 (s.getReg .x13) 24
  selfRodata : Apart (s.getReg .x10) 24 rodataBase rodataSize
  buf : ∀ x, formBuf s (s.getReg .x10) x → ¬ (Within x (s.getReg .x10) 24 ∨
    Within x (s.getReg .x11) (48 * (s.getReg .x12).toNat) ∨ Within x (s.getReg .x13) 24)

/-- `self` is `self.add_scaled(other, weight)`, its buffer the old one or a new one; memory changes
only in `self`'s header and buffer, the stack, `NEXT` and what it allocates. -/
structure AddScaledPost (s t : MachineState) : Prop where
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  value : formOf t (s.getReg .x10) = (formOf s (s.getReg .x10)).addScaled
    ⟨termsOf s (s.getReg .x11) (s.getReg .x12).toNat⟩ (eAt s (s.getReg .x13))
  ok : FormOk t (s.getReg .x10)
  buf : ∀ x, formBuf t (s.getReg .x10) x → formBuf s (s.getReg .x10) x ∨ Fresh s t x
  frame : DFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨ formBuf s (s.getReg .x10) a ∨
    Within a (stackLo s addScaledStack) addScaledStack ∨ Within a nextAddr 8 ∨ Fresh s t a

def AddScaledSpec : Prop := FunSpec Image.code 0x800119cc AddScaledPre AddScaledPost

/-! ## Composing constructors -/

/-- A `Form` built by a callee, seen from its caller: the callee's stack within the caller's, and
what the caller wrote before the call within its stack and `NEXT`. -/
theorem NewForm.lift {s t u : MachineState} {out : Word} {m n : Nat} {W : Word → Prop}
    (h : NewForm t u out m) (hn : heapNext t = heapNext s) (hf : DFrame s t W)
    (hW : ∀ a, W a → Within a (stackLo s n) n ∨ Within a nextAddr 8)
    (hst : ∀ a, Within a (stackLo t m) m → Within a (stackLo s n) n) : NewForm s u out n where
  heap := h.heap
  mono := hn ▸ h.mono
  ok := h.ok
  fresh := by simpa only [NewBuf, hn] using h.fresh
  frame := (hf.union h.frame).mono fun a ha ↦ by
    rcases ha with ha | ha | ha | ha | ha
    · rcases hW a ha with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inl ha
    · exact Or.inr (Or.inl (hst a ha))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (by simpa only [Fresh, hn] using ha)))

/-- A step that writes nothing keeps a new `Form`. -/
theorem NewForm.same {s t u : MachineState} {out : Word} {n : Nat} (h : NewForm s t out n)
    (hu : ∀ a, u.getMem a = t.getMem a) (hw : out.toNat + 24 ≤ 2 ^ 64) :
    NewForm s u out n ∧ formOf u out = formOf t out := by
  have hn : heapNext u = heapNext t := by simp only [heapNext, hu]
  have hf := formOf_frame (DFrame.of_same hu fun _ ↦ False) h.ok (fun _ _ h ↦ h) (fun _ _ h ↦ h) hw
    h.heap hn.ge
  refine ⟨⟨⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩, hn ▸ h.mono, hf.2, ?_, ?_⟩, hf.1⟩
  · simpa only [NewBuf, vecPtr, vecCap, hu, hn] using h.fresh
  · exact (h.frame.union (DFrame.of_same hu fun _ ↦ False)).mono fun a ha ↦ by
      rcases ha with ha | ha
      · rcases ha with ha | ha | ha | ha
        · exact Or.inl ha
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr (Or.inl ha))
        · exact Or.inr (Or.inr (Or.inr (by simpa only [Fresh, hn] using ha)))
      · exact ha.elim

end Rv64Verifier.Layout
