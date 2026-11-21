module

public import NativeArm.Instr
public import Std.Data.String.ToNat

/-!
# The compiler from statements to Kraken's AArch64

`Compile.code` lays a statement out as Kraken directives with local labels `.L<n>` drawn from a
counter, branching with a condition's flag-setting code and a `B.<cc>` on the inverted condition
code. `Compile.program` puts the body after the entry label `qm_entry` and the failure handler
after `qm_fail`, each ending with `ORR X0, XZR, X9` (the result, `rax`, in the return register) and
`RET`. Every label of a compiled program is distinct (`Compile.program_labels_nodup`), so that
Kraken's label lookup, which takes the first match, finds each label where the compiler put it.
-/

open Native

namespace NativeArm.Compile

@[expose] public section

/-- The local label `.L<n>`. -/
def lbl (n : Nat) : Label := ".L" ++ Nat.repr n

/-- `B l`. -/
def b (l : Label) : Directive := .instr ⟨.W64, .B (.label l)⟩

/-- `B.<cc> l`. -/
def bcc (cc : CondCode) (l : Label) : Directive := .instr ⟨.W64, .B_cond cc (.label l)⟩

/-- Instructions as directives. -/
def ins (is : List Instr) : Program := is.map .instr

/-- `X0 := X9`: the result `rax` in the return register. -/
def movRetI : Instr := ⟨.W64, .ORR_s (xr .X0) xzr (sr .X9)⟩

/-- `RET`. -/
def ret : Directive := .instr ⟨.W64, .RET (xr .X30)⟩

/-- The code of a statement and the next free label number, its labels numbered from `n`. -/
def code : Stmt → Nat → Program × Nat
  | .skip, n => ([], n)
  | .ins i, n => (ins i.toArm, n)
  | .seq s₁ s₂, n =>
    let c₁ := code s₁ n
    let c₂ := code s₂ c₁.2
    (c₁.1 ++ c₂.1, c₂.2)
  | .ite c t e, n =>
    let ct := code t (n + 2)
    let ce := code e ct.2
    (ins c.toArm ++ [bcc c.armCC.invert (lbl n)] ++ ct.1 ++ [b (lbl (n + 1)), .label (lbl n)] ++
      ce.1 ++ [.label (lbl (n + 1))], ce.2)
  | .loop c body, n =>
    let cb := code body (n + 2)
    ([.label (lbl n)] ++ ins c.toArm ++ [bcc c.armCC.invert (lbl (n + 1))] ++ cb.1 ++
      [b (lbl n), .label (lbl (n + 1))], cb.2)
  | .fail, n => ([b "qm_fail"], n)

/-- A program's code: `body` from the entry `qm_entry` to a `RET`, then `onFail` from the
failure exit `qm_fail` to a `RET`, each returning `rax` in X0. -/
def program (body onFail : Stmt) : Program :=
  let cb := code body 0
  [.label "qm_entry"] ++ cb.1 ++ [.instr movRetI, ret] ++ [.label "qm_fail"] ++
    (code onFail cb.2).1 ++ [.instr movRetI, ret]

/-- The index of the `RET` that ends the body. -/
def retOkIndex (body : Stmt) : Nat := 2 + (code body 0).1.length

/-- The index of the `RET` that ends the failure handler. -/
def retFailIndex (body onFail : Stmt) : Nat :=
  5 + (code body 0).1.length + (code onFail (code body 0).2).1.length

/-- The label a directive defines. -/
def labelOf : Directive → Option Label
  | .label l => some l
  | _ => none

end

public section

theorem program_retOk (body onFail : Stmt) :
    (program body onFail)[retOkIndex body]? = some ret := by
  simp only [program, retOkIndex]
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
    List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
  simp only [List.length_append, List.length_cons, List.length_nil]
  rw [show 2 + (code body 0).1.length - (1 + (code body 0).1.length) = 1 by omega]
  rfl

theorem program_retFail (body onFail : Stmt) :
    (program body onFail)[retFailIndex body onFail]? = some ret := by
  simp only [program, retFailIndex]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_append, List.length_cons, List.length_nil]
  rw [show 5 + (code body 0).1.length + (code onFail (code body 0).2).1.length -
    (1 + (code body 0).1.length + 2 + 1 + (code onFail (code body 0).2).1.length) = 1 by omega]
  rfl

/-! ## Distinct labels -/

theorem lbl_injective {i j : Nat} (h : lbl i = lbl j) : i = j :=
  Nat.repr_injective ((String.append_right_inj _).mp h)

theorem lbl_ne_fail (n : Nat) : lbl n ≠ "qm_fail" := by
  intro h
  have := congrArg (fun s => s.toList.head?) h
  simp [lbl, String.toList_append] at this

theorem lbl_ne_run (n : Nat) : lbl n ≠ "qm_entry" := by
  intro h
  have := congrArg (fun s => s.toList.head?) h
  simp [lbl, String.toList_append] at this

/-- `L` is a list of distinct labels `lbl j`, each with `P j`. -/
def Fresh (P : Nat → Prop) (L : List Label) : Prop :=
  L.Nodup ∧ ∀ l ∈ L, ∃ j, P j ∧ l = lbl j

theorem Fresh.nil (P : Nat → Prop) : Fresh P [] := by simp [Fresh]

theorem Fresh.single (n : Nat) : Fresh (fun j => j = n) [lbl n] := by simp [Fresh]

theorem Fresh.mono {P Q : Nat → Prop} {L : List Label} (h : Fresh P L) (hPQ : ∀ j, P j → Q j) :
    Fresh Q L :=
  ⟨h.1, fun l hl => (h.2 l hl).imp fun j hj => ⟨hPQ j hj.1, hj.2⟩⟩

theorem Fresh.append {P Q : Nat → Prop} {L₁ L₂ : List Label} (h₁ : Fresh P L₁) (h₂ : Fresh Q L₂)
    (hPQ : ∀ j, P j → Q j → False) : Fresh (fun j => P j ∨ Q j) (L₁ ++ L₂) := by
  refine ⟨List.nodup_append.mpr ⟨h₁.1, h₂.1, ?_⟩, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := h₁.2 x hx
    obtain ⟨j, hj, rfl⟩ := h₂.2 y hy
    exact hPQ i hi (lbl_injective hxy ▸ hj)
  · intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact (h₁.2 l hl).imp fun j hj => ⟨Or.inl hj.1, hj.2⟩
    · exact (h₂.2 l hl).imp fun j hj => ⟨Or.inr hj.1, hj.2⟩

theorem ins_labels (is : List Instr) : (ins is).filterMap labelOf = [] := by
  simp [ins, List.filterMap_map, labelOf]

/-- The labels of `code c n` are distinct and numbered from `n` up to the next free number. -/
theorem code_labels (c : Stmt) (n : Nat) :
    n ≤ (code c n).2 ∧
      Fresh (fun j => n ≤ j ∧ j < (code c n).2) ((code c n).1.filterMap labelOf) := by
  induction c generalizing n with
  | skip => exact ⟨Nat.le_refl _, Fresh.nil _⟩
  | ins i => exact ⟨Nat.le_refl _, by simp only [code, ins_labels]; exact Fresh.nil _⟩
  | fail => exact ⟨Nat.le_refl _, Fresh.nil _⟩
  | seq a b iha ihb =>
    obtain ⟨ha1, ha2⟩ := iha n
    obtain ⟨hb1, hb2⟩ := ihb (code a n).2
    simp only [code, List.filterMap_append]
    exact ⟨by omega, (ha2.append hb2 (fun j _ _ => by omega)).mono fun j _ => by omega⟩
  | ite c t e iht ihe =>
    obtain ⟨ht1, ht2⟩ := iht (n + 2)
    obtain ⟨he1, he2⟩ := ihe (code t (n + 2)).2
    simp only [code, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, labelOf, bcc,
      b, ins_labels, List.nil_append]
    exact ⟨by omega, ((((ht2.append (Fresh.single n) (fun j _ _ => by omega)).append he2
      (fun j _ _ => by omega)).append (Fresh.single (n + 1)) (fun j _ _ => by omega))).mono
      fun j _ => by omega⟩
  | loop c body ihb =>
    obtain ⟨hb1, hb2⟩ := ihb (n + 2)
    simp only [code, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, labelOf, bcc,
      b, ins_labels, List.append_nil]
    exact ⟨by omega, (((Fresh.single n).append hb2 (fun j _ _ => by omega)).append
      (Fresh.single (n + 1)) (fun j _ _ => by omega)).mono fun j _ => by omega⟩

/-- Every label of a compiled program is distinct. -/
theorem program_labels_nodup (body onFail : Stmt) :
    ((program body onFail).filterMap labelOf).Nodup := by
  obtain ⟨-, hb⟩ := code_labels body 0
  obtain ⟨-, hf⟩ := code_labels onFail (code body 0).2
  simp only [program, ret, movRetI, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil, labelOf, List.append_nil]
  rw [List.nodup_append, List.nodup_append, List.nodup_append]
  refine ⟨⟨⟨by simp, hb.1, ?_⟩, by simp, ?_⟩, hf.1, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨j, -, rfl⟩ := hb.2 y hy
    simp only [List.mem_singleton] at hx
    exact lbl_ne_run j (hx ▸ hxy).symm
  · intro x hx y hy hxy
    simp only [List.mem_singleton] at hy
    subst hy
    rcases List.mem_append.mp hx with hx | hx
    · simp only [List.mem_singleton] at hx
      subst hx
      exact absurd hxy (by decide)
    · obtain ⟨j, -, rfl⟩ := hb.2 x hx
      exact lbl_ne_fail j hxy
  · intro x hx y hy hxy
    obtain ⟨j, hj, rfl⟩ := hf.2 y hy
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · simp only [List.mem_singleton] at hx
        exact lbl_ne_run j (hx ▸ hxy).symm
      · obtain ⟨i, hi, rfl⟩ := hb.2 x hx
        have := lbl_injective hxy
        omega
    · simp only [List.mem_singleton] at hx
      exact lbl_ne_fail j (hx ▸ hxy).symm

end

end NativeArm.Compile
