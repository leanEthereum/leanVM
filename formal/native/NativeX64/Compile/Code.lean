module

public import NativeX64.Instr
public import Std.Data.String.ToNat

/-!
# The compiler from statements to Kraken's x86-64

`Compile.code` lays a statement out as Kraken directives with local labels `.L<n>` drawn from a
counter, branching with `cmp` or `test` and a conditional jump on the negated condition code.
`Compile.program` puts the body after the entry label `qm_entry` and the failure handler after
`qm_fail`, each ending with `ret`. Every label of a compiled program is distinct
(`Compile.program_labels_nodup`), so that Kraken's label lookup, which takes the first match, finds
each label where the compiler put it.
-/

open Native hiding Reg64 Width

namespace NativeX64.Compile

@[expose] public section

/-- The local label `.L<n>`. -/
def lbl (n : Nat) : Label := ".L" ++ Nat.repr n

/-- `jmp l`, in the form Kraken's AT&T printer prints as `jmp l`. -/
def jmp (l : Label) : Directive :=
  .instr (op64 (.jmp (.rel (.sub (.label l) .after_current_instruction))))

/-- `j<cc> l`. -/
def jcc (cc : CondCode) (l : Label) : Directive := .instr (op64 (.jcc cc l))

/-- `ret`. -/
def ret : Directive := .instr (op64 .ret)

/-- The code of a statement and the next free label number, its labels numbered from `n`. -/
def code : Stmt → Nat → Program × Nat
  | .skip, n => ([], n)
  | .ins i, n => ([.instr i.toInstr], n)
  | .seq a b, n =>
    let ca := code a n
    let cb := code b ca.2
    (ca.1 ++ cb.1, cb.2)
  | .ite c t e, n =>
    let ct := code t (n + 2)
    let ce := code e ct.2
    ([.instr c.toInstr, jcc (CondCode.not c.cc) (lbl n)] ++ ct.1 ++
      [jmp (lbl (n + 1)), .label (lbl n)] ++ ce.1 ++ [.label (lbl (n + 1))], ce.2)
  | .loop c b, n =>
    let cb := code b (n + 2)
    ([.label (lbl n), .instr c.toInstr, jcc (CondCode.not c.cc) (lbl (n + 1))] ++ cb.1 ++
      [jmp (lbl n), .label (lbl (n + 1))], cb.2)
  | .fail, n => ([jmp "qm_fail"], n)

/-- A program's code: `body` from the entry `qm_entry` to a `ret`, then `onFail` from the
failure exit `qm_fail` to a `ret`. -/
def program (body onFail : Stmt) : Program :=
  let cb := code body 0
  [.label "qm_entry"] ++ cb.1 ++ [ret] ++ [.label "qm_fail"] ++ (code onFail cb.2).1 ++
    [ret]

/-- The index of the `ret` that ends the body. -/
def retOkIndex (body : Stmt) : Nat := 1 + (code body 0).1.length

/-- The index of the `ret` that ends the failure handler. -/
def retFailIndex (body onFail : Stmt) : Nat :=
  3 + (code body 0).1.length + (code onFail (code body 0).2).1.length

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
  simp only [List.getElem?_singleton, List.length_append, List.length_cons, List.length_nil]
  split
  · rfl
  · omega

theorem program_retFail (body onFail : Stmt) :
    (program body onFail)[retFailIndex body onFail]? = some ret := by
  simp only [program, retFailIndex]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.getElem?_singleton, List.length_append, List.length_cons, List.length_nil]
  split
  · rfl
  · omega

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

/-- The labels of `code c n` are distinct and numbered from `n` up to the next free number. -/
theorem code_labels (c : Stmt) (n : Nat) :
    n ≤ (code c n).2 ∧
      Fresh (fun j => n ≤ j ∧ j < (code c n).2) ((code c n).1.filterMap labelOf) := by
  induction c generalizing n with
  | skip => exact ⟨Nat.le_refl _, Fresh.nil _⟩
  | ins i => exact ⟨Nat.le_refl _, Fresh.nil _⟩
  | fail => exact ⟨Nat.le_refl _, Fresh.nil _⟩
  | seq a b iha ihb =>
    obtain ⟨ha1, ha2⟩ := iha n
    obtain ⟨hb1, hb2⟩ := ihb (code a n).2
    simp only [code, List.filterMap_append]
    exact ⟨by omega, (ha2.append hb2 (fun j _ _ => by omega)).mono fun j _ => by omega⟩
  | ite c t e iht ihe =>
    obtain ⟨ht1, ht2⟩ := iht (n + 2)
    obtain ⟨he1, he2⟩ := ihe (code t (n + 2)).2
    simp only [code, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, labelOf, jcc,
      jmp, List.nil_append]
    exact ⟨by omega, ((((ht2.append (Fresh.single n) (fun j _ _ => by omega)).append he2
      (fun j _ _ => by omega)).append (Fresh.single (n + 1)) (fun j _ _ => by omega))).mono
      fun j _ => by omega⟩
  | loop c b ihb =>
    obtain ⟨hb1, hb2⟩ := ihb (n + 2)
    simp only [code, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, labelOf, jcc,
      jmp]
    exact ⟨by omega, (((Fresh.single n).append hb2 (fun j _ _ => by omega)).append
      (Fresh.single (n + 1)) (fun j _ _ => by omega)).mono fun j _ => by omega⟩

/-- Every label of a compiled program is distinct. -/
theorem program_labels_nodup (body onFail : Stmt) :
    ((program body onFail).filterMap labelOf).Nodup := by
  obtain ⟨-, hb⟩ := code_labels body 0
  obtain ⟨-, hf⟩ := code_labels onFail (code body 0).2
  simp only [program, ret, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, labelOf,
    List.append_nil]
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

end NativeX64.Compile
