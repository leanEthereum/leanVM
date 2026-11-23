/-
  LeanVM.Guest.CoreMode.Fam.LoopDefs

  The checks behind the loops' termination facts: each loop helper of its shape, and each loop's
  entry from outside starting its counter at `g^0` or `g^1`.
-/

module

public import LeanVM.Guest.Memory.StaticCut
public import LeanVM.Guest.Memory.Family

/-!
# The loops' checks

`termChk fn`: a loop helper (`Fn.loop`) is named `__loop…` and has its shape (`loopShape`) at the
end `endOfFn` finds (a parameter, or a constant `g^e`, `e < 256`); and every call of a loop helper
in the function, but a loop helper's own tail call, passes as counter a value set to `g^0` or `g^1`
by a top-level `SET` before it, in its block or an enclosing one (`entL`, checked by ranges of
statements with `entL_drop`). The kernel checks it over
the core IR by ranges (`RangeOk`, `CoreMode/Gen/LoopCheck*.lean`).
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- A loop helper's name. -/
def isLoopName (f : String) : Bool := f.toList.take 6 == "__loop".toList

/-- The values set to `g^0` or `g^1`, `s` added. -/
def constsAdd (cs : List V) : Stmt → List V
  | .atom (.const x w) => if constOk w 0 || constOk w 1 then x :: cs else cs
  | _ => cs

/-- A call's counter among `cs`, if the callee is a loop helper. -/
def argOk (cs : List V) (f : String) (args : List V) : Bool :=
  !isLoopName f || match args with
    | a :: _ => decide (a ∈ cs)
    | [] => false

mutual
/-- **Every loop entry of a block starts its counter at `g^0` or `g^1`**: its counter among `cs`,
the values set so before it, in its block or an enclosing one; with `nr`, no `ret` either. -/
def entL (nr : Bool) (cs : List V) : List Stmt → Bool
  | [] => true
  | s :: ss => entS nr cs s && entL nr (constsAdd cs s) ss

/-- `entL` for one statement. -/
def entS (nr : Bool) (cs : List V) : Stmt → Bool
  | .ite _ z n => entL nr cs z && entL nr cs n
  | .match_ _ arms => entA nr cs arms
  | .call f args _ => argOk cs f args
  | .callIf _ f args => argOk cs f args
  | .dispatch _ fs _ _ => fs.all fun f => !isLoopName f
  | .ret _ => !nr
  | .atom _ => true

/-- `entL` for a `match`'s arms. -/
def entA (nr : Bool) (cs : List V) : List (List Stmt) → Bool
  | [] => true
  | a :: as => entL nr cs a && entA nr cs as
end

theorem constsAdd_mono {cs cs' : List V} (h : ∀ v ∈ cs, v ∈ cs') (s : Stmt) :
    ∀ v ∈ constsAdd cs s, v ∈ constsAdd cs' s := by
  intro v hv
  cases s with
  | atom a =>
    cases a with
    | const x w =>
      simp only [constsAdd] at hv ⊢
      split_ifs at hv ⊢
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h v hv)
      · exact h v hv
    | _ => exact h v hv
  | _ => exact h v hv

mutual
theorem entL_mono {nr : Bool} : ∀ {cs cs' : List V} (l : List Stmt), (∀ v ∈ cs, v ∈ cs') →
    entL nr cs l = true → entL nr cs' l = true
  | _, _, [], _, _ => rfl
  | _, _, s :: ss, h, he => by
    simp only [entL, Bool.and_eq_true] at he ⊢
    exact ⟨entS_mono s h he.1, entL_mono ss (constsAdd_mono h s) he.2⟩

theorem entS_mono {nr : Bool} : ∀ {cs cs' : List V} (s : Stmt), (∀ v ∈ cs, v ∈ cs') →
    entS nr cs s = true → entS nr cs' s = true
  | _, _, .ite _ z n, h, he => by
    simp only [entS, Bool.and_eq_true] at he ⊢
    exact ⟨entL_mono z h he.1, entL_mono n h he.2⟩
  | _, _, .match_ _ arms, h, he => entA_mono arms h he
  | _, _, .call f args _, h, he => by
    simp only [entS, argOk, Bool.or_eq_true, Bool.not_eq_true'] at he ⊢
    rcases he with he | he
    · exact Or.inl he
    · right; split at he
      · simp only [decide_eq_true_eq] at he ⊢; exact h _ he
      · cases he
  | _, _, .callIf _ f args, h, he => by
    simp only [entS, argOk, Bool.or_eq_true, Bool.not_eq_true'] at he ⊢
    rcases he with he | he
    · exact Or.inl he
    · right; split at he
      · simp only [decide_eq_true_eq] at he ⊢; exact h _ he
      · cases he
  | _, _, .dispatch .., _, he => he
  | _, _, .atom _, _, _ => rfl
  | _, _, .ret _, _, he => he

theorem entA_mono {nr : Bool} : ∀ {cs cs' : List V} (as : List (List Stmt)), (∀ v ∈ cs, v ∈ cs') →
    entA nr cs as = true → entA nr cs' as = true
  | _, _, [], _, _ => rfl
  | _, _, a :: as, h, he => by
    simp only [entA, Bool.and_eq_true] at he ⊢
    exact ⟨entL_mono a h he.1, entA_mono as h he.2⟩
end

/-- Two blocks checked apart, the second from nothing, are checked together. -/
theorem entL_append {nr : Bool} {cs : List V} : ∀ (l1 l2 : List Stmt), entL nr cs l1 = true →
    entL nr [] l2 = true → entL nr cs (l1 ++ l2) = true
  | [], l2, _, h2 => entL_mono l2 (fun _ h ↦ absurd h List.not_mem_nil) h2
  | s :: l1, l2, h1, h2 => by
    simp only [List.cons_append, entL, Bool.and_eq_true] at h1 ⊢
    exact ⟨h1.1, entL_append (cs := constsAdd cs s) l1 l2 h1.2 h2⟩

/-- A block checked by ranges of its statements. -/
theorem entL_drop {nr : Bool} {l : List Stmt} {a n : ℕ} (h : entL nr [] ((l.drop a).take n) = true)
    (h' : entL nr [] (l.drop (a + n)) = true) : entL nr [] (l.drop a) = true := by
  rw [← List.take_append_drop n (l.drop a), List.drop_drop]
  exact entL_append _ _ h (by simpa only [Nat.add_comm] using h')

theorem entL_end {nr : Bool} {l : List Stmt} {a : ℕ} (h : l.length ≤ a) : entL nr [] (l.drop a) = true := by
  rw [List.drop_eq_nil_of_le h]; rfl

/-- A loop helper's end: its parameter (`none`), or the first constant `g^e`, `e < 256`, its tail
passes at (`loopTail`). -/
def endOfFn (fn : Fn) : Option (Option ℕ) :=
  if (loopTail fn none).isSome then some none
  else ((List.range 256).find? fun e => (loopTail fn (some e)).isSome).map some

/-- The block a function's check walks: a loop helper's body without its tail call. -/
def bodyOf (fn : Fn) : List Stmt := if fn.loop then loopBody fn else fn.body

/-- **A function's check**: a loop helper named and of its tail's shape, its body without `ret`;
every loop entry but a loop helper's tail call starting at `g^0` or `g^1`. -/
def termChk (fn : Fn) : Bool :=
  (!fn.loop || isLoopName fn.name && (endOfFn fn).isSome) && entL fn.loop [] (bodyOf fn)

theorem termChk_of {fn : Fn} (h : fn.loop = true → isLoopName fn.name = true ∧ (endOfFn fn).isSome = true)
    (he : entL fn.loop [] (bodyOf fn) = true) : termChk fn = true := by
  unfold termChk
  rw [he, Bool.and_true]
  cases hl : fn.loop
  · rfl
  · obtain ⟨h1, h2⟩ := h hl
    rw [h1, h2]; rfl

mutual
theorem entL_noRet : ∀ {cs : List V} (l : List Stmt), entL true cs l = true → Memory.Stmt.noRetListS l = true
  | _, [], _ => rfl
  | _, s :: ss, h => by
    simp only [entL, Bool.and_eq_true] at h
    simp only [Memory.Stmt.noRetListS, Bool.and_eq_true]
    exact ⟨entS_noRet s h.1, entL_noRet ss h.2⟩

theorem entS_noRet : ∀ {cs : List V} (s : Stmt), entS true cs s = true → Memory.Stmt.noRet s = true
  | _, .ite _ z n, h => by
    simp only [entS, Bool.and_eq_true] at h
    simp only [Memory.Stmt.noRet, Bool.and_eq_true]
    exact ⟨entL_noRet z h.1, entL_noRet n h.2⟩
  | _, .match_ _ arms, h => entA_noRet arms h
  | _, .ret _, h => by simp [entS] at h
  | _, .atom _, _ => rfl
  | _, .call .., _ => rfl
  | _, .callIf .., _ => rfl
  | _, .dispatch .., _ => rfl

theorem entA_noRet : ∀ {cs : List V} (as : List (List Stmt)), entA true cs as = true →
    Memory.Stmt.noRetArms as = true
  | _, [], _ => rfl
  | _, a :: as, h => by
    simp only [entA, Bool.and_eq_true] at h
    simp only [Memory.Stmt.noRetArms, Bool.and_eq_true]
    exact ⟨entL_noRet a h.1, entA_noRet as h.2⟩
end

end

end LeanVM.Guest.Res
