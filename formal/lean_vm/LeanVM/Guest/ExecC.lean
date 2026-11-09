/-
  LeanVM.Guest.ExecC

  The executor's input read past whole code chunks, for the kernel.
-/

module

public import LeanVM.Guest.Glob
public import LeanVM.Guest.FunctionTable

/-!
# A window's code, by chunks

`execWin` reads a window's code as `f.code.drop a`, a structural walk over the whole flattened
code before the window, which the kernel pays for at every evaluation. `execWinC` skips whole
chunks first (`codeFrom`); for every guest function the two agree (`execWinC_eq`, the functions
being well chunked).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Guest LeanVM.Guest.Check LeanVM.Guest.Exec

@[expose] public section

/-- A function's code from offset `a`, its whole chunks before skipped first. -/
def codeFrom (f : CompiledFunction) (a : ℕ) : List OffsetInstruction :=
  (f.chunks.drop (a / chunkSize)).flatten.drop (a % chunkSize)

/-- `execWin`, the window's code read by `codeFrom`. -/
noncomputable def execWinC (F : Facts) (f : CompiledFunction) (a : ℕ) (env : List (ℕ × Sym))
    (b : ℕ) :
    Result :=
  pass F f.entryPc f.instructionCount ((codeFrom f a).take (b - a)) a (some (Cur.init a (envOf
      env))) [] [] 0

/-- `execWinS`, the window's code read by `codeFrom`. -/
noncomputable def execWinCS (F : Facts) (f : CompiledFunction) (a : ℕ) (env : List (ℕ × Sym))
    (seeds : List ℕ) (b : ℕ) : Result :=
  pass F f.entryPc f.instructionCount ((codeFrom f a).take (b - a)) a (some (Cur.init a (envOf
      env))) (seeds.map fun t ↦ (t, envOf env)) [] 0

theorem drop_flatten_chunked {C : ℕ} (hC : 0 < C) : ∀ {cs : List (List OffsetInstruction)} {n : ℕ},
    chunked C cs n = true → ∀ a, cs.flatten.drop a = (cs.drop (a / C)).flatten.drop (a % C)
  | [], _, _, a => by simp
  | c :: cs, n, h, a => by
    by_cases ha : a < C
    · rw [Nat.div_eq_of_lt ha, Nat.mod_eq_of_lt ha, List.drop_zero]
    · have hq : a / C = (a - C) / C + 1 := Nat.div_eq_sub_div hC (by omega)
      have hr : a % C = (a - C) % C := Nat.mod_eq_sub_mod (by omega)
      unfold chunked at h
      split_ifs at h with hn
      · simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h
        obtain ⟨rfl, hl⟩ := h
        rw [hq, List.drop_succ_cons, List.drop_nil, List.flatten_nil, List.drop_nil, List.flatten_cons,
          List.flatten_nil, List.append_nil, List.drop_eq_nil_of_le (by omega)]
      · simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨hl, h'⟩ := h
        rw [hq, hr, List.drop_succ_cons, List.flatten_cons, List.drop_append,
          List.drop_eq_nil_of_le (by omega), List.nil_append, hl]
        exact drop_flatten_chunked hC h' (a - C)

private theorem nth_past {α : Type} : ∀ {l : List α} {n : ℕ} {d : α}, l.length ≤ n →
    listElementOrDefault l n d = d
  | [], _, _, _ => rfl
  | _ :: _, 0, _, h => absurd h (by simp)
  | _ :: as, n + 1, _, h => nth_past (l := as) (by simpa using h)

theorem fnOf_wellChunked (j : ℕ) : chunked chunkSize (fnOf j).chunks (fnOf j).instructionCount =
    true := by
  by_cases h : j < Data.functions.length
  · unfold fnOf
    rw [show listElementOrDefault Data.functions j default = Data.functions[j] from
      Option.some.inj ((nth_eq_getElem? default h).symm.trans (List.getElem?_eq_getElem h))]
    exact List.all_eq_true.mp functions_wellChunked _ (List.getElem_mem h)
  · unfold fnOf
    rw [nth_past (by omega)]
    rfl

theorem execWinC_eq (j : ℕ) (F : Facts) (a : ℕ) (env : List (ℕ × Sym)) (b : ℕ) :
    execWinC F (fnOf j) a env b = execWin F (fnOf j) a env b := by
  unfold execWinC execWin codeFrom CompiledFunction.code
  rw [← drop_flatten_chunked (by decide) (fnOf_wellChunked j)]

theorem execWinCS_nil (F : Facts) (f : CompiledFunction) (a : ℕ) (env : List (ℕ × Sym)) (b : ℕ) :
    execWinCS F f a env [] b = execWinC F f a env b := rfl

theorem execWinCS_eq (j : ℕ) (F : Facts) (a : ℕ) (env : List (ℕ × Sym)) (seeds : List ℕ) (b : ℕ) :
    execWinCS F (fnOf j) a env seeds b = execWinS F (fnOf j) a env seeds b := by
  unfold execWinCS execWinS codeFrom CompiledFunction.code
  rw [← drop_flatten_chunked (by decide) (fnOf_wellChunked j)]

end
end LeanVM.Guest.B2C
