module

public import LeanVM.Guest.Mode.Abs

/-!
# The mode walk by windows

A long function's walk is checked in windows: the kernel runs window `[a, b)` from the cut at `a`
(`runCode` over `winCode`, its code read past whole chunks first) and the walk ends it at the cut at
`b` (`cutAt`), whose paths and pending edges the next window starts from. `WinsOk` says each window
goes through and the last leaves no edge pending; `walk_of_wins` chains them into the whole walk.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

/-- A function's code from offset `a`, its whole chunks before skipped first. -/
def codeAt (cs : List (List OffsetInstruction)) (a : ℕ) : List OffsetInstruction :=
  (cs.drop (a / chunkSize)).flatten.drop (a % chunkSize)

/-- A function's code from offset `a` to `b`. -/
def winCode (cs : List (List OffsetInstruction)) (a b : ℕ) : List OffsetInstruction :=
  (codeAt cs a).take (b - a)

/-- The walk of the rest of the code, from offset `a` with the paths and pending edges `S`, goes
through and leaves no edge pending. -/
noncomputable def runRest (E : Env) (F : Fun) (code : List OffsetInstruction) (a : ℕ)
    (S : List Abs × Pend) : Bool :=
  match runCode E F code a S.1 S.2 with
  | some (_, pend) => pend.isEmpty
  | none => false

/-- The paths and pending edges at the cut at `b`. -/
noncomputable def cutOf (F : Fun) (b : ℕ) : List Abs × Pend := (F.cuts.get b).getD ([], [])

/-- The windows from offset `a`, each ending at a cut `b`: each goes through from the paths and
pending edges `Sa` into the cut's, and the last leaves no edge pending. -/
def WinsOk (E : Env) (F : Fun) (cs : List (List OffsetInstruction)) (n : ℕ) :
    ℕ → List Abs × Pend → List ℕ → Prop
  | a, Sa, [] => runRest E F (codeAt cs a) a Sa = true
  | a, Sa, b :: ws => a < b ∧ b ≤ n ∧ (F.cuts.get b).isSome = true ∧
      (runCode E F (winCode cs a b) a Sa.1 Sa.2).isSome = true ∧ WinsOk E F cs n b (cutOf F b) ws

end

public section

theorem forceAll_eq {β : Type} : ∀ (l : List Abs) (k : List Abs → β), forceAll l k = k l
  | [], _ => rfl
  | A :: l, k => by
    show A.force (fun A ↦ forceAll l fun l ↦ k (A :: l)) = _
    obtain ⟨w, v, nz, hv, h, r, lt, pr, xs, p⟩ := A
    simp only [Abs.force, Trie.seq_eq]
    exact forceAll_eq l _

theorem runCode_cons (E : Env) (F : Fun) (ins : OffsetInstruction) (l : List OffsetInstruction) (i : ℕ)
    (c : List Abs) (p : Pend) : runCode E F (ins :: l) i c p =
      (stepAll E F i ins (joinAt i c p).1 (joinAt i c p).2).bind fun q ↦
        (cutAt F (i + 1) q.1 q.2).bind fun r ↦ runCode E F l (i + 1) r.1 r.2 := by
  simp only [runCode, forceAll_eq]
  rcases stepAll E F i ins (joinAt i c p).1 (joinAt i c p).2 with _ | ⟨cur, pend⟩
  · rfl
  · dsimp only [Option.bind_some]
    rcases cutAt F (i + 1) cur pend with _ | ⟨c', p'⟩ <;> rfl

theorem runCode_append (E : Env) (F : Fun) : ∀ (l₁ l₂ : List OffsetInstruction) (i : ℕ) (c : List Abs)
    (p : Pend), runCode E F (l₁ ++ l₂) i c p =
      (runCode E F l₁ i c p).bind fun s ↦ runCode E F l₂ (i + l₁.length) s.1 s.2
  | [], _, _, _, _ => by simp [runCode]
  | ins :: l₁, l₂, i, c, p => by
    rw [List.cons_append, runCode_cons, runCode_cons]
    rcases stepAll E F i ins (joinAt i c p).1 (joinAt i c p).2 with _ | ⟨cur, pend⟩
    · rfl
    · simp only [Option.bind_some]
      rcases cutAt F (i + 1) cur pend with _ | ⟨c', p'⟩
      · rfl
      · simp only [Option.bind_some]
        rw [runCode_append E F l₁ l₂ (i + 1) c' p', List.length_cons, Nat.add_assoc, Nat.add_comm 1]

theorem runCode_end (E : Env) (F : Fun) {S : List Abs × Pend} :
    ∀ (l : List OffsetInstruction) (i : ℕ) (c : List Abs) (p : Pend) {X : List Abs × Pend}, l ≠ [] →
      F.cuts.get (i + l.length) = some S → runCode E F l i c p = some X → X = S
  | [], _, _, _, _, h, _, _ => absurd rfl h
  | ins :: l, i, c, p, X, _, hS, h => by
    rw [runCode_cons] at h
    rcases e1 : stepAll E F i ins (joinAt i c p).1 (joinAt i c p).2 with _ | ⟨cur, pend⟩
    · rw [e1] at h; cases h
    rw [e1, Option.bind_some] at h
    rcases e2 : cutAt F (i + 1) cur pend with _ | ⟨c', p'⟩
    · rw [e2] at h; cases h
    rw [e2, Option.bind_some] at h
    by_cases hl : l = []
    · subst hl
      simp only [runCode, Option.some.injEq] at h
      subst h
      simp only [List.length_cons, List.length_nil, Nat.zero_add] at hS
      unfold cutAt at e2
      rw [hS] at e2
      dsimp only at e2
      split at e2
      · exact (Option.some.inj e2).symm
      · cases e2
    · exact runCode_end E F l (i + 1) c' p' hl (by
        rw [List.length_cons] at hS; rwa [Nat.add_assoc, Nat.add_comm 1]) h

theorem flatten_length_of_chunked {C : ℕ} : ∀ {cs : List (List OffsetInstruction)} {n : ℕ},
    chunked C cs n = true → cs.flatten.length = n
  | [], n, h => by unfold chunked at h; simp only [beq_iff_eq] at h; simp [h]
  | c :: cs, n, h => by
    unfold chunked at h
    split_ifs at h with hn
    · simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h
      obtain ⟨rfl, hl⟩ := h
      simp [hl]
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hl, h'⟩ := h
      rw [List.flatten_cons, List.length_append, hl, flatten_length_of_chunked h']
      omega

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

theorem codeAt_eq {cs : List (List OffsetInstruction)} {n : ℕ} (hc : chunked chunkSize cs n = true)
    (a : ℕ) : codeAt cs a = cs.flatten.drop a :=
  (drop_flatten_chunked (by decide) hc a).symm

/-- The windows from `a` go through: so does the walk of the rest of the code. -/
theorem runRest_of_wins {E : Env} {F : Fun} {cs : List (List OffsetInstruction)} {n : ℕ}
    (hc : chunked chunkSize cs n = true) :
    ∀ (ws : List ℕ) (a : ℕ) (Sa : List Abs × Pend), WinsOk E F cs n a Sa ws →
      runRest E F (cs.flatten.drop a) a Sa = true
  | [], a, Sa, h => by
    unfold WinsOk at h
    rwa [codeAt_eq hc] at h
  | b :: ws, a, Sa, h => by
    obtain ⟨hab, hbn, hS, hw, hws⟩ := h
    have hS : F.cuts.get b = some (cutOf F b) := by
      unfold cutOf
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hS
      rw [hx]; rfl
    have ih := runRest_of_wins hc ws b _ hws
    have hlen := flatten_length_of_chunked hc
    have hsplit : cs.flatten.drop a = (cs.flatten.drop a).take (b - a) ++ cs.flatten.drop b := by
      conv_lhs => rw [← List.take_append_drop (b - a) (cs.flatten.drop a)]
      rw [List.drop_drop, Nat.add_sub_cancel' hab.le]
    have hwl : ((cs.flatten.drop a).take (b - a)).length = b - a := by
      simp only [List.length_take, List.length_drop]; omega
    unfold winCode at hw
    rw [codeAt_eq hc] at hw
    obtain ⟨X, hX⟩ := Option.isSome_iff_exists.mp hw
    have hne : (cs.flatten.drop a).take (b - a) ≠ [] := by
      intro h0; rw [h0] at hwl; simp at hwl; omega
    have hXS := runCode_end E F _ a Sa.1 Sa.2 hne (by rw [hwl, Nat.add_sub_cancel' hab.le]; exact hS) hX
    unfold runRest at ih ⊢
    rw [hsplit, runCode_append, hX, Option.bind_some, hwl, Nat.add_sub_cancel' hab.le, hXS]
    exact ih

/-- **The walk from the windows**: each goes through, chained at the cuts. -/
theorem walk_of_wins {E : Env} {F : Fun} {cs : List (List OffsetInstruction)} {n : ℕ}
    (hc : chunked chunkSize cs n = true) (ws : List ℕ)
    (h : WinsOk E F cs n 0 ([entryAbs E F.sig], []) ws) : walk E F cs.flatten = true := by
  have := runRest_of_wins hc ws 0 _ h
  rw [List.drop_zero] at this
  exact this

end

end LeanVM.Guest.Mode
