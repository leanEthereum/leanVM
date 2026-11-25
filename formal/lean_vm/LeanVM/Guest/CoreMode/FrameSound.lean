module

public import LeanVM.Guest.CoreMode.FramePass
public import LeanVM.Guest.Mode.Step

/-!
# The frame walk is sound

`frame_step`: at an offset of a function whose frame walk accepts its code (`FrameAcc`), an
executor state at the offset (`AtF`), fine and on the reference run, has its step's obligations
(`StepOk`): each hint's needs (given its agreement with the reference once its inputs are written),
the instruction's modedness (given the reference's part, `RefOk`), what falls through at the next
offset, and a taken `JUMP` handed over by kind (`JumpOut`): a jump in the frame to an offset the
walk names, a return with the signature's return cells written, `main`'s halt, a loop's tail call
into a frame whose entry facts hold and whose header is this frame's, or a call into a callee whose
entry facts hold, its frame's header this frame's return point, the walk resumable there once the
callee has written its return cells. Its hypotheses about the reference, all of the image at the
frame and none about time, are the composition's: the residual divisors (`hnz`), the oracle's heap
cells (`hO`), and where a jump through a cell lands (`htgt`).

`atF_entry`: the entry facts give the walk's state at offset `0`.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec (Hint St Ctx Fine Moves StepOk HintOk refMem maxCells runOp Mem gpow_inj
  Mem.get_of_written OpModed)
open LeanVM.Guest.Mode (Names written_of_get written_mono names_inj Reads opOfOff RefOk HintIn)

@[expose] public section

variable {κ : ℕ} {img : MemoryImage κ}

/-! ## The entry -/

/-- **What a function's frame walk assumes at entry**: its entry cells and self frame pointer
cell written, the latter holding the frame's address in the reference. -/
structure EntryFr (img : MemoryImage κ) (G : Mode.Sig) (s : St) : Prop where
  w : ∀ o ∈ G.entry, s.mem.written (s.fp + o) = true
  self : ∀ o, G.self = some o → s.mem.written (s.fp + o) = true ∧
    Rd img s.fp o = some (ofK (g ^ s.fp))

theorem get_foldl_set_unit : ∀ (l : List ℕ) (t : Exec.Trie Unit) {n : ℕ},
    (l.foldl (fun t o ↦ t.set () Exec.envDepth o) t).get n = some () → n ∈ l ∨ t.get n = some ()
  | [], _, _, h => Or.inr h
  | o :: l, t, n, h => by
    rw [List.foldl_cons] at h
    rcases get_foldl_set_unit l _ h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases get_set_unit (t := t) (d := Exec.envDepth) (n := o) h with rfl | h
      · exact Or.inl List.mem_cons_self
      · exact Or.inr h

theorem get_envOf : ∀ (l : List (ℕ × Exec.Sym)) (t : Exec.Trie Exec.Sym) {n : ℕ} {v : Exec.Sym},
    (l.foldl (fun t p ↦ t.set p.2 Exec.envDepth p.1) t).get n = some v → (n, v) ∈ l ∨ t.get n = some v
  | [], _, _, _, h => Or.inr h
  | p :: l, t, n, v, h => by
    rw [List.foldl_cons] at h
    rcases get_envOf l _ h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rcases Exec.Trie.get_set h with ⟨rfl, rfl⟩ | h
      · exact Or.inl List.mem_cons_self
      · exact Or.inr h

theorem envOk_mem {Fn : FFun} (h : envOk Fn = true) {n : ℕ} {v : Exec.Sym} (hm : (n, v) ∈ Fn.F.env) :
    v = .fpg 0 ∧ Fn.sig.self = some n := by
  have := List.all_eq_true.mp h _ hm
  simp only at this
  rcases v with _ | e | e <;> rcases hs : Fn.sig.self with _ | o <;> simp_all
  rcases e with _ | e <;> simp_all

/-- **The entry state holds** where the entry facts do. -/
theorem entryF_holds {Fn : FFun} (henv : envOk Fn = true) {s : St} (h : EntryFr img Fn.sig s) :
    FHolds img s (entryF Fn) := by
  refine ⟨⟨stHolds_init fun n v hv ↦ ?_, fun _ h ↦ by simp [entryF, Bits.has] at h, fun _ _ _ h ↦ by simp [entryF] at h,
    fun _ _ h ↦ by simp [entryF] at h, fun _ _ h ↦ by simp [entryF] at h⟩,
    ⟨fun o ho ↦ ?_, fun _ _ _ h ↦ by simp [entryF] at h⟩⟩
  · rcases get_envOf Fn.F.env .nil hv with hm | hm
    · obtain ⟨rfl, hso⟩ := envOk_mem henv hm
      obtain ⟨-, hr⟩ := h.self _ hso
      show Rd img s.fp n = _
      rw [hr]
      simp [Exec.Sym.val, addressOfIndex]
    · simp at hm
  · have : o ∈ (match Fn.sig.self with
        | some o => o :: Fn.sig.entry
        | none => Fn.sig.entry) := by
      exact Bits.has_ofList ho
    split at this
    · rename_i so hso
      rcases List.mem_cons.mp this with rfl | hm
      · exact (h.self _ hso).1
      · exact h.w o hm
    · exact h.w o this


/-! ## One path's step, by cases -/

/-- What one path's step at offset `i` is: its hints, its residuals, and its instruction, a `JUMP`
falling through or taken as its exit says. -/
theorem offF_cases {Fn : FFun} {i : ℕ} {hs : List Hint} {A : FSt} {ins : OffsetInstruction}
    {pend pend' : FPend} {cur' : Option FSt} (h : offF Fn i hs A ins pend = some (cur', pend')) :
    ∃ A1, stepHintsF A hs = some A1 ∧
      (((∀ c d f, ins ≠ .jump c d f) ∧ ∃ A3, stepF Fn.Ob Fn.S i (addNzs A1 ((Fn.nzr.get i).getD [])) ins = some A3 ∧
          cur' = some (execF Fn.F (Fn.entry + i) A3 ins)) ∨
       (∃ c d f, ins = .jump c d f ∧
          (addNzs A1 ((Fn.nzr.get i).getD [])).hasW c = true ∧
          (addNzs A1 ((Fn.nzr.get i).getD [])).hasW d = true ∧
          (addNzs A1 ((Fn.nzr.get i).getD [])).hasW f = true ∧
          ((Exec.isZero ((addNzs A1 ((Fn.nzr.get i).getD [])).st.env.get c) = true ∧
              cur' = some (addNzs A1 ((Fn.nzr.get i).getD []))) ∨
           (Exec.isZero ((addNzs A1 ((Fn.nzr.get i).getD [])).st.env.get c) = false ∧
              jumpF Fn i (addNzs A1 ((Fn.nzr.get i).getD []))
                (Exec.jumpExit Fn.F Fn.entry Fn.len i (addNzs A1 ((Fn.nzr.get i).getD [])).st d f) pend = some pend' ∧
              (Exec.isNonzero ((addNzs A1 ((Fn.nzr.get i).getD [])).st.env.get c) = false →
                cur' = some (addNzs A1 ((Fn.nzr.get i).getD []))))))) := by
  unfold offF at h
  rcases e1 : stepHintsF A hs with _ | A1
  · rw [e1] at h; cases h
  rw [e1] at h
  dsimp only at h
  refine ⟨A1, rfl, ?_⟩
  generalize addNzs A1 ((Fn.nzr.get i).getD []) = A2 at h ⊢
  cases ins with
  | jump c d f =>
    refine Or.inr ⟨c, d, f, rfl, ?_⟩
    simp only at h
    split_ifs at h with hw
    simp only [Bool.and_eq_true] at hw
    refine ⟨hw.1.1, hw.1.2, hw.2, ?_⟩
    rw [Exec.optSeq_eq] at h
    split_ifs at h with hz hn
    · cases h; exact Or.inl ⟨hz, rfl⟩
    · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      exact Or.inr ⟨by simpa using hz, hp, fun h' ↦ by rw [hn] at h'; cases h'⟩
    · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      exact Or.inr ⟨by simpa using hz, hp, fun _ ↦ rfl⟩
  | xor a b c =>
    refine Or.inl ⟨fun _ _ _ ↦ nofun, ?_⟩
    obtain ⟨A3, h3, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact ⟨A3, h3, rfl⟩
  | mul a b c =>
    refine Or.inl ⟨fun _ _ _ ↦ nofun, ?_⟩
    obtain ⟨A3, h3, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact ⟨A3, h3, rfl⟩
  | set a b c =>
    refine Or.inl ⟨fun _ _ _ ↦ nofun, ?_⟩
    obtain ⟨A3, h3, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact ⟨A3, h3, rfl⟩
  | deref a b c m =>
    refine Or.inl ⟨fun _ _ _ ↦ nofun, ?_⟩
    obtain ⟨A3, h3, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact ⟨A3, h3, rfl⟩
  | keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd outCells =>
    refine Or.inl ⟨fun _ _ _ ↦ nofun, ?_⟩
    obtain ⟨A3, h3, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact ⟨A3, h3, rfl⟩

/-! ## The hints -/

theorem readT_has {w : ℕ} {hs : List Hint} {o : ℕ} (h : (readT w hs).get o = some ()) : Bits.has w o = true :=
  (get_foldl_set_unit _ .nil h).elim (fun hm ↦ (List.mem_filter.mp hm).2) (by simp)

theorem hintAbs_holds {s : St} {A : FSt} (h : FWr s A) (hs : List Hint) :
    Mode.Holds s (hintAbs (readT A.w hs)) where
  w o ho := h.w o (readT_has ho)
  v _ _ hx := by simp [hintAbs] at hx
  nz _ hx := by simp [hintAbs] at hx
  hv _ hx := by simp [hintAbs] at hx
  h _ hx := by simp [hintAbs] at hx
  r _ hx := by simp [hintAbs] at hx
  lt _ hx := by simp [hintAbs] at hx
  pr _ hx := by simp [hintAbs] at hx
  xs _ _ _ hx := by simp [hintAbs] at hx
  p _ hx := by simp [hintAbs] at hx
  c _ hx := by simp [hintAbs] at hx

/-- **The hints in order**: each one's needs at the state its predecessors reach, once its inputs
are written, and the instruction's obligations after them. -/
theorem stepOk_hintsAt {C : Ctx} {M : ℕ → E} {Inv : St → Prop} {op : Prover.Exec.Op} :
    ∀ (hs : List Hint) (s : St) (A A' : Mode.Abs), Fine M s → Mode.Holds s A → Mode.stepHints A hs = some A' →
      (∀ pre h post, hs = pre ++ h :: post → ∀ s1, pre.foldlM (Prover.Exec.runHint C) s = .ok s1 →
        Moves M s s1 → HintIn s1 h → HintOk C M s1 h) →
      (∀ s1, hs.foldlM (Prover.Exec.runHint C) s = .ok s1 → Moves M s s1 → Mode.Holds s1 A' →
        StepOk C M Inv op [] s1) → StepOk C M Inv op hs s
  | [], s, A, A', hs, hA, h, _, hk => by
    cases h
    exact hk s rfl (Mode.Moves.refl' hs) hA
  | x :: xs, s, A, A', hs, hA, h, hh, hk => by
    simp only [Mode.stepHints, Option.bind_eq_some_iff] at h
    obtain ⟨B, hB, h⟩ := h
    have hin := (Mode.stepHint_sound (C := C) (s' := s) ⟨hs.agree.wf, hs.dl⟩ hs.fp hs.agree.used hA hB).1
    refine ⟨hh [] x xs rfl s rfl (Mode.Moves.refl' hs) hin, fun s1 e1 m1 ↦ ?_⟩
    have hrun := (Mode.stepHint_sound (C := C) (s' := s1) ⟨hs.agree.wf, hs.dl⟩ hs.fp hs.agree.used hA hB).2
    exact stepOk_hintsAt xs s1 B A' m1.fine (hrun e1 m1.fine.agree.used) h
      (fun pre y post hp s2 e2 m2 hi ↦ hh (x :: pre) y post (by rw [hp]; rfl) s2
        (by rw [List.foldlM_cons, e1]; exact e2) (m1.trans m2) hi)
      (fun s2 e2 m2 hB2 ↦ hk s2 (by rw [List.foldlM_cons, e1]; exact e2) (m1.trans m2) hB2)

/-- Stack runs written by the mode walk: what its state held, and the run's cells. -/
theorem writeRun_w {A : Mode.Abs} {base len o : ℕ}
    (h : A.w.get o = some () ∨ (base ≤ o ∧ o < base + len ∧ o < Bits.lim)) :
    (Mode.writeRun A (some base, none) 0 len none).w.get o = some () := by
  simp only [Mode.writeRun, Mode.foldlA_eq]
  induction len with
  | zero => exact h.elim id fun h ↦ absurd h.2.1 (by omega)
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Mode.Abs.addW]
    rcases h with h | ⟨h1, h2, h3⟩
    · exact get_set_unit_of (Or.inl (ih (Or.inl h)))
    · by_cases he : o = base + 0 + n
      · exact get_set_unit_of (Or.inr ⟨he, he ▸ h3⟩)
      · exact get_set_unit_of (Or.inl (ih (Or.inr ⟨h1, by omega, h3⟩)))

/-- **Stack runs at once** (`wsRuns`): the mode walk steps the same hints, and every cell the runs add
it writes. -/
theorem wsRuns_spec {wa : ℕ} : ∀ (hs : List Hint) (w w' : ℕ) (A : Mode.Abs), wsRuns w hs = some w' →
    (∀ o, Bits.has w o = true → Bits.has wa o = true ∨ A.w.get o = some ()) →
    ∃ B, Mode.stepHints A hs = some B ∧ ∀ o, Bits.has w' o = true → Bits.has wa o = true ∨ B.w.get o = some ()
  | [], _, _, A, h, hw => by cases h; exact ⟨A, rfl, hw⟩
  | x :: hs, w, w', A, h, hw => by
    cases x with
    | witnessStack _ base len =>
      obtain ⟨B, hB, hB'⟩ := wsRuns_spec hs _ w' (Mode.writeRun A (some base, none) 0 len none) h fun o ho ↦ by
        rcases Bits.has_addRun ho with ho | ho
        · exact (hw o ho).imp_right fun h ↦ writeRun_w (Or.inl h)
        · exact Or.inr (writeRun_w (Or.inr ho))
      exact ⟨B, by simpa [Mode.stepHints, Mode.stepHint] using hB, hB'⟩
    | _ => simp [wsRuns] at h

/-- **The hints**: each one's needs, once its inputs are written, and the instruction's obligations
after them, from the state after the hints. -/
theorem stepOk_hintsF {C : Ctx} {M : ℕ → E} {Inv : St → Prop} {op : Prover.Exec.Op} {s : St} {A A1 : FSt}
    {hs : List Hint} (hf : Fine M s) (hA : FHolds img s A) (h : stepHintsF A hs = some A1)
    (hh : ∀ pre h post, hs = pre ++ h :: post → ∀ s1, pre.foldlM (Prover.Exec.runHint C) s = .ok s1 →
      Moves M s s1 → HintIn s1 h → HintOk C M s1 h)
    (hk : ∀ s1, hs.foldlM (Prover.Exec.runHint C) s = .ok s1 → Moves M s s1 → FHolds img s1 A1 →
      StepOk C M Inv op [] s1) : StepOk C M Inv op hs s := by
  cases hs with
  | nil =>
    cases h
    exact hk s rfl (Mode.Moves.refl' hf) hA
  | cons x xs =>
    simp only [stepHintsF] at h
    -- the state after the hints, and what of it the mode walk's state `B` holds
    obtain ⟨B, hB, w', rfl, hw⟩ : ∃ B, Mode.stepHints (hintAbs (readT A.w (x :: xs))) (x :: xs) = some B ∧
        ∃ w', A1 = { A with w := w' } ∧ ∀ o, Bits.has w' o = true → Bits.has A.w o = true ∨ B.w.get o = some () := by
      rcases e : wsRuns A.w (x :: xs) with _ | w' <;> rw [e] at h
      · obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.mp h
        refine ⟨B, hB, _, rfl, fun o ho ↦ ?_⟩
        simp only [Bits.has, Nat.testBit_or, Bool.or_eq_true] at ho
        exact ho.imp id Bits.get_of_has_ofTrie
      · cases h
        exact (wsRuns_spec _ _ _ _ e fun _ ↦ .inl).imp fun B h ↦ ⟨h.1, _, rfl, h.2⟩
    exact stepOk_hintsAt (x :: xs) s _ B hf (hintAbs_holds hA.2 (x :: xs)) hB hh fun s1 e1 hm hB1 ↦
      hk s1 e1 hm ⟨by rw [hm.fp]; exact ⟨hA.1.st, hA.1.nz, hA.1.hs, hA.1.cp, hA.1.one⟩,
        ⟨fun o ho ↦ (hw o ho).elim ((hA.2.mono hm.le hm.fp).w o) (hB1.w o), (hA.2.mono hm.le hm.fp).hq⟩⟩

theorem addNzs_holds {s : St} : ∀ {A : FSt} {os : List ℕ}, FHolds img s A →
    (∀ o ∈ os, ∃ v, Rd img s.fp o = some v ∧ v ≠ 0) → FHolds img s (addNzs A os)
  | _, [], h, _ => h
  | A, o :: os, h, hn => by
    show FHolds img s (addNzs (A.addNz o) os)
    exact addNzs_holds ⟨h.1.addNz (hn o List.mem_cons_self), h.2.addNz o⟩
      fun o' ho' ↦ hn o' (List.mem_cons_of_mem _ ho')


/-! ## Jumps: what `Exec`'s kinds say -/

theorem jumpKind_spec (F : Exec.Facts) (entry len i : ℕ) (st : Exec.St) (od of : ℕ) :
    (od = 0 ∧ of = 1 ∧ Exec.jumpKind F entry len i st od of = (.ret, [])) ∨
    (∃ t, Exec.jumpKind F entry len i st od of = (.next t, [t]) ∧ i < t ∧ t < len) ∨
    (∃ pt rr, (Exec.jumpKind F entry len i st od of).1 = .call pt of rr ∧
      pt = Exec.tgtOf (st.env.get od) od ∧
      ((Exec.jumpKind F entry len i st od of).2 = [] ∨
        ∃ t, (Exec.jumpKind F entry len i st od of).2 = [t] ∧ rr = entry + t ∧ i < t ∧ t < len)) ∨
    (∃ pt ft, (Exec.jumpKind F entry len i st od of).1 = .jump pt ft ∧ pt = Exec.tgtOf (st.env.get od) od ∧
      ft = Exec.tgtOf (st.env.get of) of) := by
  unfold Exec.jumpKind
  split_ifs with h01
  · exact Or.inl ⟨h01.1, h01.2, rfl⟩
  rw [Exec.Tgt.seq_eq, Exec.Tgt.seq_eq]
  split_ifs with hself
  · split
    · rename_i e he
      split_ifs with hl
      · exact Or.inr (Or.inl ⟨e - entry, rfl, by omega, by omega⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl, rfl, rfl⟩))
    · rename_i o he
      exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl, rfl, rfl⟩))
    · rename_i e he
      exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl, rfl, rfl⟩))
  · split
    · rename_i q hq
      obtain rfl := Exec.tgtOf_cell hq
      split
      · refine Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl, ?_⟩))
        split_ifs with hr
        · exact Or.inr ⟨_, rfl, by omega, by omega, by omega⟩
        · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl, rfl, rfl⟩))
    · rename_i ft hft
      exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl, rfl, rfl⟩))

theorem jumpKind_next {F : Exec.Facts} {entry len i : ℕ} {st : Exec.St} {od of t : ℕ} {succ : List ℕ}
    (h : Exec.jumpKind F entry len i st od of = (.next t, succ)) : succ = [t] ∧ i < t ∧ t < len := by
  rcases jumpKind_spec F entry len i st od of with ⟨-, -, h'⟩ | ⟨t', h', h1, h2⟩ | ⟨pt, rr, h', -⟩ | ⟨pt, ft, h', -⟩
  · rw [h] at h'; cases h'
  · rw [h] at h'
    simp only [Prod.mk.injEq, Exec.Kind.next.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    exact ⟨rfl, h1, h2⟩
  · rw [h] at h'; cases h'
  · rw [h] at h'; cases h'

theorem jumpKind_call {F : Exec.Facts} {entry len i : ℕ} {st : Exec.St} {od of t : ℕ} {pt : Exec.Tgt}
    {q r : ℕ} (h : (Exec.jumpKind F entry len i st od of).1 = .call pt q r)
    (hs : (Exec.jumpKind F entry len i st od of).2 = [t]) : q = of ∧ r = entry + t ∧ i < t ∧ t < len := by
  rcases jumpKind_spec F entry len i st od of with ⟨-, -, h'⟩ | ⟨t', h', -, -⟩ | ⟨pt', rr, h', -, h2⟩ |
      ⟨pt', ft, h', -⟩
  · rw [h'] at h; cases h
  · rw [h'] at h; cases h
  · rw [h'] at h
    simp only [Exec.Kind.call.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    rcases h2 with h2 | ⟨t', h2, h3, h4, h5⟩
    · rw [h2] at hs; cases hs
    · rw [h2] at hs
      simp only [List.cons.injEq, and_true] at hs
      subst hs
      exact ⟨rfl, h3, h4, h5⟩
  · rw [h'] at h; cases h

theorem jumpKind_cell {F : Exec.Facts} {entry len i : ℕ} {st : Exec.St} {od of : ℕ} {o : ℕ} {ft : Exec.Tgt}
    (h : (Exec.jumpKind F entry len i st od of).1 = .jump (.cell o) ft) : o = od := by
  rcases jumpKind_spec F entry len i st od of with ⟨-, -, h'⟩ | ⟨t', h', -, -⟩ | ⟨pt', rr, h', -, -⟩ |
      ⟨pt', ft', h', hpt, -⟩
  · rw [h'] at h; cases h
  · rw [h'] at h; cases h
  · rw [h'] at h; cases h
  · rw [h'] at h
    simp only [Exec.Kind.jump.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Exec.tgtOf_cell hpt.symm

theorem jumpKind_call_cell {F : Exec.Facts} {entry len i : ℕ} {st : Exec.St} {od of : ℕ} {o q r : ℕ}
    (h : (Exec.jumpKind F entry len i st od of).1 = .call (.cell o) q r) : o = od := by
  rcases jumpKind_spec F entry len i st od of with ⟨-, -, h'⟩ | ⟨t', h', -, -⟩ | ⟨pt', rr, h', hpt, -⟩ |
      ⟨pt', ft', h', -⟩
  · rw [h'] at h; cases h
  · rw [h'] at h; cases h
  · rw [h'] at h
    simp only [Exec.Kind.call.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Exec.tgtOf_cell hpt.symm
  · rw [h'] at h; cases h

/-! ## Words -/

theorem rd_shift (fp e o : ℕ) : Rd img (fp + e) o = Rd img fp (e + o) := by
  simp only [Rd, addressOfIndex, pow_add, mul_assoc]

theorem written_lt {M : ℕ → E} {s : St} (hs : Fine M s) {x : ℕ} (h : s.mem.written x = true) :
    x < maxCells := by
  obtain ⟨v, hv⟩ := Mem.get_of_written h
  exact lt_of_lt_of_le (hs.agree.wf.get_lt hv) hs.agree.used


/-! ## The step -/

/-- An instruction's frame operands are below `2^28`. -/
def SmallOps : OffsetInstruction → Prop
  | .xor a b c | .mul a b c | .jump a b c | .deref a b c _ => a < 2 ^ 28 ∧ b < 2 ^ 28 ∧ c < 2 ^ 28
  | _ => True

/-- **Where a taken jump goes**, and what holds there. -/
inductive JumpOut (img : MemoryImage κ) (Fn : FFun) (code : List OffsetInstruction) (rj : Prop)
    (s1 s' : St) : Prop
  /-- A jump in the frame, to an offset the walk names. -/
  | local (t : ℕ) : ¬ rj → s'.fp = s1.fp → s'.pc = Fn.entry + t → AtF img Fn code t s' → JumpOut img Fn code rj s1 s'
  /-- A return: the caller's registers, the signature's return cells written, the jump a return's. -/
  | ret : retRegs img (g ^ s1.fp) = some ⟨g ^ s'.pc, g ^ s'.fp⟩ →
      (∀ o ∈ Fn.sig.ret, s1.mem.written (s1.fp + o) = true) → rj → JumpOut img Fn code rj s1 s'
  /-- `main`'s halt. -/
  | halt : ¬ rj → Fn.F.fpOne = true → s'.pc = Fn.halt → s'.fp = s1.fp → JumpOut img Fn code rj s1 s'
  /-- A loop's tail call into frame `fp + e`: its entry facts, its header this frame's, nothing
  returned in its frame. -/
  | tail (e : ℕ) : ¬ rj → s'.pc = Fn.entry → s'.fp = s1.fp + e → EntryFr img Fn.sig s' →
      Rd img s'.fp 0 = Rd img s1.fp 0 → Rd img s'.fp 1 = Rd img s1.fp 1 → Fn.sig.ret = [] →
      JumpOut img Fn code rj s1 s'
  /-- A call into callee `G` at offset `t`'s return point: its entry facts, its frame's header this
  frame's return point, and the walk at `t` once the callee has written its return cells. -/
  | call (G : Mode.Sig) (t : ℕ) : ¬ rj → t < Fn.len → Fn.sigs.get s'.pc = some G → EntryFr img G s' →
      retRegs img (g ^ s'.fp) = some ⟨g ^ (Fn.entry + t), g ^ s1.fp⟩ →
      (∀ s'', Fine (refMem img) s'' → s''.fp = s1.fp → s''.pc = Fn.entry + t → s1.mem ≤ s''.mem →
        (∀ o ∈ G.ret, s''.mem.written (s'.fp + o) = true) → AtF img Fn code t s'') →
      JumpOut img Fn code rj s1 s'

/-- Where a jump through a cell lands, of the reference: a table call at one of its callees, a
table jump at one of its arms. -/
def TgtOk (img : MemoryImage κ) (Fn : FFun) (code : List OffsetInstruction) (i fp : ℕ) : Prop :=
  ∀ c d f, code[i]? = some (.jump c d f) → ∀ cv dv, Rd img fp c = some cv → cv ≠ 0 →
    Rd img fp d = some dv → ∀ pc, pc < pcLim → dv.limb 0 = g ^ pc → ∀ k, Fn.tgt.get i = some k →
      (∀ pcs, Fn.calls.get k = some pcs → pc ∈ pcs) ∧
      (∀ ts, Fn.arms.get k = some ts → ∃ t ∈ ts, pc = Fn.entry + t)


/-! ## Taken jumps -/

theorem sigsAt_mem {sigs : Exec.Trie Mode.Sig} : ∀ {pcs : List ℕ} {Gs : List Mode.Sig},
    sigsAt sigs pcs = some Gs → ∀ pc ∈ pcs, ∃ G ∈ Gs, sigs.get pc = some G
  | [], _, _, _, h => absurd h List.not_mem_nil
  | pc :: pcs, Gs, h, x, hx => by
    simp only [sigsAt] at h
    split at h
    · rename_i G Gs' hG hGs
      cases h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨G, List.mem_cons_self .., hG⟩
      · obtain ⟨G', hG', h'⟩ := sigsAt_mem hGs x hx
        exact ⟨G', List.mem_cons_of_mem _ hG', h'⟩
    · cases h

theorem retsOf_mem : ∀ {Gs : List Mode.Sig} {o : ℕ}, o ∈ retsOf Gs → ∀ G ∈ Gs, o ∈ G.ret
  | [], _, h, _, _ => absurd h List.not_mem_nil
  | G :: Gs, o, h, G', hG' => by
    simp only [retsOf, List.mem_filter, List.all_eq_true, List.contains_iff_mem] at h
    rcases List.mem_cons.mp hG' with rfl | hG'
    · exact h.1
    · simpa using h.2 G' hG'

theorem addRets_holds {s : St} {q : ℕ} : ∀ {A : FSt} {os : List ℕ}, FHolds img s A →
    (∀ o ∈ os, o < hqLim → ∃ p x, s.mem.get (s.fp + q) = some p ∧ Names (p * ofK (g ^ o)) x ∧
      s.mem.written x = true) → FHolds img s (addRets A q os)
  | _, [], h, _ => h
  | A, o :: os, h, hw => by
    show FHolds img s (addRets (A.addQ q o) q os)
    exact addRets_holds ⟨h.1.addQ q o, h.2.addQ (hw o List.mem_cons_self)⟩
      fun o' ho' ↦ hw o' (List.mem_cons_of_mem _ ho')

theorem gpow_lt_inj {a b : ℕ} (ha : a < 2 ^ 62) (hb : b < 2 ^ 62) (h : (g : K) ^ a = g ^ b) : a = b :=
  gpow_inj (by omega) (by omega) h

/-- **What a taken jump the walk accepts is**, from where the reference goes. -/
theorem exit_out (hκ : κ ≤ 28) {Fn : FFun} {code : List OffsetInstruction} {i : ℕ}
    {s1 s' : St} {A B : FSt} {ts : List ℕ} {kind : Exec.Kind} {succ : List ℕ} {d f : ℕ}
    (hs1 : Fine (refMem img) s1) (hle : s1.mem ≤ s'.mem)
    (hend : Fn.entry + Fn.len ≤ 2 ^ 30) (hpcs : s'.pc < 2 ^ 30) (hfps : s'.fp < maxCells)
    (hfsm : f < 2 ^ 28) (hA : FHolds img s1 A) (hmain : Fn.F.fpOne = true → s1.fp = 0)
    (hfget : ∃ vf, s1.mem.get (s1.fp + f) = some vf ∧ Rd img s1.fp f = some vf)
    (hjk : Exec.jumpKind Fn.F Fn.entry Fn.len i A.st d f = (kind, succ))
    (hx : exitF Fn i A ⟨kind, A.st.env, succ⟩ = some (ts, B))
    (hregs : kind.Regs img (g ^ s1.fp) Fn.entry ⟨g ^ s'.pc, g ^ s'.fp⟩) (hextra : kind.Extra img (g ^ s1.fp))
    {dv : E} (hdv : Rd img s1.fp d = some dv)
    (htgt : ∀ k, Fn.tgt.get i = some k → (∀ pcs, Fn.calls.get k = some pcs → s'.pc ∈ pcs) ∧
      (∀ ts, Fn.arms.get k = some ts → ∃ t ∈ ts, s'.pc = Fn.entry + t))
    (cov : ∀ s j, j ∈ ts → FHolds img s B → AtF img Fn code j s) {rj : Prop} (hrj : rj → d = 0 ∧ f = 1)
    (hrj' : d = 0 → f = 1 → rj) : JumpOut img Fn code rj s1 s' := by
  have hnr : kind ≠ .ret → ¬ rj := fun hk h ↦ by
    obtain ⟨rfl, rfl⟩ := hrj h
    unfold Exec.jumpKind at hjk
    simp only [and_self, ↓reduceIte, Prod.mk.injEq] at hjk
    exact hk hjk.1.symm
  have hfp1 := hs1.fp
  unfold maxCells at hfp1 hfps
  unfold exitF at hx
  simp only at hx
  cases kind with
  | next t =>
    cases hx
    obtain ⟨rfl, hit, htl⟩ := jumpKind_next hjk
    simp only [Exec.Kind.Regs, Registers.mk.injEq, addressOfIndex] at hregs
    have h1 := gpow_lt_inj (by omega) (by omega) hregs.1
    have h2 := gpow_lt_inj (by omega) (by omega) hregs.2
    exact .local t (hnr nofun) h2 h1 (cov s' t List.mem_cons_self (hA.mono hle h2))
  | ret =>
    split_ifs at hx with hr
    cases hx
    have h01 : d = 0 ∧ f = 1 := by
      rcases jumpKind_spec Fn.F Fn.entry Fn.len i A.st d f with ⟨h0, h1, -⟩ | ⟨t, h', -⟩ | ⟨pt, rr, h', -⟩ |
          ⟨pt, ft, h', -⟩
      · exact ⟨h0, h1⟩
      all_goals simp [hjk] at h'
    exact .ret hregs (fun o ho ↦ hA.2.w o (List.all_eq_true.mp hr o ho)) (hrj' h01.1 h01.2)
  | call pt q r =>
    obtain ⟨p, a, hp, hpK, hpt, hra⟩ := hregs
    simp only [Registers.mk.injEq] at hra
    obtain ⟨hpa, hfa⟩ := hra
    replace hx : callF Fn i A q succ pt = some (ts, B) := hx
    unfold callF at hx
    rcases hpcs' : callPcs Fn i pt with _ | pcs
    · rw [hpcs'] at hx; cases hx
    rw [hpcs'] at hx
    simp only [Option.bind_some] at hx
    rcases hsg : sigsAt Fn.sigs pcs with _ | _ | ⟨G, Gs⟩
    · rw [hsg] at hx; cases hx
    · rw [hsg] at hx; cases hx
    rw [hsg] at hx
    simp only at hx
    split_ifs at hx with hall
    rcases succ with _ | ⟨t, _ | _⟩
    · cases hx
    swap
    · cases hx
    simp only [Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    obtain ⟨rfl, rfl, hit, htl⟩ := jumpKind_call (by rw [hjk]) (by rw [hjk])
    have hmem : s'.pc ∈ pcs := by
      cases pt with
      | gp e =>
        simp only [callPcs] at hpcs'
        split_ifs at hpcs' with he
        cases hpcs'
        have := gpow_lt_inj (by omega) (by unfold pcLim at he; omega) (hpa.trans hpt)
        rw [this]; exact List.mem_singleton_self _
      | cell o =>
        obtain rfl := jumpKind_call_cell (by rw [hjk])
        simp only [callPcs] at hpcs'
        obtain ⟨k, hk, hc⟩ := Option.bind_eq_some_iff.mp hpcs'
        exact (htgt k hk).1 pcs hc
      | fpg e => simp [callPcs] at hpcs'
    obtain ⟨G', hG', hsig⟩ := sigsAt_mem hsg _ hmem
    have hok := List.all_eq_true.mp hall G' hG'
    unfold calleeOk at hok
    simp only [Bool.and_eq_true, List.all_eq_true] at hok
    -- the callee frame
    have hfpp : p.limb 0 = g ^ s'.fp := hfa.symm
    have hq : ∀ o, A.hasQ q o = true → s1.mem.written (s'.fp + o) = true := fun o ho ↦ by
      unfold FSt.hasQ at ho
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ho
      obtain ⟨p', x, hp', hx', hw⟩ := hA.2.hq q o ho.1 (has_iff.mp ho.2)
      obtain rfl := rd_get hκ hs1 hfsm hp hp'
      unfold hqLim at ho
      rw [← names_gpow hfpp hx' (by omega)]
      exact hw
    have hentry : EntryFr img G' s' := by
      refine ⟨fun o ho ↦ written_mono hle (hq o (hok.1 o ho)), fun o hso ↦ ?_⟩
      have hs2 := hok.2
      rw [hso] at hs2
      simp only [Bool.and_eq_true] at hs2
      refine ⟨written_mono hle (hq o hs2.1), ?_⟩
      have hs := hs2.2
      unfold FSt.hasS at hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨p'', hp'', hpK'', hr''⟩ := hA.1.hs q o hs.1 (has_iff.mp hs.2)
      replace hp'' : img.read (g ^ s1.fp * addressOfIndex q) = some p'' := hp''
      rw [hp] at hp''; cases hp''
      show img.read (g ^ s'.fp * addressOfIndex o) = some _
      rw [← hfpp, hr'', Exec.inK_eq hpK, limb_ofK]
      simp
    obtain ⟨p3, hp3, hrr⟩ := hextra
    rw [hp] at hp3; cases hp3
    refine .call G' t (hnr nofun) htl hsig hentry (by rw [← hfpp]; exact hrr) fun s'' hs'' hfp'' hpc'' hle'' hret ↦ ?_
    refine cov s'' t List.mem_cons_self (addRets_holds ((hA.mono hle'' hfp'')) fun o ho _ ↦ ?_)
    obtain ⟨vf, hvf, hrf⟩ := hfget
    change img.read (g ^ s1.fp * addressOfIndex q) = some vf at hrf
    rw [hp] at hrf; cases hrf
    have hw := hret o (retsOf_mem ho G' hG')
    refine ⟨p, s'.fp + o, by rw [hfp'']; exact hle''.get _ _ hvf, ⟨?_, written_lt hs'' hw⟩, hw⟩
    rw [Mode.limb_mul_ofK, hfpp, ← pow_add]
  | jump pt ft =>
    obtain ⟨a, b, hpt, hft, hrab⟩ := hregs
    simp only [Registers.mk.injEq] at hrab
    obtain ⟨hpa, hfb⟩ := hrab
    replace hx : jumpExF Fn i A pt ft = some (ts, B) := hx
    unfold jumpExF at hx
    by_cases hself : Fn.F.self ft = true
    · rw [ite_eq_left hself] at hx
      have hb := Exec.self_is (L := img) (fun h1 ↦ by rw [hmain h1, pow_zero]) hself hft
      have hfp' : s'.fp = s1.fp := gpow_lt_inj (by omega) (by omega) (hfb.trans hb)
      cases pt with
      | gp e =>
        simp only at hx
        split_ifs at hx with hh
        simp only [Option.some.injEq, Prod.mk.injEq] at hx
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hh
        obtain ⟨⟨h1, rfl⟩, he⟩ := hh
        unfold pcLim at he
        exact .halt (hnr nofun) h1 (gpow_lt_inj (by omega) (by omega) (hpa.trans hpt)) hfp'
      | cell o =>
        obtain rfl := jumpKind_cell (by rw [hjk])
        simp only at hx
        rcases hk : Fn.tgt.get i with _ | k
        · rw [hk] at hx; cases hx
        rw [hk] at hx
        obtain ⟨ts', hts', he⟩ := Option.map_eq_some_iff.mp hx
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨v, hv, -, rfl⟩ := hpt
        replace hv : Rd img s1.fp o = some v := hv
        rw [hdv] at hv; cases hv
        obtain ⟨t, ht, hpt'⟩ := (htgt k hk).2 _ hts'
        exact .local t (hnr nofun) hfp' hpt' (cov s' t ht (hA.mono hle hfp'))
      | fpg e => simp at hx
    · rw [ite_eq_right hself] at hx
      rcases ft with e0 | e | o <;> rcases pt with e' | e1 | o' <;> simp only at hx <;> try cases hx
      split_ifs at hx with hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hh
      obtain ⟨⟨rfl, he⟩, htail⟩ := hh
      unfold pcLim at he
      have hpc' : s'.pc = Fn.entry := gpow_lt_inj (by omega) (by omega) (hpa.trans hpt)
      have hfp' : s'.fp = s1.fp + e := gpow_lt_inj (by omega) (by omega)
        (by rw [hfb, hft, addressOfIndex, ← pow_add])
      unfold tailOk at htail
      simp only [Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at htail
      obtain ⟨⟨⟨⟨hent, hsf⟩, h0⟩, h1⟩, hret⟩ := htail
      have hcp : ∀ t c, cpIs A t c = true → e ≤ t → Rd img s'.fp (t - e) = Rd img s1.fp c := by
        intro t c hc hte
        unfold cpIs at hc
        rcases hct : A.cp.get t with _ | c'
        · rw [hct] at hc; cases hc
        rw [hct] at hc
        obtain rfl := beq_iff_eq.mp hc
        obtain ⟨v, hv1, hv2⟩ := hA.1.cp t c' hct
        rw [hfp', rd_shift, show e + (t - e) = t by omega, hv1, hv2]
      refine .tail e (hnr nofun) hpc' hfp' ⟨fun o ho ↦ ?_, fun o hso ↦ ?_⟩ ?_ ?_ hret
      · have := hA.2.w _ (hent o ho)
        rw [hfp', Nat.add_assoc]
        exact written_mono hle this
      · rw [hso] at hsf
        unfold selfAt at hsf
        simp only [Bool.and_eq_true] at hsf
        obtain ⟨hw, hc⟩ := hsf
        refine ⟨by rw [hfp', Nat.add_assoc]; exact written_mono hle (hA.2.w _ hw), ?_⟩
        have hfpgAt : ∀ t, fpgAt A e t = true → Rd img s1.fp t = some (ofK (g ^ s1.fp * addressOfIndex e)) := by
          intro t ht
          unfold fpgAt at ht
          rcases hce : A.st.env.get t with _ | (_ | e'' | e'')
          all_goals rw [hce] at ht
          all_goals simp only [Bool.false_eq_true] at ht
          obtain rfl := beq_iff_eq.mp ht
          exact hA.1.st.1 t _ hce
        have hval : Rd img s1.fp (e + o) = some (ofK (g ^ s1.fp * addressOfIndex e)) := by
          rcases Bool.or_eq_true _ _ |>.mp hc with hc | hc
          · exact hfpgAt _ hc
          rcases hct : A.cp.get (e + o) with _ | c
          · rw [hct] at hc; cases hc
          rw [hct] at hc
          obtain ⟨v, h1, h2⟩ := hA.1.cp _ c hct
          rw [h1, ← h2, hfpgAt c hc]
        rw [hfp', rd_shift, hval]
        simp [addressOfIndex, pow_add]
      · have := hcp e 0 h0 le_rfl
        rwa [Nat.sub_self] at this
      · have := hcp (e + 1) 1 h1 (by omega)
        rwa [show e + 1 - e = 1 by omega] at this

/-! ## The step -/

theorem isZero_rd {fp : ℕ} {A : FSt} (hv : FVal img fp A) {c : ℕ} (h : Exec.isZero (A.st.env.get c) = true)
    {v : E} (hr : Rd img fp c = some v) : v = 0 := by
  have := hv.st.1 c _ (Exec.isZero_eq h)
  change Rd img fp c = _ at this
  rw [hr] at this
  exact (Option.some.inj this).trans rfl

theorem isNonzero_rd {fp : ℕ} {A : FSt} (hv : FVal img fp A) {c : ℕ} (h : Exec.isNonzero (A.st.env.get c) = true)
    {v : E} (hr : Rd img fp c = some v) : v ≠ 0 := by
  obtain ⟨w, hw, hne⟩ := Exec.isNonzero_val h (g ^ fp)
  have := hv.st.1 c w hw
  change Rd img fp c = _ at this
  rw [hr] at this
  rw [Option.some.inj this]; exact hne

/-- A `DEREF` of mode `cell` at an offset of `S` has written its heap cell. -/
def StoreW (Fn : FFun) (code : List OffsetInstruction) (i : ℕ) (s : St) : Prop :=
  ∀ a o c, code[i]? = some (.deref a o c .cell) → has Fn.S i = true →
    ∃ p x, s.mem.get (s.fp + a) = some p ∧ Names (p * ofK (g ^ o)) x ∧ s.mem.written x = true

/-- A taken `JUMP` at offset `i`: its target and frame cells name the next registers. -/
def JumpTaken (C : Ctx) (code : List OffsetInstruction) (i : ℕ) (s1 s' : St) : Prop :=
  ∃ c d f, code[i]? = some (.jump c d f) ∧ s1.mem.get (s1.fp + d) = some (ofK (g ^ s'.pc)) ∧
    s1.mem.get (s1.fp + f) = some (ofK (g ^ s'.fp)) ∧ s'.pc < C.ops.size

/-- **A step at an offset the frame walk reaches** has its obligations: the hints' and the
instruction's needs, what falls through at the next offset, and a taken `JUMP` by kind. -/
theorem frame_step {prog : LeanIsaProgram} (hκ : κ ≤ 28) {C : Ctx} {Inv : St → Prop} {Fn : FFun}
    {code : List OffsetInstruction} (har : armsOk Fn = true) (hacc : FrameAcc Fn code)
    (hpows : Fn.F.pows.Ok) (hend : Fn.entry + Fn.len ≤ 2 ^ 30)
    (hsz : C.ops.size ≤ 2 ^ 30)
    (hops : ∀ i (hi : i < code.length), C.ops[Fn.entry + i]? = some (opOfOff code[i]))
    (hhints : ∀ i < code.length, (C.hints[Fn.entry + i]?).getD [] = Mode.hintsAt Fn.hints (Fn.entry + i))
    (hfetch : Exec.Fetches prog Fn.entry code)
    (hsmall : ∀ i (hi : i < code.length), SmallOps code[i])
    {s : St} {i : ℕ} (hi : i < code.length) (hpc : s.pc = Fn.entry + i)
    (hat : AtF img Fn code i s) (hs : Fine (refMem img) s) {k : ℕ}
    (hsafe : Safe prog img k ⟨addressOfIndex s.pc, g ^ s.fp⟩)
    (hmain : Fn.F.fpOne = true → s.fp = 0)
    (hhint : ∀ pre h post, Mode.hintsAt Fn.hints (Fn.entry + i) = pre ++ h :: post → ∀ s1,
      pre.foldlM (Prover.Exec.runHint C) s = .ok s1 → Moves (refMem img) s s1 → HintIn s1 h →
      HintOk C (refMem img) s1 h)
    (hnz : ∀ o ∈ (Fn.nzr.get i).getD [], ∃ v, Rd img s.fp o = some v ∧ v ≠ 0)
    (hO : has Fn.O i = true → ∀ s1, (Mode.hintsAt Fn.hints (Fn.entry + i)).foldlM (Prover.Exec.runHint C) s = .ok s1 →
      Moves (refMem img) s s1 → HeapRd s1 code[i])
    (htgt : TgtOk img Fn code i s.fp)
    (href : ∀ s1, Moves (refMem img) s s1 → RefOk (refMem img) s1 (opOfOff code[i]))
    (hfall : ∀ s1 s', (Mode.hintsAt Fn.hints (Fn.entry + i)).foldlM (Prover.Exec.runHint C) s = .ok s1 →
      Moves (refMem img) s s1 → OpModed (refMem img) s1 (opOfOff code[i]) → runOp C s1 (opOfOff code[i]) = .ok s' →
      s'.pc = s.pc + 1 → s'.fp = s.fp → Fine (refMem img) s' → s1.mem ≤ s'.mem →
      AtF img Fn code (i + 1) s' → StoreW Fn code i s' →
      (∀ c d f, code[i]? = some (.jump c d f) → s1.mem.get (s1.fp + c) = some 0) → Inv { s' with steps := s'.steps + 1 })
    (hjump : ∀ s1 s', (Mode.hintsAt Fn.hints (Fn.entry + i)).foldlM (Prover.Exec.runHint C) s = .ok s1 →
      Moves (refMem img) s s1 → OpModed (refMem img) s1 (opOfOff code[i]) → runOp C s1 (opOfOff code[i]) = .ok s' →
      Fine (refMem img) s' → s1.mem ≤ s'.mem → JumpOut img Fn code (∃ c, code[i]? = some (.jump c 0 1)) s1 s' →
      JumpTaken C code i s1 s' →
      (∀ c d f, code[i]? = some (.jump c d f) → ∃ v, s1.mem.get (s1.fp + c) = some v ∧ v ≠ 0) →
      Inv { s' with steps := s'.steps + 1 }) :
    StepOk C (refMem img) Inv (opOfOff code[i]) ((C.hints[s.pc]?).getD []) s := by
  have hops_i := hops i hi
  have hszC : Fn.entry + i < C.ops.size := by
    by_contra hn
    rw [Array.getElem?_eq_none (by omega)] at hops_i
    cases hops_i
  obtain ⟨hf, hpcl⟩ := hfetch i code[i] (List.getElem?_eq_getElem hi)
  obtain ⟨A, hA, pa, cur', pb, e, hpa, hnext, hcov⟩ := atF_step (img := img) har hacc hi hat
  obtain ⟨A1, h1, hc⟩ := offF_cases e
  rw [hpc, hhints i hi]
  refine stepOk_hintsF hs hA h1 hhint (fun s1 e1 hm hA1 ↦ ?_)
  have hA2 : FHolds img s1 (addNzs A1 ((Fn.nzr.get i).getD [])) :=
    addNzs_holds hA1 (by rw [hm.fp]; exact hnz)
  generalize addNzs A1 ((Fn.nzr.get i).getD []) = A2 at hA2 hc
  have hg1 : s1.Good := ⟨hm.fine.agree.wf, hm.fine.dl⟩
  have hpc1 : s1.pc = Fn.entry + i := hm.pc.trans hpc
  have hsafe1 : Safe prog img k ⟨addressOfIndex (Fn.entry + i), g ^ s1.fp⟩ := by
    rw [hm.fp, ← hpc]; exact hsafe
  rcases hc with ⟨hnj, A3, h3, rfl⟩ | ⟨c, d, f, hins, hwc, hwd, hwf, hcase⟩
  · have hj : code[i].isJump = false := by
      cases hci : code[i] with
      | jump c d f => exact absurd hci (hnj c d f)
      | _ => rfl
    obtain ⟨k', -, hh, -⟩ := hsafe1.fallThrough hf hpcl hj
    have hreads := stepF_reads hκ hm.fine hA2 hh (fun a b c he ↦ by
      have := hsmall i hi; rw [he] at this; exact this) h3
    have hmo := Mode.opModed_of hm.fine.agree hreads (href s1 hm)
    refine ⟨hmo, fun s' e' hf' hle' ↦ ?_⟩
    have e'' := e'
    obtain ⟨hw', hfp', hpc', hle3⟩ := stepF_wr hg1 hm.fine.fp (by rw [hpc1]; exact hszC) hA2.2
      (fun ho ↦ hO (hacc.oracle i ho) s1 e1 hm) h3 (fun a o c mode e p hci he hp ↦ by
        have ha : a < 2 ^ 28 := by have := hsmall i hi; rw [hci] at this; exact this.1
        have hr := hA2.1.st.1 a _ he
        rw [rd_get hκ hm.fine ha hr hp]
        simp [Exec.Sym.val, addressOfIndex, pow_add]) e'
    have hstw : StoreW Fn code i s' := by
      intro a o c' hci hS
      rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hci
      rw [hci] at h3 e'
      obtain ⟨-, hc, -⟩ := stepF_deref h3
      obtain ⟨p, x, hp, -, hx, -, -, hcell⟩ := Mode.deref_vals hg1 e'
      obtain ⟨-, hst⟩ := hcell rfl
      obtain ⟨v, hv⟩ := Mem.get_of_written (hA2.2.w c' (hc hS))
      exact ⟨p, x, by rw [hfp']; exact hle3.get _ _ hp, hx, written_of_get (hst v hv)⟩
    have hv' : FVal img s'.fp (execF Fn.F (Fn.entry + i) A3 code[i]) := by
      rw [hfp']; exact execF_val (by omega) hpows (stepF_val hA2.1 hh h3) hh
    exact hfall s1 s' e1 hm hmo e'' (by rw [hpc', hm.pc]) (by rw [hfp', hm.fp]) hf' hle'
      (hnext s' ⟨_, rfl, hv', execF_wr hw'⟩) hstw (fun c d f h ↦ by
        rw [List.getElem?_eq_getElem hi, Option.some.injEq] at h
        rw [h] at hj; cases hj)
  · have hop : opOfOff code[i] = .jump c d f := by rw [hins]; rfl
    have hsm := hsmall i hi
    rw [hins] at hsm hf
    obtain ⟨sc, sd, sf⟩ := hsm
    have hW : ∀ o, A2.hasW o = true → s1.mem.written (s1.fp + o) = true := fun o ho ↦ hA2.2.w o ho
    have hreads : Reads s1 (.jump c d f) := ⟨hW c hwc, hW d hwd, hW f hwf⟩
    rw [hop]
    have hmo : OpModed (refMem img) s1 (opOfOff code[i]) := by
      rw [hop]; exact Mode.opModed_of hm.fine.agree hreads (hop ▸ href s1 hm)
    refine ⟨hop ▸ hmo, fun s' e' hf' hle' ↦ ?_⟩
    obtain ⟨k', r, -, ⟨cv, dv, fv, hcv, hdv, hfv, hcK, hdK, hfK, -⟩, -⟩ := hsafe1.jump hf hpcl
    obtain ⟨vc, vd, vf, hvc, hvd, hvf, -, hcase'⟩ := Mode.jump_vals hg1 e'
    have ec : vc = cv := rd_get hκ hm.fine sc hcv hvc
    have ed : vd = dv := rd_get hκ hm.fine sd hdv hvd
    have ef : vf = fv := rd_get hκ hm.fine sf hfv hvf
    rcases hcase' with ⟨hz, hpc', hfp'⟩ | ⟨hne, hd', hf'', hpcs, hfps⟩
    · have hcur : cur' = some A2 := by
        rcases hcase with ⟨-, h⟩ | ⟨-, -, h⟩
        · exact h
        · apply h
          cases hnz' : Exec.isNonzero (A2.st.env.get c)
          · rfl
          · exact absurd (ec ▸ hz) (isNonzero_rd hA2.1 hnz' hcv)
      exact hfall s1 s' e1 hm hmo (by rw [hop]; exact e') (by rw [hpc', hm.pc]) (by rw [hfp', hm.fp]) hf' hle'
        (hnext s' ⟨A2, hcur, hA2.mono hle' hfp'⟩)
        (fun a o c' hci _ ↦ by rw [List.getElem?_eq_getElem hi, hins] at hci; cases hci)
        (fun c' d' f' h ↦ by
          rw [List.getElem?_eq_getElem hi, hins, Option.some.injEq, OffsetInstruction.jump.injEq] at h
          obtain ⟨rfl, -, -⟩ := h
          rw [← hz]; exact hvc)
    · rcases hcase with ⟨hz, -⟩ | ⟨-, hj, -⟩
      · exact absurd (ec.trans (isZero_rd hA2.1 hz hcv)) hne
      obtain ⟨ts, B, hx, -, hP⟩ := jumpF_spec (img := img) har hj
      have cov := fun s j hj hB ↦ hcov s j ((hP hpa).1 s j hj hB)
      rw [Exec.jumpExit_eq] at hx
      rcases hjk : Exec.jumpKind Fn.F Fn.entry Fn.len i A2.st d f with ⟨kind, succ⟩
      rw [hjk] at hx
      have hdl : dv.limb 0 = g ^ s'.pc := by rw [← ed, hd']; simp
      have hfl : fv.limb 0 = g ^ s'.fp := by rw [← ef, hf'']; simp
      obtain ⟨hregs, hextra⟩ := Exec.jumpKind_holds (L := img) (entry := Fn.entry) (len := Fn.len) (i := i)
        (fun h1 ↦ by rw [hm.fp, hmain h1, pow_zero]) hA2.1.st hdv hdK hfv hfK
      rw [hjk, hdl, hfl] at hregs
      rw [hjk] at hextra
      refine hjump s1 s' e1 hm hmo (by rw [hop]; exact e') hf' hle' (exit_out hκ hm.fine hle' hend (by omega) hfps sf hA2
        (fun h1 ↦ hm.fp.trans (hmain h1)) ⟨vf, hvf, ef ▸ hfv⟩ hjk hx hregs hextra hdv ?_ cov
        (fun ⟨c', hc'⟩ ↦ by
          rw [List.getElem?_eq_getElem hi, hins, Option.some.injEq, OffsetInstruction.jump.injEq] at hc'
          exact ⟨hc'.2.1, hc'.2.2⟩)
        (fun h0 h1 ↦ ⟨c, by rw [List.getElem?_eq_getElem hi, hins, h0, h1]⟩))
        ⟨c, d, f, by rw [List.getElem?_eq_getElem hi, hins], hd' ▸ hvd, hf'' ▸ hvf, hpcs⟩
        (fun c' d' f' h ↦ by
          rw [List.getElem?_eq_getElem hi, hins, Option.some.injEq, OffsetInstruction.jump.injEq] at h
          obtain ⟨rfl, -, -⟩ := h
          exact ⟨vc, hvc, hne⟩)
      intro kk' hk'
      have hcv' : Rd img s.fp c = some cv := by rw [← hm.fp]; exact hcv
      have hdv' : Rd img s.fp d = some dv := by rw [← hm.fp]; exact hdv
      exact htgt c d f (by rw [List.getElem?_eq_getElem hi, hins]) cv dv hcv' (ec ▸ hne) hdv' s'.pc
        (by unfold pcLim; omega) hdl kk' hk'


/-- **The entry**: the entry facts give the walk's state at offset `0`. -/
theorem atF_entry {Fn : FFun} {code : List OffsetInstruction} (henv : envOk Fn = true) {s : St}
    (h : EntryFr img Fn.sig s) : AtF img Fn code 0 s :=
  atF_zero (entryF_holds henv h)

end

end LeanVM.Guest.CoreMode
