/-
  LeanVM.Guest.Bridge.BufChk

  The buffer hints' check (the bus era's `allocShape` and `pairsA`, on Hotwire's hints): every path
  allocates the body's top-level allocation atoms, in order, and the buffer hints compile them one
  for one, unaligned, their values at certificate cells of the frame.
-/

module

public import LeanVM.Guest.Bridge.AllocFnLink
public import LeanVM.Guest.Bridge.Track

/-!
# The buffer hints' check

`bufFnChk X fs fn d`, by `decide +kernel` per function (`scripts/bridge-cert/alloc.py`):

* the body's allocation atoms are top-level statements (`Stmt.noAlloc` elsewhere), and no statement
  before the last of them returns (`allocShape`), so every path allocates them all, in order
  (`allocShape_walk`);
* the buffer hints compile those atoms one for one (`pairsB`, `compilesB`): an `alloc` or `allocDyn`
  its own, an `allocDyn` whose size cell holds a constant power `g^n` an `alloc` of `n` cells, each
  unaligned, its values at certificate cells of the frame past its header (`bufCellOk`);
* the context's cells fit (`locOk`), so a certificate cell is the certificate's (`locAt_ofData`).

Restored from the tag's `Bridge/AllocDefs.lean` and `AllocSound.lean`; the hint-only cells, which
the bus era's `allocCellOk` admitted, are not.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Check (getF)

@[expose] public section

/-! ## The body's allocations -/

/-- The allocation hints of a block's top-level atoms, in order. -/
def topAllocs : List Stmt → List Core.Hint
  | [] => []
  | .atom (.hint h) :: ss => bif coreFlow h then topAllocs ss else h :: topAllocs ss
  | _ :: ss => topAllocs ss

mutual
/-- No allocation atom in a statement. -/
def Stmt.noAlloc : Stmt → Bool
  | .atom a => !allocAtom a
  | .ite _ z n => Stmt.noAllocList z && Stmt.noAllocList n
  | .match_ _ arms => Stmt.noAllocArms arms
  | _ => true

/-- No allocation atom in a block. -/
def Stmt.noAllocList : List Stmt → Bool
  | [] => true
  | s :: ss => Stmt.noAlloc s && Stmt.noAllocList ss

/-- No allocation atom in arms. -/
def Stmt.noAllocArms : List (List Stmt) → Bool
  | [] => true
  | a :: as => Stmt.noAllocList a && Stmt.noAllocArms as
end

mutual
/-- No `ret` in a statement. -/
def Stmt.retFree : Stmt → Bool
  | .ret _ => false
  | .ite _ z n => Stmt.retFreeList z && Stmt.retFreeList n
  | .match_ _ arms => Stmt.retFreeArms arms
  | _ => true

/-- No `ret` in a block. -/
def Stmt.retFreeList : List Stmt → Bool
  | [] => true
  | s :: ss => Stmt.retFree s && Stmt.retFreeList ss

/-- No `ret` in arms. -/
def Stmt.retFreeArms : List (List Stmt) → Bool
  | [] => true
  | a :: as => Stmt.retFreeList a && Stmt.retFreeArms as
end

/-- **Every path allocates the top-level allocation atoms, in order**: no allocation atom below
the top level, and no statement before the last of them returns. -/
def allocShape : List Stmt → Bool
  | [] => true
  | .atom _ :: ss => allocShape ss
  | s :: ss => Stmt.noAlloc s && ((topAllocs ss).isEmpty || Stmt.retFree s) && allocShape ss

/-! ## The check -/

/-- A value's cell holds it in the frame: a certificate cell of the frame past its header, its index
below `2^30`, no hint-only cell. -/
noncomputable def bufCellOk (X : AlignCtx) (fs : ℕ) (v : V) : Bool :=
  (X.extra.lookup v.idx).isNone && decide (v.idx < 2 ^ 30) && decide (2 ≤ X.locAt v.idx) && decide (X.locAt v.idx < fs)

/-- A buffer hint compiles an allocation atom, unaligned, its values in the frame: its own kind, or
an `allocDyn` whose size cell holds `g^n`, `n < 2^28`, as an `alloc` of `n`. -/
noncomputable def compilesB (X : AlignCtx) (fs : ℕ) : Core.Hint → Prover.Exec.Hint → Bool
  | .alloc d n, .alloc p n' a => bufCellOk X fs d && Nat.beq (X.locAt d.idx) p && Nat.beq n n' && !a
  | .allocDyn d n, .allocDyn p c => bufCellOk X fs d && bufCellOk X fs n && Nat.beq (X.locAt d.idx) p &&
      Nat.beq (X.locAt n.idx) c
  | .allocDyn d n, .alloc p n' a => bufCellOk X fs d && bufCellOk X fs n && Nat.beq (X.locAt d.idx) p &&
      X.pcAt (X.locAt n.idx) == some n' && Nat.blt n' (2 ^ 28) && !a
  | _, _ => false

/-- The atoms and the buffer hints pair one for one, each compiling its own. -/
noncomputable def pairsB (X : AlignCtx) (fs : ℕ) : List Core.Hint → List Prover.Exec.Hint → Bool
  | [], [] => true
  | a :: as, h :: hs => compilesB X fs a h && pairsB X fs as hs
  | _, _ => false

/-- The buffer hints of an advice, in order. -/
noncomputable def bufHints (X : AlignCtx) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : List Prover.Exec.Hint :=
  ((allocHints d).filter fun q ↦ isBuf X q.2).map (·.2)

/-- **The buffer hints' check** of a function of frame size `fs`. -/
noncomputable def bufFnChk (X : AlignCtx) (fs : ℕ) (fn : Fn) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) :
    Bool :=
  X.locOk && allocShape fn.body && pairsB X fs (topAllocs fn.body) (bufHints X d)

/-- **Compiled function `j` passes the buffer hints' check.** -/
def BufFnJ (j : ℕ) : Prop := bufFnChk (ctxOf j) (B2C.fsN j) (coreOf j) (adviceOf j) = true

/-! ## What a path allocates -/

/-- An event's allocation hint. -/
def Ev.allocH? : Ev → Option Core.Hint
  | .atom (.hint h) => bif coreFlow h then none else some h
  | _ => none

/-- An allocation hint's pointer. -/
def allocDstOf : Core.Hint → V
  | .alloc d _ | .allocDyn d _ => d
  | _ => default

/-- An allocation hint's size under `σ`. -/
noncomputable def allocSizeOf (σ : Val) : Core.Hint → ℕ
  | .alloc _ n => n
  | .allocDyn _ s => logG (σ s)
  | _ => 0

end

public section

/-- **A function's buffer hints' check from its pack's**, as `addrFnJ_of`. -/
theorem bufFnJ_of {j : ℕ} {f : CompiledFunction} {cf : Core.Fn} {C : Check.Cert} {P : B2C.Plumb}
    {ex : List (ℕ × ℕ)} {en : List (String × ℕ)} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} {main : Bool}
    (hf : fnOf j = f) (hcf : coreOf j = cf) (hC : certOf j = C.withPows Data.powTree) (hP : B2C.plumbOf j = P)
    (ht : (extraOf j, entsOf j, adviceOf j) = (ex, en, d)) (hm : (j == 1) = main) {n : ℕ} (hn : B2C.fsN j = n)
    (h : bufFnChk (AlignCtx.ofData C.locs ex f.entryPc main P Data.powTree Data.jtTrie en alignHalt
      f.instructionCount) n cf d = true) : BufFnJ j := by
  simp only [Prod.mk.injEq] at ht
  obtain ⟨hex, hen, hd⟩ := ht
  have hl : (certOf j).locs = C.locs := by rw [hC]; cases C; rfl
  rw [BufFnJ, ctxOf, hl, hex, hen, hd, hf, hcf, hP, hm, hn]
  exact h

variable {σ : Val}

theorem pick_noA {x : V} {args rets : List V} :
    ∀ (fs : List String) (j : ℕ), (pick σ x args rets j fs).All (fun e ↦ Ev.allocH? e = none)
  | [], _ => trivial
  | f :: fs, j => by
    unfold pick
    split_ifs
    · intro e he
      rw [List.mem_singleton] at he
      subst he
      rfl
    · exact pick_noA fs (j + 1)

mutual
theorem walk1_noA : ∀ (s : Stmt), Stmt.noAlloc s = true → (walk1 σ s).All (fun e ↦ Ev.allocH? e = none)
  | .atom a, h => by
    intro e he
    simp only [List.mem_singleton] at he
    subst he
    cases a with
    | hint hh => cases hc : coreFlow hh <;> simp_all [Ev.allocH?, allocAtom, Stmt.noAlloc]
    | _ => rfl
  | .ite c z n, h => by
    simp only [Stmt.noAlloc, Bool.and_eq_true] at h
    simp only [walk1]
    refine Out.all_pre (fun e he ↦ by rw [List.mem_singleton] at he; subst he; rfl) ?_
    split_ifs
    · exact walk_noA z h.1
    · exact walk_noA n h.2
  | .match_ x arms, h => walkArms_noA x arms 0 h
  | .call .., _ => fun e he ↦ by simp only [List.mem_singleton] at he; subst he; rfl
  | .callIf c f args, _ => by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · rfl
    · split_ifs <;> rfl
  | .dispatch x fs args rets, _ => pick_noA fs 0
  | .ret _, _ => fun _ he ↦ by simp at he

theorem walk_noA : ∀ (ss : List Stmt), Stmt.noAllocList ss = true → (walk σ ss).All (fun e ↦ Ev.allocH? e = none)
  | [], _ => by intro e he; simp at he
  | s :: ss, h => by
    simp only [Stmt.noAllocList, Bool.and_eq_true] at h
    rw [walk]
    exact Out.all_seq (walk_noA ss h.2) (walk1_noA s h.1)

theorem walkArms_noA (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ), Stmt.noAllocArms arms = true →
    (walkArms σ x j arms).All (fun e ↦ Ev.allocH? e = none)
  | [], _, _ => trivial
  | a :: as, j, h => by
    simp only [Stmt.noAllocArms, Bool.and_eq_true] at h
    unfold walkArms
    split_ifs
    · exact walk_noA a h.1
    · exact walkArms_noA x as (j + 1) h.2
end

theorem pick_retFree {x : V} {args rets : List V} :
    ∀ (fs : List String) (j : ℕ) (es : List Ev) (vs : List V), pick σ x args rets j fs ≠ .ret es vs
  | [], _, _, _ => by simp [pick]
  | f :: fs, j, es, vs => by
    unfold pick
    split_ifs
    · simp
    · exact pick_retFree fs (j + 1) es vs

mutual
theorem walk1_retFree : ∀ (s : Stmt), Stmt.retFree s = true → ∀ es vs, walk1 σ s ≠ .ret es vs
  | .atom a, _, _, _ => by simp [walk1]
  | .ite c z n, h, es, vs => by
    simp only [Stmt.retFree, Bool.and_eq_true] at h
    simp only [walk1]
    intro he
    obtain ⟨es', h1, -⟩ := pre_eq_ret he
    split_ifs at h1
    · exact walk_retFree z h.1 _ _ h1
    · exact walk_retFree n h.2 _ _ h1
  | .match_ x arms, h, es, vs => walkArms_retFree x arms 0 h es vs
  | .call .., _, _, _ => by simp [walk1]
  | .callIf .., _, _, _ => by simp [walk1]
  | .dispatch x fs args rets, _, es, vs => pick_retFree fs 0 es vs
  | .ret _, h, _, _ => by simp [Stmt.retFree] at h

theorem walk_retFree : ∀ (ss : List Stmt), Stmt.retFreeList ss = true → ∀ es vs, walk σ ss ≠ .ret es vs
  | [], _, _, _ => by simp [walk]
  | s :: ss, h, es, vs => by
    simp only [Stmt.retFreeList, Bool.and_eq_true] at h
    rw [walk]
    intro he
    rcases seq_eq_ret he with ⟨es1, es2, -, h2, -⟩ | h1
    · exact walk_retFree ss h.2 _ _ h2
    · exact walk1_retFree s h.1 _ _ h1

theorem walkArms_retFree (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ), Stmt.retFreeArms arms = true →
    ∀ es vs, walkArms σ x j arms ≠ .ret es vs
  | [], _, _, _, _ => by simp [walkArms]
  | a :: as, j, h, es, vs => by
    simp only [Stmt.retFreeArms, Bool.and_eq_true] at h
    unfold walkArms
    split_ifs
    · exact walk_retFree a h.1 es vs
    · exact walkArms_retFree x as (j + 1) h.2 es vs
end

theorem filterMap_noA {es : List Ev} (h : ∀ e ∈ es, Ev.allocH? e = none) : es.filterMap Ev.allocH? = [] :=
  List.filterMap_eq_nil_iff.mpr h

theorem shape_step {s : Stmt} {ss : List Stmt} (h1 : Stmt.noAlloc s = true)
    (h2 : ((topAllocs ss).isEmpty || Stmt.retFree s) = true)
    (ih : ∀ es, (walk σ ss = .fall es ∨ ∃ vs, walk σ ss = .ret es vs) → es.filterMap Ev.allocH? = topAllocs ss)
    (es : List Ev) (h : walk σ (s :: ss) = .fall es ∨ ∃ vs, walk σ (s :: ss) = .ret es vs) :
    es.filterMap Ev.allocH? = topAllocs ss := by
  have hA := walk1_noA (σ := σ) s h1
  rw [walk] at h
  cases hw1 : walk1 σ s with
  | fall es1 =>
    rw [hw1] at h hA
    have hA' : ∀ e ∈ es1, Ev.allocH? e = none := hA
    cases hw : walk σ ss with
    | fall es2 =>
      rw [hw] at h
      rcases h with h | ⟨vs, h⟩ <;> simp only [Out.seq, Out.pre, Out.fall.injEq, reduceCtorEq] at h
      rw [← h, List.filterMap_append, filterMap_noA hA', ih es2 (Or.inl hw), List.nil_append]
    | ret es2 vs2 =>
      rw [hw] at h
      rcases h with h | ⟨vs, h⟩ <;> simp only [Out.seq, Out.pre, Out.ret.injEq, reduceCtorEq] at h
      rw [← h.1, List.filterMap_append, filterMap_noA hA', ih es2 (Or.inr ⟨vs2, hw⟩), List.nil_append]
    | stuck =>
      rw [hw] at h
      rcases h with h | ⟨vs, h⟩ <;> simp [Out.seq, Out.pre] at h
  | ret es1 vs1 =>
    rw [hw1] at h hA
    have hA' : ∀ e ∈ es1, Ev.allocH? e = none := hA
    rcases h with h | ⟨vs, h⟩ <;> simp only [Out.seq, Out.ret.injEq, reduceCtorEq] at h
    have hnr : Stmt.retFree s = false := by
      cases hr : Stmt.retFree s
      · rfl
      · exact absurd hw1 (walk1_retFree s hr es1 vs1)
    rw [hnr, Bool.or_false, List.isEmpty_iff] at h2
    rw [← h.1, filterMap_noA hA', h2]
  | stuck =>
    rw [hw1] at h
    rcases h with h | ⟨vs, h⟩ <;> simp [Out.seq] at h

/-- **Every path allocates the top-level allocation atoms, in order.** -/
theorem allocShape_walk : ∀ (ss : List Stmt), allocShape ss = true → ∀ es,
    (walk σ ss = .fall es ∨ ∃ vs, walk σ ss = .ret es vs) → es.filterMap Ev.allocH? = topAllocs ss
  | [], _, es, h => by
    rcases h with h | ⟨vs, h⟩ <;> simp only [walk, Out.fall.injEq, reduceCtorEq] at h
    subst h; rfl
  | s :: ss, hs, es, h => by
    cases s
    case atom a =>
      rw [allocShape] at hs
      have key : ∀ es', es = .atom a :: es' → (walk σ ss = .fall es' ∨ ∃ vs, walk σ ss = .ret es' vs) →
          es.filterMap Ev.allocH? = topAllocs (.atom a :: ss) := by
        rintro es' rfl h'
        rw [List.filterMap_cons, allocShape_walk ss hs es' h']
        cases a with
        | hint hh => cases hc : coreFlow hh <;> simp [Ev.allocH?, topAllocs, hc]
        | _ => simp [Ev.allocH?, topAllocs]
      rw [walk_atom_cons] at h
      rcases h with h | ⟨vs, h⟩
      · cases hw : walk σ ss <;> rw [hw] at h <;> simp only [Out.pre, Out.fall.injEq, reduceCtorEq] at h
        exact key _ (by rw [← h]; rfl) (Or.inl hw)
      · cases hw : walk σ ss <;> rw [hw] at h <;> simp only [Out.pre, Out.ret.injEq, reduceCtorEq] at h
        exact key _ (by rw [← h.1]; rfl) (Or.inr ⟨_, hw⟩)
    all_goals
      simp only [allocShape, Bool.and_eq_true] at hs
      exact shape_step hs.1.1 hs.1.2 (allocShape_walk ss hs.2) es h

theorem allocDst_of {e : Ev} : e.allocDst? = (Ev.allocH? e).map allocDstOf := by
  rcases e with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ | _⟩ | _ | _ | _ <;>
    rfl

theorem alloc_of {e : Ev} : e.alloc? σ = (Ev.allocH? e).map (allocSizeOf σ) := by
  rcases e with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ | _⟩ | _ | _ | _ <;>
    rfl

/-- **The `HeapBuf` pointers of a path of a body of `allocShape`**: its top-level atoms'. -/
theorem allocDsts_of_shape {body : List Stmt} (hs : allocShape body = true) {es : List Ev} {vs : List V}
    (hw : walk σ body = .ret es vs) : allocDsts es = (topAllocs body).map allocDstOf := by
  rw [← allocShape_walk body hs es (Or.inr ⟨vs, hw⟩), allocDsts, List.map_filterMap]
  exact List.filterMap_congr fun e _ ↦ allocDst_of

/-- **The `HeapBuf` sizes of a path of a body of `allocShape`**: its top-level atoms'. -/
theorem allocs_of_shape {body : List Stmt} (hs : allocShape body = true) {es : List Ev} {vs : List V}
    (hw : walk σ body = .ret es vs) : allocs σ es = (topAllocs body).map (allocSizeOf σ) := by
  rw [← allocShape_walk body hs es (Or.inr ⟨vs, hw⟩), allocs, List.map_filterMap]
  exact List.filterMap_congr fun e _ ↦ alloc_of

/-- **The `k`-th buffer hint compiles the `k`-th atom.** -/
theorem pairsB_get {X : AlignCtx} {fs : ℕ} : ∀ {as : List Core.Hint} {hs : List Prover.Exec.Hint}, pairsB X fs as hs = true →
    ∀ (k : ℕ) (h : Prover.Exec.Hint), hs[k]? = some h → ∃ a, as[k]? = some a ∧ compilesB X fs a h
  | [], [], _, _, _, hk => by simp at hk
  | a :: as, h' :: hs, hp, k, h, hk => by
    simp only [pairsB, Bool.and_eq_true] at hp
    cases k with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hk ⊢; subst hk; exact ⟨a, rfl, hp.1⟩
    | succ k => simpa using pairsB_get hp.2 k h (by simpa using hk)
  | [], _ :: _, hp, _, _, _ => by simp [pairsB] at hp
  | _ :: _, [], hp, _, _, _ => by simp [pairsB] at hp

theorem pairsB_length {X : AlignCtx} {fs : ℕ} : ∀ {as : List Core.Hint} {hs : List Prover.Exec.Hint}, pairsB X fs as hs = true →
    as.length = hs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, hp => by
    simp only [pairsB, Bool.and_eq_true] at hp
    simp [pairsB_length hp.2]
  | [], _ :: _, hp => by simp [pairsB] at hp
  | _ :: _, [], hp => by simp [pairsB] at hp


/-- **Every core function passes the buffer hints' check at the deployed alignment**, from every
compiled index's. -/
theorem bufFnChk_alignA (hall : ∀ j, 1 ≤ j → j < nFns → BufFnJ j) :
    ∀ f fn, coreProgram.find? f = some fn → bufFnChk (alignA f).X (B2C.fs f) fn (alignA f).d = true := by
  intro f fn hfn
  obtain ⟨j, hj⟩ := idxOf_of_find' hfn
  obtain ⟨i, rfl, hi, -, hfind, hcore, hfs, -, h1, h2⟩ := B2C.fn_of_idx hj
  rw [hfn] at hfind
  cases hfind
  have h := hall (i + 1) h1 h2
  rw [BufFnJ, hcore] at h
  rw [alignA_of hj, hfs]
  exact h

end

end LeanVM.Guest.Bridge
