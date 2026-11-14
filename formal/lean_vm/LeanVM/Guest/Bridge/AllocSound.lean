/-
  LeanVM.Guest.Bridge.AllocSound

  What the allocation hints' check gives: every path allocates the body's top-level allocation
  atoms, in order, and the buffer hints compile them one for one.
-/

module

public import LeanVM.Guest.Bridge.AllocDefs
public import LeanVM.Guest.Bridge.Track

/-!
# The allocation check's soundness

`allocShape_walk`: a body of `allocShape` allocates, on every path, its top-level allocation atoms in
order (`Ev.allocH?`), so its `HeapBuf` pointers are theirs (`allocDsts_of_shape`) and its sizes their
sizes (`allocs_of_shape`). `pairsA_get`: the `k`-th buffer hint compiles the `k`-th atom.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

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
theorem pairsA_get {X : AlignCtx} {fs : ℕ} : ∀ {as : List Core.Hint} {hs : List Prover.Exec.Hint}, pairsA X fs as hs = true →
    ∀ (k : ℕ) (h : Prover.Exec.Hint), hs[k]? = some h → ∃ a, as[k]? = some a ∧ compilesA X fs a h
  | [], [], _, _, _, hk => by simp at hk
  | a :: as, h' :: hs, hp, k, h, hk => by
    simp only [pairsA, Bool.and_eq_true] at hp
    cases k with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hk ⊢; subst hk; exact ⟨a, rfl, hp.1⟩
    | succ k => simpa using pairsA_get hp.2 k h (by simpa using hk)
  | [], _ :: _, hp, _, _, _ => by simp [pairsA] at hp
  | _ :: _, [], hp, _, _, _ => by simp [pairsA] at hp

theorem pairsA_length {X : AlignCtx} {fs : ℕ} : ∀ {as : List Core.Hint} {hs : List Prover.Exec.Hint}, pairsA X fs as hs = true →
    as.length = hs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, hp => by
    simp only [pairsA, Bool.and_eq_true] at hp
    simp [pairsA_length hp.2]
  | [], _ :: _, hp => by simp [pairsA] at hp
  | _ :: _, [], hp => by simp [pairsA] at hp

end

end LeanVM.Guest.Bridge
