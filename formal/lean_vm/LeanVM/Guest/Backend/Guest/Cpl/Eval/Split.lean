/-
  LeanVM.Guest.Backend.Guest.Cpl.Eval.Split

  The per-function completeness test (`Cpl.cplOkWith`) decided by parts: by its conjuncts, and for
  the largest functions each conjunct by runs of top-level statements, chunks of instructions or
  states of a walk, with what the parts give.
-/

module

public import LeanVM.Guest.Backend.Guest.Cpl.At
public import LeanVM.Guest.Backend.Sound.Cut
public import LeanVM.Guest.KernelLit

/-!
# The test by parts

The kernel shares no evaluation between declarations, and a declaration's memory grows with the
evaluation it runs. A run of small functions is decided whole (`Cpl.cplOkAt`); a larger function
by groups of the conjuncts of `Cpl.cplOkWith` (`cplParts`, `partsOk`), each group placing the
function again; a function the pieces place in parts (`Guest/Compiled.lean`) on its placed body
written out (`placedAt_cut`).

For the largest functions a conjunct is itself decided by parts:

* a test of every item of a list a block function makes (`Stmt.usesList`, `Lift.blockAtoms`)
  by runs of top-level statements (`all_part`, `all_end`);
* a fold over the placed body's instructions (`Complete.cellCounts`) by chunks of instructions,
  the fold's value after each chunk written out (`foldl_part`, `foldl_end`);
* the scope walk (`Complete.scopeBlock`) by runs of top-level statements, its state after each run
  written out (`scope_part`, `scope_end`, `scopedB_of`);

the temporaries (`Stmt.tmpsList`), their cells and the cells' counts written out once.
`staticOk_of` and `tmpsApartB_of` put the parts together.
-/

namespace LeanVM.Guest.Backend.CplEval

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Backend.Cpl GuestPiece
  Complete

@[expose] public section

/-! ## Runs of entries -/

theorem range_step {f : ℕ → Bool} {a n b m k : ℕ} (h1 : (List.range' a n).all f = true)
    (hb : a + n = b) (h2 : (List.range' b m).all f = true) (hk : n + m = k) :
    (List.range' a k).all f = true := by
  subst hb hk
  rw [← List.range'_append_1, List.all_append, h1, h2]
  rfl

theorem range_one {f : ℕ → Bool} {j : ℕ} (h : f j = true) : (List.range' j 1).all f = true := by
  simp [h]

/-- **The test passes for every entry**, from the runs. -/
theorem cplOkAll_of (h : (List.range' 0 1601).all cplOkAt = true) : CplOkAll := by
  intro i hi
  exact List.all_eq_true.mp h i (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)

/-! ## The conjuncts -/

/-- The conjuncts of `cplOkWith i pf`, in its order. -/
noncomputable def cplParts (i : ℕ) (pf : Placed) : List Bool :=
  [staticOk loopsG (guestTraced.getD i default) pf (fsWant i),
    scopedB (guestTraced.getD i default),
    noSelfCallB (guestTraced.getD i default),
    tmpsApartB (guestTraced.getD i default) pf,
    alL pf.fn.body (guestTraced.getD i default).core.body,
    natsDistinct ((armsP (keyedOf i) (guestTraced.getD i default) pf).map (·.1)),
    decide (ofCnt (pmaxP (keyedOf i) pf) = (B2C.plumbOf (i + 1)).pmax),
    decide (armsP (keyedOf i) (guestTraced.getD i default) pf = Cpl.armsOf i)]

/-- The conjuncts `ks` of the test hold. -/
noncomputable def partsOk (ks : List ℕ) (i : ℕ) (pf : Placed) : Bool := ks.all fun k => (cplParts i pf).getD k false

theorem partsOk_app {a b : List ℕ} {i : ℕ} {pf : Placed} (ha : partsOk a i pf = true)
    (hb : partsOk b i pf = true) : partsOk (a ++ b) i pf = true := by
  unfold partsOk at *
  rw [List.all_append, ha, hb]
  rfl

theorem any_app {a b : List ℕ} {i : ℕ} (ha : (placedAt i).any (partsOk a i) = true)
    (hb : (placedAt i).any (partsOk b i) = true) : (placedAt i).any (partsOk (a ++ b) i) = true := by
  cases h : placedAt i with
  | none => rw [h] at ha; cases ha
  | some pf =>
    rw [h] at ha hb
    exact partsOk_app ha hb

theorem cplOkWith_of_parts {i : ℕ} {pf : Placed} (h : partsOk [0, 1, 2, 3, 4, 5, 6, 7] i pf = true) :
    cplOkWith i pf = true := by
  simp only [partsOk, cplParts, List.all_cons, List.all_nil, List.getD_cons_zero,
    List.getD_cons_succ, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [cplOkWith, h0, h1, h2, h3, h4, h5, h6, h7, Bool.and_self]

/-- **Entry `i` by groups of conjuncts**, each group placing it. -/
theorem cplOkAt_of_any {i : ℕ} (h : (placedAt i).any (partsOk [0, 1, 2, 3, 4, 5, 6, 7] i) = true) :
    cplOkAt i = true := by
  cases hp : placedAt i with
  | none => rw [hp] at h; cases h
  | some pf =>
    rw [hp] at h
    exact cplOkAt_of hp (cplOkWith_of_parts h)

/-- **Entry `i` on its placed function written out.** -/
theorem cplOkAt_of_with {i : ℕ} {pf : Placed} (hp : placedAt i = some pf)
    (h : partsOk [0, 1, 2, 3, 4, 5, 6, 7] i pf = true) : cplOkAt i = true :=
  cplOkAt_of hp (cplOkWith_of_parts h)

/-- **A function the pieces place in parts**: its placed function is the last state's. -/
theorem placedAt_cut {j k : ℕ} {st₁ st : St}
    (h₁ : placeHead (guestTraced.getD j default) k (ctxOf loopsG sigsG (guestTraced.getD j default))
      (initSt loopsG (tablesAt outsG j) (guestTraced.getD j default)) = .ok ((), st₁))
    (h₂ : placeTail (guestTraced.getD j default) k (ctxOf loopsG sigsG (guestTraced.getD j default))
      st₁ = .ok ((), st))
    (hhead : cutHeadAt loopsG guestTraced outsG Data.functions.tail j st = true) :
    placedAt j = some (placedOf (guestTraced.getD j default) st).1 := by
  simp only [cutHeadAt, Bool.and_eq_true] at hhead
  exact placedAt_of (placeFn_of_cut hhead.1 (placeBody_of_cut h₁ h₂))

/-! ## Lists of a block by runs of statements -/

theorem drop_drop' {α : Type} (l : List α) (a m : ℕ) : (l.drop a).drop m = l.drop (a + m) := by
  rw [List.drop_drop]

theorem blockAtoms_append : ∀ (a b : List Stmt),
    Lift.blockAtoms (a ++ b) = Lift.blockAtoms a ++ Lift.blockAtoms b
  | [], _ => by simp [Lift.blockAtoms]
  | s :: ss, b => by simp [Lift.blockAtoms, blockAtoms_append ss b, List.append_assoc]

theorem runVals_append : ∀ (a b : List Atom), runVals (a ++ b) = runVals a ++ runVals b
  | [], _ => rfl
  | x :: xs, b => by cases x <;> simp [runVals, runVals_append xs b]

theorem all_part {α : Type} {g : List Stmt → List α} (hg : ∀ a b, g (a ++ b) = g a ++ g b)
    {p : α → Bool} {b : List Stmt} {a m : ℕ} (h₁ : (g ((b.drop a).take m)).all p = true)
    (h₂ : (g (b.drop (a + m))).all p = true) : (g (b.drop a)).all p = true := by
  rw [← List.take_append_drop m (b.drop a), hg, List.all_append, h₁, drop_drop', h₂]
  rfl

theorem all_end {α : Type} {g : List Stmt → List α} (hg : g [] = []) {p : α → Bool}
    {b : List Stmt} {k : ℕ} (hk : b.length ≤ k) : (g (b.drop k)).all p = true := by
  rw [List.drop_eq_nil_of_le hk, hg]
  rfl

theorem runVals_atoms_append (a b : List Stmt) :
    runVals (Lift.blockAtoms (a ++ b)) = runVals (Lift.blockAtoms a) ++ runVals (Lift.blockAtoms b) := by
  rw [blockAtoms_append, runVals_append]

/-! ## Folds by chunks -/

theorem foldl_part {α β : Type} {f : β → α → β} {l : List α} {k s : ℕ} {M M' M'' : β}
    (h₁ : ((l.drop k).take s).foldl f M = M') (h₂ : (l.drop (k + s)).foldl f M' = M'') :
    (l.drop k).foldl f M = M'' := by
  rw [← List.take_append_drop s (l.drop k), List.foldl_append, h₁, drop_drop', h₂]

theorem foldl_end {α β : Type} {f : β → α → β} {l : List α} {k : ℕ} {M : β} (hk : l.drop k = []) :
    (l.drop k).foldl f M = M := by
  rw [hk]
  rfl

/-- One instruction's step of `Complete.cellCounts`. -/
def cntStep (set : NMap Unit) (m : NMap ℕ) (o : LOp) : NMap ℕ :=
  (opCells o).foldl (fun m c => if set.contains c then m.insert c ((m.get? c).getD 0 + 1) else m) m

theorem cellCounts_eq (set : NMap Unit) (ops : List LOp) :
    cellCounts set ops = (ops.drop 0).foldl (cntStep set) {} := rfl

/-! ## The scope walk by runs of statements -/

theorem scopeBlock_append (rc : ℕ) : ∀ (a b : List Stmt) (s : SSt) {s' : SSt},
    scopeBlock rc a s = .ok s' → scopeBlock rc (a ++ b) s = scopeBlock rc b s'
  | [], _, s, s', h => by
    simp only [scopeBlock, Except.ok.injEq] at h
    subst h
    rfl
  | x :: xs, b, s, s', h => by
    simp only [List.cons_append, scopeBlock] at h ⊢
    cases hx : scopeStmt rc x s with
    | error e => rw [hx] at h; cases h
    | ok s₁ =>
      rw [hx] at h
      exact scopeBlock_append rc xs b s₁ h

theorem scope_part {rc : ℕ} {b : List Stmt} {a m : ℕ} {S S' S'' : SSt}
    (h₁ : scopeBlock rc ((b.drop a).take m) S = .ok S') (h₂ : scopeBlock rc (b.drop (a + m)) S' = .ok S'') :
    scopeBlock rc (b.drop a) S = .ok S'' := by
  rw [← List.take_append_drop m (b.drop a), scopeBlock_append rc _ _ S h₁, drop_drop', h₂]

theorem scope_end {rc : ℕ} {b : List Stmt} {k : ℕ} {S : SSt} (hk : b.length ≤ k) :
    scopeBlock rc (b.drop k) S = .ok S := by
  rw [List.drop_eq_nil_of_le hk]
  rfl

/-- **Scoped, from the walk by parts.** -/
theorem scopedB_of {tf : TracedFn} {S : SSt}
    (h : scopeBlock tf.rets (tf.core.body.drop 0)
      ⟨tf.trace.toList, addLive {} tf.core.params, false⟩ = .ok S)
    (hf : (match flushAt tf.rets S with
      | .ok s => s.rest.isEmpty
      | .error _ => false) = true) : scopedB tf = true := by
  rw [List.drop_zero] at h
  unfold scopedB scopedE
  rw [h]
  cases hS : flushAt tf.rets S with
  | error e => rw [hS] at hf; cases hf
  | ok s =>
    rw [hS] at hf
    simp only at hf
    simp [hS, List.isEmpty_iff.mp hf]

/-! ## The static test and the temporaries' cells, put together -/

theorem nmap_eta {α : Type} (m : NMap α) : (⟨m.t⟩ : NMap α) = m := rfl

/-- **The static test from its parts**, the temporaries' cells written out as `Ts`. -/
theorem staticOk_of {loops : Loops} {tf : TracedFn} {pf : Placed} {n : ℕ} {Ts : NMap Unit}
    (hhead : (pf.fn.frameSize == n && isLoopName tf.core.name == tf.core.loop &&
      (!(loops[tf.core.name]?).any (·.registered) || Nat.blt (2 + tf.core.params.length) n) &&
      Nat.ble (2 + tf.core.params.length) n) = true)
    (hpar : consecFrom pf.locs tf.core.params 2 = true)
    (hret : (retL tf.core.body).all (fun vs => consecFrom pf.locs vs (2 + tf.core.params.length)) = true)
    (hin : cellsIn pf.locs (Stmt.tmpsList tf.core.body) n = true)
    (hnd : natsDistinct ((Stmt.tmpsList tf.core.body).map fun t => (cellP pf.locs t).getD 0) = true)
    (hfun : (runVals (Lift.blockAtoms (tf.core.body.drop 0))).all (fun _ => false) = true)
    (hset : cellSet pf.locs (Stmt.tmpsList tf.core.body) = Ts)
    (hself : (!(loops[tf.core.name]?).any (·.registered) || !Ts.contains (2 + tf.core.params.length)) = true)
    (hruns : (Lift.blockAtoms (tf.core.body.drop 0)).all (runOk pf.locs Ts n) = true) :
    staticOk loops tf pf n = true := by
  rw [List.drop_zero] at hfun hruns
  have hfun' : runVals (Lift.blockAtoms tf.core.body) = [] := by
    cases h : runVals (Lift.blockAtoms tf.core.body) with
    | nil => rfl
    | cons x xs => rw [h] at hfun; cases hfun
  unfold staticOk
  simp only [withLocs_eq, Trie.seq_eq, hset, hfun', nmap_eta]
  simp only [Bool.and_eq_true] at hhead
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hhead
  simp only [h1, h2, h3, h4, hpar, hret, hin, hnd, hself, hruns, cellFun, Bool.and_self]

theorem mem_of_testBit_idxMask {i : ℕ} : ∀ {l : List V}, (idxMask l).testBit i = true → ∃ v ∈ l, v.idx = i
  | [], h => by simp [idxMask] at h
  | w :: ws, h => by
    rw [idxMask, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨v, hv, he⟩ := mem_of_testBit_idxMask h
      exact ⟨v, List.mem_cons_of_mem _ hv, he⟩
    · simp only [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at h
      refine ⟨w, List.mem_cons_self, ?_⟩
      have h1 := h.2
      rw [Nat.testBit_one_eq_true_iff_self_eq_zero] at h1
      omega

/-- **Temporaries apart, from its parts**: the temporaries' indices in `T`, their cells written out
as `Ts` and the cells' counts as `C`. -/
theorem tmpsApartB_of {tf : TracedFn} {pf : Placed} {T Ts : NMap Unit} {C : NMap ℕ}
    (hnd : idxNodup (Stmt.tmpsList tf.core.body) 0 = true)
    (hT : (Stmt.tmpsList tf.core.body).all (fun t => T.contains t.idx) = true)
    (huses : (Stmt.usesList (tf.core.body.drop 0)).all (fun v => !T.contains v.idx &&
      match pf.locs[v]? with
      | some l => !Ts.contains (locBase l)
      | none => true) = true)
    (hpar : tf.core.params.all (fun v => !T.contains v.idx &&
      match pf.locs[v]? with
      | some l => !Ts.contains (locBase l)
      | none => true) = true)
    (hset : tmpCellSet pf.locs (Stmt.tmpsList tf.core.body) = Ts)
    (hcnt : ((blockOps pf.fn.body 0).drop 0).foldl (cntStep Ts) {} = C)
    (hsome : (Stmt.tmpsList tf.core.body).all (fun t => (cellP pf.locs t).isSome) = true)
    (hone : (Stmt.tmpsList tf.core.body).all (fun t => match cellP pf.locs t with
      | some n => C.get? n == some 1
      | none => false) = true) :
    tmpsApartB tf pf = true := by
  rw [List.drop_zero] at huses
  have hall : ∀ v ∈ Stmt.usesList tf.core.body ++ tf.core.params, (!T.contains v.idx &&
      match pf.locs[v]? with
      | some l => !Ts.contains (locBase l)
      | none => true) = true := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact List.all_eq_true.mp huses v hv
    · exact List.all_eq_true.mp hpar v hv
  have hcnt' : cellCounts Ts (blockOps pf.fn.body 0) = C := (cellCounts_eq _ _).trans hcnt
  unfold tmpsApartB
  simp only [nmapSeq_eq]
  rw [hset, hcnt']
  simp only [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · unfold freshOnce
    rw [natSeq_eq, hnd, Bool.true_and, List.all_eq_true]
    intro t ht
    cases hb : (idxMask (Stmt.usesList tf.core.body ++ tf.core.params)).testBit t.idx with
    | false => rfl
    | true =>
      obtain ⟨v, hv, he⟩ := mem_of_testBit_idxMask hb
      have h1 := hall v hv
      have h2 := List.all_eq_true.mp hT t ht
      rw [he, h2] at h1
      cases h1
  · unfold apartWith
    simp only [Bool.and_eq_true]
    refine ⟨⟨hsome, List.all_eq_true.mpr fun v hv => ?_⟩, hone⟩
    have := hall v hv
    simp only [Bool.and_eq_true] at this
    exact this.2

end
end LeanVM.Guest.Backend.CplEval
