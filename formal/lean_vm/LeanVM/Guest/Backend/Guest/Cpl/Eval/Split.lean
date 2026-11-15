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

/-- One instruction's step of `Complete.fpPtrs`. -/
def fpStep (m : NMap Unit) (o : LOp) : NMap Unit :=
  match o with
  | .deref p _ _ .fp => m.insert p ()
  | _ => m

/-- One instruction's test of `Complete.tmpOpsB`. -/
def tmpOpOk (set fps : NMap Unit) (o : LOp) : Bool :=
  (opCells o).all fun c => !set.contains c || match o with
    | .deref p 0 d .cell => d == c && !set.contains p && !fps.contains p
    | _ => false

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
      | none => false) = true)
    (hdc : distinctCells pf.locs (Stmt.tmpsList tf.core.body) {} = true) {F : NMap Unit}
    (hfp : ((blockOps pf.fn.body 0).drop 0).foldl fpStep {} = F)
    (hto : ((blockOps pf.fn.body 0).drop 0).all (tmpOpOk Ts F) = true) :
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
  have hfp' : fpPtrs (blockOps pf.fn.body 0) = F := hfp
  rw [List.drop_zero] at hto
  unfold tmpsApartB
  simp only [nmapSeq_eq]
  rw [hset, hcnt', hfp']
  simp only [Bool.and_eq_true]
  refine ⟨?_, ⟨?_, hdc⟩, hto⟩
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

/-! ## The largest functions: one test per run of statements -/

/-- What the test of a large function reads besides its body: its name, its places, its
temporaries `TL` (written out), its frame size and its number of parameters. -/
structure BigC where
  name : String
  locs : VMap Loc
  TL : List V
  n : ℕ
  np : ℕ

/-- The cells of the temporaries, as `staticOk` makes them. -/
def BigC.Ts (c : BigC) : NMap Unit := cellSet c.locs c.TL

/-- The cells of the temporaries, as `tmpsApartB` makes them. -/
def BigC.TA (c : BigC) : NMap Unit := tmpCellSet c.locs c.TL

/-- The temporaries' indices. -/
def BigC.T (c : BigC) : NMap Unit := c.TL.foldl (fun m t => m.insert t.idx ()) {}

/-- A value named by the body or a parameter is no temporary and not placed at a temporary's
cell. -/
def useOk (c : BigC) (v : V) : Bool :=
  !c.T.contains v.idx && match c.locs[v]? with
    | some l => !c.TA.contains (locBase l)
    | none => true

/-- **The test of a run of statements** `seg` of a large function, `L` its temporaries. -/
def segOk (c : BigC) (seg : List Stmt) (L : List V) : Bool :=
  decide (Stmt.tmpsList seg = L) && (Stmt.usesList seg).all (useOk c) &&
    (runVals (Lift.blockAtoms seg)).isEmpty && (Lift.blockAtoms seg).all (runOk c.locs c.Ts c.n) &&
    (retL seg).all (fun vs => consecFrom c.locs vs (2 + c.np)) && !callsL c.name seg

theorem retL_append : ∀ (a b : List Stmt), retL (a ++ b) = retL a ++ retL b
  | [], _ => by simp [retL]
  | s :: ss, b => by simp [retL, retL_append ss b, List.append_assoc]

theorem callsL_append (f : String) : ∀ (a b : List Stmt), callsL f (a ++ b) = (callsL f a || callsL f b)
  | [], _ => by simp [callsL]
  | s :: ss, b => by simp [callsL, callsL_append f ss b, Bool.or_assoc]

theorem segOk_append {c : BigC} {a b : List Stmt} {La Lb : List V} (ha : segOk c a La = true)
    (hb : segOk c b Lb = true) : segOk c (a ++ b) (La ++ Lb) = true := by
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.isEmpty_iff] at ha hb ⊢
  obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := ha
  obtain ⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩ := hb
  rw [tmpsList_append, usesList_append, blockAtoms_append, runVals_append, retL_append,
    callsL_append, List.all_append, List.all_append, List.all_append, a1, b1, a2, b2, a3, b3, a4, b4,
    a5, b5, a6, b6]
  simp

theorem seg_part {c : BigC} {b : List Stmt} {a m : ℕ} {L₁ L₂ : List V}
    (h₁ : segOk c ((b.drop a).take m) L₁ = true) (h₂ : segOk c (b.drop (a + m)) L₂ = true) :
    segOk c (b.drop a) (L₁ ++ L₂) = true := by
  rw [← List.take_append_drop m (b.drop a), drop_drop']
  exact segOk_append h₁ h₂

theorem seg_end {c : BigC} {b : List Stmt} {k : ℕ} (hk : b.length ≤ k) : segOk c (b.drop k) [] = true := by
  rw [List.drop_eq_nil_of_le hk]
  rfl

theorem ops_part {β : Type} {f : β → LOp → β} {b : List PStmt} {k s : ℕ} {M M' M'' : β}
    (h₁ : ((blockOpsFrom b 0 k).take s).foldl f M = M')
    (h₂ : ((blockOps b 0).drop (k + s)).foldl f M' = M'') :
    ((blockOps b 0).drop k).foldl f M = M'' := by
  rw [blockOpsFrom_eq] at h₁
  exact foldl_part h₁ h₂

theorem ops_end {β : Type} {f : β → LOp → β} {b : List PStmt} {k : ℕ} {M : β} (hk : blockSize b ≤ k) :
    ((blockOps b 0).drop k).foldl f M = M :=
  foldl_end (List.drop_eq_nil_of_le (by rw [blockOps_length]; exact hk))

theorem opsAll_part {p : LOp → Bool} {b : List PStmt} {k s : ℕ}
    (h₁ : ((blockOpsFrom b 0 k).take s).all p = true) (h₂ : ((blockOps b 0).drop (k + s)).all p = true) :
    ((blockOps b 0).drop k).all p = true := by
  rw [blockOpsFrom_eq] at h₁
  rw [← List.take_append_drop s ((blockOps b 0).drop k), List.all_append, h₁, drop_drop', h₂]
  rfl

theorem opsAll_end {p : LOp → Bool} {b : List PStmt} {k : ℕ} (hk : blockSize b ≤ k) :
    ((blockOps b 0).drop k).all p = true := by
  rw [List.drop_eq_nil_of_le (by rw [blockOps_length]; exact hk)]
  rfl

/-- The checks of a large function on its temporaries, parameters and frame, `C` the counts of
its temporaries' cells. -/
noncomputable def smallOk (j : ℕ) (pf : Placed) (TL : List V) (C : NMap ℕ) : Bool :=
  let tf := guestTraced.getD j default
  let c : BigC := ⟨tf.core.name, pf.locs, TL, fsWant j, tf.core.params.length⟩
  (pf.fn.frameSize == fsWant j && isLoopName tf.core.name == tf.core.loop &&
      (!(loopsG[tf.core.name]?).any (·.registered) || Nat.blt (2 + tf.core.params.length) (fsWant j)) &&
      Nat.ble (2 + tf.core.params.length) (fsWant j)) &&
    consecFrom pf.locs tf.core.params 2 && cellsIn pf.locs TL (fsWant j) &&
    natsDistinct (TL.map fun t => (cellP pf.locs t).getD 0) &&
    (!(loopsG[tf.core.name]?).any (·.registered) || !c.Ts.contains (2 + tf.core.params.length)) &&
    idxNodup TL 0 && TL.all (fun t => c.T.contains t.idx) && tf.core.params.all (useOk c) &&
    TL.all (fun t => (cellP pf.locs t).isSome) &&
    TL.all (fun t => match cellP pf.locs t with
      | some n => C.get? n == some 1
      | none => false) &&
    distinctCells pf.locs TL {}

/-- **A large function's test from its parts**: the runs of statements (`hseg`), the checks on its
temporaries and frame (`hsmall`), the counts of its temporaries' cells, the frame pointers' cells and the instructions' test by chunks (`hcnt`, `hfp`, `hto`), the
scope walk by runs (`hscope`, `hfin`) and the remaining conjuncts on the placed body (`hrest`). -/
theorem cplOk_big {j : ℕ} {pf : Placed} {TL : List V} {C : NMap ℕ} {S : SSt}
    (hp : placedAt j = some pf)
    (hseg : segOk ⟨(guestTraced.getD j default).core.name, pf.locs, TL, fsWant j,
      (guestTraced.getD j default).core.params.length⟩ ((guestTraced.getD j default).core.body.drop 0) TL = true)
    (hsmall : smallOk j pf TL C = true)
    (hcnt : ((blockOps pf.fn.body 0).drop 0).foldl (cntStep (tmpCellSet pf.locs TL)) {} = C)
    {F : NMap Unit} (hfp : ((blockOps pf.fn.body 0).drop 0).foldl fpStep {} = F)
    (hto : ((blockOps pf.fn.body 0).drop 0).all (tmpOpOk (tmpCellSet pf.locs TL) F) = true)
    (hscope : scopeBlock (guestTraced.getD j default).rets ((guestTraced.getD j default).core.body.drop 0)
      ⟨(guestTraced.getD j default).trace.toList, addLive {} (guestTraced.getD j default).core.params,
        false⟩ = .ok S)
    (hfin : (match flushAt (guestTraced.getD j default).rets S with
      | .ok s => s.rest.isEmpty
      | .error _ => false) = true)
    (hrest : partsOk [4, 5, 6, 7] j pf = true) : cplOkAt j = true := by
  generalize htf : guestTraced.getD j default = tf at hseg hsmall hscope hfin
  have hrest' := hrest
  simp only [partsOk, cplParts, List.all_cons, List.all_nil, List.getD_cons_zero,
    List.getD_cons_succ, Bool.and_true, Bool.and_eq_true] at hrest'
  obtain ⟨r4, r5, r6, r7⟩ := hrest'
  rw [htf] at r4 r5 r7
  set c : BigC := ⟨tf.core.name, pf.locs, TL, fsWant j, tf.core.params.length⟩ with hc
  rw [List.drop_zero] at hseg
  have hseg' := hseg
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.isEmpty_iff] at hseg'
  obtain ⟨⟨⟨⟨⟨htl, huses⟩, hrv⟩, hruns⟩, hret⟩, hcalls⟩ := hseg'
  simp only [smallOk, htf, Bool.and_eq_true] at hsmall
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hhead, hpar⟩, hin⟩, hnd⟩, hself⟩, hidx⟩, hT⟩, hparU⟩, hsome⟩, hone⟩, hdc⟩ := hsmall
  have h0 : staticOk loopsG tf pf (fsWant j) = true := by
    refine staticOk_of (Ts := c.Ts) (by simp only [Bool.and_eq_true]; exact hhead) hpar hret (by rw [htl]; exact hin) (by rw [htl]; exact hnd)
      (by rw [List.drop_zero, hrv]; rfl) (by rw [htl]; rfl) hself (by rw [List.drop_zero]; exact hruns)
  have h3 : tmpsApartB tf pf = true :=
    tmpsApartB_of (T := c.T) (Ts := c.TA) (by rw [htl]; exact hidx) (by rw [htl]; exact hT)
      (by rw [List.drop_zero]; exact huses) hparU (by rw [htl]; rfl) hcnt (by rw [htl]; exact hsome)
      (by rw [htl]; exact hone) (by rw [htl]; exact hdc) hfp hto
  have h1 : scopedB tf = true := scopedB_of hscope hfin
  have h2 : noSelfCallB tf = true := by
    unfold noSelfCallB
    rw [hcalls]
    rfl
  subst htf
  exact cplOkAt_of hp (cplOkWith_of_parts (by
    simp only [partsOk, cplParts, List.all_cons, List.all_nil, List.getD_cons_zero,
      List.getD_cons_succ, h0, h1, h2, h3, r4, r5, r6, r7, Bool.and_self]))

end
end LeanVM.Guest.Backend.CplEval
