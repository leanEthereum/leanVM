/-
  LeanVM.Guest.CoreMode.Route

  What ties a function's core data to the deployed guest's tables, so that the tree track's honest
  frames give its honest valuations.
-/

module

public import LeanVM.Guest.CoreMode.Core
public import LeanVM.Guest.CoreMode.CoreResG
public import LeanVM.Guest.CoreMode.LoopBC
public import LeanVM.Guest.Bridge.ProgAlDefs
public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.Bridge.JumpCellsPack

/-!
# Core data of the deployed guest

`CfOk Cf`: `Cf` is compiled function `j`'s: its entry, its core function (`coreOf j`), its
alignment's context (`Bridge.ctxOf j`), and its frame holds its values where the tree track's
honest frames have them (`honB`): its body the core route's shape, its parameters `V.n k` at cells `2 + k`, its returned values at
their cells, each dereferenced pointer at its certificate cell within the frame, no hint-only cell; not the prologue;
and its heap certificate's residuals of the families the honest frames make true (`resOk`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **What the route's checks read of a compiled function** (`FnV.of`): its values' cells, its hint-only values and
its frame size, which a generated check states from the function's own data (`FnV.of_tie`) rather than look up. -/
structure FnV where
  locs : List ℕ
  ex : List (ℕ × ℕ)
  fs : ℕ

/-- Compiled function `j`'s (`certOf`, `Bridge.extraOf`, `B2C.fsN`). -/
noncomputable def FnV.of (j : ℕ) : FnV := ⟨(certOf j).locs, Bridge.extraOf j, B2C.fsN j⟩

theorem FnV.of_locs (j : ℕ) : (FnV.of j).locs = (certOf j).locs := rfl
theorem FnV.of_ex (j : ℕ) : (FnV.of j).ex = Bridge.extraOf j := rfl
theorem FnV.of_fs (j : ℕ) : (FnV.of j).fs = B2C.fsN j := rfl

/-- A value at its cell `c v` within the frame of `D`, not a hint-only value. -/
def valCell (c : V → ℕ) (D : FnV) (v : V) : Bool :=
  (D.ex.lookup v.idx).isNone && decide (v.idx < 2 ^ 30) && decide (2 ≤ c v) && decide (c v < D.fs)

/-- A dereferenced pointer (`ptrOf`) at its cell `c`, within the frame, not a hint-only value. -/
def ptrCellAt (c : V → ℕ) (D : FnV) : Stmt → Bool
  | .atom a => match ptrOf a with
    | some p => valCell c D p
    | none => true
  | _ => true

/-- A `ret`'s values at their cells `c`, within the frame, not hint-only values. -/
def retCellAt (c : V → ℕ) (D : FnV) : Stmt → Bool
  | .ret vs => vs.all (valCell c D)
  | _ => true

/-- A value at its certificate cell within the frame, not a hint-only value. -/
noncomputable abbrev cellB (j : ℕ) : V → Bool := valCell (B2C.cellJ j) (FnV.of j)

/-- A dereferenced pointer at its certificate cell. -/
noncomputable abbrev ptrCellB (j : ℕ) : Stmt → Bool := ptrCellAt (B2C.cellJ j) (FnV.of j)

/-- A `ret`'s values at their certificate cells. -/
noncomputable abbrev retCellB (j : ℕ) : Stmt → Bool := retCellAt (B2C.cellJ j) (FnV.of j)

/-- A frame run's first value at its certificate cell, not a hint-only value. -/
noncomputable def faCellB (j : ℕ) : Stmt → Bool
  | .atom (.frameAddr _ (r :: _)) => ((Bridge.extraOf j).lookup r.idx).isNone && decide (r.idx < 2 ^ 30)
  | _ => true

/-- Where frame run cells are guaranteed (`faNeed`), the frame runs' first values at their cells (`HonB.fa`). -/
noncomputable def faOkB (j : ℕ) (Cf : CFun) : Bool := !faNeed Cf || stmtsAll (faCellB j) Cf.fn.body

/-- No `match` among the statements. -/
def noMatch (l : List Stmt) : Bool :=
  l.all fun s ↦ match s with
    | .match_ .. => false
    | _ => true

/-- No `dispatch` among the statements. -/
def noDsp (l : List Stmt) : Bool :=
  l.all fun s ↦ match s with
    | .dispatch .. => false
    | _ => true

/-- Statement `s` is the atom `b`. -/
def isAtom (b : Atom) : Stmt → Bool
  | .atom a => decide (a = b)
  | _ => false

/-- Atom `b` is once among the statements of `B`, nested ones included. -/
def onceB (B : List Stmt) (b : Atom) : Bool := Nat.beq ((Bridge.stmtsOf B).countP (isAtom b)) 1

/-- A top-level atom of `ss` that is once among the statements of `B`. -/
def onceAfter (B ss : List Stmt) : Bool :=
  ss.any fun s ↦ match s with
    | .atom b => onceB B b
    | _ => false

/-- **The `match`es of a branch of a top-level `ite`**, `B` the body: at the branch's top level, each on a
selector at its cell used by a top-level atom before it (`seen`, the body's then the branch's, each atom remembered
by `up`), no `match` in its arms, and a top-level atom after it in the branch once in `B` (a path through the other
branch walks none of its events). -/
def selBrK (ok : V → Bool) (B : List Stmt) (up : Atom → List Atom → List Atom) :
    List Atom → List Stmt → Bool
  | _, [] => true
  | seen, .atom a :: ss => selBrK ok B up (up a seen) ss
  | seen, .match_ x arms :: ss => ok x && seen.any (fun a ↦ decide (x ∈ Memory.atomUses a)) &&
      noMatch (Bridge.stmtsArms arms) && onceAfter B ss && selBrK ok B up seen ss
  | seen, .ite _ z n :: ss => noMatch (Bridge.stmtsOf z) && noMatch (Bridge.stmtsOf n) && selBrK ok B up seen ss
  | seen, .ret _ :: ss => selBrK ok B up seen ss
  | seen, .call .. :: ss => selBrK ok B up seen ss
  | seen, .callIf .. :: ss => selBrK ok B up seen ss
  | seen, .dispatch .. :: ss => selBrK ok B up seen ss

/-- **Each `match` and `dispatch` of a body at its top level, or a `match` at the top level of a top-level
`ite`'s branch** (`selBrK`), `B` the body: its selector used by a top-level atom before it (`seen`, each atom
remembered by `up`; a dispatch's, or a parameter of `ps`) and at its cell (`ok`); no other `match` nested, none
past a `ret`. -/
def selGoK (ok : V → Bool) (ps : List V) (B : List Stmt) (up : Atom → List Atom → List Atom) :
    List Atom → List Stmt → Bool
  | _, [] => true
  | seen, .atom a :: ss => selGoK ok ps B up (up a seen) ss
  | seen, .match_ x arms :: ss => ok x && seen.any (fun a ↦ decide (x ∈ Memory.atomUses a)) &&
      noMatch (Bridge.stmtsArms arms) && selGoK ok ps B up seen ss
  | seen, .ite _ z n :: ss => selBrK ok B up seen z && selBrK ok B up seen n && selGoK ok ps B up seen ss
  | _, .ret _ :: ss => noMatch (Bridge.stmtsOf ss) && noDsp (Bridge.stmtsOf ss)
  | seen, .call .. :: ss => selGoK ok ps B up seen ss
  | seen, .callIf .. :: ss => selGoK ok ps B up seen ss
  | seen, .dispatch x .. :: ss => ok x && (ps.contains x || seen.any fun a ↦ decide (x ∈ Memory.atomUses a)) &&
      selGoK ok ps B up seen ss

/-- `selBrK` remembering every top-level atom. -/
noncomputable abbrev selBr (j : ℕ) (B : List Stmt) : List Atom → List Stmt → Bool := selBrK (cellB j) B List.cons

/-- `selGoK` remembering every top-level atom. -/
noncomputable abbrev selGo (j : ℕ) (ps : List V) (B : List Stmt) : List Atom → List Stmt → Bool :=
  selGoK (cellB j) ps B List.cons

/-- An atom using a value of the bitset `S`. -/
def keepB (S : ℕ) (a : Atom) : Bool := (Memory.atomUses a).any fun v ↦ Nat.testBit S v.idx

/-- `seen` with `a` when it uses a value of the bitset `S`, the selectors the generator names: a long body's
selectors' check remembers only those top-level atoms (`selGo_of_keepL`), not every one. -/
def keepIn (S : ℕ) (a : Atom) (seen : List Atom) : List Atom := bif keepB S a then a :: seen else seen

/-- Function `j`'s frame (`D`) holds `fn`'s parameters at cells `2 + k` and its pointers and returned values at their
cells, `c` its values' cells; `j` not the prologue. -/
noncomputable def honAt (c : V → ℕ) (D : FnV) (j : ℕ) (fn : Fn) : Bool :=
  D.locs.all (fun c ↦ Nat.blt c (2 ^ Bridge.cellBits)) && (bodyCore fn.body || loopBC fn) &&
    stmtsAll (ptrCellAt c D) fn.body && paramsN fn.params 0 &&
    ((List.range fn.params.length).all fun k ↦ Nat.beq (c (V.n k)) (2 + k) && decide (2 + k < D.fs)) &&
    stmtsAll (retCellAt c D) fn.body && Nat.blt 0 j &&
    (selGoK (valCell c D) fn.params fn.body List.cons [] fn.body || loopBC fn)

/-- `honAt` at the certificate's cells. -/
noncomputable abbrev honB (j : ℕ) (fn : Fn) : Bool := honAt (B2C.cellJ j) (FnV.of j) j fn

/-- `honAt` but for its passes over the body (`bodyCore`, `ptrCellAt`, `retCellAt`, the selectors), which a long body
checks apart. -/
def honRestAt (c : V → ℕ) (D : FnV) (j : ℕ) (fn : Fn) : Bool :=
  D.locs.all (fun c ↦ Nat.blt c (2 ^ Bridge.cellBits)) && paramsN fn.params 0 &&
    ((List.range fn.params.length).all fun k ↦ Nat.beq (c (V.n k)) (2 + k) && decide (2 + k < D.fs)) && Nat.blt 0 j

/-- `honRestAt` at the certificate's cells. -/
noncomputable abbrev honRest (j : ℕ) (fn : Fn) : Bool := honRestAt (B2C.cellJ j) (FnV.of j) j fn

theorem honB_of {j : ℕ} {fn : Fn} (h1 : (bodyCore fn.body || loopBC fn) = true)
    (h2 : (Bridge.stmtsOf fn.body).all (ptrCellB j) = true) (h3 : (Bridge.stmtsOf fn.body).all (retCellB j) = true)
    (h4 : (selGo j fn.params fn.body [] fn.body || loopBC fn) = true) (h5 : honRest j fn = true) : honB j fn = true := by
  simp only [honRest, honRestAt, Bool.and_eq_true] at h5
  obtain ⟨⟨⟨r1, r2⟩, r3⟩, r4⟩ := h5
  simp only [honB, honAt, stmtsAll_eq, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨r1, h1⟩, h2⟩, r2⟩, r3⟩, h3⟩, r4⟩, h4⟩

/-! ## The selectors' check, remembering fewer atoms -/

/-- `up` remembers no atom but the one it is given. -/
def UpSub (up : Atom → List Atom → List Atom) : Prop := ∀ a s, ∀ b ∈ up a s, b ∈ a :: s

theorem keepIn_sub (S : ℕ) : UpSub (keepIn S) := fun a s b hb ↦ by
  unfold keepIn at hb
  generalize keepB S a = c at hb
  cases c
  · exact List.mem_cons_of_mem _ hb
  · exact hb

private theorem up_mono {up : Atom → List Atom → List Atom} (hu : UpSub up) {a : Atom} {s s' : List Atom}
    (h : ∀ b ∈ s', b ∈ s) : ∀ b ∈ up a s', b ∈ a :: s := fun b hb ↦
  (List.mem_cons.mp (hu a s' b hb)).elim (fun e ↦ e ▸ List.mem_cons_self) fun hb ↦ List.mem_cons_of_mem _ (h b hb)

private theorem any_mono {p : Atom → Bool} {s s' : List Atom} (h : ∀ b ∈ s', b ∈ s) (ha : s'.any p = true) :
    s.any p = true :=
  let ⟨b, hb, hp⟩ := List.any_eq_true.mp ha; List.any_eq_true.mpr ⟨b, h b hb, hp⟩

theorem selBr_of_up {ok : V → Bool} {B : List Stmt} {up : Atom → List Atom → List Atom} (hu : UpSub up) :
    ∀ (ss : List Stmt) (s s' : List Atom), (∀ b ∈ s', b ∈ s) → selBrK ok B up s' ss = true → selBrK ok B List.cons s ss = true
  | [], _, _, _, _ => by simp [selBrK]
  | st :: ss, s, s', hs, h => by
    cases st with
    | atom a => simp only [selBrK] at h ⊢; exact selBr_of_up hu ss _ _ (up_mono hu hs) h
    | match_ x arms =>
      simp only [selBrK, Bool.and_eq_true] at h ⊢
      exact ⟨⟨⟨⟨h.1.1.1.1, any_mono hs h.1.1.1.2⟩, h.1.1.2⟩, h.1.2⟩, selBr_of_up hu ss _ _ hs h.2⟩
    | ite c z n =>
      simp only [selBrK, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, selBr_of_up hu ss _ _ hs h.2⟩
    | ret _ => simp only [selBrK] at h ⊢; exact selBr_of_up hu ss _ _ hs h
    | call f a r => simp only [selBrK] at h ⊢; exact selBr_of_up hu ss _ _ hs h
    | callIf c f a => simp only [selBrK] at h ⊢; exact selBr_of_up hu ss _ _ hs h
    | dispatch x fs a r => simp only [selBrK] at h ⊢; exact selBr_of_up hu ss _ _ hs h

theorem selGo_of_up {ok : V → Bool} {ps : List V} {B : List Stmt} {up : Atom → List Atom → List Atom} (hu : UpSub up) :
    ∀ (ss : List Stmt) (s s' : List Atom), (∀ b ∈ s', b ∈ s) → selGoK ok ps B up s' ss = true →
      selGoK ok ps B List.cons s ss = true
  | [], _, _, _, _ => by simp [selGoK]
  | st :: ss, s, s', hs, h => by
    cases st with
    | atom a => simp only [selGoK] at h ⊢; exact selGo_of_up hu ss _ _ (up_mono hu hs) h
    | match_ x arms =>
      simp only [selGoK, Bool.and_eq_true] at h ⊢
      exact ⟨⟨⟨h.1.1.1, any_mono hs h.1.1.2⟩, h.1.2⟩, selGo_of_up hu ss _ _ hs h.2⟩
    | ite c z n =>
      simp only [selGoK, Bool.and_eq_true] at h ⊢
      exact ⟨⟨selBr_of_up hu z _ _ hs h.1.1, selBr_of_up hu n _ _ hs h.1.2⟩, selGo_of_up hu ss _ _ hs h.2⟩
    | ret _ => simp only [selGoK] at h ⊢; exact h
    | call f a r => simp only [selGoK] at h ⊢; exact selGo_of_up hu ss _ _ hs h
    | callIf c f a => simp only [selGoK] at h ⊢; exact selGo_of_up hu ss _ _ hs h
    | dispatch x fs args rets =>
      simp only [selGoK, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
      exact ⟨⟨h.1.1, h.1.2.imp id (any_mono hs)⟩, selGo_of_up hu ss _ _ hs h.2⟩

/-- **Core data of the deployed guest's function `j`.** -/
def CfOk (Cf : CFun) : Prop :=
  ∃ j, j < nFns ∧ (fnOf j).entryPc = Cf.frame.entry ∧ coreOf j = Cf.fn ∧ Bridge.ctxOf j = Cf.X ∧
    (honB j Cf.fn && resOk Cf && glOk Cf && faOkB j Cf) = true


/-- **Core data of the deployed guest**, from the tables' entries of function `j` and its checks. -/
theorem cfOk_of {j : ℕ} {f : CompiledFunction} {cf : Fn} {C : Check.Cert} {P : B2C.Plumb} {ex : List (ℕ × ℕ)}
    {en : List (String × ℕ)} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} {Cf : CFun} (hj : j < nFns)
    (hf : fnOf j = f) (hcf : coreOf j = cf) (hC : certOf j = C.withPows Data.powTree) (hP : B2C.plumbOf j = P)
    (ht : (Bridge.extraOf j, Bridge.entsOf j, Bridge.adviceOf j) = (ex, en, d)) (he : f.entryPc = Cf.frame.entry)
    (hfn : cf = Cf.fn)
    (hX : Bridge.AlignCtx.ofData C.locs ex f.entryPc (j == 1) P Data.powTree Data.jtTrie en Bridge.alignHalt
      f.instructionCount = Cf.X)
    (hb : (honB j Cf.fn && resOk Cf && glOk Cf && faOkB j Cf) = true) : CfOk Cf := by
  simp only [Prod.mk.injEq] at ht
  obtain ⟨hex, hen, -⟩ := ht
  have hl : (certOf j).locs = C.locs := by rw [hC]; cases C; rfl
  refine ⟨j, hj, by rw [hf, he], by rw [hcf, hfn], ?_, hb⟩
  rw [← hX, Bridge.ctxOf, hl, hex, hen, hf, hP]

/-- **`FnV.of` from the tables at `j`** (the glue's `Fn.«k».tie`) and its frame size (`Checked.fsEq`). -/
theorem FnV.of_tie {j : ℕ} {f : CompiledFunction} {cf : Fn} {C : Check.Cert} {P : B2C.Plumb} {ex : List (ℕ × ℕ)}
    {en : List (String × ℕ)} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} {fs : ℕ}
    (ht : fnOf j = f ∧ coreOf j = cf ∧ certOf j = C.withPows Data.powTree ∧ B2C.plumbOf j = P ∧
      (Bridge.extraOf j, Bridge.entsOf j, Bridge.adviceOf j) = (ex, en, d)) (hfs : B2C.fsN j = fs) :
    FnV.of j = ⟨C.locs, ex, fs⟩ := by
  obtain ⟨-, -, hC, -, he⟩ := ht
  simp only [Prod.mk.injEq] at he
  rw [FnV.of, hC, he.1, hfs]
  cases C
  rfl

/-- `cfOk_of` from the tables at `j` as one fact (the glue's `Fn.«k».tie`, so the route names a function by its
key, its index only in the glue). -/
theorem cfOk_of_tie {j : ℕ} {f : CompiledFunction} {cf : Fn} {C : Check.Cert} {P : B2C.Plumb} {ex : List (ℕ × ℕ)}
    {en : List (String × ℕ)} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} {Cf : CFun} (hj : j < nFns)
    (ht : fnOf j = f ∧ coreOf j = cf ∧ certOf j = C.withPows Data.powTree ∧ B2C.plumbOf j = P ∧
      (Bridge.extraOf j, Bridge.entsOf j, Bridge.adviceOf j) = (ex, en, d)) (he : f.entryPc = Cf.frame.entry)
    (hfn : cf = Cf.fn)
    (hX : Bridge.AlignCtx.ofData C.locs ex f.entryPc (j == 1) P Data.powTree Data.jtTrie en Bridge.alignHalt
      f.instructionCount = Cf.X)
    (hb : (honB j Cf.fn && resOk Cf && glOk Cf && faOkB j Cf) = true) : CfOk Cf :=
  cfOk_of hj ht.1 ht.2.1 ht.2.2.1 ht.2.2.2.1 ht.2.2.2.2 he hfn hX hb

end

end LeanVM.Guest.CoreMode
