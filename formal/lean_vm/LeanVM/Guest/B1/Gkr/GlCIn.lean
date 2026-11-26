/-
  LeanVM.Guest.B1.Gkr.GlCIn

  A radix-four layer `gkr_layer__L{p}_L{o}` and its loop load from any region holding the layer's
  slots, point row, round records and the words at the slot's cursor.
-/

module

public import LeanVM.Guest.B1.Gkr.GlCurs
public import LeanVM.Guest.B1.Gkr.GlCMid
public import LeanVM.Guest.B1.Gkr.GlLoop
public import LeanVM.Guest.B1.Tables.Kids.Walk
public import LeanVM.Guest.B1.Tables.Kids.Loop9
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«gkr_layer__L»
import LeanVM.Guest.Data.ValNames.«gkr_layer__L_loop0»

/-!
# A radix-four layer, loading from a region

* `gll_relIn`: iteration `k < K` of `gkr_layer__L{p}_L{o}_loop0` on the records from `head·g^(7k)`
  (`14` words), the rows `qrow·g^(8k)`, `nqrow·g^(8k)` (`8` words each), reading `32` words at
  the record's cursor, loads from `R`, by the depth of its derivation.
* `GlIn`: what layer `j` reads, in `R`; `gl_relIn`: with it, `gkr_layer__L{p}_L{o}` at
  `x_m = g^m`, `x_j = g^(4m + p)` loads from `R`, its loop by `gll_relIn` (the records' cursors
  by `gl_curs`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A run from `p·g^a` inside the run from `p`. -/
theorem ptrIn_pow {R : ℕ → Prop} {p : E} {a B B' : ℕ} (h : PtrIn R p B) (hle : a + B' ≤ B) :
    PtrIn R (p * gen ^ a) B' :=
  ptrIn_mul (ptrIn_mono h hle)

/-! ## The loop -/

/-- The loop's next record and guard. -/
def glLoopPostA : List Stmt :=
  (List.range 5).map (fun k ↦ .atom (.load (.n ((valf% «gkr_layer» «_loop0» "nxt[8]@8") + k)) (.n (valf% «gkr_layer» «_loop0» "rd")) (7 + k))) ++
  [.atom (.const (.n (valf% «gkr_layer» «_loop0» "s12#0")) (word (2 ^ 32) 0)), .atom (.mul (.n (valf% «gkr_layer» «_loop0» "s12#1")) (.n (valf% «gkr_layer» «_loop0» "cur")) (.n (valf% «gkr_layer» «_loop0» "s12#0"))),
    .atom (.load (.n (valf% «gkr_layer» «_loop0» "s12#1")) (.n (valf% «gkr_layer» «_loop0» "rd")) 12), .atom (.load (.n (valf% «gkr_layer» «_loop0» "nclaim@8")) (.n (valf% «gkr_layer» «_loop0» "rd")) 13),
    .atom (.const (.n (valf% «gkr_layer» «_loop0» "s15#0")) (word 2 0)), .atom (.mul (.n (valf% «gkr_layer» «_loop0» "s15#1")) (.n (valf% «gkr_layer» «_loop0» "y")) (.n (valf% «gkr_layer» «_loop0» "s15#0"))),
    .atom (.add (.n (valf% «gkr_layer» «_loop0» "s15#2")) (.n (valf% «gkr_layer» «_loop0» "s15#1")) (.n (valf% «gkr_layer» «_loop0» "bound"))), .atom (.const (.n (valf% «gkr_layer» «_loop0» "s15#3")) (word 2 0)),
    .atom (.mul (.n (valf% «gkr_layer» «_loop0» "s15#4")) (.n (valf% «gkr_layer» «_loop0» "y")) (.n (valf% «gkr_layer» «_loop0» "s15#3")))]

/-- The loop's next call. -/
def glLoopNext (nm : String) : Stmt := .callIf (.n (valf% «gkr_layer» «_loop0» "s15#2")) nm [.n (valf% «gkr_layer» «_loop0» "s15#4"), .n (valf% «gkr_layer» «_loop0» "bound"), .n (valf% «gkr_layer» «_loop0» "head"), .n (valf% «gkr_layer» «_loop0» "qrow"), .n (valf% «gkr_layer» «_loop0» "nqrow"), .n (valf% «gkr_layer» «_loop0» "tabs")]

/-- The loop's statements before its `ret`. -/
def glLoopPreK (nm : String) : List Stmt :=
  glLoopPre ++ glLoopRounds ++ glLoopPostA ++ [glLoopNext nm]

theorem glLoopBody_eq (nm : String) : glLoopBody nm = glLoopPreK nm ++ [.ret []] := by
  simp [glLoopBody, glLoopPreK, glLoopPostA, glLoopNext, glLoopPost]

theorem gll_all {f : Stmt → Bool} (h : (glLoopPre ++ glLoopRounds ++ glLoopPostA).all f = true)
    (nm : String) (hp : f (glLoopNext nm) = true) : (glLoopPreK nm).all f = true := by
  rw [glLoopPreK, List.all_append, h, List.all_cons, hp]; rfl

theorem gll_flat (nm : String) : (glLoopPreK nm).all Stmt.flat = true :=
  gll_all (by decide +kernel) nm rfl

theorem gll_noDisp (nm : String) : (glLoopPreK nm).all noDispB = true :=
  gll_all (by decide +kernel) nm rfl

theorem gll_noLoadIte (nm : String) : (glLoopPreK nm).all noLoadIte = true :=
  gll_all (by decide +kernel) nm rfl

theorem gll_loads (nm : String) :
    (glLoopPreK nm).all (loadsViaB [(valf% «gkr_layer» «_loop0» "rd", 14), (valf% «gkr_layer» «_loop0» "pt", 8), (valf% «gkr_layer» «_loop0» "npt", 8), (valf% «gkr_layer» «_loop0» "cur", 32)]) = true :=
  gll_all (by decide +kernel) nm rfl

theorem gll_calls (nm : String) : (glLoopPreK nm).filterMap Main.Stmt.callS =
    [(some (.n (valf% «gkr_layer» «_loop0» "s15#2")), nm, [.n (valf% «gkr_layer» «_loop0» "s15#4"), .n (valf% «gkr_layer» «_loop0» "bound"), .n (valf% «gkr_layer» «_loop0» "head"), .n (valf% «gkr_layer» «_loop0» "qrow"), .n (valf% «gkr_layer» «_loop0» "nqrow"), .n (valf% «gkr_layer» «_loop0» "tabs")], [])] := by
  rw [glLoopPreK, List.filterMap_append,
    show (glLoopPre ++ glLoopRounds ++ glLoopPostA).filterMap Main.Stmt.callS = [] by
      decide +kernel]
  rfl

/-- **The layer's loop loads from `R`**, every iteration `k < K`. -/
theorem gll_relIn {p o : ℕ} (hp : p < 4) (ho : o < 2) {rd : Reader} {R : ℕ → Prop} {K : ℕ}
    {head qrow nqrow tabs : E} (hh : PtrIn R head (7 * K + 7)) (hq : PtrIn R qrow (8 * K))
    (hn : PtrIn R nqrow (8 * K))
    (hcur : ∀ k < K, ∀ c, LoadHolds rd (head * gen ^ (7 * k)) 5 c → PtrIn R c 32) :
    ∀ d k, k < K → coreProgram.relN rd d (glLoopName p o) [gen ^ k, gen ^ K, head, qrow, nqrow,
        tabs] [] →
      coreProgram.RelIn rd R (glLoopName p o) [gen ^ k, gen ^ K, head, qrow, nqrow, tabs] [] := by
  intro d
  induction d with
  | zero => intro k _ h; exact h.elim
  | succ d ih =>
    intro k hk h
    obtain ⟨fn, hf, hsem⟩ := h
    obtain ⟨fn', hf', hps, hb⟩ := glIs_sound (glIs_loops p hp o ho)
    rw [hf] at hf'
    obtain rfl := Option.some.inj hf'
    refine relIn_of_flat hf (by rw [hb, glLoopBody_eq]) (gll_flat _) hsem
      (hnl := gll_noLoadIte _) fun σ hpar hhl ↦ ?_
    rw [hps] at hpar
    simp only [glLoopParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, List.cons.injEq, and_true] at hpar
    obtain ⟨p0, p1, p2, p3, p4, p5⟩ := hpar
    rw [hb, glLoopBody, List.append_assoc, holdsList_append, holdsList_noRet _ glLoopPre_noRet,
      holdsList_append, holdsList_noRet glLoopRounds (glRounds_noRet ..)] at hhl
    obtain ⟨hpre, -, hpost⟩ := hhl
    rw [glLoopPre, tb_holdsList_append_noRet (by decide), tb_holdsList_append_noRet (by decide),
      tb_holdsList_mapAtoms] at hpre
    obtain ⟨⟨hptr, -⟩, hrec⟩ := hpre
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hptr hrec
    obtain ⟨m6, m7, m8, m9, m10, m11, m12, m13, m14, m15⟩ := hptr
    obtain ⟨l17, -⟩ := hrec
    rw [glLoopPost, holdsList_append, holdsList_noRet _ (by decide), tb_holdsList_mapAtoms]
      at hpost
    obtain ⟨-, hpost⟩ := hpost
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hpost
    obtain ⟨-, -, -, -, c341, m342, a343, c344, m345, -, hnext, -⟩ := hpost
    rw [tb_word_gen] at c341 c344
    have e6 : σ (.n (valf% «gkr_layer» «_loop0» "rd")) = head * gen ^ (7 * k) := by
      rw [m10, m9, m8, m7, m6, p0, p2]; ring
    have e9 : σ (.n (valf% «gkr_layer» «_loop0» "y8")) = gen ^ (8 * k) := by rw [m13, m12, m11, p0]; ring
    refine ⟨fun s hs ↦ dispOk_of_noDisp (List.all_eq_true.mp (gll_noDisp _) s hs),
      loads_via (gll_loads _) fun pb hpb ↦ ?_, fun c hc ht ↦ ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hpb
      rcases hpb with rfl | rfl | rfl | rfl
      · rw [e6]; exact ptrIn_pow hh (by omega)
      · rw [m14, e9, p3]; exact ptrIn_pow hq (by omega)
      · rw [m15, e9, p4]; exact ptrIn_pow hn (by omega)
      · rw [e6] at l17; exact hcur k hk _ l17
    · rw [filterMap_callSF (gll_noDisp _), gll_calls] at hc
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
      subst hc
      simp only [Main.mkCall, decide_eq_true_eq] at ht ⊢
      have e345 : σ (.n (valf% «gkr_layer» «_loop0» "s15#4")) = gen ^ (k + 1) := by rw [m345, c344, p0, pow_succ]
      have e343 : σ (.n (valf% «gkr_layer» «_loop0» "s15#2")) = gen ^ (k + 1) + gen ^ K := by
        rw [a343, m342, c341, p0, p1, pow_succ]
      have hk1 : k + 1 < K := by
        rcases Nat.lt_or_ge (k + 1) K with h' | h'
        · exact h'
        · exfalso
          apply ht
          rw [e343, show k + 1 = K by omega, e_add_eq_zero_iff]
      have hrel := hnext ht
      simp only [List.map_cons, List.map_nil, e345, p1, p2, p3, p4, p5] at hrel ⊢
      exact ih (k + 1) hk1 hrel

/-! ## The layer -/

/-- The loop's guard. -/
def glG (p : ℕ) : ℕ := if p = 0 then 59 else 61 + 78 * p

/-- The loop's arguments. -/
def glLA (p : ℕ) : List V :=
  if p = 0 then [.n 60, .n (valf% «gkr_layer» "x_m"), .n (valf% «gkr_layer» "head"), .n (valf% «gkr_layer» "point_row"), .n 62, .n (valf% «gkr_layer» "tabs")]
  else [.n (62 + 78 * p), .n (valf% «gkr_layer» "x_m"), .n (valf% «gkr_layer» "head"), .n (64 + 78 * p), .n (66 + 78 * p), .n (valf% «gkr_layer» "tabs")]

/-- The layer's load pointers and their runs: the slot, the slot's cursor, the point row, the
head record, the tail record, the tail's rows and its cursor. -/
def glInTbl (p o : ℕ) : List (ℕ × ℕ) :=
  [(15, 30), (21, 8 * p), (52, 42 + 2 * p), (53, 7), (glW p, 7), (71 + glD p, 2),
    (74 + glD p, 2), (80 + glD p, 4 * (2 - o) + 12)]

/-- `gkr_layer__L{p}_L{o}`'s statements before its `ret`. -/
noncomputable def glPreK (p o : ℕ) : List Stmt := (glBody p o (glLoopName p o)).dropLast

/-- The layer's kernel facts: its `ret` last, flat, no dispatch, its loads through `glInTbl`,
its one call the loop's. -/
noncomputable def glInCheck (p o : ℕ) : Bool :=
  tbStmtsEqb (glBody p o (glLoopName p o)) (glPreK p o ++ [.ret []]) &&
    (glPreK p o).all Stmt.flat && (glPreK p o).all noDispB && (glPreK p o).all noLoadIte &&
    (glPreK p o).all (loadsViaB (glInTbl p o)) &&
    tbStmtsEqb ((glPreK p o).filterMap Main.Stmt.callS |>.map fun x ↦ Stmt.callIf
        (x.1.getD (.n 0)) x.2.1 x.2.2.1) [.callIf (.n (glG p)) (glLoopName p o) (glLA p)] &&
    ((glPreK p o).filterMap Main.Stmt.callS).all fun x ↦ x.1.isSome && x.2.2.2.isEmpty

theorem gl_inCheck : ∀ p < 4, ∀ o < 2, glInCheck p o = true := by decide +kernel

theorem gl_inFacts {p o : ℕ} (hp : p < 4) (ho : o < 2) :
    glBody p o (glLoopName p o) = glPreK p o ++ [.ret []] ∧ (glPreK p o).all Stmt.flat = true ∧
      (glPreK p o).all noDispB = true ∧ (glPreK p o).all noLoadIte = true ∧
      (glPreK p o).all (loadsViaB (glInTbl p o)) = true ∧
      (glPreK p o).filterMap Main.Stmt.callS =
        [(some (.n (glG p)), glLoopName p o, glLA p, [])] := by
  have h := gl_inCheck p hp o ho
  simp only [glInCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨tbStmtsEqb_sound h1, h2, h3, h4, h5, ?_⟩
  have e := tbStmtsEqb_sound h6
  generalize (glPreK p o).filterMap Main.Stmt.callS = l at e h7
  match l, e, h7 with
  | [(some c, f, args, rets)], e, h7 =>
    simp only [List.map_cons, List.map_nil, Option.getD_some, List.cons.injEq, and_true,
      Stmt.callIf.injEq] at e
    simp only [List.all_cons, List.all_nil, Option.isSome_some, Bool.true_and, Bool.and_true,
      List.isEmpty_iff] at h7
    obtain ⟨rfl, rfl, rfl⟩ := e
    subst h7
    rfl
  | [(none, f, args, rets)], _, h7 => simp at h7

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- The slot, its position, the point row and the head record, from the prefix. -/
theorem gl_prePtrs (h : Stmt.HoldsList C rd σ glPre True kret) {j sh : ℕ}
    (hx : σ (.n (valf% «gkr_layer» "x_j")) = gen ^ j) (hsg : σ (.n (valf% «gkr_layer» "start_g")) = gen ^ (2 - sh)) (hsh : sh < 2) :
    σ (.n (valf% «gkr_layer» "layer")) = σ (.n (valf% «gkr_layer» "layers")) * gen ^ (10 * (2 * j + 2 - sh)) ∧ LoadHolds rd (σ (.n (valf% «gkr_layer» "layer"))) 9 (σ (.n (valf% «gkr_layer» "round_pos"))) ∧
      σ (.n (valf% «gkr_layer» "point_row")) = σ (.n (valf% «gkr_layer» "gkr_pts")) * gen ^ (40 * (j + 1)) ∧ σ (.n (valf% «gkr_layer» "head")) = σ (.n (valf% «gkr_layer» "rounds")) * σ (.n (valf% «gkr_layer» "round_pos")) := by
  have hnr := glPre_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have m9 := a 0 (.mul (.n (valf% «gkr_layer» "x_layer~0")) (.n (valf% «gkr_layer» "x_j")) (.n (valf% «gkr_layer» "x_j"))) (by decide +kernel)
  have m10 := a 1 (.mul (.n (valf% «gkr_layer» "x_layer")) (.n (valf% «gkr_layer» "x_layer~0")) (.n (valf% «gkr_layer» "start_g"))) (by decide +kernel)
  have m11 := a 2 (.mul (.n (valf% «gkr_layer» "layer~0")) (.n (valf% «gkr_layer» "x_layer")) (.n (valf% «gkr_layer» "x_layer"))) (by decide +kernel)
  have m12 := a 3 (.mul (.n (valf% «gkr_layer» "layer~1")) (.n (valf% «gkr_layer» "layer~0")) (.n (valf% «gkr_layer» "layer~0"))) (by decide +kernel)
  have m13 := a 4 (.mul (.n (valf% «gkr_layer» "layer~2")) (.n (valf% «gkr_layer» "layer~1")) (.n (valf% «gkr_layer» "x_layer"))) (by decide +kernel)
  have m14 := a 5 (.mul (.n (valf% «gkr_layer» "layer~3")) (.n (valf% «gkr_layer» "layer~2")) (.n (valf% «gkr_layer» "layer~2"))) (by decide +kernel)
  have m15 := a 6 (.mul (.n (valf% «gkr_layer» "layer")) (.n (valf% «gkr_layer» "layers")) (.n (valf% «gkr_layer» "layer~3"))) (by decide +kernel)
  have l44 := a 22 (.load (.n (valf% «gkr_layer» "round_pos")) (.n (valf% «gkr_layer» "layer")) 9) (by decide +kernel)
  have c45 := a 23 (.const (.n (valf% «gkr_layer» "point_row~0")) (word 2 0)) (by decide +kernel)
  have m46 := a 24 (.mul (.n (valf% «gkr_layer» "point_row~1")) (.n (valf% «gkr_layer» "x_j")) (.n (valf% «gkr_layer» "point_row~0"))) (by decide +kernel)
  have m47 := a 25 (.mul (.n (valf% «gkr_layer» "point_row~2")) (.n (valf% «gkr_layer» "point_row~1")) (.n (valf% «gkr_layer» "point_row~1"))) (by decide +kernel)
  have m48 := a 26 (.mul (.n (valf% «gkr_layer» "point_row~3")) (.n (valf% «gkr_layer» "point_row~2")) (.n (valf% «gkr_layer» "point_row~2"))) (by decide +kernel)
  have m49 := a 27 (.mul (.n (valf% «gkr_layer» "point_row~4")) (.n (valf% «gkr_layer» "point_row~3")) (.n (valf% «gkr_layer» "point_row~1"))) (by decide +kernel)
  have m50 := a 28 (.mul (.n (valf% «gkr_layer» "point_row~5")) (.n (valf% «gkr_layer» "point_row~4")) (.n (valf% «gkr_layer» "point_row~4"))) (by decide +kernel)
  have m51 := a 29 (.mul (.n (valf% «gkr_layer» "point_row~6")) (.n (valf% «gkr_layer» "point_row~5")) (.n (valf% «gkr_layer» "point_row~5"))) (by decide +kernel)
  have m52 := a 30 (.mul (.n (valf% «gkr_layer» "point_row~7")) (.n (valf% «gkr_layer» "point_row~6")) (.n (valf% «gkr_layer» "point_row~6"))) (by decide +kernel)
  have m53 := a 31 (.mul (.n (valf% «gkr_layer» "point_row")) (.n (valf% «gkr_layer» "gkr_pts")) (.n (valf% «gkr_layer» "point_row~7"))) (by decide +kernel)
  have m54 := a 32 (.mul (.n (valf% «gkr_layer» "head")) (.n (valf% «gkr_layer» "rounds")) (.n (valf% «gkr_layer» "round_pos"))) (by decide +kernel)
  simp only [Atom.Holds] at m9 m10 m11 m12 m13 m14 m15 l44 c45 m46 m47 m48 m49 m50 m51 m52
  simp only [Atom.Holds] at m53 m54
  rw [tb_word_gen] at c45
  have e10 : σ (.n (valf% «gkr_layer» "x_layer")) = gen ^ (2 * j + 2 - sh) := by
    rw [m10, m9, hx, hsg, ← pow_add, ← pow_add, show j + j + (2 - sh) = 2 * j + 2 - sh by omega]
  refine ⟨?_, l44, ?_, m54⟩
  · rw [m15, m14, m13, m12, m11, e10, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    ring_nf
  · rw [m53, m52, m51, m50, m49, m48, m47, m46, c45, hx, ← pow_succ]
    ring

/-- The tail record's pointer. -/
theorem gl_tailW {p : ℕ} (h : Stmt.HoldsList C rd σ (glTailSetup p) True kret) :
    σ (.n (glW p)) = σ (.n (valf% «gkr_layer» "head")) * σ (.n (valf% «gkr_layer» "x_m")) ^ 7 := by
  rcases Nat.eq_zero_or_pos p with rfl | hp1
  · simp only [glTailSetup, ↓reduceIte, glTailSetup0, List.cons_append, Stmt.HoldsList,
      Stmt.Holds, Atom.Holds] at h
    obtain ⟨a0, a1, a2, a3, a4, -⟩ := h
    simp only [glW, ↓reduceIte]
    rw [a4, a3, a2, a1, a0]; ring
  · have hp0 : p ≠ 0 := by omega
    simp only [glTailSetup, hp0, ↓reduceIte, glTailSetupP, List.cons_append, Stmt.HoldsList,
      Stmt.Holds, Atom.Holds] at h
    obtain ⟨a0, a1, a2, a3, a4, -⟩ := h
    simp only [glW, hp0, ↓reduceIte]
    rw [a4, a3, a2, a1, a0]; ring

/-- The loop's guard and arguments. -/
theorem gl_loopCallV {p : ℕ} (hp4 : p < 4) {nm : String} (h : Stmt.HoldsList C rd σ (glLoopCall p nm) True kret) :
    σ (.n (glG p)) = 1 + σ (.n (valf% «gkr_layer» "x_m")) ∧ (glLA p).map σ = [1, σ (.n (valf% «gkr_layer» "x_m")), σ (.n (valf% «gkr_layer» "head")),
      σ (.n (valf% «gkr_layer» "point_row")) * gen ^ (2 * p), σ (.n (valf% «gkr_layer» "point_row")) * gen ^ (2 * p) * gen ^ 42, σ (.n (valf% «gkr_layer» "tabs"))] := by
  rcases Nat.eq_zero_or_pos p with rfl | hp1
  · simp only [glLoopCall, ↓reduceIte, glLoopCall0, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
      List.map_cons, List.map_nil] at h
    obtain ⟨c59, a60, c61, c62, m63, -⟩ := h
    rw [tb_word_one] at c59 c61
    rw [tb_word_two_pow (by norm_num)] at c62
    refine ⟨by simp only [glG, ↓reduceIte]; rw [a60, c59], ?_⟩
    simp [glLA, c61, m63, c62]
  · have hp0 : p ≠ 0 := by omega
    simp only [glLoopCall, hp0, ↓reduceIte, glLoopCallP, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
      List.map_cons, List.map_nil] at h
    obtain ⟨c1, a2, c3, c4, m5, c6, m7, -⟩ := h
    rw [tb_word_one] at c1 c3
    rw [tb_word_two_pow (by omega)] at c4 c6
    refine ⟨by simp only [glG, hp0, ↓reduceIte]; rw [a2, c1], ?_⟩
    simp only [glLA, hp0, ↓reduceIte, List.map_cons, List.map_nil, c3, m5, m7, c4, c6,
      List.cons.injEq, and_true, true_and]
    rw [mul_assoc, ← pow_add, Nat.add_comm (2 * p) 42]

end Sem

/-- **What layer `j` reads, in `R`**: the slot of `L = 2j + 2 - o` through the next slot's
stores, with its position `pos` and cursor `cj`; its point row (`L + 43` words); its records from
`rounds·pos` (`7 (j / 4) + 7` words); the `4L + 12` words from `cj`. -/
def GlIn (rd : Reader) (R : ℕ → Prop) (layers pts rounds : E) (o j : ℕ) : Prop :=
  ∃ pos cj : E,
    PtrIn R (layers * gen ^ (10 * (2 * j + 2 - o))) 30 ∧
    LoadHolds rd layers (10 * (2 * j + 2 - o) + 9) pos ∧
    LoadHolds rd layers (10 * (2 * j + 2 - o) + 5) cj ∧
    PtrIn R (pts * gen ^ (40 * (j + 1))) (2 * j + 2 - o + 43) ∧
    PtrIn R (rounds * pos) (7 * (j / 4) + 7) ∧ PtrIn R cj (4 * (2 * j + 2 - o) + 12)

/-- **`gkr_layer__L{p}_L{o}` loads from `R`**, layer `j = 4m + p`'s words in `R` (`GlIn`). -/
theorem gl_relIn {p o m : ℕ} (hp : p < 4) (ho : o < 2) (hj : 4 * m + p < 2 ^ 30) {rd : Reader}
    {R : ℕ → Prop} {layers rounds pts gmu tabs stream : E}
    (hin : GlIn rd R layers pts rounds o (4 * m + p))
    (h : coreProgram.Rel rd (glName p o) [layers, rounds, pts, gen ^ m, gen ^ (4 * m + p),
      gen ^ (2 - o), gmu, tabs, stream] []) :
    coreProgram.RelIn rd R (glName p o) [layers, rounds, pts, gen ^ m, gen ^ (4 * m + p),
      gen ^ (2 - o), gmu, tabs, stream] [] := by
  obtain ⟨fn, hf, hps, hb⟩ := glIs_sound (glIs_layers p hp o ho)
  obtain ⟨hbe, hfl, hnd, hnl, hld, hcs⟩ := gl_inFacts hp ho
  obtain ⟨pos, cj, hRS, hpos, hcj, hRP, hRR, hRC⟩ := hin
  set j := 4 * m + p with hjd
  set L := 2 * j + 2 - o with hL
  refine relIn_of_flatRel hf (by rw [hb, hbe]) hfl h (hnl := hnl) fun σ hpar hhl ↦ ?_
  rw [hps] at hpar
  simp only [glParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq, and_true] at hpar
  obtain ⟨p0, p1, p2, p3, p4, p5, -, p7, -⟩ := hpar
  rw [hb] at hhl
  obtain ⟨e21, -, hcall, hrec, e77, -⟩ := gl_curs (C := coreProgram.Rel rd) (fun _ _ _ h ↦ h) hp ho
    hhl p3 p4 p5 hj (by rw [p0]; exact hcj)
  rw [glBody] at hhl
  simp only [List.append_assoc] at hhl
  rw [holdsList_append, holdsList_noRet _ glPre_noRet, holdsList_append,
    holdsList_noRet (glHeadRounds p) (glRounds_noRet ..), holdsList_append,
    holdsList_noRet _ (glHeadStore_noRet p), holdsList_append,
    holdsList_noRet _ (glLoopCall_noRet p _), holdsList_append,
    holdsList_noRet _ (glTailSetup_noRet p)] at hhl
  obtain ⟨hPre, -, -, hLC, hTS, -⟩ := hhl
  obtain ⟨e15, l44, e53, e54⟩ := gl_prePtrs hPre p4 p5 ho
  rw [p0] at e15
  rw [p2] at e53
  rw [p1] at e54
  have e44 : σ (.n (valf% «gkr_layer» "round_pos")) = pos := by
    rw [e15, tb_loadHolds_mul_gen_pow] at l44; exact tb_loadHolds_unique l44 hpos
  rw [e44] at e54
  obtain ⟨e68, e71, -⟩ := gl_tailSetup hp hTS
  have eW := gl_tailW hTS
  obtain ⟨eG, eA⟩ := gl_loopCallV hp hLC
  have hm4 : j / 4 = m := by omega
  refine ⟨fun s hs ↦ dispOk_of_noDisp (List.all_eq_true.mp hnd s hs),
    loads_via hld fun pb hpb ↦ ?_, fun c hc ht ↦ ?_⟩
  · simp only [glInTbl, List.mem_cons, List.not_mem_nil, or_false] at hpb
    rcases hpb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [e15]; exact hRS
    · rw [e21]; exact ptrIn_mono hRC (by omega)
    · rw [e53]; exact ptrIn_mono hRP (by omega)
    · rw [e54]; exact ptrIn_mono hRR (by omega)
    · rw [eW, e54, p3, ← pow_mul, Nat.mul_comm m 7]; exact ptrIn_pow hRR (by omega)
    · rw [show σ (.n (71 + glD p)) = pts * gen ^ (40 * (j + 1)) * gen ^ (2 * p + 8 * m) by
        rw [e68, e53, p3]; ring]
      exact ptrIn_pow hRP (by omega)
    · rw [show σ (.n (74 + glD p)) = pts * gen ^ (40 * (j + 1)) * gen ^ (2 * p + 8 * m + 42) by
        rw [e71, e68, e53, p3]; ring]
      exact ptrIn_pow hRP (by omega)
    · rw [e77]; exact ptrIn_pow hRC (by omega)
  · rw [filterMap_callSF hnd, hcs] at hc
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
    subst hc
    simp only [Main.mkCall, decide_eq_true_eq] at ht ⊢
    rw [eG] at ht
    obtain ⟨d, hd⟩ := hcall ht
    rw [p3] at ht
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · exfalso; apply ht; rw [h0, pow_zero, e_add_self]
      · exact h0
    rw [e54] at hrec
    rw [eA, List.map_nil]
    rw [p3, p7, e54, e53] at hd ⊢
    rw [show (1 : E) = gen ^ 0 from (pow_zero _).symm] at hd ⊢
    exact gll_relIn hp ho (K := m) (ptrIn_mono hRR (by omega)) (ptrIn_pow hRP (by omega))
      (ptrIn_pow (ptrIn_pow hRP (B' := 42 + 8 * m) (by omega)) (by omega))
      (fun k hk c hc ↦ by
        rw [tb_loadHolds_unique hc (hrec k (by omega))]
        exact ptrIn_pow hRC (by omega)) d 0 hm0 hd

end
end LeanVM.Guest.B1.Tables
