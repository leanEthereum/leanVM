/-
  LeanVM.Guest.B1.Gkr.GlCLayers

  `gkr_layers__L{o}`, its loop and `gkr_last_layers__L{r}_L{o}`, completely: given every layer
  `j < 4n + r` (`gkr_layer__L{j % 4}_L{o}` at `x_m = g^(j/4)`, `x_j = g^j`), they hold.
-/

module

public import LeanVM.Guest.B1.Tables.Basic
public import LeanVM.Guest.B1.Gkr.GlT
public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.CoreData
import LeanVM.Guest.ValRef
import LeanVM.Guest.B1.Common.Find
import LeanVM.Guest.Data.ValNames.«gkr_last_layers__L»
import LeanVM.Guest.Data.ValNames.«gkr_layers__L»
import LeanVM.Guest.Data.ValNames.«gkr_layers__L_loop0»
import LeanVM.Guest.StmtsAppend

/-!
# The radix-four layers' dispatch, completely

`gkr_layers__L{o}` runs its loop from `1` below `n_four = g^n` (four layers an iteration, each a
call of `gkr_layer__L{p}_L{o}` at `x_j = x_m^4·g^p`) and dispatches on `rem_g = g^r` to
`gkr_last_layers__L{r}_L{o}`, which calls the layers `4n .. 4n + r - 1`. Both chains of calls are
one template (`glcChain`: `x_j` computed `g` times the previous one).

* `GlLay`: layer `j`'s relation, what the caller supplies;
* `gls_complete`: every layer `j < 4n + r` gives `gkr_layers__L{o}` at `g^n`, `g^r`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1

@[expose] public section

/-- `gkr_layers__L{o}`. -/
def glcLsN : ℕ → String
  | 0 => name% «gkr_layers__L0»
  | _ => name% «gkr_layers__L1»

/-- `gkr_layers__L{o}`'s loop. -/
def glcLsLN : ℕ → String
  | 0 => name% «gkr_layers__L0_loop0»
  | _ => name% «gkr_layers__L1_loop0»

/-- `gkr_last_layers__L{r}_L{o}`. -/
def glcLastN : ℕ → ℕ → String
  | 0, 0 => name% «gkr_last_layers__L0_L0»
  | 0, _ => name% «gkr_last_layers__L0_L1»
  | 1, 0 => name% «gkr_last_layers__L1_L0»
  | 1, _ => name% «gkr_last_layers__L1_L1»
  | 2, 0 => name% «gkr_last_layers__L2_L0»
  | 2, _ => name% «gkr_last_layers__L2_L1»
  | _, 0 => name% «gkr_last_layers__L3_L0»
  | _, _ => name% «gkr_last_layers__L3_L1»

/-! ## The chain of layer calls -/

/-- Where call `p`'s `x_j` is: the first's given, the others' computed. -/
def glcXj (x0 c0 p : ℕ) : ℕ := if p = 0 then x0 else c0 + 2 * p - 1

/-- Call `p`: `x_j` as `g` times the previous one, then `gkr_layer__L{p}_L{o}`. -/
def glcStep (o : ℕ) (hd : List V) (x0 c0 p : ℕ) : List Stmt :=
  (if p = 0 then [] else [.atom (.const (.n (c0 + 2 * p - 2)) (word 2 0)),
      .atom (.mul (.n (c0 + 2 * p - 1)) (.n (glcXj x0 c0 (p - 1))) (.n (c0 + 2 * p - 2)))]) ⧺
  [.call (glName p o) (hd ++ [.n (glcXj x0 c0 p), .n 5, .n 6, .n 7, .n 8]) []]

/-- Calls `0 .. r - 1`. -/
def glcChain (o : ℕ) (hd : List V) (x0 c0 r : ℕ) : List Stmt :=
  ((List.range r).map (glcStep o hd x0 c0)).flatten

/-- `gkr_layers__L{o}`'s loop's body. -/
def glcLsLBody (o : ℕ) : List Stmt :=
  [.atom (.mul (.n (valf% «gkr_layers» «_loop0» "x4~0")) (.n (valf% «gkr_layers» «_loop0» "x_m")) (.n (valf% «gkr_layers» «_loop0» "x_m"))), .atom (.mul (.n (valf% «gkr_layers» «_loop0» "x4")) (.n (valf% «gkr_layers» «_loop0» "x4~0")) (.n (valf% «gkr_layers» «_loop0» "x4~0")))] ⧺
  glcChain o [.n (valf% «gkr_layers» «_loop0» "layers"), .n (valf% «gkr_layers» «_loop0» "rounds"), .n (valf% «gkr_layers» «_loop0» "gkr_pts"), .n (valf% «gkr_layers» «_loop0» "x_m")] 10 11 4 ⧺
  [.atom (.const (.n (valf% «gkr_layers» «_loop0» "s6#0")) (word 2 0)), .atom (.mul (.n (valf% «gkr_layers» «_loop0» "s6#1")) (.n (valf% «gkr_layers» «_loop0» "x_m")) (.n (valf% «gkr_layers» «_loop0» "s6#0"))),
    .atom (.add (.n (valf% «gkr_layers» «_loop0» "s6#2")) (.n (valf% «gkr_layers» «_loop0» "s6#1")) (.n (valf% «gkr_layers» «_loop0» "bound"))), .atom (.const (.n (valf% «gkr_layers» «_loop0» "s6#3")) (word 2 0)),
    .atom (.mul (.n (valf% «gkr_layers» «_loop0» "s6#4")) (.n (valf% «gkr_layers» «_loop0» "x_m")) (.n (valf% «gkr_layers» «_loop0» "s6#3"))),
    .callIf (.n (valf% «gkr_layers» «_loop0» "s6#2")) (glcLsLN o) [.n (valf% «gkr_layers» «_loop0» "s6#4"), .n (valf% «gkr_layers» «_loop0» "bound"), .n (valf% «gkr_layers» «_loop0» "layers"), .n (valf% «gkr_layers» «_loop0» "rounds"), .n (valf% «gkr_layers» «_loop0» "gkr_pts"), .n (valf% «gkr_layers» «_loop0» "start_g"), .n (valf% «gkr_layers» «_loop0» "g_bus_mu"), .n (valf% «gkr_layers» «_loop0» "tabs"), .n (valf% «gkr_layers» «_loop0» "stream")],
    .ret []]

/-- `gkr_last_layers__L{r}_L{o}`'s body. -/
def glcLastBody (r o : ℕ) : List Stmt :=
  glcChain o [.n (valf% «gkr_last_layers» "layers"), .n (valf% «gkr_last_layers» "rounds"), .n (valf% «gkr_last_layers» "gkr_pts"), .n (valf% «gkr_last_layers» "n_four")] 4 9 r ⧺
  [.atom (.const (.n (9 + 2 * (r - 1))) (word 0 0)), .ret [.n (9 + 2 * (r - 1))]]

/-- `gkr_layers__L{o}`'s body. -/
def glcLsBody (o : ℕ) : List Stmt :=
  [.atom (.const (.n (valf% «gkr_layers» "s0#0")) (word 1 0)), .atom (.add (.n (valf% «gkr_layers» "s0#1")) (.n (valf% «gkr_layers» "s0#0")) (.n (valf% «gkr_layers» "n_four"))),
    .atom (.const (.n (valf% «gkr_layers» "s0#2")) (word 1 0)),
    .callIf (.n (valf% «gkr_layers» "s0#1")) (glcLsLN o) [.n (valf% «gkr_layers» "s0#2"), .n (valf% «gkr_layers» "n_four"), .n (valf% «gkr_layers» "layers"), .n (valf% «gkr_layers» "rounds"), .n (valf% «gkr_layers» "gkr_pts"), .n (valf% «gkr_layers» "start_g"), .n (valf% «gkr_layers» "g_bus_mu"), .n (valf% «gkr_layers» "tabs"), .n (valf% «gkr_layers» "stream")],
    .atom (.mul (.n (valf% «gkr_layers» "m4~0")) (.n (valf% «gkr_layers» "n_four")) (.n (valf% «gkr_layers» "n_four"))), .atom (.mul (.n (valf% «gkr_layers» "m4")) (.n (valf% «gkr_layers» "m4~0")) (.n (valf% «gkr_layers» "m4~0"))),
    .dispatch (.n (valf% «gkr_layers» "rem_g")) [glcLastN 0 o, glcLastN 1 o, glcLastN 2 o, glcLastN 3 o]
      [.n (valf% «gkr_layers» "layers"), .n (valf% «gkr_layers» "rounds"), .n (valf% «gkr_layers» "gkr_pts"), .n (valf% «gkr_layers» "n_four"), .n (valf% «gkr_layers» "m4"), .n (valf% «gkr_layers» "start_g"), .n (valf% «gkr_layers» "g_bus_mu"), .n (valf% «gkr_layers» "tabs"), .n (valf% «gkr_layers» "stream")] [.n (valf% «gkr_layers» "done")],
    .atom (.const (.n (valf% «gkr_layers» "s3#0")) (word 0 0)), .ret [.n (valf% «gkr_layers» "s3#0")]]

def glcPar9 : List V := (List.range 9).map V.n

noncomputable def glcFnCheck (f : String) (b : List Stmt) : Bool :=
  match coreProgram.find? f with
  | some fn => decide (fn.params = glcPar9) && stmtsEqb fn.body b
  | none => false

theorem glcFnCheck_sound {f : String} {b : List Stmt} (h : glcFnCheck f b = true) :
    ∃ fn : Fn, coreProgram.find? f = some fn ∧ fn.params = glcPar9 ∧ fn.body = b := by
  unfold glcFnCheck at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, stmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

/-- `glcLsN`'s index. -/
def glcLsIdx : ℕ → ℕ
  | 0 => idx% «gkr_layers__L0»
  | _ => idx% «gkr_layers__L1»

/-- `glcLsLN`'s index. -/
def glcLsLIdx : ℕ → ℕ
  | 0 => idx% «gkr_layers__L0_loop0»
  | _ => idx% «gkr_layers__L1_loop0»

/-- `glcLastN`'s index. -/
def glcLastIdx : ℕ → ℕ → ℕ
  | 0, 0 => idx% «gkr_last_layers__L0_L0»
  | 0, _ => idx% «gkr_last_layers__L0_L1»
  | 1, 0 => idx% «gkr_last_layers__L1_L0»
  | 1, _ => idx% «gkr_last_layers__L1_L1»
  | 2, 0 => idx% «gkr_last_layers__L2_L0»
  | 2, _ => idx% «gkr_last_layers__L2_L1»
  | _, 0 => idx% «gkr_last_layers__L3_L0»
  | _, _ => idx% «gkr_last_layers__L3_L1»

/-- `glcFnCheck` at function `j`, found by its index (`coreProgram.find?` compares every name on the way). -/
noncomputable def glcFnCheckAt (j : ℕ) (f : String) (b : List Stmt) : Bool :=
  match coreProgram[j]? with
  | some fn => fn.name == f && decide (fn.params = glcPar9) && stmtsEqb fn.body b
  | none => false

theorem glcFnCheck_of_at {j : ℕ} {f : String} {b : List Stmt} (h : glcFnCheckAt j f b = true) :
    glcFnCheck f b = true := by
  unfold glcFnCheckAt at h
  split at h
  · rename_i fn hj
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [glcFnCheck, coreProgram_find?_at hj h.1.1]
    simp only [h.1.2, h.2, Bool.and_self]
  · exact absurd h (by simp)

private theorem glc_layers_checkAt : ∀ o < 2, glcFnCheckAt (glcLsIdx o) (glcLsN o) (glcLsBody o) = true ∧
    glcFnCheckAt (glcLsLIdx o) (glcLsLN o) (glcLsLBody o) = true ∧
    ∀ r < 4, glcFnCheckAt (glcLastIdx r o) (glcLastN r o) (glcLastBody r o) = true := by decide +kernel

theorem glc_layers_check : ∀ o < 2, glcFnCheck (glcLsN o) (glcLsBody o) = true ∧
    glcFnCheck (glcLsLN o) (glcLsLBody o) = true ∧
    ∀ r < 4, glcFnCheck (glcLastN r o) (glcLastBody r o) = true := fun o ho ↦
  have h := glc_layers_checkAt o ho
  ⟨glcFnCheck_of_at h.1, glcFnCheck_of_at h.2.1, fun r hr ↦ glcFnCheck_of_at (h.2.2 r hr)⟩

/-! ## Holding -/

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

theorem holds_glcChain {o : ℕ} {hd : List V} {x0 : ℕ} {X : E} (hX : σ (.n x0) = X)
    {c0 : ℕ} :
    ∀ (r : ℕ) {next : Prop},
      (∀ p, 1 ≤ p → p < r → σ (.n (c0 + 2 * p - 2)) = gen ∧ σ (.n (c0 + 2 * p - 1)) = X * gen ^ p) →
      (∀ p < r, C (glName p o) (hd.map σ ++ [X * gen ^ p, σ (.n 5), σ (.n 6), σ (.n 7), σ (.n 8)])
        []) → next → Stmt.HoldsList C rd σ (glcChain o hd x0 c0 r) next kret
  | 0, _, _, _, hn => hn
  | r + 1, next, hc, hcall, hn => by
    have hxj : ∀ p < r + 1, σ (.n (glcXj x0 c0 p)) = X * gen ^ p := by
      intro p hp
      unfold glcXj
      split
      · rename_i h; subst h; rw [hX, pow_zero, mul_one]
      · exact (hc p (by omega) hp).2
    rw [glcChain, List.range_succ, List.map_append, List.flatten_append, holdsList_append]
    refine holds_glcChain hX r (fun p h1 hp ↦ hc p h1 (by omega)) (fun p hp ↦ hcall p (by omega)) ?_
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      glcStep]
    rw [holdsList_append]
    have hcl : Stmt.HoldsList C rd σ [.call (glName r o) (hd ++ [.n (glcXj x0 c0 r), .n 5, .n 6,
        .n 7, .n 8]) []] next kret := by
      simp only [Stmt.HoldsList, Stmt.Holds, List.map_append, List.map_cons, List.map_nil, hxj r (by omega)]
      exact ⟨hcall r (by omega), hn⟩
    split
    · exact hcl
    · rename_i h0
      obtain ⟨h1, h2⟩ := hc r (by omega) (by omega)
      have hp := hxj (r - 1) (by omega)
      simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
      refine ⟨by rw [h1, word_gen], ?_, hcl⟩
      rw [h2, hp, h1, mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega)]

end Sem

/-- **Layer `j`'s relation**: `gkr_layer__L{j % 4}_L{o}` at `x_m = g^(j/4)`, `x_j = g^j`. -/
def GlLay (rd : Reader) (o : ℕ) (layers rounds pts start gmu tabs stream : E) (j : ℕ) : Prop :=
  coreProgram.Rel rd (glName (j % 4) o) [layers, rounds, pts, gen ^ (j / 4), gen ^ j, start, gmu,
    tabs, stream] []

theorem glc_pow4 (m : ℕ) : gen ^ m * gen ^ m * (gen ^ m * gen ^ m) = gen ^ (4 * m) := by ring

/-- **`gkr_last_layers__L{r}_L{o}`, completely.** -/
theorem glcLast_complete {rd : Reader} {o r n : ℕ} (ho : o < 2) (hr : r < 4)
    {layers rounds pts start gmu tabs stream : E}
    (hL : ∀ p < r, GlLay rd o layers rounds pts start gmu tabs stream (4 * n + p)) :
    coreProgram.Rel rd (glcLastN r o) [layers, rounds, pts, gen ^ n,
      gen ^ n * gen ^ n * (gen ^ n * gen ^ n), start, gmu, tabs, stream] [0] := by
  obtain ⟨fn, hf, hp, hb⟩ := glcFnCheck_sound ((glc_layers_check o ho).2.2 r hr)
  set X := gen ^ n * gen ^ n * (gen ^ n * gen ^ n) with hXd
  let args : List E := [layers, rounds, pts, gen ^ n, X, start, gmu, tabs, stream]
  let σ : Val := fun v ↦ if v.idx < 9 then args.getD v.idx 0
    else if v.idx = 9 + 2 * (r - 1) then 0
    else if v.idx % 2 = 1 then gen else X * gen ^ ((v.idx - 8) / 2)
  refine (rel_iff_sem hf _ _).mpr ⟨σ, ?_, ?_⟩
  · rw [hp]; simp [glcPar9, σ, List.range_succ, args]
  · rw [hb, glcLastBody, holdsList_append]
    refine holds_glcChain (X := X) (by simp [σ, args]) r (fun p hp1 hpr ↦ ?_) (fun p hp ↦ ?_) ?_
    · have i1 : ¬ 9 + 2 * p - 2 < 9 := by omega
      have i2 : 9 + 2 * p - 2 ≠ 9 + 2 * (r - 1) := by omega
      have i3 : (9 + 2 * p - 2) % 2 = 1 := by omega
      have j1 : ¬ 9 + 2 * p - 1 < 9 := by omega
      have j2 : 9 + 2 * p - 1 ≠ 9 + 2 * (r - 1) := by omega
      have j3 : ¬ (9 + 2 * p - 1) % 2 = 1 := by omega
      have j4 : (9 + 2 * p - 1 - 8) / 2 = p := by omega
      simp only [σ, i1, i2, i3, j1, j2, j3, j4, ↓reduceIte, and_self]
    · have h := hL p hp
      unfold GlLay at h
      rw [show (4 * n + p) % 4 = p by omega, show (4 * n + p) / 4 = n by omega, pow_add, ← hXd.trans (glc_pow4 n)] at h
      simpa [σ, args] using h
    · simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
      have h9 : ¬ 9 + 2 * (r - 1) < 9 := by omega
      exact ⟨by simp [σ, h9, word_zero], by simp [σ, h9]⟩

theorem glc_isInK_one : IsInK (1 : E) := by simpa using gen_pow_isInK 0

/-- **An iteration of `gkr_layers__L{o}`'s loop** at `g^m`: its four layers and the next
iteration give it. -/
theorem glsl_iter {rd : Reader} {o m : ℕ} (ho : o < 2) {N layers rounds pts start gmu tabs stream : E}
    (hN : IsInK N)
    (hL : ∀ p < 4, GlLay rd o layers rounds pts start gmu tabs stream (4 * m + p))
    (hnext : gen ^ m * gen + N ≠ 0 → coreProgram.Rel rd (glcLsLN o)
      [gen ^ m * gen, N, layers, rounds, pts, start, gmu, tabs, stream] []) :
    coreProgram.Rel rd (glcLsLN o) [gen ^ m, N, layers, rounds, pts, start, gmu, tabs, stream] [] := by
  obtain ⟨fn, hf, hp, hb⟩ := glcFnCheck_sound (glc_layers_check o ho).2.1
  set x := gen ^ m with hx
  set X := x * x * (x * x) with hXd
  let σ : Val := fun v ↦ if v.idx < 9 then
      [x, N, layers, rounds, pts, start, gmu, tabs, stream].getD v.idx 0
    else if v.idx = 9 then x * x else if v.idx = 10 then X
    else if v.idx < 17 then (if v.idx % 2 = 1 then gen else X * gen ^ ((v.idx - 10) / 2))
    else [gen, x * gen, x * gen + N, gen, x * gen].getD (v.idx - 17) 0
  refine (rel_iff_sem hf _ _).mpr ⟨σ, ?_, ?_⟩
  · rw [hp]; simp [glcPar9, σ, List.range_succ]
  · rw [hb, glcLsLBody, holdsList_append, holdsList_append]
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds]
    refine ⟨by simp [σ], by simp [σ, X], ?_⟩
    refine holds_glcChain (X := X) (by simp [σ]) 4 (fun p hp1 hpr ↦ ?_) (fun p hp ↦ ?_) ?_
    · have i1 : ¬ 11 + 2 * p - 2 < 9 := by omega
      have i2 : 11 + 2 * p - 2 ≠ 9 := by omega
      have i3 : 11 + 2 * p - 2 ≠ 10 := by omega
      have i4 : 11 + 2 * p - 2 < 17 := by omega
      have i5 : (11 + 2 * p - 2) % 2 = 1 := by omega
      have j1 : ¬ 11 + 2 * p - 1 < 9 := by omega
      have j2 : 11 + 2 * p - 1 ≠ 9 := by omega
      have j3 : 11 + 2 * p - 1 ≠ 10 := by omega
      have j4 : 11 + 2 * p - 1 < 17 := by omega
      have j5 : ¬ (11 + 2 * p - 1) % 2 = 1 := by omega
      have j6 : (11 + 2 * p - 1 - 10) / 2 = p := by omega
      simp only [σ, i1, i2, i3, i4, i5, j1, j2, j3, j4, j5, j6, ↓reduceIte, and_self]
    · have h := hL p hp
      unfold GlLay at h
      rw [show (4 * m + p) % 4 = p by omega, show (4 * m + p) / 4 = m by omega, pow_add,
        ← glc_pow4 m, ← hx, ← hXd] at h
      simpa [σ] using h
    · simp only [List.map_cons, List.map_nil]
      refine ⟨by simp [σ, word_gen], by simp [σ], by simp [σ], by simp [σ, word_gen],
        by simp [σ], ?_, fun hne ↦ ?_, trivial⟩
      · simp only [σ]; norm_num
        exact isInK_add (isInK_mul (gen_pow_isInK _) (by simpa using gen_pow_isInK 1)) hN
      · have := hnext (by simpa [σ] using hne)
        simpa [σ] using this

/-- **`gkr_layers__L{o}`'s loop, completely**: its four layers at every `m < n` give the loop from
`1` below `g^n`. -/
theorem glsl_complete {rd : Reader} {o n : ℕ} (ho : o < 2) (hn : 0 < n) (hnb : n < 2 ^ 30)
    {layers rounds pts start gmu tabs stream : E}
    (hL : ∀ j < 4 * n, GlLay rd o layers rounds pts start gmu tabs stream j) :
    coreProgram.Rel rd (glcLsLN o) [1, gen ^ n, layers, rounds, pts, start, gmu, tabs, stream] [] := by
  have hit : ∀ m < n, ∀ p < 4, GlLay rd o layers rounds pts start gmu tabs stream (4 * m + p) :=
    fun m hm p hp ↦ hL _ (by omega)
  have key : ∀ t, t < n → coreProgram.Rel rd (glcLsLN o)
      [gen ^ (n - 1 - t), gen ^ n, layers, rounds, pts, start, gmu, tabs, stream] [] := by
    intro t
    induction t with
    | zero =>
      intro _
      refine glsl_iter ho (gen_pow_isInK _) (hit _ (by omega)) fun hne ↦ ?_
      rw [← pow_succ, show n - 1 - 0 + 1 = n by omega, e_add_self] at hne
      exact absurd rfl hne
    | succ t ih =>
      intro ht
      refine glsl_iter ho (gen_pow_isInK _) (hit _ (by omega)) fun _ ↦ ?_
      rw [← pow_succ, show n - 1 - (t + 1) + 1 = n - 1 - t by omega]
      exact ih (by omega)
  have := key (n - 1) (by omega)
  rwa [show n - 1 - (n - 1) = 0 by omega, pow_zero] at this

/-- **`gkr_layers__L{o}`, completely**: every layer `j < 4n + r` gives it at `n_four = g^n`,
`rem_g = g^r`, returning `0`. -/
theorem gls_complete {rd : Reader} {o n r : ℕ} (ho : o < 2) (hr : r < 4) (hnb : n < 2 ^ 30)
    {layers rounds pts start gmu tabs stream : E}
    (hL : ∀ j < 4 * n + r, GlLay rd o layers rounds pts start gmu tabs stream j) :
    coreProgram.Rel rd (glcLsN o) [layers, rounds, pts, gen ^ n, gen ^ r, start, gmu, tabs, stream]
      [0] := by
  obtain ⟨fn, hf, hp, hb⟩ := glcFnCheck_sound (glc_layers_check o ho).1
  set X := gen ^ n * gen ^ n * (gen ^ n * gen ^ n) with hXd
  let σ : Val := fun v ↦ if v.idx < 9 then
      [layers, rounds, pts, gen ^ n, gen ^ r, start, gmu, tabs, stream].getD v.idx 0
    else [1, 1 + gen ^ n, 1, gen ^ n * gen ^ n, X, 0, 0].getD (v.idx - 9) 0
  refine (rel_iff_sem hf _ _).mpr ⟨σ, ?_, ?_⟩
  · rw [hp]; simp [glcPar9, σ, List.range_succ]
  · rw [hb, glcLsBody]
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil]
    refine ⟨by simp [σ, word_one], by simp [σ], by simp [σ, word_one], ?_, fun hne ↦ ?_,
      by simp [σ], by simp [σ, hXd], ⟨r, by simp; omega, ?_, ?_⟩, by simp [σ, word_zero],
      by simp [σ]⟩
    · simp only [σ]; norm_num
      exact isInK_add glc_isInK_one (gen_pow_isInK _)
    · have hn0 : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · exfalso; apply hne; simp only [σ]; norm_num; rw [h0, pow_zero, e_add_self]
        · exact h0
      have := glsl_complete (rd := rd) ho hn0 hnb (layers := layers) (rounds := rounds) (pts := pts)
        (start := start) (gmu := gmu) (tabs := tabs) (stream := stream) (fun j hj ↦ hL j (by omega))
      simpa [σ] using this
    · simp only [σ]; norm_num; exact gen_pow_eq_ofK r
    · have := glcLast_complete (rd := rd) (n := n) ho hr (layers := layers) (rounds := rounds)
        (pts := pts) (start := start) (gmu := gmu) (tabs := tabs) (stream := stream)
        (fun p hp ↦ hL _ (by omega))
      interval_cases r <;> simpa [σ, hXd] using this

end
end LeanVM.Guest.B1.Tables
