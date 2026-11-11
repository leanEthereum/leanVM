/-
  LeanVM.Guest.B1.Place.OsBos

  open_stacked's frame-size bound at each stack size: its frame, its buffers, a bound per call
  statement; the named callees' words bounds; the placed completeness statements it bounds.
-/

module

public import LeanVM.Guest.B1.Whir.Template
public import LeanVM.Guest.B1.Whir.CompleteIface
public import LeanVM.Guest.B1.Bits.QueryWindowsAt
public import LeanVM.Guest.Memory.Size

/-!
# The frame-size bound of an opening arm

The arm of size `m` (`open_stacked__L{m}`, stack log `μ = minOpenLog + m`) has the body `osBody (osCfg m)`
(`Whir/Template.lean`, checked equal to the core IR by `Whir/Data*.lean`): straight-line atoms,
calls and dispatches on the rate's selector, then its `ret`. A rate is a dispatch's arm, so a
static bound of the body covers every rate.

* `osSizesL c`: the sizes of the body's `HeapBuf`s, in allocation order (the head's ten fixed
  buffers, each level's row weights, the tail's challenges, the point and `point1`, `basis_d`, the
  scales and the inner sums).
* `osCallees c`: each call statement's callees, in order: a call's one, a dispatch's every arm.
  `osCalleeNames c`: all of them.
* `osCallB fs Bk names`: a call statement entered within `Bk f` words or skipped (its frame `fs f`)
  at its costliest callee; `osKidsB`, their total; `osBos fs Bk name c`: the frame `fs name`, the
  buffers, the calls. `osBosAt fs Bnd μ`: at the arm of `μ`.
* `OsLeafBounds fs Bnd`: every callee of every arm has its trees within `Bnd` of its name (each is
  statically bounded: the leaves, `level_positions`, `level_queries`, `level_residual`).
* `OsOut`, `open_stacked_completeAtD_Spec`, `open_stacked_completeAtB_Spec`: the arm of `μ`,
  called on the rate's selector, is complete placed (within `osBosAt` words) on every accepting
  run of `whirOpen μ r target` with no zero challenge and openings that agree in the caps.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL)

@[expose] public section

/-! ## The buffers and the calls -/

/-- The sizes of the body's `HeapBuf`s, in allocation order: the head's (`final_msg`,
`level_roots`, `fold_challenges`, `level_betas`, `level_mus`, `query_positions`,
`query_win_ptrs`, `win_tabs`, `ood_z`, `ood`), each level's row weights (`osQueries`), the tail's
challenges, and the finish's (the point, `point1`, `basis_d`, the scales, the inner sums). -/
def osSizesL (c : OsCfg) : List ℕ :=
  let n := c.levels.length
  [c.yrLen, 2 * n, c.nFolds, n, n, n * ligPosCap, n * ligPosCap, 128, n * ligColsCap,
    n * oodSlots] ++ List.replicate n c.maxIl ++
  [yrLogCap, pointCap, pointCap, n * ligColsCap, n, n + 1]

/-- The callees of a call statement: a call's, a conditional call's, a dispatch's arms. -/
def Stmt.calleesS : Stmt → Option (List String)
  | .call f _ _ => some [f]
  | .callIf _ f _ => some [f]
  | .dispatch _ fs _ _ => some fs
  | _ => none

/-- The body's call statements' callees, in order. -/
def osCallees (c : OsCfg) : List (List String) := (osBody c).filterMap Stmt.calleesS

/-- Every callee of the body. -/
def osCalleeNames (c : OsCfg) : List String := (osCallees c).flatten

/-! ## The bound -/

/-- A call statement: entered within `Bk f` words or skipped (its frame `fs f`), at its costliest
callee. -/
def osCallB (fs Bk : String → ℕ) (names : List String) : ℕ :=
  (names.map fun f ↦ max (fs f) (Bk f)).foldl max 0

/-- The body's calls' total, one `osCallB` per call statement. -/
def osKidsB (fs Bk : String → ℕ) (c : OsCfg) : ℕ := ((osCallees c).map (osCallB fs Bk)).sum

/-- **`open_stacked`'s frame-size bound** at a configuration. -/
def osBos (fs Bk : String → ℕ) (name : String) (c : OsCfg) : ℕ :=
  fs name + (osSizesL c).sum + osKidsB fs Bk c

/-- `open_stacked`'s frame-size bound at the arm of the stack log `μ`. -/
def osBosAt (fs Bnd : String → ℕ) (μ : ℕ) : ℕ :=
  osBos fs Bnd (openName μ) (osCfg (μ - minOpenLog))

theorem le_foldl_max_init : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a
  | [], _ => le_rfl
  | y :: l, a => le_trans (le_max_left a y) (le_foldl_max_init l (max a y))

theorem le_foldl_max : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → ∀ a : ℕ, x ≤ l.foldl max a
  | [], _, h, _ => absurd h List.not_mem_nil
  | y :: l, x, h, a => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_trans (le_max_right a x) (le_foldl_max_init l _)
    · exact le_foldl_max h _

/-- **A callee within its statement's bound.** -/
theorem le_osCallB {fs Bk : String → ℕ} {names : List String} {f : String} (h : f ∈ names) :
    max (fs f) (Bk f) ≤ osCallB fs Bk names :=
  le_foldl_max (List.mem_map.mpr ⟨f, h, rfl⟩ : max (fs f) (Bk f) ∈ names.map fun f ↦ max (fs f) (Bk f)) 0

/-! ## The callees' bounds -/

/-- The number of opening arms, `MAX_STACKED_LOG - MIN_EXECUTION_STACKED_LOG + 1`. -/
abbrev osArms : ℕ := ligNSizes

/-- **The callees' words bounds**: every callee `f` of every arm has its trees within `Bnd f`
words. -/
def OsLeafBounds (fs : String → ℕ) (Bnd : String → ℕ) : Prop :=
  ∀ m < osArms, ∀ f ∈ osCalleeNames (osCfg m), TotalLe coreProgram fs f (fun _ ↦ Bnd f)

/-! ## The statements -/

/-- What `open_stacked` returns and the buffers it hands back. -/
def OsOut (μ : ℕ) (w : WhirEnd) : List E → Layout → Prop := fun rets Lout ↦
  ∃ b b1 : ℕ, rets = [w.target, ofK (addressOfIndex b), ofK (addressOfIndex b1), w.inner,
      w.residual] ∧
    Lout = [(b, w.point ++ List.replicate (pointCap - μ) 0),
      (b1, w.point.map (1 + ·) ++ List.replicate (pointCap - μ) 1)]

/-- **`open_stacked` is complete placed at every stack log and rate**: with the frame runs fitting
their frames, their cells consecutive, on memories defined below `2^κ`, `7 ≤ κ`
(`decode_query_windows`' range checks), on every accepting run of `whirOpen μ r target` from
`⟨capOf S, []⟩` with no zero challenge and openings that agree in the caps, the words at the
cursor among the caller's words, the arm of `μ` called on the rate's selector is `CompleteAtD`,
returning the run's claim, its two point buffers' pointers, its glued weight and its residual's
value (`OsOut`). -/
def open_stacked_completeAtD_Spec : Prop :=
  ∀ (μ r : ℕ), minOpenLog ≤ μ → μ ≤ 30 → 1 ≤ r → r ≤ 4 →
    ∀ (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ), Lift.RunsFit fs cert →
      RunsConsec cert → 7 ≤ κ →
      ∀ (S : KeccakState) (root : Digest) (target cur : E) (xs : List E) (os : List (List Opening))
        (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
        RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots' →
        NoZeroChallenge μ r target S xs os root → CapsAgree μ r target S xs os root →
        ∀ Lin : Layout, (∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs) →
          CompleteAtD fs cert κ (openName μ) Lin
            (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur])
            (OsOut μ w)

/-- **`open_stacked` is complete placed within `osBosAt` words**: `open_stacked_completeAtD_Spec`
by a tree of at most `osBosAt fs Bnd μ` words, given the callees' words bounds `Bnd`. -/
def open_stacked_completeAtB_Spec : Prop :=
  ∀ (μ r : ℕ), minOpenLog ≤ μ → μ ≤ 30 → 1 ≤ r → r ≤ 4 →
    ∀ (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (Bnd : String → ℕ),
      Lift.RunsFit fs cert → RunsConsec cert → 7 ≤ κ → OsLeafBounds fs Bnd →
      ∀ (S : KeccakState) (root : Digest) (target cur : E) (xs : List E) (os : List (List Opening))
        (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
        RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots' →
        NoZeroChallenge μ r target S xs os root → CapsAgree μ r target S xs os root →
        ∀ Lin : Layout, (∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs) →
          CompleteAtB fs cert κ (openName μ) Lin
            (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur])
            (OsOut μ w) (osBosAt fs Bnd μ)

end
end LeanVM.Guest.B1
