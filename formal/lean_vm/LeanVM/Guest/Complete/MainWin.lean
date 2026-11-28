module

public import LeanVM.Guest.Complete.MainDup
public import LeanVM.Guest.Complete.MainEval
public import LeanVM.Guest.Complete.SegA
import LeanVM.Guest.CoreRef
import LeanVM.Guest.B1.Main.Interface

/-!
# `main`'s placed completeness from its body's window

`MainWindowAt al k s w`: on the node `(s, w)`, `main`'s body before its `ret []` (`main_shape`'s
`mPre`, the DA branch, `mMid`, the leaf's branch, `mPost`) is one `SegA` window at the root (frame
`0`, cursor `B2C.fs "main"`), on the memories holding the statement's digest at the header: an
honest valuation `σ0` fixed before the memory and one per memory `σ rd`, its own words `Wo`, its
callees by `KidsAtF` from the end of its `HeapBuf`s, its tree's `Post` (the honest pushes stream by
stream, every node exact) from its callees', its end below `2^57` (each callee within `2^52` of its
cursor, `SegT`). `mainCompleteA_of_window` closes it into `MainCompleteA` by `callAtA_segRd`, the end
within `2^30` from any bound of a placed `main`'s end below `2^63` to `2^30` (`MainEndWithin`,
`within_deployed`: the words below `2^63` have a memory, and the count bounds the tree on it).

`mainCalleesA_to_mainFromVs_of_window` takes `MainWindowFromCallees al k`: the window from the callees'
fields and `verify_sub`'s placed completeness, window by window with `segA_append`, proved by
`mainWindowFromCallees` (`MainFinal.lean`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-- `main`'s `Pre` at the root: the statement's digest at the header. -/
def mainPreR (s : NodeStatement) (rd : Reader) : Prop :=
  ReadsAt rd 1 (Prover.digestCells (statementDigest guestSeed s))

/-- `main`'s `Post` at the root: the honest pushes stream by stream, every node exact. -/
def mainPostR (s : NodeStatement) (w : NodeWitness) (rd : Reader) (t : Tree) : Prop :=
  SameStreams (t.pops coreProgram rd) (Prover.honestPushes guestBytecode guestSeed s w) ∧
    t.Every (ExactAt coreProgram rd)

/-- `main`'s body before its `ret []`. -/
noncomputable def mainSs : List Stmt :=
  Main.mPre ++ [.ite (.n 384) Main.mDa Main.mDaZ] ++ Main.mMid ++ [.ite (.n 423) Main.mLeaf Main.mAgg] ++
    Main.mPost

theorem main_body : (fn% «main»).body = mainSs ++ [.ret []] := by
  rw [Main.main_shape, mainSs]

/-- **`main`'s body as one placed window** on the node `(s, w)`. -/
def MainWindowAt (al : String → Bool) (k : ℕ) (s : NodeStatement) (w : NodeWitness) : Prop :=
  ∃ (σ0 : Val) (σ : Reader → Val) (es : List Ev) (Wo : Words) (Qs : List (Reader → Tree → Prop))
    (Oend : Reader → Prop) (Dend : ℕ → Prop) (e : ℕ), e < 2 ^ 57 ∧
    WordsInA Wo (0 + 2) (0 + B2C.fs "main") (B2C.fs "main") (B2C.fs "main" + (allocs σ0 es).sum) ∧
    SegA (fs := B2C.fs) (al := al) (cert := B2C.cert) k "main" 0 σ0 σ
      (ownData B2C.cert 0 (B2C.fs "main") "main" (allocs σ0 es) es) (· < 2) (mainPreR s) mainSs es
      (B2C.fs "main") (B2C.fs "main" + (allocs σ0 es).sum) (B2C.fs "main" + (allocs σ0 es).sum) e
      (fun rd => HoldsWords rd Wo) Oend (fun _ => False) Dend Qs ∧
    ∀ rd, LowDef k rd → mainPreR s rd → Oend rd → ∀ ts,
      Tree.KidsValid coreProgram rd (σ rd) (calls es) ts → KidsPost rd Qs (calls es) ts →
      mainPostR s w rd (.node "main" (σ rd) (allocs σ0 es) ts)

theorem main_not_loop' : coreProgram.loop "main" = false := by decide +kernel

/-- **`main` completes placed at the root from its window.** -/
theorem callAtA_main_of_window {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness}
    (h : MainWindowAt al k s w) : ∃ e, e < 2 ^ 57 ∧ CallAtA B2C.fs al B2C.cert k "main" [] [] (· < 2)
      (fun _ => False) (fun _ => True) (mainPreR s) (mainPostR s w) (B2C.fs "main") 0 (B2C.fs "main") e := by
  obtain ⟨σ0, σ, es, Wo, Qs, Oend, Dend, e, he, hWo, hseg, hpost⟩ := h
  exact ⟨e, he, callAtA_segRd main_not_loop' (by omega) Main.find_main main_body σ0 σ es Wo Qs Oend Dend hWo
    (fun _ h => h.elim) hseg (fun _ _ => trivial) (fun _ _ _ _ => ⟨rfl, rfl⟩) hpost⟩

/-- **A placed `main` ending below `2^63` ends within `2^30`** on every node: what the count gives
(`within_deployed`), as `MainCompleteA`'s end needs it. -/
def MainEndWithin (al : String → Bool) (k : ℕ) : Prop :=
  ∀ (s : NodeStatement) (w : NodeWitness), NodeRelation guestBytecode guestSeed s w →
    DeployedLimits s w → ChildrenOk guestBytecode guestSeed w → ∀ (D : ℕ → Prop) (Out : Reader → Prop) (e : ℕ),
    CallAtA B2C.fs al B2C.cert k "main" [] [] (· < 2) D Out (mainPreR s) (mainPostR s w)
      (B2C.fs "main") 0 (B2C.fs "main") e → e ≤ 2 ^ 63 → e ≤ 2 ^ 30

/-- **`MainCompleteA` from the window on every node**, the end within `2^30` from the window's below
`2^57` and the count. -/
theorem mainCompleteA_of_window {al : String → Bool} {k : ℕ}
    (hw : ∀ s w, NodeRelation guestBytecode guestSeed s w → DeployedLimits s w →
      ChildrenOk guestBytecode guestSeed w → MainWindowAt al k s w) (hwi : MainEndWithin al k) :
    MainCompleteA al k := by
  intro s w hr hl hok
  obtain ⟨e, he, hc⟩ := callAtA_main_of_window (hw s w hr hl hok)
  exact ⟨_, _, e, hwi s w hr hl hok _ _ e hc (by omega), hc⟩

/-- **`main`'s placed completeness from its window**: the window from the callees' fields and
`verify_sub`'s placed completeness, on a memory floor `17 ≤ k` (`main`'s range check of the children's
count against `2^16` reads the word at `2^16 - n`, defined only from `LowDef 17`). -/
def MainWindowFromCallees (al : String → Bool) (k : ℕ) : Prop :=
  17 ≤ k → k ≤ 23 → MainCalleesA al k → VsCompleteHypA al k guestBytecode guestSeed →
    ∀ s w, NodeRelation guestBytecode guestSeed s w → DeployedLimits s w →
      ChildrenOk guestBytecode guestSeed w → MainWindowAt al k s w

/-- **`main`'s target from its callees**, given the window's statement and the count's bound on the end. -/
theorem mainCalleesA_to_mainFromVs_of_window {al : String → Bool} {k : ℕ} (hW : MainWindowFromCallees al k)
    (hk : 17 ≤ k) (hk' : k ≤ 23) (h : MainCalleesA al k) (hwi : MainEndWithin al k) : MainFromVsA al k :=
  fun hvs => mainCompleteA_of_window (hW hk hk' h hvs) hwi

end
end LeanVM.Guest.Complete
