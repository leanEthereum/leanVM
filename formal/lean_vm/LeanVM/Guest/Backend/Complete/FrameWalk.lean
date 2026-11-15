/-
  LeanVM.Guest.Backend.Complete.FrameWalk

  The frame side split at the class of valuations that agree off the temporaries: the walk's
  statement, one frame for the class, and the frame family built from it.
-/

module

public import LeanVM.Guest.Backend.Complete.Frame

/-!
# The walk's statement

`FrameCongr` asks the frame family to agree off the temporaries' cells for valuations that agree
off the temporaries. The walk of the placement therefore runs once for the class of a valuation
`σ`: its instance `instOf` takes `σ` with the temporaries zeroed, the readers of the events'
parts that name no temporary (`evNT`), and depends on `σ` off the temporaries only.
`WalkWordsStmt` says that for every path there are frame words `Ψ` and callee headers `kh` such
that every valuation `Same` as the instance's gets `FrameClauses` and `PathWords` from `Ψ`
patched at the temporaries' cells with its own temporaries' words (`patchT`). The frame family
of `FrameWordsStmt` is then the choice for the class, patched (`frameWords_of_walk`).
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

open Classical in
/-- A valuation with the temporaries `ts` zeroed. -/
noncomputable def zeroTmps (ts : List V) (σ : Val) : Val := fun v => if v ∈ ts then 0 else σ v

/-- An event's relation with its temporaries' loads left out. -/
def evNT (rd : Reader) (σ : Val) : Ev → Prop
  | .atom a => holdsNT rd σ a
  | e => e.Holds rd σ

/-- The layout's word of a `SET` immediate. -/
def kwOf {κ₀ : ℕ} (Γ : Site κ₀) (k : KVal) : E :=
  OffsetInstruction.immediateWord (resolveK Γ.l Γ.pc0 Γ.frame k).1 (resolveK Γ.l Γ.pc0 Γ.frame k).2

/-- **The walk's instance of a path** of `tf` placed as `pf` at frame `fp` with header `hdr`, the
path's events `es` of `σ`: it reads `σ` off the temporaries only. -/
noncomputable def instOf {κ₀ : ℕ} (W : World κ₀) (tf : TracedFn) (pf : Placed) (fp : ℕ)
    (hdr : E × E) (σ : Val) (es : List Ev) : Inst where
  σ := zeroTmps (Stmt.tmpsList tf.core.body) σ
  fp := fp
  Rd := fun rd => ∀ e ∈ es, evNT rd (zeroTmps (Stmt.tmpsList tf.core.body) σ) e
  size := pf.fn.frameSize
  hdr := hdr
  kw := kwOf (World.cplSite W tf.core.name)
  tmps := Stmt.tmpsList tf.core.body
  locs := pf.locs
  es := es
  ops := blockOps pf.fn.body 0
  named := Stmt.usesList tf.core.body ++ tf.core.params
  loopH := ((loopTable W.p)[tf.core.name]?).any (·.registered)
  kf := []

open Classical in
/-- The frame words `Ψ` with each temporary's cell holding the temporary's word under `σ`. -/
noncomputable def patchT (I : Inst) (Ψ : ℕ → E) (σ : Val) (n : ℕ) : E :=
  if h : I.tc n then σ (Classical.choose h) else Ψ n

/-- **The walk's statement**: for every path, frame words and callee headers that, patched at
the temporaries' cells, give every valuation agreeing with the path's off the temporaries its
`FrameClauses` (on its readers) and its `PathWords` (given a reader). -/
def WalkWordsStmt : Prop :=
  ∀ {κ₀ : ℕ} (W : World κ₀), W.Compiled → ∀ tf ∈ W.p, Scoped tf → ∀ pf, World.PlacedAs W tf pf →
  TmpsApart tf pf → NoSelfCall tf →
  ∀ (fp : ℕ), (tf.core.name = "main" → fp = 0) → ∀ (kfps : List ℕ) (hdr : E × E) (σ : Val)
    (es : List Ev) (vs : List V), walk σ tf.core.body = .ret es vs →
    (∀ q ∈ addrs es, σ q.1 = ofK (addressOfIndex (fp + (cellP pf.locs q.2).getD 0))) →
    (∃ rd, (instOf W tf pf fp hdr σ es).Rd rd) →
    ∃ (Ψ : ℕ → E) (kh : ℕ → E × E), ∀ σ', (instOf W tf pf fp hdr σ es).Same σ' →
      (∀ rd : Reader, (∀ e ∈ es, e.Holds rd σ') →
        FrameClauses (loopTable W.p) tf pf fp σ' es vs hdr
          ⟨patchT (instOf W tf pf fp hdr σ es) Ψ σ', kh⟩) ∧
      (kfps.length = (calls es).length →
        (isLoopName tf.core.name = true → ∀ kfp, kfps.getLast? = some kfp →
          kfp = fp + pf.fn.frameSize) →
        (∃ rd : Reader, ∀ e ∈ es, e.Holds rd σ') →
        PathWords W tf pf fp σ' es kfps hdr ⟨patchT (instOf W tf pf fp hdr σ es) Ψ σ', kh⟩)

end
end LeanVM.Guest.Backend.Complete
