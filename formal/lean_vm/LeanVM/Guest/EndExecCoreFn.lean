/-
  LeanVM.Guest.EndExecCoreFn

  What each entry of a function's own routing facts and families must satisfy (`CoreMode/FnReg.lean`): the
  predicates its `Sound.lean` proves of them, one per kind.
-/

module

public import LeanVM.Guest.EndExecW
public import LeanVM.Guest.CoreMode.Fn.check_opening_terminal.ResE
public import LeanVM.Guest.CoreMode.Fam.ResS
public import LeanVM.Guest.CoreMode.CoreRes

/-!
# A function's own facts and families, the soundness they owe

Each kind of a function's own routing data or family (`CoreMode.FnReg`) has a predicate on its entries, which the
function's `Sound.lean` proves of each of its own (`<kind>_ok`) and the generated `Gen/FnSound.lean` of every entry of
the registry; the shared theorems use only these:

* `ExpOk c`: an exponent fact (`Res.expFacts`) holds at every honest instance of its function (`ExpH`);
* `DimOk c`: a dimension fact (`Res.dimFacts`) likewise (`DimH`);
* `ExpValOk c`: a listed value is `g^e`, `e` below the bound, at every honest instance (`CoreMode.expVal`);
* `StLoopOk c`: a stream-cursor loop (`CoreMode.stLoops`): at every honest instance its header names its caller's frame
  `a`, whose cell `D` holds the proof stream `M`, its cursor `v` is `M·g^q` with room for an iteration's `S` words;
* `NzOk c`: a listed parameter is nonzero at every honest instance (`NzVal`, `CoreMode.coreNzs`);
* `OwnOk c`: a ghost-free family's residuals hold at every honest instance of its function (`CoreMode.ownFam`);
* `GwFamOk c`: a family over the function's own parameter words as ghosts holds at a valuation agreeing below `GB` with
  an honest instance's, its ghosts those words (`CoreMode.gwFam`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

@[expose] public section

theorem find_name' {f : String} {fn : Fn} (h : coreProgram.find? f = some fn) : fn.name = f := by
  unfold Program.find? at h
  have := List.find?_some h
  simpa using this

/-- **An exponent fact holds** at every honest instance of its function. -/
def ExpOk (c : String × ℕ × Option ℕ × ℕ) : Prop :=
  ∀ {r : Ref}, r.Ok → ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, ∀ σ bufs kids,
    J.t = .node c.1 σ bufs kids → ∀ fn, coreProgram.find? c.1 = some fn → ∀ v, fn.params[c.2.1]? = some v →
      ExpH r.img.read c.2.2.1 c.2.2.2 (σ v)

/-- **A dimension fact holds** at every honest instance of its function. -/
def DimOk (c : String × ℕ × ℕ × List (ℕ × ℕ)) : Prop :=
  ∀ {r : Ref}, r.Ok → ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, ∀ σ bufs kids,
    J.t = .node c.1 σ bufs kids → ∀ fn, coreProgram.find? c.1 = some fn → ∀ vk vb, fn.params[c.2.1]? = some vk →
      fn.params[c.2.2.1]? = some vb → DimH r.img.read (σ vk) (σ vb) c.2.2.2

/-- **A listed value is `g^e`, `e` below its bound**, at every honest instance of its function. -/
def ExpValOk (c : String × ℕ × ℕ) : Prop :=
  ∀ {r : Ref}, r.Ok → ∀ J ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, ∀ σ bufs kids,
    J.t = .node c.1 σ bufs kids → ∃ e < c.2.2, σ (.n c.2.1) = gen ^ e

/-- **The listed values' facts at an instance** (`CoreMode.expVal`). -/
def ExpVQ (J : Inst) : Prop :=
  ∀ f σ bufs kids, J.t = .node f σ bufs kids → ∀ c ∈ CoreMode.FnReg.expVals, c.1 = f → ∃ e < c.2.2, σ (.n c.2.1) = gen ^ e

/-- **A stream-cursor loop's cursor** at every honest instance: its header names its caller's frame `a`, `D > 0`, the
cursor `v < GB` is the stream at the caller's cell `D` times `g^q`, room for `S` words past it. -/
def StLoopOk (c : String × ℕ × ℕ × ℕ) : Prop :=
  c.2.1 ≠ 0 ∧ c.2.2.1 < CoreMode.GB ∧
    ∀ {r : Ref}, r.Ok → ∀ I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, ∀ σ bufs kids,
      I.t = .node c.1 σ bufs kids → ∀ fn, coreProgram.find? c.1 = some fn →
        ∃ a q, I.hdr.2 = ofK (addressOfIndex a) ∧ a + c.2.1 < maxCells ∧
        σ (.n c.2.2.1) = refMem r.img (a + c.2.1) * gen ^ q ∧ q + c.2.2.2 ≤ 8192

/-- **A listed parameter is nonzero** at every honest instance of its function. -/
def NzOk (c : String × V) : Prop := NzVal c.1 c.2

/-- **A function's own family holds** at every honest instance of it. -/
def OwnOk (c : String × (Fn → CoreMode.CRes → Bool)) : Prop :=
  ∀ {r : Ref}, r.Ok → ∀ I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, ∀ σ bufs kids,
    I.t = .node c.1 σ bufs kids → ∀ fn, coreProgram.find? c.1 = some fn → ∀ x, c.2 fn x = true → x.Holds σ

/-- **A function's own family over its own parameter words as ghosts holds** at a valuation agreeing below `GB` with
an honest instance's, its ghost slots those words (`GwR`). -/
def GwFamOk (c : String × (Fn → List (CoreMode.CCell × ℕ) → CoreMode.CRes → Bool)) : Prop :=
  ∀ {r : Ref}, r.Ok → ∀ I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, ∀ σ bufs kids,
    I.t = .node c.1 σ bufs kids → ∀ fn, coreProgram.find? c.1 = some fn → ∀ σ' : Val,
      (∀ v : V, v.idx < CoreMode.GB → σ' v = σ v) → CoreMode.ngB fn = true → ∀ G : CoreMode.HSig,
        CoreMode.GwR r.img G σ' → ∀ x, c.2 fn G.gw x = true → x.Holds σ'

end

end LeanVM.Guest.EndExec
