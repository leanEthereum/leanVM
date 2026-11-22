/-
  LeanVM.Guest.EndExecCoreFn

  What each entry of a function's own routing facts and families must satisfy (`CoreMode/FnReg.lean`): the
  predicates its `Sound.lean` proves of them, one per kind.
-/

module

public import LeanVM.Guest.EndExecW
public import LeanVM.Guest.CoreMode.Fam.ResS
public import LeanVM.Guest.CoreMode.CoreRes

/-!
# A function's own facts and families, the soundness they owe

Each kind of a function's own routing data or family (`CoreMode.FnReg`) has a predicate on its entries, which the
function's `Sound.lean` proves of each of its own (`<kind>_ok`) and the generated `Gen/FnSound.lean` of every entry of
the registry; the shared theorems use only these. Their facts at an instance: `ExpH`, an exponent fact (the word, or
the word read through it, is `g^e`, `e` below the bound); `DimH`, a dimension fact; `ExpQ r J`, `DimQ r J`, each listed
fact of `J`'s function holding at `J` on the reference memory.

* `ExpOk c`: an exponent fact (`Res.expFacts`) holds at every honest instance of its function (`ExpH`);
* `DimOk c`: a dimension fact (`Res.dimFacts`) likewise (`DimH`);
* `ExpValOk c`: a listed value is `g^e`, `e` below the bound, at every honest instance (`CoreMode.expVal`);
* `StLoopOk c`: a stream-cursor loop (`CoreMode.stLoops`): at every honest instance its header names its caller's frame
  `a`, whose cell `D` holds the proof stream `M`, its cursor `v` is `M·g^q` with room for an iteration's `S` words;
* `MlLoopOk c`, `CmLoopOk c`: a ghost family specialization (`CoreMode.mlK`), a frame loop over its caller's table
  (`CoreMode.cmK`): at every honest instance, ghost words at which its reads hold, and its caller's cells linked;
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

/-- An exponent fact: the word `x` (offset `none`), or the word read at `x·g^k`, is `g^e`, `e < b`. -/
def ExpH (rd : Reader) : Option ℕ → ℕ → E → Prop
  | none, b, x => ∃ e < b, x = gen ^ e
  | some k, b, x => ∃ e < b, LoadHolds rd x k (gen ^ e)

/-- A dimension fact: `gb = g^m`, and for each pair `(k, c)` the word at `kb·g^k` is `g^e`, `e + c ≤ m`. -/
def DimH (rd : Reader) (kb gb : E) (ps : List (ℕ × ℕ)) : Prop :=
  ∃ m < 2 ^ 33, gb = gen ^ m ∧ ∀ p ∈ ps, ∃ e, LoadHolds rd kb p.1 (gen ^ e) ∧ e + p.2 ≤ m

/-- **The exponent facts at an instance.** -/
def ExpQ (r : Ref) (J : Inst) : Prop :=
  ∀ f σ bufs kids, J.t = .node f σ bufs kids → ∀ fn, coreProgram.find? f = some fn → ∀ c ∈ Res.expFacts,
    c.1 = f → ∀ v, fn.params[c.2.1]? = some v → ExpH r.img.read c.2.2.1 c.2.2.2 (σ v)

/-- **The dimension facts at an instance.** -/
def DimQ (r : Ref) (J : Inst) : Prop :=
  ∀ f σ bufs kids, J.t = .node f σ bufs kids → ∀ fn, coreProgram.find? f = some fn → ∀ c ∈ Res.dimFacts,
    c.1 = f → ∀ vk vb, fn.params[c.2.1]? = some vk → fn.params[c.2.2.1]? = some vb →
      DimH r.img.read (σ vk) (σ vb) c.2.2.2

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

/-- **A ghost family specialization's reads and links** (`CoreMode.mlK`) at every honest instance whose header cell `1`
holds its caller's frame: ghost words at which its reads (`CoreMode.mlSub`) hold, and its caller's cells linked as its
entry says (`CoreMode.mlGl`) holding there. -/
def MlLoopOk (c : String × ℕ × ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ {r : Ref}, r.Ok → ∀ I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, ∀ σ bufs kids,
    I.t = .node c.1 σ bufs kids → ∀ fn, coreProgram.find? c.1 = some fn → CoreMode.mlK fn = some c.2 →
      r.img.read (addressOfIndex (I.fp + 1)) = some I.hdr.2 → ∃ gw : List E,
        (∀ x, CoreMode.mlSub fn x = true → x.Holds (CoreMode.setG σ gw)) ∧
        ∀ Cf : CoreMode.CFun, Cf.fn = fn → Cf.gl = c.2.2.2.2.2.2 → Cf.H.sig.ghosts = 1 →
          CoreMode.GlF r.img Cf.gl I.fp
            (Cf.fn.params.map (CoreMode.setG σ gw) ++ CoreMode.ownG Cf.H.sig (CoreMode.setG σ gw))

/-- **A frame loop's reads and links** (`CoreMode.cmK`) at every honest instance whose header cell `1` holds its
caller's frame: ghost words at which its reads (`CoreMode.cmSub`) hold, and its caller's cells linked as its entry
says (`CoreMode.cmGl`) holding there. -/
def CmLoopOk (c : String × ℕ × ℕ × ℕ × ℕ × List ℕ) : Prop :=
  ∀ {r : Ref}, r.Ok → ∀ I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, ∀ σ bufs kids,
    I.t = .node c.1 σ bufs kids → ∀ fn, coreProgram.find? c.1 = some fn → CoreMode.cmK fn = some c.2 →
      r.img.read (addressOfIndex (I.fp + 1)) = some I.hdr.2 → ∃ gw : List E,
        (∀ x, CoreMode.cmSub fn x = true → x.Holds (CoreMode.setG σ gw)) ∧
        ∀ Cf : CoreMode.CFun, Cf.fn = fn → Cf.gl = CoreMode.loopGl Cf.fn.params.length c.2.2.2.2.2 →
          Cf.H.sig.ghosts = 3 → CoreMode.GlF r.img Cf.gl I.fp
            (Cf.fn.params.map (CoreMode.setG σ gw) ++ CoreMode.ownG Cf.H.sig (CoreMode.setG σ gw))

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
