/-
  LeanVM.Guest.Backend.Complete.Spec

  The statements of the back end's completeness: the emitted code of a placed function runs, on
  a memory whose frame holds what placement gives, with its instruction counts bounded.
-/

module

public import LeanVM.Guest.Backend.Sound.Spec
public import LeanVM.Guest.Backend.Complete.Scoped
public import LeanVM.Guest.Backend.Complete.Cells
public import LeanVM.Guest.Backend.Complete.Count
public import LeanVM.Guest.B2C.Count
public import LeanVM.Guest.B2C.Types
public import LeanVM.Guest.Memory.Placed

/-!
# What the back end's completeness says

Soundness reads a halting run back into the core body; completeness goes the other way: the
valuation `σ` of a function's instance and its path through the core body (`walk σ body = .ret es
vs`) are given, and the emitted code must run from the function's entry to its return on a
memory that holds the right words. As for soundness, the proof is split at the instructions:

* **The meaning of the path at the instructions** (`cplL`, emission's side). What the instructions
  of the placed path need of one memory, read off the placed statements alone, in continuation
  form as `PStmt.Sem` is: each straight-line instruction `Holds` at its pc, each `JUMP` reads words
  of `K` and goes the way the path goes, each call finds its callee's frame pointer and entry and
  the callee's counted run (`KidRuns`) back to this frame. The placed body is read together with
  the core body through a cursor (`ctrlSplit`): a run of core atoms is a run of `PStmt.op`, a
  control statement one control `PStmt`, a run of `k + 1` `match`es one `chain` of `k + 1`
  stages. The core statement fixes which way the path goes (an `ite`'s branch by `σ c`, a
  `match`'s arm as `walkArms` picks it, whether a `callIf` is taken), and the memory's words must
  agree. The callees' frames and counts are consumed in call order from a list of kids.
* **The frame** (`FrameSpec`, `FrameOK`, placement's side). Placement fixes the words of the
  instance's own frame (`Ψ`, its cells from `2` to the frame size: values, constants, jump
  targets, frame pointers and their products, the self pointer buffer) and the headers its callees
  get (`kh`). `FrameOK` says a memory holds them, with the header, the callees' frames and the loop
  helper's tail frame. `FrameConsistentStmt` (proved by the placement side): for a scoped function
  there is such a frame family, the words of the values the path reads are the values' words, and
  on every memory holding it whose reads agree with the path's events the instructions' meaning
  holds.
* **The run** (`FnCompleteStmt`): from the instructions' meaning, a counted run from the entry to
  the return registers (`main`: the final ones), at most `pathOps` instructions of each opcode
  besides the callees'.
* **The counts** (`PathOpsStmt`): `pathOps` is at most the placed body's path maxima (`pmaxP`) and
  the separately counted arms (`armsP`, `armsCost`), the quantities the guest's tables hold.

Every statement is a proposition here; a theorem of that type lives in another module of this
directory. Nothing here is proved.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## Kids -/

/-- A callee's frame index and the counts of its run. -/
abbrev Kid := ℕ × (Opcode → ℕ)

/-- A callee entered at its entry `ent` and frame `kfp` runs, counted, to the return registers
its frame holds. -/
def KidRuns {κ : ℕ} (prog : LeanIsaProgram) (L : MemoryImage κ) (ent kfp : ℕ) (ck : Opcode → ℕ)
    (r : Registers K) : Prop :=
  retRegs L (addressOfIndex kfp) = some r ∧
    B2C.RunC prog L ⟨addressOfIndex ent, addressOfIndex kfp⟩ r ck

/-- Whether the call a core statement makes is entered under `σ`. -/
def callTaken (σ : Val) : Stmt → Prop
  | .callIf c _ _ => σ c ≠ 0
  | _ => True

/-! ## The meaning of the path at the instructions -/

section Cpl

variable {κ : ℕ} (prog : LeanIsaProgram) (Γ : Site κ) (fp : K) (σ : Val)

mutual
/-- **What the instructions of the placed statement `s`, the first at instruction `pos`, need of
the memory** on `σ`'s path, the core block from `s` on being `cs`: `next cs' ks'` after its last
instruction (`cs'` the core statements after it, `ks'` the kids left), `kj ks' d f` after a taken
straight-line jump to the words `d`, `f`, `kret` after the frame's return, `khalt` after `main`'s
closing jump. Only the last statement of a block may leave by `kj` (an arm's exit through the next
table or to the join); a straight-line jump elsewhere, and in an `ite`'s blocks, falls through. -/
def cplS : PStmt → List Stmt → ℕ → List Kid → (List Stmt → List Kid → Prop) →
    (List Kid → E → E → Prop) → Prop → Prop → Prop
  | .op _ o, cs, pos, ks, next, kj, _, _ => OpSem Γ fp o pos (next cs ks) (kj ks)
  | .ite _ c bdest sfp zero hasElse edest one nonzero, cs, pos, ks, next, _, kret, khalt =>
      match ctrlSplit cs with
      | some (.ite cv z n, rest) =>
          Holds Γ.L (Γ.pc0 + pos) fp (Γ.R (.set bdest (.local (elseAt pos zero hasElse)))) ∧
          JumpAt Γ fp c bdest sfp
            (σ cv = 0 ∧ cplL zero z (pos + 2) ks
              (fun ks' => if hasElse then
                  Holds Γ.L (Γ.pc0 + (pos + 2 + blockSize zero)) fp
                    (Γ.R (.set edest (.local (elseAt pos zero hasElse + blockSize nonzero)))) ∧
                  JumpAt Γ fp one edest sfp False (fun d f =>
                    d = Γ.tgt (elseAt pos zero hasElse + blockSize nonzero) ∧ f = ofK fp ∧
                      next rest ks')
                else next rest ks') (fun _ _ _ => False) kret khalt)
            (fun d f => σ cv ≠ 0 ∧ d = Γ.tgt (elseAt pos zero hasElse) ∧ f = ofK fp ∧
              if hasElse then
                cplL nonzero n (elseAt pos zero hasElse) ks (next rest) (fun _ _ _ => False) kret
                  khalt
              else next rest ks)
      | _ => False
  | .chain _ join x entry one sfp firsts stages, cs, pos, ks, next, _, kret, khalt =>
      match ctrlSplit cs with
      | some (s, rest) =>
          Holds Γ.L (Γ.pc0 + pos) fp (Γ.R (.set join (.local (pos + 3 + stagesSize stages)))) ∧
          Holds Γ.L (Γ.pc0 + pos + 1) fp (Γ.R (.slot x (firsts.headD 0) entry)) ∧
          JumpAt Γ fp one entry sfp False (fun d f =>
            cplStages stages ((s :: rest).take stages.length) (pos + 3)
              (next ((s :: rest).drop stages.length)) kret khalt ks d f)
      | none => False
  | .call _ c, cs, pos, ks, next, _, kret, _ =>
      match ctrlSplit cs, ks with
      | some (s, rest), (kfp, ck) :: ks' =>
          SegHolds Γ fp (callPre c) pos ∧
          JumpAt Γ fp c.oc c.entry c.nfp
            (¬ callTaken σ s ∧
              SegHolds Γ fp (callRets c.nfp c.args.length c.rets) (pos + (callPre c).length + 1) ∧
              next rest ks')
            (fun d f => callTaken σ s ∧ d = ofK (addressOfIndex (Γ.ent c.callee)) ∧
              f = ofK (addressOfIndex kfp) ∧ ∃ r, KidRuns prog Γ.L (Γ.ent c.callee) kfp ck r ∧
                if c.tail then retRegs Γ.L fp = some r ∧ kret
                else r = ⟨addressOfIndex (Γ.pc0 + (pos + (callPre c).length + 1)), fp⟩ ∧
                  SegHolds Γ fp (callRets c.nfp c.args.length c.rets)
                    (pos + (callPre c).length + 1) ∧ next rest ks')
      | _, _ => False
  | .loopNext _ callee nfp entry oc one args, cs, pos, ks, next, _, kret, _ =>
      match ctrlSplit cs, ks with
      | some (s, rest), (kfp, ck) :: ks' =>
          SegHolds Γ fp (loopPre callee nfp entry one args) pos ∧
          JumpAt Γ fp oc entry nfp (¬ callTaken σ s ∧ next rest ks')
            (fun d f => callTaken σ s ∧ d = ofK (addressOfIndex (Γ.ent callee)) ∧
              f = ofK (addressOfIndex kfp) ∧ ∃ r, KidRuns prog Γ.L (Γ.ent callee) kfp ck r ∧
                retRegs Γ.L fp = some r ∧ kret)
      | _, _ => False
  | .dispatch _ callees nfp joinCell x entry one first args rets, cs, pos, ks, next, _, _, _ =>
      match ctrlSplit cs, ks with
      | some (_, rest), (kfp, ck) :: ks' =>
          SegHolds Γ fp (dispatchPre pos nfp joinCell x entry first args) pos ∧
          JumpAt Γ fp one entry nfp False (fun d f => f = ofK (addressOfIndex kfp) ∧
            ∃ g ∈ callees, d = ofK (addressOfIndex (Γ.ent g)) ∧ ∃ r, KidRuns prog Γ.L (Γ.ent g) kfp ck r ∧
              r = ⟨addressOfIndex (Γ.pc0 + (pos + args.length + 5)), fp⟩ ∧
              SegHolds Γ fp (callRets nfp args.length rets) (pos + args.length + 5) ∧ next rest ks')
      | _, _ => False
  | .ret _ one, _, _, _, _, _, kret, _ => JumpAt Γ fp one 0 1 False (fun _ _ => kret)
  | .halt _ one dest, _, pos, _, _, _, _, khalt =>
      Holds Γ.L (Γ.pc0 + pos) fp (Γ.R (.set dest .endSentinel)) ∧
      JumpAt Γ fp one dest one False (fun _ f => f = ofK fp ∧ khalt)

/-- What the instructions of a placed block need of the memory, the core block being `cs`;
`next ks'` after its last instruction. -/
def cplL : List PStmt → List Stmt → ℕ → List Kid → (List Kid → Prop) →
    (List Kid → E → E → Prop) → Prop → Prop → Prop
  | [], _, _, ks, next, _, _, _ => next ks
  | s :: ss, cs, pos, ks, next, kj, kret, khalt =>
      cplS s cs pos ks (fun cs' ks' => cplL ss cs' (pos + stmtSize s) ks' next kj kret khalt)
        (if ss.isEmpty then kj else fun _ _ _ => False) kret khalt

/-- A jump to `(d, f)` into the stages of a chain from instruction `pos`, the core `match`es of
the stages being `cms`: into the arm of the first stage `σ` picks, or past the stages to the
join. -/
def cplStages : List (List (List PStmt)) → List Stmt → ℕ → (List Kid → Prop) → Prop → Prop →
    List Kid → E → E → Prop
  | [], _, pos, next, _, _, ks, d, f => d = Γ.tgt pos ∧ f = ofK fp ∧ next ks
  | st :: sts, cms, pos, next, kret, khalt, ks, d, f =>
      match cms with
      | .match_ xv arms :: cms' =>
          cplArms xv st arms 0 pos (cplStages sts cms' (pos + armsSize st) next kret khalt) kret
            khalt ks d f
      | _ => False

/-- A jump to `(d, f)` into the arms of a stage from instruction `pos`, from arm `j`: into the
arm `σ` picks (the first `j` with `σ xv = g^j`, as `walkArms`), which runs and leaves by a jump
`kj`, falling off its end being a jump to the next instruction. -/
def cplArms (xv : V) : List (List PStmt) → List (List Stmt) → ℕ → ℕ → (List Kid → E → E → Prop) →
    Prop → Prop → List Kid → E → E → Prop
  | [], _, _, _, _, _, _, _, _, _ => False
  | pa :: pas, arms, j, pos, kj, kret, khalt, ks, d, f =>
      match arms with
      | a :: as =>
          if σ xv = ofK (addressOfIndex j) then
            d = Γ.tgt pos ∧ f = ofK fp ∧
              cplL pa a pos ks (fun ks' => kj ks' (Γ.tgt (pos + blockSize pa)) (ofK fp)) kj kret
                khalt
          else cplArms xv pas as (j + 1) (pos + blockSize pa) kj kret khalt ks d f
      | [] => False
end

end Cpl

/-! ## A compiled program's functions -/

namespace World

variable {κ : ℕ} (W : World κ)

/-- The program on another memory, of any size. -/
def withL {κ' : ℕ} (L : MemoryImage κ') : World κ' := ⟨W.p, W.fns, W.slots, W.logSize, W.hl, L, W.U⟩

/-- Function `g`'s code in the program: its entry and frame in the layout. The contracts are not
read by the completeness side. -/
def cplSite (g : String) : Site κ :=
  ⟨W.L, W.layout, W.ent g, W.layout.frame.getD g 0, fun _ _ => True, fun _ _ => True⟩

/-- `pf` is the program's placement of `tf`. -/
def PlacedAs (tf : TracedFn) (pf : Placed) : Prop := pf ∈ W.placed ∧ pf.fn.name = tf.core.name

/-- **The instructions' meaning of an instance's path**: function `tf`, placed as `pf`, at frame
`fp` with valuation `σ`, its callees `kids` in call order. A function but `main` ends at its
frame's return, `main` at its closing jump; the body never falls off its end. -/
def CplBody (tf : TracedFn) (pf : Placed) (fp : ℕ) (σ : Val) (kids : List Kid) : Prop :=
  cplL W.prog (World.cplSite W tf.core.name) (addressOfIndex fp) σ pf.fn.body tf.core.body 0 kids
    (fun _ => False) (fun _ _ _ => False) (tf.core.name ≠ "main") (tf.core.name = "main")

/-- The callees on a path run: each call entered, from its callee's entry at its frame to the
return registers that frame holds, executing `ck[i] op` instructions of each opcode, its returns
left in its frame after its arguments (`B2C.KidsRun` on the program's own code). -/
def KidsRunP (σ : Val) (es : List Ev) (kfps : List ℕ) (ck : List (Opcode → ℕ)) : Prop :=
  ck.length = (calls es).length ∧ ∀ (i : ℕ) (c : Call) (kfp : ℕ), (calls es)[i]? = some c →
    kfps[i]? = some kfp → c.taken = true →
      (∃ r, KidRuns W.prog W.L (W.ent c.f) kfp (ck.getD i 0) r) ∧
      ∀ k (hk : k < c.rets.length),
        W.L.read (addressOfIndex (kfp + (2 + c.args.length + k))) = some (σ c.rets[k])

end World

/-! ## The frame -/

/-- The words placement fixes for an instance: its own frame's cells (`Ψ`; the cells from `2` to
the frame size are read) and the header each callee gets, by call index (`kh`). -/
structure FrameSpec where
  Ψ : ℕ → E
  kh : ℕ → E × E

/-- A registered loop helper: its frames are reserved in one run, its own pointer past its
arguments. -/
def registered (loops : Loops) (g : String) : Prop := ((loops[g]?).any (·.registered)) = true

/-- **A memory holds an instance's frame**: function `tf` (frame size `size`) at frame `fp` with
header `hdr`, frame words `FS`, path `es` of `σ`, its callees' frames at `kfps`: the header, the own
cells, one callee frame per call with its header, arguments and (a registered loop helper's) self
pointer, and a loop helper's last callee frame right after its own. -/
structure FrameOK {κ : ℕ} (L : MemoryImage κ) (loops : Loops) (tf : TracedFn) (size fp : ℕ)
    (FS : FrameSpec) (σ : Val) (es : List Ev) (kfps : List ℕ) (hdr : E × E) : Prop where
  hdr0 : L.read (addressOfIndex (fp + 0)) = some hdr.1
  hdr1 : L.read (addressOfIndex (fp + 1)) = some hdr.2
  hdrK : tf.core.name ≠ "main" → IsInK hdr.1 ∧ IsInK hdr.2
  own : ∀ n, 2 ≤ n → n < size → L.read (addressOfIndex (fp + n)) = some (FS.Ψ n)
  len : kfps.length = (calls es).length
  kid : ∀ (i : ℕ) (c : Call) (kfp : ℕ), (calls es)[i]? = some c → kfps[i]? = some kfp →
    L.read (addressOfIndex (kfp + 0)) = some (FS.kh i).1 ∧
    L.read (addressOfIndex (kfp + 1)) = some (FS.kh i).2 ∧
    (∀ k (hk : k < c.args.length), L.read (addressOfIndex (kfp + (2 + k))) = some (σ c.args[k])) ∧
    (registered loops c.f → L.read (addressOfIndex (kfp + (2 + c.args.length))) =
      some (ofK (addressOfIndex kfp)))
  tail : isLoopName tf.core.name = true → ∀ kfp, kfps.getLast? = some kfp → kfp = fp + size

mutual
/-- The selectors of the `match`es and fused dispatches on `σ`'s path through a statement. -/
noncomputable def sels1 (σ : Val) : Stmt → List V
  | .ite c z n => if σ c = 0 then pathSels σ z else pathSels σ n
  | .match_ x arms => x :: armSels σ x 0 arms
  | .dispatch x _ _ _ => [x]
  | _ => []

/-- The selectors on `σ`'s path through a block. -/
noncomputable def pathSels (σ : Val) : List Stmt → List V
  | [] => []
  | s :: ss =>
      match walk1 σ s with
      | .fall _ => sels1 σ s ++ pathSels σ ss
      | _ => sels1 σ s

/-- The selectors on the path through the arm `σ` picks, from arm `j`. -/
noncomputable def armSels (σ : Val) (x : V) : ℕ → List (List Stmt) → List V
  | _, [] => []
  | j, a :: as => if σ x = ofK (addressOfIndex j) then pathSels σ a else armSels σ x (j + 1) as
end

/-- **The values the placed path of `σ` reads**: those the core path names (`namedOf`: the
parameters, the events' values, the returned values), the range checks' temporaries, and the
selectors (which `walk` names in no event). -/
noncomputable def readsP (params : List V) (body : List Stmt) (σ : Val) (es : List Ev)
    (vs : List V) : List V :=
  params ++ es.flatMap Ev.uses ++ vs ++ es.flatMap Ev.tmps ++ pathSels σ body

/-- **What the frame words give of the values** of one instance: function `tf` placed as `pf` at
frame `fp` with header `hdr`, on the path `es`, `vs` of `σ`. A value the path reads is in its
cell's word, or (a frame address or a product kept shifted) a cell's word times `g^e`; every
range check temporary of the body, on the path or not, is in its cell's word (`TmpsApart` keeps
its cell from every other use); a registered loop helper's self pointer cell holds its frame; a
callee's header is in `K`, and a self call (a loop's last) gets this frame's header. -/
structure FrameClauses (loops : Loops) (tf : TracedFn)
    (pf : Placed) (fp : ℕ) (σ : Val) (es : List Ev) (vs : List V) (hdr : E × E)
    (FS : FrameSpec) : Prop where
  cell : ∀ v ∈ readsP tf.core.params tf.core.body σ es vs, ∀ n, cellP pf.locs v = some n →
    2 ≤ n ∧ n < pf.fn.frameSize ∧ FS.Ψ n = σ v
  shifted : ∀ v ∈ readsP tf.core.params tf.core.body σ es vs, ∀ n e,
    pf.locs[v]? = some (.shifted n e) → σ v = FS.Ψ n * ofK (addressOfIndex e)
  tmp : TmpsApart tf pf → ∀ t ∈ Stmt.tmpsList tf.core.body, ∀ n, cellP pf.locs t = some n →
    2 ≤ n ∧ n < pf.fn.frameSize ∧ FS.Ψ n = σ t
  self : registered loops tf.core.name →
    FS.Ψ (2 + tf.core.params.length) = ofK (addressOfIndex fp)
  khK : ∀ (i : ℕ) (c : Call), (calls es)[i]? = some c →
    (tf.core.name ≠ "main" → IsInK hdr.1 ∧ IsInK hdr.2) → IsInK (FS.kh i).1 ∧ IsInK (FS.kh i).2
  khSelf : ∀ (i : ℕ) (c : Call), (calls es)[i]? = some c → c.f = tf.core.name → FS.kh i = hdr

/-- The frame words of an instance do not depend on the words of its range checks' temporaries:
two valuations equal off the temporaries give equal header words and equal frame words off the
temporaries' cells. -/
def FrameCongr (tf : TracedFn) (pf : Placed) (FS : Val → FrameSpec) : Prop :=
  ∀ σ σ', (∀ v, v ∉ Stmt.tmpsList tf.core.body → σ' v = σ v) →
    (∀ n, (∀ t ∈ Stmt.tmpsList tf.core.body, cellP pf.locs t ≠ some n) → (FS σ').Ψ n = (FS σ).Ψ n) ∧
    (FS σ').kh = (FS σ).kh

/-! ## The statements -/

/-- **P5, frames**: every value of a scoped function placed in a cell is in the frame, past the
header. -/
def PlaceInFrameStmt : Prop :=
  ∀ (loops : Loops) (sigs : SMap (ℕ × ℕ)) (t t' : Tables) (tf : TracedFn) (pf : Placed),
    placeFn loops sigs t tf = .ok (pf, t') → Scoped tf →
    ∀ v n, cellP pf.locs v = some n → 2 ≤ n ∧ n < pf.fn.frameSize

/-- **Placement pairs the placed body with the core body**, for a scoped function. -/
def PlaceAlignedStmt : Prop :=
  ∀ (loops : Loops) (sigs : SMap (ℕ × ℕ)) (t t' : Tables) (tf : TracedFn) (pf : Placed),
    placeFn loops sigs t tf = .ok (pf, t') → Scoped tf → Aligned tf pf

/-- **The frame of an instance is consistent** (the placement side): for a scoped function
placed as `pf`, at a frame `fp` (`main`'s at `0`) whose frame addresses point into it, with callee
frames `kfps` and header `hdr`, there is a frame family over the valuations, chosen before any
memory (of any size) and blind to the temporaries' words, such that on every path whose events
hold on some reader its words hold the values the path reads, and on every memory holding the
frame whose reads agree with the path's events, with the jump tables written and the callees'
runs, the instructions of the path have their meaning. -/
def FrameConsistentStmt : Prop :=
  ∀ {κ₀ : ℕ} (W : World κ₀), W.Compiled → ∀ tf ∈ W.p, Scoped tf → ∀ pf, World.PlacedAs W tf pf →
  TmpsApart tf pf → NoSelfCall tf →
  ∀ (fp : ℕ), (tf.core.name = "main" → fp = 0) → ∀ (kfps : List ℕ) (hdr : E × E),
  ∃ FS : Val → FrameSpec, FrameCongr tf pf FS ∧
    ∀ (σ : Val) (es : List Ev) (vs : List V), walk σ tf.core.body = .ret es vs →
      (∀ q ∈ addrs es, σ q.1 = ofK (addressOfIndex (fp + (cellP pf.locs q.2).getD 0))) →
      (∀ rd : Reader, (∀ e ∈ es, e.Holds rd σ) →
        FrameClauses (loopTable W.p) tf pf fp σ es vs hdr (FS σ)) ∧
      ∀ {κ : ℕ} (L : MemoryImage κ) (ck : List (Opcode → ℕ)),
        FrameOK L (loopTable W.p) tf pf.fn.frameSize fp (FS σ) σ es kfps hdr →
        (∀ e ∈ es, e.Holds L.read σ) → JTHolds L W.layout W.slots →
        World.KidsRunP (World.withL W L) σ es kfps ck →
        World.CplBody (World.withL W L) tf pf fp σ (kfps.zip ck)

/-! ## Counts -/

section Ops

open Classical

mutual
/-- The instructions of each opcode `σ`'s path runs through the placed statement `s`, the core
block from it on being `cs`; the core statements after it; whether the path falls through it. -/
noncomputable def opsS (σ : Val) : PStmt → List Stmt → (Opcode → ℕ) × List Stmt × Bool
  | .op _ o, cs => (lopCnt o, cs, true)
  | .ite _ _ _ _ zero hasElse _ _ nonzero, cs =>
      match ctrlSplit cs with
      | some (.ite cv z n, rest) =>
          if σ cv = 0 then
            (setJump + (opsL σ zero z).1 + (if hasElse && (opsL σ zero z).2 then setJump else 0),
              rest, (opsL σ zero z).2)
          else if hasElse then (setJump + (opsL σ nonzero n).1, rest, (opsL σ nonzero n).2)
          else (setJump, rest, true)
      | _ => (0, [], false)
  | .chain _ _ _ _ _ _ _ stages, cs =>
      match ctrlSplit cs with
      | some (s, rest) =>
          (chainHead + (opsStages σ stages ((s :: rest).take stages.length)).1,
            (s :: rest).drop stages.length, (opsStages σ stages ((s :: rest).take stages.length)).2)
      | none => (0, [], false)
  | .call _ c, cs =>
      match ctrlSplit cs with
      | some (s, rest) =>
          if c.tail = true ∧ callTaken σ s then (opsCnt (callPre c) + jumpCnt, rest, false)
          else (opsCnt (callPre c) + jumpCnt + opsCnt (callRets c.nfp c.args.length c.rets), rest,
            true)
      | none => (0, [], false)
  | .loopNext _ callee nfp entry _ one args, cs =>
      match ctrlSplit cs with
      | some (s, rest) =>
          (opsCnt (loopPre callee nfp entry one args) + jumpCnt, rest,
            if callTaken σ s then false else true)
      | none => (0, [], false)
  | .dispatch _ _ nfp joinCell x entry _ first args rets, cs =>
      match ctrlSplit cs with
      | some (_, rest) =>
          (opsCnt (dispatchPre 0 nfp joinCell x entry first args) + jumpCnt +
            opsCnt (callRets nfp args.length rets), rest, true)
      | none => (0, [], false)
  | .ret _ _, cs => (jumpCnt, cs, false)
  | .halt _ _ _, cs => (setJump, cs, false)

/-- The instructions of each opcode `σ`'s path runs through a placed block, the core block being
`cs`, up to the path's return; whether it falls through. -/
noncomputable def opsL (σ : Val) : List PStmt → List Stmt → (Opcode → ℕ) × Bool
  | [], _ => (0, true)
  | s :: ss, cs =>
      if (opsS σ s cs).2.2 then
        ((opsS σ s cs).1 + (opsL σ ss (opsS σ s cs).2.1).1, (opsL σ ss (opsS σ s cs).2.1).2)
      else ((opsS σ s cs).1, false)

/-- Through the stages of a chain, the core `match`es being `cms`. -/
noncomputable def opsStages (σ : Val) : List (List (List PStmt)) → List Stmt → (Opcode → ℕ) × Bool
  | [], _ => (0, true)
  | st :: sts, cms =>
      match cms with
      | .match_ xv arms :: cms' =>
          if (opsArms σ xv st arms 0).2 then
            ((opsArms σ xv st arms 0).1 + (opsStages σ sts cms').1, (opsStages σ sts cms').2)
          else ((opsArms σ xv st arms 0).1, false)
      | _ => (0, false)

/-- Through the arm `σ` picks, from arm `j`. -/
noncomputable def opsArms (σ : Val) (xv : V) : List (List PStmt) → List (List Stmt) → ℕ →
    (Opcode → ℕ) × Bool
  | [], _, _ => (0, false)
  | pa :: pas, arms, j =>
      match arms with
      | a :: as => if σ xv = ofK (addressOfIndex j) then opsL σ pa a else opsArms σ xv pas as (j + 1)
      | [] => (0, false)
end

end Ops

/-- **The instructions of each opcode the path of `σ` through function `tf`, placed as `pf`,
runs**, its callees apart. -/
noncomputable def pathOps (σ : Val) (tf : TracedFn) (pf : Placed) : Opcode → ℕ :=
  (opsL σ pf.fn.body tf.core.body).1

section Cost

open Classical

mutual
/-- The separately counted arms a statement's path passes, under `σ` (`B2C.cost1`). -/
noncomputable def cost1 (acs : List (ℕ × List (List ℕ))) (σ : Val) : Stmt → Opcode → ℕ
  | .ite c z n => if σ c = 0 then armsCost acs σ z else armsCost acs σ n
  | .match_ x arms => costArms acs σ x (B2C.armRaw acs x.idx) 0 arms
  | _ => 0

/-- The separately counted arms a block's path passes, under `σ` (`B2C.costW`). -/
noncomputable def armsCost (acs : List (ℕ × List (List ℕ))) (σ : Val) : List Stmt → Opcode → ℕ
  | [] => 0
  | s :: ss => cost1 acs σ s + armsCost acs σ ss

/-- The arm `σ` picks, from arm `k` on, its count if counted separately (`B2C.costArms`). -/
noncomputable def costArms (acs : List (ℕ × List (List ℕ))) (σ : Val) (x : V)
    (key : Option (List (List ℕ))) : ℕ → List (List Stmt) → Opcode → ℕ
  | _, [] => 0
  | k, a :: as => if σ x = ofK (addressOfIndex k) then
      (fun op ↦ match key with
        | some cs => (listElementOrDefault cs k []).getD (opIx op) 0
        | none => 0) + armsCost acs σ a
    else costArms acs σ x key (k + 1) as
end

end Cost

/-- **(The run) The emitted code of a function runs** from its entry to its frame's return
registers (`main`: to the final registers), counted: on any memory where the instructions of an
instance's path have their meaning, at most `pathOps` instructions of each opcode besides the
callees'. -/
def World.FnComplete {κ : ℕ} (W : World κ) (tf : TracedFn) : Prop :=
  ∀ pf, World.PlacedAs W tf pf → ∀ (fp : ℕ), (tf.core.name = "main" → fp = 0) →
  ∀ (σ : Val) (kids : List Kid), World.CplBody W tf pf fp σ kids →
    ∃ (r : Registers K) (c : Opcode → ℕ),
      (if tf.core.name = "main" then r = Registers.final W.prog
        else retRegs W.L (addressOfIndex fp) = some r) ∧
      B2C.RunC W.prog W.L ⟨addressOfIndex (W.ent tf.core.name), addressOfIndex fp⟩ r c ∧
      ∀ op, c op ≤ pathOps σ tf pf op + (kids.map (·.2 op)).sum

/-- `fnComplete`'s statement: every function of a compiled program. -/
def FnCompleteStmt : Prop :=
  ∀ {κ : ℕ} (W : World κ), W.Compiled → ∀ tf ∈ W.p, World.FnComplete W tf

/-- **(The counts)** On a placed function that pairs up with its core body, a path to a return
runs at most the placed body's path maxima and the separately counted arms it passes, the
separately counted stages on distinct selectors. -/
def PathOpsStmt : Prop :=
  ∀ (tf : TracedFn) (pf : Placed), Aligned tf pf → ∀ (keyed : Bool),
    ((armsP keyed tf pf).map (·.1)).Nodup →
    ∀ (σ : Val) (es : List Ev) (vs : List V), walk σ tf.core.body = .ret es vs →
    ∀ op : Opcode,
      pathOps σ tf pf op ≤ pmaxP keyed pf op + armsCost (armsP keyed tf pf) σ tf.core.body op

/-! ## The interface between the frame side and the run side

`FrameConsistentStmt`'s second half is split per placed statement of the path, not at "the frame
family exists / the code runs": proving `CplBody` needs, for each instruction, the word the frame
family put in each cell it reads and which memory each `DEREF` reads, which only the construction
of the family knows. `PathWords` says it: by recursion with `cplL`'s cursor, for every placed
statement on `σ`'s path, its straight-line instructions hold on every memory `Ag` admits (own frame
the frame words, the path's events, the jump tables), and its jumps read frame words of `K` that go
the way the core path goes: conditions and selectors are `σ`'s, targets are the pcs meant, frame
pointer cells hold `g^fp`, a call of index `i` jumps to its callee's entry at the callee frame
`kfps[i]` and gives it the header `kh i` (the return pc and this frame, or this frame's header for a
tail call). The frame side proves `FrameWordsStmt`, the run side `PathRunStmt`; together they give
`FrameConsistentStmt`. -/

section Words

variable {κ₀ : ℕ} (Γ : Site κ₀) (fp : ℕ) (σ : Val) (hdr : E × E) (FS : FrameSpec)
  (Ag : (κ : ℕ) → MemoryImage κ → Prop)

/-- The frame words: the header, then `Ψ`. -/
def fwd (n : ℕ) : E := if n = 0 then hdr.1 else if n = 1 then hdr.2 else FS.Ψ n

/-- A straight-line instruction holds on every memory `Ag` admits. -/
def HW (pc : ℕ) (o : LOp) : Prop :=
  ∀ (κ : ℕ) (L : MemoryImage κ), Ag κ L → Holds L pc (addressOfIndex fp) (Γ.R o)

/-- Straight-line instructions from `pos`. -/
def SegW (ops : List LOp) (pos : ℕ) : Prop :=
  ∀ i (h : i < ops.length), HW Γ fp Ag (Γ.pc0 + pos + i) ops[i]

/-- A `JUMP` on frame words. -/
def JW (oc od of : ℕ) (fall : Prop) (taken : E → E → Prop) : Prop :=
  IsInK (fwd hdr FS oc) ∧ IsInK (fwd hdr FS od) ∧ IsInK (fwd hdr FS of) ∧
    (fwd hdr FS oc = 0 → fall) ∧ (fwd hdr FS oc ≠ 0 → taken (fwd hdr FS od) (fwd hdr FS of))

/-- A taken call into frame `kfp`, index `i`, callee header `ret`. -/
def CallW (callee : String) (kfp i : ℕ) (ret : E × E) (d f : E) : Prop :=
  d = ofK (addressOfIndex (Γ.ent callee)) ∧ f = ofK (addressOfIndex kfp) ∧ FS.kh i = ret

mutual
/-- **The frame words of a placed statement on `σ`'s path**, the core block from it being `cs`,
its calls taking `(index, callee frame)` from `ks`. -/
def wS : PStmt → List Stmt → ℕ → List (ℕ × ℕ) → (List Stmt → List (ℕ × ℕ) → Prop) →
    (List (ℕ × ℕ) → E → E → Prop) → Prop → Prop → Prop
  | .op _ o, cs, pos, ks, next, kj, _, _ =>
      match o with
      | .jump oc od of => JW hdr FS oc od of (next cs ks) (kj ks)
      | o => HW Γ fp Ag (Γ.pc0 + pos) o ∧ next cs ks
  | .ite _ c bdest sfp zero hasElse edest one nonzero, cs, pos, ks, next, _, kret, khalt =>
      match ctrlSplit cs with
      | some (.ite cv z n, rest) =>
          HW Γ fp Ag (Γ.pc0 + pos) (.set bdest (.local (elseAt pos zero hasElse))) ∧
          JW hdr FS c bdest sfp
            (σ cv = 0 ∧ wL zero z (pos + 2) ks
              (fun ks' => if hasElse then
                  HW Γ fp Ag (Γ.pc0 + (pos + 2 + blockSize zero))
                    (.set edest (.local (elseAt pos zero hasElse + blockSize nonzero))) ∧
                  JW hdr FS one edest sfp False (fun d f =>
                    d = Γ.tgt (elseAt pos zero hasElse + blockSize nonzero) ∧
                      f = ofK (addressOfIndex fp) ∧ next rest ks')
                else next rest ks') (fun _ _ _ => False) kret khalt)
            (fun d f => σ cv ≠ 0 ∧ d = Γ.tgt (elseAt pos zero hasElse) ∧
              f = ofK (addressOfIndex fp) ∧
              if hasElse then wL nonzero n (elseAt pos zero hasElse) ks (next rest)
                (fun _ _ _ => False) kret khalt
              else next rest ks)
      | _ => False
  | .chain _ join x entry one sfp firsts stages, cs, pos, ks, next, _, kret, khalt =>
      match ctrlSplit cs with
      | some (s, rest) =>
          HW Γ fp Ag (Γ.pc0 + pos) (.set join (.local (pos + 3 + stagesSize stages))) ∧
          HW Γ fp Ag (Γ.pc0 + pos + 1) (.slot x (firsts.headD 0) entry) ∧
          JW hdr FS one entry sfp False (fun d f =>
            wStages stages ((s :: rest).take stages.length) (pos + 3)
              (next ((s :: rest).drop stages.length)) kret khalt ks d f)
      | none => False
  | .call _ c, cs, pos, ks, next, _, kret, _ =>
      match ctrlSplit cs, ks with
      | some (s, rest), (i, kfp) :: ks' =>
          SegW Γ fp Ag (callPre c) pos ∧
          JW hdr FS c.oc c.entry c.nfp
            (¬ callTaken σ s ∧
              SegW Γ fp Ag (callRets c.nfp c.args.length c.rets) (pos + (callPre c).length + 1) ∧
              next rest ks')
            (fun d f => callTaken σ s ∧
              if c.tail then CallW Γ FS c.callee kfp i hdr d f ∧ kret
              else CallW Γ FS c.callee kfp i
                  (Γ.tgt (pos + (callPre c).length + 1), ofK (addressOfIndex fp)) d f ∧
                SegW Γ fp Ag (callRets c.nfp c.args.length c.rets) (pos + (callPre c).length + 1) ∧
                next rest ks')
      | _, _ => False
  | .loopNext _ callee nfp entry oc one args, cs, pos, ks, next, _, kret, _ =>
      match ctrlSplit cs, ks with
      | some (s, rest), (i, kfp) :: ks' =>
          SegW Γ fp Ag (loopPre callee nfp entry one args) pos ∧
          JW hdr FS oc entry nfp (¬ callTaken σ s ∧ next rest ks')
            (fun d f => callTaken σ s ∧ CallW Γ FS callee kfp i hdr d f ∧ kret)
      | _, _ => False
  | .dispatch _ callees nfp joinCell x entry one first args rets, cs, pos, ks, next, _, _, _ =>
      match ctrlSplit cs, ks with
      | some (_, rest), (i, kfp) :: ks' =>
          SegW Γ fp Ag (dispatchPre pos nfp joinCell x entry first args) pos ∧
          JW hdr FS one entry nfp False (fun d f => ∃ g ∈ callees,
            CallW Γ FS g kfp i (Γ.tgt (pos + args.length + 5), ofK (addressOfIndex fp)) d f ∧
            SegW Γ fp Ag (callRets nfp args.length rets) (pos + args.length + 5) ∧ next rest ks')
      | _, _ => False
  | .ret _ one, _, _, _, _, _, kret, _ => JW hdr FS one 0 1 False (fun _ _ => kret)
  | .halt _ one dest, _, pos, _, _, _, _, khalt =>
      HW Γ fp Ag (Γ.pc0 + pos) (.set dest .endSentinel) ∧
      JW hdr FS one dest one False (fun _ f => f = ofK (addressOfIndex fp) ∧ khalt)

/-- The frame words of a placed block on `σ`'s path. -/
def wL : List PStmt → List Stmt → ℕ → List (ℕ × ℕ) → (List (ℕ × ℕ) → Prop) →
    (List (ℕ × ℕ) → E → E → Prop) → Prop → Prop → Prop
  | [], _, _, ks, next, _, _, _ => next ks
  | s :: ss, cs, pos, ks, next, kj, kret, khalt =>
      wS s cs pos ks (fun cs' ks' => wL ss cs' (pos + stmtSize s) ks' next kj kret khalt)
        (if ss.isEmpty then kj else fun _ _ _ => False) kret khalt

/-- Into a chain's stages. -/
def wStages : List (List (List PStmt)) → List Stmt → ℕ → (List (ℕ × ℕ) → Prop) → Prop → Prop →
    List (ℕ × ℕ) → E → E → Prop
  | [], _, pos, next, _, _, ks, d, f => d = Γ.tgt pos ∧ f = ofK (addressOfIndex fp) ∧ next ks
  | st :: sts, cms, pos, next, kret, khalt, ks, d, f =>
      match cms with
      | .match_ xv arms :: cms' =>
          wArms xv st arms 0 pos (wStages sts cms' (pos + armsSize st) next kret khalt) kret
            khalt ks d f
      | _ => False

/-- Into the arm of a stage `σ` picks. -/
def wArms (xv : V) : List (List PStmt) → List (List Stmt) → ℕ → ℕ →
    (List (ℕ × ℕ) → E → E → Prop) → Prop → Prop → List (ℕ × ℕ) → E → E → Prop
  | [], _, _, _, _, _, _, _, _, _ => False
  | pa :: pas, arms, j, pos, kj, kret, khalt, ks, d, f =>
      match arms with
      | a :: as =>
          if σ xv = ofK (addressOfIndex j) then
            d = Γ.tgt pos ∧ f = ofK (addressOfIndex fp) ∧
              wL pa a pos ks (fun ks' => kj ks' (Γ.tgt (pos + blockSize pa))
                (ofK (addressOfIndex fp))) kj kret khalt
          else wArms xv pas as (j + 1) (pos + blockSize pa) kj kret khalt ks d f
      | [] => False
end

end Words

/-- The memories the frame words describe: own frame `fwd`, the path's events, the jump tables. -/
def AgOf {κ₀ : ℕ} (W : World κ₀) (fp : ℕ) (σ : Val) (es : List Ev) (hdr : E × E) (FS : FrameSpec)
    (size : ℕ) (κ : ℕ) (L : MemoryImage κ) : Prop :=
  (∀ n, n < size → L.read (addressOfIndex (fp + n)) = some (fwd hdr FS n)) ∧
    (∀ e ∈ es, e.Holds L.read σ) ∧ JTHolds L W.layout W.slots

/-- **`PathWords`**: the frame words of an instance's whole path; `main` ends at its closing
jump, a function at its return. -/
def PathWords {κ₀ : ℕ} (W : World κ₀) (tf : TracedFn) (pf : Placed) (fp : ℕ) (σ : Val)
    (es : List Ev) (kfps : List ℕ) (hdr : E × E) (FS : FrameSpec) : Prop :=
  wL (World.cplSite W tf.core.name) fp σ hdr FS (AgOf W fp σ es hdr FS pf.fn.frameSize)
    pf.fn.body tf.core.body 0 ((List.range kfps.length).zip kfps) (fun _ => False)
    (fun _ _ _ => False) (tf.core.name ≠ "main") (tf.core.name = "main")

/-- **(Frame side)** The frame family's words describe every path. -/
def FrameWordsStmt : Prop :=
  ∀ {κ₀ : ℕ} (W : World κ₀), W.Compiled → ∀ tf ∈ W.p, Scoped tf → ∀ pf, World.PlacedAs W tf pf →
  TmpsApart tf pf → NoSelfCall tf →
  ∀ (fp : ℕ), (tf.core.name = "main" → fp = 0) → ∀ (kfps : List ℕ) (hdr : E × E),
  ∃ FS : Val → FrameSpec, FrameCongr tf pf FS ∧
    ∀ (σ : Val) (es : List Ev) (vs : List V), walk σ tf.core.body = .ret es vs →
      (∀ q ∈ addrs es, σ q.1 = ofK (addressOfIndex (fp + (cellP pf.locs q.2).getD 0))) →
      (∀ rd : Reader, (∀ e ∈ es, e.Holds rd σ) →
        FrameClauses (loopTable W.p) tf pf fp σ es vs hdr (FS σ)) ∧
      (kfps.length = (calls es).length → PathWords W tf pf fp σ es kfps hdr (FS σ))

/-- **(Run side)** The path's frame words, on a memory holding the frame, give the instructions'
meaning. -/
def PathRunStmt : Prop :=
  ∀ {κ₀ : ℕ} (W : World κ₀), W.Compiled → ∀ tf ∈ W.p, ∀ pf, World.PlacedAs W tf pf →
  ∀ (fp : ℕ) (σ : Val) (es : List Ev) (kfps : List ℕ) (hdr : E × E) (FS : FrameSpec),
    PathWords W tf pf fp σ es kfps hdr FS →
    ∀ {κ : ℕ} (L : MemoryImage κ) (ck : List (Opcode → ℕ)),
      FrameOK L (loopTable W.p) tf pf.fn.frameSize fp FS σ es kfps hdr →
      (∀ e ∈ es, e.Holds L.read σ) → JTHolds L W.layout W.slots →
      World.KidsRunP (World.withL W L) σ es kfps ck →
      World.CplBody (World.withL W L) tf pf fp σ (kfps.zip ck)

end
end LeanVM.Guest.Backend.Complete
