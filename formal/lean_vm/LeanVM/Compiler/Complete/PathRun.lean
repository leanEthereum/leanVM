/-
  LeanVM.Compiler.Complete.PathRun

  The run side of the frame: the frame words of a path (`PathWords`), on a memory holding the
  frame, give the instructions' meaning (`CplBody`); with the frame side, the frame is consistent.
-/

module

public import LeanVM.Compiler.Complete.Run

/-!
# The frame words of a path give its instructions' meaning

`PathWords` (`wS`/`wL`/`wStages`/`wArms`) and the instructions' meaning (`cplS`/`cplL`/
`cplStages`/`cplArms`) are one recursion with one cursor. On a memory `Ag` admits, a straight-line
instruction `HW` says holds; a `JW` jump reads its frame words from its cells and goes their way;
a call of index `i` (`CallW`) is the path's entered call `i` of its callee, so the callees' runs
(`KidsRunP`) give the callee's counted run, whose return registers are the header `kh i` the frame
put in the callee frame. The calls of `wS` take `(index, frame)` pairs, those of `cplS` the kids
`(frame, counts)`; both are the same suffix of the path's calls (`KR`).

The proof is one structural induction, as `Run.lean`'s, each construct a lemma of its own.
-/

namespace LeanVM.Compiler.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- A function's site on another memory. -/
def onL {κ₀ κ : ℕ} (Γ : Site κ₀) (L : MemoryImage κ) : Site κ :=
  ⟨L, Γ.l, Γ.pc0, Γ.frame, Γ.Pre, Γ.Post⟩

section Words

variable {κ₀ κ : ℕ} (prog : LeanIsaProgram) (Γ₀ : Site κ₀) (L : MemoryImage κ) (fp : ℕ)
  (σ : Val) (hdr : E × E) (FS : FrameSpec) (Ag : (κ : ℕ) → MemoryImage κ → Prop) (cl : List Call)
  (KR : List (ℕ × ℕ) → List Kid → Prop)

/-- What the run side needs of the memory and the callees: `Ag` admits it, its frame's header
returns to `hdr`, and the calls' `(index, frame)` pairs and the kids are the same calls: each
callee frame returns to its header `kh i`, and the path's entered call `i` of a callee runs. -/
structure RunCtx : Prop where
  ag : Ag κ L
  ret : retRegs L (addressOfIndex fp) = some ⟨hdr.1.limb 0, hdr.2.limb 0⟩
  kid : ∀ i kfp ks kids, KR ((i, kfp) :: ks) kids → ∃ ck kids', kids = (kfp, ck) :: kids' ∧
    KR ks kids' ∧ retRegs L (addressOfIndex kfp) = some ⟨(FS.kh i).1.limb 0, (FS.kh i).2.limb 0⟩ ∧
    ∀ callee, (∃ c, cl[i]? = some c ∧ c.f = callee ∧ c.taken = true) →
      ∃ r, KidRuns prog L (Γ₀.ent callee) kfp ck r

/-- A placed statement's frame words give its instructions' meaning. -/
def SW (s : PStmt) : Prop :=
  ∀ (cs : List Stmt) (pos : ℕ) (ks : List (ℕ × ℕ)) (kids : List Kid)
    (next : List Stmt → List (ℕ × ℕ) → Prop) (next' : List Stmt → List Kid → Prop)
    (kj : List (ℕ × ℕ) → E → E → Prop) (kj' : List Kid → E → E → Prop) (kret khalt : Prop),
    KR ks kids → (∀ cs' ks' kids', KR ks' kids' → next cs' ks' → next' cs' kids') →
    (∀ ks' kids' d f, KR ks' kids' → kj ks' d f → kj' kids' d f) →
    wS Γ₀ fp σ hdr FS Ag cl s cs pos ks next kj kret khalt →
    cplS prog (onL Γ₀ L) (addressOfIndex fp) σ s cs pos kids next' kj' kret khalt

/-- A placed block's frame words give its instructions' meaning. -/
def LW (ps : List PStmt) : Prop :=
  ∀ (cs : List Stmt) (pos : ℕ) (ks : List (ℕ × ℕ)) (kids : List Kid)
    (next : List (ℕ × ℕ) → Prop) (next' : List Kid → Prop)
    (kj : List (ℕ × ℕ) → E → E → Prop) (kj' : List Kid → E → E → Prop) (kret khalt : Prop),
    KR ks kids → (∀ ks' kids', KR ks' kids' → next ks' → next' kids') →
    (∀ ks' kids' d f, KR ks' kids' → kj ks' d f → kj' kids' d f) →
    wL Γ₀ fp σ hdr FS Ag cl ps cs pos ks next kj kret khalt →
    cplL prog (onL Γ₀ L) (addressOfIndex fp) σ ps cs pos kids next' kj' kret khalt

/-- A jump into a chain's stages. -/
def StW (sts : List (List (List PStmt))) : Prop :=
  ∀ (cms : List Stmt) (pos : ℕ) (next : List (ℕ × ℕ) → Prop) (next' : List Kid → Prop)
    (kret khalt : Prop) (ks : List (ℕ × ℕ)) (kids : List Kid) (d f : E),
    KR ks kids → (∀ ks' kids', KR ks' kids' → next ks' → next' kids') →
    wStages Γ₀ fp σ hdr FS Ag cl sts cms pos next kret khalt ks d f →
    cplStages prog (onL Γ₀ L) (addressOfIndex fp) σ sts cms pos next' kret khalt kids d f

/-- A jump into a stage's arms. -/
def ArW (xv : V) (pas : List (List PStmt)) : Prop :=
  ∀ (arms : List (List Stmt)) (j pos : ℕ) (kj : List (ℕ × ℕ) → E → E → Prop)
    (kj' : List Kid → E → E → Prop) (kret khalt : Prop) (ks : List (ℕ × ℕ)) (kids : List Kid)
    (d f : E), KR ks kids → (∀ ks' kids' d f, KR ks' kids' → kj ks' d f → kj' kids' d f) →
    wArms Γ₀ fp σ hdr FS Ag cl xv pas arms j pos kj kret khalt ks d f →
    cplArms prog (onL Γ₀ L) (addressOfIndex fp) σ xv pas arms j pos kj' kret khalt kids d f

variable {prog Γ₀ L fp σ hdr FS Ag cl KR}

/-- A straight-line instruction on frame words holds on the memory. -/
theorem hw_at (hA : Ag κ L) {pc : ℕ} {o : LOp} (h : HW Γ₀ fp Ag pc o) :
    Holds L pc (addressOfIndex fp) ((onL Γ₀ L).R o) :=
  h κ L hA

/-- Straight-line instructions on frame words hold on the memory. -/
theorem segW_at (hA : Ag κ L) {ops : List LOp} {pos : ℕ} (h : SegW Γ₀ fp Ag ops pos) :
    SegHolds (onL Γ₀ L) (addressOfIndex fp) ops pos :=
  fun i hi => h i hi κ L hA

theorem idx_mul (a b : ℕ) : addressOfIndex a * addressOfIndex b = addressOfIndex (a + b) := by
  simp [Parameters.addressOfIndex, pow_add]

/-- A jump on frame words is a jump on the memory. -/
theorem jw_at (hA : Ag κ L) {oc od of : ℕ} {fall fall' : Prop} {taken taken' : E → E → Prop}
    (h : JW fp hdr FS Ag oc od of fall taken) (hf : fall → fall')
    (ht : ∀ d f, taken d f → taken' d f) :
    JumpAt (onL Γ₀ L) (addressOfIndex fp) oc od of fall' taken' := by
  obtain ⟨hr, hc, hd, hf', h0, h1⟩ := h
  refine ⟨_, _, _, ?_, ?_, ?_, hc, hd, hf', fun e => hf (h0 e), fun e => ht _ _ (h1 e)⟩ <;>
    simp only [onL, idx_mul] <;> exact hr κ L hA _ (by simp)

/-- The registers a callee returns to, from the header its frame holds. -/
theorem callee_ret (hx : RunCtx prog Γ₀ L fp hdr FS Ag cl KR) {i kfp : ℕ} {ks : List (ℕ × ℕ)}
    {kids : List Kid} {callee : String} {ret : E × E} {d f : E}
    (hK : KR ((i, kfp) :: ks) kids) (hc : CallW Γ₀ FS cl callee kfp i ret d f) :
    ∃ ck kids', kids = (kfp, ck) :: kids' ∧ KR ks kids' ∧
      d = ofK (addressOfIndex ((onL Γ₀ L).ent callee)) ∧ f = ofK (addressOfIndex kfp) ∧
      ∃ r, KidRuns prog L ((onL Γ₀ L).ent callee) kfp ck r ∧ r = ⟨ret.1.limb 0, ret.2.limb 0⟩ := by
  obtain ⟨ck, kids', rfl, hK', hrr, hrun⟩ := hx.kid i kfp ks kids hK
  obtain ⟨hcl, rfl, rfl, hkh⟩ := hc
  obtain ⟨r, hr⟩ := hrun callee hcl
  refine ⟨ck, kids', rfl, hK', rfl, rfl, r, hr, ?_⟩
  have := hr.1.symm.trans hrr
  subst hkh
  exact Option.some.inj this

/-! ## The constructs -/

/-- **One instruction.** -/
theorem op_w (hx : RunCtx prog Γ₀ L fp hdr FS Ag cl KR) (h : List LHint) (o : LOp) :
    SW prog Γ₀ L fp σ hdr FS Ag cl KR (.op h o) := by
  intro cs pos ks kids next next' kj kj' kret khalt hK hn hj hw
  cases o
  case jump oc od of =>
    simp only [wS] at hw
    simp only [cplS, OpSem]
    exact jw_at hx.ag hw (hn _ _ _ hK) (fun d f => hj _ _ d f hK)
  all_goals
    simp only [wS] at hw
    simp only [cplS, OpSem]
    exact ⟨hw.1 κ L hx.ag, hn _ _ _ hK hw.2⟩

/-- **The empty block.** -/
theorem nil_w : LW prog Γ₀ L fp σ hdr FS Ag cl KR [] := by
  intro cs pos ks kids next next' kj kj' kret khalt hK hn _ hw
  exact hn _ _ hK hw

/-- **A statement, then a block.** -/
theorem cons_w {s : PStmt} {ss : List PStmt} (hs : SW prog Γ₀ L fp σ hdr FS Ag cl KR s)
    (hss : LW prog Γ₀ L fp σ hdr FS Ag cl KR ss) : LW prog Γ₀ L fp σ hdr FS Ag cl KR (s :: ss) := by
  intro cs pos ks kids next next' kj kj' kret khalt hK hn hj hw
  simp only [wL] at hw
  simp only [cplL]
  refine hs cs pos ks kids _ _ _ _ kret khalt hK
    (fun cs' ks' kids' hK' h => hss cs' _ ks' kids' next next' kj kj' kret khalt hK' hn hj h)
    (fun ks' kids' d f hK' h => ?_) hw
  cases ss with
  | nil => exact hj ks' kids' d f hK' h
  | cons _ _ => exact h.elim

/-- **An `ite`.** -/
theorem ite_w (hx : RunCtx prog Γ₀ L fp hdr FS Ag cl KR) {h : List LHint} {c bdest sfp : Cell}
    {zero nonzero : List PStmt} {hasElse : Bool} {edest one : Cell}
    (hz : LW prog Γ₀ L fp σ hdr FS Ag cl KR zero) (hnz : LW prog Γ₀ L fp σ hdr FS Ag cl KR nonzero) :
    SW prog Γ₀ L fp σ hdr FS Ag cl KR (.ite h c bdest sfp zero hasElse edest one nonzero) := by
  intro cs pos ks kids next next' kj kj' kret khalt hK hn hj hw
  rcases hcs : ctrlSplit cs with _ | ⟨s, rest⟩
  · simp [wS, hcs] at hw
  cases s
  case ite cv z n =>
    simp only [wS, hcs] at hw
    simp only [cplS, hcs]
    obtain ⟨hb, hjw⟩ := hw
    refine ⟨hw_at hx.ag hb, jw_at hx.ag hjw (fun ⟨h0, hzw⟩ => ⟨h0, hz _ _ ks kids _ _ _ _ kret khalt
      hK (fun ks' kids' hK' h => ?_) (fun _ _ _ _ _ h => h.elim) hzw⟩)
      (fun d f ⟨h0, hd, hf, hnw⟩ => ⟨h0, hd, hf, ?_⟩)⟩
    · cases hasElse
      · exact hn _ _ _ hK' h
      · simp only [↓reduceIte] at h ⊢
        exact ⟨hw_at hx.ag h.1, jw_at hx.ag h.2 id
          (fun d f ⟨hd, hf, hr⟩ => ⟨hd, hf, hn _ _ _ hK' hr⟩)⟩
    · cases hasElse
      · exact hn _ _ _ hK hnw
      · simp only [↓reduceIte] at hnw ⊢
        exact hnz _ _ ks kids _ _ _ _ kret khalt hK (fun ks' kids' hK' h => hn _ _ _ hK' h)
          (fun _ _ _ _ _ h => h.elim) hnw
  all_goals simp [wS, hcs] at hw

/-- **The return.** -/
theorem ret_w (hx : RunCtx prog Γ₀ L fp hdr FS Ag cl KR) (h : List LHint) (one : Cell) :
    SW prog Γ₀ L fp σ hdr FS Ag cl KR (.ret h one) := by
  intro cs pos ks kids next next' kj kj' kret khalt hK hn hj hw
  simp only [wS] at hw
  simp only [cplS]
  exact jw_at hx.ag hw id (fun _ _ h => h)

/-- **`main`'s closing jump.** -/
theorem halt_w (hx : RunCtx prog Γ₀ L fp hdr FS Ag cl KR) (h : List LHint) (one dest : Cell) :
    SW prog Γ₀ L fp σ hdr FS Ag cl KR (.halt h one dest) := by
  intro cs pos ks kids next next' kj kj' kret khalt hK hn hj hw
  simp only [wS] at hw
  simp only [cplS]
  exact ⟨hw_at hx.ag hw.1, jw_at hx.ag hw.2 id (fun _ _ h => h)⟩

/-- **A call.** -/
theorem call_w (hx : RunCtx prog Γ₀ L fp hdr FS Ag cl KR) (h : List LHint) (c : CallSite) :
    SW prog Γ₀ L fp σ hdr FS Ag cl KR (.call h c) := by
  intro cs pos ks kids next next' kj kj' kret khalt hK hn hj hw
  rcases hcs : ctrlSplit cs with _ | ⟨s, rest⟩
  · simp [wS, hcs] at hw
  rcases ks with _ | ⟨⟨i, kfp⟩, ks'⟩
  · simp [wS, hcs] at hw
  obtain ⟨ck, kids', rfl, hK', -⟩ := hx.kid i kfp ks' kids hK
  simp only [wS, hcs] at hw
  simp only [cplS, hcs]
  obtain ⟨hpre, hjw⟩ := hw
  refine ⟨segW_at hx.ag hpre, jw_at hx.ag hjw
    (fun ⟨h0, hr, hnx⟩ => ⟨h0, segW_at hx.ag hr, hn _ _ _ hK' hnx⟩)
    (fun d f ⟨ht, hrest⟩ => ⟨ht, ?_⟩)⟩
  cases htl : c.tail
  · simp only [htl, Bool.false_eq_true, ↓reduceIte] at hrest ⊢
    obtain ⟨hcw, hr, hnx⟩ := hrest
    obtain ⟨ck', kids'', he, -, hd, hf, r, hrun, rfl⟩ := callee_ret hx hK hcw
    cases he
    refine ⟨hd, hf, _, hrun, ?_, segW_at hx.ag hr, hn _ _ _ hK' hnx⟩
    simp only [tgt_limb, limb_ofK]
    rfl
  · simp only [htl, ↓reduceIte] at hrest ⊢
    obtain ⟨hcw, hk⟩ := hrest
    obtain ⟨ck', kids'', he, -, hd, hf, r, hrun, rfl⟩ := callee_ret hx hK hcw
    cases he
    exact ⟨hd, hf, _, hrun, hx.ret, hk⟩

/-- **A loop helper's closing call.** -/
theorem loopNext_w (hx : RunCtx prog Γ₀ L fp hdr FS Ag cl KR) (h : List LHint) (callee : String)
    (nfp entry oc one : Cell) (args : List Cell) :
    SW prog Γ₀ L fp σ hdr FS Ag cl KR (.loopNext h callee nfp entry oc one args) := by
  intro cs pos ks kids next next' kj kj' kret khalt hK hn hj hw
  rcases hcs : ctrlSplit cs with _ | ⟨s, rest⟩
  · simp [wS, hcs] at hw
  rcases ks with _ | ⟨⟨i, kfp⟩, ks'⟩
  · simp [wS, hcs] at hw
  obtain ⟨ck, kids', rfl, hK', -⟩ := hx.kid i kfp ks' kids hK
  simp only [wS, hcs] at hw
  simp only [cplS, hcs]
  obtain ⟨hpre, hjw⟩ := hw
  refine ⟨segW_at hx.ag hpre, jw_at hx.ag hjw (fun ⟨h0, hnx⟩ => ⟨h0, hn _ _ _ hK' hnx⟩)
    (fun d f ⟨ht, hcw, hk⟩ => ?_)⟩
  obtain ⟨ck', kids'', he, -, hd, hf, r, hrun, rfl⟩ := callee_ret hx hK hcw
  cases he
  exact ⟨ht, hd, hf, _, hrun, hx.ret, hk⟩

/-- **A fused `match` of calls.** -/
theorem dispatch_w (hx : RunCtx prog Γ₀ L fp hdr FS Ag cl KR) (h : List LHint)
    (callees : List String) (nfp joinCell x entry one : Cell) (first : ℕ) (args rets : List Cell) :
    SW prog Γ₀ L fp σ hdr FS Ag cl KR
      (.dispatch h callees nfp joinCell x entry one first args rets) := by
  intro cs pos ks kids next next' kj kj' kret khalt hK hn hj hw
  rcases hcs : ctrlSplit cs with _ | ⟨s, rest⟩
  · simp [wS, hcs] at hw
  rcases ks with _ | ⟨⟨i, kfp⟩, ks'⟩
  · simp [wS, hcs] at hw
  obtain ⟨ck, kids', rfl, hK', -⟩ := hx.kid i kfp ks' kids hK
  simp only [wS, hcs] at hw
  simp only [cplS, hcs]
  obtain ⟨hpre, hjw⟩ := hw
  refine ⟨segW_at hx.ag hpre, jw_at hx.ag hjw id (fun d f ⟨g, hg, hcw, hr, hnx⟩ => ?_)⟩
  obtain ⟨ck', kids'', he, -, hd, hf, r, hrun, rfl⟩ := callee_ret hx hK hcw
  cases he
  refine ⟨hf, g, hg, hd, _, hrun, ?_, segW_at hx.ag hr, hn _ _ _ hK' hnx⟩
  simp only [tgt_limb, limb_ofK]
  rfl

/-- **No arms.** -/
theorem armsNil_w (xv : V) : ArW prog Γ₀ L fp σ hdr FS Ag cl KR xv [] := by
  intro arms j pos kj kj' kret khalt ks kids d f _ _ hw
  simp [wArms] at hw

/-- **An arm, then the arms after it.** -/
theorem armsCons_w {xv : V} {pa : List PStmt} {pas : List (List PStmt)}
    (hpa : LW prog Γ₀ L fp σ hdr FS Ag cl KR pa) (hpas : ArW prog Γ₀ L fp σ hdr FS Ag cl KR xv pas) :
    ArW prog Γ₀ L fp σ hdr FS Ag cl KR xv (pa :: pas) := by
  intro arms j pos kj kj' kret khalt ks kids d f hK hj hw
  rcases arms with _ | ⟨a, as⟩
  · simp [wArms] at hw
  simp only [wArms] at hw
  simp only [cplArms]
  by_cases hxj : σ xv = ofK (addressOfIndex j)
  · simp only [hxj, ↓reduceIte] at hw ⊢
    obtain ⟨hd, hf, hb⟩ := hw
    exact ⟨hd, hf, hpa a pos ks kids _ _ kj kj' kret khalt hK
      (fun ks' kids' hK' h => hj _ _ _ _ hK' h) hj hb⟩
  · simp only [hxj, ↓reduceIte] at hw ⊢
    exact hpas as (j + 1) _ kj kj' kret khalt ks kids d f hK hj hw

/-- **Past the last stage: the join.** -/
theorem stagesNil_w : StW prog Γ₀ L fp σ hdr FS Ag cl KR [] := by
  intro cms pos next next' kret khalt ks kids d f hK hn hw
  simp only [wStages] at hw
  simp only [cplStages]
  exact ⟨hw.1, hw.2.1, hn _ _ hK hw.2.2⟩

/-- **A stage, then the stages after it.** -/
theorem stagesCons_w {st : List (List PStmt)} {sts : List (List (List PStmt))}
    (har : ∀ xv, ArW prog Γ₀ L fp σ hdr FS Ag cl KR xv st)
    (hsts : StW prog Γ₀ L fp σ hdr FS Ag cl KR sts) :
    StW prog Γ₀ L fp σ hdr FS Ag cl KR (st :: sts) := by
  intro cms pos next next' kret khalt ks kids d f hK hn hw
  rcases cms with _ | ⟨m, cms'⟩
  · simp [wStages] at hw
  cases m
  case match_ xv arms =>
    simp only [wStages] at hw
    simp only [cplStages]
    exact har xv arms 0 pos _ _ kret khalt ks kids d f hK
      (fun ks' kids' d' f' hK' h => hsts cms' _ next next' kret khalt ks' kids' d' f' hK' hn h) hw
  all_goals simp [wStages] at hw

/-- **A chain of `match`es.** -/
theorem chain_w (hx : RunCtx prog Γ₀ L fp hdr FS Ag cl KR) {h : List LHint}
    {join x entry one sfp : Cell} {firsts : List ℕ} {stages : List (List (List PStmt))}
    (hst : StW prog Γ₀ L fp σ hdr FS Ag cl KR stages) :
    SW prog Γ₀ L fp σ hdr FS Ag cl KR (.chain h join x entry one sfp firsts stages) := by
  intro cs pos ks kids next next' kj kj' kret khalt hK hn hj hw
  rcases hcs : ctrlSplit cs with _ | ⟨s, rest⟩
  · simp [wS, hcs] at hw
  simp only [wS, hcs] at hw
  simp only [cplS, hcs]
  obtain ⟨h0, h1, hjw⟩ := hw
  exact ⟨hw_at hx.ag h0, hw_at hx.ag h1, jw_at hx.ag hjw id (fun d f h =>
    hst _ _ _ _ kret khalt ks kids d f hK (fun ks' kids' hK' h' => hn _ _ _ hK' h') h)⟩

/-! ## Every statement -/

mutual
/-- **A placed statement's frame words give its instructions' meaning.** -/
theorem stmt_w (hx : RunCtx prog Γ₀ L fp hdr FS Ag cl KR) :
    ∀ s : PStmt, SW prog Γ₀ L fp σ hdr FS Ag cl KR s
  | .op h o => op_w hx h o
  | .ite _ _ _ _ zero _ _ _ nonzero => ite_w hx (block_w hx zero) (block_w hx nonzero)
  | .chain _ _ _ _ _ _ _ stages => chain_w hx (stages_w hx stages)
  | .call h c => call_w hx h c
  | .loopNext h callee nfp entry oc one args => loopNext_w hx h callee nfp entry oc one args
  | .dispatch h callees nfp joinCell x entry one first args rets =>
      dispatch_w hx h callees nfp joinCell x entry one first args rets
  | .ret h one => ret_w hx h one
  | .halt h one dest => halt_w hx h one dest

/-- **A placed block's frame words give its instructions' meaning.** -/
theorem block_w (hx : RunCtx prog Γ₀ L fp hdr FS Ag cl KR) :
    ∀ ps : List PStmt, LW prog Γ₀ L fp σ hdr FS Ag cl KR ps
  | [] => nil_w
  | s :: ss => cons_w (stmt_w hx s) (block_w hx ss)

/-- **A jump into a chain's stages.** -/
theorem stages_w (hx : RunCtx prog Γ₀ L fp hdr FS Ag cl KR) :
    ∀ sts : List (List (List PStmt)), StW prog Γ₀ L fp σ hdr FS Ag cl KR sts
  | [] => stagesNil_w
  | st :: sts => stagesCons_w (fun xv => arms_w hx st xv) (stages_w hx sts)

/-- **A jump into a stage's arms.** -/
theorem arms_w (hx : RunCtx prog Γ₀ L fp hdr FS Ag cl KR) :
    ∀ (pas : List (List PStmt)) (xv : V), ArW prog Γ₀ L fp σ hdr FS Ag cl KR xv pas
  | [], xv => armsNil_w xv
  | pa :: pas, xv => armsCons_w (block_w hx pa) (arms_w hx pas xv)
end

end Words

/-! ## The path -/

/-- The calls left: the same suffix of the `(index, frame)` pairs and of the kids. -/
def KRof (kfps : List ℕ) (ck : List (Opcode → ℕ)) (ks : List (ℕ × ℕ)) (kids : List Kid) : Prop :=
  ∃ m, ks = ((List.range kfps.length).zip kfps).drop m ∧ kids = (kfps.zip ck).drop m

/-- The header a frame's cells `0`, `1` hold is where it returns. -/
theorem retRegs_of {κ : ℕ} {L : MemoryImage κ} {a : ℕ} {h : E × E}
    (h0 : L.read (addressOfIndex (a + 0)) = some h.1) (h1 : L.read (addressOfIndex (a + 1)) = some h.2) :
    retRegs L (addressOfIndex a) = some ⟨h.1.limb 0, h.2.limb 0⟩ := by
  simp only [retRegs, idx_mul, h0, h1, Option.bind_some, Option.map_some]

/-- **(Run side) The path's frame words give its instructions' meaning.** -/
theorem pathRunStmt : PathRunStmt := by
  intro κ₀ W _ tf _ pf _ fp σ es kfps hdr FS hw κ L ck hok hev hjt hkr
  have hlen : ck.length = kfps.length := hkr.1.trans hok.len.symm
  have hA : AgOf W tf fp σ es kfps hdr FS pf.fn.frameSize κ L := by
    refine ⟨fun n hn => ?_, hok, fun i c kfp h1 h2 h3 => (hkr.2 i c kfp h1 h2 h3).2, hev, hjt⟩
    rcases n with _ | _ | n
    · simpa [fwd] using hok.hdr0
    · simpa [fwd] using hok.hdr1
    · simpa [fwd] using hok.own (n + 2) (by omega) hn
  have hx : RunCtx (World.withL W L).prog (World.cplSite W tf.core.name) L fp hdr FS
      (AgOf W tf fp σ es kfps hdr FS pf.fn.frameSize) (calls es) (KRof kfps ck) := by
    refine ⟨hA, retRegs_of hok.hdr0 hok.hdr1, ?_⟩
    rintro i kfp ks kids ⟨m, hks, rfl⟩
    have hm : m < ((List.range kfps.length).zip kfps).length := by
      by_contra hc
      rw [List.drop_eq_nil_of_le (by omega)] at hks
      exact List.cons_ne_nil _ _ hks
    have hm' : m < kfps.length := by simpa using hm
    rw [List.drop_eq_getElem_cons hm] at hks
    simp only [List.getElem_zip, List.getElem_range, List.cons.injEq, Prod.mk.injEq] at hks
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hks
    have hz : i < (kfps.zip ck).length := by simp [hlen, hm']
    obtain ⟨c, hc⟩ : ∃ c, (calls es)[i]? = some c :=
      ⟨_, List.getElem?_eq_getElem (by rw [← hok.len]; exact hm')⟩
    have hkf : kfps[i]? = some kfps[i] := List.getElem?_eq_getElem hm'
    obtain ⟨hk0, hk1, -, -⟩ := hok.kid i c _ hc hkf
    refine ⟨ck[i]'(by omega), _, ?_, ⟨i + 1, rfl, rfl⟩, retRegs_of hk0 hk1,
      fun callee ⟨c', hc', hf, ht⟩ => ?_⟩
    · rw [List.drop_eq_getElem_cons hz]
      simp
    obtain ⟨⟨r, hr⟩, -⟩ := hkr.2 i c' _ hc' hkf ht
    subst hf
    have e : ck.getD i 0 = ck[i]'(by omega) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < ck.length by omega)]
    rw [e] at hr
    exact ⟨r, hr⟩
  exact block_w hx pf.fn.body tf.core.body 0 _ _ _ _ _ _ _ _ ⟨0, rfl, rfl⟩ (fun _ _ _ h => h)
    (fun _ _ _ _ _ h => h) hw

/-! ## The frame is consistent -/

/-- **`FrameConsistentStmt` from its two sides.** -/
theorem frameConsistent_of (hW : FrameWordsStmt) (hR : PathRunStmt) : FrameConsistentStmt := by
  intro κ₀ W hc tf htf hsc pf hpl hta hns fp hfp kfps hdr
  obtain ⟨FS, hcg, h⟩ := hW W hc tf htf hsc pf hpl hta hns fp hfp kfps hdr
  refine ⟨FS, hcg, fun σ es vs hw ha => ⟨(h σ es vs hw ha).1, fun L ck hok hev hjt hk => ?_⟩⟩
  exact hR W hc tf htf pf hpl fp σ es kfps hdr (FS σ)
    ((h σ es vs hw ha).2 hok.len hok.tail hok.hdrK ⟨L.read, hev⟩) L ck hok hev hjt hk

/-- **The frame is consistent, given the frame side.** -/
theorem frameConsistent_of_words (hW : FrameWordsStmt) : FrameConsistentStmt :=
  frameConsistent_of hW pathRunStmt

/-- info: 'LeanVM.Compiler.Complete.pathRunStmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pathRunStmt

end
end LeanVM.Compiler.Complete
