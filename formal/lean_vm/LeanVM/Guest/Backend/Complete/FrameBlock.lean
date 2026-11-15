/-
  LeanVM.Guest.Backend.Complete.FrameBlock

  The frame words of a placed block, cut: `wL` with the core cursor handed on, so that the words
  of a block are the words of its parts.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameWalk

/-!
# Blocks of frame words

`wL` hands its continuation the call list only. `wLc` hands on the core cursor too; `wL` is `wLc`
with a continuation that ignores the cursor (`wL_eq_wLc`), and `wLc` of two blocks is `wLc` of the
first continued by `wLc` of the second (`wLc_append`): only the last statement of a block may
jump to the block's `kj`.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

section Words

variable {κ₀ : ℕ} (Γ : Site κ₀) (fp : ℕ) (σ : Val) (hdr : E × E) (FS : FrameSpec)
  (Ag : (κ : ℕ) → MemoryImage κ → Prop) (cl : List Call)

/-- `wL` handing its continuation the core cursor too. -/
def wLc : List PStmt → List Stmt → ℕ → List (ℕ × ℕ) → (List Stmt → List (ℕ × ℕ) → Prop) →
    (List (ℕ × ℕ) → E → E → Prop) → Prop → Prop → Prop
  | [], cs, _, ks, next, _, _, _ => next cs ks
  | s :: ss, cs, pos, ks, next, kj, kret, khalt =>
      wS Γ fp σ hdr FS Ag cl s cs pos ks
        (fun cs' ks' => wLc ss cs' (pos + stmtSize s) ks' next kj kret khalt)
        (if ss.isEmpty then kj else fun _ _ _ => False) kret khalt

theorem wL_eq_wLc : ∀ (ps : List PStmt) (cs : List Stmt) (pos : ℕ) (ks : List (ℕ × ℕ))
    (next : List (ℕ × ℕ) → Prop) (kj : List (ℕ × ℕ) → E → E → Prop) (kret khalt : Prop),
    wL Γ fp σ hdr FS Ag cl ps cs pos ks next kj kret khalt =
      wLc Γ fp σ hdr FS Ag cl ps cs pos ks (fun _ ks' => next ks') kj kret khalt
  | [], _, _, _, _, _, _, _ => by unfold wL; rfl
  | s :: ss, cs, pos, ks, next, kj, kret, khalt => by
      unfold wL
      simp only [wLc]
      congr 1
      funext cs' ks'
      exact wL_eq_wLc ss cs' _ ks' next kj kret khalt

theorem wLc_append : ∀ (ps ps' : List PStmt), ps' ≠ [] → ∀ (cs : List Stmt) (pos : ℕ)
    (ks : List (ℕ × ℕ)) (next : List Stmt → List (ℕ × ℕ) → Prop)
    (kj : List (ℕ × ℕ) → E → E → Prop) (kret khalt : Prop),
    wLc Γ fp σ hdr FS Ag cl (ps ++ ps') cs pos ks next kj kret khalt =
      wLc Γ fp σ hdr FS Ag cl ps cs pos ks
        (fun cs' ks' => wLc Γ fp σ hdr FS Ag cl ps' cs' (pos + blockSize ps) ks' next kj kret khalt)
        (fun _ _ _ => False) kret khalt
  | [], ps', _, cs, pos, ks, next, kj, kret, khalt => by
      rw [List.nil_append, wLc, blockSize, Nat.add_zero]
  | s :: ss, ps', hps, cs, pos, ks, next, kj, kret, khalt => by
      rw [List.cons_append, wLc, wLc]
      have hk : (if (ss ++ ps').isEmpty then kj else fun _ _ _ => False) =
          (if ss.isEmpty then (fun _ _ _ => False : List (ℕ × ℕ) → E → E → Prop)
            else fun _ _ _ => False) := by
        cases ps' with
        | nil => exact absurd rfl hps
        | cons p ps'' => simp
      rw [hk]
      congr 1
      funext cs' ks'
      rw [wLc_append ss ps' hps cs' (pos + stmtSize s) ks' next kj kret khalt, blockSize,
        Nat.add_assoc]

end Words

/-! ## The walk on the path: invariant and the words of a block -/

/-- The events of an outcome. -/
def outEs : Out → List Ev
  | .fall es => es
  | .ret es _ => es
  | .stuck => []

/-- **The walk's invariant on the path**, in lockstep with the scope walk at `s`: the constraint
keeps its properties, both walks are at one event, the values in scope are known (once the final
placement extends the state), and while the path has made no return area the constraint does not
mention the return cells. -/
structure WInv (ctx : Ctx) (I : Inst) (C : (ℕ → E) → Prop) (st : St) (s : SSt) : Prop where
  cok : COk I C st.next st.scope st.locs
  rest : s.rest = st.rest
  vw : Fits I st → VW I C st (fun v => s.live.contains v = true)
  two : 2 ≤ st.next
  ret : s.retDone = false → ∀ Ψ k w, k < ctx.retCells → C Ψ →
    C (Function.update Ψ (2 + ctx.argCells + k) w)

/-- What the continuation of a block's words asks, by how the block's path ends: falling through,
`next` of every cursor that stands for the statements after it, with the calls left. -/
def OutK (o : Out) (tl : List Stmt) (next : List Stmt → List (ℕ × ℕ) → Prop) (kret : Prop)
    (ks : List (ℕ × ℕ)) : Prop :=
  match o with
  | .fall es => ∀ cs', ctrlSplit cs' = ctrlSplit tl → next cs' (ks.drop (calls es).length)
  | .ret _ _ => kret
  | .stuck => False

/-- The calls of a block's path, from call index `i₀` of the whole path `cl`: each takes a callee
frame from `ks` and its header `hs[j]` in `kh`. -/
def KsAt (cl : List Call) (kh : ℕ → E × E) (i₀ : ℕ) (bc : List Call) (hs : List (E × E))
    (ks : List (ℕ × ℕ)) : Prop :=
  hs.length = bc.length ∧ ∀ j < bc.length, (∃ kfp, ks[j]? = some (i₀ + j, kfp)) ∧
    cl[i₀ + j]? = bc[j]? ∧ kh (i₀ + j) = hs.getD j (0, 0)

/-- **The words of a placed block on the path**: the block `blk` placed for the core statements
`ss` (followed by `tl`) whose path under the instance's valuation is `o`, its calls from index
`i₀`; for every frame word the constraint allows and every valuation `Same` as the instance's,
its statements' words (`wLc`), the memories being `Ag σ' Ψ kh`, with headers `hs pos`. -/
def BlkW {κ₀ : ℕ} (Γ : Site κ₀) (I : Inst)
    (Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop) (cl : List Call)
    (C : (ℕ → E) → Prop) (blk : List PStmt) (ss tl : List Stmt) (o : Out) (i₀ : ℕ) : Prop :=
  ∃ hs : ℕ → List (E × E), (∀ pos, (hs pos).length = (calls (outEs o)).length) ∧
  ∀ Ψ, C Ψ → ∀ σ', I.Same σ' → ∀ (kh : ℕ → E × E) (cs : List Stmt)
    (pos : ℕ) (ks : List (ℕ × ℕ)) (next : List Stmt → List (ℕ × ℕ) → Prop)
    (kj : List (ℕ × ℕ) → E → E → Prop) (kret khalt : Prop),
    (∀ o' ∈ blockOps blk pos, o' ∈ I.ops) →
    ctrlSplit cs = ctrlSplit (ss ++ tl) → KsAt cl kh i₀ (calls (outEs o)) (hs pos) ks →
    OutK o tl next kret ks →
    wLc Γ I.fp σ' I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) cl blk cs pos ks next kj kret khalt

/-- `FAt` for actions that place control statements: the constraint's properties kept, the next
free cell and the places growing, the result under the new constraint and state. -/
def FBAt {α : Type} (ctx : Ctx) (I : Inst) (C : (ℕ → E) → Prop) (st : St) (m : P α)
    (R : α → ((ℕ → E) → Prop) → St → Prop) : Prop :=
  COk I C st.next st.scope st.locs →
  wpP m ctx st fun a st' => ∃ C', (∃ Ψ, C' Ψ) ∧ Blind C' st'.next ∧ Stronger C' C ∧
    st.next ≤ st'.next ∧ LocsLe st.locs st'.locs ∧ R a C' st'

/-- **The block lemma's statement**: placing the core block `ss` (followed by `tl`) on the path
of the instance, in lockstep with the scope walk from `s` to `s'`, keeps the invariant if the
path falls through it (after a return the rest is off the path: only the constraint's
satisfiability and blindness are kept), and lays statements whose words are `BlkW` (once the
final placement extends the state reached and has their instructions). -/
def BlockW {κ₀ : ℕ} (Γ : Site κ₀) (Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) →
    MemoryImage κ → Prop) (cl : List Call) (ctx : Ctx) (I : Inst) (m : P Unit)
    (ss tl : List Stmt) : Prop :=
  ∀ (C : (ℕ → E) → Prop) (st : St) (s s' : SSt) (i₀ : ℕ) (o : Out),
    scopeBlock ctx.retCells ss s = .ok s' → walk I.σ ss = o → o ≠ .stuck →
    (∀ e ∈ outEs o, e ∈ I.es) → (∀ j < (calls (outEs o)).length, cl[i₀ + j]? = (calls (outEs o))[j]?) →
    WInv ctx I C st s →
    FBAt ctx I C st m fun _ C' st' => (∀ es, o = .fall es → WInv ctx I C' st' s') ∧
      ∃ blk, st'.out.toList = st.out.toList ++ blk ∧
        (Fits I st' → BlkW Γ I Ag cl C' blk ss tl o i₀)

theorem bsize_append (a b : List PStmt) : blockSize (a ++ b) = blockSize a + blockSize b := by
  induction a with
  | nil => simp [blockSize]
  | cons s ss ih => simp [blockSize, ih, Nat.add_assoc]

theorem bops_append (a b : List PStmt) (pos : ℕ) :
    blockOps (a ++ b) pos = blockOps a pos ++ blockOps b (pos + blockSize a) := by
  induction a generalizing pos with
  | nil => simp [blockOps, blockSize]
  | cons s ss ih => simp [blockOps, blockSize, ih, Nat.add_assoc]

section Compose

variable {κ₀ : ℕ} {Γ : Site κ₀} {I : Inst}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}

theorem BlkW.mono {C C' : (ℕ → E) → Prop} {blk : List PStmt} {ss tl : List Stmt} {o : Out}
    {i₀ : ℕ} (h : BlkW Γ I Ag cl C blk ss tl o i₀) (hs : Stronger C' C) :
    BlkW Γ I Ag cl C' blk ss tl o i₀ := by
  obtain ⟨hs', hl, h⟩ := h
  exact ⟨hs', hl, fun Ψ hΨ => h Ψ (hs Ψ hΨ)⟩

/-- A block whose path returns, then statements off the path. -/
theorem BlkW.append_ret {C : (ℕ → E) → Prop} {blk₁ blk₂ : List PStmt} {ss₁ ss₂ tl : List Stmt}
    {es : List Ev} {vs : List V} {i₀ : ℕ}
    (h₁ : BlkW Γ I Ag cl C blk₁ ss₁ (ss₂ ++ tl) (.ret es vs) i₀) :
    BlkW Γ I Ag cl C (blk₁ ++ blk₂) (ss₁ ++ ss₂) tl (.ret es vs) i₀ := by
  obtain ⟨hs, hl, h⟩ := h₁
  refine ⟨hs, hl, fun Ψ hΨ σ' hσ kh cs pos ks next kj kret khalt hops hcs hks hk => ?_⟩
  have hops₁ : ∀ o' ∈ blockOps blk₁ pos, o' ∈ I.ops := fun o' ho =>
    hops o' (by rw [bops_append]; exact List.mem_append_left _ ho)
  have hcs₁ : ctrlSplit cs = ctrlSplit (ss₁ ++ (ss₂ ++ tl)) := by rwa [← List.append_assoc]
  cases blk₂ with
  | nil =>
    rw [List.append_nil]
    exact h Ψ hΨ σ' hσ kh cs pos ks next kj kret khalt hops₁ hcs₁ hks hk
  | cons b bs =>
    rw [wLc_append _ _ _ _ _ _ _ blk₁ (b :: bs) (List.cons_ne_nil _ _)]
    exact h Ψ hΨ σ' hσ kh cs pos ks _ _ kret khalt hops₁ hcs₁ hks hk

theorem calls_append' (a b : List Ev) : calls (a ++ b) = calls a ++ calls b := by
  simp [calls, List.filterMap_append]

theorem BlkW.append_core {C : (ℕ → E) → Prop} {blk₁ blk₂ : List PStmt} {ss₁ ss₂ tl : List Stmt}
    {es₁ : List Ev} {o o₂ : Out} {i₀ : ℕ}
    (hc : calls (outEs o) = calls es₁ ++ calls (outEs o₂))
    (hk : ∀ next kret ks, OutK o tl next kret ks →
      OutK o₂ tl next kret (ks.drop (calls es₁).length))
    (h₁ : BlkW Γ I Ag cl C blk₁ ss₁ (ss₂ ++ tl) (.fall es₁) i₀)
    (h₂ : BlkW Γ I Ag cl C blk₂ ss₂ tl o₂ (i₀ + (calls es₁).length)) :
    BlkW Γ I Ag cl C (blk₁ ++ blk₂) (ss₁ ++ ss₂) tl o i₀ := by
  obtain ⟨hs₁, hl₁, h₁⟩ := h₁
  obtain ⟨hs₂, hl₂, h₂⟩ := h₂
  simp only [outEs] at hl₁
  refine ⟨fun pos => hs₁ pos ++ hs₂ (pos + blockSize blk₁), fun pos => by
    rw [List.length_append, hl₁, hl₂, hc, List.length_append], ?_⟩
  intro Ψ hΨ σ' hσ kh cs pos ks next kj kret khalt hops hcs hks hk'
  obtain ⟨-, hks⟩ := hks
  rw [hc] at hks
  have hn₁ := hl₁ pos
  have hops₁ : ∀ o' ∈ blockOps blk₁ pos, o' ∈ I.ops := fun o' ho =>
    hops o' (by rw [bops_append]; exact List.mem_append_left _ ho)
  have hops₂ : ∀ o' ∈ blockOps blk₂ (pos + blockSize blk₁), o' ∈ I.ops := fun o' ho =>
    hops o' (by rw [bops_append]; exact List.mem_append_right _ ho)
  have hcs₁ : ctrlSplit cs = ctrlSplit (ss₁ ++ (ss₂ ++ tl)) := by rwa [← List.append_assoc]
  have hks₁ : KsAt cl kh i₀ (calls (outEs (.fall es₁))) (hs₁ pos) ks := by
    refine ⟨hn₁, fun j hj => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hks j (by rw [List.length_append]; simp only [outEs] at hj; omega)
    simp only [outEs] at hj ⊢
    refine ⟨h1, by rw [h2, List.getElem?_append_left hj], ?_⟩
    rw [h3, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [hn₁]; exact hj)]
  have hnext : ∀ cs', ctrlSplit cs' = ctrlSplit (ss₂ ++ tl) →
      wLc Γ I.fp σ' I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) cl blk₂ cs' (pos + blockSize blk₁)
        (ks.drop (calls es₁).length) next kj kret khalt := by
    intro cs' hcs'
    refine h₂ Ψ hΨ σ' hσ kh cs' _ _ next kj kret khalt hops₂ hcs' ⟨hl₂ _, fun j hj => ?_⟩
      (hk next kret ks hk')
    obtain ⟨⟨kfp, h1⟩, h2, h3⟩ := hks ((calls es₁).length + j)
      (by rw [List.length_append]; omega)
    refine ⟨⟨kfp, by rw [List.getElem?_drop, h1, Nat.add_assoc]⟩, ?_, ?_⟩
    · rw [Nat.add_assoc, h2, List.getElem?_append_right (by omega)]
      simp
    · rw [Nat.add_assoc, h3, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega), hn₁]
      simp
  cases blk₂ with
  | nil =>
    rw [List.append_nil]
    refine h₁ Ψ hΨ σ' hσ kh cs pos ks next kj kret khalt hops₁ hcs₁ hks₁ fun cs' hcs' => ?_
    have := hnext cs' hcs'
    rwa [wLc] at this
  | cons b bs =>
    rw [wLc_append _ _ _ _ _ _ _ blk₁ (b :: bs) (List.cons_ne_nil _ _)]
    exact h₁ Ψ hΨ σ' hσ kh cs pos ks _ _ kret khalt hops₁ hcs₁ hks₁ hnext

/-- A block whose path falls through, then a block on the path. -/
theorem BlkW.append_fall {C : (ℕ → E) → Prop} {blk₁ blk₂ : List PStmt} {ss₁ ss₂ tl : List Stmt}
    {es₁ : List Ev} {o₂ : Out} {i₀ : ℕ}
    (h₁ : BlkW Γ I Ag cl C blk₁ ss₁ (ss₂ ++ tl) (.fall es₁) i₀)
    (h₂ : BlkW Γ I Ag cl C blk₂ ss₂ tl o₂ (i₀ + (calls es₁).length)) :
    BlkW Γ I Ag cl C (blk₁ ++ blk₂) (ss₁ ++ ss₂) tl (o₂.pre es₁) i₀ := by
  cases o₂ with
  | stuck =>
    exact ⟨fun _ => [], fun _ => rfl, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk => hk.elim⟩
  | fall es₂ =>
    refine BlkW.append_core (by simp [outEs, Out.pre, calls_append']) (fun next kret ks hk => ?_)
      h₁ h₂
    intro cs' hcs'
    have := hk cs' hcs'
    rwa [calls_append', List.length_append, ← List.drop_drop] at this
  | ret es₂ vs =>
    exact BlkW.append_core (by simp [outEs, Out.pre, calls_append']) (fun _ _ _ hk => hk) h₁ h₂

/-- **A straight-line instruction's relation gives its words** on the memories `Ag`, for every
frame word and valuation `Same` as the instance's (from `FrameHW`'s `opW_hw`/`opW_jw` and
`Inst.Ok`: a final instruction names no temporary's cell but a temporary's `DEREF`). -/
def OpOK (Γ : Site κ₀) (I : Inst)
    (Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop) (cl : List Call) : Prop :=
  ∀ (Ψ : ℕ → E) (σ' : Val), I.Same σ' → ∀ (kh : ℕ → E × E) (h : List LHint) (o : LOp) (pos : ℕ)
    (cs : List Stmt) (ks : List (ℕ × ℕ)) (next : List Stmt → List (ℕ × ℕ) → Prop)
    (kj : List (ℕ × ℕ) → E → E → Prop) (kret khalt : Prop),
    o ∈ I.ops → OpW I Ψ o → next cs ks →
    wS Γ I.fp σ' I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) cl (.op h o) cs pos ks next kj kret khalt

/-- Straight-line instructions whose relations the constraint gives hand the cursor on. -/
theorem wLc_ops (hok : OpOK Γ I Ag cl) {C : (ℕ → E) → Prop} {Ψ : ℕ → E} (hΨ : C Ψ) {σ' : Val}
    (hσ : I.Same σ') (kh : ℕ → E × E) :
    ∀ (blk : List PStmt), (∀ s ∈ blk, ∃ h o, s = PStmt.op h o ∧ ∀ Ψ, C Ψ → OpW I Ψ o) →
    ∀ (pos : ℕ), (∀ o' ∈ blockOps blk pos, o' ∈ I.ops) → ∀ (cs : List Stmt) (ks : List (ℕ × ℕ))
    (next : List Stmt → List (ℕ × ℕ) → Prop) (kj : List (ℕ × ℕ) → E → E → Prop)
    (kret khalt : Prop), next cs ks →
    wLc Γ I.fp σ' I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) cl blk cs pos ks next kj kret khalt
  | [], _, _, _, _, _, _, _, _, _, hn => by rw [wLc]; exact hn
  | s :: ss, hs, pos, hops, cs, ks, next, kj, kret, khalt, hn => by
    obtain ⟨h, o, rfl, hw⟩ := hs s (List.mem_cons_self ..)
    rw [wLc]
    refine hok Ψ σ' hσ kh h o pos cs ks _ _ kret khalt
      (hops o (by simp [blockOps, stmtOps])) (hw Ψ hΨ) ?_
    exact wLc_ops hok hΨ hσ kh ss (fun s' hs' => hs s' (List.mem_cons_of_mem _ hs'))
      (pos + stmtSize (.op h o)) (fun o' ho' => hops o' (by
        simp only [blockOps, List.mem_append]; exact Or.inr ho')) cs ks next kj kret khalt hn

theorem op_mem_blockOps : ∀ (blk : List PStmt) (pos : ℕ) {h : List LHint} {o : LOp},
    PStmt.op h o ∈ blk → o ∈ blockOps blk pos
  | [], _, _, _, hm => nomatch hm
  | s :: ss, pos, h, o, hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · simp [blockOps, stmtOps]
    · simp only [blockOps, List.mem_append]
      exact Or.inr (op_mem_blockOps ss _ hm)

/-- **Straight-line instructions on the path are words of a block** whose core statements make
no call and stand for nothing the cursor sees (atoms). -/
theorem FAt.toBlk (hok : OpOK Γ I Ag cl) {ctx : Ctx} {C : (ℕ → E) → Prop} {st : St} {α : Type}
    {m : P α} {R : α → ((ℕ → E) → Prop) → St → Prop} {ss tl : List Stmt} {es : List Ev}
    {i₀ : ℕ} (hss : ctrlSplit (ss ++ tl) = ctrlSplit tl) (hc : calls es = [])
    (h : FAt ctx I C st m R) :
    FBAt ctx I C st m fun a C' st' => COk I C' st'.next st'.scope st'.locs ∧ R a C' st' ∧
      ∃ blk, st'.out.toList = st.out.toList ++ blk ∧
        (Fits I st' → BlkW Γ I Ag cl C' blk ss tl (.fall es) i₀) := by
  intro hc0
  refine wp_mono (h hc0) fun a st' ⟨C', hcok, hs, hn, hl, ⟨ops, ho, hops⟩, hr⟩ =>
    ⟨C', hcok.sat, hcok.blind, hs, hn, hl, hcok, hr, ops, ho, fun hfit => ⟨fun _ => [],
      fun _ => by simp [outEs, hc],
      fun Ψ hΨ σ' hσ kh cs pos ks next kj kret khalt hbo hcs _ hk => ?_⟩⟩
  refine wLc_ops hok hΨ hσ kh ops (hops hfit fun _ o hm => hbo o (op_mem_blockOps ops pos hm))
    pos hbo cs ks next kj kret khalt ?_
  have := hk cs (hcs.trans hss)
  simpa [hc] using this

end Compose

/-! ## Control placement on and off the path -/

section FB

variable {ctx : Ctx} {I : Inst} {C : (ℕ → E) → Prop} {st : St}

/-- An on-path action's spec, its final constraint's properties kept in the result. -/
theorem FBAt.ofFAt {α : Type} {m : P α} {R : α → ((ℕ → E) → Prop) → St → Prop}
    (h : FAt ctx I C st m R) :
    FBAt ctx I C st m fun a C' st' => COk I C' st'.next st'.scope st'.locs ∧ R a C' st' :=
  fun hc => wp_mono (h hc) fun _ _ ⟨C', h1, h2, h3, h4, _, h6⟩ =>
    ⟨C', h1.sat, h1.blind, h2, h3, h4, h1, h6⟩

theorem FBAt.pure {α : Type} {a : α} {R : α → ((ℕ → E) → Prop) → St → Prop} (h : R a C st) :
    FBAt ctx I C st (Pure.pure a) R :=
  fun hc => wp_pure.mpr ⟨C, hc.sat, hc.blind, Stronger.refl C, le_rfl, LocsLe.refl _, h⟩

theorem FBAt.mono {α : Type} {m : P α} {R R' : α → ((ℕ → E) → Prop) → St → Prop}
    (h : FBAt ctx I C st m R) (hr : ∀ a C' st', Stronger C' C → st.next ≤ st'.next →
      LocsLe st.locs st'.locs → R a C' st' → R' a C' st') : FBAt ctx I C st m R' := fun hc =>
  wp_mono (h hc) fun a st' ⟨C', h0, h1, h2, h3, h4, h6⟩ =>
    ⟨C', h0, h1, h2, h3, h4, hr a C' st' h2 h3 h4 h6⟩

/-- Sequencing: the first action's result keeps the constraint's properties for the second. -/
theorem FBAt.bind {α β : Type} {m : P α} {f : α → P β} {R₁ : α → ((ℕ → E) → Prop) → St → Prop}
    {R₂ : β → ((ℕ → E) → Prop) → St → Prop} (hm : FBAt ctx I C st m R₁)
    (hR : ∀ a C' st', R₁ a C' st' → COk I C' st'.next st'.scope st'.locs)
    (hf : ∀ a st' C', Stronger C' C → st.next ≤ st'.next → LocsLe st.locs st'.locs →
      R₁ a C' st' → FBAt ctx I C' st' (f a) R₂) :
    FBAt ctx I C st (m >>= f) R₂ := by
  intro hc
  refine wp_bind.mpr fun a st₁ he b st₂ he' => ?_
  obtain ⟨C₁, -, -, hs₁, hn₁, hl₁, hr₁⟩ := hm hc a st₁ he
  obtain ⟨C₂, h0, hb, hs₂, hn₂, hl₂, hr₂⟩ :=
    hf a st₁ C₁ hs₁ hn₁ hl₁ hr₁ (hR a C₁ st₁ hr₁) b st₂ he'
  exact ⟨C₂, h0, hb, hs₁.trans hs₂, le_trans hn₁ hn₂, hl₁.trans hl₂, hr₂⟩

theorem FBAt.get_bind {β : Type} {f : St → P β} {R : β → ((ℕ → E) → Prop) → St → Prop}
    (h : FBAt ctx I C st (f st) R) : FBAt ctx I C st (get >>= f) R :=
  fun hc => wp_bind.mpr (wp_get.mpr (h hc))

theorem FBAt.read_bind {β : Type} {f : Ctx → P β} {R : β → ((ℕ → E) → Prop) → St → Prop}
    (h : FBAt ctx I C st (f ctx) R) : FBAt ctx I C st (read >>= f) R :=
  fun hc => wp_bind.mpr (wp_read.mpr (h hc))

/-- **Off the path** (a branch or an arm not taken): an action that gives the scope back, moves
the next free cell up and grows the places keeps the constraint as it is, pools included. -/
theorem FBAt.offPath {α : Type} {m : P α} {Q : α → St → Prop}
    (h : wpP m ctx st fun a st' => st'.scope = st.scope ∧ st.next ≤ st'.next ∧
      LocsLe st.locs st'.locs ∧ Q a st') :
    FBAt ctx I C st m fun a C' st' => C' = C ∧ COk I C st'.next st'.scope st'.locs ∧ Q a st' :=
  fun hc => wp_mono h fun a st' ⟨hs, hn, hl, hq⟩ =>
    ⟨C, hc.sat, hc.blind.mono hn, Stronger.refl C, hn, hl, rfl,
      ⟨hc.sat, hc.blind.mono hn, fun Ψ hΨ => by rw [hs]; exact (hc.pools Ψ hΨ).grow hl,
        by rw [hs]; exact hc.cells.mono hn⟩, hq⟩

/-- **After the path returned**: whatever the rest places, the constraint stays as it is
(satisfiable, blind from the next free cell on). -/
theorem FBAt.dead {α : Type} {m : P α} {Q : α → St → Prop}
    (h : wpP m ctx st fun a st' => st.next ≤ st'.next ∧ LocsLe st.locs st'.locs ∧ Q a st') :
    FBAt ctx I C st m fun a C' st' => C' = C ∧ Q a st' :=
  fun hc => wp_mono h fun _ _ ⟨hn, hl, hq⟩ =>
    ⟨C, hc.sat, hc.blind.mono hn, Stronger.refl C, hn, hl, rfl, hq⟩

end FB

/-! ## A block, statement by statement -/

/-- **A statement's lemma's statement**: `BlockW` for `placeStmt s rest; endStmt` against the
scope walk's `scopeStmt` and the path's `walk1`. -/
def StmtW {κ₀ : ℕ} (Γ : Site κ₀) (Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) →
    MemoryImage κ → Prop) (cl : List Call) (ctx : Ctx) (I : Inst) (s : Stmt)
    (rest tl : List Stmt) : Prop :=
  ∀ (C : (ℕ → E) → Prop) (st : St) (sc sc' : SSt) (i₀ : ℕ) (o : Out),
    scopeStmt ctx.retCells s sc = .ok sc' → walk1 I.σ s = o → o ≠ .stuck →
    (∀ e ∈ outEs o, e ∈ I.es) → (∀ j < (calls (outEs o)).length, cl[i₀ + j]? = (calls (outEs o))[j]?) →
    WInv ctx I C st sc →
    FBAt ctx I C st (placeStmt s rest >>= fun _ => endStmt) fun _ C' st' =>
      (∀ es, o = .fall es → WInv ctx I C' st' sc') ∧
      ∃ blk, st'.out.toList = st.out.toList ++ blk ∧
        (Fits I st' → BlkW Γ I Ag cl C' blk [s] (rest ++ tl) o i₀)

section BlockCons

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}
  {ctx : Ctx} {I : Inst}

theorem BlockW.nil (tl : List Stmt) : BlockW Γ Ag cl ctx I (placeBlock []) [] tl := by
  intro C st s s' i₀ o hsc hw _ _ _ hinv
  rw [scopeBlock] at hsc
  cases hsc
  rw [walk] at hw
  subst hw
  rw [placeBlock]
  refine FBAt.pure ⟨fun _ _ => hinv, [], by simp, fun _ => ⟨fun _ => [], fun _ => rfl,
    fun Ψ _ σ' _ kh cs pos ks next kj kret khalt _ hcs _ hk => ?_⟩⟩
  rw [wLc]
  have := hk cs (by simpa using hcs)
  simpa [outEs, calls] using this

end BlockCons

end
end LeanVM.Guest.Backend.Complete
