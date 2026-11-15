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
keeps its properties, both walks are at one event, the values in scope are known, while the path
has made no return area the constraint does not mention the return cells, the values the rest of
the trace makes are made once, neither placed yet nor in scope, no `match` chains in, the
multiplied pool cells are no temporary's, and no value waits to be placed by the next statement. -/
structure WInv (ctx : Ctx) (I : Inst) (C : (ℕ → E) → Prop) (st : St) (s : SSt) : Prop where
  cok : COk I C st.next st.scope st.locs
  rest : s.rest = st.rest
  vw : VW I C st (fun v => s.live.contains v = true)
  two : 2 ≤ st.next
  abi : 2 + ctx.argCells + ctx.retCells ≤ st.next
  fuel : st.rest.length ≤ ctx.fuel
  ret : s.retDone = false → ∀ Ψ k w, k < ctx.retCells → C Ψ →
    C (Function.update Ψ (2 + ctx.argCells + k) w)
  nodup : (allocsOf st.rest).Nodup
  fresh : ∀ v ∈ allocsOf st.rest, st.locs[v]? = none ∧ s.live.contains v = false
  chain : st.chainIn = none
  pnt : PoolNT I st.scope
  lazy : st.lazy = none

/-- The final placement's instructions at `p₀`: `ops` from the absolute position `p₀` on. -/
def OpsIn (I : Inst) (p₀ : ℕ) (ops : List LOp) : Prop :=
  ∀ i (h : i < ops.length), I.ops[p₀ + i]? = some ops[i]

/-- The instructions the current block has placed so far, its first at the absolute position
`p₀`, are the final placement's there. -/
def OpsAt (I : Inst) (p₀ : ℕ) (st : St) : Prop := OpsIn I p₀ (blockOps st.out.toList p₀)

theorem OpsIn.mem {I : Inst} {p₀ : ℕ} {ops : List LOp} (h : OpsIn I p₀ ops) :
    ∀ o ∈ ops, o ∈ I.ops := fun o ho => by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
  exact List.mem_of_getElem? (h i hi)

theorem OpsIn.left {I : Inst} {p₀ : ℕ} {a b : List LOp} (h : OpsIn I p₀ (a ++ b)) :
    OpsIn I p₀ a := fun i hi => by
  have := h i (by rw [List.length_append]; omega)
  rwa [List.getElem_append_left hi] at this

theorem OpsIn.right {I : Inst} {p₀ : ℕ} {a b : List LOp} (h : OpsIn I p₀ (a ++ b)) :
    OpsIn I (p₀ + a.length) b := fun i hi => by
  have := h (a.length + i) (by rw [List.length_append]; omega)
  rw [List.getElem_append_right (by omega)] at this
  simpa [Nat.add_assoc] using this

/-- The values a path returns. -/
def retVals : Out → List V
  | .ret _ vs => vs
  | _ => []

/-- **The values the path through the core statements `ss` reads**, temporaries aside (the
frame words get theirs patched in): its events' values, its returned values, its selectors. -/
noncomputable def pathVals (σ : Val) (ss : List Stmt) (o : Out) : List V :=
  (outEs o).flatMap Memory.Ev.uses ++ retVals o ++ pathSels σ ss

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
def KsAt (cl : List Call) (kf : List ℕ) (kh : ℕ → E × E) (i₀ : ℕ) (bc : List Call)
    (hs : List (E × E)) (ks : List (ℕ × ℕ)) : Prop :=
  hs.length = bc.length ∧ ∀ j < bc.length,
    (∃ kfp, ks[j]? = some (i₀ + j, kfp) ∧ kf[i₀ + j]? = some kfp) ∧
    cl[i₀ + j]? = bc[j]? ∧ kh (i₀ + j) = hs.getD j (0, 0)

/-- **The callee headers of a block's calls** `bc`: in `K` once this frame's header is (a
function's), and this frame's header for a call of the function itself. -/
def HsOk (I : Inst) (bx : Ctx) (bc : List Call) (hs : List (E × E)) : Prop :=
  ((bx.isMain = false → IsInK I.hdr.1 ∧ IsInK I.hdr.2) → ∀ h ∈ hs, IsInK h.1 ∧ IsInK h.2) ∧
    ∀ j (hj : j < hs.length) c, bc[j]? = some c → c.f = bx.name → hs[j] = I.hdr

theorem HsOk.nil (I : Inst) (bx : Ctx) (bc : List Call) : HsOk I bx bc [] :=
  ⟨fun _ _ h => (nomatch h), fun _ hj => absurd hj (Nat.not_lt_zero _)⟩

theorem HsOk.append {I : Inst} {bx : Ctx} {bc₁ bc₂ : List Call} {hs₁ hs₂ : List (E × E)}
    (h₁ : HsOk I bx bc₁ hs₁) (h₂ : HsOk I bx bc₂ hs₂) (hl : hs₁.length = bc₁.length) :
    HsOk I bx (bc₁ ++ bc₂) (hs₁ ++ hs₂) := by
  refine ⟨fun hk h hm => (List.mem_append.mp hm).elim (h₁.1 hk h) (h₂.1 hk h),
    fun j hj c hc hf => ?_⟩
  by_cases hj₁ : j < hs₁.length
  · rw [List.getElem_append_left hj₁]
    exact h₁.2 j hj₁ c (by rwa [List.getElem?_append_left (by omega)] at hc) hf
  · rw [List.length_append] at hj
    rw [List.getElem_append_right (by omega)]
    exact h₂.2 (j - hs₁.length) (by omega) c
      (by rwa [List.getElem?_append_right (by omega), ← hl] at hc) hf

/-- What the words of a path take of the frame: a function's header words in `K`, and a
registered loop helper's last callee frame right past its own. -/
def PremW (I : Inst) (bx : Ctx) : Prop :=
  (bx.isMain = false → IsInK I.hdr.1 ∧ IsInK I.hdr.2) ∧
    (I.loopH = true → ∀ kfp, I.kf.getLast? = some kfp → kfp = I.fp + I.size)

/-- **The words of a placed block on the path**: the block `blk` placed at the absolute position
`pos` for the core statements `ss` (followed by `tl`) whose path under the instance's valuation is
`o`, its calls from index `i₀`; for every frame word the constraint allows and every valuation
`Same` as the instance's, its statements' words (`wLc`), the memories being `Ag σ' Ψ kh`, with
callee headers `hs`. -/
def BlkW {κ₀ : ℕ} (Γ : Site κ₀) (I : Inst) (bx : Ctx)
    (Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop) (cl : List Call)
    (C : (ℕ → E) → Prop) (blk : List PStmt) (ss tl : List Stmt) (o : Out) (i₀ pos : ℕ) : Prop :=
  ∃ hs : List (E × E), hs.length = (calls (outEs o)).length ∧ HsOk I bx (calls (outEs o)) hs ∧
  (PremW I bx → ∀ Ψ, C Ψ → ∀ σ', I.Same σ' → ∀ (kh : ℕ → E × E) (cs : List Stmt)
    (ks : List (ℕ × ℕ)) (next : List Stmt → List (ℕ × ℕ) → Prop)
    (kj : List (ℕ × ℕ) → E → E → Prop) (kret khalt : Prop),
    (∀ o' ∈ blockOps blk pos, o' ∈ I.ops) →
    ctrlSplit cs = ctrlSplit (ss ++ tl) → KsAt cl I.kf kh i₀ (calls (outEs o)) hs ks →
    OutK o tl next (if bx.isMain then khalt else kret) ks →
    wLc Γ I.fp σ' I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) cl blk cs pos ks next kj kret khalt)

/-- `FAt` for actions that place control statements: the constraint's properties kept, the next
free cell and the places growing, the result under the new constraint and state. -/
def FBAt {α : Type} (ctx : Ctx) (I : Inst) (C : (ℕ → E) → Prop) (st : St) (m : P α)
    (R : α → ((ℕ → E) → Prop) → St → Prop) : Prop :=
  COk I C st.next st.scope st.locs →
  wpP m ctx st fun a st' => ∃ C', (∃ Ψ, C' Ψ) ∧ Blind C' st'.next ∧ Stronger C' C ∧
    st.next ≤ st'.next ∧ LocsLe st.locs st'.locs ∧ R a C' st'

/-- **The words of the values a path read**: no value of `vs` is made by an event of the rest of
the trace (so no later placement places it), and a value of `vs` but a temporary, once placed,
is in the frame below the next free cell and its place holds its word under the constraint. -/
def RW (I : Inst) (C : (ℕ → E) → Prop) (st : St) (vs : List V) : Prop :=
  ∀ v ∈ vs, v ∉ allocsOf st.rest ∧ (v ∉ I.tmps → ∀ l, st.locs[v]? = some l →
    2 ≤ locBase l ∧ locBase l < st.next ∧ ∀ Ψ, C Ψ → locW Ψ l = I.σ v)

/-- **The shared jump tables the walk has made hold on every memory `Ag` admits**: slot
`first + j` of the table of the callees `fs` holds the entry of `fs[j]` (CplFrameCalls' finding
on dispatch: the walk's tables are the final layout's). -/
def TabsW {κ₀ : ℕ} (Γ : Site κ₀) (Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) →
    MemoryImage κ → Prop) (st : St) : Prop :=
  ∀ fs first, (fs, first) ∈ st.tables.shared → ∀ σ' Ψ kh κ (L : MemoryImage κ), Ag σ' Ψ kh κ L →
    ∀ j (hj : j < fs.length), L.read (addressOfIndex (Γ.l.tablesBase + (first + j))) =
      some (ofK (addressOfIndex (Γ.ent fs[j])))

/-- **A state the final placement extends**: its cells and places final, the current block's
instructions so far (from the absolute position `p₀`) final, its shared tables in the layout. -/
def FinAt {κ₀ : ℕ} (Γ : Site κ₀) (I : Inst) (Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) →
    MemoryImage κ → Prop) (p₀ : ℕ) (st : St) : Prop :=
  Fits I st ∧ OpsAt I p₀ st ∧ TabsW Γ Ag st

/-- **What a block's placement on the path gives**, from `st` to `st'` for the core statements
`ss` (followed by `tl`) with path `o`, calls from `i₀`, the current block's placed statements
starting at the absolute position `p₀`: once the final placement extends `st'` (`FinAt`), the
invariant if the path falls through, the statements laid with their words (`BlkW`) and the words
of the values the path read (`RW`). -/
def BlockOut {κ₀ : ℕ} (Γ : Site κ₀) (Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) →
    MemoryImage κ → Prop) (cl : List Call) (ctx : Ctx) (I : Inst) (st : St) (s' : SSt)
    (ss tl : List Stmt) (o : Out) (i₀ p₀ : ℕ) (C' : (ℕ → E) → Prop) (st' : St) : Prop :=
  (∀ es, o = .fall es → FinAt Γ I Ag p₀ st' → WInv ctx I C' st' s') ∧
    st'.chainIn = none ∧ (FinAt Γ I Ag p₀ st' → ∃ blk,
      st'.out.toList = st.out.toList ++ blk ∧
      BlkW Γ I ctx Ag cl C' blk ss tl o i₀ (p₀ + blockSize st.out.toList) ∧
      RW I C' st' (pathVals I.σ ss o))

/-- **The block lemma's statement**: placing the core block `ss` (followed by `tl`) on the path
of the instance, in lockstep with the scope walk from `s` to `s'`, gives `BlockOut` (after a
return the rest is off the path: only the constraint's satisfiability and blindness are kept). -/
def BlockW {κ₀ : ℕ} (Γ : Site κ₀) (Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) →
    MemoryImage κ → Prop) (cl : List Call) (ctx : Ctx) (I : Inst) (m : P Unit)
    (ss tl : List Stmt) : Prop :=
  ∀ (C : (ℕ → E) → Prop) (st : St) (s s' : SSt) (i₀ p₀ : ℕ) (o : Out),
    scopeBlock ctx.retCells ss s = .ok s' → walk I.σ ss = o → o ≠ .stuck →
    (∀ e ∈ outEs o, e ∈ I.es) → (∀ j < (calls (outEs o)).length, cl[i₀ + j]? = (calls (outEs o))[j]?) →
    WInv ctx I C st s →
    FBAt ctx I C st m fun _ C' st' => BlockOut Γ Ag cl ctx I st s' ss tl o i₀ p₀ C' st'

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
  {bx : Ctx}

theorem BlkW.mono {C C' : (ℕ → E) → Prop} {blk : List PStmt} {ss tl : List Stmt} {o : Out}
    {i₀ pos : ℕ} (h : BlkW Γ I bx Ag cl C blk ss tl o i₀ pos) (hs : Stronger C' C) :
    BlkW Γ I bx Ag cl C' blk ss tl o i₀ pos := by
  obtain ⟨hs', hl, hh, h⟩ := h
  exact ⟨hs', hl, hh, fun hp Ψ hΨ => h hp Ψ (hs Ψ hΨ)⟩

/-- A block whose path returns, then statements off the path. -/
theorem BlkW.append_ret {C : (ℕ → E) → Prop} {blk₁ blk₂ : List PStmt} {ss₁ ss₂ tl : List Stmt}
    {es : List Ev} {vs : List V} {i₀ pos : ℕ}
    (h₁ : BlkW Γ I bx Ag cl C blk₁ ss₁ (ss₂ ++ tl) (.ret es vs) i₀ pos) :
    BlkW Γ I bx Ag cl C (blk₁ ++ blk₂) (ss₁ ++ ss₂) tl (.ret es vs) i₀ pos := by
  obtain ⟨hs, hl, hh, h⟩ := h₁
  refine ⟨hs, hl, hh, fun hp Ψ hΨ σ' hσ kh cs ks next kj kret khalt hops hcs hks hk => ?_⟩
  have hops₁ : ∀ o' ∈ blockOps blk₁ pos, o' ∈ I.ops := fun o' ho =>
    hops o' (by rw [bops_append]; exact List.mem_append_left _ ho)
  have hcs₁ : ctrlSplit cs = ctrlSplit (ss₁ ++ (ss₂ ++ tl)) := by rwa [← List.append_assoc]
  cases blk₂ with
  | nil =>
    rw [List.append_nil]
    exact h hp Ψ hΨ σ' hσ kh cs ks next kj kret khalt hops₁ hcs₁ hks hk
  | cons b bs =>
    rw [wLc_append _ _ _ _ _ _ _ blk₁ (b :: bs) (List.cons_ne_nil _ _)]
    exact h hp Ψ hΨ σ' hσ kh cs ks _ _ kret khalt hops₁ hcs₁ hks hk

theorem calls_append' (a b : List Ev) : calls (a ++ b) = calls a ++ calls b := by
  simp [calls, List.filterMap_append]

theorem BlkW.append_core {C : (ℕ → E) → Prop} {blk₁ blk₂ : List PStmt} {ss₁ ss₂ tl : List Stmt}
    {es₁ : List Ev} {o o₂ : Out} {i₀ pos : ℕ}
    (hc : calls (outEs o) = calls es₁ ++ calls (outEs o₂))
    (hk : ∀ next kret ks, OutK o tl next kret ks →
      OutK o₂ tl next kret (ks.drop (calls es₁).length))
    (h₁ : BlkW Γ I bx Ag cl C blk₁ ss₁ (ss₂ ++ tl) (.fall es₁) i₀ pos)
    (h₂ : BlkW Γ I bx Ag cl C blk₂ ss₂ tl o₂ (i₀ + (calls es₁).length) (pos + blockSize blk₁)) :
    BlkW Γ I bx Ag cl C (blk₁ ++ blk₂) (ss₁ ++ ss₂) tl o i₀ pos := by
  obtain ⟨hs₁, hl₁, hh₁, h₁⟩ := h₁
  obtain ⟨hs₂, hl₂, hh₂, h₂⟩ := h₂
  simp only [outEs] at hl₁ hh₁
  refine ⟨hs₁ ++ hs₂, by rw [List.length_append, hl₁, hl₂, hc, List.length_append],
    by rw [hc]; exact hh₁.append hh₂ hl₁, ?_⟩
  intro hp Ψ hΨ σ' hσ kh cs ks next kj kret khalt hops hcs hks hk'
  obtain ⟨-, hks⟩ := hks
  rw [hc] at hks
  have hops₁ : ∀ o' ∈ blockOps blk₁ pos, o' ∈ I.ops := fun o' ho =>
    hops o' (by rw [bops_append]; exact List.mem_append_left _ ho)
  have hops₂ : ∀ o' ∈ blockOps blk₂ (pos + blockSize blk₁), o' ∈ I.ops := fun o' ho =>
    hops o' (by rw [bops_append]; exact List.mem_append_right _ ho)
  have hcs₁ : ctrlSplit cs = ctrlSplit (ss₁ ++ (ss₂ ++ tl)) := by rwa [← List.append_assoc]
  have hks₁ : KsAt cl I.kf kh i₀ (calls (outEs (.fall es₁))) hs₁ ks := by
    refine ⟨hl₁, fun j hj => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hks j (by rw [List.length_append]; simp only [outEs] at hj; omega)
    simp only [outEs] at hj ⊢
    refine ⟨h1, by rw [h2, List.getElem?_append_left hj], ?_⟩
    rw [h3, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [hl₁]; exact hj)]
  have hnext : ∀ cs', ctrlSplit cs' = ctrlSplit (ss₂ ++ tl) →
      wLc Γ I.fp σ' I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) cl blk₂ cs' (pos + blockSize blk₁)
        (ks.drop (calls es₁).length) next kj kret khalt := by
    intro cs' hcs'
    refine h₂ hp Ψ hΨ σ' hσ kh cs' _ next kj kret khalt hops₂ hcs' ⟨hl₂, fun j hj => ?_⟩
      (hk next _ ks hk')
    obtain ⟨⟨kfp, h1, h1'⟩, h2, h3⟩ := hks ((calls es₁).length + j)
      (by rw [List.length_append]; omega)
    refine ⟨⟨kfp, by rw [List.getElem?_drop, h1, Nat.add_assoc], by rw [Nat.add_assoc]; exact h1'⟩,
      ?_, ?_⟩
    · rw [Nat.add_assoc, h2, List.getElem?_append_right (by omega)]
      simp
    · rw [Nat.add_assoc, h3, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega), hl₁]
      simp
  cases blk₂ with
  | nil =>
    rw [List.append_nil]
    refine h₁ hp Ψ hΨ σ' hσ kh cs ks next kj kret khalt hops₁ hcs₁ hks₁ fun cs' hcs' => ?_
    have := hnext cs' hcs'
    rwa [wLc] at this
  | cons b bs =>
    rw [wLc_append _ _ _ _ _ _ _ blk₁ (b :: bs) (List.cons_ne_nil _ _)]
    exact h₁ hp Ψ hΨ σ' hσ kh cs ks _ _ kret khalt hops₁ hcs₁ hks₁ hnext

/-- A block whose path falls through, then a block on the path. -/
theorem BlkW.append_fall {C : (ℕ → E) → Prop} {blk₁ blk₂ : List PStmt} {ss₁ ss₂ tl : List Stmt}
    {es₁ : List Ev} {o₂ : Out} {i₀ pos : ℕ}
    (h₁ : BlkW Γ I bx Ag cl C blk₁ ss₁ (ss₂ ++ tl) (.fall es₁) i₀ pos)
    (h₂ : BlkW Γ I bx Ag cl C blk₂ ss₂ tl o₂ (i₀ + (calls es₁).length) (pos + blockSize blk₁)) :
    BlkW Γ I bx Ag cl C (blk₁ ++ blk₂) (ss₁ ++ ss₂) tl (o₂.pre es₁) i₀ pos := by
  cases o₂ with
  | stuck =>
    exact ⟨[], by simp [outEs, Out.pre, calls], HsOk.nil _ _ _,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk => hk.elim⟩
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
no call and stand for nothing the cursor sees (atoms), at every position. -/
theorem FAt.toBlk (hok : OpOK Γ I Ag cl) {ctx : Ctx} {C : (ℕ → E) → Prop} {st : St} {α : Type}
    {m : P α} {R : α → ((ℕ → E) → Prop) → St → Prop} {ss tl : List Stmt} {es : List Ev}
    {i₀ : ℕ} (hss : ctrlSplit (ss ++ tl) = ctrlSplit tl) (hc : calls es = [])
    (h : FAt ctx I C st m R) :
    FBAt ctx I C st m fun a C' st' => COk I C' st'.next st'.scope st'.locs ∧ R a C' st' ∧
      ∃ blk, st'.out.toList = st.out.toList ++ blk ∧
        (Fits I st' → OutOps I st' → ∀ pos,
          BlkW Γ I bx Ag cl C' blk ss tl (.fall es) i₀ pos) := by
  intro hc0
  refine wp_mono (h hc0) fun a st' ⟨C', hcok, hs, hn, hl, ⟨ops, ho, hops⟩, hr⟩ =>
    ⟨C', hcok.sat, hcok.blind, hs, hn, hl, hcok, hr, ops, ho, fun hfit hout pos => ⟨[],
      by simp [outEs, hc], HsOk.nil _ _ _,
      fun _ Ψ hΨ σ' hσ kh cs ks next kj kret khalt hbo hcs _ hk => ?_⟩⟩
  refine wLc_ops hok hΨ hσ kh ops (hops hfit hout)
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

/-- An action's spec on the path with a fact of all its successes. -/
theorem FBAt.and_wp {α : Type} {m : P α} {R : α → ((ℕ → E) → Prop) → St → Prop}
    {Q : α → St → Prop} (h : FBAt ctx I C st m R) (hq : wpP m ctx st Q) :
    FBAt ctx I C st m fun a C' st' => R a C' st' ∧ Q a st' :=
  fun hc a st' he =>
    let ⟨C', h1, h2, h3, h4, h5, h6⟩ := h hc a st' he
    ⟨C', h1, h2, h3, h4, h5, h6, hq a st' he⟩

end FB

/-! ## A block, statement by statement -/

/-- **A statement's lemma's statement**: `BlockW` for `placeStmt s rest; endStmt` against the
scope walk's `scopeStmt` and the path's `walk1`, the rest of the block scoped and, if the path
falls through `s`, the atoms it starts with on the path. -/
def StmtW {κ₀ : ℕ} (Γ : Site κ₀) (Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) →
    MemoryImage κ → Prop) (cl : List Call) (ctx : Ctx) (I : Inst) (s : Stmt)
    (rest tl : List Stmt) : Prop :=
  ∀ (C : (ℕ → E) → Prop) (st : St) (sc sc' : SSt) (i₀ p₀ : ℕ) (o : Out),
    scopeStmt ctx.retCells s sc = .ok sc' → (∃ sc'', scopeBlock ctx.retCells rest sc' = .ok sc'') →
    walk1 I.σ s = o → o ≠ .stuck →
    (∀ e ∈ outEs o, e ∈ I.es) → (∀ j < (calls (outEs o)).length, cl[i₀ + j]? = (calls (outEs o))[j]?) →
    (∀ es, o = .fall es → ∀ (k : ℕ) (a : Atom), (∀ j < k, ∃ b, rest[j]? = some (Stmt.atom b)) →
      rest[k]? = some (Stmt.atom a) → Memory.Ev.atom a ∈ I.es) →
    WInv ctx I C st sc →
    FBAt ctx I C st (placeStmt s rest >>= fun _ => endStmt) fun _ C' st' =>
      BlockOut Γ Ag cl ctx I st sc' [s] (rest ++ tl) o i₀ p₀ C' st'

section RWs

variable {I : Inst}

/-- The words of the values read stay through a placement that places no value but those the
rest of the trace makes. -/
theorem RW.grow {C C' : (ℕ → E) → Prop} {st st' : St} {vs : List V} (h : RW I C st vs)
    (hs : Stronger C' C) (hn : st.next ≤ st'.next) (hl : LocsLe st.locs st'.locs)
    (hnew : ∀ v ∈ vs, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf st.rest)
    (hr : ∀ v ∈ allocsOf st'.rest, v ∈ allocsOf st.rest) : RW I C' st' vs := fun v hv => by
  obtain ⟨hf, hw⟩ := h v hv
  refine ⟨fun h' => hf (hr v h'), fun ht l hl' => ?_⟩
  rcases hnew v hv (by rw [hl']; simp) with h0 | h0
  · obtain ⟨l₀, hl₀⟩ := Option.ne_none_iff_exists'.mp h0
    have hl₁ := hl v l₀ hl₀
    rw [hl'] at hl₁
    cases hl₁
    obtain ⟨b1, b2, b3⟩ := hw ht l hl₀
    exact ⟨b1, lt_of_lt_of_le b2 hn, fun Ψ hΨ => b3 Ψ (hs Ψ hΨ)⟩
  · exact absurd h0 hf

theorem RW.append {C : (ℕ → E) → Prop} {st : St} {a b : List V} (h₁ : RW I C st a)
    (h₂ : RW I C st b) : RW I C st (a ++ b) := fun v hv =>
  (List.mem_append.mp hv).elim (h₁ v) (h₂ v)

theorem RW.anti {C : (ℕ → E) → Prop} {st : St} {a b : List V} (h : RW I C st b)
    (hs : ∀ v ∈ a, v ∈ b) : RW I C st a := fun v hv => h v (hs v hv)

theorem OpsAt.back {p₀ : ℕ} {st st' : St} {blk : List PStmt} (h : OpsAt I p₀ st')
    (ho : st'.out.toList = st.out.toList ++ blk) : OpsAt I p₀ st := by
  unfold OpsAt at h ⊢
  rw [ho, bops_append] at h
  exact h.left

theorem OpsAt.outOps {p₀ : ℕ} {st : St} (h : OpsAt I p₀ st) : OutOps I st := fun _ _ hm =>
  h.mem _ (op_mem_blockOps _ p₀ hm)

/-- A state before one the final placement extends, with fewer instructions and tables. -/
theorem FinAt.back {κ₀ : ℕ} {Γ : Site κ₀}
    {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {p₀ : ℕ} {st st' : St}
    {blk : List PStmt} (h : FinAt Γ I Ag p₀ st') (hn : st.next ≤ st'.next)
    (hl : LocsLe st.locs st'.locs) (ho : st'.out.toList = st.out.toList ++ blk)
    (ht : ∀ x ∈ st.tables.shared, x ∈ st'.tables.shared) : FinAt Γ I Ag p₀ st :=
  ⟨h.1.back hn hl, h.2.1.back ho, fun fs first hm => h.2.2 fs first (ht _ hm)⟩

/-- The values `vs` but temporaries placed, in the frame below the next free cell, their places
holding their words under the constraint. -/
def PW (I : Inst) (C : (ℕ → E) → Prop) (st : St) (vs : List V) : Prop :=
  ∀ v ∈ vs, v ∉ I.tmps → ∃ l, st.locs[v]? = some l ∧ 2 ≤ locBase l ∧ locBase l < st.next ∧
    ∀ Ψ, C Ψ → locW Ψ l = I.σ v

theorem PW.grow {C C' : (ℕ → E) → Prop} {st st' : St} {vs : List V} (h : PW I C st vs)
    (hs : Stronger C' C) (hn : st.next ≤ st'.next) (hl : LocsLe st.locs st'.locs) :
    PW I C' st' vs := fun v hv ht =>
  let ⟨l, h1, h2, h3, h4⟩ := h v hv ht
  ⟨l, hl v l h1, h2, lt_of_lt_of_le h3 hn, fun Ψ hΨ => h4 Ψ (hs Ψ hΨ)⟩

theorem PW.rw {C : (ℕ → E) → Prop} {st : St} {vs : List V} (h : PW I C st vs)
    (hf : ∀ v ∈ vs, v ∉ allocsOf st.rest) : RW I C st vs := fun v hv =>
  ⟨hf v hv, fun ht l hl => by
    obtain ⟨l', h1, h2, h3, h4⟩ := h v hv ht
    rw [hl] at h1
    cases h1
    exact ⟨h2, h3, h4⟩⟩

/-- A placement on the path keeps the words of values already placed. -/
theorem FBAt.with_pw {ctx : Ctx} {C : (ℕ → E) → Prop} {st : St} {α : Type} {m : P α}
    {R : α → ((ℕ → E) → Prop) → St → Prop} {vs : List V} (h : FBAt ctx I C st m R)
    (hp : PW I C st vs) : FBAt ctx I C st m fun a C' st' => R a C' st' ∧ PW I C' st' vs :=
  fun hc a st' he =>
    let ⟨C', h0, hb, hs, hn, hl, hr⟩ := h hc a st' he
    ⟨C', h0, hb, hs, hn, hl, hr, hp.grow hs hn hl⟩

end RWs

theorem pathVals_nil (σ : Val) : pathVals σ [] (.fall []) = [] := by
  simp [pathVals, outEs, retVals, pathSels]

theorem pathVals_ret {σ : Val} {s : Stmt} {rest : List Stmt} {es : List Ev} {vs : List V}
    (h : walk1 σ s = .ret es vs) :
    pathVals σ (s :: rest) (.ret es vs) = pathVals σ [s] (.ret es vs) := by
  simp [pathVals, pathSels, h]

theorem pathVals_fall {σ : Val} {s : Stmt} {rest : List Stmt} {es₁ : List Ev} {o₂ : Out}
    (h : walk1 σ s = .fall es₁) (hns : o₂ ≠ .stuck) :
    ∀ v ∈ pathVals σ (s :: rest) (o₂.pre es₁),
      v ∈ pathVals σ [s] (.fall es₁) ++ pathVals σ rest o₂ := by
  intro v hv
  have hs1 : pathSels σ (s :: rest) = sels1 σ s ++ pathSels σ rest := by simp [pathSels, h]
  have hs2 : pathSels σ [s] = sels1 σ s := by simp [pathSels, h]
  have hr : retVals (o₂.pre es₁) = retVals o₂ := by cases o₂ <;> simp [Out.pre, retVals]
  have he : outEs (o₂.pre es₁) = es₁ ++ outEs o₂ := by cases o₂ <;> simp_all [outEs, Out.pre]
  simp only [pathVals, hs1, hs2] at hv ⊢
  rw [he, hr] at hv
  simp only [outEs, retVals, List.flatMap_append, List.mem_append, List.append_nil] at hv ⊢
  tauto

section BlockCons

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}
  {ctx : Ctx} {I : Inst}

theorem BlockW.nil (tl : List Stmt) : BlockW Γ Ag cl ctx I (placeBlock []) [] tl := by
  intro C st s s' i₀ p₀ o hsc hw _ _ _ hinv
  rw [scopeBlock] at hsc
  cases hsc
  rw [walk] at hw
  subst hw
  rw [placeBlock]
  refine FBAt.pure ⟨fun _ _ _ => hinv, hinv.chain, fun _ => ⟨[], by simp, ⟨[],
    by simp [outEs, calls], HsOk.nil _ _ _,
    fun _ Ψ _ σ' _ kh cs ks next kj kret khalt _ hcs _ hk => ?_⟩,
    by rw [pathVals_nil]; exact fun v hv => nomatch hv⟩⟩
  rw [wLc]
  have := hk cs (by simpa using hcs)
  simpa [outEs, calls] using this

/-- Sequencing where the second action needs the invariant only if `F` holds of the state
between (the final placement extends it): otherwise it is off the path, the constraint kept. -/
theorem FBAt.bind_if {C : (ℕ → E) → Prop} {st : St} {α β : Type} {m : P α} {f : α → P β}
    {R₁ : α → ((ℕ → E) → Prop) → St → Prop} {R₂ : β → ((ℕ → E) → Prop) → St → Prop}
    {Q : St → β → St → Prop} (F : St → Prop) (hm : FBAt ctx I C st m R₁)
    (hmono : ∀ a st₁, wpP (f a) ctx st₁ fun b st₂ => st₁.next ≤ st₂.next ∧
      LocsLe st₁.locs st₂.locs ∧ Q st₁ b st₂)
    (hR : ∀ a C₁ st₁, R₁ a C₁ st₁ → F st₁ → COk I C₁ st₁.next st₁.scope st₁.locs)
    (hf : ∀ a st₁ C₁, Stronger C₁ C → st.next ≤ st₁.next → LocsLe st.locs st₁.locs →
      R₁ a C₁ st₁ → F st₁ → FBAt ctx I C₁ st₁ (f a) R₂)
    (hdead : ∀ a C₁ st₁ b st₂, R₁ a C₁ st₁ → ¬ F st₁ → st₁.next ≤ st₂.next →
      LocsLe st₁.locs st₂.locs → Q st₁ b st₂ → R₂ b C₁ st₂) :
    FBAt ctx I C st (m >>= f) R₂ := by
  intro hc
  refine wp_bind.mpr fun a st₁ he b st₂ he' => ?_
  obtain ⟨C₁, hs₁, hb₁, hst₁, hn₁, hl₁, hr₁⟩ := hm hc a st₁ he
  by_cases hF : F st₁
  · obtain ⟨C₂, h0, hb, hs₂, hn₂, hl₂, hr₂⟩ :=
      hf a st₁ C₁ hst₁ hn₁ hl₁ hr₁ hF (hR a C₁ st₁ hr₁ hF) b st₂ he'
    exact ⟨C₂, h0, hb, hst₁.trans hs₂, le_trans hn₁ hn₂, hl₁.trans hl₂, hr₂⟩
  · obtain ⟨hn₂, hl₂, hq⟩ := hmono a st₁ b st₂ he'
    exact ⟨C₁, hs₁, hb₁.mono hn₂, hst₁, le_trans hn₁ hn₂, hl₁.trans hl₂,
      hdead a C₁ st₁ b st₂ hr₁ hF hn₂ hl₂ hq⟩

/-- An action, then a rest off the path (after a return). -/
theorem FBAt.bind_dead {C : (ℕ → E) → Prop} {st : St} {α β : Type} {m : P α} {f : α → P β}
    {R₁ : α → ((ℕ → E) → Prop) → St → Prop} {Q : St → β → St → Prop}
    (hm : FBAt ctx I C st m R₁)
    (hf : ∀ a st₁, wpP (f a) ctx st₁ fun b st₂ => st₁.next ≤ st₂.next ∧
      LocsLe st₁.locs st₂.locs ∧ Q st₁ b st₂) :
    FBAt ctx I C st (m >>= f) fun b C' st₂ => ∃ a st₁, R₁ a C' st₁ ∧ Q st₁ b st₂ ∧
      st₁.next ≤ st₂.next ∧ LocsLe st₁.locs st₂.locs := by
  intro hc
  refine wp_bind.mpr fun a st₁ he b st₂ he' => ?_
  obtain ⟨C₁, hs₁, hb₁, hst₁, hn₁, hl₁, hr₁⟩ := hm hc a st₁ he
  obtain ⟨hn₂, hl₂, hq⟩ := hf a st₁ b st₂ he'
  exact ⟨C₁, hs₁, hb₁.mono hn₂, hst₁, le_trans hn₁ hn₂, hl₁.trans hl₂, a, st₁, hr₁, hq, hn₂, hl₂⟩

/-- What every placement of a block does whatever the path: the next free cell up, the places
grown, and from a state no `match` chains into, statements appended and no `match` chaining out
(`FrameLocs.lean`, from the primitives' agent). -/
def PlaceMono (ctx : Ctx) : Prop :=
  ∀ (ss : List Stmt) (st : St), wpP (placeBlock ss) ctx st fun _ st' => st.next ≤ st'.next ∧
    LocsLe st.locs st'.locs ∧ (st.chainIn = none → st'.chainIn = none ∧
      ∃ blk, st'.out.toList = st.out.toList ++ blk)

mutual
/-- The atoms of a block, through its inner blocks. -/
def atomsIn : List Stmt → List Atom
  | [] => []
  | s :: ss => atomsOf s ++ atomsIn ss

/-- The atoms of a statement, through its inner blocks. -/
def atomsOf : Stmt → List Atom
  | .atom a => [a]
  | .ite _ z n => atomsIn z ++ atomsIn n
  | .match_ _ arms => armsAtoms arms
  | _ => []

/-- The atoms of the arms of a `match`. -/
def armsAtoms : List (List Stmt) → List Atom
  | [] => []
  | a :: as => atomsIn a ++ armsAtoms as
end

/-- **A block places no value but those its trace makes or its frame addresses bind** and passes
the trace on (from the primitives' agent). -/
def PlaceNew (ctx : Ctx) : Prop :=
  ∀ (ss : List Stmt) (st : St), wpP (placeBlock ss) ctx st fun _ st' =>
    (st.lazy = none → ∀ v, st'.locs[v]? ≠ none → st.locs[v]? ≠ none ∨ v ∈ allocsOf st.rest ∨
      ∃ run, Atom.frameAddr v run ∈ atomsIn ss) ∧
    (∀ v ∈ allocsOf st'.rest, v ∈ allocsOf st.rest) ∧
    ∀ x ∈ st.tables.shared, x ∈ st'.tables.shared

/-- The values a statement's path reads are bound by no frame address of the statements after it
(a core program fact: a frame address binds a value no earlier statement reads). -/
def FaAfter (σ : Val) (s : Stmt) (rest : List Stmt) : Prop :=
  ∀ v ∈ pathVals σ [s] (walk1 σ s), ∀ run, Atom.frameAddr v run ∉ atomsIn rest

theorem placeNew_vs {σ : Val} {s : Stmt} {rest : List Stmt} {st₁ st₂ : St} (hfa : FaAfter σ s rest)
    (h : ∀ v, st₂.locs[v]? ≠ none → st₁.locs[v]? ≠ none ∨ v ∈ allocsOf st₁.rest ∨
      ∃ run, Atom.frameAddr v run ∈ atomsIn rest) :
    ∀ v ∈ pathVals σ [s] (walk1 σ s), st₂.locs[v]? ≠ none → st₁.locs[v]? ≠ none ∨
      v ∈ allocsOf st₁.rest := fun v hv hp =>
  (h v hp).elim Or.inl fun h' => h'.elim Or.inr fun ⟨run, hr⟩ => absurd hr (hfa v hv run)

/-- A statement's end clears the value waiting to be placed. -/
theorem end_lazy {α : Type} (m : P α) (st : St) :
    wpP (m >>= fun _ => endStmt) ctx st fun _ st' => st'.lazy = none :=
  wp_bind.mpr fun _ _ _ => by unfold endStmt; exact wp_modify.mpr rfl

theorem outEs_pre {o : Out} (h : o ≠ .stuck) (es : List Ev) :
    outEs (o.pre es) = es ++ outEs o := by
  cases o <;> simp_all [outEs, Out.pre]

/-- The atoms a block starts with are on its path. -/
theorem atom_onPath (σ : Val) : ∀ (rest : List Stmt) (k : ℕ) (a : Atom),
    (∀ j < k, ∃ b, rest[j]? = some (Stmt.atom b)) → rest[k]? = some (Stmt.atom a) →
    walk σ rest ≠ .stuck → Memory.Ev.atom a ∈ outEs (walk σ rest)
  | [], _, _, _, h, _ => nomatch h
  | s :: rest, 0, a, _, h, hns => by
    cases h
    have hr : walk σ rest ≠ .stuck := fun h' => hns (by simp [walk, walk1, Out.seq, h', Out.pre])
    simp only [walk, walk1, Out.seq] at hns ⊢
    rw [outEs_pre hr]
    exact List.mem_append_left _ (List.mem_singleton_self _)
  | s :: rest, k + 1, a, hj, h, hns => by
    obtain ⟨b, hb⟩ := hj 0 (Nat.succ_pos k)
    cases hb
    have hr : walk σ rest ≠ .stuck := fun h' => hns (by simp [walk, walk1, Out.seq, h', Out.pre])
    simp only [walk, walk1, Out.seq] at hns ⊢
    rw [outEs_pre hr]
    exact List.mem_append_right _ (atom_onPath σ rest k a
      (fun j hj' => hj (j + 1) (by omega)) h hr)

/-- **A block, statement by statement**: the first statement, then the rest on the path if the
path falls through it (off it if the final placement does not extend the state between or lacks
its instructions), off it if it returns. -/
theorem BlockW.cons (hmono : PlaceMono ctx) (hnew : PlaceNew ctx) {s : Stmt} {rest tl : List Stmt}
    (hfa : FaAfter I.σ s rest)
    (h₁ : StmtW Γ Ag cl ctx I s rest tl) (h₂ : BlockW Γ Ag cl ctx I (placeBlock rest) rest tl) :
    BlockW Γ Ag cl ctx I (placeBlock (s :: rest)) (s :: rest) tl := by
  intro C st sc sc'' i₀ p₀ o hsc hw hns hes hcl hinv
  rw [scopeBlock] at hsc
  split at hsc
  · cases hsc
  next sc₁ hsc₁ =>
  rw [walk] at hw
  rw [placeBlock, ← bind_assoc]
  cases ho₁ : walk1 I.σ s with
  | stuck =>
    rw [ho₁] at hw
    exact absurd hw.symm (by simpa [Out.seq] using hns)
  | ret es₁ vs =>
    rw [ho₁] at hw
    simp only [Out.seq] at hw
    subst hw
    refine FBAt.mono (FBAt.bind_dead (Q := fun st₁ _ st₂ => (st₁.chainIn = none →
        st₂.chainIn = none ∧ ∃ blk, st₂.out.toList = st₁.out.toList ++ blk) ∧
        ((st₁.lazy = none → ∀ v, st₂.locs[v]? ≠ none → st₁.locs[v]? ≠ none ∨
          v ∈ allocsOf st₁.rest ∨ ∃ run, Atom.frameAddr v run ∈ atomsIn rest) ∧
          (∀ v ∈ allocsOf st₂.rest, v ∈ allocsOf st₁.rest) ∧
          ∀ x ∈ st₁.tables.shared, x ∈ st₂.tables.shared))
      (FBAt.and_wp (h₁ C st sc sc₁ i₀ p₀ _ hsc₁ ⟨sc'', hsc⟩ ho₁ (by simp) hes hcl
      (fun _ h => nomatch h) hinv) (end_lazy _ st)) fun _ st₁ a s h =>
        let ⟨h1, h2, h3⟩ := hmono rest st₁ a s h
        ⟨h1, h2, h3, hnew rest st₁ a s h⟩) ?_
    rintro _ C' st₂ - - - ⟨_, st₁, ⟨⟨-, hc₁, hw₁⟩, hlz⟩, ⟨hq, hnw, hrr, htb⟩, hn₂, hl₂⟩
    obtain ⟨hc₂, blk₂, ho₂⟩ := hq hc₁
    refine ⟨(fun _ h => nomatch h), hc₂, fun hfin => ?_⟩
    obtain ⟨blk₁, ho₁', hb₁, hrw⟩ := hw₁ (hfin.back hn₂ hl₂ ho₂ htb)
    have hvs := placeNew_vs hfa (hnw hlz)
    rw [ho₁] at hvs
    refine ⟨blk₁ ++ blk₂, by rw [ho₂, ho₁', List.append_assoc], BlkW.append_ret hb₁, ?_⟩
    rw [pathVals_ret ho₁]
    exact hrw.grow (Stronger.refl _) hn₂ hl₂ hvs hrr
  | fall es₁ =>
    rw [ho₁] at hw
    simp only [Out.seq] at hw
    have hns₂ : walk I.σ rest ≠ .stuck := fun h => hns (by rw [← hw, h]; rfl)
    have hes' : outEs o = es₁ ++ outEs (walk I.σ rest) := by rw [← hw, outEs_pre hns₂]
    have hc' : calls (outEs o) = calls es₁ ++ calls (outEs (walk I.σ rest)) := by
      rw [hes', calls_append']
    refine FBAt.bind_if (FinAt Γ I Ag p₀)
      (Q := fun st₁ _ st₂ => (st₁.chainIn = none →
        st₂.chainIn = none ∧ ∃ blk, st₂.out.toList = st₁.out.toList ++ blk) ∧
        ∀ x ∈ st₁.tables.shared, x ∈ st₂.tables.shared)
      (h₁ C st sc sc₁ i₀ p₀ _ hsc₁ ⟨sc'', hsc⟩ ho₁ (by simp)
      (fun e he => hes e (by rw [hes']; exact List.mem_append_left _ he))
      (fun j hj => by
        rw [hcl j (by rw [hc', List.length_append]; simp only [outEs] at hj; omega), hc']
        simp only [outEs] at hj ⊢
        exact List.getElem?_append_left hj)
      (fun _ _ k a hj hk => hes _ (by
        rw [hes']; exact List.mem_append_right _ (atom_onPath I.σ rest k a hj hk hns₂))) hinv)
      (fun _ st₁ a s h =>
        let ⟨h1, h2, h3⟩ := hmono rest st₁ a s h
        ⟨h1, h2, h3, (hnew rest st₁ a s h).2.2⟩)
      (fun _ _ _ hr hF => (hr.1 es₁ rfl hF).cok)
      (fun _ st₁ C₁ hs₁ _ _ ⟨hw₁, _, hb₁⟩ hF => ?_)
      (fun _ C₁ st₁ _ st₂ ⟨_, hc₁, _⟩ hF hn₂ hl₂ ⟨hq, htb⟩ => by
        obtain ⟨hc₂, blk, ho⟩ := hq hc₁
        exact ⟨fun _ _ hF₂ => absurd (hF₂.back hn₂ hl₂ ho htb) hF, hc₂,
          fun hF₂ => absurd (hF₂.back hn₂ hl₂ ho htb) hF⟩)
    have hW₁ := hw₁ es₁ rfl hF
    refine FBAt.mono (FBAt.and_wp (h₂ C₁ st₁ sc₁ sc'' (i₀ + (calls es₁).length) p₀ _ hsc rfl hns₂
      (fun e he => hes e (by rw [hes']; exact List.mem_append_right _ he))
      (fun j hj => by
        rw [Nat.add_assoc, hcl _ (by rw [hc', List.length_append]; omega), hc',
          List.getElem?_append_right (by omega)]
        simp) hW₁) (hnew rest st₁)) ?_
    rintro _ C₂ st₂ hs₂ hn₂ hl₂ ⟨⟨hw₂, hc₂, hb₂⟩, hnw, hrr, htb⟩
    refine ⟨fun es he hF₂ => ?_, hc₂, fun hfin => ?_⟩
    · obtain ⟨es₂, h⟩ : ∃ es₂, walk I.σ rest = .fall es₂ := by
        cases h : walk I.σ rest with
        | fall es₂ => exact ⟨es₂, rfl⟩
        | ret es₂ vs => rw [← hw, h] at he; nomatch he
        | stuck => exact absurd h hns₂
      exact hw₂ es₂ h hF₂
    · obtain ⟨blk₂, ho₂, hb₂', hrw₂⟩ := hb₂ hfin
      obtain ⟨blk₁, ho₁', hb₁', hrw₁⟩ := hb₁ (hfin.back hn₂ hl₂ ho₂ htb)
      refine ⟨blk₁ ++ blk₂, by rw [ho₂, ho₁', List.append_assoc], ?_, ?_⟩
      · rw [← hw]
        rw [ho₁', bsize_append, ← Nat.add_assoc] at hb₂'
        exact BlkW.append_fall (hb₁'.mono hs₂) hb₂'
      · rw [← hw]
        have hvs := placeNew_vs hfa (hnw hW₁.lazy)
        rw [ho₁] at hvs
        exact ((hrw₁.grow hs₂ hn₂ hl₂ hvs hrr).append hrw₂).anti (pathVals_fall ho₁ hns₂)

end BlockCons

end
end LeanVM.Guest.Backend.Complete
