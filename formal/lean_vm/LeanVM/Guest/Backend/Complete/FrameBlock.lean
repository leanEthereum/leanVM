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
  ∃ hs : ℕ → List (E × E), ∀ Ψ, C Ψ → ∀ σ', I.Same σ' → ∀ (kh : ℕ → E × E) (cs : List Stmt)
    (pos : ℕ) (ks : List (ℕ × ℕ)) (next : List Stmt → List (ℕ × ℕ) → Prop)
    (kj : List (ℕ × ℕ) → E → E → Prop) (kret khalt : Prop),
    ctrlSplit cs = ctrlSplit (ss ++ tl) → KsAt cl kh i₀ (calls (outEs o)) (hs pos) ks →
    OutK o tl next kret ks →
    wLc Γ I.fp σ' I.hdr ⟨patchT I Ψ σ', kh⟩ (Ag σ' Ψ kh) cl blk cs pos ks next kj kret khalt

/-- `FAt` for actions that place control statements: the constraint's properties kept, the next
free cell and the places growing, the result under the new constraint and state. -/
def FBAt {α : Type} (ctx : Ctx) (I : Inst) (C : (ℕ → E) → Prop) (st : St) (m : P α)
    (R : α → ((ℕ → E) → Prop) → St → Prop) : Prop :=
  COk I C st.next st.scope st.locs →
  wpP m ctx st fun a st' => ∃ C', COk I C' st'.next st'.scope st'.locs ∧ Stronger C' C ∧
    st.next ≤ st'.next ∧ LocsLe st.locs st'.locs ∧ R a C' st'

/-- **The block lemma's statement**: placing the core block `ss` (followed by `tl`) on the path
of the instance, in lockstep with the scope walk from `s` to `s'`, keeps the invariant and lays
statements whose words are `BlkW` (once the final placement extends the state reached and has
their instructions). -/
def BlockW {κ₀ : ℕ} (Γ : Site κ₀) (Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) →
    MemoryImage κ → Prop) (cl : List Call) (ctx : Ctx) (I : Inst) (m : P Unit)
    (ss tl : List Stmt) : Prop :=
  ∀ (C : (ℕ → E) → Prop) (st : St) (s s' : SSt) (i₀ : ℕ) (o : Out),
    scopeBlock ctx.retCells ss s = .ok s' → walk I.σ ss = o → o ≠ .stuck →
    (∀ e ∈ outEs o, e ∈ I.es) → (∀ j < (calls (outEs o)).length, cl[i₀ + j]? = (calls (outEs o))[j]?) →
    WInv ctx I C st s →
    FBAt ctx I C st m fun _ C' st' => WInv ctx I C' st' s' ∧
      ∃ blk, st'.out.toList = st.out.toList ++ blk ∧
        (Fits I st' → BlkW Γ I Ag cl C' blk ss tl o i₀)

end
end LeanVM.Guest.Backend.Complete
