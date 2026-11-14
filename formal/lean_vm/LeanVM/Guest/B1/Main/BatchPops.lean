/-
  LeanVM.Guest.B1.Main.BatchPops

  The witness-stream entries the batching of the deferred claims pops (`aggregate_claims`, `lean_ethereum.py:4855-4862`) are the honest hint generator's (`Hints.batchPushes`).
-/

module

public import LeanVM.Guest.B1.Main.AggAt
public import LeanVM.Guest.B1.Common.MutePops
public import LeanVM.Guest.B1.Common.NoWitMute
public import LeanVM.Guest.Hints

/-!
# The batching's pops

`aggregate_claims` allocates the sumcheck's messages' buffer, pops the messages into it (`bc_sumcheck_msgs`), then the bytecode's value (`bc_star_hint`); nothing else in its call tree pops.

* `agg_shape_ok`: past its head, its body has no witness hint, nor its callees' subtrees (`noWitBlock`, kernel evaluation);
* `aggHead_pops`: its first three statements pop the buffer's words and the value;
* `aggregate_claims_complete_pops`: on its completing valuation (`agg_core`), every valid call instance pops exactly `batchPushes h`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- `aggregate_claims`' first statements: the messages' buffer, its hint, the bytecode's value's hint. -/
def aggHead : List Stmt :=
  [.atom (.hint (.alloc (.n 6) 47)), .atom (.hint (.witness "bc_sumcheck_msgs" (.heap (.n 6) 0 47))),
    .atom (.hint (.witness "bc_star_hint" (.stack [.n 7])))]

/-- `aggregate_claims` starts with `aggHead`, then has no witness hint, nor its callees' subtrees. -/
noncomputable def aggShapeOk : Bool :=
  stmtsEqb ((Fn.body fn% «aggregate_claims»).take 3) aggHead &&
    noWitBlock idx% «aggregate_claims» ((Fn.body fn% «aggregate_claims»).drop 3)

theorem agg_shape_ok : aggShapeOk = true := by decide +kernel

/-- The entries `aggHead` pops on `σ`: the buffer's words, the value. -/
def aggPops (rd : Reader) (σ : Val) : List Pop :=
  [("bc_sumcheck_msgs", (List.range 47).map fun k => (rd ((σ (.n 6)).limb 0 * addressOfIndex (0 + k))).getD 0),
    ("bc_star_hint", [σ (.n 7)])]

theorem aggHead_pops (rd : Reader) (σ : Val) : FallPops rd σ aggHead (aggPops rd σ) := by
  have h := (FallPops.atom (rd := rd) (σ := σ) (.hint (.alloc (.n 6) 47))).append
    ((FallPops.atom (.hint (.witness "bc_sumcheck_msgs" (.heap (.n 6) 0 47)))).append
      (FallPops.atom (.hint (.witness "bc_star_hint" (.stack [.n 7])))))
  simpa [aggHead, aggPops, Atom.pops, Hint.pops, Dest.words] using h

theorem length_msgs (ms : List (E × E)) : (ms.flatMap fun g => [g.1, g.2]).length = 2 * ms.length := by
  induction ms with
  | nil => rfl
  | cons g ms ih => rw [List.flatMap_cons, List.length_append, ih, List.length_cons]; simp; omega

/-- A buffer of `47` words read off the memory holding them. -/
theorem words_of_reads {rd : Reader} {p : E} {L : List E} (h : ReadsAt rd p L) (hl : L.length = 47) :
    ((List.range 47).map fun k => (rd (p.limb 0 * addressOfIndex (0 + k))).getD 0) = L := by
  refine List.ext_getElem (by simp [hl]) fun k h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, Nat.zero_add]
  rw [(h k h2).2]
  rfl

/-- **`aggregate_claims` is complete, popping its hints**: on `agg_core`'s valuation, which holds the bytecode's value (`AggVals.v7`) and points at the messages' buffer (`AggVals.v6`), every valid call instance pops exactly `batchPushes h`. -/
theorem aggregate_claims_complete_pops {rd : Reader} {m : ℕ} {cpi cfresh ccarried dst tabs : E}
    {cs : List ChildClaims} (hcl : cs.length = m)
    (hcw : ∀ c (hc : c < cs.length), ChildWordsAt rd cpi cfresh ccarried c cs[c])
    {h : BatchingHints} {out : DeferredClaim} (hrl : h.sumcheckMessages.length = 23)
    (hb : batch cs h = some out) {P : AggPtrs} (hmem : AggMem rd cfresh ccarried dst cs h P) :
    AggVals rd (aggσ rd m cpi cfresh ccarried dst tabs P cs h) m cpi cfresh ccarried dst tabs P cs h ∧
      ∀ (bufs : List ℕ) (kids : List Memory.Tree) (args rets : List E),
        (Memory.Tree.node "aggregate_claims" (aggσ rd m cpi cfresh ccarried dst tabs P cs h) bufs kids).Valid
          coreProgram rd args rets →
        (Memory.Tree.node "aggregate_claims" (aggσ rd m cpi cfresh ccarried dst tabs P cs h) bufs kids).pops
          coreProgram rd = Hints.batchPushes h := by
  have hV := agg_core (tabs := tabs) hcl hcw hrl hb hmem
  refine ⟨hV, fun bufs kids args rets hv => ?_⟩
  have hs := agg_shape_ok
  simp only [aggShapeOk, Bool.and_eq_true] at hs
  have hbody : Fn.body fn% «aggregate_claims» = aggHead ++ (Fn.body fn% «aggregate_claims»).drop 3 := by
    rw [← stmtsEqb_sound hs.1, List.take_append_drop]
  rw [Tree.pops_of_prefix_mute noWitS_mute hv find_aggregate_claims hbody (aggHead_pops rd _) (noWitBlock_mute hs.2),
    aggPops, hV.v6,
    hV.v7, words_of_reads hmem.msgs (by rw [List.length_cons, length_msgs, hrl]), Hints.batchPushes]

end
end LeanVM.Guest.B1.Main
