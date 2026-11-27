/-
  LeanVM.Guest.B1.Digest.ClaimListsAtT

  `child_claim_list_digest` in the uniform placed form by a tree of honest shape
  (`Budget.NodeHonest`): the honest run takes the walk by hinted indices (`child_mono` hinted `0`),
  `child_claim_list_any`, which places the chain buffer.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListAt
public import LeanVM.Guest.B1.Digest.ChildDigest
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«child_claim_list_digest»
import LeanVM.Guest.StmtsAppend

/-!
# A child's claim list, placed

The body is a branch on `n = 0` between two runs (`ccd_body`). The empty list's arm
hashes the empty string (`ccz_core`: the evaluated valuation, its atoms holding). The nonempty
list's arm (`ccElse`) calls `list_split`, hints `child_mono`, and branches on `child_mono + g`:
the honest prover hints `0`, so the run takes the walk by hinted indices, a call of
`child_claim_list_any`. Either walk is sound
(`child_claim_list_digest_sound`); completeness picks its own hints.

`ccQ n σ`: the list's length `g^n` at `v4`; when `n ≠ 0`, `list_split`'s returns `g^a`, `g^b`, `g^c`
at `v26`, `v27`, `v28` (`n = 136a + 17b + c`), the hint `0` at `v29`. `ccCalls n`: none for the
empty list; `list_split`, `child_claim_list_any`. `ccBufs n`: none (`child_claim_list_any` places
the chain buffer). `ccTs n`: `child_claim_list_any`'s tree of honest shape `anyHonest n`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT KidsDT Returns Kid DisjL Within
  regionsOk_of LowDef)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds exists_of_length_succ)
open LeanVM.Guest.Budget (NodeHonest)

@[expose] public section

/-! ## The path -/

/-- The head of `child_claim_list_digest`'s body: `n_g + 1`. -/
def ccdHead : List Stmt := [.atom (.const (.n (val% «child_claim_list_digest» "s1#0")) (word 1 0)), .atom (.add (.n (val% «child_claim_list_digest» "s1#1")) (.n (val% «child_claim_list_digest» "n_g")) (.n (val% «child_claim_list_digest» "s1#0")))]

/-- The final copies of `child_claim_list_digest`. -/
def ccdTail : List Stmt := [.atom (.copy (.n (val% «child_claim_list_digest» "s2#0")) (.n (val% «child_claim_list_digest» "digest[0]"))), .atom (.copy (.n (val% «child_claim_list_digest» "s2#0[1]")) (.n (val% «child_claim_list_digest» "digest[1]")))]

/-- The nonempty arm before its branch: `list_split`, the hint `child_mono`, `child_mono + g`. -/
def ccE4 : List Stmt :=
  [.call "list_split" [.n (val% «child_claim_list_digest» "n_g")] [.n (val% «child_claim_list_digest» "bigs"), .n (val% «child_claim_list_digest» "groups"), .n (val% «child_claim_list_digest» "rest")],
    .atom (.hint (.witness "child_mono" (.stack [.n (val% «child_claim_list_digest» "mono")]))),
    .atom (.const (.n (val% «child_claim_list_digest» "s1.e.s2#0")) (word 2 0)), .atom (.add (.n (val% «child_claim_list_digest» "s1.e.s2#1")) (.n (val% «child_claim_list_digest» "mono")) (.n (val% «child_claim_list_digest» "s1.e.s2#0")))]

/-- The gap walk's arm. -/
def ccMonoArm : List Stmt :=
  [.call "child_claim_list_mono" [.n (val% «child_claim_list_digest» "entries_ptr"), .n (val% «child_claim_list_digest» "region"), .n (val% «child_claim_list_digest» "base"), .n (val% «child_claim_list_digest» "limit_g"), .n (val% «child_claim_list_digest» "bigs"), .n (val% «child_claim_list_digest» "groups"), .n (val% «child_claim_list_digest» "rest")] [.n (val% «child_claim_list_digest» "d0@1"), .n (val% «child_claim_list_digest» "d1@1")],
    .atom (.copy (.n (val% «child_claim_list_digest» "digest[0]")) (.n (val% «child_claim_list_digest» "d0@1"))), .atom (.copy (.n (val% «child_claim_list_digest» "digest[1]")) (.n (val% «child_claim_list_digest» "d1@1")))]

/-- The walk by hinted indices' arm. -/
def ccAnyArm : List Stmt :=
  [.call "child_claim_list_any" [.n (val% «child_claim_list_digest» "entries_ptr"), .n (val% «child_claim_list_digest» "region"), .n (val% «child_claim_list_digest» "base"), .n (val% «child_claim_list_digest» "limit_g"), .n (val% «child_claim_list_digest» "bigs"), .n (val% «child_claim_list_digest» "groups"), .n (val% «child_claim_list_digest» "rest")] [.n (val% «child_claim_list_digest» "d0@2"), .n (val% «child_claim_list_digest» "d1@2")],
    .atom (.copy (.n (val% «child_claim_list_digest» "digest[0]")) (.n (val% «child_claim_list_digest» "d0@2"))), .atom (.copy (.n (val% «child_claim_list_digest» "digest[1]")) (.n (val% «child_claim_list_digest» "d1@2")))]

/-- The nonempty arm. -/
def ccElse : List Stmt := ccE4 ⧺ [.ite (.n (val% «child_claim_list_digest» "s1.e.s2#1")) ccMonoArm ccAnyArm]

theorem ccd_body : Fn.body fn% «child_claim_list_digest» =
    ccdHead ++ .ite (.n (val% «child_claim_list_digest» "s1#1")) cc25Zero ccElse :: (ccdTail ⧺ [.ret [.n (val% «child_claim_list_digest» "s2#0"), .n (val% «child_claim_list_digest» "s2#0[1]")]]) := by
  rw [child_claim_list_digest_shape]; rfl

set_option maxRecDepth 100000 in
theorem cc25Zero_straight : cc25Zero.all Main.Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cc25Zero_parts : cc25Zero.filterMap Main.Stmt.allocSz = [] ∧
    cc25Zero.filterMap Main.Stmt.addrS = [] ∧ cc25Zero.filterMap Main.Stmt.callS = [] ∧
    cc25Zero.filterMap B1.Stmt.loadS = [] ∧ cc25Zero.all isAtomS = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ccd_loop : coreProgram.loop "child_claim_list_digest" = false := by
  rw [Program.loop_of_find? find_child_claim_list_digest]; decide +kernel

theorem ccd_param (σ : Val) : (Fn.params fn% «child_claim_list_digest»).map σ =
    [σ (.n (val% «child_claim_list_digest» "entries_ptr")), σ (.n (val% «child_claim_list_digest» "region")), σ (.n (val% «child_claim_list_digest» "base")), σ (.n (val% «child_claim_list_digest» "limit_g")), σ (.n (val% «child_claim_list_digest» "n_g"))] := rfl

/-- A straight run, then a branch between straight arms, falls through. -/
theorem walk_pre_ite (σ : Val) (z n : List Stmt) (hz : z.all Main.Stmt.straight = true)
    (hn : n.all Main.Stmt.straight = true) (c : V) : ∀ pre : List Stmt,
    pre.all Main.Stmt.straight = true →
    walk σ (pre ⧺ [.ite c z n]) =
      .fall (pre.flatMap (Main.slEvs σ) ++ .inK c :: (if σ c = 0 then z else n).flatMap (Main.slEvs σ))
  | [], _ => by
    rw [List.nil_append, walk, walk1, walk]
    by_cases h : σ c = 0
    · simp only [h, ↓reduceIte, walk_straight_fall σ z hz, Out.pre, Out.seq, List.flatMap_nil,
        List.nil_append, List.append_nil, List.singleton_append]
    · simp only [h, ↓reduceIte, walk_straight_fall σ n hn, Out.pre, Out.seq, List.flatMap_nil,
        List.nil_append, List.append_nil, List.singleton_append]
  | s :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.cons_append, walk, walk_pre_ite σ z n hz hn c pre h.2, Main.walk1_straight σ s h.1,
      Out.seq, Out.pre, List.flatMap_cons, List.append_assoc]

/-! ## The empty list -/

/-- The empty list's run, evaluated. -/
noncomputable def ccZEval : List Stmt := ccdHead ⧺ cc25Zero ⧺ fillH 15 25 ⧺ ccdTail

/-- **The empty list's run, evaluated**: in order, no store, no side condition. -/
noncomputable def cczOk : Bool :=
  (chk 5 ccZEval).isSome && (storesOf 5 ccZEval).isEmpty &&
    (atomsIn ccZEval).all (fun a => !needsSide a)

set_option maxRecDepth 100000 in
theorem ccz_ok : cczOk = true := by decide +kernel

/-- The empty list's valuation. -/
noncomputable def cczσ (rd : Reader) (args : List E) : Val :=
  B1.Val.ofArgs (ev rd (fun _ => 0) args ccZEval)

variable {rd : Reader}

set_option maxRecDepth 20000 in
/-- **The empty list's valuation**: its atoms hold, it returns the empty string's digest. -/
theorem ccz_core (entries region base limit : E) :
    let σ := cczσ rd [entries, region, base, limit, gen ^ 0]
    (∀ a ∈ atomsIn ccZEval, a.Holds rd σ) ∧
      [σ (.n (val% «child_claim_list_digest» "entries_ptr")), σ (.n (val% «child_claim_list_digest» "region")), σ (.n (val% «child_claim_list_digest» "base")), σ (.n (val% «child_claim_list_digest» "limit_g")), σ (.n (val% «child_claim_list_digest» "n_g"))] = [entries, region, base, limit, gen ^ 0] ∧
      σ (.n (val% «child_claim_list_digest» "s1#1")) = 0 ∧ σ (.n (val% «child_claim_list_digest» "s1#1")) = gen ^ 0 + gen ^ 0 ∧
      [σ (.n (val% «child_claim_list_digest» "s2#0")), σ (.n (val% «child_claim_list_digest» "s2#0[1]"))] = digestCells (keccak256 (cellsBytes [])) := by
  intro σ
  have hz1 := cc25z_ok
  have hb1 := ccz_ok
  simp only [cc25ZOk, Bool.and_eq_true, decide_eq_true_eq] at hz1
  simp only [cczOk, Bool.and_eq_true] at hb1
  obtain ⟨⟨⟨-, hzc⟩, hz13⟩, hz14⟩ := hz1
  obtain ⟨⟨b12, b13⟩, b15⟩ := hb1
  have c5 : Stmt.atom (.const (.n (val% «child_claim_list_digest» "s1#0")) (word 1 0)) ∈ ccdHead := by simp [ccdHead]
  have a6 : Stmt.atom (.add (.n (val% «child_claim_list_digest» "s1#1")) (.n (val% «child_claim_list_digest» "n_g")) (.n (val% «child_claim_list_digest» "s1#0"))) ∈ ccdHead := by simp [ccdHead]
  have t36 : Stmt.atom (.copy (.n (val% «child_claim_list_digest» "s2#0")) (.n (val% «child_claim_list_digest» "digest[0]"))) ∈ ccdTail := by simp [ccdTail]
  have t37 : Stmt.atom (.copy (.n (val% «child_claim_list_digest» "s2#0[1]")) (.n (val% «child_claim_list_digest» "digest[1]"))) ∈ ccdTail := by simp [ccdTail]
  obtain ⟨c', hchk⟩ := Option.isSome_iff_exists.mp b12
  let args : List E := [entries, region, base, limit, gen ^ 0]
  obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) ccZEval args hchk
  rw [show args.length = 5 from rfl, List.isEmpty_iff.mp b13] at hgs
  have hg : ∀ a ∈ atomsIn ccZEval, Good rd [] (fun _ => 0) σ a := fun a ha =>
    hgs _ (cl_atom_mem ha)
  have hns : ∀ a ∈ atomsIn ccZEval, needsSide a = false := by
    intro a ha
    have := List.all_eq_true.mp b15 a ha
    simpa using this
  have hat : ∀ a ∈ atomsIn ccZEval, a.Holds rd σ :=
    atoms_holds hg fun a ha hn => absurd hn (by simp [hns a ha])
  have mH : ∀ s ∈ ccdHead, s ∈ ccZEval := fun s hs => by unfold ccZEval; simp [hs]
  have mZ : ∀ s ∈ cc25Zero, s ∈ ccZEval := fun s hs => by unfold ccZEval; simp [hs]
  have mT : ∀ s ∈ ccdTail, s ∈ ccZEval := fun s hs => by unfold ccZEval; simp [hs]
  have hatZ : ∀ a ∈ atomsIn cc25Zero, a.Holds rd σ := fun a ha =>
    hat a (cl_mem_atoms (mZ _ (cl_atom_mem ha)))
  have par : ∀ i (hi : i < 5), σ (.n i) = args.getD i 0 := fun i hi =>
    ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have v5 : σ (.n (val% «child_claim_list_digest» "s1#0")) = word 1 0 := hat _ (cl_mem_atoms (mH _ c5))
  have v6 : σ (.n (val% «child_claim_list_digest» "s1#1")) = σ (.n (val% «child_claim_list_digest» "n_g")) + σ (.n (val% «child_claim_list_digest» "s1#0")) := hat _ (cl_mem_atoms (mH _ a6))
  have v36 : σ (.n (val% «child_claim_list_digest» "s2#0")) = σ (.n (val% «child_claim_list_digest» "digest[0]")) := hat _ (cl_mem_atoms (mT _ t36))
  have v37 : σ (.n (val% «child_claim_list_digest» "s2#0[1]")) = σ (.n (val% «child_claim_list_digest» "digest[1]")) := hat _ (cl_mem_atoms (mT _ t37))
  have v6' : σ (.n (val% «child_claim_list_digest» "s1#1")) = gen ^ 0 + gen ^ 0 := by
    rw [v6, v5, par 4 (by omega), word_one, pow_zero]; rfl
  have h60 : σ (.n (val% «child_claim_list_digest» "s1#1")) = 0 := by rw [v6']; exact e_add_eq_zero_iff.mpr rfl
  have hd := chain_final hzc rfl hatZ (pre := []) (n := 0) rfl
    (fun c => (cellsOfState_zero false c).symm)
  rw [hz13, hz14, show List.take (cc25ZSpec.len / 16) (cc25ZSpec.vals σ) = [] by
    simp [cc25ZSpec], List.nil_append] at hd
  refine ⟨hat, ?_, h60, v6', ?_⟩
  · rw [par 0 (by omega), par 1 (by omega), par 2 (by omega), par 3 (by omega), par 4 (by omega)]
    rfl
  · rw [v36, v37, digestCells, ← hd]

/-! ## The honest shape -/

/-- `child_claim_list_digest`'s words that end its callees' loops (`n = 136a + 17b + c`): the count
at `v4`; when `n ≠ 0`, `list_split`'s returns `g^a`, `g^b`, `g^c` at `v26`, `v27`, `v28`, the hint
`child_mono = 0` at `v29` (the walk by hinted indices). -/
def ccQ (n : ℕ) (σ : Val) : Prop :=
  σ (.n (val% «child_claim_list_digest» "n_g")) = gen ^ n ∧ (n ≠ 0 → σ (.n (val% «child_claim_list_digest» "bigs")) = gen ^ (n / 136) ∧ σ (.n (val% «child_claim_list_digest» "groups")) = gen ^ (n % 136 / 17) ∧
    σ (.n (val% «child_claim_list_digest» "rest")) = gen ^ (n % 17) ∧ σ (.n (val% «child_claim_list_digest» "mono")) = 0)

/-- `child_claim_list_digest`'s calls: none for the empty list; `list_split`,
`child_claim_list_any`. -/
def ccCalls (n : ℕ) (_ : Val) : List Call :=
  if n = 0 then [] else
    [⟨"list_split", [.n (val% «child_claim_list_digest» "n_g")], [.n (val% «child_claim_list_digest» "bigs"), .n (val% «child_claim_list_digest» "groups"), .n (val% «child_claim_list_digest» "rest")], true⟩,
      ⟨"child_claim_list_any", [.n (val% «child_claim_list_digest» "entries_ptr"), .n (val% «child_claim_list_digest» "region"), .n (val% «child_claim_list_digest» "base"), .n (val% «child_claim_list_digest» "limit_g"), .n (val% «child_claim_list_digest» "bigs"), .n (val% «child_claim_list_digest» "groups"), .n (val% «child_claim_list_digest» "rest")], [.n (val% «child_claim_list_digest» "d0@2"), .n (val% «child_claim_list_digest» "d1@2")], true⟩]

/-- No `HeapBuf` of its own: `child_claim_list_any` places the chain buffer. -/
def ccBufs (_ : ℕ) (_ : Val) : List ℕ := []

/-- `child_claim_list_any`'s tree of honest shape. -/
def ccTs (n : ℕ) : List (Tree → Prop) := [fun _ => True, anyHonest n]

end
end LeanVM.Guest.B1.Digest
