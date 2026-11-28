module

public import LeanVM.Guest.B1.Digest.ClaimListComplete
public import LeanVM.Guest.B1.Digest.CompleteSmall
public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.Memory.Straight
public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.Complete.Straight
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«claim_list_digest»
import LeanVM.Guest.Data.ValNames.«claim_list_chain»

/-!
# `claim_list_digest`'s valuations, layout-free

Restored from the archive's `B1/Digest/ClaimListAt` and `PlacedLib` (their layout-free part):
`claim_list_digest`'s and `claim_list_chain`'s paths and evaluated valuations (`clz_core`,
`chain_core`), the chain buffer's honest words (`chainCells`, `claimChainMem_of_reads`), the
honest shapes (`chHonest`, `clQ`, `clCalls`, `clTs`), `walk_ite`, the singletons' purity.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## A node's honest shape (the archive's `Budget/Kids`, `B1/Main/KidsT`) -/

/-- The entered callees' trees satisfy their predicates. -/
def KidsT : List Call → List (Tree → Prop) → List Tree → Prop
  | c :: cs, T :: Ts, k :: ks => (c.taken = true → T k) ∧ KidsT cs Ts ks
  | _, _, _ => True

/-- **A node's honest shape**: the node of `f` at a valuation satisfying `Q`, its walk's calls
`cs σ`, its `HeapBuf`s `bs σ`, its entered callees satisfying `Ts`. -/
def NodeHonest (P : Core.Program) (f : String) (Q : Val → Prop) (cs : Val → List Call)
    (bs : Val → List ℕ) (Ts : List (Tree → Prop)) (t : Tree) : Prop :=
  ∃ σ ks, t = .node f σ (bs σ) ks ∧ Q σ ∧
    (∀ fn es vs, P.find? f = some fn → walk σ fn.body = .ret es vs → calls es = cs σ) ∧
    (cs σ).length ≤ Ts.length ∧ KidsT (cs σ) Ts ks

/-! ## Shared -/
theorem walk_ite (σ : Val) (post : List Stmt) (hpost : post.all Stmt.straight = true)
    (c : V) (z n : List Stmt) (vs : List V) (esb : List Ev)
    (hb : (if σ c = 0 then walk σ z else walk σ n) = .fall esb) : ∀ pre : List Stmt,
    pre.all Stmt.straight = true →
    walk σ (pre ++ .ite c z n :: (post ++ [.ret vs])) =
      .ret (pre.flatMap (slEvs σ) ++ .inK c :: (esb ++ post.flatMap (slEvs σ))) vs
  | [], _ => by
    rw [List.nil_append, walk, walk1, hb, walk_straight σ vs post hpost]
    rfl
  | s :: pre, hpre => by
    simp only [List.all_cons, Bool.and_eq_true] at hpre
    rw [List.cons_append, walk, walk_ite σ post hpost c z n vs esb hb pre hpre.2,
      walk1_straight σ s hpre.1, Out.seq, Out.pre, List.flatMap_cons, List.append_assoc]

def noLoad : Atom → Bool
  | .load .. => false
  | _ => true

set_option maxRecDepth 100000 in
theorem list_split_leafOk : Lift.Stmt.leafOkList noLoad (fn% «list_split»).body = true :=
  by decide +kernel

theorem list_split_pure : coreProgram.PureIn ["list_split"] :=
  Lift.pureIn_of_leafOk find_list_split list_split_leafOk

section Es3

variable (σ : Val) (B C : List Ev) (g : String) (a r : List V)

theorem es3_allocs : allocs σ (B ++ .call g a r :: C) = allocs σ B ++ allocs σ C := by
  simp [allocs, List.filterMap_append, List.filterMap_cons, Ev.alloc?]

theorem es3_allocDsts : allocDsts (B ++ .call g a r :: C) = allocDsts B ++ allocDsts C := by
  simp [allocDsts, List.filterMap_append, List.filterMap_cons, Ev.allocDst?]

theorem es3_addrs : addrs (B ++ .call g a r :: C) = addrs B ++ addrs C := by
  simp [addrs, List.filterMap_append, List.filterMap_cons, Ev.addr?]

theorem es3_loads : loadAddrs σ (B ++ .call g a r :: C) = loadAddrs σ B ++ loadAddrs σ C := by
  simp [loadAddrs, List.filterMap_append, List.filterMap_cons, Ev.loadAddr?]

theorem es3_calls : calls (B ++ .call g a r :: C) = calls B ++ ⟨g, a, r, true⟩ :: calls C := by
  simp [calls, List.filterMap_append, Ev.call?]

end Es3

theorem cl_body : Fn.body fn% «claim_list_digest» =
    clHead ++ .ite (.n (val% «claim_list_digest» "s1#1")) cl23Zero cl23Else :: (clTail ++ [.ret [.n (val% «claim_list_digest» "s3#0"), .n (val% «claim_list_digest» "s3#0[1]")]]) := by
  rw [claim_list_digest_shape]; rfl

set_option maxRecDepth 100000 in
theorem cl23Zero_straight : cl23Zero.all Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cl23Else_straight : cl23Else.all Stmt.straight = true := by decide +kernel

theorem clHead_straight : clHead.all Stmt.straight = true := rfl
theorem clTail_straight : clTail.all Stmt.straight = true := rfl

set_option maxRecDepth 100000 in
theorem cl23Zero_parts : cl23Zero.filterMap Stmt.allocSz = [] ∧
    cl23Zero.filterMap Stmt.addrS = [] ∧ cl23Zero.filterMap Stmt.callS = [] ∧
    cl23Zero.filterMap stmtLoad? = [] := by decide +kernel

theorem cl_loop : coreProgram.loop "claim_list_digest" = false := by
  rw [Program.loop_of_find? find_claim_list_digest]; decide +kernel

/-! ## `claim_list_chain`'s path -/

/-- `claim_list_chain`'s body before its call of `claim_list_tail`. -/
noncomputable def chP1 : List Stmt := chainFlat.take (pos% «claim_list_chain» "d0")

/-- `claim_list_chain`'s body after its call of `claim_list_tail`: the checks of the split, the copies. -/
noncomputable def chPost : List Stmt := chainFlat.drop (pos% «claim_list_chain» "d0" + 1)

/-- The checks after the call of `claim_list_tail`: `bigs`, `groups`, `rest`, `list_split`'s identity and `n_g`. -/
noncomputable def chChk : List Stmt := chPost.dropLast.dropLast

set_option maxRecDepth 100000 in
theorem chainFlat_split : chainFlat = chP1 ++ clDispS :: chPost :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem chPost_eq :
    chPost = chChk ++ [.atom (.copy (.n (val% «claim_list_chain» "s13#0")) (.n (val% «claim_list_chain» "d0"))), .atom (.copy (.n (val% «claim_list_chain» "s13#0[1]")) (.n (val% «claim_list_chain» "d1")))] :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem chChk_atoms : chChk.all isAtomS = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem chPost_straight : chPost.all Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem chPost_parts : chPost.filterMap Stmt.allocSz = [] ∧ chPost.filterMap Stmt.addrS = [] ∧
    chPost.filterMap Stmt.callS = [] ∧ chPost.filterMap stmtLoad? = [] := by
  decide +kernel

theorem chain_body : Fn.body fn% «claim_list_chain» =
    chP1 ++ clDispS :: (chPost ++ [.ret [.n (val% «claim_list_chain» "s13#0"), .n (val% «claim_list_chain» "s13#0[1]")]]) := by
  rw [claim_list_chain_shape, chainFlat_split]; simp

set_option maxRecDepth 100000 in
theorem chP1_straight : chP1.all Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem chP1_allocs : chP1.filterMap Stmt.allocSz = [(.n (val% «claim_list_chain» "chain"), .inr (.n (val% «claim_list_chain» "chain~7")))] := by decide +kernel

set_option maxRecDepth 100000 in
theorem chP1_addrs : chP1.filterMap Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem chP1_calls : chP1.filterMap Stmt.callS =
    [(some (.n (val% «claim_list_chain» "s2#1")), name% «claim_list_chain_loop0», [.n (val% «claim_list_chain» "s2#2"), .n (val% «claim_list_chain» "bigs"), .n (val% «claim_list_chain» "chain"), .n (val% «claim_list_chain» "entries_ptr")], []),
      (some (.n (val% «claim_list_chain» "s5#1")), name% «claim_list_chain_loop1», [.n (val% «claim_list_chain» "s5#2"), .n (val% «claim_list_chain» "groups"), .n (val% «claim_list_chain» "mid"), .n (val% «claim_list_chain» "mid_entries")],
          [])] := by decide +kernel

set_option maxRecDepth 100000 in
theorem chP1_loads : chP1.filterMap stmtLoad? = (List.range 13).map fun c => (.n (val% «claim_list_chain» "chain"), c) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem chP1_kinds : chP1.all (fun s => isAtomS s || stmtEqb s clBigS || stmtEqb s clGrpS) = true := by
  decide +kernel

theorem ch_loop : coreProgram.loop "claim_list_chain" = false := by
  rw [Program.loop_of_find? find_claim_list_chain]; decide +kernel

theorem ch_param (σ : Val) : (Fn.params fn% «claim_list_chain»).map σ =
    [σ (.n (val% «claim_list_chain» "entries_ptr")), σ (.n (val% «claim_list_chain» "n_g")), σ (.n (val% «claim_list_chain» "bigs")), σ (.n (val% «claim_list_chain» "groups")), σ (.n (val% «claim_list_chain» "rest"))] := rfl

/-! ## The valuations -/

/-- The empty list's valuation. -/
noncomputable def clzσ (rd : Reader) (entries : E) : Val :=
  B1.Val.ofArgs (ev rd (fun _ => 0) [entries, gen ^ 0] clZEval)

variable {rd : Reader}

set_option maxRecDepth 20000 in
/-- **The empty list's valuation**: its atoms hold on a memory defined below `2^20`, where its check of `n_g = 1`
reads; it returns the empty string's digest. -/
theorem clz_core (entries : E) (h0 : ∃ t, LoadHolds rd (gen ^ 0) 0 t) :
    (∀ a ∈ atomsIn clZEval, a.Holds rd (clzσ rd entries)) ∧ clzσ rd entries (.n (val% «claim_list_digest» "entries_ptr")) = entries ∧
      clzσ rd entries (.n (val% «claim_list_digest» "n_g")) = gen ^ 0 ∧ clzσ rd entries (.n (val% «claim_list_digest» "s1#1")) = 0 ∧
      clzσ rd entries (.n (val% «claim_list_digest» "s1#1")) = gen ^ 0 + gen ^ 0 ∧
      [clzσ rd entries (.n (val% «claim_list_digest» "s3#0")), clzσ rd entries (.n (val% «claim_list_digest» "s3#0[1]"))] =
        digestCells (keccak256 (cellsBytes [])) := by
  have hz1 := cz_ok
  have hb1 := clbr_ok
  simp only [czOk, Bool.and_eq_true, decide_eq_true_eq] at hz1
  simp only [clBrOk, Bool.and_eq_true] at hb1
  obtain ⟨⟨⟨-, hzc⟩, hz10⟩, hz11⟩ := hz1
  obtain ⟨⟨⟨⟨-, b12⟩, b13⟩, b15⟩, -⟩ := hb1
  have c2 : Stmt.atom (.const (.n (val% «claim_list_digest» "s1#0")) (word 1 0)) ∈ clHead := by simp [clHead]
  have a3 : Stmt.atom (.add (.n (val% «claim_list_digest» "s1#1")) (.n (val% «claim_list_digest» "n_g")) (.n (val% «claim_list_digest» "s1#0"))) ∈ clHead := by simp [clHead]
  have t87 : Stmt.atom (.copy (.n (val% «claim_list_digest» "s3#0")) (.n (val% «claim_list_digest» "digest[0]"))) ∈ clTail := by simp [clTail]
  have t88 : Stmt.atom (.copy (.n (val% «claim_list_digest» "s3#0[1]")) (.n (val% «claim_list_digest» "digest[1]"))) ∈ clTail := by simp [clTail]
  obtain ⟨c', hchk⟩ := Option.isSome_iff_exists.mp b12
  let args : List E := [entries, gen ^ 0]
  set σ := clzσ rd entries with hσ
  obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) clZEval args hchk
  rw [show args.length = 2 from rfl, List.isEmpty_iff.mp b13] at hgs
  have hg : ∀ a ∈ atomsIn clZEval, Good rd [] (fun _ => 0) σ a := fun a ha =>
    hgs _ (cl_atom_mem ha)
  have e1 : σ (.n (val% «claim_list_digest» "n_g")) = gen ^ 0 := by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args])
  have hat : ∀ a ∈ atomsIn clZEval, a.Holds rd σ := by
    refine atoms_holds hg fun a ha hn => ?_
    have := List.all_eq_true.mp b15 a ha
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
    rcases this with h | h
    · rw [hn] at h; exact absurd h (by simp)
    · right; rw [atomEqb_sound h]
      obtain ⟨t, ht⟩ := h0
      show IsInK (σ (.n (val% «claim_list_digest» "n_g"))) ∧ (rd ((σ (.n (val% «claim_list_digest» "n_g"))).limb 0 * addressOfIndex 0)).isSome
      rw [e1]; exact ⟨ht.1, by rw [ht.2]; rfl⟩
  have mH : ∀ s ∈ clHead, s ∈ clZEval := fun s hs => by unfold clZEval; simp [hs]
  have mZ : ∀ s ∈ cl23Zero, s ∈ clZEval := fun s hs => by unfold clZEval; simp [hs]
  have mT : ∀ s ∈ clTail, s ∈ clZEval := fun s hs => by unfold clZEval; simp [hs]
  have hatZ : ∀ a ∈ atomsIn cl23Zero, a.Holds rd σ := fun a ha =>
    hat a (cl_mem_atoms (mZ _ (cl_atom_mem ha)))
  have e0 : σ (.n (val% «claim_list_digest» "entries_ptr")) = entries := by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args])
  have v2 : σ (.n (val% «claim_list_digest» "s1#0")) = word 1 0 := hat _ (cl_mem_atoms (mH _ c2))
  have v3 : σ (.n (val% «claim_list_digest» "s1#1")) = σ (.n (val% «claim_list_digest» "n_g")) + σ (.n (val% «claim_list_digest» "s1#0")) := hat _ (cl_mem_atoms (mH _ a3))
  have v87 : σ (.n (val% «claim_list_digest» "s3#0")) = σ (.n (val% «claim_list_digest» "digest[0]")) := hat _ (cl_mem_atoms (mT _ t87))
  have v88 : σ (.n (val% «claim_list_digest» "s3#0[1]")) = σ (.n (val% «claim_list_digest» "digest[1]")) := hat _ (cl_mem_atoms (mT _ t88))
  have h30 : σ (.n (val% «claim_list_digest» "s1#1")) = 0 := by
    rw [v3, v2, e1, word_one, pow_zero]; exact e_add_eq_zero_iff.mpr rfl
  have hd := chain_final hzc rfl hatZ (pre := []) (n := 0) rfl
    (fun c => (cellsOfState_zero false c).symm)
  rw [hz10, hz11, show List.take (czSpec.len / 16) (czSpec.vals σ) = [] by simp [czSpec],
    List.nil_append] at hd
  refine ⟨hat, e0, e1, h30, by rw [v3, v2, e1, word_one, pow_zero], ?_⟩
  rw [v87, v88, digestCells, ← hd]

/-- The oracle of `claim_list_chain`'s valuation: the chain buffer, the digest. -/
noncomputable def chw (chain : E) (D : Digest) (i : ℕ) : E :=
  if i = val% «claim_list_chain» "chain" then chain
  else if i = val% «claim_list_chain» "d0" then (digestHalves D).1
  else if i = val% «claim_list_chain» "d1" then (digestHalves D).2
  else 0

/-- `claim_list_chain`'s valuation on `n = 136a + 17b + c` claims at `entries`. -/
noncomputable def chσ (rd : Reader) (entries : E) (n : ℕ) (chain : E) (D : Digest) : Val :=
  B1.Val.ofArgs (ev rd (chw chain D) [entries, gen ^ n, gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)] chainFlat)

/-- **What `claim_list_chain`'s valuation is** (`a = n / 136`, `b = n % 136 / 17`, `c = n % 17`). -/
structure ChVals (rd : Reader) (σ : Val) (entries : E) (n : ℕ) (chain : E) (D : Digest) : Prop where
  atoms : ∀ a ∈ atomsIn chainFlat, a.Holds rd σ
  v0 : σ (.n (val% «claim_list_chain» "entries_ptr")) = entries
  v1 : σ (.n (val% «claim_list_chain» "n_g")) = gen ^ n
  v23 : σ (.n (val% «claim_list_chain» "bigs")) = gen ^ (n / 136)
  v24 : σ (.n (val% «claim_list_chain» "groups")) = gen ^ (n % 136 / 17)
  v25 : σ (.n (val% «claim_list_chain» "rest")) = gen ^ (n % 17)
  v33 : σ (.n (val% «claim_list_chain» "chain~7")) = gen ^ (13 * (n / 136 + n % 136 / 17 + 1))
  v34 : σ (.n (val% «claim_list_chain» "chain")) = chain
  v49 : σ (.n (val% «claim_list_chain» "s2#1")) = 1 + gen ^ (n / 136)
  v50 : σ (.n (val% «claim_list_chain» "s2#2")) = 1
  v56 : σ (.n (val% «claim_list_chain» "mid")) = chain * gen ^ (13 * (n / 136))
  v67 : σ (.n (val% «claim_list_chain» "mid_entries")) = entries * gen ^ (544 * (n / 136))
  v69 : σ (.n (val% «claim_list_chain» "s5#1")) = 1 + gen ^ (n % 136 / 17)
  v70 : σ (.n (val% «claim_list_chain» "s5#2")) = 1
  v76 : σ (.n (val% «claim_list_chain» "last")) = chain * gen ^ (13 * (n / 136 + n % 136 / 17))
  v84 : σ (.n (val% «claim_list_chain» "d0~9")) = entries * gen ^ (544 * (n / 136) + 68 * (n % 136 / 17))
  v85 : σ (.n (val% «claim_list_chain» "d0")) = (digestHalves D).1
  v86 : σ (.n (val% «claim_list_chain» "d1")) = (digestHalves D).2
  v87 : σ (.n (val% «claim_list_chain» "s13#0")) = (digestHalves D).1
  v88 : σ (.n (val% «claim_list_chain» "s13#0[1]")) = (digestHalves D).2

set_option maxRecDepth 100000 in
theorem ch_size_atoms : ∀ a ∈ [Atom.mul (.n (val% «claim_list_chain» "chain~0")) (.n (val% «claim_list_chain» "bigs")) (.n (val% «claim_list_chain» "groups")), .const (.n (val% «claim_list_chain» "chain~1")) (word 2 0),
    .mul (.n (val% «claim_list_chain» "chain~2")) (.n (val% «claim_list_chain» "chain~0")) (.n (val% «claim_list_chain» "chain~1")), .mul (.n (val% «claim_list_chain» "chain~3")) (.n (val% «claim_list_chain» "chain~2")) (.n (val% «claim_list_chain» "chain~2")), .mul (.n (val% «claim_list_chain» "chain~4")) (.n (val% «claim_list_chain» "chain~3")) (.n (val% «claim_list_chain» "chain~2")),
    .mul (.n (val% «claim_list_chain» "chain~5")) (.n (val% «claim_list_chain» "chain~4")) (.n (val% «claim_list_chain» "chain~4")), .mul (.n (val% «claim_list_chain» "chain~6")) (.n (val% «claim_list_chain» "chain~5")) (.n (val% «claim_list_chain» "chain~5")), .mul (.n (val% «claim_list_chain» "chain~7")) (.n (val% «claim_list_chain» "chain~6")) (.n (val% «claim_list_chain» "chain~2"))],
    a ∈ atomsIn chainFlat := by
  decide +kernel

set_option maxRecDepth 20000 in
/-- `claim_list_chain`'s check of `list_split`'s identity, over its products: `n_g = rest · bigs^136 · groups^17`. -/
theorem ch_id_ok : mono2Is ((atomsIn chainFlat).filter pureB) (.n (val% «claim_list_chain» "s11#14")) (.n (val% «claim_list_chain» "rest")) (.n (val% «claim_list_chain» "bigs")) 136 (.n (val% «claim_list_chain» "groups")) 17 = true := by
  decide +kernel

set_option maxRecDepth 20000 in
/-- **`claim_list_chain`'s valuation**: on a memory holding the zero state at the chain buffer and defined below
`2^23`, where its checks of `g^a`, `g^b`, `g^c` and `g^n`, `n < 2^23`, read. -/
theorem chain_core {entries chain : E} {n : ℕ} (D : Digest) (hz0 : StateAt rd chain 0 zeroState)
    (hdef : ∀ i, i = n / 136 ∨ i = n % 136 / 17 ∨ i = n % 17 ∨ i = n → ∃ t, LoadHolds rd (gen ^ i) 0 t) :
    ChVals rd (chσ rd entries n chain D) entries n chain D := by
  have he1 := chainBody_ok
  have hb1 := chain_ok
  simp only [chainBodyOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at he1
  simp only [chainOk, Bool.and_eq_true] at hb1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h50⟩, h49⟩, h48⟩, h70⟩, h69⟩, h68⟩, -⟩, hm56⟩, hm67⟩,
    hm76⟩, hm84⟩, hc87⟩, hc88⟩ := he1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨b2, b3⟩, b4⟩, -⟩, -⟩, -⟩, -⟩, b11⟩, b12⟩ := hb1
  set a := n / 136 with hadef
  set b := n % 136 / 17 with hbdef
  set c := n % 17 with hcdef
  set w := chw chain D with hw
  obtain ⟨c', hchk⟩ := Option.isSome_iff_exists.mp b2
  let args : List E := [entries, gen ^ n, gen ^ a, gen ^ b, gen ^ c]
  set σ := chσ rd entries n chain D with hσ
  obtain ⟨-, -, hgs⟩ := ev_spec rd w chainFlat args hchk
  rw [show args.length = 5 from rfl] at hgs
  set SE := storesOf 5 chainFlat with hSE
  have hg : ∀ a ∈ atomsIn chainFlat, Good rd SE w σ a := fun a ha => hgs _ (cl_atom_mem ha)
  have par : ∀ i (hi : i < 5), σ (.n i) = args.getD i 0 := fun i hi =>
    ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have e0 : σ (.n (val% «claim_list_chain» "entries_ptr")) = entries := par 0 (by omega)
  have e1 : σ (.n (val% «claim_list_chain» "n_g")) = gen ^ n := par 1 (by omega)
  have v23 : σ (.n (val% «claim_list_chain» "bigs")) = gen ^ a := par 2 (by omega)
  have v24 : σ (.n (val% «claim_list_chain» "groups")) = gen ^ b := par 3 (by omega)
  have v25 : σ (.n (val% «claim_list_chain» "rest")) = gen ^ c := par 4 (by omega)
  have v34 : σ (.n (val% «claim_list_chain» "chain")) = chain := by
    obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp b12
    have hga := hg x hx
    cases x with
    | hint h =>
      cases h with
      | allocDyn d s =>
        simp only [decide_eq_true_eq] at hp
        subst hp
        have hga' : σ (.n (val% «claim_list_chain» "chain")) = w (val% «claim_list_chain» "chain") := hga
        rw [hga', hw]; simp [chw]
      | _ => simp at hp
    | _ => simp at hp
  have v35 : ∀ c < 13, σ (.n ((val% «claim_list_chain» "s1.i0:zero_state.s0.u0.s0#0") + c)) = 0 := by
    intro c hc'
    obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp (List.all_eq_true.mp b11 c (List.mem_range.mpr hc'))
    have hga := hg x hx
    cases x <;> simp only [isConstAt, Bool.false_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hp
    obtain ⟨rfl, he⟩ := hp
    have hga' : σ (.n ((val% «claim_list_chain» "s1.i0:zero_state.s0.u0.s0#0") + c)) = _ := hga
    rw [hga', eEqb_sound he, word_zero]
  have hpure : ∀ a ∈ (atomsIn chainFlat).filter pureB, a.Holds rd σ := fun a ha =>
    holds_of_pure (List.mem_filter.mp ha).2 (hg a (List.mem_filter.mp ha).1)
  -- a `DEREF` through `g^i`, the word at `i` defined
  have hrd : ∀ (v : V) (i : ℕ), σ v = gen ^ i → (∃ t, LoadHolds rd (gen ^ i) 0 t) →
      IsInK (σ v) ∧ (rd ((σ v).limb 0 * addressOfIndex 0)).isSome := fun v i hv hi => by
    obtain ⟨t, ht⟩ := hi
    rw [hv]; exact ⟨ht.1, by rw [ht.2]; rfl⟩
  have hat : ∀ a ∈ atomsIn chainFlat, a.Holds rd σ := by
    refine atoms_holds_stores hg (fun x hx hnS hns => ?_) (fun _ a ha haS => ?_)
    · have := List.all_eq_true.mp b4 x hx
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
      rcases this with ((((((h | h) | h) | h) | h) | h) | h)
      · rw [hns] at h; exact absurd h (by simp)
      · exact absurd h hnS
      · right; rw [atomEqb_sound h]; exact hrd _ a v23 (hdef _ (Or.inl rfl))
      · right; rw [atomEqb_sound h]; exact hrd _ b v24 (hdef _ (Or.inr (Or.inl rfl)))
      · right; rw [atomEqb_sound h]; exact hrd _ c v25 (hdef _ (Or.inr (Or.inr (Or.inl rfl))))
      · left; rw [atomEqb_sound h]
        show σ (.n (val% «claim_list_chain» "s11#14")) + σ (.n (val% «claim_list_chain» "n_g")) = 0
        rw [mono2Is_sound ch_id_ok hpure, v25, v23, v24, e1, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add,
          show c + a * 136 + b * 17 = n by omega]
        exact CharTwo.add_self_eq_zero _
      · right; rw [atomEqb_sound h]; exact hrd _ n e1 (hdef _ (Or.inr (Or.inr (Or.inr rfl))))
    · obtain ⟨c, hc', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp b3 a haS)
      rw [atomEqb_sound he]
      have hc13 := List.mem_range.mp hc'
      show LoadHolds rd (σ (.n (val% «claim_list_chain» "chain"))) c (σ (.n ((val% «claim_list_chain» "s1.i0:zero_state.s0.u0.s0#0") + c)))
      rw [v34, v35 c hc13]
      have := hz0 ⟨c, hc13⟩
      rwa [Nat.zero_add, cellsOfState_zero] at this
  have hdisp : clDispS ∈ chainFlat := by rw [chainFlat_split]; simp
  have gd : ∀ v ∈ [V.n (val% «claim_list_chain» "d0"), V.n (val% «claim_list_chain» "d1")], σ v = w v.idx := hgs _ hdisp
  have v85 : σ (.n (val% «claim_list_chain» "d0")) = (digestHalves D).1 := (gd _ (by simp)).trans (by rw [hw]; simp [chw])
  have v86 : σ (.n (val% «claim_list_chain» "d1")) = (digestHalves D).2 := (gd _ (by simp)).trans (by rw [hw]; simp [chw])
  have v50 : σ (.n (val% «claim_list_chain» "s2#2")) = 1 := by rw [const_sound h50 hat, word_one]
  have v49 : σ (.n (val% «claim_list_chain» "s2#1")) = 1 + gen ^ a := by
    rw [add_sound h49 hat, const_sound h48 hat, word_one, v23]
  have v70 : σ (.n (val% «claim_list_chain» "s5#2")) = 1 := by rw [const_sound h70 hat, word_one]
  have v69 : σ (.n (val% «claim_list_chain» "s5#1")) = 1 + gen ^ b := by
    rw [add_sound h69 hat, const_sound h68 hat, word_one, v24]
  have v56 : σ (.n (val% «claim_list_chain» "mid")) = chain * gen ^ (13 * a) := by
    rw [monoIs_sound hm56 hat, v34, v23, gen_pow_pow]
  have v67 : σ (.n (val% «claim_list_chain» "mid_entries")) = entries * gen ^ (544 * a) := by
    rw [monoIs_sound hm67 hat, e0, v23, gen_pow_pow]
  have v76 : σ (.n (val% «claim_list_chain» "last")) = chain * gen ^ (13 * (a + b)) := by
    rw [mono2Is_sound hm76 hat, v34, v23, v24, gen_pow_pow, gen_pow_pow, mul_assoc, ← pow_add,
      Nat.mul_add]
  have v84 : σ (.n (val% «claim_list_chain» "d0~9")) = entries * gen ^ (544 * a + 68 * b) := by
    rw [mono2Is_sound hm84 hat, e0, v23, v24, gen_pow_pow, gen_pow_pow, mul_assoc, ← pow_add]
  have hs := ch_size_atoms
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs
  obtain ⟨s26, s27, s28, s29, s30, s31, s32, s33⟩ := hs
  have q26 : σ (.n (val% «claim_list_chain» "chain~0")) = σ (.n (val% «claim_list_chain» "bigs")) * σ (.n (val% «claim_list_chain» "groups")) := hat _ s26
  have q27 : σ (.n (val% «claim_list_chain» "chain~1")) = word 2 0 := hat _ s27
  have q28 : σ (.n (val% «claim_list_chain» "chain~2")) = σ (.n (val% «claim_list_chain» "chain~0")) * σ (.n (val% «claim_list_chain» "chain~1")) := hat _ s28
  have q29 : σ (.n (val% «claim_list_chain» "chain~3")) = σ (.n (val% «claim_list_chain» "chain~2")) * σ (.n (val% «claim_list_chain» "chain~2")) := hat _ s29
  have q30 : σ (.n (val% «claim_list_chain» "chain~4")) = σ (.n (val% «claim_list_chain» "chain~3")) * σ (.n (val% «claim_list_chain» "chain~2")) := hat _ s30
  have q31 : σ (.n (val% «claim_list_chain» "chain~5")) = σ (.n (val% «claim_list_chain» "chain~4")) * σ (.n (val% «claim_list_chain» "chain~4")) := hat _ s31
  have q32 : σ (.n (val% «claim_list_chain» "chain~6")) = σ (.n (val% «claim_list_chain» "chain~5")) * σ (.n (val% «claim_list_chain» "chain~5")) := hat _ s32
  have q33 : σ (.n (val% «claim_list_chain» "chain~7")) = σ (.n (val% «claim_list_chain» "chain~6")) * σ (.n (val% «claim_list_chain» "chain~2")) := hat _ s33
  refine ⟨hat, e0, e1, v23, v24, v25, ?_, v34, v49, v50, v56, v67, v69, v70, v76, v84, v85, v86,
    by rw [copy_sound hc87 hat, v85], by rw [copy_sound hc88 hat, v86]⟩
  rw [q33, q32, q31, q30, q29, q28, q27, q26, v23, v24, word_gen, ← pow_add, ← pow_succ, pow_mul']
  generalize gen ^ (a + b + 1) = x
  ring

/-! ## The chain buffer -/

/-- A state's thirteen cells. -/
def stCells (S : KeccakState) : List E := List.ofFn (cellsOfState S false)

/-- **The chain buffer's honest words**: the state after each of the first `a + b + 1` frames
(`a` big frames, then `b` groups). -/
def chainCells (cells : List E) (a b : ℕ) : List E :=
  (List.range (a + b + 1)).flatMap fun t =>
    stCells (absorbChunks (8 * clU a t) zeroState (cellsBytes (cells.take (68 * clU a t))))

theorem length_chainCells (cells : List E) (a b : ℕ) :
    (chainCells cells a b).length = 13 * (a + b + 1) := by
  simp only [chainCells, List.length_flatMap, stCells, List.length_ofFn, List.map_const',
    List.length_range, List.sum_replicate, smul_eq_mul]
  ring

theorem state_of_reads {chain : E} {cells : List E} {a b : ℕ}
    (h : ReadsAt rd chain (chainCells cells a b)) {t : ℕ} (ht : t ≤ a + b) :
    StateAt rd (chain * gen ^ (13 * t)) 0
      (absorbChunks (8 * clU a t) zeroState (cellsBytes (cells.take (68 * clU a t)))) := by
  intro c
  have := Main.readsAt_range_flatMap (w := 13) (fun q _ => by simp [stCells]) h t (by omega) c c.isLt
  rw [loadHolds_mul_gen_pow, Nat.zero_add]
  rw [stCells, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn] at this
  exact this

theorem clU_le {a t : ℕ} {n : ℕ} (ha : a = n / 136) (ht : t ≤ a + n % 136 / 17) :
    68 * clU a t ≤ 4 * n := by
  unfold clU
  have := Nat.div_add_mod n 136
  have := Nat.div_add_mod (n % 136) 17
  rcases Nat.le_total t a with h | h
  · rw [Nat.min_eq_left h]; omega
  · rw [Nat.min_eq_right h]; omega

/-- **`ClaimChainMem` off the chain buffer's honest words.** -/
theorem claimChainMem_of_reads {entries chain : E} {n : ℕ} {cells : List E}
    (hl : cells.length = 4 * n) (hr : ReadsAt rd entries cells)
    (h : ReadsAt rd chain (chainCells cells (n / 136) (n % 136 / 17))) :
    ClaimChainMem rd chain entries n := by
  intro t ht
  rw [memRun_take hr (by rw [hl]; exact clU_le rfl ht)]
  exact state_of_reads h ht

/-- The chain buffer's last state: after every frame, `68 (8a + b)` cells. -/
theorem clU_last (a b : ℕ) : clU a (a + b) = 8 * a + b := by
  unfold clU; rw [Nat.min_eq_right (by omega)]; omega

/-! ## Placed -/

theorem clNames_get {r : ℕ} (hr : r < 17) : clNames[r]! = clNames.getD r "" := by
  have h : r < clNames.length := by simp [clNames]; omega
  rw [getElem!_pos clNames r h, List.getD_eq_getElem _ _ h]

theorem one_add_gen_ne {a : ℕ} (ha : a < 2 ^ 64 - 1) : ((1 : E) + gen ^ a ≠ 0) ↔ a ≠ 0 := by
  rw [Ne, e_add_eq_zero_iff, eq_comm, gen_pow_eq_one_iff ha]

set_option maxRecDepth 100000 in
theorem cl23Zero_atoms : cl23Zero.all isAtomS = true := by decide +kernel

theorem sOk_atomS {rd : Reader} {σ : Val} {s : Stmt} (hs : isAtomS s = true)
    (h : ∀ a, s = .atom a → a.Holds rd σ) : Complete.SOk rd σ s := by
  cases s <;> simp only [isAtomS, Bool.false_eq_true] at hs
  exact h _ rfl

/-! ## The honest shapes -/

/-- `claim_list_chain`'s words that end its loops and size its buffer (`n = 136a + 17b + c`): `g^a`, `g^b`, `g^c`
(the first two end `claim_list_chain_loop0`, `claim_list_chain_loop1`), the chain buffer's size
`g^(13 (a + b + 1))`, the loops' start `1`. -/
def chQ (n : ℕ) (σ : Val) : Prop :=
  σ (.n (val% «claim_list_chain» "bigs")) = gen ^ (n / 136) ∧ σ (.n (val% «claim_list_chain» "groups")) = gen ^ (n % 136 / 17) ∧
    σ (.n (val% «claim_list_chain» "rest")) = gen ^ (n % 17) ∧ σ (.n (val% «claim_list_chain» "chain~7")) = gen ^ (13 * (n / 136 + n % 136 / 17 + 1)) ∧
    σ (.n (val% «claim_list_chain» "s2#2")) = 1 ∧ σ (.n (val% «claim_list_chain» "s5#2")) = 1

/-- `claim_list_chain`'s calls: `claim_list_chain_loop0` when `n / 136 ≠ 0`, `claim_list_chain_loop1` when
`n % 136 / 17 ≠ 0`, `claim_list_tail`. -/
def chCalls (n : ℕ) (_ : Val) : List Call :=
  [⟨name% «claim_list_chain_loop0», [.n (val% «claim_list_chain» "s2#2"), .n (val% «claim_list_chain» "bigs"), .n (val% «claim_list_chain» "chain"), .n (val% «claim_list_chain» "entries_ptr")], [], decide (n / 136 ≠ 0)⟩,
    ⟨name% «claim_list_chain_loop1», [.n (val% «claim_list_chain» "s5#2"), .n (val% «claim_list_chain» "groups"), .n (val% «claim_list_chain» "mid"), .n (val% «claim_list_chain» "mid_entries")], [],
        decide (n % 136 / 17 ≠ 0)⟩,
    ⟨"claim_list_tail", [.n (val% «claim_list_chain» "last"), .n (val% «claim_list_chain» "d0~9"), .n (val% «claim_list_chain» "rest")], [.n (val% «claim_list_chain» "d0"), .n (val% «claim_list_chain» "d1")], true⟩]

/-- `claim_list_chain`'s `HeapBuf`: the chain buffer. -/
def chBufs (n : ℕ) (_ : Val) : List ℕ := [13 * (n / 136 + n % 136 / 17 + 1)]

/-- No constraint on `claim_list_chain`'s callees. -/
def chTs : List (Tree → Prop) := [fun _ => True, fun _ => True, fun _ => True]

/-- **`claim_list_chain`'s honest shape** on `n` claims. -/
def chHonest (n : ℕ) : Tree → Prop :=
  NodeHonest coreProgram "claim_list_chain" (chQ n) (chCalls n) (chBufs n) chTs

/-- `claim_list_digest`'s words that end its callees' loops (`n = 136a + 17b + c`): the count; when `n ≠ 0`,
`list_split`'s returns. -/
def clQ (n : ℕ) (σ : Val) : Prop :=
  σ (.n (val% «claim_list_digest» "n_g")) = gen ^ n ∧ (n ≠ 0 → σ (.n (val% «claim_list_digest» "bigs")) = gen ^ (n / 136) ∧ σ (.n (val% «claim_list_digest» "groups")) = gen ^ (n % 136 / 17) ∧
    σ (.n (val% «claim_list_digest» "rest")) = gen ^ (n % 17))

/-- `claim_list_digest`'s calls: none for the empty list; `list_split`, `claim_list_chain`. -/
def clCalls (n : ℕ) (_ : Val) : List Call :=
  if n = 0 then [] else
    [⟨"list_split", [.n (val% «claim_list_digest» "n_g")], [.n (val% «claim_list_digest» "bigs"), .n (val% «claim_list_digest» "groups"), .n (val% «claim_list_digest» "rest")], true⟩,
      ⟨"claim_list_chain", [.n (val% «claim_list_digest» "entries_ptr"), .n (val% «claim_list_digest» "n_g"), .n (val% «claim_list_digest» "bigs"), .n (val% «claim_list_digest» "groups"), .n (val% «claim_list_digest» "rest")],
        [.n (val% «claim_list_digest» "d0"), .n (val% «claim_list_digest» "d1")], true⟩]

/-- The claim list's `HeapBuf`s: none (`claim_list_chain` places the chain buffer). -/
def clBufs (_ : ℕ) (_ : Val) : List ℕ := []

/-- `claim_list_digest`'s callees: `list_split` unconstrained, `claim_list_chain` of honest shape. -/
def clTs (n : ℕ) : List (Tree → Prop) := [fun _ => True, chHonest n]

/-! ## `claim_list_chain`, placed -/

set_option maxRecDepth 20000 in
noncomputable def clEσ (rd : Reader) (eP n : ℕ) (D : Digest) : Val :=
  B1.Val.ofArgs [gen ^ eP, gen ^ n, word 1 0, gen ^ n + word 1 0, 0, 0, 0, 0, 0, 0,
    (digestHalves D).1, (digestHalves D).2, gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17),
    (digestHalves D).1, (digestHalves D).2, rdAt rd (gen ^ n) 0, (digestHalves D).1, (digestHalves D).2]

theorem cl23Else_eq : cl23Else = [clSplitS, clChainS, .atom (.copy (.n (val% «claim_list_digest» "digest[0]")) (.n (val% «claim_list_digest» "d0"))),
    .atom (.copy (.n (val% «claim_list_digest» "digest[1]")) (.n (val% «claim_list_digest» "d1")))] := by
  have hb1 := clbr_ok
  simp only [clBrOk, Bool.and_eq_true] at hb1
  exact stmtsEqb_sound hb1.1.1.1.1

end
end LeanVM.Guest.B1.Digest
