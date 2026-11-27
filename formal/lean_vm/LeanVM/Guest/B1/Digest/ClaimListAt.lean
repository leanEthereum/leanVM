/-
  LeanVM.Guest.B1.Digest.ClaimListAt

  `claim_list_digest` and `claim_list_chain` toward the uniform placed form: their bodies' parts,
  their evaluated valuations, and the chain buffer holding the sponge states an honest run leaves.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListComplete
public import LeanVM.Guest.B1.Digest.PlacedLib
public import LeanVM.Guest.B1.Main.NodeHonestAt
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«claim_list_digest»
import LeanVM.Guest.Data.ValNames.«claim_list_chain»
meta import LeanVM.Guest.KernelRfl
import LeanVM.Guest.StmtsAppend

/-!
# `claim_list_digest`, placed

`claim_list_digest`'s body is a branch on `n = 0` between two straight runs (`cl_body`). The empty
list's arm is atoms (`clz_core`: the evaluated valuation, its atoms holding). The nonempty list's
arm calls `list_split` and `claim_list_chain`. `claim_list_chain`'s body is straight
(`chain_body`): it allocates the chain buffer (`13 (a + b + 1)` words for `n = 136 a + 17 b + c`),
stores the zero state, runs `claim_list_chain_loop0` over the big frames when `a ≠ 0`,
`claim_list_chain_loop1` over the groups when `b ≠ 0`, and calls `claim_list_tail` on the rest
(`chain_core`: the evaluated valuation, its atoms holding on a memory holding the zero state at the
buffer). `chainCells`: the buffer's honest words, the state after each frame
(`claimChainMem_of_reads`). `ClaimListAtTB.lean` places them within their bounds.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT KidsDT Returns Kid DisjL Within
  disj_append completeAt_of_rel_pureD regionsOk_of within_append bufL bufL_within bufL_disj
  bufL_region LowDef)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)
open LeanVM.Guest.Budget (NodeHonest)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds exists_of_length_succ limb0_gen_pow_mul reads_of_memL
  regionL_of_mem)

@[expose] public section

/-! ## `claim_list_digest`'s path -/

theorem cl_body : Fn.body fn% «claim_list_digest» =
    clHead ++ .ite (.n (val% «claim_list_digest» "s1#1")) cl23Zero cl23Else :: (clTail ⧺ [.ret [.n (val% «claim_list_digest» "s3#0"), .n (val% «claim_list_digest» "s3#0[1]")]]) := by
  rw [claim_list_digest_shape]; rfl

set_option maxRecDepth 100000 in
theorem cl23Zero_straight : cl23Zero.all Main.Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cl23Else_straight : cl23Else.all Main.Stmt.straight = true := by decide +kernel

theorem clHead_straight : clHead.all Main.Stmt.straight = true := rfl
theorem clTail_straight : clTail.all Main.Stmt.straight = true := rfl

set_option maxRecDepth 100000 in
theorem cl23Zero_parts : cl23Zero.filterMap Main.Stmt.allocSz = [] ∧
    cl23Zero.filterMap Main.Stmt.addrS = [] ∧ cl23Zero.filterMap Main.Stmt.callS = [] ∧
    cl23Zero.filterMap B1.Stmt.loadS = [] := by decide +kernel

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
theorem chainFlat_split : chainFlat = chP1 ++ clDispS :: chPost := by
  kernel_rfl

set_option maxRecDepth 100000 in
theorem chPost_eq :
    chPost = chChk ⧺ [.atom (.copy (.n (val% «claim_list_chain» "s13#0")) (.n (val% «claim_list_chain» "d0"))), .atom (.copy (.n (val% «claim_list_chain» "s13#0[1]")) (.n (val% «claim_list_chain» "d1")))] := by
  kernel_rfl

set_option maxRecDepth 100000 in
theorem chChk_atoms : chChk.all isAtomS = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem chPost_straight : chPost.all Main.Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem chPost_parts : chPost.filterMap Main.Stmt.allocSz = [] ∧ chPost.filterMap Main.Stmt.addrS = [] ∧
    chPost.filterMap Main.Stmt.callS = [] ∧ chPost.filterMap B1.Stmt.loadS = [] := by
  decide +kernel

theorem chain_body : Fn.body fn% «claim_list_chain» =
    chP1 ++ clDispS :: (chPost ⧺ [.ret [.n (val% «claim_list_chain» "s13#0"), .n (val% «claim_list_chain» "s13#0[1]")]]) := by
  rw [claim_list_chain_shape, chainFlat_split]; simp

set_option maxRecDepth 100000 in
theorem chP1_straight : chP1.all Main.Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem chP1_allocs : chP1.filterMap Main.Stmt.allocSz = [(.n (val% «claim_list_chain» "chain"), .inr (.n (val% «claim_list_chain» "chain~7")))] := by decide +kernel

set_option maxRecDepth 100000 in
theorem chP1_addrs : chP1.filterMap Main.Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem chP1_calls : chP1.filterMap Main.Stmt.callS =
    [(some (.n (val% «claim_list_chain» "s2#1")), name% «claim_list_chain_loop0», [.n (val% «claim_list_chain» "s2#2"), .n (val% «claim_list_chain» "bigs"), .n (val% «claim_list_chain» "chain"), .n (val% «claim_list_chain» "entries_ptr")], []),
      (some (.n (val% «claim_list_chain» "s5#1")), name% «claim_list_chain_loop1», [.n (val% «claim_list_chain» "s5#2"), .n (val% «claim_list_chain» "groups"), .n (val% «claim_list_chain» "mid"), .n (val% «claim_list_chain» "mid_entries")],
          [])] := by decide +kernel

set_option maxRecDepth 100000 in
theorem chP1_loads : chP1.filterMap B1.Stmt.loadS = (List.range 13).map fun c => (.n (val% «claim_list_chain» "chain"), c) := by
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
theorem clz_core (entries : E) (hlow : LowDef 20 rd) :
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
      obtain ⟨t, ht⟩ := Sig.load_gpow hlow (show 0 < 2 ^ 20 by norm_num)
      rw [← gen_pow_eq_ofK] at ht
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
    (hlow : LowDef 23 rd) (hn23 : n < 2 ^ 23) :
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
  -- a `DEREF` through `g^i`, `i < 2^23`
  have hrd : ∀ (v : V) (i : ℕ), σ v = gen ^ i → i < 2 ^ 23 →
      IsInK (σ v) ∧ (rd ((σ v).limb 0 * addressOfIndex 0)).isSome := fun v i hv hi => by
    obtain ⟨t, ht⟩ := Sig.load_gpow hlow hi
    rw [← gen_pow_eq_ofK] at ht
    rw [hv]; exact ⟨ht.1, by rw [ht.2]; rfl⟩
  have hat : ∀ a ∈ atomsIn chainFlat, a.Holds rd σ := by
    refine atoms_holds_stores hg (fun x hx hnS hns => ?_) (fun _ a ha haS => ?_)
    · have := List.all_eq_true.mp b4 x hx
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
      rcases this with ((((((h | h) | h) | h) | h) | h) | h)
      · rw [hns] at h; exact absurd h (by simp)
      · exact absurd h hnS
      · right; rw [atomEqb_sound h]; exact hrd _ a v23 (by omega)
      · right; rw [atomEqb_sound h]; exact hrd _ b v24 (by omega)
      · right; rw [atomEqb_sound h]; exact hrd _ c v25 (by omega)
      · left; rw [atomEqb_sound h]
        show σ (.n (val% «claim_list_chain» "s11#14")) + σ (.n (val% «claim_list_chain» "n_g")) = 0
        rw [mono2Is_sound ch_id_ok hpure, v25, v23, v24, e1, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add,
          show c + a * 136 + b * 17 = n by omega]
        exact CharTwo.add_self_eq_zero _
      · right; rw [atomEqb_sound h]; exact hrd _ n e1 hn23
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

set_option maxRecDepth 100000 in
theorem big_pure : coreProgram.PureIn [name% «claim_list_chain_loop0»] :=
  pure_one (find_of_idx big_idx) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem grp_pure : coreProgram.PureIn [name% «claim_list_chain_loop1»] :=
  pure_one (find_of_idx grp_idx) (by decide +kernel)

theorem one_add_gen_ne {a : ℕ} (ha : a < 2 ^ 64 - 1) : ((1 : E) + gen ^ a ≠ 0) ↔ a ≠ 0 := by
  rw [Ne, e_add_eq_zero_iff, eq_comm, gen_pow_eq_one_iff ha]

set_option maxRecDepth 100000 in
theorem cl23Zero_atoms : cl23Zero.all isAtomS = true := by decide +kernel

theorem slOk_atomS {rd : Reader} {σ : Val} {s : Stmt} (hs : isAtomS s = true)
    (h : ∀ a, s = .atom a → a.Holds rd σ) : SlOk rd σ s := by
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

/-! ## `claim_list_digest`, placed -/

/-- The nonempty list's valuation, written out (`n = 136a + 17b + c`, the digest `D`, the touch of `g^n`). -/
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
