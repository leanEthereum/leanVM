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

theorem cl23Zero_straight : cl23Zero.all Main.Stmt.straight = true := by decide +kernel

theorem cl23Else_straight : cl23Else.all Main.Stmt.straight = true := by decide +kernel

theorem clHead_straight : clHead.all Main.Stmt.straight = true := rfl
theorem clTail_straight : clTail.all Main.Stmt.straight = true := rfl

theorem cl23Zero_parts : cl23Zero.filterMap Main.Stmt.allocSz = [] ∧
    cl23Zero.filterMap Main.Stmt.addrS = [] ∧ cl23Zero.filterMap Main.Stmt.callS = [] ∧
    cl23Zero.filterMap B1.Stmt.loadS = [] := by decide +kernel

theorem chainFlat_split : chainFlat = chP1 ++ clDispS :: chPost := by
  kernel_rfl

theorem chPost_eq :
    chPost = chChk ⧺ [.atom (.copy (.n (val% «claim_list_chain» "s13#0")) (.n (val% «claim_list_chain» "d0"))), .atom (.copy (.n (val% «claim_list_chain» "s13#0[1]")) (.n (val% «claim_list_chain» "d1")))] := by
  kernel_rfl

theorem chChk_atoms : chChk.all isAtomS = true := by decide +kernel

theorem chPost_straight : chPost.all Main.Stmt.straight = true := by decide +kernel

theorem chPost_parts : chPost.filterMap Main.Stmt.allocSz = [] ∧ chPost.filterMap Main.Stmt.addrS = [] ∧
    chPost.filterMap Main.Stmt.callS = [] ∧ chPost.filterMap B1.Stmt.loadS = [] := by
  decide +kernel

theorem chain_body : Fn.body fn% «claim_list_chain» =
    chP1 ++ clDispS :: (chPost ⧺ [.ret [.n (val% «claim_list_chain» "s13#0"), .n (val% «claim_list_chain» "s13#0[1]")]]) := by
  rw [claim_list_chain_shape, chainFlat_split]; simp

theorem chP1_straight : chP1.all Main.Stmt.straight = true := by decide +kernel

theorem chP1_allocs : chP1.filterMap Main.Stmt.allocSz = [(.n (val% «claim_list_chain» "chain"), .inr (.n (val% «claim_list_chain» "chain~7")))] := by decide +kernel

theorem chP1_addrs : chP1.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem chP1_calls : chP1.filterMap Main.Stmt.callS =
    [(some (.n (val% «claim_list_chain» "s2#1")), name% «claim_list_chain_loop0», [.n (val% «claim_list_chain» "s2#2"), .n (val% «claim_list_chain» "bigs"), .n (val% «claim_list_chain» "chain"), .n (val% «claim_list_chain» "entries_ptr")], []),
      (some (.n (val% «claim_list_chain» "s5#1")), name% «claim_list_chain_loop1», [.n (val% «claim_list_chain» "s5#2"), .n (val% «claim_list_chain» "groups"), .n (val% «claim_list_chain» "mid"), .n (val% «claim_list_chain» "mid_entries")],
          [])] := by decide +kernel

theorem chP1_loads : chP1.filterMap B1.Stmt.loadS = (List.range 13).map fun c => (.n (val% «claim_list_chain» "chain"), c) := by
  decide +kernel

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

theorem ch_size_atoms : ∀ a ∈ [Atom.mul (.n (val% «claim_list_chain» "chain~0")) (.n (val% «claim_list_chain» "bigs")) (.n (val% «claim_list_chain» "groups")), .const (.n (val% «claim_list_chain» "chain~1")) (word 2 0),
    .mul (.n (val% «claim_list_chain» "chain~2")) (.n (val% «claim_list_chain» "chain~0")) (.n (val% «claim_list_chain» "chain~1")), .mul (.n (val% «claim_list_chain» "chain~3")) (.n (val% «claim_list_chain» "chain~2")) (.n (val% «claim_list_chain» "chain~2")), .mul (.n (val% «claim_list_chain» "chain~4")) (.n (val% «claim_list_chain» "chain~3")) (.n (val% «claim_list_chain» "chain~2")),
    .mul (.n (val% «claim_list_chain» "chain~5")) (.n (val% «claim_list_chain» "chain~4")) (.n (val% «claim_list_chain» "chain~4")), .mul (.n (val% «claim_list_chain» "chain~6")) (.n (val% «claim_list_chain» "chain~5")) (.n (val% «claim_list_chain» "chain~5")), .mul (.n (val% «claim_list_chain» "chain~7")) (.n (val% «claim_list_chain» "chain~6")) (.n (val% «claim_list_chain» "chain~2"))],
    a ∈ atomsIn chainFlat := by
  decide +kernel

/-- `claim_list_chain`'s check of `list_split`'s identity, over its products: `n_g = rest · bigs^136 · groups^17`. -/
theorem ch_id_ok : mono2Is ((atomsIn chainFlat).filter pureB) (.n (val% «claim_list_chain» "s11#14")) (.n (val% «claim_list_chain» "rest")) (.n (val% «claim_list_chain» "bigs")) 136 (.n (val% «claim_list_chain» "groups")) 17 = true := by
  decide +kernel

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

theorem big_pure : coreProgram.PureIn [name% «claim_list_chain_loop0»] :=
  pure_one (find_of_idx big_idx) (by decide +kernel)

theorem grp_pure : coreProgram.PureIn [name% «claim_list_chain_loop1»] :=
  pure_one (find_of_idx grp_idx) (by decide +kernel)

theorem one_add_gen_ne {a : ℕ} (ha : a < 2 ^ 64 - 1) : ((1 : E) + gen ^ a ≠ 0) ↔ a ≠ 0 := by
  rw [Ne, e_add_eq_zero_iff, eq_comm, gen_pow_eq_one_iff ha]

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

/-- **`claim_list_digest` is complete, placed, by a tree of honest shape**: `n < 136 · 2^20` claims' cells at `g^eP`
among the caller's words; it returns their digest's cells. -/
theorem claim_list_digest_completeAtT (fs : String → ℕ) (cert : String → V → ℕ) {Lin : Main.Layout}
    {eP n : ℕ} {cells : List E} (hn : n < 2 ^ 23) (hl : cells.length = 4 * n)
    (hLe : ∀ rd, MemL rd Lin → ReadsAt rd (gen ^ eP) cells) :
    CompleteAtDT fs cert 23 "claim_list_digest" Lin [gen ^ eP, gen ^ n]
      (Returns (digestCells (keccak256 (cellsBytes cells))))
      (NodeHonest coreProgram "claim_list_digest" (clQ n) (clCalls n) (clBufs n) (clTs n)) := by
  intro fp
  have mH : ∀ s ∈ clHead, isAtomS s = true := by decide
  have mTl : ∀ s ∈ clTail, isAtomS s = true := by decide
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · -- the empty list
    have hcl : cells = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hcl
    refine ⟨fs "claim_list_digest", [], _, [], ⟨rfl, rfl⟩, fun q hq => by simp at hq, B1.disj_nil,
      fun rd hlow hm => ?_⟩
    obtain ⟨hat, e0, e1, h30, h3, hret⟩ := clz_core (rd := rd) (gen ^ eP) (hlow.mono (by norm_num))
    set σ := clzσ rd (gen ^ eP) with hσ
    have hb : (if σ (.n (val% «claim_list_digest» "s1#1")) = 0 then walk σ cl23Zero else walk σ cl23Else) =
        .fall (cl23Zero.flatMap (Main.slEvs σ)) := by
      simp only [h30, ↓reduceIte]; exact walk_straight_fall σ _ cl23Zero_straight
    have hw := walk_ite σ clTail clTail_straight (.n (val% «claim_list_digest» "s1#1")) cl23Zero cl23Else [.n (val% «claim_list_digest» "s3#0"), .n (val% «claim_list_digest» "s3#0[1]")] _ hb
      clHead clHead_straight
    rw [← cl_body] at hw
    set es := clHead.flatMap (Main.slEvs σ) ++ .inK (.n (val% «claim_list_digest» "s1#1")) ::
      (cl23Zero.flatMap (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ)) with hes
    have hmZ : ∀ s ∈ clHead ++ cl23Zero ++ clTail, ∀ a, s = .atom a → a.Holds rd σ := by
      intro s hs a rfl
      refine hat a (cl_mem_atoms ?_)
      unfold clZEval
      simp only [List.mem_append] at hs ⊢
      rcases hs with (hs | hs) | hs
      · exact Or.inl (Or.inl (Or.inl hs))
      · exact Or.inl (Or.inl (Or.inr hs))
      · exact Or.inr hs
    have hev : ∀ e ∈ es, e.Holds rd σ := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact slEvs_holds (fun s hs => slOk_atomS (mH s hs) (hmZ s (by simp [hs]))) e he
      rcases List.mem_cons.mp he with rfl | he
      · show IsInK (σ (.n (val% «claim_list_digest» "s1#1"))); rw [h3]; exact gen_pow_add_isInK 0 0
      rcases List.mem_append.mp he with he | he
      · exact slEvs_holds (fun s hs => slOk_atomS (List.all_eq_true.mp cl23Zero_atoms s hs)
          (hmZ s (by simp [hs]))) e he
      · exact slEvs_holds (fun s hs => slOk_atomS (mTl s hs) (hmZ s (by simp [hs]))) e he
    obtain ⟨hhd, hha, hhad, hhc⟩ := Main.straight_parts σ _ clHead_straight
    obtain ⟨hzd, hza, hzad, hzc⟩ := Main.straight_parts σ _ cl23Zero_straight
    obtain ⟨htd, hta, htad, htc⟩ := Main.straight_parts σ _ clTail_straight
    obtain ⟨z1, z2, z3, z4⟩ := cl23Zero_parts
    have hal : allocs σ es = [] := by
      rw [hes, allocs_append, show allocs σ (.inK (.n (val% «claim_list_digest» "s1#1")) :: (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ))) = allocs σ (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ)) from rfl, allocs_append, hha, hza, hta, z1]
      rfl
    have h := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
      (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (N := 0) (fp := fp)
      (args := [gen ^ eP, gen ^ 0]) (rets := digestCells (keccak256 (cellsBytes [])))
      coreProgram_wf find_claim_list_digest (Or.inl cl_loop) (by rw [cl_param, e0, e1]) hw hret hev
      (by
        rw [hal, hes, allocDsts_append, show allocDsts (.inK (.n (val% «claim_list_digest» "s1#1")) :: (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ))) = allocDsts (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ)) from rfl, allocDsts_append, hhd, hzd, htd, z1]
        rfl)
      (fun q hq => by
        rw [hes, addrs_append, show addrs (.inK (.n (val% «claim_list_digest» "s1#1")) :: (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ))) = addrs (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ)) from rfl, addrs_append, hhad, hzad, htad, z2] at hq
        simp [clHead, clTail, Main.Stmt.addrS] at hq)
      (clTs 0)
      (by
        rw [hes, calls_append, show calls (.inK (.n (val% «claim_list_digest» "s1#1")) :: (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ))) = calls (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ)) from rfl, calls_append, hhc, hzc, htc, z3]
        exact ⟨rfl, fun _ h => h⟩)
      (fun A hA => by
        rw [hes, loadAddrs_append, show loadAddrs σ (.inK (.n (val% «claim_list_digest» "s1#1")) :: (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ))) = loadAddrs σ (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ)) from rfl, loadAddrs_append,
          B1.loadAddrs_straight σ _ clHead_straight, B1.loadAddrs_straight σ _ cl23Zero_straight,
          B1.loadAddrs_straight σ _ clTail_straight, z4] at hA
        simp [clHead, clTail, B1.Stmt.loadS] at hA)
      (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
    have hce : calls es = [] := by
      rw [hes, calls_append, show calls (.inK (.n (val% «claim_list_digest» "s1#1")) :: (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ))) = calls (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ)) from rfl, calls_append, hhc, hzc, htc, z3]
      rfl
    have h' := relAtInT_nodeHonest (Q := clQ 0) (cs := clCalls 0) (bs := clBufs 0) h
      find_claim_list_digest hw ⟨e1, fun h0 => absurd rfl h0⟩ (by rw [hce]; rfl) (by rw [hal]; rfl)
      (by simp [clCalls, clTs])
    rw [hal] at h'
    simpa using h'
  · -- a nonempty list
    set D := keccak256 (cellsBytes cells) with hD
    let ks : List Kid :=
      [⟨"list_split", true, [gen ^ n], [], Returns [gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)]⟩,
        ⟨"claim_list_chain", true, [gen ^ eP, gen ^ n, gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)],
          Lin, Returns (digestCells D)⟩]
    have hsplit : CompleteAtD fs cert 20 "list_split" [] [gen ^ n]
        (Returns [gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)]) := by
      have := list_split_completeAt fs cert (a := n / 136) (b := n % 136 / 17) (c := n % 17)
        (by simp [bigFramesCap]; omega) (by simp [bigGroups]; omega) (by simp [claimGroup]; omega)
      rwa [show claimBig * (n / 136) + claimGroup * (n % 136 / 17) + n % 17 = n by
        simp [claimBig, claimGroup]; omega] at this
    have hokT : KidsDT fs cert 23 ks (clTs n) :=
      ⟨fun _ => (hsplit.lowMono (by norm_num)).toT,
        fun _ => claim_list_chain_completeAtT fs cert hn hl hLe, trivial⟩
    obtain ⟨Nk, Lk, outs, hoo, hW, hDj, -, hKids⟩ :=
      kidsFromInT_of_kidsDT (fs := fs) (cert := cert) 23 ks (clTs n) hokT (fp + fs "claim_list_digest")
    have hl0 : outs.length = 2 := hoo.length
    obtain ⟨o1, t1, rfl, hl1⟩ := exists_of_length_succ hl0
    obtain ⟨o2, t2, rfl, hl2⟩ := exists_of_length_succ hl1
    obtain rfl := List.eq_nil_of_length_eq_zero hl2
    obtain ⟨h1, h2, -⟩ := hoo
    refine ⟨fs "claim_list_digest" + Nk, Lk, _, [], ⟨rfl, rfl⟩, ?_, by rw [List.nil_append]; exact hDj,
      fun rd hlow hm => ?_⟩
    · rw [List.nil_append]; exact hW.mono (by omega) (by omega)
    simp only [List.nil_append] at hm
    obtain ⟨hLk, hLin'⟩ := memL_append.mp hm
    set σ := clEσ rd eP n D with hσ
    have hgn : gen ^ n ≠ 1 := fun h => (Nat.pos_iff_ne_zero.mp hn0) ((gen_pow_eq_one_iff (by omega)).mp h)
    have h3ne : σ (.n (val% «claim_list_digest» "s1#1")) ≠ 0 := by
      show gen ^ n + word 1 0 ≠ 0
      rw [word_one, Ne, e_add_eq_zero_iff]; exact hgn
    have hb : (if σ (.n (val% «claim_list_digest» "s1#1")) = 0 then walk σ cl23Zero else walk σ cl23Else) =
        .fall (cl23Else.flatMap (Main.slEvs σ)) := by
      simp only [h3ne, ↓reduceIte]; exact walk_straight_fall σ _ cl23Else_straight
    have hw := walk_ite σ clTail clTail_straight (.n (val% «claim_list_digest» "s1#1")) cl23Zero cl23Else [.n (val% «claim_list_digest» "s3#0"), .n (val% «claim_list_digest» "s3#0[1]")] _ hb
      clHead clHead_straight
    rw [← cl_body] at hw
    set es := clHead.flatMap (Main.slEvs σ) ++ .inK (.n (val% «claim_list_digest» "s1#1")) ::
      (cl23Else.flatMap (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ)) with hes
    have hev : ∀ e ∈ es, e.Holds rd σ := by
      intro e he
      simp only [hes, cl23Else_eq, clHead, clTail, clSplitS, clChainS, List.flatMap_cons, List.flatMap_nil,
        Main.slEvs, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show σ (.n (val% «claim_list_digest» "s1#0")) = word 1 0; rfl
      · show σ (.n (val% «claim_list_digest» "s1#1")) = σ (.n (val% «claim_list_digest» "n_g")) + σ (.n (val% «claim_list_digest» "s1#0")); rfl
      · show IsInK (gen ^ n + word 1 0)
        rw [word_one, ← pow_zero gen]; exact gen_pow_add_isInK _ _
      · trivial
      · trivial
      · show σ (.n (val% «claim_list_digest» "digest[0]")) = σ (.n (val% «claim_list_digest» "d0")); rfl
      · show σ (.n (val% «claim_list_digest» "digest[1]")) = σ (.n (val% «claim_list_digest» "d1")); rfl
      · obtain ⟨t, ht⟩ := Sig.load_gpow hlow hn
        rw [← gen_pow_eq_ofK] at ht
        show LoadHolds rd (gen ^ n) 0 (rdAt rd (gen ^ n) 0)
        exact load_of_rdAt rfl ht.1 (by rw [ht.2]; rfl)
      · show σ (.n (val% «claim_list_digest» "s3#0")) = σ (.n (val% «claim_list_digest» "digest[0]")); rfl
      · show σ (.n (val% «claim_list_digest» "s3#0[1]")) = σ (.n (val% «claim_list_digest» "digest[1]")); rfl
    have hal : allocs σ es = [] := by simp [hes, cl23Else_eq, clHead, clTail, clSplitS, clChainS, allocs, Main.slEvs, Ev.alloc?]
    have hcalls : calls es = clCalls n σ := by
      simp only [clCalls, Nat.pos_iff_ne_zero.mp hn0, ↓reduceIte]
      simp only [hes, cl23Else_eq, clHead, clTail, clSplitS, clChainS, List.flatMap_cons, List.flatMap_nil,
        Main.slEvs, List.cons_append, List.nil_append, List.append_nil]
      rfl
    have h := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
      (R := RegionL Lin) (D := RegionL []) (fp := fp) (N := Nk)
      (args := [gen ^ eP, gen ^ n]) (rets := digestCells D)
      (Dk := fun i => (fun _ => False) i ∨ outRegion ks [o1, o2] i)
      coreProgram_wf find_claim_list_digest (Or.inl cl_loop) rfl hw rfl hev
      (by
        rw [hal]
        simp only [hes, cl23Else_eq, clHead, clTail, clSplitS, clChainS, List.flatMap_cons, List.flatMap_nil,
          Main.slEvs, List.cons_append, List.nil_append, List.append_nil]
        rfl)
      (fun q hq => by simp [hes, cl23Else_eq, clHead, clTail, clSplitS, clChainS, addrs, Main.slEvs, Ev.addr?] at hq)
      (clTs n) ?_ ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
    · have h' := relAtInT_nodeHonest (Q := clQ n) (cs := clCalls n) (bs := clBufs n) h
        find_claim_list_digest hw ⟨rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩ hcalls (by rw [hal]; rfl)
        (by simp [clCalls, clTs, Nat.pos_iff_ne_zero.mp hn0])
      rw [hal] at h'
      simpa using h'
    · rw [hcalls, hal]
      simp only [clCalls, Nat.pos_iff_ne_zero.mp hn0, ↓reduceIte, List.sum_nil, Nat.add_zero]
      refine hKids rd σ _ _ _ ?_ hlow hLk ?_ (regionsOk_of fun k hk _ i hi => ?_)
      · refine ⟨rfl, rfl, fun _ => ⟨rfl, ?_⟩, rfl, rfl, fun _ => ⟨rfl, ?_⟩, trivial⟩
        · rw [(h1 rfl).1]; rfl
        · rw [(h2 rfl).1]; rfl
      · intro q hq
        simp only [Kid.lins, ks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.nil_append] at hq
        exact hLin' q hq
      · simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl
        · obtain ⟨q, hq, -⟩ := hi; simp at hq
        · exact Or.inl (Or.inl hi)
    · intro A hA
      simp [hes, cl23Else_eq, clHead, clTail, clSplitS, clChainS, loadAddrs, Main.slEvs, Ev.loadAddr?] at hA

/-- **`claim_list_digest` is complete, placed**: `n < 136 · 2^20` claims' cells at `g^eP` among the caller's words;
it returns their digest's cells. -/
theorem claim_list_digest_completeAt (fs : String → ℕ) (cert : String → V → ℕ) {Lin : Main.Layout}
    {eP n : ℕ} {cells : List E} (hn : n < 2 ^ 23) (hl : cells.length = 4 * n)
    (hLe : ∀ rd, MemL rd Lin → ReadsAt rd (gen ^ eP) cells) :
    CompleteAtD fs cert 23 "claim_list_digest" Lin [gen ^ eP, gen ^ n]
      (Returns (digestCells (keccak256 (cellsBytes cells)))) :=
  (claim_list_digest_completeAtT fs cert hn hl hLe).toD

end
end LeanVM.Guest.B1.Digest
