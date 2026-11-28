module

public import LeanVM.Guest.Complete.Claims.MonoAt
public import LeanVM.Guest.Complete.Claims.Digest
public import LeanVM.Guest.B1.Digest.ChildDigest
public import LeanVM.Guest.B1.Digest.ClaimListCChk
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«child_claim_list_digest»

/-!
# `child_claim_list_digest`, placed

The body is a branch on `n = 0` (`ccd_body`). The empty list's arm hashes the empty string
(`ccz_core`). The nonempty list's arm calls `list_split`, hints `child_mono` (`ccHint mono`: `g`
for the gap walk, `g^0` for the walk by hinted indices, as `Prover.childSlotPushes` pushes it) and
branches on `child_mono + g` to `child_claim_list_mono` or `child_claim_list_any` (`ccF mono`).

* `ccd0_callAtA`: the empty list, a node with no callee, popping nothing.
* `ccdNe_callAtA`: the nonempty list, given its arm completing at its position popping `P`: the
  node pops the split, the hint, then `P` (`ccPops`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-! ## The body -/

/-- The head of `child_claim_list_digest`'s body: `n_g + 1`. -/
def ccdHead : List Stmt := [.atom (.const (.n (val% «child_claim_list_digest» "s1#0")) (word 1 0)), .atom (.add (.n (val% «child_claim_list_digest» "s1#1")) (.n (val% «child_claim_list_digest» "n_g")) (.n (val% «child_claim_list_digest» "s1#0")))]

/-- The final copies of `child_claim_list_digest`. -/
def ccdTail : List Stmt := [.atom (.copy (.n (val% «child_claim_list_digest» "s2#0")) (.n (val% «child_claim_list_digest» "digest[0]"))), .atom (.copy (.n (val% «child_claim_list_digest» "s2#0[1]")) (.n (val% «child_claim_list_digest» "digest[1]")))]

/-- The nonempty arm before its branch: `list_split`, the hint `child_mono`, `child_mono + g`. -/
def ccE4 : List Stmt :=
  [.call "list_split" [.n (val% «child_claim_list_digest» "n_g")] [.n (val% «child_claim_list_digest» "bigs"), .n (val% «child_claim_list_digest» "groups"), .n (val% «child_claim_list_digest» "rest")],
    .atom (.hint (.witness "child_mono" (.stack [.n (val% «child_claim_list_digest» "mono")]))),
    .atom (.const (.n (val% «child_claim_list_digest» "s1.e.s2#0")) (word 2 0)), .atom (.add (.n (val% «child_claim_list_digest» "s1.e.s2#1")) (.n (val% «child_claim_list_digest» "mono")) (.n (val% «child_claim_list_digest» "s1.e.s2#0")))]

/-- The walks' arguments in `child_claim_list_digest`. -/
def ccArgsV : List V := [.n (val% «child_claim_list_digest» "entries_ptr"), .n (val% «child_claim_list_digest» "region"), .n (val% «child_claim_list_digest» "base"), .n (val% «child_claim_list_digest» "limit_g"), .n (val% «child_claim_list_digest» "bigs"), .n (val% «child_claim_list_digest» "groups"), .n (val% «child_claim_list_digest» "rest")]

/-- The gap walk's arm. -/
def ccMonoArm : List Stmt :=
  [.call "child_claim_list_mono" ccArgsV [.n (val% «child_claim_list_digest» "d0@1"), .n (val% «child_claim_list_digest» "d1@1")],
    .atom (.copy (.n (val% «child_claim_list_digest» "digest[0]")) (.n (val% «child_claim_list_digest» "d0@1"))), .atom (.copy (.n (val% «child_claim_list_digest» "digest[1]")) (.n (val% «child_claim_list_digest» "d1@1")))]

/-- The walk by hinted indices' arm. -/
def ccAnyArm : List Stmt :=
  [.call "child_claim_list_any" ccArgsV [.n (val% «child_claim_list_digest» "d0@2"), .n (val% «child_claim_list_digest» "d1@2")],
    .atom (.copy (.n (val% «child_claim_list_digest» "digest[0]")) (.n (val% «child_claim_list_digest» "d0@2"))), .atom (.copy (.n (val% «child_claim_list_digest» "digest[1]")) (.n (val% «child_claim_list_digest» "d1@2")))]

/-- The nonempty arm. -/
def ccElse : List Stmt := ccE4 ++ [.ite (.n (val% «child_claim_list_digest» "s1.e.s2#1")) ccMonoArm ccAnyArm]

/-- The returned words. -/
def ccVs : List V := [.n (val% «child_claim_list_digest» "s2#0"), .n (val% «child_claim_list_digest» "s2#0[1]")]

theorem ccd_body : Fn.body fn% «child_claim_list_digest» =
    ccdHead ++ .ite (.n (val% «child_claim_list_digest» "s1#1")) cc25Zero ccElse :: (ccdTail ++ [.ret ccVs]) := by
  rw [child_claim_list_digest_shape]; rfl

set_option maxRecDepth 100000 in
theorem cc25Zero_straight : cc25Zero.all Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cc25Zero_parts : cc25Zero.filterMap Stmt.allocSz = [] ∧ cc25Zero.filterMap Stmt.addrS = [] ∧
    cc25Zero.filterMap Stmt.callS = [] ∧ cc25Zero.filterMap stmtLoad? = [] ∧ cc25Zero.all isAtomS = true ∧
    Stmt.noWitList cc25Zero = true ∧ cc25Zero.all noHeapHintC = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ccd_loop : coreProgram.loop "child_claim_list_digest" = false := by
  rw [Program.loop_of_find? find_child_claim_list_digest]; decide +kernel

set_option maxRecDepth 100000 in
theorem child_claim_list_digest_exact : ExactFreeG "child_claim_list_digest" :=
  exactFreeG_of (j := idx% «child_claim_list_digest») (by decide +kernel)

/-- A straight run, then a branch between straight arms, falls through. -/
theorem walk_pre_ite (σ : Val) (z n : List Stmt) (hz : z.all Stmt.straight = true)
    (hn : n.all Stmt.straight = true) (c : V) : ∀ pre : List Stmt,
    pre.all Stmt.straight = true →
    walk σ (pre ++ [.ite c z n]) =
      .fall (pre.flatMap (slEvs σ) ++ .inK c :: (if σ c = 0 then z else n).flatMap (slEvs σ))
  | [], _ => by
    rw [List.nil_append, walk, walk1, walk]
    by_cases h : σ c = 0
    · simp only [h, ↓reduceIte, walk_straight_fall σ z hz, Out.pre, Out.seq, List.flatMap_nil,
        List.nil_append, List.append_nil, List.singleton_append]
    · simp only [h, ↓reduceIte, walk_straight_fall σ n hn, Out.pre, Out.seq, List.flatMap_nil,
        List.nil_append, List.append_nil, List.singleton_append]
  | s :: pre, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.cons_append, walk, walk_pre_ite σ z n hz hn c pre h.2, walk1_straight σ s h.1,
      Out.seq, Out.pre, List.flatMap_cons, List.append_assoc]

/-! ## The empty list -/

/-- The empty list's run, evaluated. -/
noncomputable def ccZEval : List Stmt := ccdHead ++ cc25Zero ++ fillH 15 25 ++ ccdTail

/-- **The empty list's run, evaluated**: in order, no store, no side condition. -/
noncomputable def cczOk : Bool :=
  (chk 5 ccZEval).isSome && (storesOf 5 ccZEval).isEmpty &&
    (atomsIn ccZEval).all (fun a => !needsSide a)

set_option maxRecDepth 100000 in
theorem ccz_ok : cczOk = true := by decide +kernel

/-- The empty list's valuation. -/
noncomputable def cczσ (rd : Reader) (args : List E) : Val :=
  B1.Val.ofArgs (ev rd (fun _ => 0) args ccZEval)

set_option maxRecDepth 20000 in
/-- **The empty list's valuation**: its atoms hold, it returns the empty string's digest. -/
theorem ccz_core {rd : Reader} (entries region base limit : E) :
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

/-- The empty list's events. -/
noncomputable def ccZEs (σ : Val) : List Ev :=
  ccdHead.flatMap (slEvs σ) ++ .inK (.n (val% «child_claim_list_digest» "s1#1")) ::
    (cc25Zero.flatMap (slEvs σ) ++ ccdTail.flatMap (slEvs σ))

theorem ccZEs_congr (σ σ' : Val) : ccZEs σ = ccZEs σ' := by
  have hZ : cc25Zero.flatMap (slEvs σ) = cc25Zero.flatMap (slEvs σ') := slEvs_congr cc25Zero fun c f a hm => by
    have := List.all_eq_true.mp cc25Zero_parts.2.2.2.2.1 _ hm
    simp [isAtomS] at this
  rw [ccZEs, ccZEs, hZ]; rfl

theorem ccZEs_parts (σ : Val) : allocs σ (ccZEs σ) = [] ∧ allocDsts (ccZEs σ) = [] ∧ addrs (ccZEs σ) = [] ∧
    calls (ccZEs σ) = [] ∧ loadAddrs σ (ccZEs σ) = [] ∧ heapHintAddrs σ (ccZEs σ) = [] ∧
    ∀ e ∈ ccZEs σ, e.noWit := by
  obtain ⟨z1, z2, z3, z4, -, z6, z7⟩ := cc25Zero_parts
  obtain ⟨hzd, hza, hzad, hzc⟩ := straight_parts σ _ cc25Zero_straight
  have hlz := Memory.loadAddrs_straight σ _ cc25Zero_straight
  have hhz := heapHintAddrs_nil_of (σ := σ) (pre := cc25Zero) z7
  have hnw : ∀ e ∈ cc25Zero.flatMap (slEvs σ), e.noWit := by
    have h := walk_noWit (σ := σ) cc25Zero z6
    rw [walk_straight_fall σ _ cc25Zero_straight] at h
    exact h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ccZEs, allocs, List.filterMap_append, List.filterMap_cons, Ev.alloc?] at hza ⊢
    rw [hza, z1]; rfl
  · simp only [ccZEs, allocDsts, List.filterMap_append, List.filterMap_cons, Ev.allocDst?] at hzd ⊢
    rw [hzd, z1]; rfl
  · simp only [ccZEs, addrs, List.filterMap_append, List.filterMap_cons, Ev.addr?] at hzad ⊢
    rw [hzad, z2]; simp [ccdHead, ccdTail, slEvs, Ev.addr?]
  · simp only [ccZEs, calls, List.filterMap_append, List.filterMap_cons, Ev.call?] at hzc ⊢
    rw [hzc, z3]; rfl
  · simp only [ccZEs, loadAddrs, List.filterMap_append, List.filterMap_cons, Ev.loadAddr?]
    simp only [loadAddrs] at hlz
    rw [hlz, z4]; simp [ccdHead, ccdTail, slEvs, Ev.loadAddr?]
  · simp only [ccZEs, heapHintAddrs, List.flatMap_append, List.flatMap_cons]
    simp only [heapHintAddrs] at hhz
    rw [hhz]; simp [ccdHead, ccdTail, slEvs, Ev.hintAddrs]
  · intro e he
    simp only [ccZEs, List.mem_append, List.mem_cons] at he
    rcases he with he | rfl | he | he
    · simp only [ccdHead, List.flatMap_cons, List.flatMap_nil, slEvs, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> rfl
    · trivial
    · exact hnw e he
    · simp only [ccdTail, List.flatMap_cons, List.flatMap_nil, slEvs, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- **The empty list completes placed**: a node with no callee, popping nothing. -/
theorem ccd0_callAtA {k : ℕ} {eP rg L : ℕ} {base : E} {R : ℕ → Prop} {Pre : Reader → Prop} {fp c : ℕ}
    (hfc : fp + fs "child_claim_list_digest" ≤ c) :
    CallAtA fs al cert k "child_claim_list_digest" [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ 0]
      (digestCells (keccak256 (cellsBytes []))) R (fun _ => False) (fun _ => True) Pre
      (fun rd t => t.pops coreProgram rd = []) (fs "child_claim_list_digest") fp c c := by
  set σ0 := cczσ (fun _ => none) [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ 0] with hσ0
  obtain ⟨hal0, hd0, ha0, hc0, -, -, -⟩ := ccZEs_parts σ0
  have hes : ∀ σ, ccZEs σ = ccZEs σ0 := fun σ => ccZEs_congr σ σ0
  refine callAtA_nodeRd ccd_loop hfc ⟨σ0, fn% «child_claim_list_digest», ccZEs σ0, ccVs, [], [], fun _ => True,
    fun _ => False, find_child_claim_list_digest, by rw [hal0]; exact ⟨by simp, List.Pairwise.nil⟩,
    fun i hi => hi.elim, ?_, fun _ _ => trivial, ?_⟩
  · rw [hc0, hal0, List.sum_nil, Nat.add_zero, KidsAtF]
    exact ⟨rfl, fun _ _ => trivial, fun _ h => h⟩
  intro rd hl hp _
  obtain ⟨hat, hpar, h60, h6, hret⟩ := ccz_core (rd := rd) (gen ^ eP) (gen ^ rg) base (gen ^ L)
  set σ := cczσ rd [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ 0] with hσ
  obtain ⟨hal, hd, ha, hc, hlo, hhi, hnw⟩ := ccZEs_parts σ
  have hb : (if σ (.n (val% «child_claim_list_digest» "s1#1")) = 0 then walk σ cc25Zero else walk σ ccElse) =
      .fall (cc25Zero.flatMap (slEvs σ)) := by
    simp only [h60, ↓reduceIte]; exact walk_straight_fall σ _ cc25Zero_straight
  have hw := walk_ite σ ccdTail rfl (.n (val% «child_claim_list_digest» "s1#1")) cc25Zero ccElse ccVs _ hb ccdHead rfl
  rw [← ccd_body] at hw
  have hw' : walk σ (Fn.body fn% «child_claim_list_digest») = .ret (ccZEs σ0) ccVs := by rw [hw, ← hes σ]; rfl
  have hmZ : ∀ s ∈ ccdHead ++ cc25Zero ++ ccdTail, ∀ a, s = .atom a → a.Holds rd σ := by
    intro s hs a rfl
    refine hat a (cl_mem_atoms ?_)
    unfold ccZEval
    simp only [List.mem_append] at hs ⊢
    rcases hs with (hs | hs) | hs
    · exact Or.inl (Or.inl (Or.inl hs))
    · exact Or.inl (Or.inl (Or.inr hs))
    · exact Or.inr hs
  have hH : ∀ s ∈ ccdHead, isAtomS s = true := by decide
  have hT : ∀ s ∈ ccdTail, isAtomS s = true := by decide
  refine ⟨σ, hpar, hw', hret, by rw [hal0, ← hes σ, hal], ?_, fun _ h => by rw [hc0] at h; simp at h, ?_, ?_, ?_, ?_⟩
  · rw [hal0]; exact ⟨by rw [hd0]; rfl, fun q hq => by rw [ha0] at hq; simp at hq⟩
  · intro A hA; rw [← hes σ, hlo] at hA; simp at hA
  · intro A hA; rw [← hes σ, hhi] at hA; simp at hA
  · intro ev hev
    rw [← hes σ] at hev
    simp only [ccZEs] at hev
    rcases List.mem_append.mp hev with he | he
    · exact events_straight (fun s hs => sOk_atomS (hH s hs) (hmZ s (by simp [hs]))) ev he
    rcases List.mem_cons.mp he with rfl | he
    · show IsInK (σ (.n (val% «child_claim_list_digest» "s1#1"))); rw [h6]; exact gen_pow_add_isInK 0 0
    rcases List.mem_append.mp he with he | he
    · exact events_straight (fun s hs => sOk_atomS (List.all_eq_true.mp cc25Zero_parts.2.2.2.2.1 s hs)
        (hmZ s (by simp [hs]))) ev he
    · exact events_straight (fun s hs => sOk_atomS (hT s hs) (hmZ s (by simp [hs]))) ev he
  · intro ts hv _
    rw [hc0] at hv
    have hts : ts = [] := by
      cases ts with
      | nil => rfl
      | cons _ _ => exact hv.elim
    subst hts
    rw [Tree.pops, events_node find_child_claim_list_digest hw', Tree.popsKids, ← hes σ,
      splice_mute _ _ (fun e he => ?_) (by rw [hc]; rfl)]
    · rfl
    · have := hnw e he
      cases e with
      | atom a =>
        cases a with
        | hint x => cases x <;> simp_all [Ev.noWit, atomNoWit, Ev.pops, Atom.pops, Hint.pops]
        | _ => rfl
      | _ => rfl

/-! ## The nonempty list -/

/-- The walk the hint picks. -/
def ccF (mono : Bool) : String := if mono then "child_claim_list_mono" else "child_claim_list_any"

/-- The hint `child_mono`: `g` for the gap walk, `g^0` for the walk by hinted indices. -/
noncomputable def ccHint (mono : Bool) : E := gen ^ (if mono then 1 else 0)

/-- The arm's returned words. -/
def ccD (mono : Bool) : List V :=
  if mono then [.n (val% «child_claim_list_digest» "d0@1"), .n (val% «child_claim_list_digest» "d1@1")]
  else [.n (val% «child_claim_list_digest» "d0@2"), .n (val% «child_claim_list_digest» "d1@2")]

/-- The nonempty list's valuation. -/
noncomputable def ccEσ (mono : Bool) (eP rg L n : ℕ) (base : E) (D : Digest) : Val :=
  B1.Val.ofArgs [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ n, word 1 0, gen ^ n + word 1 0,
    0, 0, 0, 0, 0, 0, (digestHalves D).1, (digestHalves D).2,
    gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17), ccHint mono, word 2 0, ccHint mono + word 2 0,
    (digestHalves D).1, (digestHalves D).2, (digestHalves D).1, (digestHalves D).2,
    (digestHalves D).1, (digestHalves D).2]

/-- The nonempty list's events. -/
def ccEs (mono : Bool) : List Ev :=
  [.atom (.const (.n (val% «child_claim_list_digest» "s1#0")) (word 1 0)),
    .atom (.add (.n (val% «child_claim_list_digest» "s1#1")) (.n (val% «child_claim_list_digest» "n_g")) (.n (val% «child_claim_list_digest» "s1#0"))),
    .inK (.n (val% «child_claim_list_digest» "s1#1")),
    .call "list_split" [.n (val% «child_claim_list_digest» "n_g")] [.n (val% «child_claim_list_digest» "bigs"), .n (val% «child_claim_list_digest» "groups"), .n (val% «child_claim_list_digest» "rest")],
    .atom (.hint (.witness "child_mono" (.stack [.n (val% «child_claim_list_digest» "mono")]))),
    .atom (.const (.n (val% «child_claim_list_digest» "s1.e.s2#0")) (word 2 0)),
    .atom (.add (.n (val% «child_claim_list_digest» "s1.e.s2#1")) (.n (val% «child_claim_list_digest» "mono")) (.n (val% «child_claim_list_digest» "s1.e.s2#0"))),
    .inK (.n (val% «child_claim_list_digest» "s1.e.s2#1")),
    .call (ccF mono) ccArgsV (ccD mono),
    .atom (.copy (.n (val% «child_claim_list_digest» "digest[0]")) ((ccD mono).getD 0 (.n 0))),
    .atom (.copy (.n (val% «child_claim_list_digest» "digest[1]")) ((ccD mono).getD 1 (.n 0))),
    .atom (.copy (.n (val% «child_claim_list_digest» "s2#0")) (.n (val% «child_claim_list_digest» "digest[0]"))),
    .atom (.copy (.n (val% «child_claim_list_digest» "s2#0[1]")) (.n (val% «child_claim_list_digest» "digest[1]")))]

/-- The nonempty list's calls. -/
def ccCalls (mono : Bool) : List Call :=
  [⟨"list_split", [.n (val% «child_claim_list_digest» "n_g")], [.n (val% «child_claim_list_digest» "bigs"), .n (val% «child_claim_list_digest» "groups"), .n (val% «child_claim_list_digest» "rest")], true⟩,
    ⟨ccF mono, ccArgsV, ccD mono, true⟩]

theorem ccEs_calls (mono : Bool) : calls (ccEs mono) = ccCalls mono := by cases mono <;> rfl

theorem ccEs_parts (mono : Bool) (σ : Val) : allocs σ (ccEs mono) = [] ∧ allocDsts (ccEs mono) = [] ∧
    addrs (ccEs mono) = [] ∧ loadAddrs σ (ccEs mono) = [] ∧ heapHintAddrs σ (ccEs mono) = [] := by
  cases mono <;> simp [ccEs, allocs, allocDsts, addrs, loadAddrs, heapHintAddrs, Ev.alloc?, Ev.allocDst?, Ev.addr?,
    Ev.loadAddr?, Ev.hintAddrs, hintDest?, destHeap?]

theorem ccHint_branch (mono : Bool) : (ccHint mono + word 2 0 = 0) ↔ mono = true := by
  rw [word_gen, ccHint]
  cases mono
  · simp only [Bool.false_eq_true, ↓reduceIte, pow_zero, iff_false]
    rw [e_add_eq_zero_iff]
    intro h
    exact absurd ((gen_pow_eq_one_iff (a := 1) (by norm_num)).mp (by rw [pow_one]; exact h.symm)) (by norm_num)
  · simp only [↓reduceIte, pow_one, iff_true]
    exact e_add_eq_zero_iff.mpr rfl

set_option maxRecDepth 20000 in
theorem ccEs_walk (mono : Bool) {eP rg L n : ℕ} {base : E} {D : Digest} (hn0 : n ≠ 0) (hn : n < 2 ^ 19) :
    walk (ccEσ mono eP rg L n base D) (Fn.body fn% «child_claim_list_digest») = .ret (ccEs mono) ccVs := by
  set σ := ccEσ mono eP rg L n base D
  have hgn : gen ^ n ≠ 1 := fun h => hn0 ((gen_pow_eq_one_iff (by omega)).mp h)
  have h6ne : σ (.n (val% «child_claim_list_digest» "s1#1")) ≠ 0 := by
    show gen ^ n + word 1 0 ≠ 0
    rw [word_one, Ne, e_add_eq_zero_iff]; exact hgn
  have h31 : σ (.n (val% «child_claim_list_digest» "s1.e.s2#1")) = ccHint mono + word 2 0 := rfl
  have hb : (if σ (.n (val% «child_claim_list_digest» "s1#1")) = 0 then walk σ cc25Zero else walk σ ccElse) =
      .fall (ccE4.flatMap (slEvs σ) ++ .inK (.n (val% «child_claim_list_digest» "s1.e.s2#1")) ::
        (if mono then ccMonoArm else ccAnyArm).flatMap (slEvs σ)) := by
    simp only [h6ne, ↓reduceIte]
    rw [ccElse, walk_pre_ite σ ccMonoArm ccAnyArm rfl rfl (.n (val% «child_claim_list_digest» "s1.e.s2#1")) ccE4 rfl]
    cases mono
    · have : σ (.n (val% «child_claim_list_digest» "s1.e.s2#1")) ≠ 0 := by
        rw [h31]; exact fun h => absurd ((ccHint_branch false).mp h) (by simp)
      simp [this]
    · have : σ (.n (val% «child_claim_list_digest» "s1.e.s2#1")) = 0 := by
        rw [h31]; exact (ccHint_branch true).mpr rfl
      simp [this]
  have hw := walk_ite σ ccdTail rfl (.n (val% «child_claim_list_digest» "s1#1")) cc25Zero ccElse ccVs _ hb ccdHead rfl
  rw [← ccd_body] at hw
  rw [hw]
  cases mono <;> rfl

/-- The nonempty list's pops: the split, the hint, the walk's. -/
noncomputable def ccPops (mono : Bool) (n : ℕ) (P : List Pop) : List Pop :=
  ("signers_split", [gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)]) :: ("child_mono", [ccHint mono]) :: P

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- **The nonempty list completes placed**, given its walk completing at its position popping `P`,
ending at `armE`: the node pops the split, the hint, then `P`. -/
theorem ccdNe_callAtA (hwf : coreProgram.Wf) {k : ℕ} (hk : 17 ≤ k) (mono : Bool) {eP rg L n : ℕ} {base : E}
    {D : Digest} (hn0 : n ≠ 0) (hn : n < 2 ^ 19) {R : ℕ → Prop} {Pre : Reader → Prop} {P : List Pop}
    {armE : ℕ → ℕ}
    (hArm : ∀ fpA cA, fpA + fs (ccF mono) ≤ cA → CallAtA fs al cert k (ccF mono) (anyArgs eP rg base L n)
      (digestCells D) R (fun _ => False) (fun _ => True) Pre (fun rd t => t.pops coreProgram rd = P)
      (fs (ccF mono)) fpA cA (armE cA))
    {fp c : ℕ} (hfc : fp + fs "child_claim_list_digest" ≤ c) :
    CallAtA fs al cert k "child_claim_list_digest" [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ n]
      (digestCells D) R (fun _ => False) (fun _ => True) Pre (fun rd t => t.pops coreProgram rd = ccPops mono n P)
      (fs "child_claim_list_digest") fp c
      (armE (allocBase (al (ccF mono)) (allocBase (al "list_split") c + fs "list_split") + fs (ccF mono))) := by
  set σ0 := ccEσ mono eP rg L n base D with hσ0
  obtain ⟨hal0, hd0, ha0, hlo0, hhi0⟩ := ccEs_parts mono σ0
  set c1 := allocBase (al "list_split") c + fs "list_split" with hc1
  set fA := allocBase (al (ccF mono)) c1 with hfA
  refine callAtA_nodeRd ccd_loop hfc ⟨σ0, fn% «child_claim_list_digest», ccEs mono, ccVs, [],
    [fun _ _ => True, fun rd t => t.pops coreProgram rd = P], fun _ => True, fun _ => False,
    find_child_claim_list_digest, by rw [hal0]; exact ⟨by simp, List.Pairwise.nil⟩,
    fun i hi => hi.elim, ?_, fun _ _ => trivial, ?_⟩
  · rw [ccEs_calls, hal0, List.sum_nil, Nat.add_zero, ccCalls, KidsAtF]
    simp only [↓reduceIte, List.map_cons, List.map_nil, List.headD_cons, List.tail_cons]
    refine ⟨fs "list_split", c1, R, fun _ => False, fun _ => True,
      fun i hi => Or.inl (Or.inl hi), list_split_callAtA hwf hk hn _ _, ?_⟩
    rw [KidsAtF]
    simp only [↓reduceIte, List.headD_cons, List.tail_cons]
    refine ⟨fs (ccF mono), armE (fA + fs (ccF mono)), R, fun _ => False, fun _ => True,
      fun i hi => Or.inl (Or.inl hi), ?_, ?_⟩
    · have h := hArm fA (fA + fs (ccF mono)) le_rfl
      have ha : ccArgsV.map σ0 = anyArgs eP rg base L n := rfl
      have hr : (ccD mono).map σ0 = digestCells D := by cases mono <;> rfl
      rw [ha, hr]
      exact h.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ h => h.1) (fun _ _ _ h => h)
    · rw [KidsAtF]; exact ⟨rfl, fun _ _ => trivial, fun _ h => h.elim⟩
  intro rd hl' hp _
  have hw := ccEs_walk mono (eP := eP) (rg := rg) (L := L) (base := base) (D := D) hn0 hn
  refine ⟨σ0, rfl, hw, ?_, rfl, ?_, fun c' _ => ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · show [(digestHalves D).1, (digestHalves D).2] = digestCells D; rfl
  · rw [hal0]; exact ⟨by rw [hd0]; rfl, fun q hq => by rw [ha0] at hq; simp at hq⟩
  · intro A hA; rw [hlo0] at hA; simp at hA
  · intro A hA; rw [hhi0] at hA; simp at hA
  · intro ev hev
    have hK : IsInK (ccHint mono + word 2 0) := by
      rw [word_gen, ccHint, ← pow_one gen]; exact gen_pow_add_isInK _ 1
    have hK1 : IsInK (gen ^ n + word 1 0) := by
      rw [word_one, ← pow_zero gen]; exact gen_pow_add_isInK _ _
    cases mono
    all_goals
      simp only [ccEs, ccD, List.mem_cons, List.not_mem_nil, or_false] at hev
      rcases hev with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact rfl | trivial
  · intro ts hv hq
    rw [ccEs_calls] at hv hq
    obtain ⟨t1, t2, rfl⟩ : ∃ t1 t2, ts = [t1, t2] := by
      have := kidsValid_len hv
      simp only [ccCalls, List.length_cons, List.length_nil] at this
      match ts, this with
      | [t1, t2], _ => exact ⟨t1, t2, rfl⟩
    have hv' := hv
    simp only [ccCalls, Tree.KidsValid, ↓reduceIte] at hv'
    obtain ⟨hn1, hv1, -⟩ := hv'
    simp only [ccCalls] at hq
    rw [kidsPost_cons, kidsPost_cons] at hq
    have h1 := list_split_pops hn1 hv1
    have h2 := hq.2.1 rfl
    rw [Tree.pops, events_node find_child_claim_list_digest hw, Tree.popsKids, Tree.popsKids, Tree.popsKids, h1, h2]
    have hm : σ0 (.n (val% «child_claim_list_digest» "mono")) = ccHint mono := rfl
    cases mono
    all_goals
      simp only [ccEs, ccD, splice, Atom.pops, Hint.pops, Dest.words, List.map_cons, List.map_nil, ↓reduceIte,
        List.headD_cons, List.tail_cons, List.nil_append, List.cons_append, List.append_nil, ccPops, hm]
      rfl

end
end LeanVM.Guest.Complete
