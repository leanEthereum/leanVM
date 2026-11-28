module

public import LeanVM.Guest.Complete.Claims.Chain
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«claim_list_digest»

/-!
# `claim_list_digest`, placed

`digest_callAtA`: `claim_list_digest` at `(fp, c)` on `n < 2^19` claims' cells at `e` in the region:
the empty list's branch (no callee), or `list_split` then `claim_list_chain` after its frame; its
tree of honest shape (`NodeHonest … clQ clCalls clBufs clTs`), so its pops are the split's, then the
claims' (`cl_valid_pops`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.Value.Keccak LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- `claim_list_digest`'s honest shape on `n` claims. -/
def clHonest (n : ℕ) : Tree → Prop :=
  NodeHonest coreProgram "claim_list_digest" (clQ n) (clCalls n) (clBufs n) (clTs n)

/-- `claim_list_digest`'s end at `(fp, c)` on `n` claims. -/
def clEnd (fs : String → ℕ) (al : String → Bool) (n c : ℕ) : ℕ :=
  if n = 0 then c else
    chEnd fs al n (allocBase (al "claim_list_chain") (allocBase (al "list_split") c + fs "list_split") +
      fs "claim_list_chain")

theorem noCallIf_congr {σ σ' : Val} {P : List Stmt} (h : P.all (fun s => match s with
    | .callIf .. => false | _ => true) = true) : P.flatMap (slEvs σ) = P.flatMap (slEvs σ') :=
  slEvs_congr P fun c f a hm => by have := List.all_eq_true.mp h _ hm; simp at this

/-! ## The nonempty list -/

/-- The nonempty list's path: its events, the same on every valuation. -/
noncomputable def clEs : List Ev :=
  clHead.flatMap (slEvs fun _ => 0) ++ .inK (.n (val% «claim_list_digest» "s1#1")) ::
    (cl23Else.flatMap (slEvs fun _ => 0) ++ clTail.flatMap (slEvs fun _ => 0))

/-- The nonempty list's returns. -/
def clVs : List V := [.n (val% «claim_list_digest» "s3#0"), .n (val% «claim_list_digest» "s3#0[1]")]

set_option maxRecDepth 20000 in
theorem clEs_eq : clEs = [.atom (.const (.n (val% «claim_list_digest» "s1#0")) (word 1 0)),
    .atom (.add (.n (val% «claim_list_digest» "s1#1")) (.n (val% «claim_list_digest» "n_g")) (.n (val% «claim_list_digest» "s1#0"))),
    .inK (.n (val% «claim_list_digest» "s1#1")),
    .call "list_split" [.n (val% «claim_list_digest» "n_g")] [.n (val% «claim_list_digest» "bigs"),
      .n (val% «claim_list_digest» "groups"), .n (val% «claim_list_digest» "rest")],
    .call "claim_list_chain" [.n (val% «claim_list_digest» "entries_ptr"), .n (val% «claim_list_digest» "n_g"),
      .n (val% «claim_list_digest» "bigs"), .n (val% «claim_list_digest» "groups"), .n (val% «claim_list_digest» "rest")]
      [.n (val% «claim_list_digest» "d0"), .n (val% «claim_list_digest» "d1")],
    .atom (.copy (.n (val% «claim_list_digest» "digest[0]")) (.n (val% «claim_list_digest» "d0"))),
    .atom (.copy (.n (val% «claim_list_digest» "digest[1]")) (.n (val% «claim_list_digest» "d1"))),
    .atom (.touch (.n (val% «claim_list_digest» "s2#0")) (.n (val% «claim_list_digest» "n_g"))),
    .atom (.copy (.n (val% «claim_list_digest» "s3#0")) (.n (val% «claim_list_digest» "digest[0]"))),
    .atom (.copy (.n (val% «claim_list_digest» "s3#0[1]")) (.n (val% «claim_list_digest» "digest[1]")))] := by
  rw [clEs, cl23Else_eq]
  rfl

theorem clEs_walk {e n : ℕ} {D : Digest} (hn0 : n ≠ 0) (hn : n < 2 ^ 19) (rd : Reader) :
    walk (clEσ rd e n D) (Fn.body fn% «claim_list_digest») = .ret clEs clVs := by
  have mH : clHead.all (fun s => match s with | .callIf .. => false | _ => true) = true := rfl
  have mTl : clTail.all (fun s => match s with | .callIf .. => false | _ => true) = true := rfl
  have mE : cl23Else.all (fun s => match s with | .callIf .. => false | _ => true) = true := by decide +kernel
  have hgn : gen ^ n ≠ 1 := fun h => hn0 ((gen_pow_eq_one_iff (by omega)).mp h)
  have h3ne : clEσ rd e n D (.n (val% «claim_list_digest» "s1#1")) ≠ 0 := by
    show gen ^ n + word 1 0 ≠ 0
    rw [word_one, Ne, e_add_eq_zero_iff]; exact hgn
  have hb : (if clEσ rd e n D (.n (val% «claim_list_digest» "s1#1")) = 0 then walk (clEσ rd e n D) cl23Zero
      else walk (clEσ rd e n D) cl23Else) = .fall (cl23Else.flatMap (slEvs (clEσ rd e n D))) := by
    simp only [h3ne, ↓reduceIte]; exact walk_straight_fall _ _ cl23Else_straight
  have := walk_ite (clEσ rd e n D) clTail clTail_straight (.n (val% «claim_list_digest» "s1#1")) cl23Zero
    cl23Else [.n (val% «claim_list_digest» "s3#0"), .n (val% «claim_list_digest» "s3#0[1]")] _ hb clHead
    clHead_straight
  rw [← cl_body] at this
  rw [this, clVs, clEs, noCallIf_congr (σ := clEσ rd e n D) (σ' := fun _ => 0) mH,
    noCallIf_congr (σ := clEσ rd e n D) (σ' := fun _ => 0) mE, noCallIf_congr (σ := clEσ rd e n D) (σ' := fun _ => 0) mTl]

theorem clEs_parts (σ : Val) : allocs σ clEs = [] ∧ allocDsts clEs = [] ∧ addrs clEs = [] ∧
    loadAddrs σ clEs = [] ∧ heapHintAddrs σ clEs = [] := by
  rw [clEs_eq]
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  simp [heapHintAddrs, Ev.hintAddrs]

theorem clEs_calls (n : ℕ) (hn0 : n ≠ 0) (σ : Val) : calls clEs = clCalls n σ := by
  rw [clEs_eq]
  simp only [clCalls, hn0, ↓reduceIte]
  rfl

theorem clEs_holds {e n : ℕ} {D : Digest} {rd : Reader} (ht : ∃ t, LoadHolds rd (gen ^ n) 0 t) :
    ∀ ev ∈ clEs, ev.Holds rd (clEσ rd e n D) := by
  intro ev hev
  rw [clEs_eq] at hev
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
  obtain ⟨t, ht⟩ := ht
  rcases hev with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show clEσ rd e n D (.n (val% «claim_list_digest» "s1#0")) = word 1 0; rfl
  · show clEσ rd e n D (.n (val% «claim_list_digest» "s1#1")) = clEσ rd e n D (.n (val% «claim_list_digest» "n_g")) +
      clEσ rd e n D (.n (val% «claim_list_digest» "s1#0")); rfl
  · show IsInK (gen ^ n + word 1 0)
    rw [word_one, ← pow_zero gen]; exact gen_pow_add_isInK _ _
  · trivial
  · trivial
  · show clEσ rd e n D (.n (val% «claim_list_digest» "digest[0]")) = clEσ rd e n D (.n (val% «claim_list_digest» "d0")); rfl
  · show clEσ rd e n D (.n (val% «claim_list_digest» "digest[1]")) = clEσ rd e n D (.n (val% «claim_list_digest» "d1")); rfl
  · show LoadHolds rd (gen ^ n) 0 (rdAt rd (gen ^ n) 0)
    exact load_of_rdAt rfl ht.1 (by rw [ht.2]; rfl)
  · show clEσ rd e n D (.n (val% «claim_list_digest» "s3#0")) = clEσ rd e n D (.n (val% «claim_list_digest» "digest[0]")); rfl
  · show clEσ rd e n D (.n (val% «claim_list_digest» "s3#0[1]")) = clEσ rd e n D (.n (val% «claim_list_digest» "digest[1]")); rfl

theorem clEσ_args (rd rd' : Reader) (e n : ℕ) (D : Digest) (cl : Call) (hcl : cl ∈ clCalls n (fun _ => 0)) :
    cl.args.map (clEσ rd e n D) = cl.args.map (clEσ rd' e n D) ∧ cl.rets.map (clEσ rd e n D) = cl.rets.map (clEσ rd' e n D) := by
  simp only [clCalls] at hcl
  split at hcl
  · simp at hcl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
    rcases hcl with rfl | rfl <;>
      simp only [clEσ, List.map_cons, List.map_nil, ofArgs_n, List.getD_cons_succ, List.getD_cons_zero, and_self]

set_option maxHeartbeats 600000 in
theorem digest_ne_kids (hwf : coreProgram.Wf) {k : ℕ} (hk : 17 ≤ k) {e n : ℕ} {cells : List E}
    (hn0 : n ≠ 0) (hn : n < 2 ^ 19) (hl : cells.length = 4 * n) {R : ℕ → Prop}
    (hR : ∀ i, e ≤ i → i < e + 4 * n → R i) {Pre : Reader → Prop} (hP : ∀ rd, Pre rd → ReadsAt rd (ptrAt e) cells)
    (hdef : ∀ rd, LowDef k rd → Pre rd → ∀ i, (i = n / 136 ∨ i = n % 136 / 17 ∨ i = n % 17 ∨ i = n) →
      ∃ t, LoadHolds rd (gen ^ i) 0 t) {D : Digest} (hD : D = keccak256 (cellsBytes cells)) (R' : ℕ → Prop)
    (hR' : ∀ i, R i → R' i) (c : ℕ) :
    KidsAtF fs al cert k (clEσ (fun _ => none) e n D) R' Pre (fun rd => HoldsWords rd []) (fun _ => False)
      [fun _ _ => True, fun _ t => chHonest n t] (clCalls n (fun _ => 0)) c
      (chEnd fs al n (allocBase (al "claim_list_chain") (allocBase (al "list_split") c + fs "list_split") +
        fs "claim_list_chain")) (fun _ => True) (fun _ => False) := by
  simp only [clCalls, hn0, ↓reduceIte]
  rw [KidsAtF]
  simp only [↓reduceIte, List.map_cons, List.map_nil, List.headD_cons, List.tail_cons]
  refine ⟨fs "list_split", allocBase (al "list_split") c + fs "list_split", R, fun _ => False, fun _ => True,
    fun i hi => Or.inl (hR' i hi), list_split_callAtA hwf hk hn _ _, ?_⟩
  rw [KidsAtF]
  simp only [↓reduceIte, List.map_cons, List.map_nil, List.headD_cons, List.tail_cons]
  refine ⟨fs "claim_list_chain", chEnd fs al n (allocBase (al "claim_list_chain")
    (allocBase (al "list_split") c + fs "list_split") + fs "claim_list_chain"), R, fun _ => False, fun _ => True,
    fun i hi => Or.inl (hR' i hi), ?_, ?_⟩
  · have h := chain_callAtA (fs := fs) (al := al) (cert := cert) hwf hn hl hR hP hdef
      (fp := allocBase (al "claim_list_chain") (allocBase (al "list_split") c + fs "list_split")) le_rfl
    rw [chArgs, ptrAt_eq_gpow, ← hD] at h
    have ha : [clEσ (fun _ => none) e n D (V.n (val% «claim_list_digest» "entries_ptr")),
        clEσ (fun _ => none) e n D (.n (val% «claim_list_digest» "n_g")),
        clEσ (fun _ => none) e n D (.n (val% «claim_list_digest» "bigs")),
        clEσ (fun _ => none) e n D (.n (val% «claim_list_digest» "groups")),
        clEσ (fun _ => none) e n D (.n (val% «claim_list_digest» "rest"))] =
        [gen ^ e, gen ^ n, gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)] := rfl
    have hr : [clEσ (fun _ => none) e n D (V.n (val% «claim_list_digest» "d0")),
        clEσ (fun _ => none) e n D (.n (val% «claim_list_digest» "d1"))] = digestCells D := rfl
    rw [ha, hr]
    exact h.mono (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ h => h.1) (fun _ _ _ h => h)
  · rw [KidsAtF]; exact ⟨rfl, fun _ _ => trivial, fun _ h => h.elim⟩

set_option maxHeartbeats 600000 in
/-- **`claim_list_digest` on a nonempty list completes placed.** -/
theorem digest_ne_callAtA (hwf : coreProgram.Wf) {k : ℕ} (hk : 17 ≤ k) {e n : ℕ} {cells : List E}
    (hn0 : n ≠ 0) (hn : n < 2 ^ 19) (hl : cells.length = 4 * n) {R : ℕ → Prop}
    (hR : ∀ i, e ≤ i → i < e + 4 * n → R i) {Pre : Reader → Prop} (hP : ∀ rd, Pre rd → ReadsAt rd (ptrAt e) cells)
    (hdef : ∀ rd, LowDef k rd → Pre rd → ∀ i, (i = n / 136 ∨ i = n % 136 / 17 ∨ i = n % 17 ∨ i = n) →
      ∃ t, LoadHolds rd (gen ^ i) 0 t)
    {fp c : ℕ} (hfc : fp + fs "claim_list_digest" ≤ c) :
    CallAtA fs al cert k "claim_list_digest" [ptrAt e, gen ^ n] (digestCells (keccak256 (cellsBytes cells))) R
      (fun _ => False) (fun _ => True) Pre (fun _ t => clHonest n t) (fs "claim_list_digest") fp c (clEnd fs al n c) := by
  set D := keccak256 (cellsBytes cells) with hD
  have hend : clEnd fs al n c = chEnd fs al n (allocBase (al "claim_list_chain")
      (allocBase (al "list_split") c + fs "list_split") + fs "claim_list_chain") := by simp [clEnd, hn0]
  rw [hend, ptrAt_eq_gpow]
  obtain ⟨hal0, hd0, ha0, hlo0, hhi0⟩ := clEs_parts (clEσ (fun _ => none) e n D)
  refine callAtA_nodeRd cl_loop hfc ⟨clEσ (fun _ => none) e n D, fn% «claim_list_digest», clEs, clVs, [],
    [fun _ _ => True, fun _ t => chHonest n t], fun _ => True, fun _ => False, find_claim_list_digest,
    by rw [hal0]; exact ⟨by simp, List.Pairwise.nil⟩, fun i hi => hi.elim, ?_, fun _ _ => trivial, ?_⟩
  · rw [clEs_calls n hn0, hal0, List.sum_nil, Nat.add_zero]
    exact digest_ne_kids hwf hk hn0 hn hl hR hP hdef hD _ (fun i hi => Or.inl hi) c
  intro rd hl' hp _
  obtain ⟨hal, -, -, hlo, hhi⟩ := clEs_parts (clEσ rd e n D)
  refine ⟨clEσ rd e n D, rfl, clEs_walk hn0 hn rd, rfl, by rw [hal, hal0], ?_, ?_, ?_, ?_,
    clEs_holds (hdef rd hl' hp n (Or.inr (Or.inr (Or.inr rfl)))), ?_⟩
  · rw [hal0]; exact ⟨by rw [hd0]; rfl, fun q hq => by rw [ha0] at hq; simp at hq⟩
  · rw [clEs_calls n hn0 (fun _ => 0)]
    intro cl hcl
    exact clEσ_args _ _ e n D cl hcl
  · intro A hA; rw [hlo] at hA; simp at hA
  · intro A hA; rw [hhi] at hA; simp at hA
  · intro ts hv hq
    rw [clEs_calls n hn0 (fun _ => 0)] at hv hq
    simp only [clCalls, hn0, ↓reduceIte] at hv hq
    obtain ⟨t1, t2, rfl⟩ : ∃ t1 t2, ts = [t1, t2] := by
      have := kidsValid_len hv
      simp only [List.length_cons, List.length_nil] at this
      match ts, this with
      | [t1, t2], _ => exact ⟨t1, t2, rfl⟩
    rw [kidsPost_cons, kidsPost_cons] at hq
    refine ⟨clEσ rd e n D, [t1, t2], by rw [hal0]; rfl, ⟨rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩,
      fun fn es' vs' hf hw' => ?_, by simp [clCalls, clTs, hn0], ?_⟩
    · rw [find_claim_list_digest] at hf
      cases hf
      rw [clEs_walk hn0 hn rd] at hw'
      obtain ⟨he', -⟩ := Out.ret.inj hw'
      rw [← he', clEs_calls n hn0]
    · simp only [clCalls, clTs, hn0, ↓reduceIte, KidsT]
      exact ⟨fun _ => trivial, fun _ => hq.2.1 rfl, trivial⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 600000 in
/-- **`claim_list_digest` completes placed** on `n < 2^19` claims' cells at `e` in the region `R`. -/
theorem digest_callAtA (hwf : coreProgram.Wf) {k : ℕ} (hk : 17 ≤ k) {e n : ℕ} {cells : List E}
    (hn : n < 2 ^ 19) (hl : cells.length = 4 * n) {R : ℕ → Prop} (hR : ∀ i, e ≤ i → i < e + 4 * n → R i)
    {Pre : Reader → Prop} (hP : ∀ rd, Pre rd → ReadsAt rd (ptrAt e) cells)
    (hdef : ∀ rd, LowDef k rd → Pre rd → ∀ i, (i = n / 136 ∨ i = n % 136 / 17 ∨ i = n % 17 ∨ i = n) →
      ∃ t, LoadHolds rd (gen ^ i) 0 t)
    {fp c : ℕ} (hfc : fp + fs "claim_list_digest" ≤ c) :
    CallAtA fs al cert k "claim_list_digest" [ptrAt e, gen ^ n] (digestCells (keccak256 (cellsBytes cells))) R
      (fun _ => False) (fun _ => True) Pre (fun _ t => clHonest n t) (fs "claim_list_digest") fp c (clEnd fs al n c) := by
  have mH : clHead.all (fun s => match s with | .callIf .. => false | _ => true) = true := rfl
  have mTl : clTail.all (fun s => match s with | .callIf .. => false | _ => true) = true := rfl
  have mZ : cl23Zero.all (fun s => match s with | .callIf .. => false | _ => true) = true := by decide +kernel
  have mE : cl23Else.all (fun s => match s with | .callIf .. => false | _ => true) = true := by decide +kernel
  have hH : ∀ s ∈ clHead, isAtomS s = true := by decide
  have hT : ∀ s ∈ clTail, isAtomS s = true := by decide
  set vs : List V := [.n (val% «claim_list_digest» "s3#0"), .n (val% «claim_list_digest» "s3#0[1]")]
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · -- the empty list
    have hcl : cells = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hcl
    have hend : clEnd fs al 0 c = c := by simp [clEnd]
    rw [hend]
    set σ0 := clzσ (fun _ => none) (ptrAt e) with hσ0
    set es := clHead.flatMap (slEvs σ0) ++ .inK (.n (val% «claim_list_digest» "s1#1")) ::
      (cl23Zero.flatMap (slEvs σ0) ++ clTail.flatMap (slEvs σ0)) with hes
    have hesσ : ∀ σ : Val, es = clHead.flatMap (slEvs σ) ++ .inK (.n (val% «claim_list_digest» "s1#1")) ::
        (cl23Zero.flatMap (slEvs σ) ++ clTail.flatMap (slEvs σ)) := fun σ => by
      rw [hes, noCallIf_congr (σ := σ0) (σ' := σ) mH, noCallIf_congr (σ := σ0) (σ' := σ) mZ,
        noCallIf_congr (σ := σ0) (σ' := σ) mTl]
    obtain ⟨z1, z2, z3, z4⟩ := cl23Zero_parts
    have hparts : ∀ σ : Val, allocs σ es = [] ∧ allocDsts es = [] ∧ addrs es = [] ∧ calls es = [] ∧
        loadAddrs σ es = [] := by
      intro σ
      obtain ⟨hhd, hha, hhad, hhc⟩ := straight_parts σ _ clHead_straight
      obtain ⟨hzd, hza, hzad, hzc⟩ := straight_parts σ _ cl23Zero_straight
      obtain ⟨htd, hta, htad, htc⟩ := straight_parts σ _ clTail_straight
      rw [hesσ σ]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [allocs, List.filterMap_append, List.filterMap_cons, Ev.alloc?] at hha hza hta ⊢
        rw [hha, hza, hta, z1]; rfl
      · simp only [allocDsts, List.filterMap_append, List.filterMap_cons, Ev.allocDst?] at hhd hzd htd ⊢
        rw [hhd, hzd, htd, z1]; rfl
      · simp only [addrs, List.filterMap_append, List.filterMap_cons, Ev.addr?] at hhad hzad htad ⊢
        rw [hhad, hzad, htad, z2]; simp [clHead, clTail, Stmt.addrS]
      · simp only [calls, List.filterMap_append, List.filterMap_cons, Ev.call?] at hhc hzc htc ⊢
        rw [hhc, hzc, htc, z3]; rfl
      · simp only [loadAddrs, List.filterMap_append, List.filterMap_cons, Ev.loadAddr?]
        have h1 := Memory.loadAddrs_straight σ _ clHead_straight
        have h2 := Memory.loadAddrs_straight σ _ cl23Zero_straight
        have h3 := Memory.loadAddrs_straight σ _ clTail_straight
        simp only [loadAddrs] at h1 h2 h3
        rw [h1, h2, h3, z4]; simp [clHead, clTail, stmtLoad?]
    obtain ⟨hal0, hd0, ha0, hc0, -⟩ := hparts σ0
    refine callAtA_nodeRd cl_loop hfc ⟨σ0, fn% «claim_list_digest», es, vs, [], [], fun _ => True,
      fun _ => False, find_claim_list_digest, by rw [hal0]; exact ⟨by simp, List.Pairwise.nil⟩,
      fun i hi => hi.elim, ?_, fun _ _ => trivial, ?_⟩
    · rw [hc0, hal0, List.sum_nil, Nat.add_zero, KidsAtF]
      exact ⟨rfl, fun _ _ => trivial, fun _ h => h⟩
    intro rd hl hp _
    obtain ⟨t0, ht0⟩ := Sig.load_gpow (fun i hi => hl i hi) (show 0 < 2 ^ k from Nat.two_pow_pos k)
    rw [← gen_pow_eq_ofK] at ht0
    obtain ⟨hat, e0, e1, h30, h3, hret⟩ := clz_core (rd := rd) (ptrAt e) ⟨t0, ht0⟩
    set σ := clzσ rd (ptrAt e) with hσ
    obtain ⟨hal, hd, ha, hc, hlo⟩ := hparts σ
    have hb : (if σ (.n (val% «claim_list_digest» "s1#1")) = 0 then walk σ cl23Zero else walk σ cl23Else) =
        .fall (cl23Zero.flatMap (slEvs σ)) := by
      simp only [h30, ↓reduceIte]; exact walk_straight_fall σ _ cl23Zero_straight
    have hw := walk_ite σ clTail clTail_straight (.n (val% «claim_list_digest» "s1#1")) cl23Zero cl23Else
      vs _ hb clHead clHead_straight
    rw [← cl_body, ← hesσ σ] at hw
    have hmZ : ∀ s ∈ clHead ++ cl23Zero ++ clTail, ∀ x, s = .atom x → x.Holds rd σ := by
      intro s hs x rfl
      refine hat x (cl_mem_atoms ?_)
      unfold clZEval
      simp only [List.mem_append] at hs ⊢
      rcases hs with (hs | hs) | hs
      · exact Or.inl (Or.inl (Or.inl hs))
      · exact Or.inl (Or.inl (Or.inr hs))
      · exact Or.inr hs
    refine ⟨σ, by rw [cl_param, e0, e1, pow_zero], hw, hret, by rw [hal, hal0], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hal0]; exact ⟨by rw [hd]; rfl, fun q hq => by rw [ha] at hq; simp at hq⟩
    · rw [hc]; intro cl hcl; simp at hcl
    · intro A hA; rw [hlo] at hA; simp at hA
    · intro A hA
      rw [hesσ σ] at hA
      have e1' := heapHintAddrs_nil_of (σ := σ) (pre := clHead) (by decide)
      have e2' := heapHintAddrs_nil_of (σ := σ) (pre := cl23Zero) (by decide +kernel)
      have e3' := heapHintAddrs_nil_of (σ := σ) (pre := clTail) (by decide)
      simp only [heapHintAddrs] at e1' e2' e3'
      simp only [heapHintAddrs, List.flatMap_append, List.flatMap_cons, e1', e2', e3'] at hA
      simp [Ev.hintAddrs] at hA
    · intro ev hev
      rw [hesσ σ] at hev
      rcases List.mem_append.mp hev with he | he
      · exact events_straight (fun s hs => sOk_atomS (hH s hs) (hmZ s (by simp [hs]))) ev he
      rcases List.mem_cons.mp he with rfl | he
      · show IsInK (σ (.n (val% «claim_list_digest» "s1#1"))); rw [h3]; exact gen_pow_add_isInK 0 0
      rcases List.mem_append.mp he with he | he
      · exact events_straight (fun s hs => sOk_atomS (List.all_eq_true.mp cl23Zero_atoms s hs)
          (hmZ s (by simp [hs]))) ev he
      · exact events_straight (fun s hs => sOk_atomS (hT s hs) (hmZ s (by simp [hs]))) ev he
    · intro ts hv _
      refine ⟨σ, ts, by rw [hal0]; rfl, ⟨e1, fun h0 => absurd rfl h0⟩, fun fn es' vs' hf hw' => ?_,
        by simp [clCalls, clTs], ?_⟩
      · rw [find_claim_list_digest] at hf
        cases hf
        rw [hw] at hw'
        obtain ⟨rfl, -⟩ := Out.ret.inj hw'
        rw [hc]; rfl
      · rw [hc] at hv
        cases ts with
        | nil => simp [KidsT, clCalls]
        | cons _ _ => exact hv.elim
  · exact digest_ne_callAtA hwf hk (by omega) hn hl hR hP hdef hfc

end
end LeanVM.Guest.Complete
