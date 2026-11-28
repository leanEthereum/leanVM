module

public import LeanVM.Guest.Complete.Claims.AnyCore
public import LeanVM.Guest.Complete.Claims.Vals
public import LeanVM.Guest.B1.Digest.ChildList
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«child_claim_list_any»

/-!
# `child_claim_list_any`'s path and valuation, layout-free

Restored from the archive's `B1/Digest/ChildListAt0` and `ChildListAt` (tag `formal-bus-archive`),
their layout-free part. The body is flat: a straight run `anyP1` (the chain buffer's `HeapBuf`, the
zero state, `child_claim_list_any_loop0` over the big frames, `child_claim_list_any_loop1` over the
groups), the dispatch on the rest (`anyDispS`), the checks and copies `anyPost`, the `ret`
(`anyFlat_split`). `anyBody_core`: on a memory holding the zero state at the chain buffer, where its
checks of `g^a` and `g^b` read, the evaluated valuation holds every atom (`AnyVals`). `anyHonest`:
the honest shape (`anyQ`, `anyCalls`, `anyBufs`, `anyTs`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd

@[expose] public section

/-! ## The path -/

/-- `child_claim_list_any_loop0`'s call: the big frames. -/
def any17S : Stmt := .callIf (.n (val% «child_claim_list_any» "s3#1")) name% «child_claim_list_any_loop0»
  [.n (val% «child_claim_list_any» "s3#2"), .n (val% «child_claim_list_any» "bigs"), .n (val% «child_claim_list_any» "chain"),
    .n (val% «child_claim_list_any» "entries_ptr"), .n (val% «child_claim_list_any» "region"),
    .n (val% «child_claim_list_any» "base"), .n (val% «child_claim_list_any» "last_g")]

/-- `child_claim_list_any_loop1`'s call: the groups. -/
def any18S : Stmt := .callIf (.n (val% «child_claim_list_any» "s6#1")) name% «child_claim_list_any_loop1»
  [.n (val% «child_claim_list_any» "s6#2"), .n (val% «child_claim_list_any» "groups"), .n (val% «child_claim_list_any» "mid"),
    .n (val% «child_claim_list_any» "entries_ptr"), .n (val% «child_claim_list_any» "region"),
    .n (val% «child_claim_list_any» "mid_base"), .n (val% «child_claim_list_any» "last_g")]

/-- The dispatch's arguments. -/
def anyDispArgs : List V := [.n (val% «child_claim_list_any» "last"), .n (val% «child_claim_list_any» "entries_ptr"),
  .n (val% «child_claim_list_any» "region"), .n (val% «child_claim_list_any» "d0~6"), .n (val% «child_claim_list_any» "last_g")]

/-- The dispatch's returns. -/
def anyDispRets : List V := [.n (val% «child_claim_list_any» "d0"), .n (val% «child_claim_list_any» "d1")]

/-- The dispatch on the rest. -/
def anyDispS : Stmt := .dispatch (.n (val% «child_claim_list_any» "rest")) cclNames anyDispArgs anyDispRets

/-- The body's returns. -/
def anyVs : List V := [.n (val% «child_claim_list_any» "s11#0"), .n (val% «child_claim_list_any» "s11#0[1]")]

/-- The body before its dispatch. -/
noncomputable def anyP1 : List Stmt := anyFlat.take (pos% «child_claim_list_any» "d0")

/-- The body after its dispatch. -/
noncomputable def anyPost : List Stmt := anyFlat.drop (pos% «child_claim_list_any» "d0" + 1)

set_option maxRecDepth 100000 in
theorem anyFlat_split : anyFlat = anyP1 ++ anyDispS :: anyPost :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem anyPost_atoms : anyPost.all isAtomS = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anyPost_straight : anyPost.all Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anyPost_parts : anyPost.filterMap Stmt.allocSz = [] ∧ anyPost.filterMap Stmt.addrS = [] ∧
    anyPost.filterMap Stmt.callS = [] ∧ anyPost.filterMap stmtLoad? = [] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem anyP1_straight : anyP1.all Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anyP1_allocs : anyP1.filterMap Stmt.allocSz =
    [(.n (val% «child_claim_list_any» "chain"), .inr (.n (val% «child_claim_list_any» "chain~7")))] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem anyP1_addrs : anyP1.filterMap Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem anyP1_calls : anyP1.filterMap Stmt.callS =
    [(some (.n (val% «child_claim_list_any» "s3#1")), name% «child_claim_list_any_loop0»,
        [.n (val% «child_claim_list_any» "s3#2"), .n (val% «child_claim_list_any» "bigs"), .n (val% «child_claim_list_any» "chain"),
          .n (val% «child_claim_list_any» "entries_ptr"), .n (val% «child_claim_list_any» "region"),
          .n (val% «child_claim_list_any» "base"), .n (val% «child_claim_list_any» "last_g")], []),
      (some (.n (val% «child_claim_list_any» "s6#1")), name% «child_claim_list_any_loop1»,
        [.n (val% «child_claim_list_any» "s6#2"), .n (val% «child_claim_list_any» "groups"), .n (val% «child_claim_list_any» "mid"),
          .n (val% «child_claim_list_any» "entries_ptr"), .n (val% «child_claim_list_any» "region"),
          .n (val% «child_claim_list_any» "mid_base"), .n (val% «child_claim_list_any» "last_g")], [])] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem anyP1_loads : anyP1.filterMap stmtLoad? =
    (List.range 13).map fun c => (.n (val% «child_claim_list_any» "chain"), c) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem anyP1_kinds : anyP1.all (fun s => isAtomS s || stmtEqb s any17S || stmtEqb s any18S) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem any_loop : coreProgram.loop "child_claim_list_any" = false := by
  rw [Program.loop_of_find? find_child_claim_list_any]; decide +kernel

theorem any_param (σ : Val) : (Fn.params fn% «child_claim_list_any»).map σ =
    [σ (.n (val% «child_claim_list_any» "entries_ptr")), σ (.n (val% «child_claim_list_any» "region")),
      σ (.n (val% «child_claim_list_any» "base")), σ (.n (val% «child_claim_list_any» "limit_g")),
      σ (.n (val% «child_claim_list_any» "bigs")), σ (.n (val% «child_claim_list_any» "groups")),
      σ (.n (val% «child_claim_list_any» "rest"))] := rfl

theorem any_body : Fn.body fn% «child_claim_list_any» = anyP1 ++ anyDispS :: (anyPost ++ [.ret anyVs]) := by
  rw [child_claim_list_any_shape, anyFlat_split]; simp [anyVs]

theorem cclNames_get {r : ℕ} (hr : r < 17) : cclNames[r]! = cclNames.getD r "" := by
  have h : r < cclNames.length := by simp [cclNames]; omega
  rw [getElem!_pos cclNames r h, List.getD_eq_getElem _ _ h]

/-! ## The evaluated body -/

/-- **`child_claim_list_any`'s body, evaluated**: in order, its stores the zero state's thirteen
words at the chain buffer, every other atom needing a side condition the division `limit / g` or
the checks of `bigs` and `groups`. -/
noncomputable def anyCOk : Bool :=
  let SE := storesOf 7 anyFlat
  (chk 7 anyFlat).isSome &&
  SE.all (fun a => (List.range 13).any fun c => atomEqb a
    (.load (.n ((val% «child_claim_list_any» "s2.i0:zero_state.s0.u0.s0#0") + c)) (.n (val% «child_claim_list_any» "chain")) c)) &&
  (atomsIn anyFlat).all (fun a => !needsSide a || decide (a ∈ SE) ||
    atomEqb a (.mul (.n (val% «child_claim_list_any» "limit_g")) (.n (val% «child_claim_list_any» "last_g"))
      (.n (val% «child_claim_list_any» "last_g~0"))) ||
    atomEqb a (.touch (.n (val% «child_claim_list_any» "s9#0")) (.n (val% «child_claim_list_any» "bigs"))) ||
    atomEqb a (.touch (.n (val% «child_claim_list_any» "s10#0")) (.n (val% «child_claim_list_any» "groups"))))

set_option maxRecDepth 100000 in
theorem anyc_ok : anyCOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem any_atoms : ∀ a ∈ [Atom.const (.n (val% «child_claim_list_any» "last_g~0")) (word 2 0),
    .mul (.n (val% «child_claim_list_any» "limit_g")) (.n (val% «child_claim_list_any» "last_g")) (.n (val% «child_claim_list_any» "last_g~0")),
    .mul (.n (val% «child_claim_list_any» "chain~0")) (.n (val% «child_claim_list_any» "bigs")) (.n (val% «child_claim_list_any» "groups")),
    .const (.n (val% «child_claim_list_any» "chain~1")) (word 2 0),
    .mul (.n (val% «child_claim_list_any» "chain~2")) (.n (val% «child_claim_list_any» "chain~0")) (.n (val% «child_claim_list_any» "chain~1")),
    .mul (.n (val% «child_claim_list_any» "chain~3")) (.n (val% «child_claim_list_any» "chain~2")) (.n (val% «child_claim_list_any» "chain~2")),
    .mul (.n (val% «child_claim_list_any» "chain~4")) (.n (val% «child_claim_list_any» "chain~3")) (.n (val% «child_claim_list_any» "chain~2")),
    .mul (.n (val% «child_claim_list_any» "chain~5")) (.n (val% «child_claim_list_any» "chain~4")) (.n (val% «child_claim_list_any» "chain~4")),
    .mul (.n (val% «child_claim_list_any» "chain~6")) (.n (val% «child_claim_list_any» "chain~5")) (.n (val% «child_claim_list_any» "chain~5")),
    .mul (.n (val% «child_claim_list_any» "chain~7")) (.n (val% «child_claim_list_any» "chain~6")) (.n (val% «child_claim_list_any» "chain~2")),
    .hint (.allocDyn (.n (val% «child_claim_list_any» "chain")) (.n (val% «child_claim_list_any» "chain~7")))],
    a ∈ atomsIn anyFlat := by
  decide +kernel

/-- The oracle of `child_claim_list_any`'s valuation: the chain buffer, the digest. -/
noncomputable def anyw (chain : E) (D : Digest) (i : ℕ) : E :=
  if i = val% «child_claim_list_any» "chain" then chain
  else if i = val% «child_claim_list_any» "d0" then (digestHalves D).1
  else if i = val% «child_claim_list_any» "d1" then (digestHalves D).2
  else 0

/-- `child_claim_list_any`'s valuation. -/
noncomputable def anyσ (rd : Reader) (args : List E) (chain : E) (D : Digest) : Val :=
  B1.Val.ofArgs (ev rd (anyw chain D) args anyFlat)

/-- **What `child_claim_list_any`'s valuation is** (`n = 136a + 17b + c`). -/
structure AnyVals (rd : Reader) (σ : Val) (args : List E) (a b : ℕ) (chain : E) (D : Digest) : Prop where
  atoms : ∀ x ∈ atomsIn anyFlat, x.Holds rd σ
  par : [σ (.n (val% «child_claim_list_any» "entries_ptr")), σ (.n (val% «child_claim_list_any» "region")),
    σ (.n (val% «child_claim_list_any» "base")), σ (.n (val% «child_claim_list_any» "limit_g")),
    σ (.n (val% «child_claim_list_any» "bigs")), σ (.n (val% «child_claim_list_any» "groups")),
    σ (.n (val% «child_claim_list_any» "rest"))] = args
  v8 : σ (.n (val% «child_claim_list_any» "last_g")) * gen = σ (.n (val% «child_claim_list_any» "limit_g"))
  v16 : σ (.n (val% «child_claim_list_any» "chain~7")) = gen ^ (13 * (a + b + 1))
  v17 : σ (.n (val% «child_claim_list_any» "chain")) = chain
  v32 : σ (.n (val% «child_claim_list_any» "s3#1")) = 1 + gen ^ a
  v33 : σ (.n (val% «child_claim_list_any» "s3#2")) = 1
  v39 : σ (.n (val% «child_claim_list_any» "mid")) = chain * gen ^ (13 * a)
  v48 : σ (.n (val% «child_claim_list_any» "mid_base")) = σ (.n (val% «child_claim_list_any» "base")) * gen ^ (136 * a)
  v50 : σ (.n (val% «child_claim_list_any» "s6#1")) = 1 + gen ^ b
  v51 : σ (.n (val% «child_claim_list_any» "s6#2")) = 1
  v57 : σ (.n (val% «child_claim_list_any» "last")) = chain * gen ^ (13 * (a + b))
  v63 : σ (.n (val% «child_claim_list_any» "d0~6")) = σ (.n (val% «child_claim_list_any» "base")) * gen ^ (136 * a + 17 * b)
  v64 : σ (.n (val% «child_claim_list_any» "d0")) = (digestHalves D).1
  v65 : σ (.n (val% «child_claim_list_any» "d1")) = (digestHalves D).2
  v68 : σ (.n (val% «child_claim_list_any» "s11#0")) = (digestHalves D).1
  v69 : σ (.n (val% «child_claim_list_any» "s11#0[1]")) = (digestHalves D).2

variable {rd : Reader}

set_option maxRecDepth 20000 in
/-- **`child_claim_list_any`'s valuation**: on a memory holding the zero state at the chain buffer,
where its checks of `g^a` and `g^b` read. -/
theorem anyBody_core {entries region base limit chain : E} {a b c : ℕ} (D : Digest)
    (hz0 : StateAt rd chain 0 zeroState) (hda : ∃ t, LoadHolds rd (gen ^ a) 0 t)
    (hdb : ∃ t, LoadHolds rd (gen ^ b) 0 t) :
    AnyVals rd (anyσ rd [entries, region, base, limit, gen ^ a, gen ^ b, gen ^ c] chain D)
      [entries, region, base, limit, gen ^ a, gen ^ b, gen ^ c] a b chain D := by
  have hk := anyc_ok
  simp only [anyCOk, Bool.and_eq_true] at hk
  obtain ⟨⟨hchk1, hst⟩, hside⟩ := hk
  have hb := anyBody_ok
  simp only [anyBodyOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hdis⟩, -⟩, h33⟩, h32⟩, h31⟩, h51⟩, h50⟩, h49⟩,
    hzs⟩, hm39⟩, hm48⟩, hm57⟩, hm63⟩, hc68⟩, hc69⟩ := hb
  set w := anyw chain D with hw
  obtain ⟨c', hchk⟩ := Option.isSome_iff_exists.mp hchk1
  let args : List E := [entries, region, base, limit, gen ^ a, gen ^ b, gen ^ c]
  set σ := anyσ rd args chain D with hσ
  obtain ⟨-, -, hgs⟩ := ev_spec rd w anyFlat args hchk
  rw [show args.length = 7 from rfl] at hgs
  set SE := storesOf 7 anyFlat with hSE
  have hg : ∀ x ∈ atomsIn anyFlat, Good rd SE w σ x := fun x hx => hgs _ (cl_atom_mem hx)
  have par : ∀ i (hi : i < 7), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have hs := any_atoms
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs
  obtain ⟨s7, s3, s9, s10, s11, s12, s13, s14, s15, s16, s17⟩ := hs
  have v7 : σ (.n (val% «child_claim_list_any» "last_g~0")) = gen := by
    have : σ (.n (val% «child_claim_list_any» "last_g~0")) = word 2 0 := hg _ s7
    rw [this, word_gen]
  have v17 : σ (.n (val% «child_claim_list_any» "chain")) = chain := by
    have : σ (.n (val% «child_claim_list_any» "chain")) = w (val% «child_claim_list_any» "chain") := hg _ s17
    rw [this, hw]; simp [anyw]
  have v18 : ∀ c < 13, σ (.n ((val% «child_claim_list_any» "s2.i0:zero_state.s0.u0.s0#0") + c)) = 0 := by
    intro c hc'
    obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp (hzs c hc').2
    have hgx := hg x hx
    cases x <;> simp only [isConstAt, Bool.false_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hp
    obtain ⟨rfl, he⟩ := hp
    have hgx' : σ (.n ((val% «child_claim_list_any» "s2.i0:zero_state.s0.u0.s0#0") + c)) = _ := hgx
    rw [hgx', eEqb_sound he, word_zero]
  have e4 : σ (.n (val% «child_claim_list_any» "bigs")) = gen ^ a := par 4 (by omega)
  have e5 : σ (.n (val% «child_claim_list_any» "groups")) = gen ^ b := par 5 (by omega)
  have hat : ∀ x ∈ atomsIn anyFlat, x.Holds rd σ := by
    refine atoms_holds_stores hg (fun x hx hnS hns => ?_) (fun _ x hx hxS => ?_)
    · have := List.all_eq_true.mp hside x hx
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
      rcases this with (((h | h) | h) | h) | h
      · rw [hns] at h; exact absurd h (by simp)
      · exact absurd h hnS
      · rw [atomEqb_sound h]
        right
        show if (val% «child_claim_list_any» "last_g") < (val% «child_claim_list_any» "limit_g") ∧
          (val% «child_claim_list_any» "last_g~0") < (val% «child_claim_list_any» "limit_g") then True
          else σ (.n (val% «child_claim_list_any» "last_g~0")) ≠ 0
        rw [ite_neg' (by omega), v7]
        exact gen_ne_zero
      · right; rw [atomEqb_sound h]
        obtain ⟨t, ht⟩ := hda
        show IsInK (σ (.n (val% «child_claim_list_any» "bigs"))) ∧
          (rd ((σ (.n (val% «child_claim_list_any» "bigs"))).limb 0 * addressOfIndex 0)).isSome
        rw [e4]; exact ⟨ht.1, by rw [ht.2]; rfl⟩
      · right; rw [atomEqb_sound h]
        obtain ⟨t, ht⟩ := hdb
        show IsInK (σ (.n (val% «child_claim_list_any» "groups"))) ∧
          (rd ((σ (.n (val% «child_claim_list_any» "groups"))).limb 0 * addressOfIndex 0)).isSome
        rw [e5]; exact ⟨ht.1, by rw [ht.2]; rfl⟩
    · obtain ⟨c, hc', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hst x hxS)
      rw [atomEqb_sound he]
      have hc13 := List.mem_range.mp hc'
      show LoadHolds rd (σ (.n (val% «child_claim_list_any» "chain"))) c
        (σ (.n ((val% «child_claim_list_any» "s2.i0:zero_state.s0.u0.s0#0") + c)))
      rw [v17, v18 c hc13]
      have := hz0 ⟨c, hc13⟩
      rwa [Nat.zero_add, cellsOfState_zero] at this
  have gd : ∀ v ∈ [V.n (val% «child_claim_list_any» "d0"), V.n (val% «child_claim_list_any» "d1")], σ v = w v.idx := by
    obtain ⟨s, hs, he⟩ := List.any_eq_true.mp hdis
    rw [stmtEqb_sound he] at hs
    exact hgs _ hs
  have v64 : σ (.n (val% «child_claim_list_any» "d0")) = (digestHalves D).1 := by
    rw [gd _ (by simp), hw]; simp [anyw]
  have v65 : σ (.n (val% «child_claim_list_any» "d1")) = (digestHalves D).2 := by
    rw [gd _ (by simp), hw]; simp [anyw]
  have q3 : σ (.n (val% «child_claim_list_any» "limit_g")) =
      σ (.n (val% «child_claim_list_any» "last_g")) * σ (.n (val% «child_claim_list_any» "last_g~0")) := hat _ s3
  have q9 : σ (.n (val% «child_claim_list_any» "chain~0")) =
      σ (.n (val% «child_claim_list_any» "bigs")) * σ (.n (val% «child_claim_list_any» "groups")) := hat _ s9
  have q10 : σ (.n (val% «child_claim_list_any» "chain~1")) = word 2 0 := hat _ s10
  have q11 : σ (.n (val% «child_claim_list_any» "chain~2")) =
      σ (.n (val% «child_claim_list_any» "chain~0")) * σ (.n (val% «child_claim_list_any» "chain~1")) := hat _ s11
  have q12 : σ (.n (val% «child_claim_list_any» "chain~3")) =
      σ (.n (val% «child_claim_list_any» "chain~2")) * σ (.n (val% «child_claim_list_any» "chain~2")) := hat _ s12
  have q13 : σ (.n (val% «child_claim_list_any» "chain~4")) =
      σ (.n (val% «child_claim_list_any» "chain~3")) * σ (.n (val% «child_claim_list_any» "chain~2")) := hat _ s13
  have q14 : σ (.n (val% «child_claim_list_any» "chain~5")) =
      σ (.n (val% «child_claim_list_any» "chain~4")) * σ (.n (val% «child_claim_list_any» "chain~4")) := hat _ s14
  have q15 : σ (.n (val% «child_claim_list_any» "chain~6")) =
      σ (.n (val% «child_claim_list_any» "chain~5")) * σ (.n (val% «child_claim_list_any» "chain~5")) := hat _ s15
  have q16 : σ (.n (val% «child_claim_list_any» "chain~7")) =
      σ (.n (val% «child_claim_list_any» "chain~6")) * σ (.n (val% «child_claim_list_any» "chain~2")) := hat _ s16
  have v39 : σ (.n (val% «child_claim_list_any» "mid")) = chain * gen ^ (13 * a) := by
    rw [monoIs_sound hm39 hat, v17, e4, gen_pow_pow]
  have v48 : σ (.n (val% «child_claim_list_any» "mid_base")) =
      σ (.n (val% «child_claim_list_any» "base")) * gen ^ (136 * a) := by
    rw [monoIs_sound hm48 hat, e4, gen_pow_pow]
  refine ⟨hat, ?_, by rw [q3, v7], ?_, v17, ?_, ?_, v39, v48, ?_, ?_, ?_, ?_, v64, v65, ?_, ?_⟩
  · rw [par 0 (by omega), par 1 (by omega), par 2 (by omega), par 3 (by omega), par 4 (by omega),
      par 5 (by omega), par 6 (by omega)]
    rfl
  · rw [q16, q15, q14, q13, q12, q11, q10, q9, e4, e5, word_gen, ← pow_add, ← pow_succ, pow_mul']
    generalize gen ^ (a + b + 1) = x
    ring
  · rw [add_sound h32 hat, const_sound h31 hat, word_one, e4]
  · rw [const_sound h33 hat, word_one]
  · rw [add_sound h50 hat, const_sound h49 hat, word_one, e5]
  · rw [const_sound h51 hat, word_one]
  · rw [mono2Is_sound hm57 hat, v17, e4, e5, gen_pow_pow, gen_pow_pow, mul_assoc, ← pow_add,
      Nat.mul_add]
  · rw [mono2Is_sound hm63 hat, e4, e5, gen_pow_pow, gen_pow_pow, mul_assoc, ← pow_add]
  · rw [copy_sound hc68 hat, v64]
  · rw [copy_sound hc69 hat, v65]

/-! ## The honest shape -/

/-- `child_claim_list_any`'s words that end its loops and size its buffer (`n = 136a + 17b + c`). -/
def anyQ (n : ℕ) (σ : Val) : Prop :=
  σ (.n (val% «child_claim_list_any» "bigs")) = gen ^ (n / 136) ∧
    σ (.n (val% «child_claim_list_any» "groups")) = gen ^ (n % 136 / 17) ∧
    σ (.n (val% «child_claim_list_any» "rest")) = gen ^ (n % 17) ∧
    σ (.n (val% «child_claim_list_any» "chain~7")) = gen ^ (13 * (n / 136 + n % 136 / 17 + 1)) ∧
    σ (.n (val% «child_claim_list_any» "s3#2")) = 1 ∧ σ (.n (val% «child_claim_list_any» "s6#2")) = 1

/-- `child_claim_list_any`'s calls: the two loops when entered, `child_claim_list_last__L{n % 17}`. -/
def anyCalls (n : ℕ) (_ : Val) : List Call :=
  [⟨name% «child_claim_list_any_loop0», [.n (val% «child_claim_list_any» "s3#2"), .n (val% «child_claim_list_any» "bigs"),
      .n (val% «child_claim_list_any» "chain"), .n (val% «child_claim_list_any» "entries_ptr"),
      .n (val% «child_claim_list_any» "region"), .n (val% «child_claim_list_any» "base"),
      .n (val% «child_claim_list_any» "last_g")], [], decide (n / 136 ≠ 0)⟩,
    ⟨name% «child_claim_list_any_loop1», [.n (val% «child_claim_list_any» "s6#2"), .n (val% «child_claim_list_any» "groups"),
      .n (val% «child_claim_list_any» "mid"), .n (val% «child_claim_list_any» "entries_ptr"),
      .n (val% «child_claim_list_any» "region"), .n (val% «child_claim_list_any» "mid_base"),
      .n (val% «child_claim_list_any» "last_g")], [], decide (n % 136 / 17 ≠ 0)⟩,
    ⟨cclNames.getD (n % 17) "", anyDispArgs, anyDispRets, true⟩]

/-- `child_claim_list_any`'s `HeapBuf`: the chain buffer. -/
def anyBufs (n : ℕ) (_ : Val) : List ℕ := [13 * (n / 136 + n % 136 / 17 + 1)]

/-- No constraint on `child_claim_list_any`'s callees. -/
def anyTs : List (Tree → Prop) := [fun _ => True, fun _ => True, fun _ => True]

/-- **`child_claim_list_any`'s honest shape** on `n` claims. -/
def anyHonest (n : ℕ) : Tree → Prop :=
  NodeHonest coreProgram "child_claim_list_any" (anyQ n) (anyCalls n) (anyBufs n) anyTs

end
end LeanVM.Guest.B1.Digest
