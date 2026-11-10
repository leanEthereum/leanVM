/-
  LeanVM.Guest.B1.Digest.ChildListAt0

  `child_claim_list_any`'s path and honest valuation, and its callees `child_claim_list_last__L{k}`
  in the uniform placed form.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListComplete
public import LeanVM.Guest.B1.Digest.ChildListCore
public import LeanVM.Guest.B1.Digest.ClaimListAt
public import LeanVM.Guest.Budget.Bounded

/-!
# The walk by hinted indices, the parts

* The path: `child_claim_list_any`'s body is flat (G:4210-4230): a straight run `anyP1` (the chain
  buffer's `HeapBuf`, the zero state, `__loop17` over the big frames, `__loop18` over the groups),
  the dispatch on the rest, two copies, the `ret` (`anyFlat_split`).
* `anyCOk`: the body evaluated in order (`Fwd.ev`), its stores the zero state's thirteen words,
  its only side condition beyond them the division `last = limit / g`.
* `anyBody_core`: on a memory holding the zero state at the chain buffer, the evaluated valuation
  holds every atom (`AnyVals`: the words that size the buffer, end the loops and place the
  callees).
* `recMem_drop`: the records after the first `s`, the marks `base · g^s`.
* `ccl_completeAtB`, `ccl_completeAt`: `child_claim_list_last__L{k}` is complete, placed, a leaf
  within its frame (`relAtIn_atoms` on `ccl_core`), reading the state's words, the records' marks
  at `region · g^(os j)` and their cells among the caller's words.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDTB Returns LowDef)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)
open LeanVM.Guest.B1.Da (relAtIn_atoms)

@[expose] public section

/-! ## The path -/

/-- `__loop17`'s call: the big frames. -/
def any17S : Stmt := .callIf (.n 32) "__loop17" [.n 33, .n 4, .n 17, .n 0, .n 1, .n 2, .n 8]

/-- `__loop18`'s call: the groups. -/
def any18S : Stmt := .callIf (.n 50) "__loop18" [.n 51, .n 5, .n 39, .n 0, .n 1, .n 48, .n 8]

/-- The dispatch on the rest. -/
def anyDispS : Stmt := .dispatch (.n 6) cclNames [.n 57, .n 0, .n 1, .n 63, .n 8] [.n 64, .n 65]

/-- The body before its dispatch. -/
noncomputable def anyP1 : List Stmt := anyFlat.take 72

/-- The body after its dispatch. -/
noncomputable def anyPost : List Stmt := anyFlat.drop 73

set_option maxRecDepth 100000 in
theorem anyFlat_split : anyFlat = anyP1 ++ anyDispS :: anyPost :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem anyPost_eq : anyPost = [.atom (.copy (.n 66) (.n 64)), .atom (.copy (.n 67) (.n 65))] :=
  stmtsEqb_sound (by decide +kernel)

theorem anyPost_straight : anyPost.all Main.Stmt.straight = true := by rw [anyPost_eq]; rfl

set_option maxRecDepth 100000 in
theorem anyP1_straight : anyP1.all Main.Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem anyP1_allocs : anyP1.filterMap Main.Stmt.allocSz = [(.n 17, .inr (.n 16))] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem anyP1_addrs : anyP1.filterMap Main.Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem anyP1_calls : anyP1.filterMap Main.Stmt.callS =
    [(some (.n 32), "__loop17", [.n 33, .n 4, .n 17, .n 0, .n 1, .n 2, .n 8], []),
      (some (.n 50), "__loop18", [.n 51, .n 5, .n 39, .n 0, .n 1, .n 48, .n 8], [])] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem anyP1_loads : anyP1.filterMap B1.Stmt.loadS = (List.range 13).map fun c => (.n 17, c) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem anyP1_kinds : anyP1.all (fun s => isAtomS s || stmtEqb s any17S || stmtEqb s any18S) =
    true := by decide +kernel

set_option maxRecDepth 100000 in
theorem any_loop : coreProgram.loop "child_claim_list_any" = false := by
  rw [Program.loop_of_find? find_child_claim_list_any]; decide +kernel

theorem any_param (σ : Val) : (Fn.params Data.core25).map σ =
    [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6)] := rfl

theorem any_body : Fn.body Data.core25 =
    anyP1 ++ anyDispS :: (anyPost ++ [.ret [.n 66, .n 67]]) := by
  rw [core25_shape, anyFlat_split]; simp

theorem cclNames_get {r : ℕ} (hr : r < 17) : cclNames[r]! = cclNames.getD r "" := by
  have h : r < cclNames.length := by simp [cclNames]; omega
  rw [getElem!_pos cclNames r h, List.getD_eq_getElem _ _ h]

/-! ## The evaluated body -/

/-- **`child_claim_list_any`'s body, evaluated**: in order, its stores the zero state's words at
the chain buffer `.n 17`, every other atom needing a side condition the division
`.n 8 = .n 3 / .n 7`, no chain. -/
noncomputable def anyCOk : Bool :=
  let SE := storesOf 7 anyFlat
  (chk 7 anyFlat).isSome &&
  SE.all (fun a => (List.range 13).any fun c => atomEqb a (.load (.n (18 + c)) (.n 17) c)) &&
  (atomsIn anyFlat).all (fun a => !needsSide a || decide (a ∈ SE) ||
    atomEqb a (.mul (.n 3) (.n 8) (.n 7))) &&
  canonChk [] ((atomsIn anyFlat).filter fun a => decide (a ∉ SE))

set_option maxRecDepth 100000 in
theorem anyc_ok : anyCOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem any_atoms : ∀ a ∈ [Atom.const (.n 7) (word 2 0), .mul (.n 3) (.n 8) (.n 7),
    .mul (.n 9) (.n 4) (.n 5), .const (.n 10) (word 2 0), .mul (.n 11) (.n 9) (.n 10),
    .mul (.n 12) (.n 11) (.n 11), .mul (.n 13) (.n 12) (.n 11), .mul (.n 14) (.n 13) (.n 13),
    .mul (.n 15) (.n 14) (.n 14), .mul (.n 16) (.n 15) (.n 11), .hint (.allocDyn (.n 17) (.n 16))],
    a ∈ atomsIn anyFlat := by
  decide +kernel

/-- The oracle of `child_claim_list_any`'s valuation: the chain buffer, the digest. -/
noncomputable def anyw (chain : E) (D : Digest) (i : ℕ) : E :=
  if i = 17 then chain else if i = 64 then (digestHalves D).1 else if i = 65 then (digestHalves D).2
  else 0

/-- `child_claim_list_any`'s valuation. -/
noncomputable def anyσ (rd : Reader) (args : List E) (chain : E) (D : Digest) : Val :=
  B1.Val.ofArgs (ev rd (anyw chain D) args anyFlat)

/-- **What `child_claim_list_any`'s valuation is** (`n = 136a + 17b + c`). -/
structure AnyVals (rd : Reader) (σ : Val) (args : List E) (a b : ℕ) (chain : E) (D : Digest) :
    Prop where
  atoms : ∀ x ∈ atomsIn anyFlat, x.Holds rd σ
  par : [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6)] = args
  v8 : σ (.n 8) * gen = σ (.n 3)
  v16 : σ (.n 16) = gen ^ (13 * (a + b + 1))
  v17 : σ (.n 17) = chain
  v32 : σ (.n 32) = 1 + gen ^ a
  v33 : σ (.n 33) = 1
  v39 : σ (.n 39) = chain * gen ^ (13 * a)
  v48 : σ (.n 48) = σ (.n 2) * gen ^ (136 * a)
  v50 : σ (.n 50) = 1 + gen ^ b
  v51 : σ (.n 51) = 1
  v57 : σ (.n 57) = chain * gen ^ (13 * (a + b))
  v63 : σ (.n 63) = σ (.n 2) * gen ^ (136 * a + 17 * b)
  v64 : σ (.n 64) = (digestHalves D).1
  v65 : σ (.n 65) = (digestHalves D).2
  v66 : σ (.n 66) = (digestHalves D).1
  v67 : σ (.n 67) = (digestHalves D).2

variable {rd : Reader}

set_option maxRecDepth 20000 in
/-- **`child_claim_list_any`'s valuation**: on a memory holding the zero state at the chain
buffer. -/
theorem anyBody_core {entries region base limit chain : E} {a b c : ℕ} (D : Digest)
    (hz0 : StateAt rd chain 0 zeroState) :
    AnyVals rd (anyσ rd [entries, region, base, limit, gen ^ a, gen ^ b, gen ^ c] chain D)
      [entries, region, base, limit, gen ^ a, gen ^ b, gen ^ c] a b chain D := by
  have hk := anyc_ok
  simp only [anyCOk, Bool.and_eq_true] at hk
  obtain ⟨⟨⟨hchk1, hst⟩, hside⟩, hcan⟩ := hk
  have hb := anyBody_ok
  simp only [anyBodyOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hdis⟩, -⟩, h33⟩, h32⟩, h31⟩, h51⟩, h50⟩, h49⟩,
    hzs⟩, hm39⟩, hm48⟩, hm57⟩, hm63⟩, hc66⟩, hc67⟩ := hb
  set w := anyw chain D with hw
  obtain ⟨c', hchk⟩ := Option.isSome_iff_exists.mp hchk1
  let args : List E := [entries, region, base, limit, gen ^ a, gen ^ b, gen ^ c]
  set σ := anyσ rd args chain D with hσ
  have hidx : ∀ v, σ v = σ (.n v.idx) := fun v => by rw [hσ]; rfl
  obtain ⟨-, -, hgs⟩ := ev_spec rd w anyFlat args hchk
  rw [show args.length = 7 from rfl] at hgs
  set SE := storesOf 7 anyFlat with hSE
  have hg : ∀ x ∈ atomsIn anyFlat, Good rd SE w σ x := fun x hx => hgs _ (cl_atom_mem hx)
  have par : ∀ i (hi : i < 7), σ (.n i) = args.getD i 0 := fun i hi => by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args]; omega)
  have hs := any_atoms
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs
  obtain ⟨s7, s3, s9, s10, s11, s12, s13, s14, s15, s16, s17⟩ := hs
  have v7 : σ (.n 7) = gen := by
    have : σ (.n 7) = word 2 0 := hg _ s7
    rw [this, word_gen]
  have v17 : σ (.n 17) = chain := by
    have : σ (.n 17) = w 17 := hg _ s17
    rw [this, hw]; simp [anyw]
  have v18 : ∀ c < 13, σ (.n (18 + c)) = 0 := by
    intro c hc'
    obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp (hzs c hc').2
    have hgx := hg x hx
    cases x <;> simp only [isConstAt, Bool.false_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hp
    obtain ⟨rfl, he⟩ := hp
    have hgx' : σ (.n (18 + c)) = _ := hgx
    rw [hgx', eEqb_sound he, word_zero]
  have hat : ∀ x ∈ atomsIn anyFlat, x.Holds rd σ := by
    refine atoms_holds_stores (S := SE) (w := w) hidx hcan hg (A := []) (by simp)
      (fun x hx hnS hns => ?_) (fun _ x hx hxS => ?_)
    · have := List.all_eq_true.mp hside x hx
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
      rcases this with (h | h) | h
      · rw [hns] at h; exact absurd h (by simp)
      · exact absurd h hnS
      · rw [atomEqb_sound h]
        right
        show if (8 : ℕ) < 3 ∧ (7 : ℕ) < 3 then True else σ (.n 7) ≠ 0
        rw [ite_neg' (by omega), v7]
        exact gen_ne_zero
    · obtain ⟨c, hc', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp hst x hxS)
      rw [atomEqb_sound he]
      have hc13 := List.mem_range.mp hc'
      show LoadHolds rd (σ (.n 17)) c (σ (.n (18 + c)))
      rw [v17, v18 c hc13]
      have := hz0 ⟨c, hc13⟩
      rwa [Nat.zero_add, cellsOfState_zero] at this
  have gd : ∀ v ∈ [V.n 64, V.n 65], σ v = w v.idx := by
    obtain ⟨s, hs, he⟩ := List.any_eq_true.mp hdis
    rw [stmtEqb_sound he] at hs
    exact hgs _ hs
  have v64 : σ (.n 64) = (digestHalves D).1 := by
    rw [gd _ (by simp), hw]; simp [anyw]
  have v65 : σ (.n 65) = (digestHalves D).2 := by
    rw [gd _ (by simp), hw]; simp [anyw]
  have e2 : σ (.n 2) = base := par 2 (by omega)
  have e4 : σ (.n 4) = gen ^ a := par 4 (by omega)
  have e5 : σ (.n 5) = gen ^ b := par 5 (by omega)
  have q3 : σ (.n 3) = σ (.n 8) * σ (.n 7) := hat _ s3
  have q9 : σ (.n 9) = σ (.n 4) * σ (.n 5) := hat _ s9
  have q10 : σ (.n 10) = word 2 0 := hat _ s10
  have q11 : σ (.n 11) = σ (.n 9) * σ (.n 10) := hat _ s11
  have q12 : σ (.n 12) = σ (.n 11) * σ (.n 11) := hat _ s12
  have q13 : σ (.n 13) = σ (.n 12) * σ (.n 11) := hat _ s13
  have q14 : σ (.n 14) = σ (.n 13) * σ (.n 13) := hat _ s14
  have q15 : σ (.n 15) = σ (.n 14) * σ (.n 14) := hat _ s15
  have q16 : σ (.n 16) = σ (.n 15) * σ (.n 11) := hat _ s16
  have v39 : σ (.n 39) = chain * gen ^ (13 * a) := by
    rw [monoIs_sound hm39 hat, v17, e4, gen_pow_pow]
  have v48 : σ (.n 48) = σ (.n 2) * gen ^ (136 * a) := by
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
  · rw [copy_sound hc66 hat, v64]
  · rw [copy_sound hc67 hat, v65]

/-! ## The events of a body with a dispatch -/

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

/-! ## The records, the chain buffer -/

/-- The records after the first `s`, the marks `base · g^s`. -/
theorem recMem_drop {region limit entries base : E} {n : ℕ} {o : ℕ → ℕ} {cells : List E}
    (h : RecMem rd region limit entries base n o cells) {s k : ℕ} (hsk : s + k ≤ n) :
    RecMem rd region limit entries (base * gen ^ s) k (fun j => o (s + j)) (cells.drop (4 * s)) := by
  intro j hj
  obtain ⟨h1, h2, h3⟩ := h (s + j) (by omega)
  refine ⟨h1, by rwa [mul_assoc, ← pow_add], fun c hc => ?_⟩
  have e : (cells.drop (4 * s)).getD (4 * j + c) 0 = cells.getD (4 * (s + j) + c) 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [show 4 * s + (4 * j + c) = 4 * (s + j) + c by ring]
  rw [e]
  exact h3 c hc

/-- `clU` over the big frames. -/
theorem clU_big {a q : ℕ} (hq : q ≤ a) : clU a q = 8 * q := by
  unfold clU; rw [Nat.min_eq_left hq]; omega

/-- `clU` after the big frames. -/
theorem clU_grp (a q : ℕ) : clU a (a + q) = 8 * a + q := by
  unfold clU; rw [Nat.min_eq_right (by omega)]; omega

/-! ## The last claims -/

/-- **`child_claim_list_last__L{k}` is complete, placed, within its frame**: the state at
`sp = g^sP`, the records' marks at `region · g^(os j)` and their cells among the caller's words. -/
theorem ccl_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) {k : ℕ} (hk : k < 17) {κ : ℕ}
    {Lin : Main.Layout} {sp entries region marks last : E} {sP eP rg L n : ℕ}
    {pre : List UInt8} {os : ℕ → ℕ} {cells : List E}
    (hsp : sp = gen ^ sP) (hen : entries = gen ^ eP) (hrg : region = gen ^ rg)
    (hpre : pre.length = rate * n) (hl : cells.length = 4 * k) (hc : AllCanonical cells)
    (hlast : last * gen = gen ^ L) (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ)
    (hmem : ∀ rd, MemL rd Lin → StateAt rd sp 0 (absorbChunks n zeroState pre) ∧
      RecMem rd region (gen ^ L) entries marks k os cells)
    (hR1 : ∀ o < 13, RegionL Lin (sP + o)) (hR2 : ∀ j < k, RegionL Lin (rg + os j))
    (hR3 : ∀ j < k, ∀ c < 4, RegionL Lin (eP + 4 * os j + c)) :
    CompleteAtDTB fs cert κ (cclNames.getD k "") Lin [sp, entries, region, marks, last]
      (Returns (digestCells (keccak256 (pre ++ cellsBytes cells)))) (fun _ => True)
      (fs (cclNames.getD k "")) := by
  intro fp
  refine ⟨fs (cclNames.getD k ""), [], _, [], le_rfl, ⟨rfl, rfl⟩, fun q hq => by simp at hq,
    B1.disj_nil, fun rd hlow hm => ?_⟩
  simp only [List.append_nil, List.nil_append] at hm
  obtain ⟨hS, hrec⟩ := hmem rd hm
  obtain ⟨vs, σ, hb, hp, hat, hr, hload⟩ := ccl_core hk hsp hen hrg hpre hS hl hc hrec hlast hL33
    (boundMem_of_low hlow hLκ)
  refine RelAtIn.relAtInT (relAtIn_atoms (ccl_name hk) hb (ccl_loop hk) (ccl_na hk) hp hat hr
    (fun q hq => by rw [ccl_addr hk] at hq; exact absurd hq List.not_mem_nil) (fun q hq => ?_)
    (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq))
  rcases hload q hq with ⟨o, ho, h⟩ | ⟨j, hj, h⟩ | ⟨j, hj, c, hc4, h⟩
  · exact ⟨_, h, Or.inl (hR1 o ho)⟩
  · exact ⟨_, h, Or.inl (hR2 j hj)⟩
  · exact ⟨_, h, Or.inl (hR3 j hj c hc4)⟩

/-- **`child_claim_list_last__L{k}` is complete, placed.** -/
theorem ccl_completeAt (fs : String → ℕ) (cert : String → V → ℕ) {k : ℕ} (hk : k < 17) {κ : ℕ}
    {Lin : Main.Layout} {sp entries region marks last : E} {sP eP rg L n : ℕ}
    {pre : List UInt8} {os : ℕ → ℕ} {cells : List E}
    (hsp : sp = gen ^ sP) (hen : entries = gen ^ eP) (hrg : region = gen ^ rg)
    (hpre : pre.length = rate * n) (hl : cells.length = 4 * k) (hc : AllCanonical cells)
    (hlast : last * gen = gen ^ L) (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ)
    (hmem : ∀ rd, MemL rd Lin → StateAt rd sp 0 (absorbChunks n zeroState pre) ∧
      RecMem rd region (gen ^ L) entries marks k os cells)
    (hR1 : ∀ o < 13, RegionL Lin (sP + o)) (hR2 : ∀ j < k, RegionL Lin (rg + os j))
    (hR3 : ∀ j < k, ∀ c < 4, RegionL Lin (eP + 4 * os j + c)) :
    CompleteAtD fs cert κ (cclNames.getD k "") Lin [sp, entries, region, marks, last]
      (Returns (digestCells (keccak256 (pre ++ cellsBytes cells)))) :=
  (ccl_completeAtB fs cert hk hsp hen hrg hpre hl hc hlast hL33 hLκ hmem hR1 hR2 hR3).toDT.toD

end
end LeanVM.Guest.B1.Digest
