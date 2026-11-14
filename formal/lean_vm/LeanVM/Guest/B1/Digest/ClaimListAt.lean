/-
  LeanVM.Guest.B1.Digest.ClaimListAt

  `claim_list_digest` in the uniform placed form: its chain buffer after its frame, holding the
  sponge states an honest run leaves, its callees after it; it reads the claims among its caller's
  words.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListComplete
public import LeanVM.Guest.B1.Digest.PlacedLib
public import LeanVM.Guest.B1.Main.NodeHonestAt
public import LeanVM.Guest.Data.NameStrings

/-!
# `claim_list_digest`, placed

The body is a branch on `n = 0` between two straight runs (`cl_body`). The empty list's arm is
atoms (`clz_core`: the evaluated valuation, its atoms holding). The nonempty list's arm
(`cl23Else_split`) calls `list_split`, allocates the chain buffer (`13 (m + 1)` words for
`n = 17 m + r`), stores the zero state, runs `claim_list_digest_loop0` over the groups when `m ≠ 0`,
and dispatches on `r` to `claim_list_last__L{r}` (`cl_core`: the evaluated valuation, its atoms
holding on a memory holding the zero state at the buffer). `chainCells`: the buffer's honest words,
the state after each group (`claimChainMem_of_reads`).

`claim_list_digest_completeAt`: for `n < 136 · 2^20` claims' cells at `g^eP` among the
caller's words `Lin`, `claim_list_digest` is `CompleteAtD` returning their digest's cells.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT KidsDT kidsFromInT_of_kidsDT Returns Kid DisjL Within
  disj_append completeAt_of_rel_pureD regionsOk_of within_append bufL bufL_within bufL_disj
  bufL_region LowDef)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)
open LeanVM.Guest.Budget (NodeHonest)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds exists_of_length_succ limb0_gen_pow_mul reads_of_memL
  regionL_of_mem)

@[expose] public section

/-! ## The path -/

/-- The nonempty arm before its dispatch. -/
noncomputable def clP1 : List Stmt := cl23Else.take 75

/-- The nonempty arm after its dispatch. -/
noncomputable def clPost : List Stmt := cl23Else.drop 76

set_option maxRecDepth 100000 in
theorem cl23Else_split :
    cl23Else = clP1 ++ clDispS :: clPost :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem clPost_eq : clPost = [.atom (.copy (.n 10) (.n 74)), .atom (.copy (.n 11) (.n 75))] :=
  stmtsEqb_sound (by decide +kernel)

theorem cl_body : Fn.body fn% «claim_list_digest» =
    clHead ++ .ite (.n 3) cl23Zero cl23Else :: (clTail ++ [.ret [.n 76, .n 77]]) := by
  rw [claim_list_digest_shape]; rfl

set_option maxRecDepth 100000 in
theorem clP1_straight : clP1.all Main.Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cl23Zero_straight : cl23Zero.all Main.Stmt.straight = true := by decide +kernel

theorem clHead_straight : clHead.all Main.Stmt.straight = true := rfl
theorem clTail_straight : clTail.all Main.Stmt.straight = true := rfl

set_option maxRecDepth 100000 in
theorem clP1_allocs : clP1.filterMap Main.Stmt.allocSz = [(.n 23, .inr (.n 22))] := by decide +kernel

set_option maxRecDepth 100000 in
theorem clP1_addrs : clP1.filterMap Main.Stmt.addrS = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem clP1_calls : clP1.filterMap Main.Stmt.callS =
    [(none, "list_split", [.n 1], [.n 12, .n 13, .n 14]),
      (some (.n 38), name% «claim_list_digest_loop0», [.n 39, .n 12, .n 23, .n 0], []),
      (some (.n 58), name% «claim_list_digest_loop1», [.n 59, .n 13, .n 45, .n 56],
          [])] := by decide +kernel

set_option maxRecDepth 100000 in
theorem clP1_loads : clP1.filterMap B1.Stmt.loadS = (List.range 13).map fun c => (.n 23, c) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cl23Zero_parts : cl23Zero.filterMap Main.Stmt.allocSz = [] ∧
    cl23Zero.filterMap Main.Stmt.addrS = [] ∧ cl23Zero.filterMap Main.Stmt.callS = [] ∧
    cl23Zero.filterMap B1.Stmt.loadS = [] := by decide +kernel

theorem cl_loop : coreProgram.loop "claim_list_digest" = false := by
  rw [Program.loop_of_find? find_claim_list_digest]; decide +kernel

/-! ## The valuations -/

/-- The empty list's valuation. -/
noncomputable def clzσ (rd : Reader) (entries : E) : Val :=
  B1.Val.ofArgs (ev rd (fun _ => 0) [entries, gen ^ 0] clZEval)

/-- The oracle of the nonempty list's valuation (`n = 136a + 17b + c`). -/
noncomputable def clw (a b c : ℕ) (chain : E) (D : Digest) (i : ℕ) : E :=
  if i = 12 then gen ^ a else if i = 13 then gen ^ b else if i = 14 then gen ^ c
  else if i = 23 then chain
  else if i = 10 ∨ i = 74 then (digestHalves D).1 else if i = 11 ∨ i = 75 then (digestHalves D).2
  else 0

/-- The nonempty list's valuation. -/
noncomputable def clσ (rd : Reader) (entries : E) (n : ℕ) (chain : E) (D : Digest) : Val :=
  B1.Val.ofArgs (ev rd (clw (n / 136) (n % 136 / 17) (n % 17) chain D) [entries, gen ^ n] clEEval)

variable {rd : Reader}

set_option maxRecDepth 20000 in
/-- **The empty list's valuation**: its atoms hold, it returns the empty string's digest. -/
theorem clz_core (entries : E) :
    (∀ a ∈ atomsIn clZEval, a.Holds rd (clzσ rd entries)) ∧ clzσ rd entries (.n 0) = entries ∧
      clzσ rd entries (.n 1) = gen ^ 0 ∧ clzσ rd entries (.n 3) = 0 ∧
      clzσ rd entries (.n 3) = gen ^ 0 + gen ^ 0 ∧
      [clzσ rd entries (.n 76), clzσ rd entries (.n 77)] =
        digestCells (keccak256 (cellsBytes [])) := by
  have hz1 := cz_ok
  have hb1 := clbr_ok
  simp only [czOk, Bool.and_eq_true, decide_eq_true_eq] at hz1
  simp only [clBrOk, Bool.and_eq_true] at hb1
  obtain ⟨⟨⟨-, hzc⟩, hz10⟩, hz11⟩ := hz1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, b12⟩, b13⟩, b15⟩, -⟩ := hb1
  have c2 : Stmt.atom (.const (.n 2) (word 1 0)) ∈ clHead := by simp [clHead]
  have a3 : Stmt.atom (.add (.n 3) (.n 1) (.n 2)) ∈ clHead := by simp [clHead]
  have t87 : Stmt.atom (.copy (.n 76) (.n 10)) ∈ clTail := by simp [clTail]
  have t88 : Stmt.atom (.copy (.n 77) (.n 11)) ∈ clTail := by simp [clTail]
  obtain ⟨c', hchk⟩ := Option.isSome_iff_exists.mp b12
  let args : List E := [entries, gen ^ 0]
  set σ := clzσ rd entries with hσ
  obtain ⟨-, -, hgs⟩ := ev_spec rd (fun _ => 0) clZEval args hchk
  rw [show args.length = 2 from rfl, List.isEmpty_iff.mp b13] at hgs
  have hg : ∀ a ∈ atomsIn clZEval, Good rd [] (fun _ => 0) σ a := fun a ha =>
    hgs _ (cl_atom_mem ha)
  have hns : ∀ a ∈ atomsIn clZEval, needsSide a = false := by
    intro a ha
    have := List.all_eq_true.mp b15 a ha
    simpa using this
  have hat : ∀ a ∈ atomsIn clZEval, a.Holds rd σ :=
    atoms_holds hg fun a ha hn => absurd hn (by simp [hns a ha])
  have mH : ∀ s ∈ clHead, s ∈ clZEval := fun s hs => by unfold clZEval; simp [hs]
  have mZ : ∀ s ∈ cl23Zero, s ∈ clZEval := fun s hs => by unfold clZEval; simp [hs]
  have mT : ∀ s ∈ clTail, s ∈ clZEval := fun s hs => by unfold clZEval; simp [hs]
  have hatZ : ∀ a ∈ atomsIn cl23Zero, a.Holds rd σ := fun a ha =>
    hat a (cl_mem_atoms (mZ _ (cl_atom_mem ha)))
  have e0 : σ (.n 0) = entries := by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args])
  have e1 : σ (.n 1) = gen ^ 0 := by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args])
  have v2 : σ (.n 2) = word 1 0 := hat _ (cl_mem_atoms (mH _ c2))
  have v3 : σ (.n 3) = σ (.n 1) + σ (.n 2) := hat _ (cl_mem_atoms (mH _ a3))
  have v87 : σ (.n 76) = σ (.n 10) := hat _ (cl_mem_atoms (mT _ t87))
  have v88 : σ (.n 77) = σ (.n 11) := hat _ (cl_mem_atoms (mT _ t88))
  have h30 : σ (.n 3) = 0 := by
    rw [v3, v2, e1, word_one, pow_zero]; exact e_add_eq_zero_iff.mpr rfl
  have hd := chain_final hzc rfl hatZ (pre := []) (n := 0) rfl
    (fun c => (cellsOfState_zero false c).symm)
  rw [hz10, hz11, show List.take (czSpec.len / 16) (czSpec.vals σ) = [] by simp [czSpec],
    List.nil_append] at hd
  refine ⟨hat, e0, e1, h30, by rw [v3, v2, e1, word_one, pow_zero], ?_⟩
  rw [v87, v88, digestCells, ← hd]

/-- **What the nonempty list's valuation is** (`a = n / 136`, `b = n % 136 / 17`). -/
structure ClVals (rd : Reader) (σ : Val) (entries : E) (n : ℕ) (chain : E) (D : Digest) : Prop where
  atoms : ∀ a ∈ atomsIn clEEval, a.Holds rd σ
  v0 : σ (.n 0) = entries
  v1 : σ (.n 1) = gen ^ n
  v3 : σ (.n 3) = gen ^ n + gen ^ 0
  v10 : σ (.n 10) = (digestHalves D).1
  v11 : σ (.n 11) = (digestHalves D).2
  v23 : σ (.n 12) = gen ^ (n / 136)
  v24 : σ (.n 13) = gen ^ (n % 136 / 17)
  v25 : σ (.n 14) = gen ^ (n % 17)
  v33 : σ (.n 22) = gen ^ (13 * (n / 136 + n % 136 / 17 + 1))
  v34 : σ (.n 23) = chain
  v49 : σ (.n 38) = 1 + gen ^ (n / 136)
  v50 : σ (.n 39) = 1
  v56 : σ (.n 45) = chain * gen ^ (13 * (n / 136))
  v67 : σ (.n 56) = entries * gen ^ (544 * (n / 136))
  v69 : σ (.n 58) = 1 + gen ^ (n % 136 / 17)
  v70 : σ (.n 59) = 1
  v76 : σ (.n 65) = chain * gen ^ (13 * (n / 136 + n % 136 / 17))
  v84 : σ (.n 73) = entries * gen ^ (544 * (n / 136) + 68 * (n % 136 / 17))
  v85 : σ (.n 74) = (digestHalves D).1
  v86 : σ (.n 75) = (digestHalves D).2
  v87 : σ (.n 76) = (digestHalves D).1
  v88 : σ (.n 77) = (digestHalves D).2

set_option maxRecDepth 100000 in
theorem cl_size_atoms : ∀ a ∈ [Atom.mul (.n 15) (.n 12) (.n 13), .const (.n 16) (word 2 0),
    .mul (.n 17) (.n 15) (.n 16), .mul (.n 18) (.n 17) (.n 17), .mul (.n 19) (.n 18) (.n 17),
    .mul (.n 20) (.n 19) (.n 19), .mul (.n 21) (.n 20) (.n 20), .mul (.n 22) (.n 21) (.n 17)],
    a ∈ atomsIn clEEval := by
  decide +kernel

set_option maxRecDepth 20000 in
/-- **The nonempty list's valuation**: on a memory holding the zero state at the chain buffer. -/
theorem cl_core {entries chain : E} {n : ℕ} (D : Digest) (hz0 : StateAt rd chain 0 zeroState) :
    ClVals rd (clσ rd entries n chain D) entries n chain D := by
  have he1 := ce_ok
  have hb1 := clbr_ok
  simp only [ceOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at he1
  simp only [clBrOk, Bool.and_eq_true] at hb1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, h50⟩, h49⟩, h48⟩, h70⟩, h69⟩, h68⟩, -⟩, hm56⟩, hm67⟩,
    hm76⟩, hm84⟩, -⟩, -⟩ := he1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, -⟩, b7⟩, -⟩, -⟩, b10⟩, b11⟩, b12⟩, -⟩, -⟩, -⟩, -⟩ := hb1
  have hE := stmtsEqb_sound b1
  have c2 : Stmt.atom (.const (.n 2) (word 1 0)) ∈ clHead := by simp [clHead]
  have a3 : Stmt.atom (.add (.n 3) (.n 1) (.n 2)) ∈ clHead := by simp [clHead]
  have t87 : Stmt.atom (.copy (.n 76) (.n 10)) ∈ clTail := by simp [clTail]
  have t88 : Stmt.atom (.copy (.n 77) (.n 11)) ∈ clTail := by simp [clTail]
  set a := n / 136 with hadef
  set b := n % 136 / 17 with hbdef
  set c := n % 17 with hcdef
  set w := clw a b c chain D with hw
  have w23 : w 12 = gen ^ a := by rw [hw]; simp [clw]
  have w24 : w 13 = gen ^ b := by rw [hw]; simp [clw]
  have w25 : w 14 = gen ^ c := by rw [hw]; simp [clw]
  have w34 : w 23 = chain := by rw [hw]; simp [clw]
  have w10 : w 10 = (digestHalves D).1 := by rw [hw]; simp [clw]
  have w85 : w 74 = (digestHalves D).1 := by rw [hw]; simp [clw]
  have w11 : w 11 = (digestHalves D).2 := by rw [hw]; simp [clw]
  have w86 : w 75 = (digestHalves D).2 := by rw [hw]; simp [clw]
  obtain ⟨c', hchk⟩ := Option.isSome_iff_exists.mp b2
  let args : List E := [entries, gen ^ n]
  set σ := clσ rd entries n chain D with hσ
  obtain ⟨-, -, hgs⟩ := ev_spec rd w clEEval args hchk
  rw [show args.length = 2 from rfl] at hgs
  set SE := storesOf 2 clEEval with hSE
  have hg : ∀ a ∈ atomsIn clEEval, Good rd SE w σ a := fun a ha => hgs _ (cl_atom_mem ha)
  have mH : ∀ s ∈ clHead, s ∈ clEEval := fun s hs => by unfold clEEval; simp [hs]
  have mP : ∀ s ∈ clElsePre, s ∈ clEEval := fun s hs => by unfold clEEval; simp [hs]
  have mT : ∀ s ∈ clTail, s ∈ clEEval := fun s hs => by unfold clEEval; simp [hs]
  have mF : ∀ i < 8, Stmt.atom (.hint (.alloc (.n (4 + i)) 0)) ∈ clEEval := fun i hi => by
    unfold clEEval
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩)))
  have e0 : σ (.n 0) = entries := by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args])
  have e1 : σ (.n 1) = gen ^ n := by
    rw [hσ]; exact ev_params rd _ (l := args) hchk (by simp [args])
  have v34 : σ (.n 23) = chain := by
    obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp b12
    have hga := hg a (cl_mem_atoms (mP _ (cl_atom_mem ha)))
    cases a with
    | hint h =>
      cases h with
      | allocDyn d s =>
        simp only [decide_eq_true_eq] at hp
        subst hp
        have hga' : σ (.n 23) = w 23 := hga
        rw [hga', w34]
      | _ => simp at hp
    | _ => simp at hp
  have v35 : ∀ c < 13, σ (.n (24 + c)) = 0 := by
    intro c hc'
    obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp (List.all_eq_true.mp b11 c (List.mem_range.mpr hc'))
    have hga := hg a (cl_mem_atoms (mP _ (cl_atom_mem ha)))
    cases a <;> simp only [isConstAt, Bool.false_eq_true, Bool.and_eq_true,
      decide_eq_true_eq] at hp
    obtain ⟨rfl, he⟩ := hp
    have hga' : σ (.n (24 + c)) = _ := hga
    rw [hga', eEqb_sound he, word_zero]
  have hat : ∀ a ∈ atomsIn clEEval, a.Holds rd σ := by
    refine atoms_holds_stores hg (fun a ha hnS hns => ?_) (fun _ a ha haS => ?_)
    · have := List.all_eq_true.mp b4 a ha
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
      rcases this with h | h
      · rw [hns] at h; exact absurd h (by simp)
      · exact absurd h hnS
    · obtain ⟨c, hc', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp b3 a haS)
      rw [atomEqb_sound he]
      have hc13 := List.mem_range.mp hc'
      show LoadHolds rd (σ (.n 23)) c (σ (.n (24 + c)))
      rw [v34, v35 c hc13]
      have := hz0 ⟨c, hc13⟩
      rwa [Nat.zero_add, cellsOfState_zero] at this
  have hdisp : clDispS ∈ clElsePre := by
    obtain ⟨s, hs, he⟩ := List.any_eq_true.mp b10; rwa [stmtEqb_sound he] at hs
  have hcall : clSplitS ∈ clElsePre := by
    obtain ⟨s, hs, he⟩ := List.any_eq_true.mp b7; rwa [stmtEqb_sound he] at hs
  have gd : ∀ v ∈ [V.n 74, V.n 75], σ v = w v.idx := hgs _ (mP _ hdisp)
  have gc : ∀ v ∈ [V.n 12, V.n 13, V.n 14], σ v = w v.idx := hgs _ (mP _ hcall)
  have v85 : σ (.n 74) = (digestHalves D).1 := (gd _ (by simp)).trans w85
  have v86 : σ (.n 75) = (digestHalves D).2 := (gd _ (by simp)).trans w86
  have v23 : σ (.n 12) = gen ^ a := (gc _ (by simp)).trans w23
  have v24 : σ (.n 13) = gen ^ b := (gc _ (by simp)).trans w24
  have v25 : σ (.n 14) = gen ^ c := (gc _ (by simp)).trans w25
  have v10 : σ (.n 10) = (digestHalves D).1 := by
    have : σ (.n 10) = w 10 := hgs _ (mF 6 (by omega))
    rw [this, w10]
  have v11 : σ (.n 11) = (digestHalves D).2 := by
    have : σ (.n 11) = w 11 := hgs _ (mF 7 (by omega))
    rw [this, w11]
  have hatElse : ∀ a ∈ atomsIn cl23Else, a.Holds rd σ := by
    intro a ha
    have hs := cl_atom_mem ha
    rw [hE] at hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hat a (cl_mem_atoms (mP _ hs))
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at hs
      rcases hs with rfl | rfl
      · show σ (.n 10) = σ (.n 74); rw [v10, v85]
      · show σ (.n 11) = σ (.n 75); rw [v11, v86]
  have v50 : σ (.n 39) = 1 := by rw [const_sound h50 hatElse, word_one]
  have v49 : σ (.n 38) = 1 + gen ^ a := by
    rw [add_sound h49 hatElse, const_sound h48 hatElse, word_one, v23]
  have v70 : σ (.n 59) = 1 := by rw [const_sound h70 hatElse, word_one]
  have v69 : σ (.n 58) = 1 + gen ^ b := by
    rw [add_sound h69 hatElse, const_sound h68 hatElse, word_one, v24]
  have v56 : σ (.n 45) = chain * gen ^ (13 * a) := by
    rw [monoIs_sound hm56 hatElse, v34, v23, gen_pow_pow]
  have v67 : σ (.n 56) = entries * gen ^ (544 * a) := by
    rw [monoIs_sound hm67 hatElse, e0, v23, gen_pow_pow]
  have v76 : σ (.n 65) = chain * gen ^ (13 * (a + b)) := by
    rw [mono2Is_sound hm76 hatElse, v34, v23, v24, gen_pow_pow, gen_pow_pow, mul_assoc, ← pow_add,
      Nat.mul_add]
  have v84 : σ (.n 73) = entries * gen ^ (544 * a + 68 * b) := by
    rw [mono2Is_sound hm84 hatElse, e0, v23, v24, gen_pow_pow, gen_pow_pow, mul_assoc, ← pow_add]
  have v2 : σ (.n 2) = word 1 0 := hat _ (cl_mem_atoms (mH _ c2))
  have v3 : σ (.n 3) = σ (.n 1) + σ (.n 2) := hat _ (cl_mem_atoms (mH _ a3))
  have v87 : σ (.n 76) = σ (.n 10) := hat _ (cl_mem_atoms (mT _ t87))
  have v88 : σ (.n 77) = σ (.n 11) := hat _ (cl_mem_atoms (mT _ t88))
  have hs := cl_size_atoms
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hs
  obtain ⟨s26, s27, s28, s29, s30, s31, s32, s33⟩ := hs
  have q26 : σ (.n 15) = σ (.n 12) * σ (.n 13) := hat _ s26
  have q27 : σ (.n 16) = word 2 0 := hat _ s27
  have q28 : σ (.n 17) = σ (.n 15) * σ (.n 16) := hat _ s28
  have q29 : σ (.n 18) = σ (.n 17) * σ (.n 17) := hat _ s29
  have q30 : σ (.n 19) = σ (.n 18) * σ (.n 17) := hat _ s30
  have q31 : σ (.n 20) = σ (.n 19) * σ (.n 19) := hat _ s31
  have q32 : σ (.n 21) = σ (.n 20) * σ (.n 20) := hat _ s32
  have q33 : σ (.n 22) = σ (.n 21) * σ (.n 17) := hat _ s33
  refine ⟨hat, e0, e1, by rw [v3, v2, e1, word_one, pow_zero], v10, v11, v23, v24, v25, ?_, v34,
    v49, v50, v56, v67, v69, v70, v76, v84, v85, v86, by rw [v87, v10], by rw [v88, v11]⟩
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
theorem cl_pure_all : ∀ k < 17,
    Stmt.pureList [clNames.getD k ""] (coreProgram.getD (idx% «claim_list_last__L0» + k)
        default).body = true := by
  decide +kernel

theorem cl_pure {r : ℕ} (hr : r < 17) : coreProgram.PureIn [clNames.getD r ""] :=
  pure_one (find_of_idx (cl_idx r hr)) (cl_pure_all r hr)

set_option maxRecDepth 100000 in
theorem big_pure : coreProgram.PureIn [name% «claim_list_digest_loop0»] :=
  pure_one (find_of_idx big_idx) (by decide +kernel)

set_option maxRecDepth 100000 in
theorem grp_pure : coreProgram.PureIn [name% «claim_list_digest_loop1»] :=
  pure_one (find_of_idx grp_idx) (by decide +kernel)

theorem one_add_gen_ne {a : ℕ} (ha : a < 2 ^ 64 - 1) : ((1 : E) + gen ^ a ≠ 0) ↔ a ≠ 0 := by
  rw [Ne, e_add_eq_zero_iff, eq_comm, gen_pow_eq_one_iff ha]

theorem clElsePre_eq : clElsePre = clP1 ++ [clDispS] := by
  rw [clElsePre, cl23Else_split, clPost_eq]; simp

set_option maxRecDepth 100000 in
theorem clP1_kinds : clP1.all (fun s => isAtomS s || stmtEqb s clSplitS || stmtEqb s clBigS ||
    stmtEqb s clGrpS) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cl23Zero_atoms : cl23Zero.all isAtomS = true := by decide +kernel

theorem slOk_atomS {rd : Reader} {σ : Val} {s : Stmt} (hs : isAtomS s = true)
    (h : ∀ a, s = .atom a → a.Holds rd σ) : SlOk rd σ s := by
  cases s <;> simp only [isAtomS, Bool.false_eq_true] at hs
  exact h _ rfl

/-! ## The honest shape -/

/-- `claim_list_digest`'s words that end its loops and size its buffer (`n = 136a + 17b + c`):
the count at `v1`; when `n ≠ 0`, `list_split`'s returns at `v23`, `v24`, `v25` (the first two end
`claim_list_digest_loop0`, `claim_list_digest_loop1`), the chain buffer's size `g^(13 (a + b + 1))`
at `v33`, the loops' start
`1` at `v50`, `v70`. -/
def clQ (n : ℕ) (σ : Val) : Prop :=
  σ (.n 1) = gen ^ n ∧ (n ≠ 0 → σ (.n 12) = gen ^ (n / 136) ∧ σ (.n 13) = gen ^ (n % 136 / 17) ∧
    σ (.n 14) = gen ^ (n % 17) ∧ σ (.n 22) = gen ^ (13 * (n / 136 + n % 136 / 17 + 1)) ∧
    σ (.n 39) = 1 ∧ σ (.n 59) = 1)

/-- `claim_list_digest`'s calls: none for the empty list; `list_split`, `claim_list_digest_loop0`
when
`n / 136 ≠ 0`, `claim_list_digest_loop1` when `n % 136 / 17 ≠ 0`, `claim_list_last__L{n % 17}`. -/
def clCalls (n : ℕ) (_ : Val) : List Call :=
  if n = 0 then [] else
    [⟨"list_split", [.n 1], [.n 12, .n 13, .n 14], true⟩,
      ⟨name% «claim_list_digest_loop0», [.n 39, .n 12, .n 23, .n 0], [], decide (n / 136 ≠ 0)⟩,
      ⟨name% «claim_list_digest_loop1», [.n 59, .n 13, .n 45, .n 56], [],
          decide (n % 136 / 17 ≠ 0)⟩,
      ⟨clNames[n % 17]!, [.n 65, .n 73], [.n 74, .n 75], true⟩]

/-- The claim list's `HeapBuf`: the chain buffer (none for the empty list). -/
def clBufs (n : ℕ) (_ : Val) : List ℕ :=
  if n = 0 then [] else [13 * (n / 136 + n % 136 / 17 + 1)]

/-- No constraint on the claim list's callees. -/
def clTs : List (Tree → Prop) := [fun _ => True, fun _ => True, fun _ => True, fun _ => True]

set_option maxRecDepth 20000 in
/-- **`claim_list_digest` is complete, placed, by a tree of honest shape**: `n < 136 · 2^20`
claims' cells at `g^eP` among the caller's words, its chain buffer after its frame
holding the states after each frame; it returns their digest's cells. -/
theorem claim_list_digest_completeAtT (fs : String → ℕ) (cert : String → V → ℕ) {Lin : Main.Layout}
    {eP n : ℕ} {cells : List E} (hn : n < claimBig * bigFramesCap) (hl : cells.length = 4 * n)
    (hLe : ∀ rd, MemL rd Lin → ReadsAt rd (gen ^ eP) cells)
    (hLr : ∀ k < cells.length, RegionL Lin (eP + k)) :
    CompleteAtDT fs cert 20 "claim_list_digest" Lin [gen ^ eP, gen ^ n]
      (Returns (digestCells (keccak256 (cellsBytes cells))))
      (NodeHonest coreProgram "claim_list_digest" (clQ n) (clCalls n) (clBufs n) clTs) := by
  intro fp
  simp only [claimBig, bigFramesCap] at hn
  have mH : ∀ s ∈ clHead, isAtomS s = true := by decide
  have mTl : ∀ s ∈ clTail, isAtomS s = true := by decide
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · -- the empty list
    have hcl : cells = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hcl
    refine ⟨fs "claim_list_digest", [], _, [], ⟨rfl, rfl⟩, fun q hq => by simp at hq, B1.disj_nil,
      fun rd hlow hm => ?_⟩
    obtain ⟨hat, e0, e1, h30, h3, hret⟩ := clz_core (rd := rd) (gen ^ eP)
    set σ := clzσ rd (gen ^ eP) with hσ
    have hb : (if σ (.n 3) = 0 then walk σ cl23Zero else walk σ cl23Else) =
        .fall (cl23Zero.flatMap (Main.slEvs σ)) := by
      simp only [h30, ↓reduceIte]; exact walk_straight_fall σ _ cl23Zero_straight
    have hw := walk_ite σ clTail clTail_straight (.n 3) cl23Zero cl23Else [.n 76, .n 77] _ hb
      clHead clHead_straight
    rw [← cl_body] at hw
    set es := clHead.flatMap (Main.slEvs σ) ++ .inK (.n 3) ::
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
      · show IsInK (σ (.n 3)); rw [h3]; exact gen_pow_add_isInK 0 0
      rcases List.mem_append.mp he with he | he
      · exact slEvs_holds (fun s hs => slOk_atomS (List.all_eq_true.mp cl23Zero_atoms s hs)
          (hmZ s (by simp [hs]))) e he
      · exact slEvs_holds (fun s hs => slOk_atomS (mTl s hs) (hmZ s (by simp [hs]))) e he
    obtain ⟨hhd, hha, hhad, hhc⟩ := Main.straight_parts σ _ clHead_straight
    obtain ⟨hzd, hza, hzad, hzc⟩ := Main.straight_parts σ _ cl23Zero_straight
    obtain ⟨htd, hta, htad, htc⟩ := Main.straight_parts σ _ clTail_straight
    obtain ⟨z1, z2, z3, z4⟩ := cl23Zero_parts
    have hal : allocs σ es = [] := by
      rw [hes, allocs_append, show allocs σ (.inK (.n 3) :: (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ))) = allocs σ (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ)) from rfl, allocs_append, hha, hza, hta, z1]
      rfl
    have h := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
      (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (N := 0) (fp := fp)
      (args := [gen ^ eP, gen ^ 0]) (rets := digestCells (keccak256 (cellsBytes [])))
      coreProgram_wf find_claim_list_digest (Or.inl cl_loop) (by rw [cl_param, e0, e1]) hw hret hev
      (by
        rw [hal, hes, allocDsts_append, show allocDsts (.inK (.n 3) :: (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ))) = allocDsts (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ)) from rfl, allocDsts_append, hhd, hzd, htd, z1]
        rfl)
      (fun q hq => by
        rw [hes, addrs_append, show addrs (.inK (.n 3) :: (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ))) = addrs (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ)) from rfl, addrs_append, hhad, hzad, htad, z2] at hq
        simp [clHead, clTail, Main.Stmt.addrS] at hq)
      clTs
      (by
        rw [hes, calls_append, show calls (.inK (.n 3) :: (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ))) = calls (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ)) from rfl, calls_append, hhc, hzc, htc, z3]
        exact ⟨rfl, fun _ h => h⟩)
      (fun A hA => by
        rw [hes, loadAddrs_append, show loadAddrs σ (.inK (.n 3) :: (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ))) = loadAddrs σ (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ)) from rfl, loadAddrs_append,
          B1.loadAddrs_straight σ _ clHead_straight, B1.loadAddrs_straight σ _ cl23Zero_straight,
          B1.loadAddrs_straight σ _ clTail_straight, z4] at hA
        simp [clHead, clTail, B1.Stmt.loadS] at hA)
      (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
    have hce : calls es = [] := by
      rw [hes, calls_append, show calls (.inK (.n 3) :: (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ))) = calls (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ)) from rfl, calls_append, hhc, hzc, htc, z3]
      rfl
    have h' := relAtInT_nodeHonest (Q := clQ 0) (cs := clCalls 0) (bs := clBufs 0) h
      find_claim_list_digest hw ⟨e1, fun h0 => absurd rfl h0⟩ (by rw [hce]; rfl) (by rw [hal]; rfl)
      (by simp [clCalls, clTs])
    rw [hal] at h'
    simpa using h'
  · -- a nonempty list
    set a := n / 136 with hadef
    set b := n % 136 / 17 with hbdef
    set r := n % 17 with hrdef
    have hnm : n = 136 * a + 17 * b + r := by omega
    have ha20 : a < 1048576 := by omega
    have hb8 : b < 8 := by omega
    have hr17 : r < 17 := Nat.mod_lt _ (by norm_num)
    set b0 := fp + fs "claim_list_digest" with hb0
    set chain : E := gen ^ b0 with hchain
    set Own : Main.Layout := [(b0, chainCells cells a b)] with hOwn
    set D := keccak256 (cellsBytes cells) with hD
    have hWo : Within Own b0 (13 * (a + b + 1)) := by
      intro q hq; simp only [hOwn, List.mem_singleton] at hq; subst hq
      simp [length_chainCells]
    have hDo : DisjL Own := List.pairwise_singleton _ _
    have hmOwn : ∀ rd, MemL rd Own → ReadsAt rd chain (chainCells cells a b) := fun rd hm =>
      reads_of_memL hm List.mem_cons_self
    -- the callees
    let ks : List Kid :=
      [⟨"list_split", true, [gen ^ n], [], Returns [gen ^ a, gen ^ b, gen ^ r]⟩,
        ⟨name% «claim_list_digest_loop0», decide (a ≠ 0), [1, gen ^ a, chain, gen ^ eP],
            Lin ++ Own, Returns []⟩,
        ⟨name% «claim_list_digest_loop1», decide (b ≠ 0), [1, gen ^ b, chain * gen ^ (13 * a),
            gen ^ eP * gen ^ (544 * a)],
          Lin ++ Own, Returns []⟩,
        ⟨clNames[r]!, true, [chain * gen ^ (13 * (a + b)), gen ^ eP * gen ^ (544 * a + 68 * b)],
          Lin ++ Own, Returns (digestCells D)⟩]
    have hok : ∀ k ∈ ks, k.taken = true → CompleteAtD fs cert 20 k.f k.Lin k.args k.Out := by
      intro k hk ht
      simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · have := list_split_completeAt fs cert (a := a) (b := b) (c := r) (by simp [bigFramesCap]; omega)
          (by simp [bigGroups]; omega) (by simp [claimGroup]; omega)
        rwa [show claimBig * a + claimGroup * b + r = n by simp [claimBig, claimGroup]; omega] at this
      · simp only [decide_eq_true_eq] at ht
        refine completeAt_of_rel_pureD big_pure (List.mem_singleton_self _) (fun rd hm => ?_) 20
        have hr := hLe rd (memL_append.mp hm).1
        have hmem := claimChainMem_of_reads hl hr (hmOwn rd (memL_append.mp hm).2)
        exact (guard_complete (find_of_idx big_idx)
          (grpc_shapeF grpc_big) (cl_bigBlocks hl hr hmem)).2 ((one_add_gen_ne (by omega)).mpr ht)
      · simp only [decide_eq_true_eq] at ht
        refine completeAt_of_rel_pureD grp_pure (List.mem_singleton_self _) (fun rd hm => ?_) 20
        have hr := hLe rd (memL_append.mp hm).1
        have hmem := claimChainMem_of_reads hl hr (hmOwn rd (memL_append.mp hm).2)
        have := (guard_complete (find_of_idx grp_idx)
          (grpc_shapeF grpc_ok) (cl_grpBlocks hl hr hmem)).2 ((one_add_gen_ne (by omega)).mpr ht)
        exact this
      · show CompleteAtD fs cert 20 clNames[r]! (Lin ++ Own) _ _
        rw [clNames_get hr17]
        refine completeAt_of_rel_pureD (cl_pure hr17) (List.mem_singleton_self _) (fun rd hm => ?_) 20
        have hr := hLe rd (memL_append.mp hm).1
        have hS := state_of_reads (hmOwn rd (memL_append.mp hm).2) (le_refl (a + b))
        rw [clU_last] at hS
        have hpre : (cellsBytes (cells.take (68 * (8 * a + b)))).length = rate * (8 * (8 * a + b)) := by
          rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
          show 16 * (68 * (8 * a + b)) = 136 * (8 * (8 * a + b)); omega
        have := claimLast_complete hr17 hpre hS (cells := cells.drop (68 * (8 * a + b)))
          (by simp; omega) (readsAt_drop' hr _)
        rw [← cellsBytes_append, List.take_append_drop] at this
        rw [show 544 * a + 68 * b = 68 * (8 * a + b) by ring]
        exact this
    have hokT : KidsDT fs cert 20 ks clTs :=
      ⟨fun ht => (hok _ List.mem_cons_self ht).toT,
        fun ht => (hok _ (List.mem_cons_of_mem _ List.mem_cons_self) ht).toT,
        fun ht => (hok _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) ht).toT,
        fun ht => (hok _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ List.mem_cons_self))) ht).toT,
        trivial⟩
    obtain ⟨Nk, Lk, outs, hoo, hW, hD, -, hKids⟩ :=
      kidsFromInT_of_kidsDT (fs := fs) (cert := cert) 20 ks clTs hokT (b0 + 13 * (a + b + 1))
    have hl0 : outs.length = 4 := hoo.length
    obtain ⟨o1, t1, rfl, hl1⟩ := exists_of_length_succ hl0
    obtain ⟨o2, t2, rfl, hl2⟩ := exists_of_length_succ hl1
    obtain ⟨o3, t3, rfl, hl3⟩ := exists_of_length_succ hl2
    obtain ⟨o4, t4, rfl, hl4⟩ := exists_of_length_succ hl3
    obtain rfl := List.eq_nil_of_length_eq_zero hl4
    obtain ⟨h1, h2, h3, h4, -⟩ := hoo
    refine ⟨fs "claim_list_digest" + 13 * (a + b + 1) + Nk, Own ++ Lk, _, [], ⟨rfl, rfl⟩, ?_,
      by rw [List.nil_append]; exact disj_append hDo hD hWo hW le_rfl, fun rd hlow hm => ?_⟩
    · rw [List.nil_append, within_append]
      exact ⟨hWo.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
    simp only [List.nil_append] at hm
    obtain ⟨hm1, hLin'⟩ := memL_append.mp hm
    obtain ⟨hmO, hLk⟩ := memL_append.mp hm1
    have hch := hmOwn rd hmO
    have hz0 : StateAt rd chain 0 zeroState := by
      have := state_of_reads hch (Nat.zero_le (a + b))
      rw [Nat.mul_zero, pow_zero, mul_one, show clU a 0 = 0 by simp [clU]] at this
      exact this
    have hV := cl_core (rd := rd) (entries := gen ^ eP) (n := n) D hz0
    set σ := clσ rd (gen ^ eP) n chain D with hσ
    -- the path
    have h3ne : σ (.n 3) ≠ 0 := by
      rw [hV.v3, Ne, e_add_eq_zero_iff, pow_zero, gen_pow_eq_one_iff (by omega)]; omega
    have hx : σ (.n 14) = ofK (addressOfIndex r) := by rw [hV.v25, gen_pow_eq_ofK]
    have hb : (if σ (.n 3) = 0 then walk σ cl23Zero else walk σ cl23Else) =
        .fall (clP1.flatMap (Main.slEvs σ) ++ .call clNames[r]! [.n 65, .n 73] [.n 74, .n 75] ::
          clPost.flatMap (Main.slEvs σ)) := by
      simp only [h3ne, ↓reduceIte]
      rw [cl23Else_split]
      exact walk_dispatch_fall σ clP1 clPost clP1_straight (by rw [clPost_eq]; rfl) (.n 14) clNames
        [.n 65, .n 73] [.n 74, .n 75] (i := r) (by simp [clNames]; omega) (by simp [clNames]) hx
    have hw := walk_ite σ clTail clTail_straight (.n 3) cl23Zero cl23Else [.n 76, .n 77] _ hb
      clHead clHead_straight
    rw [← cl_body] at hw
    set es := clHead.flatMap (Main.slEvs σ) ++ .inK (.n 3) ::
      ((clP1.flatMap (Main.slEvs σ) ++ .call clNames[r]! [.n 65, .n 73] [.n 74, .n 75] ::
        clPost.flatMap (Main.slEvs σ)) ++ clTail.flatMap (Main.slEvs σ)) with hes
    have hmE : ∀ s ∈ clHead ++ clP1 ++ clTail, ∀ a, s = .atom a → a.Holds rd σ := by
      intro s hs a rfl
      refine hV.atoms a (cl_mem_atoms ?_)
      unfold clEEval
      rw [clElsePre_eq]
      simp only [List.mem_append] at hs ⊢
      rcases hs with (hs | hs) | hs <;> simp [hs]
    have hev : ∀ e ∈ es, e.Holds rd σ := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact slEvs_holds (fun s hs => slOk_atomS (mH s hs) (hmE s (by simp [hs]))) e he
      rcases List.mem_cons.mp he with rfl | he
      · show IsInK (σ (.n 3)); rw [hV.v3]; exact gen_pow_add_isInK n 0
      rcases List.mem_append.mp he with he | he
      · rcases List.mem_append.mp he with he | he
        · refine slEvs_holds (fun s hs => ?_) e he
          have hk := List.all_eq_true.mp clP1_kinds s hs
          simp only [Bool.or_eq_true] at hk
          rcases hk with ((hk | hk) | hk) | hk
          · exact slOk_atomS hk (hmE s (by simp [hs]))
          · rw [stmtEqb_sound hk]; trivial
          · rw [stmtEqb_sound hk]
            show IsInK (σ (.n 38)); rw [hV.v49, ← pow_zero gen]; exact gen_pow_add_isInK _ _
          · rw [stmtEqb_sound hk]
            show IsInK (σ (.n 58)); rw [hV.v69, ← pow_zero gen]; exact gen_pow_add_isInK _ _
        rcases List.mem_cons.mp he with rfl | he
        · trivial
        · refine slEvs_holds (fun s hs => ?_) e he
          rw [clPost_eq] at hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · show σ (.n 10) = σ (.n 74); rw [hV.v10, hV.v85]
          · show σ (.n 11) = σ (.n 75); rw [hV.v11, hV.v86]
      · exact slEvs_holds (fun s hs => slOk_atomS (mTl s hs) (hmE s (by simp [hs]))) e he
    obtain ⟨hhd, hha, hhad, hhc⟩ := Main.straight_parts σ _ clHead_straight
    obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ clP1_straight
    obtain ⟨hqd, hqa, hqad, hqc⟩ := Main.straight_parts σ _ (show clPost.all Main.Stmt.straight = true by rw [clPost_eq]; rfl)
    obtain ⟨htd, hta, htad, htc⟩ := Main.straight_parts σ _ clTail_straight
    have hpostA : clPost.filterMap Main.Stmt.allocSz = [] ∧ clPost.filterMap Main.Stmt.addrS = [] ∧
        clPost.filterMap Main.Stmt.callS = [] ∧ clPost.filterMap B1.Stmt.loadS = [] := by
      rw [clPost_eq]; exact ⟨rfl, rfl, rfl, rfl⟩
    have hal : allocs σ es = [13 * (a + b + 1)] := by
      rw [hes, es5_allocs, hha, hpa, hqa, hta, clP1_allocs, hpostA.1]
      simp only [clHead, clTail, List.filterMap_cons, List.filterMap_nil, Main.Stmt.allocSz,
        List.map_cons, List.map_nil, Sum.elim_inr, hV.v33,
        logG_gen_pow (show 13 * (n / 136 + n % 136 / 17 + 1) < 2 ^ 64 - 1 by omega), List.nil_append,
        List.append_nil]
      rfl
    have h49 : decide (σ (.n 38) ≠ 0) = decide (a ≠ 0) := by
      rw [hV.v49]; exact decide_eq_decide.mpr (one_add_gen_ne (by omega))
    have h69 : decide (σ (.n 58) ≠ 0) = decide (b ≠ 0) := by
      rw [hV.v69]; exact decide_eq_decide.mpr (one_add_gen_ne (by omega))
    have hcalls : calls es = [⟨"list_split", [.n 1], [.n 12, .n 13, .n 14], true⟩,
        ⟨name% «claim_list_digest_loop0», [.n 39, .n 12, .n 23, .n 0], [], decide (a ≠ 0)⟩,
        ⟨name% «claim_list_digest_loop1», [.n 59, .n 13, .n 45, .n 56], [], decide (b ≠ 0)⟩,
        ⟨clNames[r]!, [.n 65, .n 73], [.n 74, .n 75], true⟩] := by
      rw [hes, es5_calls, hhc, hpc, hqc, htc, clP1_calls, hpostA.2.2.1]
      simp only [List.map_cons, List.map_nil, Main.mkCall, h49, h69, clHead, clTail,
        List.filterMap_cons, List.filterMap_nil, Main.Stmt.callS, List.nil_append, List.cons_append,
        List.append_nil]
    have hown : ∀ i, b0 ≤ i → i < b0 + 13 * (a + b + 1) →
        ownData cert fp (fp + fs "claim_list_digest") "claim_list_digest" [13 * (a + b + 1)] es i :=
      fun i h1 h2 => Or.inl ⟨(13 * (a + b + 1), b0), List.Mem.head _, h1, h2⟩
    have h := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
      (R := RegionL Lin) (D := RegionL []) (fp := fp) (N := Nk)
      (args := [gen ^ eP, gen ^ n]) (rets := digestCells D)
      (Dk := fun i => (fun _ => False) i ∨ outRegion ks [o1, o2, o3, o4] i)
      coreProgram_wf find_claim_list_digest (Or.inl cl_loop) (by rw [cl_param, hV.v0, hV.v1]) hw
      (by show [σ (.n 76), σ (.n 77)] = _; rw [hV.v87, hV.v88]; rfl) hev
      (by
        rw [hal, hes, es5_allocDsts, hhd, hpd, hqd, htd, clP1_allocs, hpostA.1]
        simp only [List.map_cons, List.map_nil, clHead, clTail, List.filterMap_cons,
          List.filterMap_nil, Main.Stmt.allocSz, List.nil_append, List.append_nil, bases, hV.v34]
        rw [hchain, gen_pow_eq_ofK])
      (fun q hq => by
        rw [hes, es5_addrs, hhad, hpad, hqad, htad, clP1_addrs, hpostA.2.1] at hq
        simp [clHead, clTail, Main.Stmt.addrS] at hq)
      clTs ?_ ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
    · have h' := relAtInT_nodeHonest (Q := clQ n) (cs := clCalls n) (bs := clBufs n) h
        find_claim_list_digest hw ⟨hV.v1, fun _ => ⟨hV.v23, hV.v24, hV.v25, hV.v33, hV.v50, hV.v70⟩⟩
        (by rw [hcalls]; unfold clCalls; split <;> first | omega | rfl)
        (by rw [hal]; unfold clBufs; split <;> first | omega | rfl)
        (by unfold clCalls; split <;> simp [clTs])
      rw [hal] at h'
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at h'
      exact h'
    · rw [hcalls, hal]
      rw [List.sum_cons, List.sum_nil, Nat.add_zero]
      refine hKids rd σ _ _ _ ?_ hlow hLk ?_ (regionsOk_of fun k hk _ i hi => ?_)
      · refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl,
          fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, trivial⟩
        · show [σ (.n 1)] = _; rw [hV.v1]
        · rw [(h1 rfl).1]; show [σ (.n 12), σ (.n 13), σ (.n 14)] = _; rw [hV.v23, hV.v24, hV.v25]
        · show [σ (.n 39), σ (.n 12), σ (.n 23), σ (.n 0)] = _
          rw [hV.v50, hV.v23, hV.v34, hV.v0]
        · rename_i ht; rw [(h2 ht).1]; rfl
        · show [σ (.n 59), σ (.n 13), σ (.n 45), σ (.n 56)] = _
          rw [hV.v70, hV.v24, hV.v56, hV.v67]
        · rename_i ht; rw [(h3 ht).1]; rfl
        · show [σ (.n 65), σ (.n 73)] = _; rw [hV.v76, hV.v84]
        · rw [(h4 rfl).1]; show [σ (.n 74), σ (.n 75)] = _; rw [hV.v85, hV.v86]; rfl
      · intro q hq
        simp only [B1.Kid.lins, ks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.nil_append, List.mem_append, or_assoc] at hq
        rcases hq with hq | hq | hq | hq | hq | hq <;> first | exact hLin' q hq | exact hmO q hq
      · simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl
        · obtain ⟨q, hq, -⟩ := hi; simp at hq
        all_goals
          obtain ⟨q, hq, h1', h2'⟩ := hi
          rcases List.mem_append.mp hq with hq | hq
          · exact Or.inl (Or.inl ⟨q, hq, h1', h2'⟩)
          · simp only [hOwn, List.mem_singleton] at hq
            subst hq
            simp only [length_chainCells] at h2'
            exact Or.inl (Or.inr (hown i h1' h2'))
    · intro A hA
      rw [hes, es5_loads, B1.loadAddrs_straight σ _ clHead_straight,
        B1.loadAddrs_straight σ _ clP1_straight,
        B1.loadAddrs_straight σ _ (show clPost.all Main.Stmt.straight = true by rw [clPost_eq]; rfl),
        B1.loadAddrs_straight σ _ clTail_straight, clP1_loads, hpostA.2.2.2] at hA
      simp only [clHead, clTail, List.filterMap_cons, List.filterMap_nil, B1.Stmt.loadS,
        List.map_nil, List.nil_append, List.append_nil, List.map_map, List.mem_map,
        List.mem_range, Function.comp] at hA
      obtain ⟨c, hc13, rfl⟩ := hA
      refine ⟨b0 + c, by rw [hV.v34, hchain, limb0_gen_pow_mul], Or.inl ?_⟩
      rw [hal]
      exact hown _ (by omega) (by omega)

/-- **`claim_list_digest` is complete, placed**: `n < 136 · 2^20` claims' cells at `g^eP`
among the caller's words, its chain buffer after its frame; it returns their digest's cells. -/
theorem claim_list_digest_completeAt (fs : String → ℕ) (cert : String → V → ℕ) {Lin : Main.Layout}
    {eP n : ℕ} {cells : List E} (hn : n < claimBig * bigFramesCap) (hl : cells.length = 4 * n)
    (hLe : ∀ rd, MemL rd Lin → ReadsAt rd (gen ^ eP) cells)
    (hLr : ∀ k < cells.length, RegionL Lin (eP + k)) :
    CompleteAtD fs cert 20 "claim_list_digest" Lin [gen ^ eP, gen ^ n]
      (Returns (digestCells (keccak256 (cellsBytes cells)))) :=
  (claim_list_digest_completeAtT fs cert hn hl hLe hLr).toD

end
end LeanVM.Guest.B1.Digest
