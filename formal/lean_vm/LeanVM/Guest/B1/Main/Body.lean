/-
  LeanVM.Guest.B1.Main.Body

  `main`'s body: its shape and its facts checked by evaluation.
-/

module

public import LeanVM.Guest.B1.Main.Loops
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main»

/-!
# `main`'s body

`fn% «main»`'s body is a flat block (`mPre`: the counts, the coverage table's size and their
checks (`assert_gpow`, a load through each; range checks for the children and the direct DA check), the exponent
tables, the claim list digests, the byte table, the raw signatures' loops, `da_digests`), the
direct DA check behind `n_direct_da == g` (`mDa`: `da_verify`, then its claim's digest stored at
`own_da`) or the zero digest stored there (`mDaZ`), a flat block (`mMid`: the children's loop, the
final count, `da_pick` and its two checks), the leaf's deferred claim or the batching behind
`n_children == 1` (`mLeaf`, `mAgg`), and a flat block (`mPost`: the statement's digest against
the public input) (`main_shape`). `preOk`, `daOk`, `daZOk`, `midOk`, `leafOk`, `postOk` check
every fact the proof reads, by evaluation.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-! ## The shape -/

noncomputable def mPre : List Stmt := (Fn.body fn% «main»).take (pos% «main» "root_0")
noncomputable def mDa : List Stmt := match (Fn.body fn% «main»).getD (pos% «main» "root_0") default with
  | .ite _ z _ => z
  | _ => []
noncomputable def mDaZ : List Stmt := match (Fn.body fn% «main»).getD (pos% «main» "root_0") default with
  | .ite _ _ n => n
  | _ => []
noncomputable def mMid : List Stmt := ((Fn.body fn% «main»).drop (pos% «main» "child_pi")).take (span% «main» "child_pi" "leaf_value")
noncomputable def mLeaf : List Stmt := match (Fn.body fn% «main»).getD (pos% «main» "leaf_value") default with
  | .ite _ z _ => z
  | _ => []
noncomputable def mAgg : List Stmt := match (Fn.body fn% «main»).getD (pos% «main» "leaf_value") default with
  | .ite _ _ n => n
  | _ => []
noncomputable def mPost : List Stmt := ((Fn.body fn% «main»).drop (pos% «main» "own_0~2")).dropLast

set_option maxRecDepth 100000 in
theorem main_shape : Fn.body fn% «main» =
    mPre ++ [.ite (.n (val% «main» "s50#1")) mDa mDaZ] ++ mMid ++ [.ite (.n (val% «main» "s63#1")) mLeaf mAgg] ++ mPost ++ [.ret []] :=
  stmtsEqb_sound (by decide +kernel)

/-! ## The facts, by evaluation -/

/-- `a == b` is asserted. -/
def isAssertEqAt (a b : V) : Atom → Bool
  | .assertEq x y => decide (x = a) && decide (y = b)
  | _ => false

theorem assertEq_sound {rd : Reader} {σ : Val} {atoms : List Atom} {a b : V}
    (h : atoms.any (isAssertEqAt a b) = true) (hat : ∀ x ∈ atoms, x.Holds rd σ) : σ a = σ b := by
  obtain ⟨x, hp, hx⟩ := any_holds h hat
  cases x <;> simp only [isAssertEqAt, Bool.false_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  exact e_add_eq_zero_iff.mp hx

/-- `x` is range-checked against `b` itself (`assert log x < log (b · g)`, the bound built
directly). -/
theorem rcDir_sound {rd : Reader} (hm : MemOk rd) {σ : Val} {atoms : List Atom} {x b : V}
    (h : decide (rcOf atoms x = some b) = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    ∃ e, σ x = gen ^ e ∧ BelowLog (σ b * gen) e := by
  obtain ⟨y, t1, t2, h1, h2, h3⟩ := rcOf_sound (of_decide_eq_true h) hat
  obtain ⟨e, e', he, he', hx, hk⟩ := rc_sound hm ⟨h1, h2, h3⟩
  exact ⟨e, hx, he, e', he', by rw [hk, ← pow_succ]⟩

/-- `lx_tags` (lean_ethereum.py): the `LX_N_TAGS = 51` constants `.n 318 ..< .n 369`,
the carried chain indices, passed whole to `main_loop2` after its four parameters. -/
def lxTagsV : List V := (List.range 51).map fun j => .n ((val% «main» "lx_tags[0]") + j)

/-- The chain indices `lx_tags` holds, by slot: the carried indices below `LX_V = 58` (neither `0`
nor a power of two), in increasing order (`LX_TAG_SLOT`). -/
def lxTagVals : List ℕ := (List.range 58).filter Sig.lxTagCarried

/-- `lx_tags`' words. -/
def lxTagWords : List E := lxTagVals.map fun i => word i 0

noncomputable def preOk : Bool :=
  let P := mPre
  let A := atomsIn mPre
  P.all Stmt.flat &&
  ((List.range 6).all fun v => isTouch A (.n ((val% «main» "s10#0") + v)) (.n v)) &&
  rcConstOk A (.n (val% «main» "meta[6]")) 65536 && rcConstOk A (.n (val% «main» "meta[7]")) 2 &&
  isTouch A (.n (val% «main» "s21#0")) (.n (val% «main» "n_total_g")) &&
  isMul A (.n (val% «main» "lx_slots_g")) (.n (val% «main» "meta[0]")) (.n (val% «main» "meta[1]")) && isMul A (.n (val% «main» "lean_sphincs_slots_g")) (.n (val% «main» "meta[3]")) (.n (val% «main» "meta[4]")) &&
  isMul A (.n (val% «main» "n_total_g")) (.n (val% «main» "lx_slots_g")) (.n (val% «main» "lean_sphincs_slots_g")) &&
  hasCall P "exponent_tables" [] [.n (val% «main» "g_squares")] &&
  hasCall P "claim_list_digest" [.n (val% «main» "lx_table"), .n (val% «main» "meta[0]")] [.n (val% «main» "xd_0"), .n (val% «main» "xd_1")] &&
  hasCall P "claim_list_digest" [.n (val% «main» "lean_sphincs_table"), .n (val% «main» "meta[3]")] [.n (val% «main» "sd_0"), .n (val% «main» "sd_1")] &&
  ((List.range 256).all fun v => A.any (isConstAt (.n ((val% «main» "s43.u0.s0#0") + v)) v 0) &&
    A.any (isLoadAt (.n ((val% «main» "s43.u0.s0#0") + v)) (.n (val% «main» "byte_bits")) v)) &&
  isMul A (.n (val% «main» "sp_cover")) (.n (val% «main» "cover")) (.n (val% «main» "lx_slots_g")) &&
  guardOk P (.n (val% «main» "s46#1")) name% «main_loop2» (.n (val% «main» "s46#2")) (.n (val% «main» "meta[2]")) ([.n (val% «main» "lx_slots_g"), .n (val% «main» "cover"), .n (val% «main» "lx_table")] ++ lxTagsV) &&
  ((List.range 58).all fun i => !Sig.lxTagCarried i ||
    A.any (isConstAt (.n ((val% «main» "lx_tags[0]") + (Sig.lxTagSlot i - 1))) i 0)) &&
  guardOk P (.n (val% «main» "s47#1")) name% «main_loop3» (.n (val% «main» "s47#2")) (.n (val% «main» "meta[5]")) [.n (val% «main» "lean_sphincs_slots_g"), .n (val% «main» "sp_cover"), .n (val% «main» "meta[2]"), .n (val% «main» "lean_sphincs_table"), .n (val% «main» "byte_bits")] &&
  isMul A (.n (val% «main» "own_da~0")) (.n (val% «main» "meta[6]")) (.n (val% «main» "meta[6]")) && isMul A (.n (val% «main» "own_da")) (.n (val% «main» "da_digests")) (.n (val% «main» "own_da~0")) &&
  A.any (isAddAt (.n (val% «main» "s50#1")) (.n (val% «main» "meta[7]")) (.n (val% «main» "s50#0"))) && A.any (isConstAt (.n (val% «main» "s50#0")) 2 0)

noncomputable def daOk : Bool :=
  let D := mDa
  D.all Stmt.flat &&
  hasCall D "da_verify" [.n (val% «main» "byte_bits")] [.n (val% «main» "root_0"), .n (val% «main» "root_1"), .n (val% «main» "z")] &&
  (atomsIn D).any (isConstAt (.n (val% «main» "s50.t.s1#1[1]")) 0 0) &&
  pairHashOk (atomsIn D) (.n (val% «main» "root_0")) (.n (val% «main» "root_1")) (.n (val% «main» "z")) (.n (val% «main» "s50.t.s1#1[1]")) (.n (val% «main» "own_da"))

noncomputable def daZOk : Bool :=
  let A := atomsIn mDaZ
  mDaZ.all Stmt.flat &&
  A.any (isConstAt (.n (val% «main» "s50.e.s0#0")) 0 0) && isLoad A (.n (val% «main» "s50.e.s0#0")) (.n (val% «main» "own_da")) 0 &&
  A.any (isConstAt (.n (val% «main» "s50.e.s1#0")) 0 0) && isLoad A (.n (val% «main» "s50.e.s1#0")) (.n (val% «main» "own_da")) 1

noncomputable def midOk : Bool :=
  let M := mMid
  let A := atomsIn mMid
  M.all Stmt.flat &&
  isMul A (.n (val% «main» "s55#0")) (.n (val% «main» "meta[2]")) (.n (val% «main» "meta[5]")) && isLoad A (.n (val% «main» "s55#0")) (.n (val% «main» "written")) 0 &&
  guardOk M (.n (val% «main» "s56#1")) name% «main_loop4» (.n (val% «main» "s56#2")) (.n (val% «main» "meta[6]")) [.n (val% «main» "written"), .n (val% «main» "lx_table"), .n (val% «main» "cover"), .n (val% «main» "lx_slots_g"), .n (val% «main» "lean_sphincs_table"), .n (val% «main» "sp_cover"),
    .n (val% «main» "lean_sphincs_slots_g"), .n (val% «main» "child_carried"), .n (val% «main» "da_digests"), .n (val% «main» "fs_seed[0]"), .n (val% «main» "fs_seed[1]"), .n (val% «main» "child_pi"), .n (val% «main» "g_squares"), .n (val% «main» "child_fresh")] &&
  isMul A (.n (val% «main» "s57#0")) (.n (val% «main» "written")) (.n (val% «main» "meta[6]")) && isLoad A (.n (val% «main» "s57#1")) (.n (val% «main» "s57#0")) 0 &&
  A.any (isAssertEqAt (.n (val% «main» "s57#1")) (.n (val% «main» "n_total_g"))) &&
  decide (rcOf A (.n (val% «main» "da_pick")) = some (.n (val% «main» "meta[6]"))) &&
  A.any (isAddAt (.n (val% «main» "s60#0")) (.n (val% «main» "da_pick")) (.n (val% «main» "meta[6]"))) && A.any (isAddAt (.n (val% «main» "s60#2")) (.n (val% «main» "meta[7]")) (.n (val% «main» "s60#1"))) &&
  A.any (isConstAt (.n (val% «main» "s60#1")) 1 0) && isMul A (.n (val% «main» "s60#3")) (.n (val% «main» "s60#0")) (.n (val% «main» "s60#2")) &&
  A.any (isConstAt (.n (val% «main» "s60#4")) 0 0) && A.any (isAssertEqAt (.n (val% «main» "s60#3")) (.n (val% «main» "s60#4"))) &&
  isMul A (.n (val% «main» "da~0")) (.n (val% «main» "da_pick")) (.n (val% «main» "da_pick")) && isMul A (.n (val% «main» "da")) (.n (val% «main» "da_digests")) (.n (val% «main» "da~0")) &&
  A.any (isAddAt (.n (val% «main» "s63#1")) (.n (val% «main» "meta[6]")) (.n (val% «main» "s63#0"))) && A.any (isConstAt (.n (val% «main» "s63#0")) 1 0)

noncomputable def leafOk : Bool :=
  mLeaf.all Stmt.flat &&
  ((List.range 23).all fun k => (atomsIn mLeaf).any (isConstAt (.n ((val% «main» "s63.t.s1.u0.s0#0") + k)) 0 0) &&
    isLoad (atomsIn mLeaf) (.n ((val% «main» "s63.t.s1.u0.s0#0") + k)) (.n (val% «main» "defer_stmt")) k) &&
  isLoad (atomsIn mLeaf) (.n (val% «main» "leaf_value")) (.n (val% «main» "defer_stmt")) 23 &&
  mAgg.all Stmt.flat &&
  (atomsIn mAgg).any (isConstAt (.n (val% «main» "s63.e.s0#0")) 133823759239872512 0) &&
  isMul (atomsIn mAgg) (.n (val% «main» "s63.e.s0#1")) (.n (val% «main» "g_squares")) (.n (val% «main» "s63.e.s0#0")) &&
  hasCall mAgg "aggregate_claims" [.n (val% «main» "meta[6]"), .n (val% «main» "child_pi"), .n (val% «main» "child_fresh"), .n (val% «main» "child_carried"), .n (val% «main» "defer_stmt"), .n (val% «main» "s63.e.s0#1")] []

noncomputable def postOk : Bool :=
  let A := atomsIn mPost
  mPost.all Stmt.flat &&
  isLoad A (.n (val% «main» "own_0~2")) (.n (val% «main» "da")) 0 && isLoad A (.n (val% «main» "own_0~3")) (.n (val% «main» "da")) 1 &&
  hasCall mPost "statement_digest" [.n (val% «main» "fs_seed[0]"), .n (val% «main» "fs_seed[1]"), .n (val% «main» "xd_0"), .n (val% «main» "xd_1"), .n (val% «main» "sd_0"), .n (val% «main» "sd_1"), .n (val% «main» "own_0~2"), .n (val% «main» "own_0~3"), .n (val% «main» "defer_stmt")]
    [.n (val% «main» "own_0"), .n (val% «main» "own_1")] &&
  A.any (isConstAt (.n (val% «main» "s66#0")) 1 0) && isLoad A (.n (val% «main» "s66#1")) (.n (val% «main» "s66#0")) 0 &&
  A.any (isAssertEqAt (.n (val% «main» "s66#1")) (.n (val% «main» "own_0"))) &&
  A.any (isConstAt (.n (val% «main» "s67#0")) 2 0) && isLoad A (.n (val% «main» "s67#1")) (.n (val% «main» "s67#0")) 0 &&
  A.any (isAssertEqAt (.n (val% «main» "s67#1")) (.n (val% «main» "own_1")))

set_option maxRecDepth 100000 in
theorem pre_ok : preOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem da_ok : daOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem daZ_ok : daZOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem mid_ok : midOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem leaf_ok : leafOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem post_ok : postOk = true := by decide +kernel

end
end LeanVM.Guest.B1.Main
