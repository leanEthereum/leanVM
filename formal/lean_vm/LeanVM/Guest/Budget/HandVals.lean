/-
  LeanVM.Guest.Budget.HandVals

  The hand functions' virtual values on a valid tree: per hand function, what its path fixes of
  the values `hand.py` takes as virtual parameters, for the words' and the cycles' hand facts alike.
-/

module

public import LeanVM.Guest.Exact.Every
public import LeanVM.Guest.Memory.Straight
public import LeanVM.Guest.B1.Link.SqueezePacked
public import LeanVM.Guest.B1.Link.RoundsLoop
public import LeanVM.Guest.B1.Eq.RsEqRun
public import LeanVM.Guest.B1.Eq.RingRows
public import LeanVM.Guest.B1.Digest.ClaimList
public import LeanVM.Guest.B1.Digest.ChildDigest
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«claim_list_digest»
import LeanVM.Guest.Data.ValNames.«child_claim_list_digest»
import LeanVM.Guest.Data.ValNames.«rs_eq_run»
import LeanVM.Guest.Data.ValNames.«ring_rows»
import LeanVM.Guest.Value.FieldBits

/-!
# The hand functions' virtual values

A hand function's certificate (`Memory/StaticSound.lean`'s `Hand`, `HandFact`) reads values of its
body as further parameters. Their facts come from the node's path: its atoms hold and each call it
enters is related by `P.Rel` (`PathHolds`, on every node of a valid tree by
`every_pathHolds`). Per hand function, `<f>_vals` states what the path fixes of them, as
exponents of `g` (`GPow`), from which each family's certificate inequality follows by linear
arithmetic.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest
open LeanVM.Guest.B1 LeanVM.Guest.B1.Link LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-! ## Paths -/

/-- **A node's path holds**: its function's body holds at `σ` on `rd`, each call it enters
related by `P.Rel`. -/
def PathHolds (P : Core.Program) (rd : Reader) (f : String) (σ : Val) : Prop :=
  ∃ fn, P.find? f = some fn ∧ Stmt.HoldsList (P.Rel rd) rd σ fn.body True (fun _ => True)

variable {P : Core.Program} {rd : Reader}

theorem pathHolds_of_walk {f : String} {fn : Fn} (hf : P.find? f = some fn) {σ : Val} {es : List Ev}
    {vs : List V} (hw : walk σ fn.body = .ret es vs) (hes : ∀ e ∈ es, e.Holds rd σ)
    (hc : ∀ g a r, Ev.call g a r ∈ es → P.Rel rd g (a.map σ) (r.map σ)) : PathHolds P rd f σ :=
  ⟨fn, hf, holdsList_of_walk fn.body (by
    rw [hw]
    exact ⟨fun e he => ⟨hes e he, fun g a r hg => hc g a r (hg ▸ he)⟩, trivial⟩)⟩

mutual
/-- **Every node of a valid tree has its path holding.** -/
theorem every_pathHolds : ∀ (t : Tree) {args rets : List E}, t.Valid P rd args rets →
    t.Every (PathHolds P rd)
  | .node f σ _ kids, _, _, ⟨fn, hf, _, es, vs, hw, _, hes, hk⟩ => by
      rw [Tree.every_node]
      refine ⟨pathHolds_of_walk hf hw hes fun g a r hg => ?_, everyKids_pathHolds σ kids _ hk⟩
      exact Tree.KidsValid.rel σ kids (calls es) hk ⟨g, a, r, true⟩ (mem_calls_of_call hg) rfl
  | .phantom .., _, _, h => h.elim

/-- `every_pathHolds` for the callees. -/
theorem everyKids_pathHolds : ∀ (σ : Val) (ks : List Tree) (cs : List Call),
    Tree.KidsValid P rd σ cs ks → Tree.EveryKids (PathHolds P rd) ks
  | _, [], [], _ => by rw [Tree.EveryKids]; trivial
  | σ, k :: ks, c :: cs, ⟨_, hc, hks⟩ => by
      rw [Tree.EveryKids]
      refine ⟨?_, everyKids_pathHolds σ ks cs hks⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact every_pathHolds k hc
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
        exact Tree.every_phantom
  | _, _ :: _, [], h => h.elim
end

/-- A guest node's path, its body the generated one. -/
theorem pathHolds_body {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn) {σ : Val}
    (h : PathHolds coreProgram rd f σ) :
    Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body True (fun _ => True) := by
  obtain ⟨fn', hf', hh⟩ := h
  rw [hf] at hf'
  cases hf'
  exact hh

/-! ## Powers of `g` -/

/-- `w = g^e` with `e` below the order of `g`. -/
def GPow (w : E) (e : ℕ) : Prop := w = gen ^ e ∧ e < 2 ^ 64 - 1

theorem GPow.logG {w : E} {e : ℕ} (h : GPow w e) : Memory.logG w = e := by
  rw [h.1]; exact logG_gen_pow h.2

theorem GPow.ofK {w : E} {e : ℕ} (h : GPow w e) : w = ofK (addressOfIndex e) := by
  rw [h.1]; exact gen_pow_eq_ofK e

/-! ## `squeeze_packed` -/

/-- **`squeeze_packed`'s virtual value** `v40 = g^q`, its count `v6 = g^(4q + r)`, `r < 4`, `q < 16`. -/
theorem squeeze_packed_vals {σ : Val} (h : PathHolds coreProgram rd "squeeze_packed" σ) :
    ∃ q r, q < 16 ∧ r < 4 ∧ GPow (σ (.n 40)) q ∧ GPow (σ (.n 6)) (4 * q + r) := by
  have hb := pathHolds_body (coreProgram_find?_at (j := idx% «squeeze_packed») rfl) h
  rw [spMain_body] at hb
  simp only [spMainBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    true_and] at hb
  obtain ⟨b0, c13, c14, m15, a16, b1, c17, c18, m19, a20, m21, b2, c22, c23, m24, a25, b3, c26, c27, m28, a29,
    m30, b4, c31, c32, m33, a34, m35, b5, c36, c37, m38, a39, m40, m41, m42, m43, hassert, -⟩ := hb
  have w3 : word 3 0 = gen ^ 1 + 1 := word_two_pow_xor_one (a := 1) (by norm_num)
  have w5 : word 5 0 = gen ^ 2 + 1 := word_two_pow_xor_one (a := 2) (by norm_num)
  have w17 : word 17 0 = gen ^ 4 + 1 := word_two_pow_xor_one (a := 4) (by norm_num)
  have w257 : word 257 0 = gen ^ 8 + 1 := word_two_pow_xor_one (a := 8) (by norm_num)
  have hrg : σ (.n 21) = gen ^ (bv (σ (.n 7)) + 2 * bv (σ (.n 8))) := by
    rw [m21, a16, a20, m15, m19, c13, c14, c17, c18, w3, w5, word_one, bit_factor b0, bit_factor b1,
      ← pow_add]
    simp only [bv, one_mul]
  have hqg : σ (.n 40) = gen ^ (bv (σ (.n 9)) + 2 * bv (σ (.n 10)) + 4 * bv (σ (.n 11)) + 8 * bv (σ (.n 12))) := by
    rw [m40, m35, m30, a25, a29, a34, a39, m24, m28, m33, m38, c22, c23, c26, c27, c31, c32, c36, c37, w3, w5,
      w17, w257, word_one, bit_factor b2, bit_factor b3, bit_factor b4, bit_factor b5, ← pow_add, ← pow_add,
      ← pow_add]
    simp only [bv, one_mul]
  set rv := bv (σ (.n 7)) + 2 * bv (σ (.n 8)) with hrv
  set qv := bv (σ (.n 9)) + 2 * bv (σ (.n 10)) + 4 * bv (σ (.n 11)) + 8 * bv (σ (.n 12)) with hqv
  have hrv4 : rv < 4 := by have := bv_le (σ (.n 7)); have := bv_le (σ (.n 8)); omega
  have hqv16 : qv < 16 := by
    have := bv_le (σ (.n 9)); have := bv_le (σ (.n 10)); have := bv_le (σ (.n 11))
    have := bv_le (σ (.n 12)); omega
  have hcg : σ (.n 6) = gen ^ (4 * qv + rv) := by
    have : σ (.n 6) = σ (.n 43) := by linear_combination hassert.symm + σ (.n 6) * two_eq_zero_E
    rw [this, m43, m42, m41, hqg, hrg]
    ring
  exact ⟨qv, rv, hqv16, hrv4, ⟨hqg, by omega⟩, ⟨hcg, by omega⟩⟩

/-! ## `rs_eq_run`, `ring_rows` -/

/-- `rs_eq_run`'s virtual parameter is `q_g@3`. -/
theorem rs_eq_run_vp : val% «rs_eq_run» "q_g@3" = 37 ∧ val% «rs_eq_run» "count_g" = 2 := ⟨rfl, rfl⟩

/-- **`rs_eq_run`'s virtual value** `q_g = g^q`, its count `count_g = g^(8q + r)`, `q, r < 8`. -/
theorem rs_eq_run_vals {σ : Val} (h : PathHolds coreProgram rd "rs_eq_run" σ) :
    ∃ q r, q < 8 ∧ r < 8 ∧ GPow (σ (.n 37)) q ∧ GPow (σ (.n 2)) (8 * q + r) := by
  obtain ⟨w3, w5, w17⟩ := rs_consts
  have hb := pathHolds_body find_rs_eq_run h
  rw [rs_eq_run_body, rsBody] at hb
  simp only [rsA, rsAlloc, List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    true_and] at hb
  obtain ⟨b0, h10, h11, h12, h13, b1, h14, h15, h16, h17, h18, b2, h19, h20, h21, h22, h23,
    b3, h24, h25, h26, h27, b4, h28, h29, h30, h31, h32, b5, h33, h34, h35, h36, h37, h38, h39,
    h40, h41, ha, -⟩ := hb
  have hbr : ∀ j < 3, σ (.n ((val% «rs_eq_run» "bits[0]") + j)) * σ (.n ((val% «rs_eq_run» "bits[0]") + j)) = σ (.n ((val% «rs_eq_run» "bits[0]") + j)) := by
    intro j hj; interval_cases j
    exacts [b0.symm, b1.symm, b2.symm]
  have hbq : ∀ j < 3, σ (.n ((val% «rs_eq_run» "bits[3]") + j)) * σ (.n ((val% «rs_eq_run» "bits[3]") + j)) = σ (.n ((val% «rs_eq_run» "bits[3]") + j)) := by
    intro j hj; interval_cases j
    exacts [b3.symm, b4.symm, b5.symm]
  have rg : σ (.n (val% «rs_eq_run» "r_g@3")) = ∏ j ∈ Finset.range 3, (1 + σ (.n ((val% «rs_eq_run» "bits[0]") + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h23, h18, h13, h17, h22, h12, h16, h21, h10, h14, h19, h11, h15, h20, w3, w5, w17, word_one]
  have qg : σ (.n (val% «rs_eq_run» "q_g@3")) = ∏ j ∈ Finset.range 3, (1 + σ (.n ((val% «rs_eq_run» "bits[3]") + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h37, h32, h27, h31, h36, h26, h30, h35, h24, h28, h33, h25, h29, h34, w3, w5, w17, word_one]
  rw [prod_gen_pow_of_bool hbr] at rg
  rw [prod_gen_pow_of_bool hbq] at qg
  set r := bitsVal (fun j ↦ decide (σ (.n ((val% «rs_eq_run» "bits[0]") + j)) = 1)) 3 with hrdef
  set q := bitsVal (fun j ↦ decide (σ (.n ((val% «rs_eq_run» "bits[3]") + j)) = 1)) 3 with hqdef
  have hr8 : r < 8 := bitsVal_lt _ 3
  have hq8 : q < 8 := bitsVal_lt _ 3
  have hcg : σ (.n (val% «rs_eq_run» "count_g")) = gen ^ (8 * q + r) := by
    rw [← e_add_eq_zero_iff.mp ha, h41, h40, h39, h38, qg, rg, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add]
    congr 1; ring
  exact ⟨q, r, hq8, hr8, ⟨qg, by omega⟩, ⟨hcg, by omega⟩⟩

/-- `ring_rows`' virtual parameter is `q_g@3`. -/
theorem ring_rows_vp : val% «ring_rows» "q_g@3" = 102 ∧ val% «ring_rows» "count_g" = 4 := ⟨rfl, rfl⟩

/-- **`ring_rows`' virtual value** `q_g = g^q`, its count `count_g = g^(8q + r)`, `q, r < 8`. -/
theorem ring_rows_vals {σ : Val} (h : PathHolds coreProgram rd "ring_rows" σ) :
    ∃ q r, q < 8 ∧ r < 8 ∧ GPow (σ (.n 102)) q ∧ GPow (σ (.n 4)) (8 * q + r) := by
  obtain ⟨w3, w5, w17⟩ := rs_consts
  have hb := pathHolds_body find_ring_rows h
  rw [ring_rows_body, rgBody, holdsList_append, rgInits, holdsList_range_flatten 64 rgInit rgInit_noRet] at hb
  obtain ⟨-, hb⟩ := hb
  simp only [rgA, List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    true_and] at hb
  obtain ⟨b0, h10, h11, h12, h13, b1, h14, h15, h16, h17, h18, b2, h19, h20, h21, h22, h23,
    b3, h24, h25, h26, h27, b4, h28, h29, h30, h31, h32, b5, h33, h34, h35, h36, h37, h38, h39,
    h40, h41, ha, -⟩ := hb
  have hbr : ∀ j < 3, σ (.n ((val% «ring_rows» "bits[0]") + j)) * σ (.n ((val% «ring_rows» "bits[0]") + j)) = σ (.n ((val% «ring_rows» "bits[0]") + j)) := by
    intro j hj; interval_cases j
    exacts [b0.symm, b1.symm, b2.symm]
  have hbq : ∀ j < 3, σ (.n ((val% «ring_rows» "bits[3]") + j)) * σ (.n ((val% «ring_rows» "bits[3]") + j)) = σ (.n ((val% «ring_rows» "bits[3]") + j)) := by
    intro j hj; interval_cases j
    exacts [b3.symm, b4.symm, b5.symm]
  have rg : σ (.n (val% «ring_rows» "r_g@3")) = ∏ j ∈ Finset.range 3, (1 + σ (.n ((val% «ring_rows» "bits[0]") + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h23, h18, h13, h17, h22, h12, h16, h21, h10, h14, h19, h11, h15, h20, w3, w5, w17, word_one]
  have qg : σ (.n (val% «ring_rows» "q_g@3")) = ∏ j ∈ Finset.range 3, (1 + σ (.n ((val% «ring_rows» "bits[3]") + j)) * (gen ^ 2 ^ j + 1)) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [h37, h32, h27, h31, h36, h26, h30, h35, h24, h28, h33, h25, h29, h34, w3, w5, w17, word_one]
  rw [prod_gen_pow_of_bool hbr] at rg
  rw [prod_gen_pow_of_bool hbq] at qg
  set r := bitsVal (fun j ↦ decide (σ (.n ((val% «ring_rows» "bits[0]") + j)) = 1)) 3 with hrdef
  set q := bitsVal (fun j ↦ decide (σ (.n ((val% «ring_rows» "bits[3]") + j)) = 1)) 3 with hqdef
  have hr8 : r < 8 := bitsVal_lt _ 3
  have hq8 : q < 8 := bitsVal_lt _ 3
  have hcg : σ (.n (val% «ring_rows» "count_g")) = gen ^ (8 * q + r) := by
    rw [← e_add_eq_zero_iff.mp ha, h41, h40, h39, h38, qg, rg, ← pow_add, ← pow_add, ← pow_add,
      ← pow_add]
    congr 1; ring
  exact ⟨q, r, hq8, hr8, ⟨qg, by omega⟩, ⟨hcg, by omega⟩⟩

/-! ## `link_rounds__*` -/

/-- **`link_rounds`' virtual value** on its template: `v43 = g^q`, its count `v8 = g^(4q + r)`,
`r < 4`, `q < 16`. -/
theorem lr_vals {name loop : String} {lasts : List String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (hbody : fn.body = lrMainBody loop lasts) {σ : Val} (h : PathHolds coreProgram rd name σ) :
    ∃ q r, q < 16 ∧ r < 4 ∧ GPow (σ (.n 43)) q ∧ GPow (σ (.n 8)) (4 * q + r) := by
  have hb := pathHolds_body hf h
  rw [hbody] at hb
  simp only [lrMainBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    true_and] at hb
  obtain ⟨b0, c16, c17, m18, a19, b1, c20, c21, m22, a23, m24, b2, c25, c26, m27, a28, b3, c29, c30,
    m31, a32, m33, b4, c34, c35, m36, a37, m38, b5, c39, c40, m41, a42, m43, m44, m45, m46, hassert, -⟩ := hb
  have w3 : word 3 0 = gen ^ 1 + 1 := word_two_pow_xor_one (a := 1) (by norm_num)
  have w5 : word 5 0 = gen ^ 2 + 1 := word_two_pow_xor_one (a := 2) (by norm_num)
  have w17 : word 17 0 = gen ^ 4 + 1 := word_two_pow_xor_one (a := 4) (by norm_num)
  have w257 : word 257 0 = gen ^ 8 + 1 := word_two_pow_xor_one (a := 8) (by norm_num)
  have hrg : σ (.n 24) = gen ^ (bv (σ (.n 10)) + 2 * bv (σ (.n 11))) := by
    rw [m24, a19, a23, m18, m22, c16, c17, c20, c21, w3, w5, word_one, bit_factor b0, bit_factor b1,
      ← pow_add]
    simp only [bv, one_mul]
  have hqg : σ (.n 43) = gen ^ (bv (σ (.n 12)) + 2 * bv (σ (.n 13)) + 4 * bv (σ (.n 14)) + 8 * bv (σ (.n 15))) := by
    rw [m43, m38, m33, a28, a32, a37, a42, m27, m31, m36, m41, c25, c26, c29, c30, c34, c35, c39, c40, w3, w5,
      w17, w257, word_one, bit_factor b2, bit_factor b3, bit_factor b4, bit_factor b5, ← pow_add, ← pow_add,
      ← pow_add]
    simp only [bv, one_mul]
  set rv := bv (σ (.n 10)) + 2 * bv (σ (.n 11)) with hrv
  set qv := bv (σ (.n 12)) + 2 * bv (σ (.n 13)) + 4 * bv (σ (.n 14)) + 8 * bv (σ (.n 15)) with hqv
  have hrv4 : rv < 4 := by have := bv_le (σ (.n 10)); have := bv_le (σ (.n 11)); omega
  have hqv16 : qv < 16 := by
    have := bv_le (σ (.n 12)); have := bv_le (σ (.n 13)); have := bv_le (σ (.n 14))
    have := bv_le (σ (.n 15)); omega
  have hcg : σ (.n 8) = gen ^ (4 * qv + rv) := by
    have : σ (.n 8) = σ (.n 46) := by linear_combination hassert.symm + σ (.n 8) * two_eq_zero_E
    rw [this, m46, m45, m44, hqg, hrg]
    ring
  exact ⟨qv, rv, hqv16, hrv4, ⟨hqg, by omega⟩, ⟨hcg, by omega⟩⟩

/-- `link_rounds__{L1_L0, L6_L0, L7_L0, L8_L1, L9_L1, L10_L1}`, the link's round functions. -/
def LinkRoundsName (f : String) : Prop :=
  f = "link_rounds__L1_L0" ∨ f = "link_rounds__L6_L0" ∨ f = "link_rounds__L7_L0" ∨
    f = "link_rounds__L8_L1" ∨ f = "link_rounds__L9_L1" ∨ f = "link_rounds__L10_L1"

set_option maxRecDepth 100000 in
/-- **The link's round functions' virtual value**: `v43 = g^q`, their count `v8 = g^(4q + r)`. -/
theorem link_rounds_vals {f : String} (hf : LinkRoundsName f) {σ : Val} (h : PathHolds coreProgram rd f σ) :
    ∃ q r, q < 16 ∧ r < 4 ∧ GPow (σ (.n 43)) q ∧ GPow (σ (.n 8)) (4 * q + r) := by
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lr_vals (coreProgram_find?_at (j := idx% «link_rounds__L1_L0») rfl) lrMain_L1_L0_body h
  · exact lr_vals (coreProgram_find?_at (j := idx% «link_rounds__L6_L0») rfl) lrMain_L6_L0_body h
  · exact lr_vals (coreProgram_find?_at (j := idx% «link_rounds__L7_L0») rfl) lrMain_L7_L0_body h
  · exact lr_vals (coreProgram_find?_at (j := idx% «link_rounds__L8_L1») rfl) lrMain_L8_L1_body h
  · exact lr_vals (coreProgram_find?_at (j := idx% «link_rounds__L9_L1») rfl) lrMain_L9_L1_body h
  · exact lr_vals (coreProgram_find?_at (j := idx% «link_rounds__L10_L1») rfl) lrMain_L10_L1_body h

/-! ## `claim_list_digest`, `child_claim_list_digest`: `list_split`'s returns, on a nonempty list -/

theorem digest_vps : val% «claim_list_digest» "n_g" = 1 ∧ val% «claim_list_digest» "bigs" = 12 ∧
    val% «claim_list_digest» "groups" = 13 ∧ val% «claim_list_digest» "s1#1" = 3 ∧
    val% «child_claim_list_digest» "n_g" = 4 ∧ val% «child_claim_list_digest» "bigs" = 15 ∧
    val% «child_claim_list_digest» "groups" = 16 ∧ val% «child_claim_list_digest» "s1#1" = 6 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`claim_list_digest`'s virtual values on a nonempty list** (its path past `n_g ≠ 1`, a memory
image below `2^32`): `list_split`'s `g^a`, `g^b` with `n_g = g^(136 a + 17 b + c)`, `b < 8`, `c < 17`. -/
theorem claim_list_digest_vals (hm : Digest.MemOk rd) {σ : Val}
    (h : PathHolds coreProgram rd "claim_list_digest" σ) (h3 : σ (.n 3) ≠ 0) :
    ∃ a b c, a < 2 ^ 32 ∧ b < 8 ∧ c < 17 ∧ σ (.n 1) = gen ^ (136 * a + 17 * b + c) ∧
      σ (.n 12) = gen ^ a ∧ σ (.n 13) = gen ^ b := by
  have hb := pathHolds_body Digest.find_claim_list_digest h
  rw [Digest.claim_list_digest_shape] at hb
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hb
  obtain ⟨-, -, -, -, hnz⟩ := hb
  have he1 := Digest.ce_ok
  simp only [Digest.ceOk, Bool.and_eq_true, List.all_eq_true] at he1
  obtain ⟨⟨⟨⟨hef, hls⟩, -⟩, -⟩, -⟩ := he1
  obtain ⟨hall, -⟩ := Digest.holdsList_flat _ (List.all_eq_true.mpr hef) _ _ (hnz h3)
  obtain ⟨a, ha, b, hb, c, hc, hn, habc⟩ := Digest.list_split_sound rd hm _ _ (Digest.call_of_flat hall hls)
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at habc
  obtain ⟨h23, h24, -⟩ := habc
  simp only [Digest.claimGroup, Digest.bigGroups, Digest.claimBig] at hb hc hn
  exact ⟨a, b, c, ha, hb, hc, hn, h23, h24⟩

/-- **`child_claim_list_digest`'s virtual values on a nonempty list**, as `claim_list_digest_vals`. -/
theorem child_claim_list_digest_vals (hm : Digest.MemOk rd) {σ : Val}
    (h : PathHolds coreProgram rd "child_claim_list_digest" σ) (h6 : σ (.n 6) ≠ 0) :
    ∃ a b c, a < 2 ^ 32 ∧ b < 8 ∧ c < 17 ∧ σ (.n 4) = gen ^ (136 * a + 17 * b + c) ∧
      σ (.n 15) = gen ^ a ∧ σ (.n 16) = gen ^ b := by
  have hb := pathHolds_body Digest.find_child_claim_list_digest h
  rw [Digest.child_claim_list_digest_shape] at hb
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨-, -, -, -, hnz⟩ := hb
  obtain ⟨hsplit, -⟩ := hnz h6
  obtain ⟨a, ha, b, hb, c, hc, hn, habc⟩ := Digest.list_split_sound rd hm _ _ hsplit
  simp only [List.cons.injEq, and_true] at habc
  obtain ⟨h26, h27, -⟩ := habc
  simp only [Digest.claimGroup, Digest.bigGroups, Digest.claimBig] at hb hc hn
  exact ⟨a, b, c, ha, hb, hc, hn, h26, h27⟩

end
end LeanVM.Guest.Budget
