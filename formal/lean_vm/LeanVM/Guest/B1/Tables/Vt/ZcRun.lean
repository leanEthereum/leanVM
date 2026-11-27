/-
  LeanVM.Guest.B1.Tables.Vt.ZcRun

  `verify_tables`' table sumcheck from its target: the batching challenge's powers, the target
  from the three sides' totals, the first record, the rounds, the last record, the challenges'
  running products and the prefix equality weights.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Rounds
public import LeanVM.Guest.B1.Eq.EqPrefixRev
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# The table sumcheck

`vt_xi`: `ξ = zc_xi` is squeezed with the bytecode's value waiting (`vtXiFs`). `vt_zc_run`: with
the sides' totals `T_s`, the target `ξ²·T_0 + ξ³·T_1 + ξ⁴·T_2` runs `n` plain rounds from the sponge
after `ξ`, reading `3n` words after the bytecode's value; the
last record holds the sponge, the cursor and the final claim; the challenges are in `chi` from
its top; `cprod[g^j]` is the product of the first `j`; `peq` holds the prefix equality weights of
`chi` against `1 + ζ`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The sponge `ξ` is squeezed from: the bytecode sumcheck's last capacity, its value waiting. -/
def vtXiFs (σ : Val) : Fs :=
  (⟨(List.range 5).map fun k ↦ σ (.n ((val% «verify_tables» "bfs0@3") + k)), []⟩ : Fs).absorb (σ (.n (val% «verify_tables» "x@8"))) dsObserve

/-- **The batching challenge `ξ`** (`XI_GRIND_BITS = 0`: a plain squeeze, the bytecode's value
waiting) and the capacity after it. -/
theorem vt_xi {rd : Reader} {σ : Val} (h : VtH rd σ) :
    σ (.n (val% «verify_tables» "nxt[0]@3")) = (vtXiFs σ).squeeze.1 ∧
      (vtXiFs σ).squeeze.2 = ⟨(List.range 5).map fun k ↦ σ (.n ((val% «verify_tables» "nxt[8]@3") + k)), []⟩ := by
  have c0 := h.atomAt 1641 (.copy (.n (val% «verify_tables» "sp[0]@2")) (.n (val% «verify_tables» "bfs0@3"))) (by decide +kernel)
  have c1 := h.atomAt 1642 (.copy (.n (val% «verify_tables» "sp[1]@2")) (.n (val% «verify_tables» "bfs1@3"))) (by decide +kernel)
  have c2 := h.atomAt 1643 (.copy (.n (val% «verify_tables» "sp[2]@2")) (.n (val% «verify_tables» "bfs2@3"))) (by decide +kernel)
  have c3 := h.atomAt 1644 (.copy (.n (val% «verify_tables» "sp[3]@2")) (.n (val% «verify_tables» "bfs3@3"))) (by decide +kernel)
  have c4 := h.atomAt 1645 (.copy (.n (val% «verify_tables» "sp[4]@2")) (.n (val% «verify_tables» "bfs4@3"))) (by decide +kernel)
  have c6 := h.atomAt 1647 (.copy (.n (val% «verify_tables» "rate[0]@3")) (.n (val% «verify_tables» "x@8"))) (by decide +kernel)
  have d7 := h.atomAt 1648 (.const (.n (val% «verify_tables» "rate[1]@3")) (word 0 1)) (by decide +kernel)
  have z3 := h.atomAt 2322 (.const (.n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]")) (word 0 0)) (by decide +kernel)
  have z4 := h.atomAt 2323 (.const (.n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[2]")) (word 0 0)) (by decide +kernel)
  have z5 := h.atomAt 2324 (.const (.n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[3]")) (word 0 0)) (by decide +kernel)
  have z6 := h.atomAt 2325 (.const (.n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[4]")) (word 0 0)) (by decide +kernel)
  have k := h.atomAt 2326 (.keccak [.n (val% «verify_tables» "rate[0]@3"), .n (val% «verify_tables» "rate[1]@3"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[2]"),
    .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[3]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[4]"), .n (val% «verify_tables» "sp[0]@2"), .n (val% «verify_tables» "sp[1]@2"), .n (val% «verify_tables» "sp[2]@2"), .n (val% «verify_tables» "sp[3]@2"), .n (val% «verify_tables» "sp[4]@2")] (vtOuts 2293) false false)
    (by decide +kernel)
  simp only [Atom.Holds, word_zero] at c0 c1 c2 c3 c4 c6 d7 z3 z4 z5 z6
  obtain ⟨hP, hC⟩ := vt_keccak k
  have hs : vtXiFs σ = ⟨(List.range 5).map fun k ↦ σ (.n ((val% «verify_tables» "bfs0@3") + k)),
      [(σ (.n (val% «verify_tables» "x@8")), dsObserve)]⟩ := by
    simp [vtXiFs, Fs.absorb, rateScalars]
  have hin : ([.n (val% «verify_tables» "rate[0]@3"), .n (val% «verify_tables» "rate[1]@3"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[1]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[2]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[3]"), .n (val% «verify_tables» "s60.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s2.t.s0#0[4]"), .n (val% «verify_tables» "sp[0]@2"),
      .n (val% «verify_tables» "sp[1]@2"), .n (val% «verify_tables» "sp[2]@2"), .n (val% «verify_tables» "sp[3]@2"), .n (val% «verify_tables» "sp[4]@2")] : List V).map σ =
      rateOf (vtXiFs σ).pend ++ (vtXiFs σ).cap := by
    rw [hs, rateOf_eq_cells _ (by simp)]
    simp only [List.map_cons, List.map_nil, pendCells, List.flatMap_cons, List.flatMap_nil,
      List.length_cons, List.length_nil, List.cons_append, List.nil_append, List.append_nil,
      List.range_succ, List.range_zero, c0, c1, c2, c3, c4, c6, d7, z3, z4, z5, z6]
    rfl
  rw [hin] at hP hC
  refine ⟨?_, ?_⟩
  · simp only [Fs.squeeze, Fs.perm]
    exact challengeT_value (s0 := .n (val% «verify_tables» "nxt[0]@3")) (b := 2293) rfl (hP 0 (by omega))
  · simp only [Fs.squeeze, Fs.perm]
    have e : ∀ k, 2293 + 8 + k = 2301 + k := fun k => by omega
    simp only [e] at hC
    rw [hC]

/-- **The table sumcheck.** -/
theorem vt_zc_run {rd : Reader} {σ : Val} (h : VtH rd σ) {n : ℕ} (hn : n < 34)
    (hgn : σ (.n (val% «verify_tables» "g_zc_n")) = gen ^ n) :
    σ (.n (val% «verify_tables» "bus_target@3")) = σ (.n (val% «verify_tables» "nxt[0]@3")) ^ 2 * σ (.n (val% «verify_tables» "bus_table_total[0]")) + σ (.n (val% «verify_tables» "nxt[0]@3")) ^ 3 * σ (.n (val% «verify_tables» "bus_table_total[1]")) +
      σ (.n (val% «verify_tables» "nxt[0]@3")) ^ 4 * σ (.n (val% «verify_tables» "bus_table_total[2]")) ∧
    ∃ (xs pts : List E) (claimN : E),
      RunsTo (sumcheck (σ (.n (val% «verify_tables» "bus_target@3"))) 4 (List.replicate n none))
        ⟨(List.range 5).map fun k ↦ σ (.n ((val% «verify_tables» "nxt[8]@3") + k)), []⟩ xs (pts, claimN)
        ⟨(List.range 5).map fun k ↦ σ (.n ((val% «verify_tables» "fs_load.sp[0]") + k)), []⟩ ∧
      ReadsAt rd (σ (.n (val% «verify_tables» "cursor@4")) * gen) xs ∧ xs.length = 3 * n ∧ pts.length = n ∧
      σ (.n (val% «verify_tables» "cursor@5")) = σ (.n (val% «verify_tables» "cursor@4")) * gen * gen ^ (3 * n) ∧ σ (.n (val% «verify_tables» "claim")) = claimN ∧
      (∀ i < n, LoadHolds rd (σ (.n (val% «verify_tables» "chi"))) (n - 1 - i) (pts.getD i 0)) ∧
      (∀ j ≤ n, LoadHolds rd (σ (.n (val% «verify_tables» "zc_cprod"))) j ((pts.take j).prod)) ∧
      EqPrefix rd (σ (.n (val% «verify_tables» "zc_peq"))) 1 (σ (.n (val% «verify_tables» "chi"))) (σ (.n (val% «verify_tables» "zeta1"))) n := by
  have a5207 := h.atomAt 2327 (.const (.n (val% «verify_tables» "zc_xi_pows[0]")) (word 1 0)) (by decide +kernel)
  have a5208 := h.atomAt 2328 (.mul (.n (val% «verify_tables» "zc_xi_pows[1]")) (.n (val% «verify_tables» "zc_xi_pows[0]")) (.n (val% «verify_tables» "nxt[0]@3"))) (by decide +kernel)
  have a5209 := h.atomAt 2329 (.mul (.n (val% «verify_tables» "zc_xi_pows[2]")) (.n (val% «verify_tables» "zc_xi_pows[1]")) (.n (val% «verify_tables» "nxt[0]@3"))) (by decide +kernel)
  have a5210 := h.atomAt 2330 (.mul (.n (val% «verify_tables» "zc_xi_pows[3]")) (.n (val% «verify_tables» "zc_xi_pows[2]")) (.n (val% «verify_tables» "nxt[0]@3"))) (by decide +kernel)
  have a5211 := h.atomAt 2331 (.mul (.n (val% «verify_tables» "zc_xi_pows[4]")) (.n (val% «verify_tables» "zc_xi_pows[3]")) (.n (val% «verify_tables» "nxt[0]@3"))) (by decide +kernel)
  have a5212 := h.atomAt 2332 (.mul (.n (val% «verify_tables» "bus_target@1")) (.n (val% «verify_tables» "zc_xi_pows[2]")) (.n (val% «verify_tables» "bus_table_total[0]"))) (by decide +kernel)
  have a5213 := h.atomAt 2333 (.mul (.n (val% «verify_tables» "bus_target@2~0")) (.n (val% «verify_tables» "zc_xi_pows[3]")) (.n (val% «verify_tables» "bus_table_total[1]"))) (by decide +kernel)
  have a5214 := h.atomAt 2334 (.add (.n (val% «verify_tables» "bus_target@2")) (.n (val% «verify_tables» "bus_target@1")) (.n (val% «verify_tables» "bus_target@2~0"))) (by decide +kernel)
  have a5215 := h.atomAt 2335 (.mul (.n (val% «verify_tables» "bus_target@3~0")) (.n (val% «verify_tables» "zc_xi_pows[4]")) (.n (val% «verify_tables» "bus_table_total[2]"))) (by decide +kernel)
  have a5216 := h.atomAt 2336 (.add (.n (val% «verify_tables» "bus_target@3")) (.n (val% «verify_tables» "bus_target@2")) (.n (val% «verify_tables» "bus_target@3~0"))) (by decide +kernel)
  have a5227 := h.atomAt 2339 (.load (.n (val% «verify_tables» "nxt[8]@3")) (.n (val% «verify_tables» "zc_rounds")) 0) (by decide +kernel)
  have a5228 := h.atomAt 2340 (.load (.n (val% «verify_tables» "nxt[9]@3")) (.n (val% «verify_tables» "zc_rounds")) 1) (by decide +kernel)
  have a5229 := h.atomAt 2341 (.load (.n (val% «verify_tables» "nxt[10]@3")) (.n (val% «verify_tables» "zc_rounds")) 2) (by decide +kernel)
  have a5230 := h.atomAt 2342 (.load (.n (val% «verify_tables» "nxt[11]@3")) (.n (val% «verify_tables» "zc_rounds")) 3) (by decide +kernel)
  have a5231 := h.atomAt 2343 (.load (.n (val% «verify_tables» "nxt[12]@3")) (.n (val% «verify_tables» "zc_rounds")) 4) (by decide +kernel)
  have a5232 := h.atomAt 2344 (.const (.n (val% «verify_tables» "s69#0")) (word 2 0)) (by decide +kernel)
  have a5233 := h.atomAt 2345 (.mul (.n (val% «verify_tables» "s69#1")) (.n (val% «verify_tables» "cursor@4")) (.n (val% «verify_tables» "s69#0"))) (by decide +kernel)
  have a5234 := h.atomAt 2346 (.load (.n (val% «verify_tables» "s69#1")) (.n (val% «verify_tables» "zc_rounds")) 5) (by decide +kernel)
  have a5235 := h.atomAt 2347 (.load (.n (val% «verify_tables» "bus_target@3")) (.n (val% «verify_tables» "zc_rounds")) 6) (by decide +kernel)
  have a5236 := h.atomAt 2348 (.const (.n (val% «verify_tables» "s71#0")) (word 1 0)) (by decide +kernel)
  have a5237 := h.atomAt 2349 (.load (.n (val% «verify_tables» "s71#0")) (.n (val% «verify_tables» "zc_cprod")) 0) (by decide +kernel)
  have a5238 := h.atomAt 2351 (.const (.n (val% «verify_tables» "s73#0")) (word 1 0)) (by decide +kernel)
  have a5239 := h.atomAt 2352 (.add (.n (val% «verify_tables» "s73#1")) (.n (val% «verify_tables» "s73#0")) (.n (val% «verify_tables» "g_zc_n"))) (by decide +kernel)
  have a5240 := h.atomAt 2353 (.const (.n (val% «verify_tables» "s73#2")) (word 1 0)) (by decide +kernel)
  have a5242 := h.atomAt 2355 (.mul (.n (val% «verify_tables» "zc_last~0")) (.n (val% «verify_tables» "g_zc_n")) (.n (val% «verify_tables» "g_zc_n"))) (by decide +kernel)
  have a5243 := h.atomAt 2356 (.mul (.n (val% «verify_tables» "zc_last~1")) (.n (val% «verify_tables» "zc_last~0")) (.n (val% «verify_tables» "g_zc_n"))) (by decide +kernel)
  have a5244 := h.atomAt 2357 (.mul (.n (val% «verify_tables» "zc_last~2")) (.n (val% «verify_tables» "zc_last~1")) (.n (val% «verify_tables» "zc_last~1"))) (by decide +kernel)
  have a5245 := h.atomAt 2358 (.mul (.n (val% «verify_tables» "zc_last~3")) (.n (val% «verify_tables» "zc_last~2")) (.n (val% «verify_tables» "g_zc_n"))) (by decide +kernel)
  have a5246 := h.atomAt 2359 (.mul (.n (val% «verify_tables» "zc_last")) (.n (val% «verify_tables» "zc_rounds")) (.n (val% «verify_tables» "zc_last~3"))) (by decide +kernel)
  have a5247 := h.atomAt 2360 (.load (.n (val% «verify_tables» "fs_load.sp[0]")) (.n (val% «verify_tables» "zc_last")) 0) (by decide +kernel)
  have a5248 := h.atomAt 2361 (.load (.n (val% «verify_tables» "fs_load.sp[1]")) (.n (val% «verify_tables» "zc_last")) 1) (by decide +kernel)
  have a5249 := h.atomAt 2362 (.load (.n (val% «verify_tables» "fs_load.sp[2]")) (.n (val% «verify_tables» "zc_last")) 2) (by decide +kernel)
  have a5250 := h.atomAt 2363 (.load (.n (val% «verify_tables» "fs_load.sp[3]")) (.n (val% «verify_tables» "zc_last")) 3) (by decide +kernel)
  have a5251 := h.atomAt 2364 (.load (.n (val% «verify_tables» "fs_load.sp[4]")) (.n (val% «verify_tables» "zc_last")) 4) (by decide +kernel)
  have a5252 := h.atomAt 2365 (.load (.n (val% «verify_tables» "cursor@5")) (.n (val% «verify_tables» "zc_last")) 5) (by decide +kernel)
  have a5253 := h.atomAt 2366 (.load (.n (val% «verify_tables» "claim")) (.n (val% «verify_tables» "zc_last")) 6) (by decide +kernel)
  have hloop := h.callIfAt 2354 (.n (val% «verify_tables» "s73#1")) name% «verify_tables_loop0» [.n (val% «verify_tables» "s73#2"), .n (val% «verify_tables» "g_zc_n"), .n (val% «verify_tables» "zc_rounds"),
      .n (val% «verify_tables» "tabs"), .n (val% «verify_tables» "zc_rk"), .n (val% «verify_tables» "zc_cprod")] (by decide +kernel)
  have hchain := h.callAt 2368 "eq_prefix_chain_rev" [.n (val% «verify_tables» "zc_peq"), .n (val% «verify_tables» "chi"), .n (val% «verify_tables» "zc_rk"), .n (val% «verify_tables» "zeta1"), .n (val% «verify_tables» "g_zc_n")] []
    (by decide +kernel)
  simp only [Atom.Holds] at a5207 a5208 a5209 a5210 a5211 a5212 a5213 a5214 a5215 a5216
  simp only [Atom.Holds] at a5227 a5228
  simp only [Atom.Holds] at a5229 a5230 a5231 a5232 a5233 a5234 a5235 a5236 a5237 a5238
  simp only [Atom.Holds] at a5239 a5240 a5242 a5243 a5244 a5245 a5246 a5247 a5248 a5249
  simp only [Atom.Holds] at a5250 a5251 a5252 a5253
  simp only [List.map_cons, List.map_nil] at hloop hchain
  obtain ⟨hC, hep⟩ : EqPrefixRev rd (σ (.n (val% «verify_tables» "zc_peq"))) (σ (.n (val% «verify_tables» "chi"))) (σ (.n (val% «verify_tables» "zc_rk"))) (σ (.n (val% «verify_tables» "zeta1"))) n := by
    have hm := (eq_prefix_chain_rev_holds rd _ _).mp hchain
    simp only [MeaningEqPrefixChainRev] at hm
    obtain ⟨-, -, n', hn', hn'v, hep⟩ := hm
    rw [hgn] at hn'v
    obtain rfl := gen_pow_inj (by omega) (by omega) hn'v
    exact hep
  refine ⟨by rw [a5216, a5214, a5212, a5213, a5215, a5211, a5210, a5209, a5208, a5207,
    word_one]; ring, ?_⟩
  have hne : 0 < n → ∀ a b : E, a = 1 → b = a + gen ^ n → b ≠ 0 := by
    intro hn0 a b ha hb h0
    rw [hb, ha] at h0
    have := gen_pow_inj (by omega) (by omega)
      ((e_add_eq_zero_iff.mp h0).symm.trans (pow_zero gen).symm)
    omega
  have hB : ∀ j < n, L10B rd (σ (.n (val% «verify_tables» "zc_rounds"))) (σ (.n (val% «verify_tables» "tabs"))) (σ (.n (val% «verify_tables» "zc_rk"))) (σ (.n (val% «verify_tables» "zc_cprod"))) (gen ^ j) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · intro j hj; omega
    · have hr := hloop.2 (hne hn0 (σ (.n (val% «verify_tables» "s73#0"))) _ (by rw [a5238, word_one]) (by rw [a5239, hgn]))
      rw [a5240, word_one, hgn] at hr
      exact l10_loop hn0 (by omega) hr
  have hc0 : CapAt rd (σ (.n (val% «verify_tables» "zc_rounds")) * gen ^ (7 * 0)) 0 1
      ((List.range 5).map fun k ↦ σ (.n ((val% «verify_tables» "nxt[8]@3") + k))) := by
    refine ⟨by simp, fun j hj => ?_⟩
    simp only [List.length_map, List.length_range] at hj
    simp only [Nat.mul_zero, pow_zero, mul_one, Nat.zero_add, List.getElem_map,
      List.getElem_range]
    interval_cases j
    · exact a5227
    · exact a5228
    · exact a5229
    · exact a5230
    · exact a5231
  have hcur0 : LoadHolds rd (σ (.n (val% «verify_tables» "zc_rounds")) * gen ^ (7 * 0)) 5 (σ (.n (val% «verify_tables» "cursor@4")) * gen) := by
    rw [Nat.mul_zero, pow_zero, mul_one, ← word_gen, ← a5232, ← a5233]
    exact a5234
  have hcl0 : LoadHolds rd (σ (.n (val% «verify_tables» "zc_rounds")) * gen ^ (7 * 0)) 6 (σ (.n (val% «verify_tables» "bus_target@3"))) := by
    rw [Nat.mul_zero, pow_zero, mul_one]; exact a5235
  obtain ⟨xs, pts, claimN, capN, hrun, hxs, hxl, hpl, hcN, hcurN, hclN, hchi⟩ :=
    l10_chain (by omega) hB n le_rfl 0 (by omega) _ _ _ hc0 hcur0 hcl0
  have e5926 : σ (.n (val% «verify_tables» "zc_last")) = σ (.n (val% «verify_tables» "zc_rounds")) * gen ^ (7 * n) := by
    rw [a5246, a5245, a5244, a5243, a5242, hgn]; ring
  have hcF : CapAt rd (σ (.n (val% «verify_tables» "zc_rounds")) * gen ^ (7 * n)) 0 1
      ((List.range 5).map fun k ↦ σ (.n ((val% «verify_tables» "fs_load.sp[0]") + k))) := by
    refine ⟨by simp, fun j hj => ?_⟩
    simp only [List.length_map, List.length_range] at hj
    simp only [Nat.zero_add, mul_one, List.getElem_map, List.getElem_range, ← e5926]
    interval_cases j
    · exact a5247
    · exact a5248
    · exact a5249
    · exact a5250
    · exact a5251
  obtain rfl := capAt_eq hcN hcF
  rw [← e5926] at hcurN hclN
  refine ⟨xs, pts, claimN, hrun, by simpa using hxs, hxl, hpl,
    loadHolds_unique a5252 hcurN, loadHolds_unique a5253 hclN, fun i hi => ?_, ?_, ?_⟩
  · obtain ⟨v, hv, hcv⟩ := hC (n - 1 - i) (by omega)
    rw [show n - 1 - (n - 1 - i) = i by omega] at hv
    rw [loadHolds_unique hv (by simpa using hchi i hi)] at hcv
    exact hcv
  · intro j hj
    induction j with
    | zero =>
      rw [a5236, word_one] at a5237
      simpa using a5237
    | succ j ih =>
      obtain ⟨-, -, -, -, rk, -, -, -, -, -, hrk, cp, hcp, hcp1⟩ := hB j (by omega)
      rw [loadHolds_mul_gen_pow, Nat.add_zero] at hrk
      have erk : rk = pts.getD j 0 := loadHolds_unique hrk (by simpa using hchi j (by omega))
      rw [loadHolds_mul_gen_pow, Nat.add_zero] at hcp
      rw [loadHolds_mul_gen_pow] at hcp1
      rw [loadHolds_unique hcp (ih (by omega)), erk] at hcp1
      rw [List.prod_take_succ _ _ (by omega), ← List.getD_eq_getElem _ 0 (by omega)]
      exact hcp1
  · exact hep

end
end LeanVM.Guest.B1.Tables
