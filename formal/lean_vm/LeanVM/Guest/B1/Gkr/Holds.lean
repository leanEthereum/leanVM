/-
  LeanVM.Guest.B1.Gkr.Holds

  `verify_bus_gkr` computes the specification's bus GKR walk: `verify_bus_gkr_holds`.
-/

module

public import LeanVM.Guest.B1.Gkr.Interface
public import LeanVM.Guest.B1.Gkr.Walk
public import LeanVM.Guest.B1.Gkr.Root
public import LeanVM.Guest.B1.Gkr.Gls
public import LeanVM.Guest.B1.Gkr.Loop8
public import LeanVM.Guest.B1.Placement.Common
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.CoreData
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_bus_gkr»

/-!
# `verify_bus_gkr` is sound

The body (`vbgPre`, the core IR's): the range check of `g_bus_mu = g^depth` (`depth ≤ 32`), the
two roots read and the count asserted nonzero, the combiner drawn from the two roots waiting
(a grind of `0` bits) and the batched claim (`gkr_combine`), the tables
`depth_odd[d] = g^(d % 2)`, `four_bounds[d] = g^((d - 1) / 8)` and
`four_rem[d] = g^(((d - 1) / 2) % 4)`, `start_g = g^(2 - d % 2)`, the root-most layer (`rt_two` at
an odd depth, `rt_four` at an even one), the radix-four layers (`gkr_layers__L{d % 2}`: `gls_lyB`,
`ly_chain`), the final slot and point row, the point's copy to `zeta` (`verify_bus_gkr_loop0`),
the trees' values into a buffer of three, and the return.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A depth's round records: one unused, then radix-four layer `j`'s `j / 4 + 1`, `j < depth / 2`. -/
def gkRecCount (d : ℕ) : ℕ :=
  1 + d / 2 + 2 * (d / 8) * (d / 8) + (d / 2 % 4) * (d / 8) - 2 * (d / 8)

/-- `verify_bus_gkr`'s parameters. -/
def vbgParams : List V := (List.range 10).map V.n

/-- `verify_bus_gkr`'s body, the core IR's. -/
noncomputable def vbgBody : List Stmt := (fn% «verify_bus_gkr»).body

/-- `verify_bus_gkr`'s statements before its `ret`. -/
noncomputable def vbgPre : List Stmt := vbgBody.dropLast

/-- `verify_bus_gkr`'s returned values. -/
def vbgRets : List V := (List.range 7).map fun k ↦ .n ((val% «verify_bus_gkr» "s39#0") + k)

noncomputable def vbgCheck : Bool :=
  match coreProgram.find? name% «verify_bus_gkr» with
  | some fn => decide (fn.params = vbgParams) && tbStmtsEqb fn.body (vbgPre ++ [.ret vbgRets])
  | none => false

theorem vbgCheck_eq : vbgCheck = true := by decide +kernel

theorem vbgFound : ∃ fn : Fn, coreProgram.find? name% «verify_bus_gkr» = some fn ∧
    fn.params = vbgParams ∧ fn.body = vbgPre ++ [.ret vbgRets] := by
  have h := vbgCheck_eq
  unfold vbgCheck at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

theorem vbgPre_noRet : Stmt.noRetList vbgPre = true := by decide +kernel

/-- The sponge after the two roots: the carried capacity, both waiting. -/
def vbgS1 (σ : Val) : Fs :=
  ⟨[σ (.n (val% «verify_bus_gkr» "fs0")), σ (.n (val% «verify_bus_gkr» "fs1")), σ (.n (val% «verify_bus_gkr» "fs2")), σ (.n (val% «verify_bus_gkr» "fs3")), σ (.n (val% «verify_bus_gkr» "fs4"))],
    [(σ (.n (val% «verify_bus_gkr» "x@1")), dsObserve), (σ (.n (val% «verify_bus_gkr» "x@2")), dsObserve)]⟩

/-- The trees' roots: push and pull share one, then the count's. -/
def vbgSt0 (σ : Val) : GkrState := ⟨[σ (.n (val% «verify_bus_gkr» "x@1")), σ (.n (val% «verify_bus_gkr» "x@1")), σ (.n (val% «verify_bus_gkr» "x@2"))], []⟩

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **The roots and the combiner**: the two roots read at the cursor, the count nonzero, the
combiner the sponge's challenge with both waiting, the batched claim, the capacity after it, and
the zeros the layers' empty rates read. -/
theorem vbg_root (h : Stmt.HoldsList C rd σ vbgPre True kret) :
    LoadHolds rd (σ (.n (val% «verify_bus_gkr» "cursor@1"))) 0 (σ (.n (val% «verify_bus_gkr» "x@1"))) ∧ LoadHolds rd (σ (.n (val% «verify_bus_gkr» "cursor@1"))) 1 (σ (.n (val% «verify_bus_gkr» "x@2"))) ∧
      σ (.n (val% «verify_bus_gkr» "x@2")) ≠ 0 ∧ σ (.n (val% «verify_bus_gkr» "nxt[0]@1")) = (vbgS1 σ).squeeze.1 ∧
      σ (.n (val% «verify_bus_gkr» "claim@2")) = polyEval (vbgSt0 σ).values (vbgS1 σ).squeeze.1 ∧
      (lyCap (val% «verify_bus_gkr» "nxt[0]@1")).map σ = capOf (vbgS1 σ).perm ∧
      σ (.n (val% «verify_bus_gkr» "s15.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]")) = 0 ∧ σ (.n (val% «verify_bus_gkr» "s15.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]")) = 0 ∧ σ (.n (val% «verify_bus_gkr» "s15.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]")) = 0 ∧ σ (.n (val% «verify_bus_gkr» "s15.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")) = 0 := by
  have hnr := vbgPre_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have r0 := tb_holds_slice hnr h 153 (fsNextT (.n (val% «verify_bus_gkr» "cursor@1")) 0 (val% «verify_bus_gkr» "x@1")) (by decide +kernel)
  have r1 := tb_holds_slice hnr h 158 (fsNextT (.n (val% «verify_bus_gkr» "cursor@1")) 1 (val% «verify_bus_gkr» "x@2")) (by decide +kernel)
  rw [holds_fsNextT] at r0 r1
  obtain ⟨⟨l28, p28⟩, -⟩ := r0
  obtain ⟨⟨l33, p33⟩, -⟩ := r1
  have cp : ∀ k < 5, σ (.n ((val% «verify_bus_gkr» "sp[0]") + k)) = σ (.n k) := by
    intro k hk
    have := tb_holds_slice hnr h 148 ((List.range 5).map fun k ↦
      Stmt.atom (.copy (.n ((val% «verify_bus_gkr» "sp[0]") + k)) (.n k))) (by decide +kernel)
    rw [tb_holdsList_mapAtoms] at this
    exact this k hk
  have q31 := a 156 (.copy (.n (val% «verify_bus_gkr» "vals[0]")) (.n (val% «verify_bus_gkr» "x@1"))) (by decide +kernel)
  have q32 := a 157 (.copy (.n (val% «verify_bus_gkr» "vals[1]")) (.n (val% «verify_bus_gkr» "x@1"))) (by decide +kernel)
  have q36 := a 161 (.copy (.n (val% «verify_bus_gkr» "vals[2]")) (.n (val% «verify_bus_gkr» "x@2"))) (by decide +kernel)
  have c37 := a 162 (.const (.n (val% «verify_bus_gkr» "s14#0")) (word 0 0)) (by decide +kernel)
  have a38 := a 163 (.add (.n (val% «verify_bus_gkr» "s14#1")) (.n (val% «verify_bus_gkr» "x@2")) (.n (val% «verify_bus_gkr» "s14#0"))) (by decide +kernel)
  have n38 := a 165 (.assertNe (.n (val% «verify_bus_gkr» "s14#1")) (.n (val% «verify_bus_gkr» "s14#2")) (.n (val% «verify_bus_gkr» "s14#3"))) (by decide +kernel)
  have c42 := a 167 (.const (.n (val% «verify_bus_gkr» "s15.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]")) (word 0 0)) (by decide +kernel)
  have c43 := a 168 (.const (.n (val% «verify_bus_gkr» "s15.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]")) (word 0 0)) (by decide +kernel)
  have c44 := a 169 (.const (.n (val% «verify_bus_gkr» "s15.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]")) (word 0 0)) (by decide +kernel)
  have c45 := a 170 (.const (.n (val% «verify_bus_gkr» "s15.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")) (word 0 0)) (by decide +kernel)
  have k1 := a 171 (.keccak ([.n (val% «verify_bus_gkr» "rate[0]@1"), .n (val% «verify_bus_gkr» "rate[1]@1"), .n (val% «verify_bus_gkr» "rate[2]@1"), .n (val% «verify_bus_gkr» "rate[3]@1"), .n (val% «verify_bus_gkr» "s15.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (val% «verify_bus_gkr» "s15.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (val% «verify_bus_gkr» "s15.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (val% «verify_bus_gkr» "s15.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")] ++
    (List.range 5).map fun k ↦ .n ((val% «verify_bus_gkr» "sp[0]") + k)) (lyOuts (val% «verify_bus_gkr» "nxt[0]@1")) false false) (by decide +kernel)
  have m60 := a 172 (.mul (.n (val% «verify_bus_gkr» "claim@1~0")) (.n (val% «verify_bus_gkr» "nxt[0]@1")) (.n (val% «verify_bus_gkr» "vals[2]"))) (by decide +kernel)
  have a61 := a 173 (.add (.n (val% «verify_bus_gkr» "claim@1")) (.n (val% «verify_bus_gkr» "vals[1]")) (.n (val% «verify_bus_gkr» "claim@1~0"))) (by decide +kernel)
  have m62 := a 174 (.mul (.n (val% «verify_bus_gkr» "claim@2~0")) (.n (val% «verify_bus_gkr» "nxt[0]@1")) (.n (val% «verify_bus_gkr» "claim@1"))) (by decide +kernel)
  have a63 := a 175 (.add (.n (val% «verify_bus_gkr» "claim@2")) (.n (val% «verify_bus_gkr» "vals[0]")) (.n (val% «verify_bus_gkr» "claim@2~0"))) (by decide +kernel)
  simp only [Atom.Holds, tb_word_zero] at q31 q32 q36 c37 a38 n38 c42 c43 c44 c45 m60 a61 m62 a63
  obtain ⟨P, B⟩ := ly_keccak k1
  have hins : (([.n (val% «verify_bus_gkr» "rate[0]@1"), .n (val% «verify_bus_gkr» "rate[1]@1"), .n (val% «verify_bus_gkr» "rate[2]@1"), .n (val% «verify_bus_gkr» "rate[3]@1"), .n (val% «verify_bus_gkr» "s15.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[1]"), .n (val% «verify_bus_gkr» "s15.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[2]"), .n (val% «verify_bus_gkr» "s15.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[3]"), .n (val% «verify_bus_gkr» "s15.i0:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s3.t.s0#0[4]")] ++
      (List.range 5).map fun k ↦ V.n ((val% «verify_bus_gkr» "sp[0]") + k)) : List V).map σ =
      rateOf (vbgS1 σ).pend ++ (vbgS1 σ).cap := by
    obtain ⟨e29, e30⟩ := Prod.ext_iff.mp (fsPackT_cells p28)
    obtain ⟨e34, e35⟩ := Prod.ext_iff.mp (fsPackT_cells p33)
    have hcapE : ((List.range 5).map fun k ↦ V.n ((val% «verify_bus_gkr» "sp[0]") + k)).map σ =
        [σ (.n (val% «verify_bus_gkr» "fs0")), σ (.n (val% «verify_bus_gkr» "fs1")), σ (.n (val% «verify_bus_gkr» "fs2")), σ (.n (val% «verify_bus_gkr» "fs3")), σ (.n (val% «verify_bus_gkr» "fs4"))] := by
      rw [List.map_map, show [σ (.n (val% «verify_bus_gkr» "fs0")), σ (.n (val% «verify_bus_gkr» "fs1")), σ (.n (val% «verify_bus_gkr» "fs2")), σ (.n (val% «verify_bus_gkr» "fs3")), σ (.n (val% «verify_bus_gkr» "fs4"))] =
        (List.range 5).map (fun k ↦ σ (.n k)) from rfl]
      exact List.map_congr_left fun k hk => cp k (List.mem_range.mp hk)
    rw [List.map_append, hcapE, rateOf_eq_cells _ (by simp [vbgS1])]
    norm_num at e29 e30 e34 e35
    simp [vbgS1, pendCells, e29, e30, e34, e35, c42, c43, c44, c45]
  rw [hins] at P B
  have e59 : σ (.n (val% «verify_bus_gkr» "nxt[0]@1")) = (vbgS1 σ).squeeze.1 := by
    rw [P 0 (by omega)]; exact (Keccak.challengeOf_cells _).symm
  refine ⟨l28, l33, fun h0 => ?_, e59, ?_, B, c42, c43, c44, c45⟩
  · obtain ⟨e40, e1⟩ := n38
    rw [a38, c37, h0, zero_add, zero_mul] at e40
    exact zero_ne_one (e40.symm.trans e1)
  · rw [a63, m62, a61, m60, q31, q32, q36, ← e59]
    simp only [vbgSt0, polyEval, List.foldr]
    ring

/-- **The tables** at `g_bus_mu = g^depth`, `depth ≠ 0`: `depth_odd[depth] = g^(depth % 2)`,
`four_bounds[depth] = g^((depth - 1) / 8)`, `four_rem[depth] = g^(((depth - 1) / 2) % 4)`, and
`start_g = g^(2 - depth % 2)`. -/
theorem vbg_tables (h : Stmt.HoldsList C rd σ vbgPre True kret) {depth : ℕ}
    (hg : σ (.n (val% «verify_bus_gkr» "g_bus_mu")) = gen ^ depth) (hd : depth < 33) (hd0 : depth ≠ 0) :
    σ (.n (val% «verify_bus_gkr» "odd_g")) = gen ^ (depth % 2) ∧ σ (.n (val% «verify_bus_gkr» "n_four")) = gen ^ ((depth - 1) / 8) ∧
      σ (.n (val% «verify_bus_gkr» "rem_g")) = gen ^ (((depth - 1) / 2) % 4) ∧ σ (.n (val% «verify_bus_gkr» "start_g")) = gen ^ (2 - depth % 2) := by
  have hnr := vbgPre_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr h n a heq
  have ht := tb_holds_slice hnr h 185 (((List.range 32).map fun e ↦
    [Stmt.atom (.const (.n (140 + 3 * e)) (word (2 ^ ((e + 1) % 2)) 0)),
      .atom (.load (.n (140 + 3 * e)) (.n (val% «verify_bus_gkr» "depth_odd")) (e + 1)),
      .atom (.const (.n (141 + 3 * e)) (word (2 ^ (e / 8)) 0)),
      .atom (.load (.n (141 + 3 * e)) (.n (val% «verify_bus_gkr» "four_bounds")) (e + 1)),
      .atom (.const (.n (142 + 3 * e)) (word (2 ^ ((e / 2) % 4)) 0)),
      .atom (.load (.n (142 + 3 * e)) (.n (val% «verify_bus_gkr» "four_rem")) (e + 1))]).flatten) (by decide +kernel)
  rw [tb_holdsList_flatten_range _ _ (fun _ => rfl)] at ht
  have hdt := ht (depth - 1) (by omega)
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true,
    show depth - 1 + 1 = depth by omega] at hdt
  obtain ⟨c0, l0, c1, l1, c2, l2⟩ := hdt
  rw [c0, tb_word_two_pow (by omega)] at l0
  rw [c1, tb_word_two_pow (by omega)] at l1
  rw [c2, tb_word_two_pow (by omega)] at l2
  have m166 := a 377 (.mul (.n (val% «verify_bus_gkr» "odd_g~0")) (.n (val% «verify_bus_gkr» "depth_odd")) (.n (val% «verify_bus_gkr» "g_bus_mu"))) (by decide +kernel)
  have l167 := a 378 (.load (.n (val% «verify_bus_gkr» "odd_g")) (.n (val% «verify_bus_gkr» "odd_g~0")) 0) (by decide +kernel)
  have c168 := a 379 (.const (.n (val% «verify_bus_gkr» "start_g~0")) (word 4 0)) (by decide +kernel)
  have m168 := a 380 (.mul (.n (val% «verify_bus_gkr» "start_g~0")) (.n (val% «verify_bus_gkr» "start_g")) (.n (val% «verify_bus_gkr» "odd_g"))) (by decide +kernel)
  have m399 := a 389 (.mul (.n (val% «verify_bus_gkr» "n_four~0")) (.n (val% «verify_bus_gkr» "four_bounds")) (.n (val% «verify_bus_gkr» "g_bus_mu"))) (by decide +kernel)
  have l400 := a 390 (.load (.n (val% «verify_bus_gkr» "n_four")) (.n (val% «verify_bus_gkr» "n_four~0")) 0) (by decide +kernel)
  have m401 := a 391 (.mul (.n (val% «verify_bus_gkr» "rem_g~0")) (.n (val% «verify_bus_gkr» "four_rem")) (.n (val% «verify_bus_gkr» "g_bus_mu"))) (by decide +kernel)
  have l402 := a 392 (.load (.n (val% «verify_bus_gkr» "rem_g")) (.n (val% «verify_bus_gkr» "rem_g~0")) 0) (by decide +kernel)
  simp only [Atom.Holds] at m166 l167 c168 m168 m399 l400 m401 l402
  rw [m166, hg, tb_loadHolds_mul_gen_pow, Nat.add_zero] at l167
  rw [m399, hg, tb_loadHolds_mul_gen_pow, Nat.add_zero] at l400
  rw [m401, hg, tb_loadHolds_mul_gen_pow, Nat.add_zero] at l402
  have e167 := tb_loadHolds_unique l167 l0
  refine ⟨e167, tb_loadHolds_unique l400 l1, tb_loadHolds_unique l402 l2, ?_⟩
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, tb_word_two_pow (by norm_num)] at c168
  rw [c168, e167] at m168
  have hsh : depth % 2 ≤ 2 := by omega
  have hne : (gen : E) ^ (depth % 2) ≠ 0 := pow_ne_zero _ gen_ne_zero
  apply mul_right_cancel₀ hne
  rw [← m168, ← pow_add, Nat.sub_add_cancel hsh]

end Sem

theorem rtSh_lo {k : ℕ} (h : k < 19) : rtSh (.n k) = .n k := by
  simp [rtSh, show ¬ 66 ≤ k by omega, show ¬ 19 ≤ k by omega]

theorem rtSh_mid {k : ℕ} (h1 : 19 ≤ k) (h2 : k < 66) : rtSh (.n k) = .n (k + 71) := by
  simp [rtSh, h1, show ¬ 66 ≤ k by omega]

theorem rtSh_hi {k : ℕ} (h : 66 ≤ k) : rtSh (.n k) = .n (k + 105) := by simp [rtSh, h]

theorem vbgArm_noRet_t : Stmt.noRetList (core% «verify_bus_gkr» s388_t) = true := by decide +kernel

theorem vbgArm_noRet_e : Stmt.noRetList (core% «verify_bus_gkr» s388_e) = true := by decide +kernel

/-- **The walk**: from the sponge the roots wait in, the root-most layer and the radix-four
layers run `gkrLayers depth` to the slot of `L = depth`, nothing waiting, its point in row
`(depth - 1) / 2 + 1`. -/
theorem vbg_walk {rd : Reader} {σ : Val} {kret : List E → Prop}
    (h : Stmt.HoldsList (coreProgram.Rel rd) rd σ vbgPre True kret) {depth : ℕ}
    (hg : σ (.n (val% «verify_bus_gkr» "g_bus_mu")) = gen ^ depth) (hd : depth < 33) (hd0 : depth ≠ 0) :
    ∃ (xs : List E) (st : GkrState) (s : Fs) (pos : E),
      RunsTo (gkrLayers depth (vbgSt0 σ)) (vbgS1 σ) xs st s ∧
      TbReadsAt rd (σ (.n (val% «verify_bus_gkr» "cursor@1")) * gen ^ 2) xs ∧
      GkSlot rd (σ (.n (val% «verify_bus_gkr» "layers"))) depth s (σ (.n (val% «verify_bus_gkr» "cursor@1")) * gen ^ 2 * gen ^ xs.length) st
        (σ (.n (val% «verify_bus_gkr» "gkr_pts")) * gen ^ (40 * ((depth - 1) / 2 + 1))) pos := by
  have hnr := vbgPre_noRet
  have a := fun n a heq => tb_holds_atom hnr h n a heq
  obtain ⟨-, -, -, h59, h63, hcap, z42, z43, z44, z45⟩ := vbg_root h
  obtain ⟨e167, e400, e402, e169⟩ := vbg_tables h hg hd hd0
  -- the root-most slot
  have m170 := a 381 (.mul (.n (val% «verify_bus_gkr» "nxt~0")) (.n (val% «verify_bus_gkr» "start_g")) (.n (val% «verify_bus_gkr» "start_g"))) (by decide +kernel)
  have m171 := a 382 (.mul (.n (val% «verify_bus_gkr» "nxt~1")) (.n (val% «verify_bus_gkr» "nxt~0")) (.n (val% «verify_bus_gkr» "nxt~0"))) (by decide +kernel)
  have m172 := a 383 (.mul (.n (val% «verify_bus_gkr» "nxt~2")) (.n (val% «verify_bus_gkr» "nxt~1")) (.n (val% «verify_bus_gkr» "start_g"))) (by decide +kernel)
  have m173 := a 384 (.mul (.n (val% «verify_bus_gkr» "nxt~3")) (.n (val% «verify_bus_gkr» "nxt~2")) (.n (val% «verify_bus_gkr» "nxt~2"))) (by decide +kernel)
  have m174 := a 385 (.mul (.n (val% «verify_bus_gkr» "nxt")) (.n (val% «verify_bus_gkr» "layers")) (.n (val% «verify_bus_gkr» "nxt~3"))) (by decide +kernel)
  simp only [Atom.Holds] at m170 m171 m172 m173 m174
  have e174 : σ (.n (val% «verify_bus_gkr» "nxt")) = σ (.n (val% «verify_bus_gkr» "layers")) * gen ^ (10 * (2 - depth % 2)) := by
    rw [m174, m173, m172, m171, m170, e169, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    ring_nf
  -- the radix-four layers
  obtain ⟨jj, hjj, hx, hls⟩ := tb_holds_dispatch hnr h 396 (.n (val% «verify_bus_gkr» "odd_g"))
    [name% «gkr_layers__L0», name% «gkr_layers__L1»]
    [.n (val% «verify_bus_gkr» "layers"), .n (val% «verify_bus_gkr» "rounds"), .n (val% «verify_bus_gkr» "gkr_pts"), .n (val% «verify_bus_gkr» "n_four"), .n (val% «verify_bus_gkr» "rem_g"), .n (val% «verify_bus_gkr» "start_g"), .n (val% «verify_bus_gkr» "g_bus_mu"), .n (val% «verify_bus_gkr» "tabs"), .n (val% «verify_bus_gkr» "stream")] [.n (val% «verify_bus_gkr» "done")] (by decide +kernel)
  have hjo : jj = depth % 2 := by
    simp only [List.length_cons, List.length_nil] at hjj
    rw [e167, ← gen_pow_eq_ofK] at hx
    exact (gen_pow_inj (by omega) (by omega) hx).symm
  have hls' : coreProgram.Rel rd (glcLsN (depth % 2)) [σ (.n (val% «verify_bus_gkr» "layers")), σ (.n (val% «verify_bus_gkr» "rounds")), σ (.n (val% «verify_bus_gkr» "gkr_pts")),
      gen ^ ((depth - 1) / 8), gen ^ (((depth - 1) / 2) % 4), gen ^ (2 - depth % 2), σ (.n (val% «verify_bus_gkr» "g_bus_mu")),
      σ (.n (val% «verify_bus_gkr» "tabs")), σ (.n (val% «verify_bus_gkr» "stream"))] [σ (.n (val% «verify_bus_gkr» "done"))] := by
    have e : [name% «gkr_layers__L0», name% «gkr_layers__L1»][jj] = glcLsN (depth % 2) := by
      subst hjo
      simp only [List.length_cons, List.length_nil] at hjj
      interval_cases h2 : depth % 2 <;> rfl
    simp only [List.map_cons, List.map_nil] at hls
    rw [e, e400, e402, e169] at hls
    exact hls
  have hB := gls_lyB (o := depth % 2) (by omega) (by omega) (by omega) hls'
  rw [show 4 * ((depth - 1) / 8) + ((depth - 1) / 2) % 4 = (depth - 1) / 2 by omega] at hB
  -- the root-most layer
  have c175 := a 386 (.const (.n (val% «verify_bus_gkr» "s28#0")) (word 1 0)) (by decide +kernel)
  have a176 := a 387 (.add (.n (val% «verify_bus_gkr» "s28#1")) (.n (val% «verify_bus_gkr» "odd_g")) (.n (val% «verify_bus_gkr» "s28#0"))) (by decide +kernel)
  simp only [Atom.Holds, tb_word_one] at c175 a176
  have hi := tb_holds_slice hnr h 388 [.ite (.n (val% «verify_bus_gkr» "s28#1")) (core% «verify_bus_gkr» s388_t)
    (core% «verify_bus_gkr» s388_e)] (by decide +kernel)
  simp only [Stmt.HoldsList] at hi
  rw [tb_holds_ite_noRet _ _ _ vbgArm_noRet_t vbgArm_noRet_e] at hi
  obtain ⟨⟨-, hfour, htwo⟩, -⟩ := hi
  rw [rtFour_eq, Stmt.holdsList_rename] at hfour
  rw [rtTwo_eq, Stmt.holdsList_rename] at htwo
  have h140 : (σ ∘ rtSh) (.n 139) = σ (.n (val% «verify_bus_gkr» "nxt")) := by
    rw [Function.comp_apply, rtSh_hi (by omega)]
  have hcap' : (lyCap 46).map (σ ∘ rtSh) = capOf (vbgS1 σ).perm := by
    rw [← hcap]
    simp only [lyCap, List.map_map]
    apply List.map_congr_left
    intro k hk
    have hk5 := List.mem_range.mp hk
    simp only [Function.comp_apply, rtSh_mid (show 19 ≤ 46 + 8 + k by omega) (show 46 + 8 + k < 66 by omega)]
    rw [show 46 + 8 + k + 71 = (val% «verify_bus_gkr» "nxt[0]@1") + 8 + k by omega]
  have root : ∃ (xs1 : List E) (st1 : GkrState) (s1 : Fs),
      RunsTo (gkrStep (2 - depth % 2) false (vbgSt0 σ)) (vbgS1 σ) xs1 st1 s1 ∧
      TbReadsAt rd (σ (.n (val% «verify_bus_gkr» "cursor@1")) * gen ^ 2) xs1 ∧
      GkSlot rd (σ (.n (val% «verify_bus_gkr» "layers"))) (2 - depth % 2) s1 (σ (.n (val% «verify_bus_gkr» "cursor@1")) * gen ^ 2 * gen ^ xs1.length) st1
        (σ (.n (val% «verify_bus_gkr» "gkr_pts")) * gen ^ 40) (gen ^ 7) := by
    rcases Nat.mod_two_eq_zero_or_one depth with h2 | h2
    · have h0 : σ (.n (val% «verify_bus_gkr» "s28#1")) = 0 := by rw [a176, c175, e167, h2, pow_zero, e_add_self]
      rw [h2] at e174 ⊢
      exact rt_four (hfour h0) (by rw [h140, e174]; rfl) rfl rfl h59 h63 hcap' z42 z43 z44 z45
    · have hne : σ (.n (val% «verify_bus_gkr» "s28#1")) ≠ 0 := by
        rw [a176, c175, e167, h2, pow_one]
        intro h0
        have := gen_pow_inj (a := 1) (b := 0) (by omega) (by omega)
          ((pow_one gen).trans ((e_add_eq_zero_iff.mp h0).trans (pow_zero gen).symm))
        omega
      rw [h2] at e174 ⊢
      exact rt_two (htwo hne) (by rw [h140, e174]; rfl) rfl rfl h59 h63 hcap' z42 z43 z44 z45
  obtain ⟨xs1, st1, s1, hrun1, hrd1, hsl1⟩ := root
  obtain ⟨xs, st, s, pos, hrun, hrd, hsl⟩ := ly_chain (sh := depth % 2) (by omega) hB hsl1
    ((depth - 1) / 2) le_rfl
  have hrun' : RunsTo (gkrLayers depth (vbgSt0 σ)) (vbgS1 σ) (xs1 ++ xs) st s := by
    rcases Nat.mod_two_eq_zero_or_one depth with h2 | h2
    · rw [h2] at hrun1
      rw [show depth = 2 * ((depth - 1) / 2) + 2 by omega, gkrLayers_even]
      exact hrun1.bind hrun
    · rw [h2] at hrun1
      rw [show depth = 2 * ((depth - 1) / 2) + 1 by omega, gkrLayers_odd]
      exact hrun1.bind hrun
  have hrd' : TbReadsAt rd (σ (.n (val% «verify_bus_gkr» "cursor@1")) * gen ^ 2) (xs1 ++ xs) := by
    rw [tbReadsAt_append]
    exact ⟨hrd1, hrd⟩
  rw [show 2 * ((depth - 1) / 2) + 2 - depth % 2 = depth by omega,
    mul_assoc (σ (.n (val% «verify_bus_gkr» "cursor@1")) * gen ^ 2), ← pow_add, ← List.length_append] at hsl
  exact ⟨xs1 ++ xs, st, s, _, hrun', hrd', hsl⟩

/-- **`verify_bus_gkr` is sound**: on any memory of at most `2^32` words, at a depth other than
`0`, it runs the specification's GKR walk and count check (`gkrPhase`) on the words it reads,
writes the point to `zeta` and returns the sponge's capacity, the cursor past the words and a
buffer of the three values. -/
theorem verify_bus_gkr_holds {μ : ℕ} (hμ : μ ≤ 32)
    (Lm : MemoryImage μ) : verify_bus_gkr_Spec Lm.read := by
  intro args rets hne hrel
  obtain ⟨fn, hf, hp, hb⟩ := vbgFound
  obtain ⟨σ, hpar, h, hret⟩ := (tb_rel_pre hf hb vbgPre_noRet args rets).mp hrel
  rw [hp] at hpar
  have hargs : args = [σ (.n (val% «verify_bus_gkr» "fs0")), σ (.n (val% «verify_bus_gkr» "fs1")), σ (.n (val% «verify_bus_gkr» "fs2")), σ (.n (val% «verify_bus_gkr» "fs3")), σ (.n (val% «verify_bus_gkr» "fs4")), σ (.n (val% «verify_bus_gkr» "cursor@1")), σ (.n (val% «verify_bus_gkr» "g_bus_mu")),
      σ (.n (val% «verify_bus_gkr» "zeta")), σ (.n (val% «verify_bus_gkr» "tabs")), σ (.n (val% «verify_bus_gkr» "stream"))] := by rw [← hpar]; rfl
  have hrets : rets = [σ (.n (val% «verify_bus_gkr» "s39#0")), σ (.n (val% «verify_bus_gkr» "s39#0[1]")), σ (.n (val% «verify_bus_gkr» "s39#0[2]")), σ (.n (val% «verify_bus_gkr» "s39#0[3]")), σ (.n (val% «verify_bus_gkr» "s39#0[4]")), σ (.n (val% «verify_bus_gkr» "s39#0[5]")),
      σ (.n (val% «verify_bus_gkr» "s39#0[6]"))] := by rw [← hret]; rfl
  subst hargs hrets
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hne
  have hnr := vbgPre_noRet
  have a := fun n a heq => tb_holds_atom hnr h n a heq
  -- the depth
  have c19 := a 140 (.const (.n (val% «verify_bus_gkr» "s3#0")) (word 4294967296 0)) (by decide +kernel)
  have rc := a 141 (.rangeCheck (.n (val% «verify_bus_gkr» "g_bus_mu")) (.n (val% «verify_bus_gkr» "s3#1")) (.n (val% «verify_bus_gkr» "s3#2")) (.n (val% «verify_bus_gkr» "s3#3")) (.n (val% «verify_bus_gkr» "s3#0"))) (by decide +kernel)
  simp only [Atom.Holds] at c19 rc
  obtain ⟨depth, hd, hg⟩ := tb_rc_sound' hμ Lm (K := 33) (by omega) (by norm_num)
    (by rw [c19, show (4294967296 : ℕ) = 2 ^ 32 by norm_num, tb_word_two_pow (by norm_num),
      gen_pow_eq_ofK]) rc.1 rc.2.1 rc.2.2
  have hd0 : depth ≠ 0 := by rintro rfl; exact hne (by rw [hg, pow_zero])
  -- the roots and the walk
  obtain ⟨l28, l33, hcnt, -⟩ := vbg_root h
  obtain ⟨-, e400, e402, e169⟩ := vbg_tables h hg hd hd0
  obtain ⟨xs, st, s, pos, hrun, hrd, hsl⟩ := vbg_walk h hg hd hd0
  have m403 := a 393 (.mul (.n (val% «verify_bus_gkr» "n_pairs~0")) (.n (val% «verify_bus_gkr» "n_four")) (.n (val% «verify_bus_gkr» "n_four"))) (by decide +kernel)
  have m404 := a 394 (.mul (.n (val% «verify_bus_gkr» "n_pairs~1")) (.n (val% «verify_bus_gkr» "n_pairs~0")) (.n (val% «verify_bus_gkr» "n_pairs~0"))) (by decide +kernel)
  have m405 := a 395 (.mul (.n (val% «verify_bus_gkr» "n_pairs")) (.n (val% «verify_bus_gkr» "n_pairs~1")) (.n (val% «verify_bus_gkr» "rem_g"))) (by decide +kernel)
  simp only [Atom.Holds] at m403 m404 m405
  have e405 : σ (.n (val% «verify_bus_gkr» "n_pairs")) = gen ^ ((depth - 1) / 2) := by
    rw [m405, m404, m403, e400, e402, ← pow_add, ← pow_add, ← pow_add,
      show (depth - 1) / 8 + (depth - 1) / 8 + ((depth - 1) / 8 + (depth - 1) / 8) +
        (depth - 1) / 2 % 4 = (depth - 1) / 2 by omega]
  obtain ⟨hcl, hcap, hpe, hcur, hvl, hval, hpl, hpt, -⟩ := hsl
  -- the final slot and point row
  have m407 := a 397 (.mul (.n (val% «verify_bus_gkr» "last~0")) (.n (val% «verify_bus_gkr» "n_pairs")) (.n (val% «verify_bus_gkr» "n_pairs"))) (by decide +kernel)
  have m408 := a 398 (.mul (.n (val% «verify_bus_gkr» "last~1")) (.n (val% «verify_bus_gkr» "last~0")) (.n (val% «verify_bus_gkr» "start_g"))) (by decide +kernel)
  have m409 := a 399 (.mul (.n (val% «verify_bus_gkr» "last~2")) (.n (val% «verify_bus_gkr» "last~1")) (.n (val% «verify_bus_gkr» "last~1"))) (by decide +kernel)
  have m410 := a 400 (.mul (.n (val% «verify_bus_gkr» "last~3")) (.n (val% «verify_bus_gkr» "last~2")) (.n (val% «verify_bus_gkr» "last~2"))) (by decide +kernel)
  have m411 := a 401 (.mul (.n (val% «verify_bus_gkr» "last~4")) (.n (val% «verify_bus_gkr» "last~3")) (.n (val% «verify_bus_gkr» "last~1"))) (by decide +kernel)
  have m412 := a 402 (.mul (.n (val% «verify_bus_gkr» "last~5")) (.n (val% «verify_bus_gkr» "last~4")) (.n (val% «verify_bus_gkr» "last~4"))) (by decide +kernel)
  have m413 := a 403 (.mul (.n (val% «verify_bus_gkr» "last")) (.n (val% «verify_bus_gkr» "layers")) (.n (val% «verify_bus_gkr» "last~5"))) (by decide +kernel)
  have l414 := a 404 (.load (.n (val% «verify_bus_gkr» "cursor@2")) (.n (val% «verify_bus_gkr» "last")) 5) (by decide +kernel)
  have c415 := a 405 (.const (.n (val% «verify_bus_gkr» "final_point_row~0")) (word 2 0)) (by decide +kernel)
  have m416 := a 406 (.mul (.n (val% «verify_bus_gkr» "final_point_row~1")) (.n (val% «verify_bus_gkr» "n_pairs")) (.n (val% «verify_bus_gkr» "final_point_row~0"))) (by decide +kernel)
  have m417 := a 407 (.mul (.n (val% «verify_bus_gkr» "final_point_row~2")) (.n (val% «verify_bus_gkr» "final_point_row~1")) (.n (val% «verify_bus_gkr» "final_point_row~1"))) (by decide +kernel)
  have m418 := a 408 (.mul (.n (val% «verify_bus_gkr» "final_point_row~3")) (.n (val% «verify_bus_gkr» "final_point_row~2")) (.n (val% «verify_bus_gkr» "final_point_row~2"))) (by decide +kernel)
  have m419 := a 409 (.mul (.n (val% «verify_bus_gkr» "final_point_row~4")) (.n (val% «verify_bus_gkr» "final_point_row~3")) (.n (val% «verify_bus_gkr» "final_point_row~1"))) (by decide +kernel)
  have m420 := a 410 (.mul (.n (val% «verify_bus_gkr» "final_point_row~5")) (.n (val% «verify_bus_gkr» "final_point_row~4")) (.n (val% «verify_bus_gkr» "final_point_row~4"))) (by decide +kernel)
  have m421 := a 411 (.mul (.n (val% «verify_bus_gkr» "final_point_row~6")) (.n (val% «verify_bus_gkr» "final_point_row~5")) (.n (val% «verify_bus_gkr» "final_point_row~5"))) (by decide +kernel)
  have m422 := a 412 (.mul (.n (val% «verify_bus_gkr» "final_point_row~7")) (.n (val% «verify_bus_gkr» "final_point_row~6")) (.n (val% «verify_bus_gkr» "final_point_row~6"))) (by decide +kernel)
  have m423 := a 413 (.mul (.n (val% «verify_bus_gkr» "final_point_row")) (.n (val% «verify_bus_gkr» "gkr_pts")) (.n (val% «verify_bus_gkr» "final_point_row~7"))) (by decide +kernel)
  have c424 := a 414 (.const (.n (val% «verify_bus_gkr» "s36#0")) (word 1 0)) (by decide +kernel)
  have a425 := a 415 (.add (.n (val% «verify_bus_gkr» "s36#1")) (.n (val% «verify_bus_gkr» "s36#0")) (.n (val% «verify_bus_gkr» "g_bus_mu"))) (by decide +kernel)
  have c426 := a 416 (.const (.n (val% «verify_bus_gkr» "s36#2")) (word 1 0)) (by decide +kernel)
  have q436 := a 430 (.copy (.n (val% «verify_bus_gkr» "s39#0[5]")) (.n (val% «verify_bus_gkr» "cursor@2"))) (by decide +kernel)
  have q437 := a 431 (.copy (.n (val% «verify_bus_gkr» "s39#0[6]")) (.n (val% «verify_bus_gkr» "leaves"))) (by decide +kernel)
  simp only [Atom.Holds] at m407 m408 m409 m410 m411 m412 m413 l414 c415 m416 m417 m418 m419
  simp only [Atom.Holds] at m420 m421 m422 m423 c424 a425 c426 q436 q437
  rw [tb_word_one] at c424 c426
  rw [tb_word_gen] at c415
  have e408 : σ (.n (val% «verify_bus_gkr» "last~1")) = gen ^ depth := by
    rw [m408, m407, e405, e169, ← pow_add, ← pow_add,
      show (depth - 1) / 2 + (depth - 1) / 2 + (2 - depth % 2) = depth by omega]
  have e413 : σ (.n (val% «verify_bus_gkr» "last")) = σ (.n (val% «verify_bus_gkr» "layers")) * gen ^ (10 * depth) := by
    rw [m413, m412, m411, m410, m409, e408, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    ring_nf
  have e423 : σ (.n (val% «verify_bus_gkr» "final_point_row")) = σ (.n (val% «verify_bus_gkr» "gkr_pts")) * gen ^ (40 * ((depth - 1) / 2 + 1)) := by
    rw [m423, m422, m421, m420, m419, m418, m417, m416, c415, e405, ← pow_succ]
    ring
  have ld : ∀ k w, LoadHolds Lm.read (σ (.n (val% «verify_bus_gkr» "last"))) k w →
      LoadHolds Lm.read (σ (.n (val% «verify_bus_gkr» "layers"))) (10 * depth + k) w := fun k w hw => by
    rw [e413, tb_loadHolds_mul_gen_pow] at hw; exact hw
  have hcs := tb_holds_slice hnr h 425 ((List.range 5).map fun k ↦
    Stmt.atom (.load (.n ((val% «verify_bus_gkr» "s39#0") + k)) (.n (val% «verify_bus_gkr» "last")) k)) (by decide +kernel)
  have hvs := tb_holds_slice hnr h 419 ((List.range 3).map fun k ↦
    [Stmt.atom (.load (.n ((val% «verify_bus_gkr» "s38.u0.s0#0") + k)) (.n (val% «verify_bus_gkr» "last")) (6 + k)),
      .atom (.load (.n ((val% «verify_bus_gkr» "s38.u0.s0#0") + k)) (.n (val% «verify_bus_gkr» "leaves")) k)]).flatten (by decide +kernel)
  rw [tb_holdsList_mapAtoms] at hcs
  rw [tb_holdsList_flatten_range _ _ (fun _ => rfl)] at hvs
  simp only [Atom.Holds] at hcs
  have ecap : ∀ k < 5, σ (.n ((val% «verify_bus_gkr» "s39#0") + k)) = s.cap.getD k 0 := fun k hk =>
    tb_loadHolds_unique (ld _ _ (hcs k hk)) (hcap k hk)
  have eval : ∀ k < 3, LoadHolds Lm.read (σ (.n (val% «verify_bus_gkr» "leaves"))) k (st.values.getD k 0) := by
    intro k hk
    have := hvs k hk
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
    obtain ⟨l1, l2⟩ := this
    have e := tb_loadHolds_unique (by have := ld _ _ l1; rwa [← Nat.add_assoc] at this) (hval k hk)
    rw [e] at l2
    exact l2
  have e414 := tb_loadHolds_unique (ld _ _ l414) hcur
  -- the point's copy
  obtain ⟨-, h7⟩ := tb_holds_callIf hnr h 417 (.n (val% «verify_bus_gkr» "s36#1")) name% «verify_bus_gkr_loop0» [.n (val% «verify_bus_gkr» "s36#2"), .n (val% «verify_bus_gkr» "g_bus_mu"),
      .n (val% «verify_bus_gkr» "zeta"), .n (val% «verify_bus_gkr» "final_point_row")]
    (by decide +kernel)
  have hne7 : σ (.n (val% «verify_bus_gkr» "s36#1")) ≠ 0 := by
    rw [a425, c424, hg]
    intro h0
    have := gen_pow_inj (by omega) (by omega)
      ((e_add_eq_zero_iff.mp h0).symm.trans (pow_zero gen).symm)
    omega
  have hrel7 := h7 hne7
  simp only [List.map_cons, List.map_nil, c426, e423] at hrel7
  have hz := l8_loop hg (by omega) (by omega) hrel7 hpl hpt
  -- the specification's run
  have hs : s = ⟨s.cap, []⟩ := by cases s; simp only at hpe; rw [hpe]
  have r1 := runsTo_readE ⟨[σ (.n (val% «verify_bus_gkr» "fs0")), σ (.n (val% «verify_bus_gkr» "fs1")), σ (.n (val% «verify_bus_gkr» "fs2")), σ (.n (val% «verify_bus_gkr» "fs3")), σ (.n (val% «verify_bus_gkr» "fs4"))], []⟩ (σ (.n (val% «verify_bus_gkr» "x@1")))
  have r2 := runsTo_readE ⟨[σ (.n (val% «verify_bus_gkr» "fs0")), σ (.n (val% «verify_bus_gkr» "fs1")), σ (.n (val% «verify_bus_gkr» "fs2")), σ (.n (val% «verify_bus_gkr» "fs3")), σ (.n (val% «verify_bus_gkr» "fs4"))],
    [(σ (.n (val% «verify_bus_gkr» "x@1")), dsObserve)]⟩ (σ (.n (val% «verify_bus_gkr» "x@2")))
  have ea1 : (⟨[σ (.n (val% «verify_bus_gkr» "fs0")), σ (.n (val% «verify_bus_gkr» "fs1")), σ (.n (val% «verify_bus_gkr» "fs2")), σ (.n (val% «verify_bus_gkr» "fs3")), σ (.n (val% «verify_bus_gkr» "fs4"))], []⟩ : Fs).absorb (σ (.n (val% «verify_bus_gkr» "x@1")))
      dsObserve = ⟨[σ (.n (val% «verify_bus_gkr» "fs0")), σ (.n (val% «verify_bus_gkr» "fs1")), σ (.n (val% «verify_bus_gkr» "fs2")), σ (.n (val% «verify_bus_gkr» "fs3")), σ (.n (val% «verify_bus_gkr» "fs4"))], [(σ (.n (val% «verify_bus_gkr» "x@1")), dsObserve)]⟩ := by
    simp [Fs.absorb, rateScalars]
  have ea2 : (⟨[σ (.n (val% «verify_bus_gkr» "fs0")), σ (.n (val% «verify_bus_gkr» "fs1")), σ (.n (val% «verify_bus_gkr» "fs2")), σ (.n (val% «verify_bus_gkr» "fs3")), σ (.n (val% «verify_bus_gkr» "fs4"))], [(σ (.n (val% «verify_bus_gkr» "x@1")), dsObserve)]⟩ :
      Fs).absorb (σ (.n (val% «verify_bus_gkr» "x@2"))) dsObserve = vbgS1 σ := by
    simp [Fs.absorb, rateScalars, vbgS1]
  rw [ea1] at r1
  rw [ea2] at r2
  have hv : RunsTo (verifyGkrGrandProducts depth)
      ⟨[σ (.n (val% «verify_bus_gkr» "fs0")), σ (.n (val% «verify_bus_gkr» "fs1")), σ (.n (val% «verify_bus_gkr» "fs2")), σ (.n (val% «verify_bus_gkr» "fs3")), σ (.n (val% «verify_bus_gkr» "fs4"))], []⟩
      ([σ (.n (val% «verify_bus_gkr» "x@1"))] ++ ([σ (.n (val% «verify_bus_gkr» "x@2"))] ++ (xs ++ []))) (σ (.n (val% «verify_bus_gkr» "x@2")), st.point, st.values) s :=
    r1.bind (r2.bind (hrun.bind (runsTo_ret _ _)))
  have hph : RunsTo (gkrPhase depth) ⟨[σ (.n (val% «verify_bus_gkr» "fs0")), σ (.n (val% «verify_bus_gkr» "fs1")), σ (.n (val% «verify_bus_gkr» "fs2")), σ (.n (val% «verify_bus_gkr» "fs3")), σ (.n (val% «verify_bus_gkr» "fs4"))], []⟩
      ([σ (.n (val% «verify_bus_gkr» "x@1"))] ++ ([σ (.n (val% «verify_bus_gkr» "x@2"))] ++ (xs ++ [])) ++ ([] ++ []))
      (σ (.n (val% «verify_bus_gkr» "x@2")), st.point, st.values) s :=
    hv.bind ((tb_runsTo_require hcnt s).bind (runsTo_ret _ _))
  rw [hs] at hph
  refine ⟨depth, _, _, s.cap, σ (.n (val% «verify_bus_gkr» "leaves")), hg, hd, ?_, hph, hpl, hvl, hz, ?_, ?_⟩
  · simp only [List.append_nil, List.singleton_append]
    rw [tbReadsAt_cons, tbReadsAt_cons]
    have l33' := (tb_loadHolds_mul_gen_pow Lm.read (σ (.n (val% «verify_bus_gkr» "cursor@1"))) 1 0 (σ (.n (val% «verify_bus_gkr» "x@2")))).mpr l33
    rw [pow_one] at l33'
    refine ⟨l28, l33', ?_⟩
    rw [mul_assoc, ← pow_two]
    exact hrd
  · intro k hk
    have := eval k (by simpa [hvl] using hk)
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk] using this
  · rw [tb_eq_map_getD hcl]
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
      List.cons_append, List.length_append, List.length_cons,
      List.length_nil, List.cons.injEq, and_true]
    refine ⟨ecap 0 (by omega), ecap 1 (by omega), ecap 2 (by omega), ecap 3 (by omega),
      ecap 4 (by omega), ?_, q437⟩
    rw [q436, e414]
    ring

end
end LeanVM.Guest.B1.Tables
