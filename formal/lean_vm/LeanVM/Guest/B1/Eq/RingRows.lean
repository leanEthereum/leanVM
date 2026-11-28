/-
  LeanVM.Guest.B1.Eq.RingRows

  B1 for `ring_rows`: the ring weight's rows of a table's row point, every partial product kept.
-/

module

public import LeanVM.Guest.B1.Eq.RsEqRun
public import LeanVM.Guest.B1.Eq.RsRowsAll
import LeanVM.Guest.ValRef
import LeanVM.Guest.B1.Common.Vc
import LeanVM.Guest.Value.FieldBits
import LeanVM.Guest.Data.ValNames.«ring_rows»

/-!
# `ring_rows` (lean_ethereum.py)

`ring_rows(chain, zs, ps, c_table, count_g)` copies the 64 coefficients at `c_table` into row `0` of
`chain` (`rgInits`), splits `count = 8q + r` from its six hinted bits as `rs_eq_run` does (`rgA`), runs
`ring_rows_loop0` over the `q` full chunks (`rs_eq_rows_all__L8` on row `8t`, `loopRg_sound`), and
dispatches the remainder's `rs_eq_rows_all__L{r}` on row `8q` (`rgT`). Row `m ≤ count` of the chain,
64 words from `chain·g^(64 m)`, is then `ringRow c_k zs[..m] ps[..m] k` (`MeaningRingRows`,
`ring_rows_sound`): `check_stack_terminal` reads row `h_t` for a table of height `2^(h_t)`, the
pointer columns' shared row of the ring weight.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The meaning -/

/-- **`ring_rows(chain, zs, ps, c_table, count_g)`**: `count_g = g^count`, `count < 64`; the words
`zs`, `ps` at `zs`, `ps` below `count` and the 64 words `c` at `c_table`; the chain's row `0` (64 words
at `chain`) is `c`, and its row `m`, `1 ≤ m ≤ count` (64 words from `chain·g^(64 m)`), is
`ringRow c_k zs[..m] ps[..m] k`. It returns nothing. -/
def MeaningRingRows (rd : Reader) : List E → List E → Prop
  | [chain, z, p, ct, cg], rets =>
      ∃ count < 64, cg = gen ^ count ∧ ∃ zs ps c : List E, zs.length = count ∧ ps.length = count ∧
        c.length = 64 ∧ ReadsAt rd z zs ∧ ReadsAt rd p ps ∧ ReadsAt rd ct c ∧ ReadsAt rd chain c ∧
        (∀ m, 1 ≤ m → m ≤ count → ∀ k < 64,
          LoadHolds rd chain (64 * m + k) (ringRow (c.getD k 0) (zs.take m) (ps.take m) k)) ∧
        rets = []
  | _, _ => False

/-! ## The loop -/

theorem find_loopRg : coreProgram.find? name% «ring_rows_loop0» = some fn% «ring_rows_loop0» :=
  coreProgram_find?_at (j := idx% «ring_rows_loop0») rfl

/-- The loop's body at `x`: eight rows from `chain·x^512`, the coordinates from `z·x^8`, `p·x^8`. -/
def LRgBody (rd : Reader) (chain z p x : E) : Prop :=
  ∃ r, coreProgram.Rel rd "rs_eq_rows_all__L8" [chain * x ^ 512, z * x ^ 8, p * x ^ 8] [r]

/-- **`ring_rows_loop0`, one step**, at depth `d + 1`. -/
theorem loopRg_sound (rd : Reader) (N chain z p : E) (d : ℕ) (x : E)
    (h : coreProgram.relN rd (d + 1) name% «ring_rows_loop0» (x :: [N, chain, z, p]) []) :
    LRgBody rd chain z p x ∧ IsInK (x * gen + N) ∧
      (x * gen + N ≠ 0 → coreProgram.relN rd d name% «ring_rows_loop0» (x * gen :: [N, chain, z,
          p]) []) := by
  revert h
  rw [relN_succ_iff_fnSem find_loopRg]
  vc [word_gen, ← pow_two]
  simp only [← pow_mul, Nat.reduceMul, and_true]
  rintro ⟨r, hr, hK, hn⟩
  exact ⟨⟨r, relN_le_rel _ d _ _ _ hr⟩, hK, hn⟩

/-- **`ring_rows_loop0`, one step back**: the body and the next step give the loop at `x`. -/
theorem loopRg_complete (rd : Reader) (N chain z p : E) (x : E) (hB : LRgBody rd chain z p x)
    (hK : IsInK (x * gen + N))
    (hnext : x * gen + N ≠ 0 → coreProgram.Rel rd name% «ring_rows_loop0» (x * gen :: [N, chain, z,
        p]) []) :
    coreProgram.Rel rd name% «ring_rows_loop0» (x :: [N, chain, z, p]) [] := by
  rw [rel_iff_fnSem find_loopRg]
  vc [word_gen, ← pow_two]
  simp only [← pow_mul, Nat.reduceMul, and_true]
  obtain ⟨r, hr⟩ := hB
  exact ⟨r, hr, hK, hnext⟩

/-! ## The template -/

/-- Row `0`'s entry `k`: the coefficient's (`chain[k] = c_table[k]`). -/
def rgInit (k : ℕ) : List Stmt :=
  [.atom (.load (.n ((val% «ring_rows» "s0.u0.s0#0") + k)) (.n (val% «ring_rows» "c_table")) k),
    .atom (.load (.n ((val% «ring_rows» "s0.u0.s0#0") + k)) (.n (val% «ring_rows» "chain")) k)]

/-- Row `0`, the coefficients. -/
def rgInits : List Stmt := ((List.range 64).map rgInit).flatten

/-- `ring_rows`' atoms after row `0`: the count's bits, `r_g`, `q_g`, the check. -/
def rgA : List Stmt :=
  [.atom (.hint (.bitsExp (.n (val% «ring_rows» "count_g")) 6 (.stack [.n (val% «ring_rows» "bits[0]"), .n (val% «ring_rows» "bits[1]"), .n (val% «ring_rows» "bits[2]"), .n (val% «ring_rows» "bits[3]"), .n (val% «ring_rows» "bits[4]"), .n (val% «ring_rows» "bits[5]")]))),
    .atom (.mul (.n (val% «ring_rows» "bits[0]")) (.n (val% «ring_rows» "bits[0]")) (.n (val% «ring_rows» "bits[0]"))), .atom (.const (.n (val% «ring_rows» "r_g@1~0")) (word 1 0)),
    .atom (.const (.n (val% «ring_rows» "r_g@1~1")) (word 3 0)), .atom (.mul (.n (val% «ring_rows» "r_g@1~2")) (.n (val% «ring_rows» "bits[0]")) (.n (val% «ring_rows» "r_g@1~1"))),
    .atom (.add (.n (val% «ring_rows» "r_g@1")) (.n (val% «ring_rows» "r_g@1~0")) (.n (val% «ring_rows» "r_g@1~2"))), .atom (.mul (.n (val% «ring_rows» "bits[1]")) (.n (val% «ring_rows» "bits[1]")) (.n (val% «ring_rows» "bits[1]"))),
    .atom (.const (.n (val% «ring_rows» "r_g@2~0")) (word 1 0)), .atom (.const (.n (val% «ring_rows» "r_g@2~1")) (word 5 0)),
    .atom (.mul (.n (val% «ring_rows» "r_g@2~2")) (.n (val% «ring_rows» "bits[1]")) (.n (val% «ring_rows» "r_g@2~1"))), .atom (.add (.n (val% «ring_rows» "r_g@2~3")) (.n (val% «ring_rows» "r_g@2~0")) (.n (val% «ring_rows» "r_g@2~2"))),
    .atom (.mul (.n (val% «ring_rows» "r_g@2")) (.n (val% «ring_rows» "r_g@1")) (.n (val% «ring_rows» "r_g@2~3"))), .atom (.mul (.n (val% «ring_rows» "bits[2]")) (.n (val% «ring_rows» "bits[2]")) (.n (val% «ring_rows» "bits[2]"))),
    .atom (.const (.n (val% «ring_rows» "r_g@3~0")) (word 1 0)), .atom (.const (.n (val% «ring_rows» "r_g@3~1")) (word 17 0)),
    .atom (.mul (.n (val% «ring_rows» "r_g@3~2")) (.n (val% «ring_rows» "bits[2]")) (.n (val% «ring_rows» "r_g@3~1"))), .atom (.add (.n (val% «ring_rows» "r_g@3~3")) (.n (val% «ring_rows» "r_g@3~0")) (.n (val% «ring_rows» "r_g@3~2"))),
    .atom (.mul (.n (val% «ring_rows» "r_g@3")) (.n (val% «ring_rows» "r_g@2")) (.n (val% «ring_rows» "r_g@3~3"))), .atom (.mul (.n (val% «ring_rows» "bits[3]")) (.n (val% «ring_rows» "bits[3]")) (.n (val% «ring_rows» "bits[3]"))),
    .atom (.const (.n (val% «ring_rows» "q_g@1~0")) (word 1 0)), .atom (.const (.n (val% «ring_rows» "q_g@1~1")) (word 3 0)),
    .atom (.mul (.n (val% «ring_rows» "q_g@1~2")) (.n (val% «ring_rows» "bits[3]")) (.n (val% «ring_rows» "q_g@1~1"))), .atom (.add (.n (val% «ring_rows» "q_g@1")) (.n (val% «ring_rows» "q_g@1~0")) (.n (val% «ring_rows» "q_g@1~2"))),
    .atom (.mul (.n (val% «ring_rows» "bits[4]")) (.n (val% «ring_rows» "bits[4]")) (.n (val% «ring_rows» "bits[4]"))), .atom (.const (.n (val% «ring_rows» "q_g@2~0")) (word 1 0)),
    .atom (.const (.n (val% «ring_rows» "q_g@2~1")) (word 5 0)), .atom (.mul (.n (val% «ring_rows» "q_g@2~2")) (.n (val% «ring_rows» "bits[4]")) (.n (val% «ring_rows» "q_g@2~1"))),
    .atom (.add (.n (val% «ring_rows» "q_g@2~3")) (.n (val% «ring_rows» "q_g@2~0")) (.n (val% «ring_rows» "q_g@2~2"))), .atom (.mul (.n (val% «ring_rows» "q_g@2")) (.n (val% «ring_rows» "q_g@1")) (.n (val% «ring_rows» "q_g@2~3"))),
    .atom (.mul (.n (val% «ring_rows» "bits[5]")) (.n (val% «ring_rows» "bits[5]")) (.n (val% «ring_rows» "bits[5]"))), .atom (.const (.n (val% «ring_rows» "q_g@3~0")) (word 1 0)),
    .atom (.const (.n (val% «ring_rows» "q_g@3~1")) (word 17 0)), .atom (.mul (.n (val% «ring_rows» "q_g@3~2")) (.n (val% «ring_rows» "bits[5]")) (.n (val% «ring_rows» "q_g@3~1"))),
    .atom (.add (.n (val% «ring_rows» "q_g@3~3")) (.n (val% «ring_rows» "q_g@3~0")) (.n (val% «ring_rows» "q_g@3~2"))), .atom (.mul (.n (val% «ring_rows» "q_g@3")) (.n (val% «ring_rows» "q_g@2")) (.n (val% «ring_rows» "q_g@3~3"))),
    .atom (.mul (.n (val% «ring_rows» "s1.i0:split_count.s5#0")) (.n (val% «ring_rows» "q_g@3")) (.n (val% «ring_rows» "q_g@3"))), .atom (.mul (.n (val% «ring_rows» "s1.i0:split_count.s5#1")) (.n (val% «ring_rows» "s1.i0:split_count.s5#0")) (.n (val% «ring_rows» "s1.i0:split_count.s5#0"))),
    .atom (.mul (.n (val% «ring_rows» "s1.i0:split_count.s5#2")) (.n (val% «ring_rows» "s1.i0:split_count.s5#1")) (.n (val% «ring_rows» "s1.i0:split_count.s5#1"))), .atom (.mul (.n (val% «ring_rows» "s1.i0:split_count.s5#3")) (.n (val% «ring_rows» "s1.i0:split_count.s5#2")) (.n (val% «ring_rows» "r_g@3"))),
    .atom (.assertEq (.n (val% «ring_rows» "s1.i0:split_count.s5#3")) (.n (val% «ring_rows» "count_g")))]

/-- The loop's guard and call, the remainder's pointers, its dispatch. -/
def rgT : List Stmt :=
  [.atom (.const (.n (val% «ring_rows» "s2#0")) (word 1 0)), .atom (.add (.n (val% «ring_rows» "s2#1")) (.n (val% «ring_rows» "s2#0")) (.n (val% «ring_rows» "q_g@3"))),
    .atom (.const (.n (val% «ring_rows» "s2#2")) (word 1 0)),
    .callIf (.n (val% «ring_rows» "s2#1")) name% «ring_rows_loop0» [.n (val% «ring_rows» "s2#2"), .n (val% «ring_rows» "q_g@3"), .n (val% «ring_rows» "chain"), .n (val% «ring_rows» "zs"), .n (val% «ring_rows» "ps")],
    .atom (.mul (.n (val% «ring_rows» "base~0")) (.n (val% «ring_rows» "q_g@3")) (.n (val% «ring_rows» "q_g@3"))),
    .atom (.mul (.n (val% «ring_rows» "base~1")) (.n (val% «ring_rows» "base~0")) (.n (val% «ring_rows» "base~0"))),
    .atom (.mul (.n (val% «ring_rows» "base")) (.n (val% «ring_rows» "base~1")) (.n (val% «ring_rows» "base~1"))),
    .atom (.mul (.n (val% «ring_rows» "done~1")) (.n (val% «ring_rows» "base")) (.n (val% «ring_rows» "base"))),
    .atom (.mul (.n (val% «ring_rows» "done~2")) (.n (val% «ring_rows» "done~1")) (.n (val% «ring_rows» "done~1"))),
    .atom (.mul (.n (val% «ring_rows» "done~3")) (.n (val% «ring_rows» "done~2")) (.n (val% «ring_rows» "done~2"))),
    .atom (.mul (.n (val% «ring_rows» "done~4")) (.n (val% «ring_rows» "done~3")) (.n (val% «ring_rows» "done~3"))),
    .atom (.mul (.n (val% «ring_rows» "done~5")) (.n (val% «ring_rows» "done~4")) (.n (val% «ring_rows» "done~4"))),
    .atom (.mul (.n (val% «ring_rows» "done~6")) (.n (val% «ring_rows» "done~5")) (.n (val% «ring_rows» "done~5"))),
    .atom (.mul (.n (val% «ring_rows» "done~7")) (.n (val% «ring_rows» "chain")) (.n (val% «ring_rows» "done~6"))),
    .atom (.mul (.n (val% «ring_rows» "done~8")) (.n (val% «ring_rows» "zs")) (.n (val% «ring_rows» "base"))),
    .atom (.mul (.n (val% «ring_rows» "done~9")) (.n (val% «ring_rows» "ps")) (.n (val% «ring_rows» "base"))),
    .dispatch (.n (val% «ring_rows» "r_g@3")) ["rs_eq_rows_all__L0", "rs_eq_rows_all__L1", "rs_eq_rows_all__L2",
      "rs_eq_rows_all__L3", "rs_eq_rows_all__L4", "rs_eq_rows_all__L5", "rs_eq_rows_all__L6",
      "rs_eq_rows_all__L7"] [.n (val% «ring_rows» "done~7"), .n (val% «ring_rows» "done~8"), .n (val% «ring_rows» "done~9")] [.n (val% «ring_rows» "done")]]

/-- **The expansion of `ring_rows`.** -/
def rgBody : List Stmt := rgInits ++ (rgA ++ (rgT ++ [.ret []]))

theorem ring_rows_body : Fn.body fn% «ring_rows» = rgBody := stmtsEqb_sound (by decide +kernel)

theorem find_ring_rows : coreProgram.find? "ring_rows" = some fn% «ring_rows» :=
  coreProgram_find?_at (j := idx% «ring_rows») rfl

/-! ## The rows from the chunks -/

/-- The word at `p·g^j`, `0` where memory has none. -/
def memW (rd : Reader) (p : E) (j : ℕ) : E := (rd (p.limb 0 * addressOfIndex j)).getD 0

theorem memW_of_load {rd : Reader} {p : E} {j : ℕ} {w : E} (h : LoadHolds rd p j w) :
    memW rd p j = w := by
  unfold memW; rw [h.2]; rfl

theorem load_memW {rd : Reader} {p : E} {j : ℕ} {w : E} (h : LoadHolds rd p j w) :
    LoadHolds rd p j (memW rd p j) := by
  rw [memW_of_load h]; exact h

/-- Chunk `t` of `n` coordinates: its words from `z·g^(8t)`, `p·g^(8t)`, its row `8t` from
`chain·g^(64·8t)`, and the `n` rows after it. -/
def ChunkAll (rd : Reader) (chain z p : E) (t n : ℕ) : Prop :=
  ∃ zt pt ct : List E, zt.length = n ∧ pt.length = n ∧ ct.length = 64 ∧
    ReadsAt rd (z * gen ^ (8 * t)) zt ∧ ReadsAt rd (p * gen ^ (8 * t)) pt ∧
    ReadsAt rd (chain * gen ^ (64 * (8 * t))) ct ∧
    ∀ i < n, ∀ k < 64, LoadHolds rd (chain * gen ^ (64 * (8 * t))) (64 * (i + 1) + k)
      (ringRow (ct.getD k 0) (zt.take (i + 1)) (pt.take (i + 1)) k)

theorem chunkAll_of_meaning {rd : Reader} {chain z p ret : E} {t n : ℕ} (hn : 0 < n)
    (h : MeaningRsEqRowsAll n rd [chain * gen ^ (64 * (8 * t)), z * gen ^ (8 * t), p * gen ^ (8 * t)] [ret]) :
    ChunkAll rd chain z p t n := by
  obtain ⟨zt, pt, ct, a, b, c, d, e, f, g⟩ := h.2 hn
  exact ⟨zt, pt, ct, a, b, c, d, e, f, g⟩

/-- A chunk's words are memory's. -/
theorem chunk_words {rd : Reader} {q : E} {o n : ℕ} {xs : List E} (hl : xs.length = n)
    (h : ReadsAt rd (q * gen ^ o) xs) :
    xs = (List.range n).map (fun i ↦ memW rd q (o + i)) ∧ ∀ i < n, LoadHolds rd q (o + i) (memW rd q (o + i)) := by
  have hl' := readsAt_mul_gen_pow.mp h
  refine ⟨List.ext_getElem (by simp [hl]) fun i h1 h2 ↦ ?_, fun i hi ↦ load_memW (hl' i (by omega))⟩
  have := hl' i h1
  rw [List.getD_eq_getElem _ _ h1] at this
  simp [memW_of_load this]

theorem take_split (f : ℕ → E) (count a b : ℕ) (h : a + b ≤ count) :
    ((List.range count).map f).take (a + b) =
      ((List.range count).map f).take a ++ (List.range b).map fun i ↦ f (a + i) := by
  rw [List.take_add]
  congr 1
  apply List.ext_getElem (by simp; omega)
  intro j h1 h2
  simp

/-- **The rows after a chunk**: row `8t` and the chunk give rows `8t + 1 .. 8t + n`. -/
theorem rows_of_chunkAll {rd : Reader} {chain z p : E} {t n count : ℕ} (C : ℕ → E)
    (hc : 8 * t + n ≤ count) (hch : ChunkAll rd chain z p t n)
    (hrow : ∀ k < 64, LoadHolds rd chain (64 * (8 * t) + k)
      (ringRow (C k) (((List.range count).map (memW rd z)).take (8 * t))
        (((List.range count).map (memW rd p)).take (8 * t)) k)) :
    ∀ i < n, ∀ k < 64, LoadHolds rd chain (64 * (8 * t + i + 1) + k)
      (ringRow (C k) (((List.range count).map (memW rd z)).take (8 * t + i + 1))
        (((List.range count).map (memW rd p)).take (8 * t + i + 1)) k) := by
  obtain ⟨zt, pt, ct, hz, hp, hc64, rz, rp, rc, hr⟩ := hch
  obtain ⟨ez, -⟩ := chunk_words hz rz
  obtain ⟨ep, -⟩ := chunk_words hp rp
  intro i hi k hk
  have h1 := hr i hi k hk
  rw [loadHolds_mul_gen_pow, show 64 * (8 * t) + (64 * (i + 1) + k) = 64 * (8 * t + i + 1) + k by ring] at h1
  have hct : ct.getD k 0 = ringRow (C k) (((List.range count).map (memW rd z)).take (8 * t))
      (((List.range count).map (memW rd p)).take (8 * t)) k := by
    have := readsAt_mul_gen_pow.mp rc k (by omega)
    exact loadHolds_unique this (hrow k hk)
  rw [hct, ← ringRow_append _ _ _ _ _ _ (by simp)] at h1
  rw [show 8 * t + i + 1 = 8 * t + (i + 1) by ring, take_split _ _ _ _ (by omega),
    take_split _ _ _ _ (by omega)]
  convert h1 using 3
  · rw [ez, ← List.map_take, List.take_range, min_eq_left (by omega)]
  · rw [ep, ← List.map_take, List.take_range, min_eq_left (by omega)]

/-! ## Soundness -/

theorem rgInit_noRet (k : ℕ) : Stmt.noRetList (rgInit k) = true := rfl

theorem rgNames_get (j : ℕ) (hj : j < 8) :
    ["rs_eq_rows_all__L0", "rs_eq_rows_all__L1", "rs_eq_rows_all__L2", "rs_eq_rows_all__L3",
      "rs_eq_rows_all__L4", "rs_eq_rows_all__L5", "rs_eq_rows_all__L6", "rs_eq_rows_all__L7"][j] =
      rsEqRowsAllNames.getD j "" := by
  interval_cases j <;> rfl

/-- **`ring_rows`' core IR gives its meaning.** -/
theorem ring_rows_sound (rd : Reader) (args rets : List E)
    (h : coreProgram.Rel rd "ring_rows" args rets) : MeaningRingRows rd args rets := by
  obtain ⟨w3, w5, w17⟩ := rs_consts
  rw [rel_iff_sem find_ring_rows, show Fn.params fn% «ring_rows» = [.n (val% «ring_rows» "chain"), .n (val% «ring_rows» "zs"),
      .n (val% «ring_rows» "ps"), .n (val% «ring_rows» "c_table"), .n (val% «ring_rows» "count_g")] from rfl, ring_rows_body, rgBody] at h
  obtain ⟨σ, hp, h⟩ := h
  subst hp
  rw [holdsList_append, rgInits, holdsList_range_flatten 64 rgInit rgInit_noRet] at h
  obtain ⟨hinit, h⟩ := h
  simp only [rgA, List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    true_and] at h
  obtain ⟨b0, h10, h11, h12, h13, b1, h14, h15, h16, h17, h18, b2, h19, h20, h21, h22, h23,
    b3, h24, h25, h26, h27, b4, h28, h29, h30, h31, h32, b5, h33, h34, h35, h36, h37, h38, h39,
    h40, h41, ha, h⟩ := h
  simp only [rgT, List.cons_append, List.nil_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    List.map_cons, List.map_nil] at h
  obtain ⟨h42, h43, h44, hK, hcall, h45, h46, h47, d1, d2, d3, d4, d5, d6, d7, d8, d9,
    ⟨j, hj, hx, hdisp⟩, hret⟩ := h
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
  -- the loop over the full chunks
  rw [h43, h42, word_one] at hK hcall
  rw [h44, word_one] at hcall
  obtain ⟨m, hm, hm', hB⟩ := (guarded_loop_rel_iff
    (fun d x ↦ loopRg_sound rd (σ (.n (val% «ring_rows» "q_g@3"))) (σ (.n (val% «ring_rows» "chain"))) (σ (.n (val% «ring_rows» "zs"))) (σ (.n (val% «ring_rows» "ps"))) d x)
    (fun x hb hk hn ↦ loopRg_complete rd _ _ _ _ x hb hk hn)).mp ⟨hK, hcall⟩
  have hmq : m = q := by
    rw [qg] at hm'
    exact gen_pow_inj hm (by show q < 2 ^ 64 - 1; omega) hm'.symm
  subst hmq
  have hch : ∀ t < q, ChunkAll rd (σ (.n (val% «ring_rows» "chain"))) (σ (.n (val% «ring_rows» "zs"))) (σ (.n (val% «ring_rows» "ps"))) t 8 := fun t ht ↦ by
    obtain ⟨ret, hr⟩ := hB t ht
    rw [← pow_mul, ← pow_mul, show t * 512 = 64 * (8 * t) by ring, Nat.mul_comm t 8] at hr
    exact chunkAll_of_meaning (by norm_num) (rs_eq_rows_all_holds 8 le_rfl rd _ _ hr)
  -- the remainder
  have hj' : j = r := by
    rw [rg, gen_pow_eq_ofK] at hx
    exact gen_pow_inj (by simp only [List.length_cons, List.length_nil] at hj; show j < 2 ^ 64 - 1; omega)
      (by show r < 2 ^ 64 - 1; omega) (by rw [gen_pow_eq_ofK, gen_pow_eq_ofK]; exact hx.symm)
  subst hj'
  rw [rgNames_get _ hj] at hdisp
  have e7 : σ (.n (val% «ring_rows» "done~7")) = σ (.n (val% «ring_rows» "chain")) * gen ^ (64 * (8 * q)) := by
    rw [d7, d6, d5, d4, d3, d2, d1, h47, h46, h45, qg]; ring
  have e8 : σ (.n (val% «ring_rows» "done~8")) = σ (.n (val% «ring_rows» "zs")) * gen ^ (8 * q) := by rw [d8, h47, h46, h45, qg]; ring
  have e9 : σ (.n (val% «ring_rows» "done~9")) = σ (.n (val% «ring_rows» "ps")) * gen ^ (8 * q) := by rw [d9, h47, h46, h45, qg]; ring
  rw [e7, e8, e9] at hdisp
  have hlast : 0 < r → ChunkAll rd (σ (.n (val% «ring_rows» "chain"))) (σ (.n (val% «ring_rows» "zs"))) (σ (.n (val% «ring_rows» "ps"))) q r := fun h0 ↦
    chunkAll_of_meaning h0 (rs_eq_rows_all_holds r (by omega) rd _ _ hdisp)
  clear_value r q
  -- the words
  obtain ⟨count, hcount⟩ : ∃ count, count = 8 * q + r := ⟨_, rfl⟩
  rw [← hcount] at hcg
  set Zl := (List.range count).map (memW rd (σ (.n (val% «ring_rows» "zs")))) with hZl
  set Pl := (List.range count).map (memW rd (σ (.n (val% «ring_rows» "ps")))) with hPl
  set C : ℕ → E := fun k ↦ σ (.n ((val% «ring_rows» "s0.u0.s0#0") + k)) with hC
  have hloads : ∀ i < count, LoadHolds rd (σ (.n (val% «ring_rows» "zs"))) i (memW rd (σ (.n (val% «ring_rows» "zs"))) i) ∧
      LoadHolds rd (σ (.n (val% «ring_rows» "ps"))) i (memW rd (σ (.n (val% «ring_rows» "ps"))) i) := by
    intro i hi
    by_cases ht : i / 8 < q
    · obtain ⟨zt, pt, ct, hz, hp, -, rz, rp, -, -⟩ := hch (i / 8) ht
      have a := (chunk_words hz rz).2 (i % 8) (Nat.mod_lt _ (by norm_num))
      have b := (chunk_words hp rp).2 (i % 8) (Nat.mod_lt _ (by norm_num))
      rw [Nat.div_add_mod] at a b
      exact ⟨a, b⟩
    · obtain ⟨zt, pt, ct, hz, hp, -, rz, rp, -, -⟩ := hlast (by omega)
      have a := (chunk_words hz rz).2 (i - 8 * q) (by omega)
      have b := (chunk_words hp rp).2 (i - 8 * q) (by omega)
      rw [show 8 * q + (i - 8 * q) = i by omega] at a b
      exact ⟨a, b⟩
  -- the rows
  have hrows : ∀ n ≤ count, ∀ k < 64, LoadHolds rd (σ (.n (val% «ring_rows» "chain"))) (64 * n + k)
      (ringRow (C k) (Zl.take n) (Pl.take n) k) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn k hk
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        rw [ringRow_nil]
        have := hinit k hk
        simp only [rgInit, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
        simpa using this.2
      · obtain ⟨t, i, hi8, rfl⟩ : ∃ t i, i < 8 ∧ n = 8 * t + i + 1 :=
          ⟨(n - 1) / 8, (n - 1) % 8, Nat.mod_lt _ (by norm_num), by omega⟩
        have hprev := ih (8 * t) (by omega) (by omega)
        by_cases ht : t < q
        · exact rows_of_chunkAll C (by omega) (hch t ht) hprev i hi8 k hk
        · obtain rfl : t = q := by omega
          exact rows_of_chunkAll C (by omega) (hlast (by omega)) hprev i (by omega) k hk
  refine ⟨count, by omega, hcg, Zl, Pl, (List.range 64).map C, by simp [hZl], by simp [hPl], by simp,
    readsAt_range fun i hi ↦ (hloads i hi).1, readsAt_range fun i hi ↦ (hloads i hi).2,
    readsAt_range fun k hk ↦ ?_, readsAt_range fun k hk ↦ ?_, fun n h1 h2 k hk ↦ ?_, hret.symm⟩
  · have := hinit k hk
    simp only [rgInit, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
    exact this.1
  · have := hinit k hk
    simp only [rgInit, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at this
    exact this.2
  · have := hrows n h2 k hk
    rwa [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]

end
end LeanVM.Guest.B1
