/-
  LeanVM.Guest.B1.Main.AggCols

  The column challenges in `aggregate_claims`: their squeezes, their equality table (`eqtree`,
  inlined), their equality factor at the sumcheck's point, and the algebra that reads them as the
  batching program's `foldColumns` and batched weight.
-/

module

public import LeanVM.Guest.B1.Main.AggRun
public import LeanVM.Guest.B1.Main.AggSqueeze
public import LeanVM.Guest.Batch.Split

/-!
# The column challenges

* `sqChain_sound`: `n` checked `KECCAK`s, block `k` reading eight zero rate cells and block
  `k - 1`'s capacity outputs (block `0` a given capacity), each block's cell `0` stored at
  `col[k]`, are `n` squeezes of the carried sponge (`sqIter`, `Fs.squeezeN`).
* `tree_sound`: `eqtree(col, tree, n)` inlined, checked level by level (`treeOk`), writes the
  equality table of the first `t + 1` challenges at offset `2^(t+1) - 2` (`eqLevels`, which is
  `eqKernel`, `eqLevels_eqKernel`).
* `eqcChain_sound`: `Π_{j < n} (col[j] + pt1[off + j])`, `pt1 = 1 + r`, is `eqEval`.
* `fvAcc_eq_foldColumns`: the loop's fold of a fresh claim's values is `foldColumns`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node LeanVM.Guest.B1 Finset

@[expose] public section

variable {rd : Reader} {σ : Val} {atoms : List Atom}

/-! ## Squeezes -/

/-- The sponge after `k` squeezes. -/
def sqIter : ℕ → Fs → Fs
  | 0, s => s
  | k + 1, s => sqIter k s.squeeze.2

theorem squeezeN_getD : ∀ (n : ℕ) (s : Fs) (k : ℕ), k < n →
    (s.squeezeN n).1.getD k 0 = (sqIter k s).squeeze.1
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, _, 0, _ => rfl
  | n + 1, s, k + 1, h => by
    simp only [Fs.squeezeN, List.getD_cons_succ]
    exact squeezeN_getD n _ k (by omega)

theorem squeezeN_snd : ∀ (n : ℕ) (s : Fs), (s.squeezeN n).2 = sqIter n s
  | 0, _ => rfl
  | n + 1, s => squeezeN_snd n s.squeeze.2

theorem length_squeezeN : ∀ (n : ℕ) (s : Fs), (s.squeezeN n).1.length = n
  | 0, _ => rfl
  | n + 1, s => by simp [Fs.squeezeN, length_squeezeN n]

theorem sqIter_succ : ∀ (k : ℕ) (s : Fs), sqIter (k + 1) s = (sqIter k s).squeeze.2
  | 0, _ => rfl
  | k + 1, s => sqIter_succ k s.squeeze.2

theorem sqIter_pend : ∀ (k : ℕ) (s : Fs), s.pend = [] → (sqIter k s).pend = []
  | 0, _, h => h
  | k + 1, _, _ => sqIter_pend k _ rfl

theorem rateOf_nil : rateOf [] = List.replicate 8 0 := by
  simp [rateOf, List.range_succ, Keccak.rateCell_past]

/-- Block `k`'s inputs: eight zero rate cells, then block `k - 1`'s capacity outputs (`cap0` for
block `0`); its outputs from `b + 13k`. -/
def sqIns (zs cap0 : List V) (b : ℕ) : ℕ → List V
  | 0 => zs ++ cap0
  | k + 1 => zs ++ (List.range 5).map fun i => .n (b + 13 * k + 8 + i)

/-- Block `k`'s outputs. -/
def sqOuts (b k : ℕ) : List V := (List.range 13).map fun i => .n (b + 13 * k + i)

/-- **`n` squeezes, checked**: each block a `KECCAK` from `sqIns` to `sqOuts`, its cell `0` stored
at `col[k]`. -/
def sqChainOk (A : List Atom) (zs cap0 : List V) (b : ℕ) (colP : V) (n : ℕ) : Bool :=
  (List.range n).all fun k => A.any (isKeccakAt (sqIns zs cap0 b k) (sqOuts b k) false false) &&
    A.any (isLoadAt (.n (b + 13 * k)) colP k)

theorem sqOuts_getD (b k c : ℕ) (hc : c < 13) : (sqOuts b k).getD c default = .n (b + 13 * k + c) := by
  simp [sqOuts, List.getD_eq_getElem?_getD, hc]

/-- **The checked chain is `n` squeezes** of a carried sponge with nothing waiting whose capacity
`cap0` holds: block `k`'s cell `0`, stored at `col[k]`, is the `k`-th challenge, and the last
block's capacity outputs are the sponge's after them. -/
theorem sqChain_sound {zs cap0 : List V} {b : ℕ} {colP : V} {n : ℕ} {s : Fs}
    (h : sqChainOk atoms zs cap0 b colP n = true) (hat : ∀ a ∈ atoms, a.Holds rd σ)
    (hz : zs.map σ = List.replicate 8 0) (hs : s.pend = []) (hc : cap0.map σ = s.cap) :
    (∀ k < n, memAt rd (σ colP) k = (sqIter k s).squeeze.1) ∧
      (0 < n → ((List.range 5).map fun i => σ (.n (b + 13 * (n - 1) + 8 + i))) = (sqIter n s).cap) := by
  simp only [sqChainOk, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  -- block `k` reads `0⁸` and the capacity of the sponge after `k` squeezes, and permutes it
  have key : ∀ k < n, (sqIns zs cap0 b k).map σ = List.replicate 8 0 ++ (sqIter k s).cap ∧
      ∀ c (hc : c < 13), σ (.n (b + 13 * k + c)) = cellsOfState (sqIter k s).perm false ⟨c, hc⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hin : (sqIns zs cap0 b 0).map σ = List.replicate 8 0 ++ (sqIter 0 s).cap := by
        simp only [sqIns, List.map_append, hz, hc, sqIter]
      refine ⟨hin, fun c hc => ?_⟩
      have := DupSpec.keccak_facts (keccak_sound (h 0 hk).1 hat) (by simp [sqOuts]) c hc
      rw [sqOuts_getD _ _ _ hc, hin] at this
      rw [this, Fs.perm, sqIter_pend 0 s hs, rateOf_nil]
    | succ k ih =>
      intro hk
      obtain ⟨-, hout⟩ := ih (by omega)
      have hin : (sqIns zs cap0 b (k + 1)).map σ = List.replicate 8 0 ++ (sqIter (k + 1) s).cap := by
        rw [sqIter_succ, sqIns, List.map_append, hz]
        congr 1
        simp only [List.map_map, Function.comp_def]
        rw [show (List.range 5).map (fun i => σ (.n (b + 13 * k + 8 + i))) =
          [σ (.n (b + 13 * k + 8)), σ (.n (b + 13 * k + 9)), σ (.n (b + 13 * k + 10)),
            σ (.n (b + 13 * k + 11)), σ (.n (b + 13 * k + 12))] from rfl,
          hout 8 (by omega), hout 9 (by omega), hout 10 (by omega), hout 11 (by omega),
          hout 12 (by omega)]
        rfl
      refine ⟨hin, fun c hc => ?_⟩
      have := DupSpec.keccak_facts (keccak_sound (h (k + 1) hk).1 hat) (by simp [sqOuts]) c hc
      rw [sqOuts_getD _ _ _ hc, hin] at this
      rw [this, Fs.perm, sqIter_pend _ s hs, rateOf_nil]
  refine ⟨fun k hk => ?_, fun hn => ?_⟩
  · have hl := memAt_of_load (load_sound (h k hk).2 hat)
    rw [hl, show b + 13 * k = b + 13 * k + 0 from rfl, (key k hk).2 0 (by omega), Fs.squeeze,
      Keccak.challengeOf_cells]
    rfl
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hout := (key m (by omega)).2
    rw [sqIter_succ, Nat.add_sub_cancel]
    show _ = capOf (sqIter m s).perm
    rw [show (List.range 5).map (fun i => σ (.n (b + 13 * m + 8 + i))) =
      [σ (.n (b + 13 * m + 8)), σ (.n (b + 13 * m + 9)), σ (.n (b + 13 * m + 10)),
        σ (.n (b + 13 * m + 11)), σ (.n (b + 13 * m + 12))] from rfl,
      hout 8 (by omega), hout 9 (by omega), hout 10 (by omega), hout 11 (by omega),
      hout 12 (by omega)]
    rfl

/-! ## The equality table -/

/-- The equality table of the challenges `c 0, …, c t`, as `eqtree` doubles it. -/
def eqLevels (c : ℕ → E) : ℕ → List E
  | 0 => [1 + c 0, c 0]
  | t + 1 => (eqLevels c t).map (· * (1 + c (t + 1))) ++ (eqLevels c t).map (· * c (t + 1))

theorem getD_map_lt {f : E → E} {l : List E} {j : ℕ} (hj : j < l.length) :
    (l.map f).getD j 0 = f (l.getD j 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj, List.getElem_map]

theorem length_eqLevels (c : ℕ → E) : ∀ t, (eqLevels c t).length = 2 ^ (t + 1)
  | 0 => rfl
  | t + 1 => by simp [eqLevels, length_eqLevels c t, pow_succ]; ring

theorem eqLevels_congr {c c' : ℕ → E} : ∀ {t : ℕ}, (∀ k ≤ t, c k = c' k) →
    eqLevels c t = eqLevels c' t
  | 0, h => by simp [eqLevels, h 0 le_rfl]
  | t + 1, h => by
    simp only [eqLevels, eqLevels_congr (t := t) (fun k hk => h k (by omega)), h (t + 1) le_rfl]

/-- A list equation under `zipWith`, its left arguments in a list. -/
theorem zipWith_congr_mem {α β γ : Type} {f g : α → β → γ} :
    ∀ (xs : List α) (ys : List β), (∀ x ∈ xs, ∀ y, f x y = g x y) →
      List.zipWith f xs ys = List.zipWith g xs ys
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | x :: xs, y :: ys, h => by
    rw [List.zipWith_cons_cons, List.zipWith_cons_cons, h x (by simp) y,
      zipWith_congr_mem xs ys fun x' hx' y' => h x' (by simp [hx']) y']

/-- **`eqtree`'s table is `eqKernel`.** -/
theorem eqLevels_eqKernel (cols : List E) : ∀ t, t < cols.length →
    eqLevels (fun k => cols.getD k 0) t = eqKernel (cols.take (t + 1))
  | 0, h => by
    obtain ⟨x, rest, rfl⟩ : ∃ x rest, cols = x :: rest := ⟨cols.head (by intro e; simp [e] at h),
      cols.tail, (List.cons_head_tail _).symm⟩
    simp [eqLevels, eqKernel]
  | t + 1, h => by
    rw [List.take_succ_eq_append_getElem h, Hotwire.eqKernel_append, ← eqLevels_eqKernel cols t
      (by omega), eqLevels, List.getD_eq_getElem _ _ h]

/-- **`eqtree(col, tree, n)`, checked**: level `0` (`1 + col[0]`, `col[0]` at offsets `0`, `1`,
through `r0`, `r0 + 1`, `r0 + 2`), then each level `t` from its values `B t` on: `col[t]`, `1`,
`1 + col[t]`, then per entry `i` the previous level's word, its products by `1 + col[t]` and by
`col[t]` stored at `2^(t+1) - 2 + i` and `2^(t+1) - 2 + 2^t + i`. -/
def treeOk (A : List Atom) (colP treeP : V) (r0 : ℕ) (B : ℕ → ℕ) (n : ℕ) : Bool :=
  A.any (isLoadAt (.n r0) colP 0) && A.any (isConstAt (.n (r0 + 1)) 1 0) &&
  A.any (isAddAt (.n (r0 + 2)) (.n (r0 + 1)) (.n r0)) && A.any (isLoadAt (.n (r0 + 2)) treeP 0) &&
  A.any (isLoadAt (.n r0) treeP 1) &&
  (List.range n).all fun t => decide (t = 0) ||
    (A.any (isLoadAt (.n (B t)) colP t) && A.any (isConstAt (.n (B t + 1)) 1 0) &&
      A.any (isAddAt (.n (B t + 2)) (.n (B t + 1)) (.n (B t))) &&
      (List.range (2 ^ t)).all fun i =>
        A.any (isLoadAt (.n (B t + 3 + 3 * i)) treeP (2 ^ t - 2 + i)) &&
        isMul A (.n (B t + 4 + 3 * i)) (.n (B t + 3 + 3 * i)) (.n (B t + 2)) &&
        A.any (isLoadAt (.n (B t + 4 + 3 * i)) treeP (2 ^ (t + 1) - 2 + i)) &&
        isMul A (.n (B t + 5 + 3 * i)) (.n (B t + 3 + 3 * i)) (.n (B t)) &&
        A.any (isLoadAt (.n (B t + 5 + 3 * i)) treeP (2 ^ (t + 1) - 2 + 2 ^ t + i)))

/-- **The checked table**: level `t`'s entry `j` lies at `2^(t+1) - 2 + j`. -/
theorem tree_sound {colP treeP : V} {r0 : ℕ} {B : ℕ → ℕ} {n : ℕ}
    (h : treeOk atoms colP treeP r0 B n = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    ∀ t < n, ∀ j < 2 ^ (t + 1), LoadHolds rd (σ treeP) (2 ^ (t + 1) - 2 + j)
      ((eqLevels (memAt rd (σ colP)) t).getD j 0) := by
  simp only [treeOk, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨l0, c0⟩, a0⟩, s0⟩, s1⟩, hl⟩ := h
  intro t
  induction t with
  | zero =>
    intro _ j hj
    have e0 := memAt_of_load (load_sound l0 hat)
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · have := load_sound s0 hat
      rwa [add_sound a0 hat, const_sound c0 hat, word_one, ← e0] at this
    · have := load_sound s1 hat
      rwa [← e0] at this
  | succ t ih =>
    intro hn j hj
    rcases hl (t + 1) hn with h0 | ⟨⟨⟨hlt, hct⟩, hat'⟩, hi⟩
    · omega
    have et := memAt_of_load (load_sound hlt hat)
    have hB2 : σ (.n (B (t + 1) + 2)) = 1 + memAt rd (σ colP) (t + 1) := by
      rw [add_sound hat' hat, const_sound hct hat, word_one, et]
    have hlen := length_eqLevels (memAt rd (σ colP)) t
    by_cases hj1 : j < 2 ^ (t + 1)
    · obtain ⟨⟨⟨⟨p, m1⟩, s1'⟩, -⟩, -⟩ := hi j hj1
      have hp := ih (by omega) j hj1
      have ep := memAt_of_load (load_sound p hat)
      rw [show 2 ^ (t + 1) - 2 + j = 2 ^ (t + 1) - 2 + j from rfl] at ep
      have := load_sound s1' hat
      rw [isMul_sound m1 hat, hB2, ← ep, memAt_of_load hp] at this
      rw [eqLevels, List.getD_append _ _ _ _ (by simp [hlen]; exact hj1), getD_map_lt (by rw [hlen]; exact hj1)]
      · exact this
    · obtain ⟨i, rfl⟩ : ∃ i, j = 2 ^ (t + 1) + i := ⟨j - 2 ^ (t + 1), by omega⟩
      have hi1 : i < 2 ^ (t + 1) := by rw [pow_succ] at hj; omega
      obtain ⟨⟨⟨⟨p, -⟩, -⟩, m2⟩, s2⟩ := hi i hi1
      have hp := ih (by omega) i hi1
      have ep := memAt_of_load (load_sound p hat)
      have := load_sound s2 hat
      rw [isMul_sound m2 hat, ← et, ← ep, memAt_of_load hp,
        show 2 ^ (t + 1 + 1) - 2 + 2 ^ (t + 1) + i = 2 ^ (t + 1 + 1) - 2 + (2 ^ (t + 1) + i) by omega]
        at this
      rw [eqLevels, List.getD_append_right _ _ _ _ (by simp [hlen]), List.length_map, hlen,
        Nat.add_sub_cancel_left, getD_map_lt (by rw [hlen]; exact hi1)]
      exact this

/-! ## The column factor -/

/-- `t = col[j] + pt1[off + j]`, one `ADD` of loads through `pC`, `pR`. -/
def eqcTermOk (A : List Atom) (t pC pR : V) (off j : ℕ) : Bool :=
  match addOf A t with
  | some (a, b) => A.any (isLoadAt a pC j) && A.any (isLoadAt b pR (off + j))
  | none => false

theorem eqcTerm_sound {t pC pR : V} {off j : ℕ} (h : eqcTermOk atoms t pC pR off j = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    σ t = memAt rd (σ pC) j + memAt rd (σ pR) (off + j) := by
  unfold eqcTermOk at h
  split at h
  · rename_i a b hm
    simp only [Bool.and_eq_true] at h
    rw [addOf_sound hm hat, memAt_of_load (load_sound h.1 hat), memAt_of_load (load_sound h.2 hat)]
  · exact absurd h (by simp)

/-- `out` is `Π_{j < n} (col[j] + pt1[off + j])`, through `MUL`s from the last. -/
def eqcChainOk (A : List Atom) (pC pR : V) (off : ℕ) : ℕ → V → Bool
  | 0, _ => false
  | 1, t => eqcTermOk A t pC pR off 0
  | n + 2, out => match mulOf A out with
    | some (prev, t) => eqcTermOk A t pC pR off (n + 1) && eqcChainOk A pC pR off (n + 1) prev
    | none => false

/-- **The chain is the equality polynomial** of the points at `pC` and `1 + pt1[off ..]`. -/
theorem eqcChain_sound {pC pR : V} {off : ℕ} : ∀ {n : ℕ} {out : V},
    eqcChainOk atoms pC pR off n out = true → (∀ a ∈ atoms, a.Holds rd σ) →
    σ out = eqEval (memRun rd (σ pC) n)
      ((List.range n).map fun j => 1 + memAt rd (σ pR) (off + j))
  | 0, _, h, _ => absurd h (by simp [eqcChainOk])
  | 1, t, h, hat => by
    rw [eqcTerm_sound h hat]
    simp only [memRun, List.range_one, List.map_cons, List.map_nil, eqEval, List.zipWith_cons_cons,
      List.zipWith_nil_left, List.foldl_cons, List.foldl_nil, one_mul, one_add_add_one_add,
      Nat.add_zero]
  | n + 2, out, h, hat => by
    unfold eqcChainOk at h
    split at h
    · rename_i prev t hm
      simp only [Bool.and_eq_true] at h
      rw [mulOf_sound hm hat, eqcChain_sound h.2 hat, eqcTerm_sound h.1 hat,
        memRun_succ rd _ (n + 1), List.range_succ (n := n + 1), List.map_append, List.map_singleton,
        eqEval_snoc _ _ _ _ (by simp), one_add_add_one_add]
    · exact absurd h (by simp)

/-! ## The algebra -/

theorem fvAcc_eq_sum (e f : E) : ∀ n, fvAcc rd e f n = ∑ j ∈ range n, memAt rd e j * memAt rd f (19 + j)
  | 0 => by simp [fvAcc]
  | n + 1 => by rw [fvAcc, fvAcc_eq_sum e f n, sum_range_succ]

/-- **The loop's fold is `foldColumns`**: the `36` values of a fresh claim against the equality
table of `6` column challenges. -/
theorem fvAcc_eq_foldColumns {e f : E} {cols values : List E} (hc : cols.length = splitLog)
    (hv : values.length = nSplit)
    (he : ∀ j < nSplit, memAt rd e j = (eqKernel cols).getD j 0)
    (hf : ∀ j < nSplit, memAt rd f (19 + j) = values.getD j 0) :
    fvAcc rd e f nSplit = Batch.foldColumns cols values := by
  rw [fvAcc_eq_sum, Batch.foldColumns, Batch.sumE_zipWith_mul, Hotwire.eqKernel_length, hc, hv]
  rw [show min (2 ^ splitLog) nSplit = nSplit by decide]
  exact sum_congr rfl fun j hj => by rw [he j (mem_range.mp hj), hf j (mem_range.mp hj)]

/-- **A fresh claim's equality factor splits**: the point over the instructions, then the columns'. -/
theorem eqEval_fresh {fp cols r : List E} (hf : fp.length = 19) (hr : 19 ≤ r.length) :
    eqEval (fp ++ cols) r = eqEval fp (r.take 19) * eqEval cols (r.drop 19) := by
  conv_lhs => rw [← List.take_append_drop 19 r]
  exact Tables.eqEval_append _ _ _ _ (by simp [hf, hr])

end
end LeanVM.Guest.B1.Main
