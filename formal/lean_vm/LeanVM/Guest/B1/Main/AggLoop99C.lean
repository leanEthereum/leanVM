/-
  LeanVM.Guest.B1.Main.AggLoop99C

  `__loop99` (G:3434-3480), one child's matrix weights, backward: the honest words in memory give
  the iteration.
-/

module

public import LeanVM.Guest.B1.Main.AggStepsC
public import LeanVM.Guest.B1.Main.AggLoop99

/-!
# The matrix weights, backward

`l99Val` is the iteration's honest valuation, block by block (`setb`): the prefix and suffix
products of the Lagrange numerators, the numerators, the row sum and its eq factors, the column
sum and its eq factors, the carried claim's product, and the two weight rows. `loop99_back`
checks the body against it, each block by its forward lemma (`holds_l99Pre`, …).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

theorem setb_at {σ : Val} {b n w : ℕ} {g : ℕ → ℕ → E} {b' k : ℕ} (h1 : b ≤ b') (h2 : b' < b + w)
    (hk : k < n) : setb σ b n w g (.n (b' + w * k)) = g k (b' - b) := by
  have := setb_in (σ := σ) (b := b) (n := n) (w := w) (g := g) (o := b' - b) (by omega) hk
  rwa [show b + w * k + (b' - b) = b' + w * k by omega] at this

/-- Lookups in a valuation built by `setl`, `setv` and `setb`, the blocks by `setb_at`. -/
macro "b1_lookc" : tactic =>
  `(tactic| simp (disch := omega) only [setl, set_n_lt, set_n_ge, set_n_in, setb_lt, setb_ge, setb_at,
    setb_in, Nat.add_sub_cancel_left, ofArgs_n, List.getD_cons_succ, List.getD_cons_zero,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.add_zero, Nat.sub_self,
    Nat.zero_add])

theorem preV_succ (k : ℕ) : preV (k + 1 + 1) = 16 + 3 * k := by
  unfold preV; rw [ite_neg' (by omega)]; omega

theorem preAt_succ (k : ℕ) : preAt (k + 1 + 1) = 16 + 3 * k := by
  unfold preAt; rw [ite_neg' (by omega)]; omega

theorem sufAt_lt {i : ℕ} (hi : i < 63) : sufAt (i + 1) = 206 + 3 * (62 - i) := by
  unfold sufAt; rw [ite_neg' (by omega)]; omega

theorem prod_Ico_pred (f : ℕ → E) {k : ℕ} (hk : k + 1 ≤ 63) :
    ∏ l ∈ Finset.Ico (63 - (k + 1)) 64, f l = (∏ l ∈ Finset.Ico (63 - k) 64, f l) * f (63 - (k + 1)) := by
  rw [Finset.prod_eq_prod_Ico_succ_bot (by omega), show 63 - (k + 1) + 1 = 63 - k by omega, mul_comm]

/-- Literal lookups in a `setb` block. -/
macro "b1_lit" : tactic =>
  `(tactic| simp (disch := omega) only [setb_lit, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod])

/-- `LAGRANGE_INV_S` as the data's word. -/
abbrev lagInvE : E := word 11666641484232641359 0 0

/-- The row sum against the row `eqtree`'s words `er`. -/
def rowSum (z : E) (er : List E) : E := ∑ i ∈ Finset.range 64, lagNum z i * er.getD i 0

/-- The column sum of the slices `fs[41 ..]` against the column `eqtree`'s words `ec`. -/
def colSum (fs ec : List E) : E := ∑ i ∈ Finset.range 64, fs.getD (41 + i) 0 * ec.getD i 0

/-- The first `n` row eq factors. -/
def rowProd (fs mp : List E) (n : ℕ) : E :=
  ∏ j ∈ Finset.range n, (1 + fs.getD (25 + j) 0 + mp.getD (6 + j) 0)

/-- The first `n` column eq factors. -/
def colProd (fs mp : List E) (n : ℕ) : E :=
  ∏ j ∈ Finset.range n, (1 + fs.getD (33 + j) 0 + mp.getD (27 - j) 0)

/-- The first `n` factors of the carried claim's eq product. -/
def carProd (cc mp : List E) (n : ℕ) : E :=
  ∏ j ∈ Finset.range n, (1 + cc.getD (23 + j) 0 + mp.getD j 0)

/-- The fresh claim's weight `U`, as `__loop99` assembles it. -/
def l99U (fs er ec mp : List E) : E :=
  rowSum (fs.getD 24 0) er * lagInvE * rowProd fs mp 8 * (colSum fs ec * colProd fs mp 8)

/-- Prefix block `k`: node `k + 1`, `z` plus it, the product up to it. -/
def preG (z : E) (k : ℕ) : ℕ → E
  | 0 => phiE (k + 1)
  | 1 => z + phiE (k + 1)
  | _ => ∏ j ∈ Finset.range (k + 2), (z + phiE j)

/-- Suffix block `k`: node `63 - k`, `z` plus it, the product from it. -/
def sufG (z : E) (k : ℕ) : ℕ → E
  | 0 => phiE (63 - k)
  | 1 => z + phiE (63 - k)
  | _ => ∏ l ∈ Finset.Ico (63 - k) 64, (z + phiE l)

/-- Row block `k`: the word `k + 1`, its term, the running sum. -/
def rowG (z : E) (er : List E) (k : ℕ) : ℕ → E
  | 0 => er.getD (k + 1) 0
  | 1 => lagNum z (k + 1) * er.getD (k + 1) 0
  | _ => ∑ i ∈ Finset.range (k + 2), lagNum z i * er.getD i 0

/-- Row eq block `k`. -/
def rowEqG (fs mp : List E) (s : E) (k : ℕ) : ℕ → E
  | 0 => 1
  | 1 => fs.getD (25 + k) 0
  | 2 => 1 + fs.getD (25 + k) 0
  | 3 => mp.getD (6 + k) 0
  | 4 => 1 + fs.getD (25 + k) 0 + mp.getD (6 + k) 0
  | _ => s * rowProd fs mp (k + 1)

/-- Column block `k`: slice `k + 1`, the word, the term, the running sum. -/
def colG (fs ec : List E) (k : ℕ) : ℕ → E
  | 0 => fs.getD (42 + k) 0
  | 1 => ec.getD (k + 1) 0
  | 2 => fs.getD (42 + k) 0 * ec.getD (k + 1) 0
  | _ => ∑ i ∈ Finset.range (k + 2), fs.getD (41 + i) 0 * ec.getD i 0

/-- Column eq block `j`. -/
def colEqG (fs mp : List E) (s : E) (j : ℕ) : ℕ → E
  | 0 => 1
  | 1 => fs.getD (33 + j) 0
  | 2 => 1 + fs.getD (33 + j) 0
  | 3 => mp.getD (27 - j) 0
  | 4 => 1 + fs.getD (33 + j) 0 + mp.getD (27 - j) 0
  | _ => s * colProd fs mp (j + 1)

/-- Carried block `k`, factor `k + 1`. -/
def carG (cc mp : List E) (k : ℕ) : ℕ → E
  | 0 => 1
  | 1 => cc.getD (24 + k) 0
  | 2 => 1 + cc.getD (24 + k) 0
  | 3 => mp.getD (k + 1) 0
  | 4 => 1 + cc.getD (24 + k) 0 + mp.getD (k + 1) 0
  | _ => carProd cc mp (k + 2)

/-- **`__loop99`'s honest valuation at `x = g^c`**, from the rows' pointers `fp`, `cp`, the fresh
cells `fs`, the carried cells `cc`, the matrix point `mp`, the `eqtree`s `er`, `ec`, the lambdas
and the weight rows. -/
def l99Val (c : ℕ) (N frow eqR mpp eqC crow lamm wsums fp cp w0 w1 l1 l2 l3 : E)
    (fs cc mp er ec : List E) : Val :=
  setl (setb (setl (setb (setb (setl (setb (setl (setb (setl (setv (setl (setb (setl (setb (setl
    (Val.ofArgs [gen ^ c, N, frow, eqR, mpp, eqC, crow, lamm, wsums]) 9
      [frow * gen ^ c, fp, fs.getD 24 0, 1, 1 * fs.getD 24 0])
    14 63 3 (preG (fs.getD 24 0))) 203 [1])
    204 63 3 (sufG (fs.getD 24 0)))
    393 [(∏ l ∈ Finset.Ico 1 64, (fs.getD 24 0 + phiE l)) * fs.getD 24 0])
    394 64 (lagNum (fs.getD 24 0)))
    458 [er.getD 0 0, lagNum (fs.getD 24 0) 0 * er.getD 0 0])
    460 63 3 (rowG (fs.getD 24 0) er))
    649 [lagInvE, rowSum (fs.getD 24 0) er * lagInvE])
    651 8 6 (rowEqG fs mp (rowSum (fs.getD 24 0) er * lagInvE)))
    699 [fs.getD 41 0, ec.getD 0 0, fs.getD 41 0 * ec.getD 0 0])
    702 63 4 (colG fs ec))
    954 8 6 (colEqG fs mp (colSum fs ec)))
    1002 [l99U fs er ec mp, crow * gen ^ c, cp, 1, cc.getD 23 0, 1 + cc.getD 23 0, mp.getD 0 0,
      1 + cc.getD 23 0 + mp.getD 0 0])
    1010 27 6 (carG cc mp))
    1172 [gen ^ (2 * c), gen ^ (3 * c), lamm * gen ^ (3 * c), l1, gen ^ (2 * c), wsums * gen ^ (2 * c),
      w0, l1 * l99U fs er ec mp, w0 + l1 * l99U fs er ec mp, lamm * gen ^ (3 * c), l2,
      l2 * carProd cc mp 28, w0 + l1 * l99U fs er ec mp + l2 * carProd cc mp 28, w1, fs.getD 23 0,
      l1 * fs.getD 23 0, l1 * fs.getD 23 0 * l99U fs er ec mp,
      w1 + l1 * fs.getD 23 0 * l99U fs er ec mp, lamm * gen ^ (3 * c), l3, l3 * carProd cc mp 28,
      w1 + l1 * fs.getD 23 0 * l99U fs er ec mp + l3 * carProd cc mp 28, gen, gen ^ c * gen,
      gen ^ c * gen + N, gen, gen ^ c * gen]

section Blocks

variable {C : CallRel} {kret : List E → Prop} {c : ℕ}
  {N frow eqR mpp eqC crow lamm wsums fp cp w0 w1 l1 l2 l3 : E} {fs cc mp er ec : List E}

local notation "σ99" => l99Val c N frow eqR mpp eqC crow lamm wsums fp cp w0 w1 l1 l2 l3 fs cc mp er ec

theorem l99_pre (k : ℕ) (hk : k < 63) :
    Stmt.HoldsList C rd σ99 (l99Pre (k + 1)) True kret := by
  rw [holds_l99Pre]
  rcases k with _ | k
  · simp only [preV, ↓reduceIte, l99Val]
    b1_lookc
    refine ⟨rfl, rfl, ?_⟩
    simp [preG, Finset.prod_range_succ, phiE_zero]
  · simp only [preV_succ, l99Val]
    b1_lookc
    exact ⟨rfl, rfl, Finset.prod_range_succ _ _⟩

theorem l99_suf (k : ℕ) (hk : k < 63) :
    Stmt.HoldsList C rd σ99 (l99Suf k) True kret := by
  rw [holds_l99Suf]
  rcases k with _ | k
  · simp only [↓reduceIte, l99Val]
    b1_lookc
    refine ⟨rfl, rfl, ?_⟩
    simp [sufG]
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, show 203 + 3 * (k + 1) = 206 + 3 * k by ring,
      l99Val]
    b1_lookc
    exact ⟨rfl, rfl, prod_Ico_pred _ (by omega)⟩

theorem l99_num (i : ℕ) (hi : i < 64) :
    σ99 (.n (394 + i)) = σ99 (.n (preAt i)) * σ99 (.n (sufAt (i + 1))) ∧ True := by
  have hp : σ99 (.n (preAt i)) = ∏ j ∈ Finset.range i, (fs.getD 24 0 + phiE j) := by
    rcases i with _ | _ | i
    · simp only [show preAt 0 = 12 from rfl, l99Val]; b1_lookc; simp
    · simp only [show preAt 1 = 13 from rfl, l99Val]; b1_lookc; simp [phiE_zero]
    · simp only [preAt_succ, l99Val]; b1_lookc; rfl
  have hs : σ99 (.n (sufAt (i + 1))) = ∏ l ∈ Finset.Ico (i + 1) 64, (fs.getD 24 0 + phiE l) := by
    rcases Nat.lt_or_ge i 63 with h | h
    · simp only [sufAt_lt h, l99Val]; b1_lookc
      simp only [sufG, show 63 - (62 - i) = i + 1 by omega]
    · simp only [show i = 63 by omega, show sufAt (63 + 1) = 203 from rfl, l99Val]; b1_lookc
      simp
  refine ⟨?_, trivial⟩
  rw [hp, hs]
  simp only [l99Val]; b1_lookc; rfl

theorem l99_row (hR : ∀ i < 64, LoadHolds rd eqR (62 + i) (er.getD i 0)) (k : ℕ) (hk : k < 63) :
    Stmt.HoldsList C rd σ99 (l99Row (k + 1)) True kret := by
  rw [holds_l99Row]
  rcases k with _ | k
  · simp only [↓reduceIte, l99Val]
    b1_lookc
    refine ⟨hR 1 (by omega), rfl, ?_⟩
    simp [rowG, Finset.sum_range_succ]
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, show 459 + 3 * (k + 1) = 462 + 3 * k by ring,
      l99Val]
    b1_lookc
    exact ⟨hR _ (by omega), rfl, Finset.sum_range_succ _ _⟩

theorem l99_rowEq (hfl : fs.length = 106) (hml : mp.length = 28) (hF : ReadsAt rd fp fs)
    (hM : ReadsAt rd mpp mp) (k : ℕ) (hk : k < 8) :
    Stmt.HoldsList C rd σ99 (l99RowEq k) True kret := by
  rw [holds_l99RowEq]
  rcases k with _ | k
  · simp only [l99Val]
    b1_lookc
    refine ⟨rfl, readsAt_getD' hF (by omega), rfl, readsAt_getD' hM (by omega), rfl, ?_⟩
    simp [rowEqG, rowProd]
  · simp only [show 650 + 6 * (k + 1) = 656 + 6 * k by ring, l99Val]
    b1_lookc
    refine ⟨rfl, readsAt_getD' hF (by omega), rfl, readsAt_getD' hM (by omega), rfl, ?_⟩
    simp only [rowEqG, rowProd, Finset.prod_range_succ (n := k + 1), mul_assoc]

theorem l99_col (hfl : fs.length = 106) (hF : ReadsAt rd fp fs)
    (hE : ∀ i < 64, LoadHolds rd eqC (62 + i) (ec.getD i 0)) (k : ℕ) (hk : k < 63) :
    Stmt.HoldsList C rd σ99 (l99Col (k + 1)) True kret := by
  rw [holds_l99Col]
  rcases k with _ | k
  · simp only [l99Val]
    b1_lookc
    refine ⟨readsAt_getD' hF (by omega), hE 1 (by omega), rfl, ?_⟩
    simp [colG, Finset.sum_range_succ]
  · simp only [show 701 + 4 * (k + 1) = 705 + 4 * k by ring, l99Val]
    b1_lookc
    refine ⟨by rw [show 41 + (k + 1 + 1) = 42 + (k + 1) by omega]; exact readsAt_getD' hF (by omega),
      hE _ (by omega), rfl, ?_⟩
    simp only [colG, Finset.sum_range_succ (n := k + 2)]
    rw [show 42 + (k + 1) = 41 + (k + 2) by omega, show k + 1 + 1 = k + 2 by omega]

theorem l99_colEq (hfl : fs.length = 106) (hml : mp.length = 28) (hF : ReadsAt rd fp fs)
    (hM : ReadsAt rd mpp mp) (k : ℕ) (hk : k < 8) :
    Stmt.HoldsList C rd σ99 (l99ColEq k) True kret := by
  rw [holds_l99ColEq]
  rcases k with _ | k
  · simp only [Nat.mul_zero, Nat.add_zero, l99Val]
    b1_lookc
    b1_lit
    refine ⟨rfl, readsAt_getD' hF (by omega), rfl, readsAt_getD' hM (by omega), rfl, ?_⟩
    simp only [colEqG, colG, colProd, colSum, Nat.reduceAdd, Finset.prod_range_one]
  · simp only [show 953 + 6 * (k + 1) = 959 + 6 * k by ring, l99Val]
    b1_lookc
    refine ⟨rfl, readsAt_getD' hF (by omega), rfl, readsAt_getD' hM (by omega), rfl, ?_⟩
    simp only [colEqG, colProd, Finset.prod_range_succ (n := k + 1), mul_assoc]

theorem l99_car (hcl : cc.length = 53) (hml : mp.length = 28) (hC : ReadsAt rd cp cc)
    (hM : ReadsAt rd mpp mp) (k : ℕ) (hk : k < 27) :
    Stmt.HoldsList C rd σ99 (l99Car (k + 1)) True kret := by
  rw [holds_l99Car]
  rcases k with _ | k
  · simp only [l99Val]
    b1_lookc
    refine ⟨rfl, readsAt_getD' hC (by omega), rfl, readsAt_getD' hM (by omega), rfl, ?_⟩
    simp [carG, carProd, Finset.prod_range_succ]
  · simp only [show 1009 + 6 * (k + 1) = 1015 + 6 * k by ring, l99Val]
    b1_lookc
    refine ⟨rfl, by rw [show 23 + (k + 1 + 1) = 24 + (k + 1) by omega]; exact readsAt_getD' hC (by omega),
      rfl, readsAt_getD' hM (by omega), rfl, ?_⟩
    simp only [carG, carProd, Finset.prod_range_succ (n := k + 2)]
    rw [show 24 + (k + 1) = 23 + (k + 2) by omega, show k + 1 + 1 = k + 2 by omega]

end Blocks

/-- **`__loop99` at `x = g^c`, backward**: the row's words give the iteration. -/
theorem loop99_back {N frow eqR mpp eqC crow lamm wsums : E} (d c : ℕ) (fp cp w0 w1 l1 l2 l3 : E)
    (fs cc mp er ec : List E) (hfl : fs.length = 106) (hcl : cc.length = 53) (hml : mp.length = 28)
    (hf : LoadHolds rd frow c fp) (hc : LoadHolds rd crow c cp) (hF : ReadsAt rd fp fs)
    (hC : ReadsAt rd cp cc) (hM : ReadsAt rd mpp mp)
    (hR : ∀ i < 64, LoadHolds rd eqR (62 + i) (er.getD i 0))
    (hE : ∀ i < 64, LoadHolds rd eqC (62 + i) (ec.getD i 0))
    (hl1 : LoadHolds rd lamm (3 * c) l1) (hl2 : LoadHolds rd lamm (3 * c + 1) l2)
    (hl3 : LoadHolds rd lamm (3 * c + 2) l3) (hw0 : LoadHolds rd wsums (2 * c) w0)
    (hw1 : LoadHolds rd wsums (2 * c + 1) w1)
    (hn0 : LoadHolds rd wsums (2 * c + 2) (w0 + l1 * l99U fs er ec mp + l2 * carProd cc mp 28))
    (hn1 : LoadHolds rd wsums (2 * c + 3)
      (w1 + l1 * fs.getD 23 0 * l99U fs er ec mp + l3 * carProd cc mp 28))
    (hK : IsInK (gen ^ c * gen + N))
    (hnext : gen ^ c * gen + N ≠ 0 →
      coreProgram.relN rd d "__loop99" [gen ^ c * gen, N, frow, eqR, mpp, eqC, crow, lamm, wsums] []) :
    coreProgram.relN rd (d + 1) "__loop99" [gen ^ c, N, frow, eqR, mpp, eqC, crow, lamm, wsums] [] := by
  rw [relN_succ_iff find_loop99]
  refine ⟨l99Val c N frow eqR mpp eqC crow lamm wsums fp cp w0 w1 l1 l2 l3 fs cc mp er ec,
    by simp only [show Fn.params Data.core572 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8]
      from rfl, List.map_cons, List.map_nil, l99Val]; b1_lookb, ?_⟩
  rw [core572_body, l99Body]
  simp only [holdsList_append,
    holdsList_range_flatten 63 (fun i => l99Pre (i + 1)) (fun _ => rfl),
    holdsList_range_flatten 63 l99Suf (fun _ => rfl),
    holdsList_range_flatten 64
      (fun i => [Stmt.atom (.mul (.n (394 + i)) (.n (preAt i)) (.n (sufAt (i + 1))))]) (fun _ => rfl),
    holdsList_range_flatten 63 (fun i => l99Row (i + 1)) (fun _ => rfl),
    holdsList_range_flatten 8 l99RowEq (fun _ => rfl),
    holdsList_range_flatten 63 (fun i => l99Col (i + 1)) (fun _ => rfl),
    holdsList_range_flatten 8 l99ColEq (fun _ => rfl),
    holdsList_range_flatten 27 (fun k => l99Car (k + 1)) (fun _ => rfl)]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_gen,
    word_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, l99_pre, ?_, l99_suf, ?_, l99_num, ?_, ?_, l99_row hR, ?_, ?_,
    l99_rowEq hfl hml hF hM, ?_, ?_, ?_, l99_col hfl hF hE, l99_colEq hfl hml hF hM, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, l99_car hcl hml hC hM, ?_⟩
  all_goals simp only [l99Val]
  all_goals b1_lookc
  all_goals try b1_lit
  · exact loadHolds_of_mul0 rfl hf
  · exact readsAt_getD' hF (by omega)
  · rfl
  · simpa using hR 0 (by omega)
  · rfl
  · exact readsAt_getD' hF (by omega)
  · simpa using hE 0 (by omega)
  · rfl
  · exact loadHolds_of_mul0 rfl hc
  · exact readsAt_getD' hC (by omega)
  · exact readsAt_getD' hM (by omega)
  · simp only [loadHolds_mul_gen_pow, Nat.add_zero, true_and, and_true]
    exact ⟨by ring, by ring, hl1, by ring, hw0, hl2, rfl, hn0, hw1, readsAt_getD' hF (by omega), hl3,
      rfl, hn1, hK, hnext⟩

end
end LeanVM.Guest.B1.Main
