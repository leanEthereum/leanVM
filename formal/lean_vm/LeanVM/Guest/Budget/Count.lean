module

public import Statement.LeanVmGuestCompleteness

/-!
# The guest's words, rows and weighted rows by a node's items

The static count of the compiled guest (`notes/hotwire-port.md`, `M2-guest complete`, the budget's
verdict) as functions of a node's items: its children, each at its shape (`ChildShape`: its stacked
opening's stack log and rate, and whether a level of the opening takes the zero-challenge sum) with
its two claim lists, its raw signatures, its declared claims and its blob matrix. Three measures: the
words the run reserves (`nodeWords`), its steps (`nodeRows`, every table's rows), and its rows
weighed by each table's committed columns (`nodeWeighted`, `Σ_t cols_t · rows_t` with
`cols = [7, 9, 5, 10, 14, 68]`, `q_keccak`'s `64` among the `KECCAK` table's `68`).

Each is a bound the count gives, not the run's exact cost: every branch's two arms counted, a dispatch
at its costliest arm, a child's stream at `32` chunks, its pointer width, tallest table and Keccak
table at `24` and its link at `19` permutations. A child's part by stack log and rate is a table
(`vsWordsNone`, …), the zero-challenge sum's part the difference of its `All` and `None` tables.

Against a budget of coefficients `C` (`Coefs`, `Coefs.budget`, the deployed ones `Coefs.deployed`,
`NodeWitness.memoryBudget`): `nodeWords_le` (the claim's excess on short lists charged to the child),
`nodeRows_lt` and `nodeWeighted_le` under the coefficients' lower bounds (`Coefs.Covers`), with
the child's part a hypothesis; `childWords_le_corrected` (any child) discharges it.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Node

@[expose] public section

/-! ## The items -/

/-- A child's shape as the count reads it: its stacked opening's stack log `m ∈ [16, 30]` and rate
`r ∈ [1, 4]`, and whether some level of the opening takes `level_residual_sum` (a zero product of
the level's later fold and tail challenges, `level_residual_slow`). -/
structure ChildShape where
  stackLog : ℕ
  rate : ℕ
  zeroSum : Bool

/-- The shapes the deferring verifier admits: `m - 16 < LIG_N_LOG_SIZES = 15`, `r - 1 < 4`. -/
def ChildShape.Admissible (s : ChildShape) : Prop :=
  16 ≤ s.stackLog ∧ s.stackLog ≤ 30 ∧ 1 ≤ s.rate ∧ s.rate ≤ 4

/-- A child item: its shape and its two lists' lengths (leanXMSS, leanSPHINCS). -/
structure ChildItem where
  shape : ChildShape
  xmssClaims : ℕ
  sphincsClaims : ℕ

/-- A node's items: its children, raw signatures, declared claims of each scheme and the rows of the
blob matrix it checks directly. -/
structure NodeItems where
  children : List ChildItem
  xmss : ℕ
  sphincs : ℕ
  declaredXmss : ℕ
  declaredSphincs : ℕ
  rows : Option ℕ

/-- The claims of the children's lists. -/
def NodeItems.childClaims (it : NodeItems) : ℕ :=
  (it.children.map fun c ↦ c.xmssClaims + c.sphincsClaims).sum

/-- The coverage slots: one a holder, each raw signature and each child list entry (`main`'s count
`written[n_children] == n_total`). -/
def NodeItems.holders (it : NodeItems) : ℕ := it.xmss + it.sphincs + it.childClaims

/-- The declared claims take a slot each. -/
def NodeItems.DeclaredFit (it : NodeItems) : Prop :=
  it.declaredXmss + it.declaredSphincs ≤ it.holders

/-! ## The budget's coefficients -/

/-- A budget's coefficients: a child list's claim, a child, a raw leanXMSS and leanSPHINCS
signature, a blob matrix, its row, and the rest. -/
structure Coefs where
  claim : ℕ
  child : ℕ
  xmss : ℕ
  sphincs : ℕ
  matrix : ℕ
  row : ℕ
  fixed : ℕ

/-- A node's budget under `C`. -/
def Coefs.budget (C : Coefs) (it : NodeItems) : ℕ :=
  C.claim * it.childClaims + C.child * it.children.length + C.xmss * it.xmss +
    C.sphincs * it.sphincs + (it.rows.map fun r ↦ C.matrix + C.row * r).getD 0 + C.fixed

/-- `NodeWitness.memoryBudget`'s coefficients. -/
def Coefs.deployed : Coefs := ⟨66, 457265, 1400, 7500, 131072, 122000, 41297⟩

/-- The coefficients the count needs, but the child's (a hypothesis of each theorem). -/
structure Coefs.Covers (C : Coefs) : Prop where
  claim : 46 ≤ C.claim
  xmss : 1333 ≤ C.xmss
  sphincs : 7336 ≤ C.sphincs
  matrix : 95546 ≤ C.matrix
  row : 118441 ≤ C.row
  fixed : 23791 ≤ C.fixed

/-- Coefficients at least `C`'s, each. -/
structure Coefs.Above (C D : Coefs) : Prop where
  claim : C.claim ≤ D.claim
  child : C.child ≤ D.child
  xmss : C.xmss ≤ D.xmss
  sphincs : C.sphincs ≤ D.sphincs
  matrix : C.matrix ≤ D.matrix
  row : C.row ≤ D.row
  fixed : C.fixed ≤ D.fixed

/-- A node's items read off a witness, its children's shapes by `shape` and its declared claims by
`statement`. -/
def NodeItems.ofWitness (shape : Child → ChildShape) (statement : NodeStatement)
    (witness : NodeWitness) : NodeItems where
  children := witness.children.map fun c ↦
    ⟨shape c, c.statement.claims.xmss.length, c.statement.claims.sphincs.length⟩
  xmss := witness.xmssSignatures.length
  sphincs := witness.sphincsSignatures.length
  declaredXmss := statement.claims.xmss.length
  declaredSphincs := statement.claims.sphincs.length
  rows := witness.daMatrix.map fun p ↦ p.2.rows.length

/-- **The deployed coefficients' budget is `NodeWitness.memoryBudget`.** -/
theorem deployed_budget_ofWitness (shape : Child → ChildShape) (statement : NodeStatement)
    (witness : NodeWitness) :
    Coefs.deployed.budget (NodeItems.ofWitness shape statement witness) = witness.memoryBudget := by
  simp only [Coefs.budget, Coefs.deployed, NodeItems.ofWitness, NodeItems.childClaims,
    NodeWitness.memoryBudget, NodeWitness.childClaimCount, List.map_map, List.length_map,
    Function.comp_def]
  cases witness.daMatrix <;> simp

/-! ## `verify_sub`'s count by stack log and rate

Row `4 (m - 16) + (r - 1)`, `verify_sub`'s own allocations (its frame charged to the caller); `None`
without the zero-challenge sum, `All` with it on every level. -/

def vsWordsNone : List ℕ := [236249, 174052, 153456, 144074, 236214, 175975, 157357, 144776,
  238061, 181019, 158079, 144843, 242304, 184144, 159137, 146749, 255613, 189177, 164749, 152737,
  256843, 190115, 166854, 156164, 258734, 192478, 169933, 159142, 262171, 196156, 173988, 161711,
  270489, 204950, 180290, 167319, 276631, 208356, 183476, 169037, 284543, 212111, 185218, 170579,
  290328, 214392, 186962, 173965, 296119, 220814, 193296, 181324, 299881, 223603, 198398, 184686,
  302710, 230534, 201959, 187107]

def vsWordsAll : List ℕ := [272189, 193220, 166872, 154562, 274140, 196489, 171801, 155910,
  278249, 202839, 173379, 156847, 284836, 207514, 175537, 159623, 303667, 216491, 184579, 168627,
  307683, 219147, 188034, 173154, 312624, 223320, 192463, 177232, 319111, 228808, 197868, 180901,
  332625, 241374, 207298, 189295, 342047, 246800, 212024, 192293, 353239, 252575, 215306, 195115,
  362304, 256876, 218590, 199781, 373061, 266912, 227966, 209830, 380283, 271891, 234768, 214724,
  386572, 281012, 240029, 218585]

def vsRowsNone : List ℕ := [192173, 141400, 124551, 116181, 192676, 143185, 127009, 116560,
  194675, 146458, 127550, 116628, 198631, 148786, 128352, 118567, 205263, 151621, 132238, 122789,
  205948, 152773, 134200, 125819, 208077, 154900, 136851, 128035, 211438, 158327, 140059, 129945,
  217749, 164272, 144130, 133488, 223226, 166710, 146397, 134675, 227789, 169262, 147493, 135735,
  231957, 170958, 148876, 138677, 235684, 175444, 153269, 143498, 238793, 177628, 156903, 145952,
  240998, 182365, 159493, 147783]

def vsRowsAll : List ℕ := [228969, 161031, 138292, 126922, 231437, 164156, 141775, 127941,
  235686, 168729, 143166, 128879, 241977, 172607, 145068, 131688, 254217, 179460, 152452, 138988,
  257682, 182327, 155764, 143118, 262861, 186264, 159765, 146434, 269272, 191501, 164323, 149444,
  280841, 201274, 171572, 155820, 289598, 205732, 175379, 158287, 297441, 210304, 178015, 160627,
  304889, 214020, 180938, 164849, 313629, 222164, 188414, 172398, 320198, 226538, 193748, 176387,
  325863, 233465, 198038, 179658]

def vsWeightedNone : List ℕ := [1895402, 1381939, 1216718, 1148383, 1897804, 1403416, 1262440,
  1155972, 1920588, 1469457, 1273399, 1156111, 1970252, 1500635, 1280722, 1174401, 2119987,
  1546546, 1335268, 1233654, 2132770, 1556203, 1355712, 1269199, 2151279, 1578358, 1388161,
  1306804, 2183904, 1616752, 1441038, 1333411, 2265894, 1724267, 1505718, 1387867, 2331834,
  1760491, 1532784, 1401841, 2450861, 1791372, 1546756, 1411506, 2496801, 1811291, 1559512,
  1447038, 2553992, 1874533, 1626383, 1527273, 2586322, 1899170, 1684352, 1561830, 2610386,
  1980790, 1721489, 1586089]

def vsWeightedAll : List ℕ := [2197772, 1543558, 1329971, 1236964, 2214846, 1575222, 1383520,
  1249350, 2254693, 1651142, 1400893, 1256188, 2322140, 1694255, 1416686, 1281177, 2517110,
  1772896, 1499827, 1365660, 2551168, 1795693, 1530666, 1409675, 2593162, 1831785, 1573510,
  1455750, 2649272, 1884116, 1636782, 1490827, 2773278, 2022505, 1727200, 1568299, 2864474,
  2074283, 1766124, 1592129, 3008757, 2120718, 1791954, 1611650, 3079953, 2156191, 1816568,
  1657038, 3176946, 2248736, 1908249, 1759284, 3235918, 2290236, 1979308, 1805726, 3286624,
  2388719, 2029535, 1841073]

/-- A shape's row of the tables. -/
def ChildShape.index (s : ChildShape) : ℕ := 4 * (s.stackLog - 16) + (s.rate - 1)

/-- A table at a shape: its `All` row with the zero-challenge sum, else its `None` row. -/
def ChildShape.read (s : ChildShape) (none all : List ℕ) : ℕ :=
  (if s.zeroSum then all else none).getD s.index 0

/-! ## A child's part

`verify_sub`'s count, its frame (`3198`, aligned: `+15`), and `main`'s part a child (its loop frame,
the two claim lists' digests with both walks' fixed parts and their costliest last block, the
statement digest, `main`'s and `aggregate_claims`' cells and loop frames a child): `6625` words,
`1741` rows, `17989` weighted rows. -/

def childWords (s : ChildShape) : ℕ := s.read vsWordsNone vsWordsAll + 6625
def childRows (s : ChildShape) : ℕ := s.read vsRowsNone vsRowsAll + 1741
def childWeighted (s : ChildShape) : ℕ := s.read vsWeightedNone vsWeightedAll + 17989

/-- The admissible shapes' rows. -/
theorem ChildShape.Admissible.index_lt {s : ChildShape} (h : s.Admissible) : s.index < 60 := by
  unfold ChildShape.index; obtain ⟨_, _, _, _⟩ := h; omega

theorem forall_index {s : ChildShape} (h : s.Admissible) {P : ℕ → Prop}
    (hP : ∀ i < 60, P i) : P s.index := hP _ h.index_lt

/-- **The zero-challenge sum's words**: `childWords` without it plus this term, zero unless some
level of the opening takes the sum. -/
def zeroSumWords (s : ChildShape) : ℕ :=
  if s.zeroSum then vsWordsAll.getD s.index 0 - vsWordsNone.getD s.index 0 else 0

theorem childWords_eq {s : ChildShape} (h : s.Admissible) :
    childWords s = vsWordsNone.getD s.index 0 + zeroSumWords s + 6625 := by
  have hle := forall_index h (P := fun i ↦ vsWordsNone.getD i 0 ≤ vsWordsAll.getD i 0) (by decide)
  unfold childWords ChildShape.read zeroSumWords
  split_ifs <;> omega

/-! ## The claim lists

A list of `L = 136 b + 17 g + r` claims (`list_split`, `g < 8`, `r < 17`): its walk's big and group
loops (`child_claim_list_any`, the costlier walk: `3232 + 13` words a big block, `448 + 13` a group),
the node's digest of its declared claims (`claim_list_chain`: `2000 + 13`, `288 + 13`). A slot is
`4 + 1` words (its table entry and coverage cell) and a duplicate slot's loop frame `16` more. -/

def walkWords (L : ℕ) : ℕ := 3245 * (L / 136) + 461 * (L % 136 / 17)
def walkRows (L : ℕ) : ℕ := 2464 * (L / 136) + 354 * (L % 136 / 17)
def walkWeighted (L : ℕ) : ℕ := 25778 * (L / 136) + 3659 * (L % 136 / 17)
def digestWords (D : ℕ) : ℕ := 2013 * (D / 136) + 301 * (D % 136 / 17)
def digestRows (D : ℕ) : ℕ := 1240 * (D / 136) + 201 * (D % 136 / 17)
def digestWeighted (D : ℕ) : ℕ := 14351 * (D / 136) + 2228 * (D % 136 / 17)

/-- **A list's walk and slots within `46` a claim, but `252`**: the group loop's `27.12` a claim and a
duplicate slot's `21`, on at most `7` groups. -/
theorem walkWords_le (L : ℕ) : walkWords L + 21 * L ≤ 46 * L + 252 := by
  unfold walkWords; omega

theorem walkRows_le (L : ℕ) : walkRows L + 18 * L ≤ 46 * L := by
  unfold walkRows; omega

theorem walkWeighted_le (L : ℕ) : walkWeighted L + 159 * L ≤ 25 * 46 * L := by
  unfold walkWeighted; omega

/-- The declared claims' digest against a duplicate slot's frame each: within `16` a claim, but
`203`. -/
theorem digestWords_le (D : ℕ) : digestWords D ≤ 16 * D + 203 := by
  unfold digestWords; omega

theorem digestRows_le (D : ℕ) : digestRows D ≤ 18 * D := by
  unfold digestRows; omega

theorem digestWeighted_le (D : ℕ) : digestWeighted D ≤ 159 * D := by
  unfold digestWeighted; omega

/-! ## The node -/

/-- A blob matrix and its rows: `da_verify` at `n` rows (its padding loop shrinking as `n` grows). -/
def matrixWords (rows : Option ℕ) : ℕ := (rows.map fun r ↦ 95403 + 118441 * r).getD 0
def matrixRows (rows : Option ℕ) : ℕ := (rows.map fun r ↦ 95546 + 76993 * r).getD 0
def matrixWeighted (rows : Option ℕ) : ℕ := (rows.map fun r ↦ 813339 + 766924 * r).getD 0

/-- **The node's words**: `main`'s rest (`23385`, its frame `15862` among them), the declared
claims' digests, the children, the raw signatures (`1312` and `28 + 7287`), every slot's `5` and every
duplicate slot's `16`, and the blob matrix. -/
def nodeWords (it : NodeItems) : ℕ :=
  23385 + digestWords it.declaredXmss + digestWords it.declaredSphincs +
    (it.children.map fun c ↦ childWords c.shape + walkWords c.xmssClaims +
      walkWords c.sphincsClaims).sum +
    1312 * it.xmss + 7315 * it.sphincs + 5 * it.holders +
    16 * (it.holders - it.declaredXmss - it.declaredSphincs) + matrixWords it.rows

/-- **The node's rows** (its steps): `main`'s rest `6850`, each duplicate slot's loop `18`. -/
def nodeRows (it : NodeItems) : ℕ :=
  6850 + digestRows it.declaredXmss + digestRows it.declaredSphincs +
    (it.children.map fun c ↦ childRows c.shape + walkRows c.xmssClaims +
      walkRows c.sphincsClaims).sum +
    978 * it.xmss + 6547 * it.sphincs +
    18 * (it.holders - it.declaredXmss - it.declaredSphincs) + matrixRows it.rows

/-- **The node's weighted rows**: `Σ_t cols_t · rows_t`, `main`'s rest `57261`. -/
def nodeWeighted (it : NodeItems) : ℕ :=
  57261 + digestWeighted it.declaredXmss + digestWeighted it.declaredSphincs +
    (it.children.map fun c ↦ childWeighted c.shape + walkWeighted c.xmssClaims +
      walkWeighted c.sphincsClaims).sum +
    32366 * it.xmss + 102171 * it.sphincs +
    159 * (it.holders - it.declaredXmss - it.declaredSphincs) + matrixWeighted it.rows

theorem sum_children_le {l : List ChildItem} {f : ChildItem → ℕ} {k a b : ℕ}
    (h : ∀ c ∈ l, f c ≤ k * a + k * (b * (c.xmssClaims + c.sphincsClaims))) :
    (l.map f).sum ≤ k * (a * l.length) + k * (b * (l.map fun c ↦ c.xmssClaims + c.sphincsClaims).sum) := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h c (by simp)
    have h2 := ih fun c hc ↦ h c (by simp [hc])
    rw [Nat.mul_add a, Nat.mul_one, Nat.mul_add b, Nat.mul_add k, Nat.mul_add k]
    omega

theorem matrix_le {C : Coefs} (hC : C.Covers) {m r : ℕ} (hm : m ≤ 95546) (hr : r ≤ C.row)
    (rows : Option ℕ) :
    (rows.map fun n ↦ m + r * n).getD 0 ≤ (rows.map fun n ↦ C.matrix + C.row * n).getD 0 := by
  cases rows with
  | none => simp
  | some n =>
    simp only [Option.map_some, Option.getD_some]
    have := Nat.mul_le_mul_right n hr
    have := hC.matrix
    omega

/-- **The node's words within its budget**, each child's words with the claim lists' excess (`2 · 252`)
within the child's coefficient. -/
theorem nodeWords_le (C : Coefs) (hC : C.Covers) (it : NodeItems) (hd : it.DeclaredFit)
    (hchild : ∀ c ∈ it.children, childWords c.shape + 504 ≤ C.child) :
    nodeWords it ≤ C.budget it := by
  have hs := sum_children_le (l := it.children) (k := 1) (a := C.child) (b := C.claim)
    (f := fun c ↦ childWords c.shape + walkWords c.xmssClaims + walkWords c.sphincsClaims +
      21 * (c.xmssClaims + c.sphincsClaims)) fun c hc ↦ by
      have := hchild c hc
      have := walkWords_le c.xmssClaims
      have := walkWords_le c.sphincsClaims
      have : 46 * (c.xmssClaims + c.sphincsClaims) ≤ C.claim * (c.xmssClaims + c.sphincsClaims) :=
        Nat.mul_le_mul_right _ hC.claim
      omega
  rw [List.sum_map_add, List.sum_map_mul_left] at hs
  have hdx := digestWords_le it.declaredXmss
  have hds := digestWords_le it.declaredSphincs
  have hx : 1333 * it.xmss ≤ C.xmss * it.xmss := Nat.mul_le_mul_right _ hC.xmss
  have hsp : 7336 * it.sphincs ≤ C.sphincs * it.sphincs := Nat.mul_le_mul_right _ hC.sphincs
  have hm := matrix_le hC (m := 95403) (r := 118441) (by omega) hC.row it.rows
  have hf := hC.fixed
  unfold nodeWords Coefs.budget matrixWords
  unfold NodeItems.DeclaredFit NodeItems.holders at hd
  unfold NodeItems.holders NodeItems.childClaims at *
  generalize (it.children.map fun c ↦ c.xmssClaims + c.sphincsClaims).sum = Sg at *
  generalize (it.children.map fun c ↦ childWords c.shape + walkWords c.xmssClaims +
    walkWords c.sphincsClaims).sum = SG at *
  omega

/-- **The node's rows below its budget.** -/
theorem nodeRows_lt (C : Coefs) (hC : C.Covers) (it : NodeItems) (hd : it.DeclaredFit)
    (hchild : ∀ c ∈ it.children, childRows c.shape ≤ C.child) :
    nodeRows it < C.budget it := by
  have hs := sum_children_le (l := it.children) (k := 1) (a := C.child) (b := C.claim)
    (f := fun c ↦ childRows c.shape + walkRows c.xmssClaims + walkRows c.sphincsClaims +
      18 * (c.xmssClaims + c.sphincsClaims)) fun c hc ↦ by
      have := hchild c hc
      have := walkRows_le c.xmssClaims
      have := walkRows_le c.sphincsClaims
      have : 46 * (c.xmssClaims + c.sphincsClaims) ≤ C.claim * (c.xmssClaims + c.sphincsClaims) :=
        Nat.mul_le_mul_right _ hC.claim
      omega
  rw [List.sum_map_add, List.sum_map_mul_left] at hs
  have hdx := digestRows_le it.declaredXmss
  have hds := digestRows_le it.declaredSphincs
  have hx : 1333 * it.xmss ≤ C.xmss * it.xmss := Nat.mul_le_mul_right _ hC.xmss
  have hsp : 7336 * it.sphincs ≤ C.sphincs * it.sphincs := Nat.mul_le_mul_right _ hC.sphincs
  have hm := matrix_le hC (m := 95546) (r := 76993) (by omega) (by have := hC.row; omega) it.rows
  have hf := hC.fixed
  unfold nodeRows Coefs.budget matrixRows
  unfold NodeItems.DeclaredFit NodeItems.holders at hd
  unfold NodeItems.holders NodeItems.childClaims at *
  generalize (it.children.map fun c ↦ c.xmssClaims + c.sphincsClaims).sum = Sg at *
  generalize (it.children.map fun c ↦ childRows c.shape + walkRows c.xmssClaims +
    walkRows c.sphincsClaims).sum = SG at *
  omega

/-- **The node's weighted rows within `25` times its budget**, each child's within `25` times the
child's coefficient. -/
theorem nodeWeighted_le (C : Coefs) (hC : C.Covers) (it : NodeItems) (hd : it.DeclaredFit)
    (hchild : ∀ c ∈ it.children, childWeighted c.shape ≤ 25 * C.child) :
    nodeWeighted it ≤ 25 * C.budget it := by
  have hs := sum_children_le (l := it.children) (k := 25) (a := C.child) (b := C.claim)
    (f := fun c ↦ childWeighted c.shape + walkWeighted c.xmssClaims +
      walkWeighted c.sphincsClaims + 159 * (c.xmssClaims + c.sphincsClaims)) fun c hc ↦ by
      have := hchild c hc
      have := walkWeighted_le c.xmssClaims
      have := walkWeighted_le c.sphincsClaims
      have : 46 * (c.xmssClaims + c.sphincsClaims) ≤ C.claim * (c.xmssClaims + c.sphincsClaims) :=
        Nat.mul_le_mul_right _ hC.claim
      omega
  rw [List.sum_map_add, List.sum_map_mul_left] at hs
  have hdx := digestWeighted_le it.declaredXmss
  have hds := digestWeighted_le it.declaredSphincs
  have hx : 1333 * it.xmss ≤ C.xmss * it.xmss := Nat.mul_le_mul_right _ hC.xmss
  have hsp : 7336 * it.sphincs ≤ C.sphincs * it.sphincs := Nat.mul_le_mul_right _ hC.sphincs
  have hm : matrixWeighted it.rows ≤ 25 * (it.rows.map fun n ↦ C.matrix + C.row * n).getD 0 := by
    cases it.rows with
    | none => simp [matrixWeighted]
    | some n =>
      simp only [matrixWeighted, Option.map_some, Option.getD_some]
      have := Nat.mul_le_mul_right n hC.row
      have := hC.matrix
      omega
  have hf := hC.fixed
  unfold nodeWeighted Coefs.budget
  unfold NodeItems.DeclaredFit NodeItems.holders at hd
  unfold NodeItems.holders NodeItems.childClaims at *
  generalize (it.children.map fun c ↦ c.xmssClaims + c.sphincsClaims).sum = Sg at *
  generalize (it.children.map fun c ↦ childWeighted c.shape + walkWeighted c.xmssClaims +
    walkWeighted c.sphincsClaims).sum = SG at *
  omega

/-! ## A child's part against the child's coefficient -/

/-- **A child's words and the claim lists' excess**, with or without the zero-challenge sum, within
`393701`, the least child coefficient this count covers every child with
(`childWords_corrected_attained`). -/
theorem childWords_le_corrected {s : ChildShape} (h : s.Admissible) :
    childWords s + 504 ≤ 393701 := by
  have := forall_index h (P := fun i ↦ vsWordsNone.getD i 0 + 6625 + 504 ≤ 393701 ∧
      vsWordsAll.getD i 0 + 6625 + 504 ≤ 393701) (by decide)
  unfold childWords ChildShape.read
  split_ifs <;> omega

/-- The bound is attained: a child at stack `2^30`, rate `1`, with the sum. -/
theorem childWords_corrected_attained : childWords ⟨30, 1, true⟩ + 504 = 393701 := by decide

theorem childRows_le {s : ChildShape} (h : s.Admissible) : childRows s ≤ 327604 := by
  have := forall_index h (P := fun i ↦ vsRowsNone.getD i 0 + 1741 ≤ 327604 ∧
      vsRowsAll.getD i 0 + 1741 ≤ 327604) (by decide)
  unfold childRows ChildShape.read
  split_ifs <;> omega

theorem childWeighted_le {s : ChildShape} (h : s.Admissible) : childWeighted s ≤ 3304613 := by
  have := forall_index h (P := fun i ↦ vsWeightedNone.getD i 0 + 17989 ≤ 3304613 ∧
      vsWeightedAll.getD i 0 + 17989 ≤ 3304613) (by decide)
  unfold childWeighted ChildShape.read
  split_ifs <;> omega

/-! ## A corrected budget -/

/-- The deployed coefficients with the child's replaced. -/
def Coefs.corrected (child : ℕ) : Coefs := ⟨46, child, 1400, 7500, 131072, 122000, 32768⟩

theorem Coefs.corrected_covers (child : ℕ) : (Coefs.corrected child).Covers :=
  ⟨by simp [Coefs.corrected], by simp [Coefs.corrected], by simp [Coefs.corrected],
    by simp [Coefs.corrected], by simp [Coefs.corrected], by simp [Coefs.corrected]⟩

/-- **A corrected budget bounds the count on every node**, a child's coefficient at least `393701`. -/
theorem corrected_bounds {child : ℕ} (hchild : 393701 ≤ child) (it : NodeItems) (hd : it.DeclaredFit)
    (hadm : ∀ c ∈ it.children, c.shape.Admissible) :
    nodeWords it ≤ (Coefs.corrected child).budget it ∧
      nodeRows it < (Coefs.corrected child).budget it ∧
      nodeWeighted it ≤ 25 * (Coefs.corrected child).budget it := by
  have hC := Coefs.corrected_covers child
  refine ⟨nodeWords_le _ hC it hd fun c hc ↦ ?_, nodeRows_lt _ hC it hd fun c hc ↦ ?_,
    nodeWeighted_le _ hC it hd fun c hc ↦ ?_⟩
  · have := childWords_le_corrected (hadm c hc); simp only [Coefs.corrected]; omega
  · have := childRows_le (hadm c hc); simp only [Coefs.corrected]; omega
  · have := childWeighted_le (hadm c hc); simp only [Coefs.corrected]; omega

end

end LeanVM.Guest.Budget
