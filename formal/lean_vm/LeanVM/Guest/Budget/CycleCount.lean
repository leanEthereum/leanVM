/-
  LeanVM.Guest.Budget.CycleCount

  The static checker's count of each opcode's instructions with hand functions, as functions of a
  node's items (`cntC`), the run's opcode counts within it (`opcodeCount_le_cnt`), so its steps and
  weighted table rows (`rows_le_count`), and the smallest coefficients it fits (`Coefs.rowsC`): within
  a budget of at most `2^24` at coefficients at least those, fewer than `2^24` steps and a committed
  size of at most `2^30` (`cycles_committed_of_count`).
-/

module

public import LeanVM.Guest.Memory.GuestCnt
public import LeanVM.Guest.Complete.Committed

/-!
# The checker's count of instructions and its coefficients

The vector family with hand functions (`Memory/GuestCnt.lean`) bounds `main`'s tree's instructions of
each opcode by its inner bound at its virtual parameters plus the node's constants, `da_verify`'s at the
node's blob rows and the children's loop's at its children's lists. As functions of the node's items,
a coordinate per opcode (`v6`):

* `mainCntC`: `main`'s inner bound (`mainV`), a declared claim `declV`, a duplicate slot `dupV`, a raw
  leanXMSS loop iteration `xmssV`, a raw leanSPHINCS one `sphincsV`, a child's own `childV`;
* `daCntC`: `da_verify`'s at `n` rows, `daV + rowV n + padV (32 - n)`;
* `loopCntC K`: the children's loop, an iteration `K` and `claimV` a claim of the child's two lists each,
  its last phantom frame `lastV`; `K = iterSumV` with the zero-challenge sum counted, `iterZeroV`
  without.

B2's count (`B2C.b2_countL`) bounds a run's instructions of each opcode by `B2C.cnt T op`, within `T`'s
weight at `ωC op` and the jump table's `SET`s (`B2C.cnt_le_weight_arm`). So the run's steps are within
`rowsOf (cntJ K · it)` and its weighted table rows within `weightedOf`, and at any coefficients above
`Coefs.rowsC` with the budget within `2^24` its steps are fewer than `2^24` and, its memory within
`2^24` words, its committed size at most `2^30` (`cycles_committed_of_count`, by the lead's
`committedOfRows`). The words' coefficients `Coefs.checker`, `Coefs.checkerZero` are above them
(`checker_aboveRows`, `checkerZero_aboveRows`).
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest LeanVM.Node
open LeanVM.Protocol

@[expose] public section

/-- A count per opcode, in `Opcode`'s order. -/
def v6 (a b c d e f : ℕ) : Opcode → ℕ
  | .xor => a
  | .mulNative => b
  | .setConstant => c
  | .deref => d
  | .jump => e
  | .keccak => f

/-- A count's instructions. -/
def rowsOf (x : Opcode → ℕ) : ℕ := x .xor + x .mulNative + x .setConstant + x .deref + x .jump + x .keccak

/-- A count's instructions weighed by their tables' committed columns (`tableWeighted`'s). -/
def weightedOf (x : Opcode → ℕ) : ℕ :=
  7 * x .xor + 9 * x .mulNative + 5 * x .setConstant + 10 * x .deref + 14 * x .jump + 68 * x .keccak

/-! ## The vectors, read off the family (`scripts/count/cycles.py --table`) -/

/-- `main`'s inner constant. -/
def mainV : Opcode → ℕ := v6 1374 614 2703 4759 77 169
/-- A declared claim's (the two claim-list digests). -/
def declV : Opcode → ℕ := v6 5 1 1 5 1 1
/-- A duplicate slot's loop. -/
def dupV : Opcode → ℕ := v6 1 6 4 5 2 0
/-- A raw leanXMSS loop iteration. -/
def xmssV : Opcode → ℕ := v6 181 138 109 166 42 398
/-- A raw leanSPHINCS loop iteration. -/
def sphincsV : Opcode → ℕ := v6 2081 1465 1661 298 143 899
/-- A child's own instructions in `main`. -/
def childV : Opcode → ℕ := v6 87 119 101 301 8 21
/-- `da_verify`'s constant. -/
def daV : Opcode → ℕ := v6 34082 34729 1686 23708 605 32
/-- `da_verify`'s row. -/
def rowV : Opcode → ℕ := v6 33159 18365 2893 19643 780 2175
/-- `da_verify`'s padding row. -/
def padV : Opcode → ℕ := v6 1 6 6 7 2 0
/-- The children's loop's iteration, the zero-challenge sum counted. -/
def iterSumV : Opcode → ℕ := v6 99887 130680 30507 66245 13177 9533
/-- The children's loop's iteration, the zero-challenge sum absent. -/
def iterZeroV : Opcode → ℕ := v6 77398 99889 14570 51991 11783 9533
/-- A claim of a child's list in the children's loop. -/
def claimV : Opcode → ℕ := v6 9 11 1 14 1 1
/-- The children's loop's last frame. -/
def lastV : Opcode → ℕ := v6 1 19 8 64 6 0

/-- `main`'s inner bound at a node's items. -/
def mainCntC (op : Opcode) (it : NodeItems) : ℕ :=
  mainV op + declV op * (it.declaredXmss + it.declaredSphincs) +
    dupV op * (it.holders - it.declaredXmss - it.declaredSphincs) + xmssV op * it.xmss +
    sphincsV op * it.sphincs + childV op * it.children.length

/-- `da_verify`'s inner bound at a node's blob rows. -/
def daCntC (op : Opcode) (rows : Option ℕ) : ℕ :=
  (rows.map fun n ↦ daV op + rowV op * n + padV op * (32 - n)).getD 0

/-- The children's loop: an iteration `K` and `claimV` a claim of each child's lists, and its last frame. -/
def loopCntC (K : Opcode → ℕ) (op : Opcode) (it : NodeItems) : ℕ :=
  (it.children.map fun c ↦ K op + claimV op * (c.xmssClaims + c.sphincsClaims)).sum + lastV op

/-- **The checker's count of a node's instructions of `op`**, but the jump table's. -/
def cntC (K : Opcode → ℕ) (op : Opcode) (it : NodeItems) : ℕ :=
  mainCntC op it + daCntC op it.rows + loopCntC K op it

/-- The count with the jump table's `SET`s. -/
def cntJ (K : Opcode → ℕ) (op : Opcode) (it : NodeItems) : ℕ := cntC K op it + B2C.jtSets op

theorem loopCntC_eq (K : Opcode → ℕ) (op : Opcode) (it : NodeItems) :
    loopCntC K op it = K op * it.children.length + claimV op * it.childClaims + lastV op := by
  unfold loopCntC NodeItems.childClaims
  induction it.children with
  | nil => simp
  | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      rw [Nat.mul_succ, Nat.mul_add]
      linarith

theorem jtSets_eq (op : Opcode) : B2C.jtSets op = v6 0 0 15429 0 0 0 op := by
  cases op <;> rfl

/-! ## The run within the count -/

variable {rd : Reader} {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree} {args rets : List E} {it : NodeItems}

/-- **`main`'s tree's instructions of each opcode within the checker's count**, the zero-challenge
sum absent: its callees' hand facts at the node's constants `daCntC op it.rows`, `loopCntC iterZeroV op
it`, the children's loop's run within the latter, and `main`'s inner bound at its values within
`mainCntC op it`. -/
theorem cz_weight_le_count (op : Opcode)
    (hv : (Memory.Tree.node "main" σ bufs kids).Valid coreProgram rd args rets)
    (hb : (Memory.Tree.node "main" σ bufs kids).BufsOk coreProgram)
    (hkids : ∀ k ∈ kids, k.name = "__loop4_main" ∨ k.Every (HandFact coreProgram
      (czCertAt op (daCntC op it.rows) (loopCntC iterZeroV op it))
      (czHandAt op (daCntC op it.rows) (loopCntC iterZeroV op it)) (czOut op)))
    (hloop : ∀ k ∈ kids, k.name = "__loop4_main" → ∀ a r, k.Valid coreProgram rd a r → ∃ S,
      LoopRun "__loop4_main" (coreProgram[Data.czidxLoop]'cz_nodeIdx.hl).params
        (Data.czloopHand.proj (B2C.opIdx op)) (ωC op "__loop4_main")
        (fun k => k.Every (HandFact coreProgram (czCertAt op (daCntC op it.rows) (loopCntC iterZeroV op it))
          (czHandAt op (daCntC op it.rows) (loopCntC iterZeroV op it)) (czOut op))) k S ∧
        S ≤ loopCntC iterZeroV op it)
    (hpre : ArgsPre Data.czmainHand.pre (args ++ Data.czmainHand.vps.map σ))
    (hmain : (Data.czmainHand.b.proj (B2C.opIdx op)).eval (args ++ Data.czmainHand.vps.map σ) ≤ mainCntC op it) :
    (Memory.Tree.node "main" σ bufs kids).weight (ωC op) ≤ cntC iterZeroV op it :=
  (cz_mainWeight_le op _ _ hv hb hkids hloop hpre).trans (by unfold cntC; omega)

/-- **`main`'s tree's instructions of each opcode within the checker's count**, the zero-challenge
sum counted. -/
theorem ch_weight_le_count (op : Opcode)
    (hv : (Memory.Tree.node "main" σ bufs kids).Valid coreProgram rd args rets)
    (hb : (Memory.Tree.node "main" σ bufs kids).BufsOk coreProgram)
    (hkids : ∀ k ∈ kids, k.name = "__loop4_main" ∨ k.Every (HandFact coreProgram
      (chCertAt op (daCntC op it.rows) (loopCntC iterSumV op it))
      (chHandAt op (daCntC op it.rows) (loopCntC iterSumV op it)) (chOut op)))
    (hloop : ∀ k ∈ kids, k.name = "__loop4_main" → ∀ a r, k.Valid coreProgram rd a r → ∃ S,
      LoopRun "__loop4_main" (coreProgram[Data.chidxLoop]'ch_nodeIdx.hl).params
        (Data.chloopHand.proj (B2C.opIdx op)) (ωC op "__loop4_main")
        (fun k => k.Every (HandFact coreProgram (chCertAt op (daCntC op it.rows) (loopCntC iterSumV op it))
          (chHandAt op (daCntC op it.rows) (loopCntC iterSumV op it)) (chOut op))) k S ∧
        S ≤ loopCntC iterSumV op it)
    (hpre : ArgsPre Data.chmainHand.pre (args ++ Data.chmainHand.vps.map σ))
    (hmain : (Data.chmainHand.b.proj (B2C.opIdx op)).eval (args ++ Data.chmainHand.vps.map σ) ≤ mainCntC op it) :
    (Memory.Tree.node "main" σ bufs kids).weight (ωC op) ≤ cntC iterSumV op it :=
  (ch_mainWeight_le op _ _ hv hb hkids hloop hpre).trans (by unfold cntC; omega)

/-- **A run's instructions of each opcode within the count**: B2's `cnt T op` (`B2C.b2_countL`) within
`T`'s weight and the jump table's `SET`s. -/
theorem opcodeCount_le_cnt {K : Opcode → ℕ} {t : Execution guestProgram} {T : Memory.Tree}
    (hv : T.Valid coreProgram rd [] []) (hc : ∀ op, t.opcodeCount op ≤ B2C.cnt T op)
    (hw : ∀ op, T.weight (ωC op) ≤ cntC K op it) (op : Opcode) : t.opcodeCount op ≤ cntJ K op it :=
  (hc op).trans ((B2C.cnt_le_weight_arm B2C.xmssArmC B2C.xmssArmC_spec rd T hv op).trans
    (Nat.add_le_add_right (hw op) _))

theorem tableRows_sum_eq (t : Execution guestProgram) : t.tableRows.sum = rowsOf t.opcodeCount := by
  simp only [Execution.tableRows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, rowsOf]
  omega

theorem tableWeighted_eq (t : Execution guestProgram) : tableWeighted t = weightedOf t.opcodeCount := by
  simp only [tableWeighted, Execution.tableRows, List.map_cons, List.map_nil, List.zipWith_cons_cons,
    List.zipWith_nil_left, List.sum_cons, List.sum_nil, weightedOf]
  omega

/-- **The run's table rows and weighted rows within the count.** -/
theorem rows_le_count {K : Opcode → ℕ} {t : Execution guestProgram} (h : ∀ op, t.opcodeCount op ≤ cntJ K op it) :
    t.tableRows.sum ≤ rowsOf (cntJ K · it) ∧ tableWeighted t ≤ weightedOf (cntJ K · it) := by
  rw [tableRows_sum_eq, tableWeighted_eq]
  have := h .xor; have := h .mulNative; have := h .setConstant; have := h .deref; have := h .jump
  have := h .keccak
  simp only [rowsOf, weightedOf]
  omega

/-! ## The coefficients -/

/-- **The smallest coefficients the checker's count of instructions fits**, the children's loop's
iteration `K`: steps below the budget and weighted rows within `31` times it less `2^15`. -/
def Coefs.rowsC (K : Opcode → ℕ) : Coefs := ⟨60, rowsOf K + 637, 1057, 6570, 95546, 76993, 25224⟩

theorem cntJ_split (K : Opcode → ℕ) (op : Opcode) (it : NodeItems) :
    cntJ K op it = cntJ (fun _ ↦ 0) op it + K op * it.children.length := by
  simp only [cntJ, cntC, loopCntC_eq]; ring

theorem rowsOf_cntJ (K : Opcode → ℕ) (it : NodeItems) :
    rowsOf (cntJ K · it) = rowsOf (cntJ (fun _ ↦ 0) · it) + rowsOf K * it.children.length := by
  simp only [rowsOf, cntJ_split K _ it]; ring

theorem weightedOf_cntJ (K : Opcode → ℕ) (it : NodeItems) :
    weightedOf (cntJ K · it) = weightedOf (cntJ (fun _ ↦ 0) · it) + weightedOf K * it.children.length := by
  simp only [weightedOf, cntJ_split K _ it]; ring

/-- The blob matrix's instructions within its coefficients, and its weighted ones within `31` times. -/
theorem da_le_budget {C : Coefs} (hm : 95546 ≤ C.matrix) (hr : 76993 ≤ C.row) {rows : Option ℕ}
    (hrows : ∀ n ∈ rows, n ≤ 32) :
    rowsOf (fun op ↦ daCntC op rows) ≤ (rows.map fun n ↦ C.matrix + C.row * n).getD 0 ∧
      weightedOf (fun op ↦ daCntC op rows) ≤ 31 * (rows.map fun n ↦ C.matrix + C.row * n).getD 0 := by
  cases rows with
  | none => simp [rowsOf, weightedOf, daCntC]
  | some n =>
      have hn := hrows n rfl
      have := Nat.mul_le_mul_right n hr
      simp only [rowsOf, weightedOf, daCntC, Option.map_some, Option.getD_some, daV, rowV, padV, v6]
      constructor <;> omega

/-- **The count's steps and weighted rows within the budget** at coefficients above `Coefs.rowsC K`,
`K`'s weighted rows within `31` times its child's coefficient. -/
theorem cnt_le_budget {K : Opcode → ℕ} {C : Coefs} (hC : Coefs.Above (Coefs.rowsC K) C)
    (hK : weightedOf K + 6735 ≤ 31 * (rowsOf K + 637)) (it : NodeItems)
    (hd : it.DeclaredFit) (hrows : ∀ n ∈ it.rows, n ≤ 32) :
    rowsOf (cntJ K · it) + 1 ≤ C.budget it ∧ weightedOf (cntJ K · it) + 2 ^ 15 ≤ 31 * C.budget it := by
  rw [rowsOf_cntJ, weightedOf_cntJ]
  have hc := Nat.mul_le_mul_right it.childClaims hC.claim
  have hx := Nat.mul_le_mul_right it.xmss hC.xmss
  have hs := Nat.mul_le_mul_right it.sphincs hC.sphincs
  have hf := hC.fixed
  have hk : rowsOf K * it.children.length + 637 * it.children.length ≤ C.child * it.children.length := by
    have := Nat.mul_le_mul_right it.children.length hC.child
    simp only [Coefs.rowsC] at this
    calc rowsOf K * it.children.length + 637 * it.children.length
        = (rowsOf K + 637) * it.children.length := by ring
      _ ≤ _ := this
  have hKk : weightedOf K * it.children.length + 6735 * it.children.length ≤
      31 * (rowsOf K * it.children.length) + 19747 * it.children.length := by
    have := Nat.mul_le_mul_right it.children.length hK
    calc weightedOf K * it.children.length + 6735 * it.children.length
        = (weightedOf K + 6735) * it.children.length := by ring
      _ ≤ 31 * (rowsOf K + 637) * it.children.length := this
      _ = 31 * (rowsOf K * it.children.length) + 19747 * it.children.length := by ring
  obtain ⟨hR, hW⟩ := da_le_budget (C := C) hC.matrix hC.row hrows
  simp only [Coefs.rowsC] at hc hx hs hf
  unfold NodeItems.DeclaredFit NodeItems.holders at hd
  generalize rowsOf K * it.children.length = X at hk hKk ⊢
  generalize weightedOf K * it.children.length = Y at hKk ⊢
  simp only [rowsOf, weightedOf] at hR hW
  simp only [rowsOf, weightedOf, cntJ, cntC, loopCntC_eq, jtSets_eq, mainCntC, mainV, declV, dupV, xmssV,
    sphincsV, childV, claimV, lastV, v6, Nat.zero_mul, Nat.add_zero, NodeItems.holders, Coefs.budget]
  constructor <;> omega

theorem iterZero_weighted : weightedOf iterZeroV + 6735 ≤ 31 * (rowsOf iterZeroV + 637) := by decide

theorem iterSum_weighted : weightedOf iterSumV + 6735 ≤ 31 * (rowsOf iterSumV + 637) := by decide

/-- The coefficients' values: the child's `265801` without the zero-challenge sum, `350666` with it. -/
theorem rowsC_values : Coefs.rowsC iterZeroV = ⟨60, 265801, 1057, 6570, 95546, 76993, 25224⟩ ∧
    Coefs.rowsC iterSumV = ⟨60, 350666, 1057, 6570, 95546, 76993, 25224⟩ := ⟨by rfl, by rfl⟩

/-- **Fewer than `2^24` steps and a committed size of at most `2^30` from the budget**: at coefficients
above `Coefs.rowsC K`, a valid execution whose instructions of each opcode are within the count and
whose memory is within `2^24` words, on a node within a budget of `2^24`. -/
theorem cycles_committed_of_count {K : Opcode → ℕ} {C : Coefs} (hC : Coefs.Above (Coefs.rowsC K) C)
    (hK : weightedOf K + 6735 ≤ 31 * (rowsOf K + 637)) {it : NodeItems} (hd : it.DeclaredFit)
    (hrows : ∀ n ∈ it.rows, n ≤ 32) (hB : C.budget it ≤ 2 ^ 24) {input : PublicInput}
    {t : Execution guestProgram} (hv : ValidExecution guestProgram input t) (hlog : t.logMemorySize ≤ 24)
    (hcnt : ∀ op, t.opcodeCount op ≤ cntJ K op it) :
    t.stepCount < 2 ^ 24 ∧ t.committedSize ≤ 2 ^ 30 := by
  obtain ⟨h1, h2⟩ := cnt_le_budget hC hK it hd hrows
  obtain ⟨hr, hw⟩ := rows_le_count hcnt
  rw [Complete.tableRows_sum hv] at hr
  have hc := Complete.committedOfRows t
  have hp : 2 ^ (t.logMemorySize + 1) ≤ 2 ^ 25 := Nat.pow_le_pow_right (by decide) (by omega)
  constructor <;> omega

end

end LeanVM.Guest.Budget
