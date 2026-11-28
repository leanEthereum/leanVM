/-
  LeanVM.Guest.Budget.HandCount

  The static checker's count with hand functions as a function of a node's items (`nodeWordsC`), the
  smallest coefficients it fits (`Coefs.checker`, `Coefs.checkerZero`), and `main`'s aligned words, so
  the run's memory, within the budget at any coefficients at least those.
-/

module

public import LeanVM.Guest.Memory.GuestWordsNode
public import LeanVM.Guest.Budget.Words

/-!
# The checker's count and its coefficients

The family with hand functions (`Memory/GuestWordsH.lean`) bounds `main`'s tree by its inner bound at
its virtual parameters plus the node's constants (`Memory/GuestWordsNode.lean`): `da_verify`'s words at
the node's blob rows and the children's loop's at its children's lists. As functions of the node's
items:

* `mainWordsC`: `main`'s inner bound (its frame and fixed callees `41235`, a slot `5`, a declared claim
  `15` for the two lists' digests, a duplicate slot's loop `16`, a raw leanXMSS loop iteration `1327`,
  a raw leanSPHINCS one `7315`, a child's cells `993`), at its values: the slots, the declared claims,
  the duplicate slots, the raw signatures and the children of its meta hint;
* `daWordsC`: `da_verify`'s inner bound at `n` rows (`96198 + 120893 n` and `18` a padding row);
* `loopWordsC K`: the children's loop, an iteration `K` and `45` a claim of the child's two lists
  (`child_claim_list_digest`'s outer bound) each, and its last phantom frame `62`; `K = 456272` with the
  zero-challenge sum counted, `372185` without (`verify_sub`'s outer bound `427606`, `343519`).

`nodeWordsC_le`: within `C.budget` for every `C` covering `Coefs.checker` (`Coefs.checkerZero`
without the sum): a claim `66`, a child `K + 993`, a raw leanXMSS `1348`, a raw leanSPHINCS `7336`, a
blob matrix `96774`, a row `120875`, the rest `41297`. So `main`'s aligned words, and the memory's log
size, are within `2^24` when the budget at such coefficients is (`logMem_le_of_hand`).
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest

@[expose] public section

/-- `main`'s inner bound at a node's items. -/
def mainWordsC (it : NodeItems) : ℕ :=
  41235 + 5 * it.holders + 15 * (it.declaredXmss + it.declaredSphincs) +
    16 * (it.holders - it.declaredXmss - it.declaredSphincs) + 1327 * it.xmss + 7315 * it.sphincs +
    993 * it.children.length

/-- `da_verify`'s inner bound at a node's blob rows. -/
def daWordsC (rows : Option ℕ) : ℕ := (rows.map fun n ↦ 96198 + 120893 * n + 18 * (32 - n)).getD 0

/-- The children's loop: an iteration `K` and `45` a claim of each child's lists, and its last frame. -/
def loopWordsC (K : ℕ) (it : NodeItems) : ℕ :=
  (it.children.map fun c ↦ K + 45 * (c.xmssClaims + c.sphincsClaims)).sum + 62

/-- **The checker's count of a node's words**, an iteration of the children's loop at `K`. -/
def nodeWordsC (K : ℕ) (it : NodeItems) : ℕ := mainWordsC it + daWordsC it.rows + loopWordsC K it

/-- The children's loop's iteration, the zero-challenge sum counted. -/
def iterSum : ℕ := 456272
/-- The children's loop's iteration, the zero-challenge sum absent. -/
def iterZero : ℕ := 372185

/-- **The smallest coefficients the checker's count fits**, the zero-challenge sum counted. -/
def Coefs.checker : Coefs := ⟨66, iterSum + 993, 1348, 7336, 96774, 120875, 41297⟩
/-- **The smallest coefficients the checker's count fits**, the zero-challenge sum absent. -/
def Coefs.checkerZero : Coefs := ⟨66, iterZero + 993, 1348, 7336, 96774, 120875, 41297⟩

theorem loopWordsC_eq (K : ℕ) (it : NodeItems) :
    loopWordsC K it = K * it.children.length + 45 * it.childClaims + 62 := by
  unfold loopWordsC NodeItems.childClaims
  induction it.children with
  | nil => simp
  | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      rw [Nat.add_assoc] at ih ⊢
      have := ih
      rw [Nat.mul_succ]
      omega

/-- **The checker's count within the budget** at coefficients covering its own: the children's loop's
iteration `K` within the child's less `993`, each blob matrix of at most `32` rows. -/
theorem nodeWordsC_le {K : ℕ} {C : Coefs}
    (hC : Coefs.Above ⟨66, K + 993, 1348, 7336, 96774, 120875, 41297⟩ C) (it : NodeItems)
    (hd : it.DeclaredFit) (hrows : ∀ n ∈ it.rows, n ≤ 32) : nodeWordsC K it ≤ C.budget it := by
  have hl := loopWordsC_eq K it
  have hc := Nat.mul_le_mul_right it.childClaims hC.claim
  have hk := Nat.mul_le_mul_right it.children.length hC.child
  have hx := Nat.mul_le_mul_right it.xmss hC.xmss
  have hs := Nat.mul_le_mul_right it.sphincs hC.sphincs
  have hf := hC.fixed
  have hda : daWordsC it.rows ≤ (it.rows.map fun n ↦ C.matrix + C.row * n).getD 0 := by
    unfold daWordsC
    cases h : it.rows with
    | none => simp
    | some n =>
        simp only [Option.map_some, Option.getD_some]
        have := hrows n (by rw [h]; rfl)
        have := Nat.mul_le_mul_right n hC.row
        have := hC.matrix
        simp only at *
        omega
  unfold nodeWordsC mainWordsC Coefs.budget
  unfold NodeItems.DeclaredFit NodeItems.holders at hd
  unfold NodeItems.holders
  simp only at hc hk hx hs hf
  rw [Nat.add_mul] at hk
  omega

theorem checker_above : Coefs.Above ⟨66, iterSum + 993, 1348, 7336, 96774, 120875, 41297⟩ Coefs.checker :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

theorem checkerZero_above :
    Coefs.Above ⟨66, iterZero + 993, 1348, 7336, 96774, 120875, 41297⟩ Coefs.checkerZero :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

/-- **Memory within `2^24` from the budget at the checker's coefficients**: a tree of cost within the
count has its memory's log size at most `24` when the budget is within `2^24`. -/
theorem logMem_le_of_count {K : ℕ} {C : Coefs}
    (hC : Coefs.Above ⟨66, K + 993, 1348, 7336, 96774, 120875, 41297⟩ C) {it : NodeItems}
    (hd : it.DeclaredFit) (hrows : ∀ n ∈ it.rows, n ≤ 32) (hB : C.budget it ≤ 2 ^ 24)
    {fs : String → ℕ} {lp al : String → Bool} (hfs : ∀ g, fs g ≤ fsW g)
    (hal : ∀ g, al g = true → alW g = true) (htl : ∀ f, fs (tailKey f) ≤ fs f) {T : Tree}
    (hb : T.BufsOk coreProgram) (hc : T.cost coreProgram true (fsPad fsW alW) ≤ nodeWordsC K it) :
    logMem (T.wordsA fs lp al) ≤ 24 :=
  logMem_le_iff.mpr ⟨by decide, (wordsA_le_of_cost hfs hal htl hb
    (hc.trans (nodeWordsC_le hC it hd hrows))).trans hB⟩

variable {rd : Reader} {σ : Val} {bufs : List ℕ} {kids : List Memory.Tree} {args rets : List E} {it : NodeItems}

/-- **`main`'s tree within the checker's count**, the zero-challenge sum counted: its callees' hand
facts at the node's constants `daWordsC it.rows`, `loopWordsC iterSum it`, the children's loop's run
within the latter, and `main`'s inner bound at its values within `mainWordsC it`. -/
theorem wh_cost_le_count
    (hv : (Memory.Tree.node "main" σ bufs kids).Valid coreProgram rd args rets)
    (hb : (Memory.Tree.node "main" σ bufs kids).BufsOk coreProgram)
    (hkids : ∀ k ∈ kids, k.name = "__loop4_main" ∨ k.Every (HandFact coreProgram
      (whCertAt (daWordsC it.rows) (loopWordsC iterSum it)) (whHandAt (daWordsC it.rows) (loopWordsC iterSum it))
      whOut))
    (hloop : ∀ k ∈ kids, k.name = "__loop4_main" → ∀ a r, k.Valid coreProgram rd a r → ∃ S,
      LoopRun "__loop4_main" (coreProgram[Data.whidxLoop]'wh_nodeIdx.hl).params Data.whloopHand 62
        (fun k => k.Every (HandFact coreProgram (whCertAt (daWordsC it.rows) (loopWordsC iterSum it))
          (whHandAt (daWordsC it.rows) (loopWordsC iterSum it)) whOut)) k S ∧ S ≤ loopWordsC iterSum it)
    (hpre : ArgsPre Data.whmainHand.pre (args ++ Data.whmainHand.vps.map σ))
    (hmain : Data.whmainHand.b.eval (args ++ Data.whmainHand.vps.map σ) ≤ mainWordsC it) :
    (Memory.Tree.node "main" σ bufs kids).cost coreProgram true (fsPad fsW alW) ≤ nodeWordsC iterSum it :=
  (wh_mainCost_le _ _ hv hb hkids hloop hpre).trans (by unfold nodeWordsC; omega)

/-- **`main`'s tree within the checker's count**, the zero-challenge sum absent (no
`level_residual_sum__*` node, `wzOut` in every hand fact). -/
theorem wz_cost_le_count
    (hv : (Memory.Tree.node "main" σ bufs kids).Valid coreProgram rd args rets)
    (hb : (Memory.Tree.node "main" σ bufs kids).BufsOk coreProgram)
    (hkids : ∀ k ∈ kids, k.name = "__loop4_main" ∨ k.Every (HandFact coreProgram
      (wzCertAt (daWordsC it.rows) (loopWordsC iterZero it)) (wzHandAt (daWordsC it.rows) (loopWordsC iterZero it))
      wzOut))
    (hloop : ∀ k ∈ kids, k.name = "__loop4_main" → ∀ a r, k.Valid coreProgram rd a r → ∃ S,
      LoopRun "__loop4_main" (coreProgram[Data.wzidxLoop]'wz_nodeIdx.hl).params Data.wzloopHand 62
        (fun k => k.Every (HandFact coreProgram (wzCertAt (daWordsC it.rows) (loopWordsC iterZero it))
          (wzHandAt (daWordsC it.rows) (loopWordsC iterZero it)) wzOut)) k S ∧ S ≤ loopWordsC iterZero it)
    (hpre : ArgsPre Data.wzmainHand.pre (args ++ Data.wzmainHand.vps.map σ))
    (hmain : Data.wzmainHand.b.eval (args ++ Data.wzmainHand.vps.map σ) ≤ mainWordsC it) :
    (Memory.Tree.node "main" σ bufs kids).cost coreProgram true (fsPad fsW alW) ≤ nodeWordsC iterZero it :=
  (wz_mainCost_le _ _ hv hb hkids hloop hpre).trans (by unfold nodeWordsC; omega)

end

end LeanVM.Guest.Budget
