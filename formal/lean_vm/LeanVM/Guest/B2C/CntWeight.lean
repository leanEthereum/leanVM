/-
  LeanVM.Guest.B2C.CntWeight

  The instruction counts as weights: `cnt T op` is `T`'s weight at `pathMax · op` and the jump
  table's `SET`s, the form `B1.Main.mainComplete_of` takes.
-/

module

public import LeanVM.Guest.B2C.Cells

/-!
# Counts as weights

`cnt_le_weight`: `cnt t op ≤ t.weight (ω op) + jtSets op` (`mainComplete_of`'s and
`ea_mainComplete`'s `hcnt`, at `jt := jtSets`), whenever each instance's path count is within its
function's weight `ω op f` (`cnt_le_weight_of`); with no arm counted separately, at
`ω op := (pathMax · op)`.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

mutual
theorem weightV_le (ω : String → Val → ℕ) (ω' : String → ℕ) (h : ∀ f σ, ω f σ ≤ ω' f) :
    ∀ t : Tree, weightV ω t ≤ t.weight ω'
  | .node f σ _ kids => by
    rw [weightV, Tree.weight]
    exact Nat.add_le_add (h f σ) (weightVKids_le ω ω' h kids)
  | .phantom .. => by rw [weightV, Tree.weight]

theorem weightVKids_le (ω : String → Val → ℕ) (ω' : String → ℕ) (h : ∀ f σ, ω f σ ≤ ω' f) :
    ∀ ks : List Tree, weightVKids ω ks ≤ Tree.weightKids ω' ks
  | [] => by rw [weightVKids, Tree.weightKids]
  | k :: ks => by
    rw [weightVKids, Tree.weightKids]
    exact Nat.add_le_add (weightV_le ω ω' h k) (weightVKids_le ω ω' h ks)
end

/-- **The counts within the weights**, each instance's path count within its function's. -/
theorem cnt_le_weight_of (ω : Opcode → String → ℕ) (h : ∀ op f σ, pathCountN f σ op ≤ ω op f)
    (t : Tree) (op : Opcode) : cnt t op ≤ t.weight (ω op) + jtSets op :=
  Nat.add_le_add_right (weightV_le _ _ (h op) t) _

section Valid

variable {P : Core.Program} {rd : Reader} (ω : String → Val → ℕ) (ω' : String → ℕ)

mutual
theorem weightV_le_valid
    (h : ∀ f σ bufs kids args rets, (Memory.Tree.node f σ bufs kids).Valid P rd args rets → ω f σ ≤ ω' f) :
    ∀ (t : Tree) (args rets : List E), t.Valid P rd args rets → weightV ω t ≤ t.weight ω'
  | .node f σ bufs kids, args, rets, hv => by
    have hn := h f σ bufs kids args rets hv
    obtain ⟨_, _, _, es, _, _, _, _, hk⟩ := hv
    rw [weightV, Tree.weight]
    exact Nat.add_le_add hn (weightVKids_le_valid h σ (calls es) kids hk)
  | .phantom .., _, _, hv => hv.elim

theorem weightVKids_le_valid
    (h : ∀ f σ bufs kids args rets, (Memory.Tree.node f σ bufs kids).Valid P rd args rets → ω f σ ≤ ω' f) :
    ∀ (σ : Val) (cs : List Call) (ks : List Tree), Tree.KidsValid P rd σ cs ks →
      weightVKids ω ks ≤ Tree.weightKids ω' ks
  | _, [], [], _ => by rw [weightVKids, Tree.weightKids]
  | _, [], _ :: _, hk => hk.elim
  | _, _ :: _, [], hk => hk.elim
  | σ, c :: cs, k :: ks, ⟨_, hk, hks⟩ => by
    rw [weightVKids, Tree.weightKids]
    refine Nat.add_le_add ?_ (weightVKids_le_valid h σ cs ks hks)
    split_ifs at hk
    · exact weightV_le_valid h k _ _ hk
    · obtain ⟨⟨f, σ', rfl⟩, -⟩ := hk
      rw [weightV]
      exact Nat.zero_le _
end

end Valid

/-- **The counts within the weights** of a valid tree, each valid instance's path count within
its function's weight. -/
theorem cnt_le_weight_valid (ω : Opcode → String → ℕ)
    (h : ∀ op f σ bufs kids rd args rets, (Memory.Tree.node f σ bufs kids).Valid coreProgram rd args rets →
      pathCountN f σ op ≤ ω op f) :
    ∀ (rd : Reader) (t : Tree), t.Valid coreProgram rd [] [] → ∀ op, cnt t op ≤ t.weight (ω op) + jtSets op :=
  fun rd t hv op ↦ Nat.add_le_add_right
    (weightV_le_valid _ _ (fun f σ bufs kids args rets hv' ↦ h op f σ bufs kids rd args rets hv') t [] [] hv) _

mutual
theorem costW_nil (σ : Val) : ∀ ss : List Stmt, costW [] σ ss = 0
  | [] => by rw [costW]
  | s :: ss => by rw [costW, cost1_nil σ s, costW_nil σ ss, zero_add]

theorem cost1_nil (σ : Val) : ∀ s : Stmt, cost1 [] σ s = 0
  | .ite c z n => by
    rw [cost1]
    split_ifs
    · exact costW_nil σ z
    · exact costW_nil σ n
  | .match_ x arms => by rw [cost1]; exact costArms_nil σ x 0 arms
  | .atom _ => rfl
  | .call .. => rfl
  | .callIf .. => rfl
  | .dispatch .. => rfl
  | .ret _ => rfl

theorem costArms_nil (σ : Val) (x : V) : ∀ (k : ℕ) (arms : List (List Stmt)),
    costArms [] σ x (armRaw [] x.idx) k arms = 0
  | _, [] => by rw [costArms]
  | k, a :: as => by
    rw [costArms]
    split_ifs
    · rw [costW_nil σ a, add_zero]
      funext op
      rfl
    · exact costArms_nil σ x (k + 1) as
end

/-! ## The separately counted arms -/

/-- The weights: the most a path runs, and for `verify_lean_xmss` its arms' counts `C`. -/
noncomputable def ωArm (C : Opcode → ℕ) (op : Opcode) (f : String) : ℕ :=
  pathMax f op + if f = "verify_lean_xmss" then C op else 0

/-- Only `verify_lean_xmss` (function `17`) counts arms separately. -/
theorem cplArms_only17 : ∀ j, j ≠ 17 → nth Data.cplArms j [] = [] := by
  intro j hj
  by_cases hl : j < Data.cplArms.length
  · have h : (List.range Data.cplArms.length).all
        (fun j ↦ Nat.beq j 17 || (nth Data.cplArms j []).isEmpty) = true := by decide +kernel
    have := List.all_eq_true.mp h j (List.mem_range.mpr hl)
    simp only [Bool.or_eq_true, List.isEmpty_iff] at this
    rcases this with h1 | h1
    · exact absurd (Nat.eq_of_beq_eq_true h1) hj
    · exact h1
  · exact Check.nth_of_le (by omega)

theorem coreOf17_name : (coreOf 17).name = "verify_lean_xmss" := by decide +kernel

/-- **A valid instance's path count within its weight**, given `verify_lean_xmss`'s arms within
`C` on its valid instances. -/
theorem pathCountN_le_arm (C : Opcode → ℕ)
    (hC : ∀ op σ bufs kids rd args rets,
      (Memory.Tree.node "verify_lean_xmss" σ bufs kids).Valid coreProgram rd args rets →
        costW (nth Data.cplArms 17 []) σ (coreOf 17).body op ≤ C op)
    (op : Opcode) (f : String) (σ : Val) (bufs : List ℕ) (kids : List Tree) (rd : Reader)
    (args rets : List E) (hv : (Memory.Tree.node f σ bufs kids).Valid coreProgram rd args rets) :
    pathCountN f σ op ≤ ωArm C op f := by
  unfold ωArm pathCountN pathMax
  split
  · rename_i j hj
    unfold pathCount
    by_cases h17 : j = 17
    · subst h17
      obtain ⟨i, hi1, hi, hn, -, hcore, -⟩ := fn_of_idx hj
      have hf : f = "verify_lean_xmss" := by rw [← hn, ← hcore, coreOf17_name]
      subst hf
      simp only [↓reduceIte]
      have := hC op σ bufs kids rd args rets hv
      omega
    · rw [cplArms_only17 j h17, costW_nil, Pi.zero_apply]
      omega
  · exact Nat.zero_le _

/-- **The counts within the weights `ωArm C`** on valid trees. -/
theorem cnt_le_weight_arm (C : Opcode → ℕ)
    (hC : ∀ op σ bufs kids rd args rets,
      (Memory.Tree.node "verify_lean_xmss" σ bufs kids).Valid coreProgram rd args rets →
        costW (nth Data.cplArms 17 []) σ (coreOf 17).body op ≤ C op) :
    ∀ (rd : Reader) (t : Tree), t.Valid coreProgram rd [] [] → ∀ op,
      cnt t op ≤ t.weight (ωArm C op) + jtSets op :=
  cnt_le_weight_valid (ωArm C) fun op f σ bufs kids rd args rets hv ↦
    pathCountN_le_arm C hC op f σ bufs kids rd args rets hv

end
end LeanVM.Guest.B2C
