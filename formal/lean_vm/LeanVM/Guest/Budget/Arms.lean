/-
  LeanVM.Guest.Budget.Arms

  The instruction counts as weights: `cnt T op` within `T`'s weight at `ωArm xmssArmC op` (each
  function's `pathMax`, `main_loop2`'s separately counted arms at their largest) and the jump
  table's `SET`s (`cnt_le_weight_arm`, `xmssArmC_spec`). Restored from tag `formal-bus-archive`
  (`B2C/CntWeight.lean`, `B2C/ArmBound.lean`).
-/

module

public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.CoreRef

/-!
# Counts as weights

`cnt_le_weight_valid`: `cnt t op ≤ t.weight (ω op) + jtSets op` whenever each valid instance's path
count is within its function's weight `ω op f`. `pathCount` adds, to a function's `pathMax`, the
separately counted arms its path passes (`costW`), only in `main_loop2` (`cplArms_only`); whatever the
path, they are at most `costMaxW` (`costW_le_max`), on `main_loop2`'s body `xmssArmC op`
(`costMaxCW_arm`, by the kernel), so `cnt_le_weight_arm` holds at `C := xmssArmC` (`xmssArmC_spec`).
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

/-- The weights: the most a path runs, and for `main_loop2` its arms' counts `C`. -/
noncomputable def ωArm (C : Opcode → ℕ) (op : Opcode) (f : String) : ℕ :=
  pathMax f op + if f = name% «main_loop2» then C op else 0

/-- Only `main_loop2` (function `Data.armFn`, leanXMSS's check inline) counts arms separately. -/
theorem cplArms_only : ∀ j, j ≠ Data.armFn → listElementOrDefault Data.cplArms j [] = [] := by
  intro j hj
  by_cases hl : j < Data.cplArms.length
  · have h : (List.range Data.cplArms.length).all
        (fun j ↦ Nat.beq j Data.armFn
            || (listElementOrDefault Data.cplArms j []).isEmpty) = true := by decide +kernel
    have := List.all_eq_true.mp h j (List.mem_range.mpr hl)
    simp only [Bool.or_eq_true, List.isEmpty_iff] at this
    rcases this with h1 | h1
    · exact absurd (Nat.eq_of_beq_eq_true h1) hj
    · exact h1
  · exact Check.nth_of_le (by omega)

theorem coreOf_armFn_name : (coreOf Data.armFn).name = name% «main_loop2» := by decide +kernel

/-- **A valid instance's path count within its weight**, given `main_loop2`'s arms within
`C` on its valid instances. -/
theorem pathCountN_le_arm (C : Opcode → ℕ)
    (hC : ∀ op σ bufs kids rd args rets,
      (Memory.Tree.node name% «main_loop2» σ bufs kids).Valid coreProgram rd args rets →
        costW (listElementOrDefault Data.cplArms Data.armFn []) σ (coreOf Data.armFn).body op ≤ C op)
    (op : Opcode) (f : String) (σ : Val) (bufs : List ℕ) (kids : List Tree) (rd : Reader)
    (args rets : List E) (hv : (Memory.Tree.node f σ bufs kids).Valid coreProgram rd args rets) :
    pathCountN f σ op ≤ ωArm C op f := by
  unfold ωArm pathCountN pathMax
  split
  · rename_i j hj
    unfold pathCount
    by_cases h37 : j = Data.armFn
    · subst h37
      obtain ⟨i, hi1, hi, hn, -, hcore, -⟩ := fn_of_idx hj
      have hf : f = name% «main_loop2» := by rw [← hn, ← hcore, coreOf_armFn_name]
      subst hf
      simp only [↓reduceIte]
      have := hC op σ bufs kids rd args rets hv
      omega
    · rw [cplArms_only j h37, costW_nil, Pi.zero_apply]
      omega
  · exact Nat.zero_le _

/-- **The counts within the weights `ωArm C`** on valid trees. -/
theorem cnt_le_weight_arm (C : Opcode → ℕ)
    (hC : ∀ op σ bufs kids rd args rets,
      (Memory.Tree.node name% «main_loop2» σ bufs kids).Valid coreProgram rd args rets →
        costW (listElementOrDefault Data.cplArms Data.armFn []) σ (coreOf Data.armFn).body op ≤ C op) :
    ∀ (rd : Reader) (t : Tree), t.Valid coreProgram rd [] [] → ∀ op,
      cnt t op ≤ t.weight (ωArm C op) + jtSets op :=
  cnt_le_weight_valid (ωArm C) fun op f σ bufs kids rd args rets hv ↦
    pathCountN_le_arm C hC op f σ bufs kids rd args rets hv

/-! ## `main_loop2`'s arms, bounded -/

/-- A counted `match`'s largest arm at `op`, `0` if not counted. -/
def keyMax (key : Option (List (List ℕ))) (op : Opcode) : ℕ :=
  match key with
  | some cs => (cs.map fun l => l.getD (opIdx op) 0).foldr max 0
  | none => 0

mutual
/-- The separately counted arms a statement can pass, at most. -/
def costMax1 (acs : List (ℕ × List (List ℕ))) (op : Opcode) : Stmt → ℕ
  | .ite _ z n => max (costMaxW acs op z) (costMaxW acs op n)
  | .match_ x arms => keyMax (armRaw acs x.idx) op + costMaxArms acs op arms
  | _ => 0

/-- The separately counted arms a block can pass, at most. -/
def costMaxW (acs : List (ℕ × List (List ℕ))) (op : Opcode) : List Stmt → ℕ
  | [] => 0
  | s :: ss => costMax1 acs op s + costMaxW acs op ss

/-- The separately counted arms an arm of a `match` can pass, at most. -/
def costMaxArms (acs : List (ℕ × List (List ℕ))) (op : Opcode) : List (List Stmt) → ℕ
  | [] => 0
  | a :: as => max (costMaxW acs op a) (costMaxArms acs op as)
end

theorem nth_getD_le_foldr (i : ℕ) : ∀ (cs : List (List ℕ)) (k : ℕ),
    (listElementOrDefault cs k []).getD i 0 ≤ (cs.map fun l => l.getD i 0).foldr max 0
  | [], _ => by simp [listElementOrDefault]
  | c :: cs, 0 => by simp [listElementOrDefault]
  | c :: cs, k + 1 => by
    simp only [listElementOrDefault, List.map_cons, List.foldr_cons]
    exact (nth_getD_le_foldr i cs k).trans (le_max_right _ _)

section Le

variable (acs : List (ℕ × List (List ℕ))) (σ : Val) (op : Opcode)

mutual
theorem cost1_le_max : ∀ s : Stmt, cost1 acs σ s op ≤ costMax1 acs op s
  | .atom _ => Nat.zero_le _
  | .ite c z n => by
    rw [cost1, costMax1]
    split
    · exact (costW_le_max z).trans (le_max_left _ _)
    · exact (costW_le_max n).trans (le_max_right _ _)
  | .match_ x arms => by
    rw [cost1, costMax1]
    exact costArms_le_max x arms 0 (armRaw acs x.idx)
  | .call .. => Nat.zero_le _
  | .callIf .. => Nat.zero_le _
  | .dispatch .. => Nat.zero_le _
  | .ret _ => Nat.zero_le _

theorem costW_le_max : ∀ ss : List Stmt, costW acs σ ss op ≤ costMaxW acs op ss
  | [] => by rw [costW, costMaxW]; exact Nat.zero_le _
  | s :: ss => by
    rw [costW, costMaxW, Pi.add_apply]
    exact Nat.add_le_add (cost1_le_max s) (costW_le_max ss)

theorem costArms_le_max (x : V) : ∀ (arms : List (List Stmt)) (k : ℕ) (key : Option (List (List ℕ))),
    costArms acs σ x key k arms op ≤ keyMax key op + costMaxArms acs op arms
  | [], _, _ => by rw [costArms]; exact Nat.zero_le _
  | a :: as, k, key => by
    rw [costArms, costMaxArms]
    split
    · rw [Pi.add_apply]
      refine Nat.add_le_add ?_ ((costW_le_max a).trans (le_max_left _ _))
      cases key with
      | none => exact Nat.zero_le _
      | some cs => exact nth_getD_le_foldr _ cs k
    · exact (costArms_le_max x as (k + 1) key).trans
        (Nat.add_le_add_left (le_max_right _ _) _)
end

end Le

/-! ## Every opcode at once

`costMaxW` at each opcode is one walk of the block; `costMaxCW` takes the six in one walk (`C6`),
and agrees with it at each (`costMaxCW_at`). -/

/-- A count per opcode, in `opIdx`'s order. -/
structure C6 where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  c4 : ℕ
  c5 : ℕ
  deriving DecidableEq

/-- The count at an opcode. -/
def C6.at (c : C6) : Opcode → ℕ
  | .xor => c.c0
  | .mulNative => c.c1
  | .setConstant => c.c2
  | .deref => c.c3
  | .jump => c.c4
  | .keccak => c.c5

def C6.zero : C6 := ⟨0, 0, 0, 0, 0, 0⟩

def C6.max (a b : C6) : C6 :=
  ⟨Nat.max a.c0 b.c0, Nat.max a.c1 b.c1, Nat.max a.c2 b.c2, Nat.max a.c3 b.c3, Nat.max a.c4 b.c4,
    Nat.max a.c5 b.c5⟩

def C6.add (a b : C6) : C6 :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3, a.c4 + b.c4, a.c5 + b.c5⟩

/-- The counts of a list in `opIdx`'s order. -/
def C6.ofList (l : List ℕ) : C6 := ⟨l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0, l.getD 5 0⟩

theorem C6.at_zero (op : Opcode) : C6.zero.at op = 0 := by cases op <;> rfl

theorem C6.at_max (a b : C6) (op : Opcode) : (a.max b).at op = Max.max (a.at op) (b.at op) := by
  cases op <;> rfl

theorem C6.at_add (a b : C6) (op : Opcode) : (a.add b).at op = a.at op + b.at op := by
  cases op <;> rfl

theorem C6.at_ofList (l : List ℕ) (op : Opcode) : (C6.ofList l).at op = l.getD (opIdx op) 0 := by
  cases op <;> rfl

/-- `keyMax` at every opcode. -/
def keyMaxC (key : Option (List (List ℕ))) : C6 :=
  match key with
  | some cs => cs.foldr (fun l acc ↦ (C6.ofList l).max acc) C6.zero
  | none => C6.zero

theorem keyMaxC_at (key : Option (List (List ℕ))) (op : Opcode) : (keyMaxC key).at op = keyMax key op := by
  rcases key with _ | cs
  · exact C6.at_zero op
  · induction cs with
    | nil => exact C6.at_zero op
    | cons l cs ih =>
      simp only [keyMaxC, keyMax, List.foldr_cons, List.map_cons] at ih ⊢
      rw [C6.at_max, C6.at_ofList, ih]

mutual
/-- `costMax1` at every opcode. -/
def costMaxC1 (acs : List (ℕ × List (List ℕ))) : Stmt → C6
  | .ite _ z n => (costMaxCW acs z).max (costMaxCW acs n)
  | .match_ x arms => (keyMaxC (armRaw acs x.idx)).add (costMaxCArms acs arms)
  | _ => C6.zero

/-- `costMaxW` at every opcode. -/
def costMaxCW (acs : List (ℕ × List (List ℕ))) : List Stmt → C6
  | [] => C6.zero
  | s :: ss => (costMaxC1 acs s).add (costMaxCW acs ss)

/-- `costMaxArms` at every opcode. -/
def costMaxCArms (acs : List (ℕ × List (List ℕ))) : List (List Stmt) → C6
  | [] => C6.zero
  | a :: as => (costMaxCW acs a).max (costMaxCArms acs as)
end

section At

variable (acs : List (ℕ × List (List ℕ))) (op : Opcode)

mutual
theorem costMaxC1_at : ∀ s : Stmt, (costMaxC1 acs s).at op = costMax1 acs op s
  | .atom _ => C6.at_zero op
  | .ite _ z n => by rw [costMaxC1, costMax1, C6.at_max, costMaxCW_at z, costMaxCW_at n]
  | .match_ x arms => by rw [costMaxC1, costMax1, C6.at_add, keyMaxC_at, costMaxCArms_at arms]
  | .call .. => C6.at_zero op
  | .callIf .. => C6.at_zero op
  | .dispatch .. => C6.at_zero op
  | .ret _ => C6.at_zero op

theorem costMaxCW_at : ∀ ss : List Stmt, (costMaxCW acs ss).at op = costMaxW acs op ss
  | [] => C6.at_zero op
  | s :: ss => by rw [costMaxCW, costMaxW, C6.at_add, costMaxC1_at s, costMaxCW_at ss]

theorem costMaxCArms_at : ∀ arms : List (List Stmt), (costMaxCArms acs arms).at op = costMaxArms acs op arms
  | [] => C6.at_zero op
  | a :: as => by rw [costMaxCArms, costMaxArms, C6.at_max, costMaxCW_at a, costMaxCArms_at as]
end

end At

/-- **`main_loop2`'s separately counted arms, per opcode** (leanXMSS's check, inline in it): the sum
of its counted `match`es' largest arms, as `guest-cert` computes them (`Data.armMax`). -/
def xmssArmC (op : Opcode) : ℕ := Data.armMax.getD (opIdx op) 0

-- a kernel evaluation over the body of the function with counted arms (`Data.armFn`)
set_option maxRecDepth 100000 in
theorem costMaxCW_arm :
    costMaxCW (listElementOrDefault Data.cplArms Data.armFn []) (coreOf Data.armFn).body =
      C6.ofList Data.armMax := by
  decide +kernel

theorem costMaxW_xmss (op : Opcode) :
    costMaxW (listElementOrDefault Data.cplArms Data.armFn []) op (coreOf Data.armFn).body = xmssArmC op := by
  rw [← costMaxCW_at, costMaxCW_arm, C6.at_ofList]
  rfl

/-- **`cnt_le_weight_arm`'s `hC` at `xmssArmC`**: `main_loop2`'s arms within `xmssArmC`, on
every valuation. -/
theorem xmssArmC_spec : ∀ op σ bufs kids rd args rets,
    (Memory.Tree.node name% «main_loop2» σ bufs kids).Valid coreProgram rd args rets →
      costW (listElementOrDefault Data.cplArms Data.armFn []) σ (coreOf Data.armFn).body op ≤ xmssArmC op :=
  fun op σ _ _ _ _ _ _ => (costW_le_max _ σ op _).trans (costMaxW_xmss op).le

end
end LeanVM.Guest.B2C
