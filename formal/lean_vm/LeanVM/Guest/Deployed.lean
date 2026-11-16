/-
  LeanVM.Guest.Deployed

  The deployed guest's frame sizes and instruction counts, read from the back end's own tables
  (`Deployed.Data`): what the completeness budget is stated over.
-/

module

public import LeanVM.Guest.Deployed.Data
public import LeanVM.Guest.Memory
public import LeanVM.Guest.Memory.Size
public import LeanVM.Guest.Memory.Fresh
public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.CoreNames
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Backend.Complete.Count

/-!
# The deployed guest's frames and counts

The back end places the guest (`placeProgram guestTraced`) and `lake exe guest-tables` writes its
numbers by compiled function index `j` (`Deployed.Data`). From them:

* `fs f`: function `f`'s frame size, at least the header; `main`'s holds the jump table after its
  own cells (`mainFrame`). `fsN j` is `fs` by index.
* `pathMax f op`: the most instructions of opcode `op` one path through `f`'s placed code runs
  (`pmaxOf`), `main_loop2`'s separately counted arms (`Data.arms`) excluded. `cnt T op` counts, per
  instance of `T` that runs, its path's count (`pathCount`: `pathMax` and the counted arms its
  valuation picks), plus the jump table's `SET`s (`jtSets`).
* `ωArm C op f`: the weight `B1` takes, `pathMax` and, for `main_loop2`, the arms' bound `C`;
  `cnt_le_weight_arm` bounds `cnt` by it on valid trees, and `xmssArmC_spec` gives `C := xmssArmC`
  (`Data.armMax`, by the kernel).

The frames' cells `frameE` keep one candidate per cell, within the frame (`dedupC`); `walk_blockAtoms`:
a path's atoms are its function's block's (`Lift.blockAtoms`). `cntRetemp`: the counts do not see
the temporaries' values.
-/

namespace LeanVM.Guest.Deployed

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## Functions by name -/

/-- The compiled index of a core function. -/
noncomputable def idxOf (f : String) : Option ℕ := (coreProgram.indexOf? f).map (· + 1)

/-- The back end's frame size of compiled function `j` (`main`'s without the jump table). -/
def fsAt (j : ℕ) : ℕ := Data.frameSizes.getD j 0

theorem frameSizes_length : Data.frameSizes.length = fn_count% := by decide +kernel

/-- `main`'s frame: its cells and the jump table after them. -/
def mainFrame : ℕ := Data.mainCells + Data.jtSlots

/-- **The frame sizes**: the back end's, `main`'s holding the jump table, at least the header. -/
noncomputable def fs (f : String) : ℕ :=
  match coreProgram.indexOf? f with
  | some 0 => mainFrame
  | some i => max 2 (fsAt (i + 1))
  | none => 2

/-- The frame size of compiled function `j`, `fs` by index. -/
def fsN (j : ℕ) : ℕ := bif Nat.beq j 1 then mainFrame else max 2 (fsAt j)

/-- The entry pc of a function, by name. -/
noncomputable def entryOf (f : String) : ℕ :=
  match idxOf f with
  | some j => (fnOf j).entryPc
  | none => 0

/-! ## The cells of a frame -/

/-- One cell per offset, the first, within `[2, n)`. -/
def dedupC : List (ℕ × E) → List (ℕ × E)
  | [] => []
  | q :: qs => q :: (dedupC qs).filter fun q' => !(q'.1 == q.1)

/-- A frame's cells from a list of candidates. -/
def frameE (n : ℕ) (L : List (ℕ × E)) : List (ℕ × E) :=
  dedupC (L.filter fun q => Nat.ble 2 q.1 && Nat.blt q.1 n)

/-! ## Instruction counts -/

/-- An opcode's position in `Opcode`'s order. -/
def opIdx : Opcode → ℕ
  | .xor => 0
  | .mulNative => 1
  | .setConstant => 2
  | .deref => 3
  | .jump => 4
  | .keccak => 5

/-- The path maxima of compiled function `j`, by `opIdx`. -/
def pmaxOf (j : ℕ) : List ℕ := Data.pmax.getD j []

/-- The most instructions of opcode `op` one path through function `f`'s code runs (the back
end's, `Complete.pmaxP`). -/
noncomputable def pathMax (f : String) (op : Opcode) : ℕ :=
  match idxOf f with
  | some j => (pmaxOf j).getD (opIdx op) 0
  | none => 0

/-! ## The counts of a path

A `match` whose arms are counted separately (`Data.arms`) adds the count of the arm its
selector picks; the rest of a path is counted by the most any path runs (`pathMax`). -/

mutual
/-- The separately counted arms a statement's path passes, under `σ`. -/
noncomputable def cost1 (acs : List (ℕ × List (List ℕ))) (σ : Val) : Stmt → Opcode → ℕ
  | .ite c z n => if σ c = 0 then costW acs σ z else costW acs σ n
  | .match_ x arms => costArms acs σ x (Backend.Complete.armRaw acs x.idx) 0 arms
  | _ => 0

/-- The separately counted arms a block's path passes, under `σ`. -/
noncomputable def costW (acs : List (ℕ × List (List ℕ))) (σ : Val) : List Stmt → Opcode → ℕ
  | [] => 0
  | s :: ss => cost1 acs σ s + costW acs σ ss

/-- The arm `σ` picks, from arm `k` on (`walkArms`), its count if counted separately. -/
noncomputable def costArms (acs : List (ℕ × List (List ℕ))) (σ : Val) (x : V)
    (key : Option (List (List ℕ))) : ℕ → List (List Stmt) → Opcode → ℕ
  | _, [] => 0
  | k, a :: as => if σ x = ofK (addressOfIndex k) then
      (fun op ↦ match key with
        | some cs => (listElementOrDefault cs k []).getD (opIdx op) 0
        | none => 0) + costW acs σ a
    else costArms acs σ x key (k + 1) as
end

/-- **The count of function `j`'s path under `σ`**: the most a path runs, and the separately
counted arms it passes. -/
noncomputable def pathCount (j : ℕ) (σ : Val) (op : Opcode) : ℕ :=
  (pmaxOf j).getD (opIdx op) 0 + costW (listElementOrDefault Data.arms j []) σ (coreOf j).body op

/-- `pathCount`, by function name. -/
noncomputable def pathCountN (f : String) (σ : Val) (op : Opcode) : ℕ :=
  match idxOf f with
  | some j => pathCount j σ op
  | none => 0

mutual
/-- The weight of a call tree, each instance weighing `ω f σ` by its function and valuation. -/
def weightV (ω : String → Val → ℕ) : Tree → ℕ
  | .node f σ _ kids => ω f σ + weightVKids ω kids
  | .phantom .. => 0

/-- The weight of a list of call trees. -/
def weightVKids (ω : String → Val → ℕ) : List Tree → ℕ
  | [] => 0
  | k :: ks => weightV ω k + weightVKids ω ks
end

/-- The jump table's `SET`s, run before `main`. -/
def jtSets (op : Opcode) : ℕ := if op = .setConstant then Data.jtSlots else 0

/-- **The instructions of opcode `op` a run on the honest memory of `T` executes at most**: its
path's count, per instance that runs, and the jump table. -/
noncomputable def cnt (T : Tree) (op : Opcode) : ℕ := weightV (fun f σ ↦ pathCountN f σ op) T + jtSets op

/-! ## One candidate per cell -/

section Dedup

theorem mem_dedupC : ∀ {L : List (ℕ × E)} {q : ℕ × E}, q ∈ dedupC L → q ∈ L
  | [], _, h => by simp [dedupC] at h
  | x :: L, q, h => by
    simp only [dedupC, List.mem_cons, List.mem_filter] at h
    rcases h with rfl | ⟨h, -⟩
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_dedupC h)

theorem dedupC_key : ∀ {L : List (ℕ × E)} {q q' : ℕ × E}, q ∈ dedupC L → q' ∈ dedupC L →
    q.1 = q'.1 → q = q'
  | [], _, _, h, _, _ => by simp [dedupC] at h
  | x :: L, q, q', h, h', he => by
    simp only [dedupC, List.mem_cons, List.mem_filter, Bool.not_eq_true', beq_eq_false_iff_ne,
      ne_eq] at h h'
    rcases h with rfl | ⟨h, hx⟩ <;> rcases h' with rfl | ⟨h', hx'⟩
    · rfl
    · exact absurd he.symm hx'
    · exact absurd he hx
    · exact dedupC_key h h' he

/-- The candidate kept at a cell is the first at that cell. -/
theorem dedupC_first : ∀ {L1 L2 : List (ℕ × E)} {q : ℕ × E}, q ∈ dedupC (L1 ++ L2) →
    (∃ x ∈ L1, x.1 = q.1) → q ∈ L1
  | [], _, _, _, ⟨_, h, _⟩ => by simp at h
  | x :: L1, L2, q, h, ⟨y, hy, he⟩ => by
    simp only [List.cons_append, dedupC, List.mem_cons, List.mem_filter, Bool.not_eq_true',
      beq_eq_false_iff_ne, ne_eq] at h
    rcases h with rfl | ⟨h, hx⟩
    · exact List.mem_cons_self
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact absurd he.symm hx
      · exact List.mem_cons_of_mem _ (dedupC_first h ⟨y, hy, he⟩)

/-- A candidate before which every candidate at its cell is itself is kept. -/
theorem dedupC_mem : ∀ {L1 L2 : List (ℕ × E)} {q : ℕ × E}, q ∈ L1 → (∀ x ∈ L1, x.1 = q.1 → x = q) →
    q ∈ dedupC (L1 ++ L2)
  | [], _, _, h, _ => by simp at h
  | x :: L1, L2, q, h, hx => by
    simp only [List.cons_append, dedupC, List.mem_cons, List.mem_filter, Bool.not_eq_true',
      beq_eq_false_iff_ne, ne_eq]
    by_cases hxq : x = q
    · exact Or.inl hxq.symm
    · right
      rcases List.mem_cons.mp h with rfl | h
      · exact absurd rfl hxq
      · refine ⟨dedupC_mem h fun y hy ↦ hx y (List.mem_cons_of_mem _ hy), fun he ↦ hxq ?_⟩
        exact hx x List.mem_cons_self he.symm

/-- Candidates with the same cells first keep the same candidates at the other cells. -/
theorem dedupC_swap : ∀ {A A' R : List (ℕ × E)} {q : ℕ × E}, A.map Prod.fst = A'.map Prod.fst →
    q ∈ dedupC (A' ++ R) → q.1 ∉ A'.map Prod.fst → q ∈ dedupC (A ++ R)
  | [], [], _, _, _, h, _ => h
  | [], _ :: _, _, _, he, _, _ => by simp at he
  | _ :: _, [], _, _, he, _, _ => by simp at he
  | a :: A, a' :: A', R, q, he, h, hn => by
    simp only [List.map_cons, List.cons.injEq] at he
    simp only [List.cons_append, dedupC, List.mem_cons, List.mem_filter, Bool.not_eq_true',
      beq_eq_false_iff_ne, ne_eq] at h ⊢
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    rcases h with rfl | ⟨h, hx⟩
    · exact absurd rfl hn.1
    · exact Or.inr ⟨dedupC_swap he.2 h hn.2, by rw [he.1]; exact hx⟩

theorem frameE_append (n : ℕ) (L1 L2 : List (ℕ × E)) :
    frameE n (L1 ++ L2) = dedupC ((L1.filter fun q ↦ Nat.ble 2 q.1 && Nat.blt q.1 n) ++
      (L2.filter fun q ↦ Nat.ble 2 q.1 && Nat.blt q.1 n)) := by
  rw [frameE, List.filter_append]

theorem mem_frameE {n : ℕ} {L : List (ℕ × E)} {q : ℕ × E} (h : q ∈ frameE n L) :
    q ∈ L ∧ 2 ≤ q.1 ∧ q.1 < n := by
  have := mem_dedupC h
  simp only [List.mem_filter, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at this
  exact ⟨this.1, this.2⟩

end Dedup

/-! ## Functions by name -/

section Lookup

theorem indexOf?_spec {f : String} {i : ℕ} (h : coreProgram.indexOf? f = some i) :
    ∃ hi : i < coreProgram.length, coreProgram[i].name = f := by
  unfold Program.indexOf? at h
  rw [List.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hi, he, -⟩ := h
  exact ⟨hi, by simpa using he⟩

/-- Core function `j` is the first of its name. -/
theorem indexOf?_getElem {j : ℕ} (h : j < coreProgram.length) :
    coreProgram.indexOf? coreProgram[j].name = some j := by
  unfold Program.indexOf?
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨h, by simp, fun i hij ↦ ?_⟩
  simp only [beq_iff_eq]
  intro he
  have := (List.Nodup.getElem_inj_iff coreProgram_names_nodup (i := i) (j := j)
    (hi := by simp; omega) (hj := by simp; omega)).mp (by simpa using he)
  omega

theorem find?_none {f : String} (h : coreProgram.indexOf? f = none) : coreProgram.find? f = none := by
  unfold Program.indexOf? at h
  unfold Program.find?
  rw [List.findIdx?_eq_none_iff] at h
  rw [List.find?_eq_none]
  exact fun x hx ↦ by simpa using h x hx

/-- What the name of core function `i` gives: its compiled function `i + 1` and its frame size. -/
theorem fn_of_idx {f : String} {j : ℕ} (h : idxOf f = some j) :
    ∃ i, j = i + 1 ∧ ∃ hi : i < coreProgram.length, coreProgram[i].name = f ∧
      coreProgram.find? f = some coreProgram[i] ∧ coreOf j = coreProgram[i] ∧ fs f = fsN j ∧
      1 ≤ j ∧ j < nFns := by
  unfold idxOf at h
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hlt, hn⟩ := indexOf?_spec hi
  refine ⟨i, rfl, hlt, hn, by rw [← hn]; exact coreProgram_find_getElem hlt, ?_, ?_,
    by omega, by have : coreProgram.length + 1 = nFns := (by rw [coreProgram_length]; rfl); omega⟩
  · unfold coreOf; simp only [Nat.add_sub_cancel]; exact nth_eq hlt
  · unfold fs fsN
    rw [hi]
    cases i with
    | zero => rfl
    | succ i => simp

theorem two_le_fs (f : String) : 2 ≤ fs f := by
  unfold fs
  split
  · decide
  · omega
  · exact le_rfl

theorem main_idx : idxOf "main" = some 1 := by decide +kernel

theorem fs_main : fs "main" = mainFrame := by decide +kernel

theorem find_main : coreProgram.find? "main" = some Data.core0 :=
  Program.find?_of_indexOf? (j := 0) (by decide +kernel) rfl

end Lookup

/-! ## The atoms of a path -/

section Atoms

variable {σ : Val}

theorem evs_seq_mem {o k : Out} {e : Ev} (h : e ∈ (o.seq k).evs) : e ∈ o.evs ∨ e ∈ k.evs := by
  rcases o with es | ⟨es, vs⟩ | _ <;> rcases k with es' | ⟨es', vs'⟩ | _ <;>
    simp_all [Out.seq, Out.pre, Out.evs]

theorem evs_pre_mem {o : Out} {es : List Ev} {e : Ev} (h : e ∈ (o.pre es).evs) : e ∈ es ∨ e ∈ o.evs := by
  rcases o with es' | ⟨es', vs⟩ | _ <;> simp_all [Out.pre, Out.evs]

theorem pick_noAtom {x : V} {args rets : List V} : ∀ (gs : List String) (j : ℕ) {a : Atom},
    Ev.atom a ∉ (pick σ x args rets j gs).evs
  | [], _, a => by simp [pick, Out.evs]
  | g :: gs, j, a => by
    unfold pick
    split_ifs
    · simp [Out.evs]
    · exact pick_noAtom gs (j + 1)

mutual
/-- **A statement's path's atoms are its atoms.** -/
theorem walk1_blockAtoms : ∀ (s : Stmt) {a : Atom}, Ev.atom a ∈ (walk1 σ s).evs → a ∈ Lift.stmtAtoms s
  | .atom b, a, h => by
    simp only [walk1, Out.evs, List.mem_singleton, Ev.atom.injEq] at h
    simp [Lift.stmtAtoms, h]
  | .ite c z m, a, h => by
    rw [walk1] at h
    rcases evs_pre_mem h with h | h
    · simp at h
    · simp only [Lift.stmtAtoms, List.mem_append]
      split_ifs at h
      · exact Or.inl (walk_blockAtoms z h)
      · exact Or.inr (walk_blockAtoms m h)
  | .match_ x arms, a, h => by
    rw [walk1] at h
    exact walkArms_blockAtoms x arms 0 h
  | .call .., a, h => by simp [walk1, Out.evs] at h
  | .callIf c f args, a, h => by
    rw [walk1] at h
    split_ifs at h <;> simp [Out.evs] at h
  | .dispatch x gs args rets, a, h => by
    rw [walk1] at h
    exact absurd h (pick_noAtom gs 0)
  | .ret _, a, h => by simp [walk1, Out.evs] at h

/-- **A block's path's atoms are its atoms.** -/
theorem walk_blockAtoms : ∀ (ss : List Stmt) {a : Atom}, Ev.atom a ∈ (walk σ ss).evs →
    a ∈ Lift.blockAtoms ss
  | [], a, h => by simp [walk, Out.evs] at h
  | s :: ss, a, h => by
    rw [walk] at h
    simp only [Lift.blockAtoms, List.mem_append]
    rcases evs_seq_mem h with h | h
    · exact Or.inl (walk1_blockAtoms s h)
    · exact Or.inr (walk_blockAtoms ss h)

theorem walkArms_blockAtoms (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) {a : Atom},
    Ev.atom a ∈ (walkArms σ x j arms).evs → a ∈ Lift.armsAtoms arms
  | [], _, a, h => by simp [walkArms, Out.evs] at h
  | b :: bs, j, a, h => by
    unfold walkArms at h
    simp only [Lift.armsAtoms, List.mem_append]
    split_ifs at h
    · exact Or.inl (walk_blockAtoms b h)
    · exact Or.inr (walkArms_blockAtoms x bs (j + 1) h)
end

end Atoms

/-! ## Counts as weights

`cnt_le_weight_valid`: `cnt t op ≤ t.weight (ω op) + jtSets op` (`mainComplete_of`'s and
`ea_mainComplete`'s `hcnt`, at `jt := jtSets`), whenever each valid instance's path count is
within its function's weight `ω op f`. -/

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
    costArms [] σ x (Backend.Complete.armRaw [] x.idx) k arms = 0
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

private theorem listElementOrDefault_of_le {α : Type} :
    ∀ {l : List α} {n : ℕ} {d : α}, l.length ≤ n → listElementOrDefault l n d = d
  | [], _, _, _ => rfl
  | _ :: _, 0, _, h => absurd h (by simp)
  | _ :: l, n + 1, d, h => listElementOrDefault_of_le (l := l) (n := n) (d := d) (by simpa using h)

/-- Only `main_loop2` (function `Data.armFn`, leanXMSS's check inline) counts arms separately. -/
theorem arms_only : ∀ j, j ≠ Data.armFn → listElementOrDefault Data.arms j [] = [] := by
  intro j hj
  by_cases hl : j < Data.arms.length
  · have h : (List.range Data.arms.length).all
        (fun j ↦ Nat.beq j Data.armFn
            || (listElementOrDefault Data.arms j []).isEmpty) = true := by decide +kernel
    have := List.all_eq_true.mp h j (List.mem_range.mpr hl)
    simp only [Bool.or_eq_true, List.isEmpty_iff] at this
    rcases this with h1 | h1
    · exact absurd (Nat.eq_of_beq_eq_true h1) hj
    · exact h1
  · exact listElementOrDefault_of_le (by omega)

theorem coreOf_armFn_name : (coreOf Data.armFn).name = name% «main_loop2» := by decide +kernel

/-- **A valid instance's path count within its weight**, given `main_loop2`'s arms within
`C` on its valid instances. -/
theorem pathCountN_le_arm (C : Opcode → ℕ)
    (hC : ∀ op σ bufs kids rd args rets,
      (Memory.Tree.node name% «main_loop2» σ bufs kids).Valid coreProgram rd args rets →
        costW (listElementOrDefault Data.arms Data.armFn []) σ (coreOf Data.armFn).body op ≤ C op)
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
    · rw [arms_only j h37, costW_nil, Pi.zero_apply]
      omega
  · exact Nat.zero_le _

/-- **The counts within the weights `ωArm C`** on valid trees. -/
theorem cnt_le_weight_arm (C : Opcode → ℕ)
    (hC : ∀ op σ bufs kids rd args rets,
      (Memory.Tree.node name% «main_loop2» σ bufs kids).Valid coreProgram rd args rets →
        costW (listElementOrDefault Data.arms Data.armFn []) σ (coreOf Data.armFn).body op ≤ C op) :
    ∀ (rd : Reader) (t : Tree), t.Valid coreProgram rd [] [] → ∀ op,
      cnt t op ≤ t.weight (ωArm C op) + jtSets op :=
  cnt_le_weight_valid (ωArm C) fun op f σ bufs kids rd args rets hv ↦
    pathCountN_le_arm C hC op f σ bufs kids rd args rets hv

/-! ## `main_loop2`'s arms, bounded

`costW acs σ ss op` adds, along the path `σ` takes through `ss`, the count of each separately
counted arm it passes. Whatever the path, it is at most `costMaxW acs op ss`: an `ite` its larger
side, a `match` its table's largest arm and its larger arm's own (`costMaxArms`). On
`main_loop2`'s body (`Data.armFn`) this is `xmssArmC op`, the values `guest-tables` computes
(`Data.armMax`; by `decide +kernel`, every opcode in one walk), so `cnt_le_weight_arm` holds at
`C := xmssArmC`. -/

/-- A counted `match`'s largest arm at `op`, `0` if not counted. -/
def keyMax (key : Option (List (List ℕ))) (op : Opcode) : ℕ :=
  match key with
  | some cs => (cs.map fun l => l.getD (opIdx op) 0).foldr max 0
  | none => 0

mutual
/-- The separately counted arms a statement can pass, at most. -/
def costMax1 (acs : List (ℕ × List (List ℕ))) (op : Opcode) : Stmt → ℕ
  | .ite _ z n => max (costMaxW acs op z) (costMaxW acs op n)
  | .match_ x arms => keyMax (Backend.Complete.armRaw acs x.idx) op + costMaxArms acs op arms
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
    exact costArms_le_max x arms 0 (Backend.Complete.armRaw acs x.idx)
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

/-! ### Every opcode at once

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
  | .match_ x arms => (keyMaxC (Backend.Complete.armRaw acs x.idx)).add (costMaxCArms acs arms)
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
of its counted `match`es' largest arms, as `guest-tables` computes them (`Data.armMax`). -/
def xmssArmC (op : Opcode) : ℕ := Data.armMax.getD (opIdx op) 0

-- a kernel evaluation over the body of the function with counted arms (`Data.armFn`)
set_option maxRecDepth 100000 in
theorem costMaxCW_arm :
    costMaxCW (listElementOrDefault Data.arms Data.armFn []) (coreOf Data.armFn).body =
      C6.ofList Data.armMax := by
  decide +kernel

theorem costMaxW_xmss (op : Opcode) :
    costMaxW (listElementOrDefault Data.arms Data.armFn []) op (coreOf Data.armFn).body = xmssArmC op := by
  rw [← costMaxCW_at, costMaxCW_arm, C6.at_ofList]
  rfl

/-- **`cnt_le_weight_arm`'s `hC` at `xmssArmC`**: `main_loop2`'s arms within `xmssArmC`, on
every valuation. -/
theorem xmssArmC_spec : ∀ op σ bufs kids rd args rets,
    (Memory.Tree.node name% «main_loop2» σ bufs kids).Valid coreProgram rd args rets →
      costW (listElementOrDefault Data.arms Data.armFn []) σ (coreOf Data.armFn).body op ≤ xmssArmC op :=
  fun op σ _ _ _ _ _ _ => (costW_le_max _ σ op _).trans (costMaxW_xmss op).le

/-! ## The counts do not see the temporaries -/

mutual
theorem costW_congr (acs : List (ℕ × List (List ℕ))) {σ σ' : Val} :
    ∀ ss : List Stmt, (∀ v ∈ Stmt.usesList ss, σ' v = σ v) → costW acs σ' ss = costW acs σ ss
  | [], _ => by rw [costW, costW]
  | s :: ss, h => by
    rw [costW, costW, cost1_congr acs s (fun v hv ↦ h v (by rw [Stmt.usesList]; exact List.mem_append_left _ hv)),
      costW_congr acs ss (fun v hv ↦ h v (by rw [Stmt.usesList]; exact List.mem_append_right _ hv))]

theorem cost1_congr (acs : List (ℕ × List (List ℕ))) {σ σ' : Val} :
    ∀ s : Stmt, (∀ v ∈ Stmt.uses s, σ' v = σ v) → cost1 acs σ' s = cost1 acs σ s
  | .ite c z n, h => by
    rw [cost1, cost1, h c (by rw [Stmt.uses]; exact List.mem_cons_self),
      costW_congr acs z (fun v hv ↦ h v (by rw [Stmt.uses]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hv))),
      costW_congr acs n (fun v hv ↦ h v (by rw [Stmt.uses]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hv)))]
  | .match_ x arms, h => by
    rw [cost1, cost1]
    exact costArms_congr acs x _ 0 arms (h x (by rw [Stmt.uses]; exact List.mem_cons_self))
      (fun v hv ↦ h v (by rw [Stmt.uses]; exact List.mem_cons_of_mem _ hv))
  | .atom _, _ => rfl
  | .call .., _ => rfl
  | .callIf .., _ => rfl
  | .dispatch .., _ => rfl
  | .ret _, _ => rfl

theorem costArms_congr (acs : List (ℕ × List (List ℕ))) {σ σ' : Val} (x : V) (key : Option (List (List ℕ))) :
    ∀ (k : ℕ) (arms : List (List Stmt)), σ' x = σ x → (∀ v ∈ Stmt.usesArms arms, σ' v = σ v) →
      costArms acs σ' x key k arms = costArms acs σ x key k arms
  | _, [], _, _ => by rw [costArms, costArms]
  | k, a :: as, hx, h => by
    rw [costArms, costArms, hx,
      costW_congr acs a (fun v hv ↦ h v (by rw [Stmt.usesArms]; exact List.mem_append_left _ hv)),
      costArms_congr acs x key (k + 1) as hx
        (fun v hv ↦ h v (by rw [Stmt.usesArms]; exact List.mem_append_right _ hv))]
end

/-- A path's count does not see the temporaries' values. -/
theorem pathCountN_retemp (hfr : coreProgram.Fresh) (ν : ℕ → String → Val → V → E) (fp : ℕ) (f : String)
    (σ : Val) (op : Opcode) :
    pathCountN f (retempVal coreProgram ν fp f σ) op = pathCountN f σ op := by
  unfold pathCountN
  split
  · rename_i j hj
    obtain ⟨i, rfl, hi, -, hfind, hcore, -⟩ := fn_of_idx hj
    unfold pathCount
    rw [hcore, costW_congr _ _ (fun v hv ↦ retempVal_uses hfr hfind hv)]
  · rfl

mutual
theorem weightV_retemp (hfr : coreProgram.Fresh) (ν : ℕ → String → Val → V → E) (op : Opcode) :
    ∀ (t : Tree) (fp : ℕ), weightV (fun f σ ↦ pathCountN f σ op) (t.retemp coreProgram fs ν fp) =
      weightV (fun f σ ↦ pathCountN f σ op) t
  | .node f σ bufs kids, fp => by
      rw [retemp_node, weightV, weightV, pathCountN_retemp hfr, weightVKids_retempKids hfr ν op kids _
        (by rw [length_kidPos, List.length_map])]
  | .phantom .., fp => by rw [retemp_phantom]

theorem weightVKids_retempKids (hfr : coreProgram.Fresh) (ν : ℕ → String → Val → V → E) (op : Opcode) :
    ∀ (ks : List Tree) (ps : List ℕ), ps.length = ks.length →
      weightVKids (fun f σ ↦ pathCountN f σ op) (Tree.retempKids coreProgram fs ν ps ks) =
        weightVKids (fun f σ ↦ pathCountN f σ op) ks
  | [], _, _ => by rw [retempKids_nil]
  | _ :: _, [], h => absurd h (by simp)
  | k :: ks, p :: ps, h => by
      rw [retempKids_cons, weightVKids, weightVKids, weightV_retemp hfr ν op k p,
        weightVKids_retempKids hfr ν op ks ps (by simpa using h)]
end

/-- **The instruction counts do not see the temporaries' values** (`End.CntRetemp`). -/
theorem cntRetemp (hfr : coreProgram.Fresh) :
    ∀ (ν : ℕ → String → Val → V → E) (t : Tree), cnt (t.retemp coreProgram fs ν 0) = cnt t := by
  intro ν t
  funext op
  simp only [cnt, weightV_retemp hfr]

end
end LeanVM.Guest.Deployed
