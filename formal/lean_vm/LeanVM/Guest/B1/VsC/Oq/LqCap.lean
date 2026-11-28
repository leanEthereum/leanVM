/-
  LeanVM.Guest.B1.VsC.Oq.LqCap

  The cap and flags `levelHints` builds are honest when the phase's openings climb to the root and
  agree wherever they meet.
-/

module

public import LeanVM.Guest.B1.VsC.Oq.LqHints
public import LeanVM.Guest.Child.Collision
public import LeanVM.Guest.WithHashBridge
public import LeanVM.Guest.B1.Merkle.Climb

/-!
# `level_queries`' honest cap (`lqCapHonest`)

`levelHints`' cap is a `foldl` of `set!`s over the phase's cap steps (each step's node, then its
sibling), then the root at `1`; its flags a `foldl` of `set!`s of `1` at each cap step's parent.

* `setAll`: a `foldl` of `set!`s. One whose writes to an index all carry one value, one at least,
  leaves that value there (`getElem?_setAll`); one with no write there leaves the initial value
  (`getElem?_setAll_of_not`).
* `climbSteps_opening`: an opening's climb steps are its node and sibling at each level, at
  `merkleHeapIndex` (`capStep`), its root `Limits.climbTo` at the opening's position.
* A cap step's two writes are what its opening gives the node and its sibling
  (`Limits.OpeningGivesNode`, `capWrites_gives`), so `Limits.OpeningsAgree` makes the writes to one
  index agree (`capNodes_node`, `capNodes_sibling`).
* A flag is set exactly where some climb passes (`capFlags_one`, `capFlags_zero`), so an unset
  flag's children are unset.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.B1 LeanVM.Guest.Value LeanVM.Guest.Child
open LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## A `foldl` of `set!`s -/

section SetAll

variable {α : Type}

/-- The writes `ws` applied in order by `set!`. -/
def setAll (a : Array α) (ws : List (ℕ × α)) : Array α := ws.foldl (fun a p => a.set! p.1 p.2) a

theorem setAll_cons (a : Array α) (p : ℕ × α) (ws : List (ℕ × α)) :
    setAll a (p :: ws) = setAll (a.set! p.1 p.2) ws := rfl

theorem size_setAll : ∀ (a : Array α) (ws : List (ℕ × α)), (setAll a ws).size = a.size
  | _, [] => rfl
  | a, p :: ws => by rw [setAll_cons, size_setAll]; simp

/-- **No write to `i`** leaves `i`'s value. -/
theorem getElem?_setAll_of_not (i : ℕ) : ∀ (a : Array α) (ws : List (ℕ × α)), (∀ p ∈ ws, p.1 ≠ i) →
    (setAll a ws)[i]? = a[i]?
  | _, [], _ => rfl
  | a, p :: ws, h => by
    rw [setAll_cons, getElem?_setAll_of_not i _ ws fun q hq => h q (List.mem_cons_of_mem _ hq)]
    have hp := h p List.mem_cons_self
    simp [Array.set!, hp]

/-- **Writes to `i` that all carry `v`**, one at least, leave `v` there. -/
theorem getElem?_setAll (i : ℕ) (v : α) : ∀ (a : Array α) (ws : List (ℕ × α)), i < a.size →
    (∀ p ∈ ws, p.1 = i → p.2 = v) → (∃ p ∈ ws, p.1 = i) → (setAll a ws)[i]? = some v
  | _, [], _, _, ⟨_, hp, _⟩ => absurd hp List.not_mem_nil
  | a, p :: ws, hi, hall, hex => by
    rw [setAll_cons]
    by_cases h : ∃ q ∈ ws, q.1 = i
    · exact getElem?_setAll i v _ ws (by simpa [Array.set!] using hi)
        (fun q hq => hall q (List.mem_cons_of_mem _ hq)) h
    · have hp : p.1 = i := by
        obtain ⟨q, hq, hqi⟩ := hex
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hqi
        · exact absurd ⟨q, hq, hqi⟩ h
      have hv := hall p List.mem_cons_self hp
      rw [getElem?_setAll_of_not i _ ws fun q hq hqi => h ⟨q, hq, hqi⟩]
      obtain ⟨p1, p2⟩ := p
      dsimp only at hp hv
      subst hp hv
      simp [Array.set!, hi]

theorem foldl_set_eq {β : Type} (f : β → ℕ) (g : β → α) : ∀ (l : List β) (a : Array α),
    l.foldl (fun a x => a.set! (f x) (g x)) a = setAll a (l.map fun x => (f x, g x))
  | [], _ => rfl
  | _ :: l, _ => foldl_set_eq f g l _

theorem foldl_set2_eq {β : Type} (f f' : β → ℕ) (g g' : β → α) : ∀ (l : List β) (a : Array α),
    l.foldl (fun a x => (a.set! (f x) (g x)).set! (f' x) (g' x)) a =
      setAll a (l.flatMap fun x => [(f x, g x), (f' x, g' x)])
  | [], _ => rfl
  | _ :: l, _ => by
    rw [List.foldl_cons, foldl_set2_eq f f' g g' l, List.flatMap_cons]
    rfl

end SetAll

/-! ## Heap indices -/

theorem xor_one_eq (n : ℕ) : n ^^^ 1 = 2 * (n / 2) + (1 - n % 2) := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.testBit_xor]
  rcases i with _ | i
  · rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
      simp [Nat.testBit_zero, h]
  · rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    have : (2 * (n / 2) + (1 - n % 2)) / 2 = n / 2 := by omega
    rw [this]
    simp

theorem mhi_succ {D q l : ℕ} (hl : l < D) :
    Limits.merkleHeapIndex D q l = 2 * Limits.merkleHeapIndex D q (l + 1) + q / 2 ^ l % 2 := by
  unfold Limits.merkleHeapIndex
  have h2 : 2 ^ (D - l) = 2 * 2 ^ (D - (l + 1)) := by
    rw [← pow_succ']
    congr 1
    omega
  have hdiv : q / 2 ^ (l + 1) = q / 2 ^ l / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [h2, hdiv]
  generalize q / 2 ^ l = x
  generalize 2 ^ (D - (l + 1)) = e
  omega

theorem mhi_half {D q l : ℕ} (hl : l < D) :
    Limits.merkleHeapIndex D q l / 2 = Limits.merkleHeapIndex D q (l + 1) := by
  rw [mhi_succ hl]
  generalize q / 2 ^ l = x
  generalize Limits.merkleHeapIndex D q (l + 1) = m
  omega

theorem two_le_mhi {D q l : ℕ} (hl : l < D) : 2 ≤ Limits.merkleHeapIndex D q l := by
  unfold Limits.merkleHeapIndex
  have : 2 ^ 1 ≤ 2 ^ (D - l) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [pow_one] at this
  exact le_trans this (Nat.le_add_right _ _)

theorem mhi_lt {D q l cd : ℕ} (hq : q < 2 ^ D) (hl : l ≤ D) (hcd : D - l ≤ cd) :
    Limits.merkleHeapIndex D q l < 2 * 2 ^ cd := by
  unfold Limits.merkleHeapIndex
  have h1 := div_pow_lt hq hl
  have h2 : 2 ^ (D - l) ≤ 2 ^ cd := Nat.pow_le_pow_right (by norm_num) hcd
  omega

theorem mhi_depth {D q : ℕ} (hq : q < 2 ^ D) : Limits.merkleHeapIndex D q D = 1 := by
  rw [Limits.merkleHeapIndex, Nat.sub_self, pow_zero, Nat.div_eq_of_lt hq]

theorem heap_div {D q l : ℕ} (hl : l ≤ D) : (2 ^ D + q) / 2 ^ l = Limits.merkleHeapIndex D q l := by
  unfold Limits.merkleHeapIndex
  have : 2 ^ D = 2 ^ (D - l) * 2 ^ l := by rw [← pow_add, Nat.sub_add_cancel hl]
  rw [this, add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos l), add_comm]

theorem heap_parity {D q l : ℕ} (hl : l < D) : (2 ^ D + q) / 2 ^ l % 2 = q / 2 ^ l % 2 := by
  rw [heap_div hl.le, mhi_succ hl]
  generalize q / 2 ^ l = x
  generalize Limits.merkleHeapIndex D q (l + 1) = m
  omega

/-- A node's sibling is its index with the low bit flipped. -/
theorem xor_sibling {D q l : ℕ} (hl : l < D) :
    Limits.merkleHeapIndex D q l ^^^ 1 = Limits.siblingHeapIndex D q l := by
  rw [xor_one_eq, Limits.siblingHeapIndex, mhi_succ hl]
  have hbit : (!q.testBit l).toNat = 1 - q / 2 ^ l % 2 := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (q / 2 ^ l) with h | h <;> simp [h]
  rw [hbit]
  generalize q / 2 ^ l = x
  generalize Limits.merkleHeapIndex D q (l + 1) = m
  omega

/-! ## Climbs -/

theorem climbD_eq_climbTo (x : Digest) (q : ℕ) (p : List Digest) : climbD x q p = Limits.climbTo x q p :=
  (Limits.climbTo_eq_withHash x q p).symm

theorem climbTo_pos_congr : ∀ (path : List Digest) (node : Digest) (a b : ℕ),
    (∀ l < path.length, a / 2 ^ l % 2 = b / 2 ^ l % 2) →
    Limits.climbTo node a path = Limits.climbTo node b path
  | [], _, _, _, _ => rfl
  | s :: ss, node, a, b, h => by
    have h0 : a % 2 = b % 2 := by simpa using h 0 (by simp)
    rw [climbTo_cons, climbTo_cons, h0]
    refine climbTo_pos_congr ss _ (a / 2) (b / 2) fun l hl => ?_
    have := h (l + 1) (by simp only [List.length_cons]; omega)
    rwa [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at this

/-- **A climb's steps**: per level, the node's index, the node and its sibling; and the root. -/
theorem climbSteps_eq : ∀ (path : List Digest) (idx : ℕ) (node : Digest),
    Hints.climbSteps idx node path =
      ((List.range path.length).map fun l =>
        (idx / 2 ^ l, Limits.climbTo node idx (path.take l), path.getD l default),
        Limits.climbTo node idx path)
  | [], _, _ => rfl
  | s :: ss, idx, node => by
    have hpar : (if idx % 2 = 0 then keccak256 (digestBytes node ++ digestBytes s)
        else keccak256 (digestBytes s ++ digestBytes node)) =
        keccak256 (if idx % 2 = 0 then digestBytes node ++ digestBytes s
          else digestBytes s ++ digestBytes node) := by
      split <;> rfl
    simp only [Hints.climbSteps, climbSteps_eq ss, hpar]
    refine Prod.ext ?_ ?_
    · simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      refine List.cons_eq_cons.mpr ⟨by simp [climbTo_nil], ?_⟩
      refine List.map_congr_left fun l _ => ?_
      simp only [Function.comp_apply, List.take_succ_cons, climbTo_cons, List.getD_cons_succ, pow_succ',
        Nat.div_div_eq_div_mul]
    · simp only [climbTo_cons]

/-- An opening's climb step at `level`: the node's heap index, the node, its sibling. -/
def capStep (D : ℕ) (o : Opening) (l : ℕ) : ℕ × Digest × Digest :=
  (Limits.merkleHeapIndex D o.leafIndex l,
    Limits.climbTo (merkleLeafDigest o.leaf) o.leafIndex (o.path.take l), o.path.getD l default)

theorem climbSteps_opening {D : ℕ} {o : Opening} (hlen : o.path.length = D) :
    Hints.climbSteps (2 ^ D + o.leafIndex) (merkleLeafDigest o.leaf) o.path =
      ((List.range D).map (capStep D o), Limits.climbTo (merkleLeafDigest o.leaf) o.leafIndex o.path) := by
  have hpos : ∀ p : List Digest, p.length ≤ D →
      Limits.climbTo (merkleLeafDigest o.leaf) (2 ^ D + o.leafIndex) p =
        Limits.climbTo (merkleLeafDigest o.leaf) o.leafIndex p := fun p hp =>
    climbTo_pos_congr p _ _ _ fun l hl => heap_parity (by omega)
  rw [climbSteps_eq, hlen]
  refine Prod.ext ?_ (hpos _ (le_of_eq hlen))
  refine List.map_congr_left fun l hl => ?_
  have hl' := List.mem_range.mp hl
  simp only [capStep, heap_div hl'.le]
  rw [hpos (o.path.take l) (by rw [List.length_take]; omega)]

/-! ## The cap and the flags `levelHints` builds -/

section Cap

variable (D : ℕ) (phase : List Opening)

/-- A phase's cap steps, as `levelHints` takes them. -/
def capSteps : List (ℕ × Digest × Digest) :=
  phase.flatMap fun o => (Hints.climbSteps (2 ^ D + o.leafIndex) (merkleLeafDigest o.leaf) o.path).1.drop
    (D - Hints.capDepthOf phase.length D)

/-- The cap steps' writes: each node, then its sibling. -/
def capWrites : List (ℕ × Digest) := (capSteps D phase).flatMap fun s => [(s.1, s.2.1), (s.1 ^^^ 1, s.2.2)]

/-- The roots' writes, at `1`. -/
def capRoots : List (ℕ × Digest) :=
  phase.map fun o => (1, (Hints.climbSteps (2 ^ D + o.leafIndex) (merkleLeafDigest o.leaf) o.path).2)

/-- The cap's nodes. -/
def capNodes : Array Digest :=
  setAll (setAll (Array.replicate (2 * 2 ^ Hints.capDepthOf phase.length D) (Vector.replicate 4 0))
    (capWrites D phase)) (capRoots D phase)

/-- The flags: `1` at each cap step's parent. -/
def capFlags : Array E :=
  setAll (Array.replicate (2 ^ Hints.capDepthOf phase.length D) 0) ((capSteps D phase).map fun s => (s.1 / 2, 1))

theorem lqCapW_eq : lqCapW D phase.length phase = (capNodes D phase).toList.flatMap Hints.digestCells := by
  unfold lqCapW levelCapPushes capNodes capWrites capRoots capSteps
  simp only [List.headD_cons, foldl_set2_eq, List.foldl_map, flatMap_map']
  congr 1
  rw [← foldl_set_eq]

theorem lqFlW_eq : lqFlW D phase.length phase = (capFlags D phase).toList := by
  unfold lqFlW levelCapPushes capFlags capSteps
  simp only [List.getD_cons_succ, List.getD_cons_zero, flatMap_map']
  rw [← foldl_set_eq]

end Cap

section Phase

variable {D cd : ℕ} {phase : List Opening} {root : Digest}
  (hcd : Hints.capDepthOf phase.length D = cd) (hcdD : cd ≤ D)
  (hph : ∀ o ∈ phase, o.leafIndex < 2 ^ D ∧ o.path.length = D)

include hcd hph in
theorem mem_capSteps {s : ℕ × Digest × Digest} :
    s ∈ capSteps D phase ↔ ∃ o ∈ phase, ∃ l, D - cd ≤ l ∧ l < D ∧ s = capStep D o l := by
  simp only [capSteps, hcd, List.mem_flatMap]
  constructor
  · rintro ⟨o, ho, hs⟩
    rw [climbSteps_opening (hph o ho).2, ← List.map_drop, List.mem_map] at hs
    obtain ⟨l, hl, rfl⟩ := hs
    obtain ⟨j, hj, hjl⟩ := List.mem_drop_iff_getElem.mp hl
    rw [List.getElem_range] at hjl
    subst hjl
    simp only [List.length_range] at hj
    exact ⟨o, ho, D - cd + j, by omega, by omega, rfl⟩
  · rintro ⟨o, ho, l, hl1, hl2, rfl⟩
    refine ⟨o, ho, ?_⟩
    rw [climbSteps_opening (hph o ho).2, ← List.map_drop]
    refine List.mem_map_of_mem ?_
    rw [List.mem_drop_iff_getElem]
    exact ⟨l - (D - cd), by simp only [List.length_range]; omega, by simp only [List.getElem_range]; omega⟩

include hcd hph in
/-- **A cap write is what an opening gives its node.** -/
theorem capWrites_gives {p : ℕ × Digest} (hp : p ∈ capWrites D phase) :
    ∃ o ∈ phase, Limits.OpeningGivesNode D (o.leafIndex, o) p.1 p.2 := by
  simp only [capWrites, List.mem_flatMap] at hp
  obtain ⟨s, hs, hp⟩ := hp
  obtain ⟨o, ho, l, -, hl, rfl⟩ := (mem_capSteps hcd hph).mp hs
  refine ⟨o, ho, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact Or.inl ⟨l, hl.le, rfl, rfl⟩
  · exact Or.inr ⟨l, hl, xor_sibling hl, rfl⟩

variable (hag : Limits.OpeningsAgree D (phase.map fun o => (o.leafIndex, o)))

include hcd hph hag in
theorem capWrites_agree {i : ℕ} {v : Digest} (hiv : (i, v) ∈ capWrites D phase) :
    ∀ p ∈ capWrites D phase, p.1 = i → p.2 = v := by
  intro p hp hpi
  obtain ⟨a, ha, h1⟩ := capWrites_gives hcd hph hp
  obtain ⟨b, hb, h2⟩ := capWrites_gives hcd hph hiv
  rw [hpi] at h1
  exact hag _ (List.mem_map_of_mem ha) _ (List.mem_map_of_mem hb) i p.2 v h1 h2

theorem size_capNodes : (capNodes D phase).size = 2 * 2 ^ Hints.capDepthOf phase.length D := by
  simp [capNodes, size_setAll]

theorem size_capFlags : (capFlags D phase).size = 2 ^ Hints.capDepthOf phase.length D := by
  simp [capFlags, size_setAll]

include hcd in
theorem capNodes_of_ne {i : ℕ} (hi : i ≠ 1) :
    (capNodes D phase)[i]? =
      (setAll (Array.replicate (2 * 2 ^ cd) (Vector.replicate 4 0)) (capWrites D phase))[i]? := by
  rw [capNodes, hcd]
  refine getElem?_setAll_of_not i _ _ fun p hp => ?_
  simp only [capRoots, List.mem_map] at hp
  obtain ⟨o, -, rfl⟩ := hp
  exact fun h => hi h.symm

include hcd hph hag in
theorem capNodesA_write {i : ℕ} {v : Digest} (hiv : (i, v) ∈ capWrites D phase) (hi : i < 2 * 2 ^ cd) :
    (setAll (Array.replicate (2 * 2 ^ cd) (Vector.replicate 4 0)) (capWrites D phase))[i]? = some v :=
  getElem?_setAll i v _ _ (by simpa using hi) (capWrites_agree hcd hph hag hiv) ⟨_, hiv, rfl⟩

include hcd hcdD hph hag in
/-- **A cap step's node** is its climb's. -/
theorem capNodes_node {o : Opening} (ho : o ∈ phase) {l : ℕ} (hl1 : D - cd ≤ l) (hl2 : l < D) :
    (capNodes D phase)[Limits.merkleHeapIndex D o.leafIndex l]? =
      some (Limits.climbTo (merkleLeafDigest o.leaf) o.leafIndex (o.path.take l)) := by
  rw [capNodes_of_ne hcd (by have := two_le_mhi (q := o.leafIndex) hl2; omega)]
  have hs : capStep D o l ∈ capSteps D phase := (mem_capSteps hcd hph).mpr ⟨o, ho, l, hl1, hl2, rfl⟩
  refine capNodesA_write hcd hph hag ?_ (mhi_lt (hph o ho).1 hl2.le (by omega))
  simp only [capWrites, List.mem_flatMap]
  exact ⟨_, hs, by simp [capStep]⟩

include hcd hcdD hph hag in
/-- **A cap step's sibling** is its path's. -/
theorem capNodes_sibling {o : Opening} (ho : o ∈ phase) {l : ℕ} (hl1 : D - cd ≤ l) (hl2 : l < D) :
    (capNodes D phase)[Limits.merkleHeapIndex D o.leafIndex l ^^^ 1]? = some (o.path.getD l default) := by
  have h2 := two_le_mhi (q := o.leafIndex) hl2
  have hlt := mhi_lt (hph o ho).1 hl2.le (show D - l ≤ cd by omega)
  rw [xor_one_eq]
  rw [capNodes_of_ne hcd (by omega)]
  have hs : capStep D o l ∈ capSteps D phase := (mem_capSteps hcd hph).mpr ⟨o, ho, l, hl1, hl2, rfl⟩
  refine capNodesA_write hcd hph hag ?_ (by omega)
  simp only [capWrites, List.mem_flatMap]
  exact ⟨_, hs, by simp [capStep, xor_one_eq]⟩

variable (hroot : ∀ o ∈ phase, Limits.climbTo (merkleLeafDigest o.leaf) o.leafIndex o.path = root)

include hph hroot in
/-- **The cap's root** is the phase's. -/
theorem capNodes_one (hne : phase ≠ []) : (capNodes D phase)[1]? = some root := by
  rw [capNodes]
  refine getElem?_setAll 1 root _ _ ?_ ?_ ?_
  · rw [size_setAll, Array.size_replicate]
    have := Nat.one_le_two_pow (n := Hints.capDepthOf phase.length D)
    omega
  · intro p hp _
    simp only [capRoots, List.mem_map] at hp
    obtain ⟨o, ho, rfl⟩ := hp
    rw [climbSteps_opening (hph o ho).2]
    exact hroot o ho
  · obtain ⟨o, os, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact ⟨_, List.mem_map_of_mem List.mem_cons_self, rfl⟩

include hcd hcdD hph hag hroot in
/-- **A climb's node at a level of the cap**, the root's included. -/
theorem capNodes_climb {o : Opening} (ho : o ∈ phase) {l : ℕ} (hl1 : D - cd ≤ l) (hl2 : l ≤ D) :
    (capNodes D phase)[Limits.merkleHeapIndex D o.leafIndex l]? =
      some (Limits.climbTo (merkleLeafDigest o.leaf) o.leafIndex (o.path.take l)) := by
  rcases Nat.lt_or_ge l D with h | h
  · exact capNodes_node hcd hcdD hph hag ho hl1 h
  · have hlD : l = D := by omega
    subst hlD
    rw [mhi_depth (hph o ho).1, List.take_of_length_le (le_of_eq (hph o ho).2), hroot o ho]
    exact capNodes_one hph hroot (List.ne_nil_of_mem ho)

include hcd hph in
/-- **A flag a climb passes is set.** -/
theorem capFlags_one {o : Opening} (ho : o ∈ phase) {l : ℕ} (hl1 : D - cd ≤ l) (hl2 : l < D) :
    (capFlags D phase)[Limits.merkleHeapIndex D o.leafIndex (l + 1)]? = some 1 := by
  have hs : capStep D o l ∈ capSteps D phase := (mem_capSteps hcd hph).mpr ⟨o, ho, l, hl1, hl2, rfl⟩
  have hlt := mhi_lt (hph o ho).1 hl2.le (show D - l ≤ cd by omega)
  have hh := mhi_half (q := o.leafIndex) hl2
  rw [capFlags, hcd]
  refine getElem?_setAll _ 1 _ _ (by rw [Array.size_replicate]; omega) (fun p hp _ => ?_)
    ⟨_, List.mem_map_of_mem hs, ?_⟩
  · simp only [List.mem_map] at hp
    obtain ⟨s, -, rfl⟩ := hp
    rfl
  · simp [capStep, hh]

include hcd hph in
/-- **A flag no climb passes is unset.** -/
theorem capFlags_zero {k : ℕ} (hk : k < 2 ^ cd)
    (hno : ∀ o ∈ phase, ∀ l, D - cd ≤ l → l < D → Limits.merkleHeapIndex D o.leafIndex (l + 1) ≠ k) :
    (capFlags D phase)[k]? = some 0 := by
  rw [capFlags, hcd, getElem?_setAll_of_not]
  · simp [hk]
  · intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨s, hs, rfl⟩ := hp
    obtain ⟨o, ho, l, hl1, hl2, rfl⟩ := (mem_capSteps hcd hph).mp hs
    simp only [capStep]
    rw [mhi_half hl2]
    exact hno o ho l hl1 hl2

end Phase

/-! ## The cells -/

theorem length_flatMap_digestCells : ∀ l : List Digest, (l.flatMap Hints.digestCells).length = 2 * l.length
  | [] => rfl
  | x :: l => by
    rw [List.flatMap_cons, List.length_append, length_flatMap_digestCells l, List.length_cons]
    simp only [Hints.digestCells, List.length_cons, List.length_nil]
    ring

theorem getD_flatMap_digestCells : ∀ (l : List Digest) (i : ℕ) (d : Digest), l[i]? = some d →
    (l.flatMap Hints.digestCells).getD (2 * i) 0 = (digestHalves d).1 ∧
      (l.flatMap Hints.digestCells).getD (2 * i + 1) 0 = (digestHalves d).2
  | [], _, _, h => by simp at h
  | x :: l, 0, d, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  | x :: l, i + 1, d, h => by
    simp only [List.getElem?_cons_succ] at h
    have := getD_flatMap_digestCells l i d h
    rw [List.flatMap_cons, show 2 * (i + 1) = 2 * i + 1 + 1 by ring]
    simpa only [Hints.digestCells, List.cons_append, List.nil_append, List.getD_cons_succ] using this

theorem cells_of_get {a : Array Digest} {i : ℕ} {d : Digest} (h : a[i]? = some d) :
    (a.toList.flatMap Hints.digestCells).getD (2 * i) 0 = (digestHalves d).1 ∧
      (a.toList.flatMap Hints.digestCells).getD (2 * i + 1) 0 = (digestHalves d).2 :=
  getD_flatMap_digestCells _ i d (by simpa using h)

/-- **A node's cells hash its children's** when the node is their digest. -/
theorem hashesPair_of {x y p : Digest} (h : p = keccak256 (digestBytes x ++ digestBytes y)) :
    HashesPair (digestHalves x).1 (digestHalves x).2 (digestHalves y).1 (digestHalves y).2
      (digestHalves p).1 (digestHalves p).2 := by
  unfold HashesPair
  rw [show [(digestHalves x).1, (digestHalves x).2, (digestHalves y).1, (digestHalves y).2] =
      [(digestHalves x).1, (digestHalves x).2] ++ [(digestHalves y).1, (digestHalves y).2] from rfl,
    cellsBytes_append, cellsBytes_digestScalars, cellsBytes_digestScalars, ← h]

section Hash

variable {D cd : ℕ} {phase : List Opening} {root : Digest}
  (hcd : Hints.capDepthOf phase.length D = cd) (hcdD : cd ≤ D)
  (hph : ∀ o ∈ phase, o.leafIndex < 2 ^ D ∧ o.path.length = D)
  (hag : Limits.OpeningsAgree D (phase.map fun o => (o.leafIndex, o)))
  (hroot : ∀ o ∈ phase, Limits.climbTo (merkleLeafDigest o.leaf) o.leafIndex o.path = root)

include hcd hcdD hph hag hroot in
/-- **A node a climb passes in the cap hashes its children**. -/
theorem capNodes_hash {o : Opening} (ho : o ∈ phase) {l : ℕ} (hl1 : D - cd ≤ l) (hl2 : l < D) (m : ℕ)
    (hm : Limits.merkleHeapIndex D o.leafIndex (l + 1) = m) :
    HashesPair (((capNodes D phase).toList.flatMap Hints.digestCells).getD (4 * m) 0)
      (((capNodes D phase).toList.flatMap Hints.digestCells).getD (4 * m + 1) 0)
      (((capNodes D phase).toList.flatMap Hints.digestCells).getD (4 * m + 2) 0)
      (((capNodes D phase).toList.flatMap Hints.digestCells).getD (4 * m + 3) 0)
      (((capNodes D phase).toList.flatMap Hints.digestCells).getD (2 * m) 0)
      (((capNodes D phase).toList.flatMap Hints.digestCells).getD (2 * m + 1) 0) := by
  obtain ⟨hp1, hp2⟩ := cells_of_get (capNodes_climb hcd hcdD hph hag hroot ho (l := l + 1) (by omega) (by omega))
  rw [hm] at hp1 hp2
  obtain ⟨hn1, hn2⟩ := cells_of_get (capNodes_node hcd hcdD hph hag ho hl1 hl2)
  obtain ⟨hs1, hs2⟩ := cells_of_get (capNodes_sibling hcd hcdD hph hag ho hl1 hl2)
  rw [xor_one_eq] at hs1 hs2
  have e := mhi_succ (q := o.leafIndex) hl2
  rw [hm] at e
  have hstep := climbTo_take_succ (merkleLeafDigest o.leaf) o.leafIndex o.path l (by rw [(hph o ho).2]; exact hl2)
  rw [hp1, hp2]
  generalize Limits.merkleHeapIndex D o.leafIndex l = n at hn1 hn2 hs1 hs2 e
  generalize o.leafIndex / 2 ^ l = x at e hstep
  rcases Nat.mod_two_eq_zero_or_one x with hb | hb
  · rw [show 2 * n = 4 * m by omega] at hn1
    rw [show 2 * n + 1 = 4 * m + 1 by omega] at hn2
    rw [show 2 * (2 * (n / 2) + (1 - n % 2)) = 4 * m + 2 by omega] at hs1
    rw [show 2 * (2 * (n / 2) + (1 - n % 2)) + 1 = 4 * m + 3 by omega] at hs2
    rw [hn1, hn2, hs1, hs2]
    exact hashesPair_of (by simp only [hstep, hb, ↓reduceIte])
  · rw [show 2 * n = 4 * m + 2 by omega] at hn1
    rw [show 2 * n + 1 = 4 * m + 3 by omega] at hn2
    rw [show 2 * (2 * (n / 2) + (1 - n % 2)) = 4 * m by omega] at hs1
    rw [show 2 * (2 * (n / 2) + (1 - n % 2)) + 1 = 4 * m + 1 by omega] at hs2
    rw [hn1, hn2, hs1, hs2]
    exact hashesPair_of (by simp only [hstep, hb, one_ne_zero, ↓reduceIte])

end Hash

theorem isInK_zero' : IsInK (0 : E) := limb_zero 1

theorem isInK_one'' : IsInK (1 : E) := (isInK_iff _).mpr ⟨1, (map_one (algebraMap K E)).symm⟩

/-- **`level_queries`' honest cap**: a phase whose openings climb to `root` and agree wherever they
meet has an honest cap and honest flags at its cap depth. -/
theorem lqCapHonest : LqCapHonest := by
  intro D phase root hne hcd2 hcdD hph0 hag
  obtain ⟨cd, hcd⟩ : ∃ cd, Hints.capDepthOf phase.length D = cd := ⟨_, rfl⟩
  rw [hcd] at hcd2 hcdD ⊢
  have hph : ∀ o ∈ phase, o.leafIndex < 2 ^ D ∧ o.path.length = D :=
    fun o ho => ⟨(hph0 o ho).1, (hph0 o ho).2.1⟩
  have hroot : ∀ o ∈ phase, Limits.climbTo (merkleLeafDigest o.leaf) o.leafIndex o.path = root :=
    fun o ho => by rw [← climbD_eq_climbTo]; exact (hph0 o ho).2.2
  have hsz := size_capNodes (D := D) (phase := phase)
  have hfz := size_capFlags (D := D) (phase := phase)
  rw [hcd] at hsz hfz
  have hev : 2 ^ cd = 2 * 2 ^ (cd - 1) := by rw [← pow_succ']; congr 1; omega
  have hF : ∀ k, (lqFlW D phase.length phase).getD k 0 = ((capFlags D phase)[k]?).getD 0 := fun k => by
    rw [lqFlW_eq, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  have hC := lqCapW_eq D phase
  have flag1 : ∀ o ∈ phase, ∀ l, D - cd ≤ l → l < D →
      (lqFlW D phase.length phase).getD (Limits.merkleHeapIndex D o.leafIndex (l + 1)) 0 = 1 := by
    intro o ho l hl1 hl2
    rw [hF, capFlags_one hcd hph ho hl1 hl2]
    rfl
  have flag0 : ∀ k, k < 2 ^ cd →
      (∀ o ∈ phase, ∀ l, D - cd ≤ l → l < D → Limits.merkleHeapIndex D o.leafIndex (l + 1) ≠ k) →
      (lqFlW D phase.length phase).getD k 0 = 0 := by
    intro k hk hn
    rw [hF, capFlags_zero hcd hph hk hn]
    rfl
  have hit : ∀ k, k < 2 ^ cd → (lqFlW D phase.length phase).getD k 0 ≠ 0 →
      ∃ o ∈ phase, ∃ l, D - cd ≤ l ∧ l < D ∧ Limits.merkleHeapIndex D o.leafIndex (l + 1) = k := by
    intro k hk hne'
    by_contra hn
    push Not at hn
    exact hne' (flag0 k hk hn)
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hC, length_flatMap_digestCells, Array.length_toList, hsz]
    ring
  · rw [lqFlW_eq, Array.length_toList, hfz]
  · intro k _ hk
    by_cases h : (lqFlW D phase.length phase).getD k 0 = 0
    · rw [h]; exact isInK_zero'
    · obtain ⟨o, ho, l, hl1, hl2, rfl⟩ := hit k hk h
      rw [flag1 o ho l hl1 hl2]
      exact isInK_one''
  · intro k _ hk2 hk
    have hk' : ∃ o ∈ phase, ∃ l, D - cd ≤ l ∧ l < D ∧ Limits.merkleHeapIndex D o.leafIndex (l + 1) = k := by
      rcases hk with hk1 | hk
      · subst hk1
        obtain ⟨o, os, rfl⟩ := List.exists_cons_of_ne_nil hne
        refine ⟨o, List.mem_cons_self, D - 1, by omega, by omega, ?_⟩
        rw [Nat.sub_add_cancel (by omega)]
        exact mhi_depth (hph o List.mem_cons_self).1
      · exact hit k hk2 hk
    obtain ⟨o, ho, l, hl1, hl2, hm⟩ := hk'
    rw [hC]
    exact capNodes_hash hcd hcdD hph hag hroot ho hl1 hl2 k hm
  · intro k hk2 hk22 hk0
    have child : ∀ j, j / 2 = k → j < 2 ^ cd → (lqFlW D phase.length phase).getD j 0 = 0 := by
      intro j hj hjlt
      by_contra hne'
      obtain ⟨o, ho, l, hl1, hl2, hjm⟩ := hit j hjlt hne'
      have hl3 : l + 1 < D := by
        by_contra hge
        have h1 : l + 1 = D := by omega
        rw [h1, mhi_depth (hph o ho).1] at hjm
        omega
      have h2 := flag1 o ho (l + 1) (by omega) hl3
      rw [← mhi_half hl3, hjm, hj, hk0] at h2
      exact zero_ne_one h2
    exact ⟨child (2 * k) (by omega) hk22, child (2 * k + 1) (by omega) (by omega)⟩
  · have h1 := cells_of_get (capNodes_one hph hroot hne)
    rw [hC]
    exact Prod.ext h1.1 h1.2
  · intro k hk
    have ho : opAt phase k ∈ phase := by
      unfold opAt
      rw [List.getD_eq_getElem _ _ hk]
      exact List.getElem_mem hk
    have hpd : D - cd < D := by omega
    have hcells := cells_of_get (capNodes_node hcd hcdD hph hag ho le_rfl hpd)
    have hidx : 2 * Limits.merkleHeapIndex D (opAt phase k).leafIndex (D - cd) =
        2 ^ (cd + 1) + 2 * ((opAt phase k).leafIndex / 2 ^ (D - cd)) := by
      rw [Limits.merkleHeapIndex, Nat.sub_sub_self hcdD, pow_succ]
      ring
    rw [hidx] at hcells
    have hfi : 2 ^ (cd - 1) + (opAt phase k).leafIndex / 2 ^ (D - cd + 1) =
        Limits.merkleHeapIndex D (opAt phase k).leafIndex (D - cd + 1) := by
      rw [Limits.merkleHeapIndex]
      congr 2
      omega
    refine ⟨?_, ?_, ?_⟩
    · rw [hC, hcells.1, climbD_eq_climbTo]
    · rw [hC, hcells.2, climbD_eq_climbTo]
    · rw [hfi]
      exact flag1 _ ho _ le_rfl hpd

end

end LeanVM.Guest.B1.VsC
