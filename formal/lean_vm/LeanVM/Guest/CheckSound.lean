/-
  LeanVM.Guest.CheckSound

  Soundness of the checker: a function whose check passes satisfies its core IR relation, under
  its callees' contracts.
-/

module

public import LeanVM.Guest.Exec
public import LeanVM.Guest.Check
public import LeanVM.Guest.CoreLoc
import Mathlib.Data.List.GetD

/-!
# Soundness of the checker

On a memory `L` and a frame `fp`, the valuation of a check reads every core value from its
certificate cell (`val`). A book holds when every atom filed in it holds (`BookHolds`); passing an
item keeps that (`BookHolds.addFact`), and each of the checker's tests for a core atom implies the
atom under the valuation (`atomOk_sound`).
-/

namespace LeanVM.Guest.Check

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

/-! ## Words of the frame -/

section Words

variable {κ : ℕ} (L : MemoryImage κ) (fp : K)

/-- The word in frame cell `o`, `0` if none. -/
noncomputable def wd (o : ℕ) : E := (L.read (fp * addressOfIndex o)).getD 0

/-- The valuation of a check: every value is the word in its cell. -/
noncomputable def val (loc : Trie ℕ) : Core.Val := fun v ↦ wd L fp (cellOf loc v)

/-- The valuation of a function's check: every value is the word in its cell. -/
noncomputable def valG (C : Cert) : Core.Val := fun v ↦ wd L fp (C.locs.getD v.idx 0)

/-- The `n` words of the frame from cell `o`. -/
noncomputable def frameWords (o n : ℕ) : List E := (List.range n).map fun i ↦ wd L fp (o + i)

/-- The atoms filed in a book hold. -/
def BookHolds (B : Book) : Prop := ∀ o, ∀ a ∈ look B o, a.Holds L fp

/-- The bounds hold: `fp[c] = g^e` with `e < n` for each `(c, n)`. -/
def BndHolds (bnd : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ bnd, ∃ e < p.2, L.read (fp * addressOfIndex p.1) = some (ofK (addressOfIndex e))

end Words

section Basic

variable {κ : ℕ} {L : MemoryImage κ} {fp : K}

theorem wd_of {o : ℕ} {v : E} (h : L.read (fp * addressOfIndex o) = some v) : wd L fp o = v := by
  simp [wd, h]

theorem look_addKey {a b : Exec.Atom} {B : Book} {o o' : ℕ} (h : b ∈ look (addKey a B o) o') :
    b = a ∨ b ∈ look B o' := by
  have e : addKey a B o = B.set (a :: look B o) envDepth o := by
    unfold addKey
    rw [listSeq_eq, setF_eq]
  rw [e] at h
  have h' : b ∈ ((B.set (a :: look B o) envDepth o).get o').getD [] := by
    simpa [look, getF_eq] using h
  rcases hg : (B.set (a :: look B o) envDepth o).get o' with _ | l
  · simp [hg] at h'
  · rw [hg] at h'
    rcases Trie.get_set hg with ⟨rfl, rfl⟩ | h''
    · simpa using h'
    · right
      simpa [look, getF_eq, h''] using h'

theorem BookHolds.nil : BookHolds L fp .nil := fun _ _ h ↦ by simp [look, getF_eq] at h

theorem BookHolds.addFact {B : Book} (hB : BookHolds L fp B) {a : Exec.Atom} (ha : a.Holds L fp) :
    BookHolds L fp (Check.addFact B a) := by
  unfold Check.addFact
  generalize keys a = ks
  induction ks generalizing B with
  | nil => exact hB
  | cons o ks ih =>
    refine ih (fun o' b hb ↦ ?_)
    rcases look_addKey hb with rfl | hb
    · exact ha
    · exact hB o' b hb

theorem BndHolds.append {b₁ b₂ : List (ℕ × ℕ)} (h₁ : BndHolds L fp b₁) (h₂ : BndHolds L fp b₂) :
    BndHolds L fp (b₁ ++ b₂) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact h₁ p hp
  · exact h₂ p hp

theorem nth_eq {α : Type} {l : List α} {n : ℕ} {d : α} (h : n < l.length) : listElementOrDefault l n
    d = l[n] :=
  Option.some.inj ((nth_eq_getElem? d h).symm.trans (List.getElem?_eq_getElem h))

theorem limb_ofK0 (a : K) : (ofK a).limb 0 = a := by simp

theorem char2 (a b : E) : a + (a + b) = b := by
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem ofBits_toNat (a : K) : K.ofBits a.toBitVec.toNat = a := by
  simp [K.ofBits, BitVec.ofNat_toNat]

theorem eq_imm_of_limbs {x : E} {k0 k1 : ℕ} (h0 : limbNat x 0 = k0) (h1 : limbNat x 1 = k1) :
    x = OffsetInstruction.immediateWord k0 k1 := by
  subst h0 h1
  rw [OffsetInstruction.immediateWord, limbNat, limbNat, ofBits_toNat, ofBits_toNat, ofLimbs_limb]

end Basic

/-! ## The atoms of a book -/

section Atoms

variable {κ : ℕ} {L : MemoryImage κ} {fp : K} {B : Book}

theorem setImm_sound (hB : BookHolds L fp B) {c l0 l1 : ℕ} (h : setImm B c l0 l1 = true) :
    L.read (fp * addressOfIndex c) = some (OffsetInstruction.immediateWord l0 l1) := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  have hh := hB c a ha
  split at hp
  · rename_i pc o k0 k1
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp
    exact hh
  · simp at hp

theorem setIs_sound (hB : BookHolds L fp B) {c : ℕ} {x : E} (h : setIs B c x = true) :
    L.read (fp * addressOfIndex c) = some x := by
  rw [eq_imm_of_limbs rfl rfl (x := x)]
  exact setImm_sound hB h

theorem perm3_sound {x y z p q r : ℕ} (h : perm3 x y z p q r = true) {vX vY : E}
    (hx : L.read (fp * addressOfIndex x) = some vX) (hy : L.read (fp * addressOfIndex y) = some vY)
    (hz : L.read (fp * addressOfIndex z) = some (vX + vY)) : wd L fp r = wd L fp p + wd L fp q := by
  simp only [perm3, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ((((⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩) | ⟨⟨rfl, rfl⟩, rfl⟩) |
    ⟨⟨rfl, rfl⟩, rfl⟩) | ⟨⟨rfl, rfl⟩, rfl⟩) | ⟨⟨rfl, rfl⟩, rfl⟩
  · rw [wd_of hx, wd_of hy, wd_of hz]
  · rw [wd_of hx, wd_of hy, wd_of hz, add_comm]
  · rw [wd_of hx, wd_of hy, wd_of hz, char2]
  · rw [wd_of hx, wd_of hy, wd_of hz, add_comm vX, char2]
  · rw [wd_of hx, wd_of hy, wd_of hz, add_comm, char2]
  · rw [wd_of hx, wd_of hy, wd_of hz, add_comm (vX + vY), add_comm vX, char2]

theorem xorIn_sound (hB : BookHolds L fp B) {o p q r : ℕ} (h : xorIn B o p q r = true) :
    wd L fp r = wd L fp p + wd L fp q := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  have hh := hB o a ha
  split at hp
  · obtain ⟨vX, vY, hx, hy, hz⟩ := hh
    exact perm3_sound hp hx hy hz
  · simp at hp

theorem addOk_sound (hB : BookHolds L fp B) {d a b : ℕ} (h : addOk B d a b = true) :
    wd L fp d = wd L fp a + wd L fp b := by
  simp only [addOk, Bool.or_eq_true] at h
  rcases h with (h | h) | h <;> exact xorIn_sound hB h

theorem mulOk_sound (hB : BookHolds L fp B) {d a b : ℕ} (h : mulOk B d a b = true) :
    ∃ vA vB, L.read (fp * addressOfIndex a) = some vA ∧ L.read (fp * addressOfIndex b) = some vB ∧
      L.read (fp * addressOfIndex d) = some (vA * vB) := by
  obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
  have hh := hB d x hx
  split at hp
  · rename_i pc x' y' z'
    obtain ⟨vX, vY, h1, h2, h3⟩ := hh
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hp
    obtain ⟨rfl, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ := hp
    · exact ⟨vX, vY, h1, h2, h3⟩
    · exact ⟨vY, vX, h2, h1, by rw [mul_comm vY vX]; exact h3⟩
  · simp at hp

theorem mulOk_wd (hB : BookHolds L fp B) {d a b : ℕ} (h : mulOk B d a b = true) :
    wd L fp d = wd L fp a * wd L fp b := by
  obtain ⟨vA, vB, h1, h2, h3⟩ := mulOk_sound hB h
  rw [wd_of h1, wd_of h2, wd_of h3]

theorem sameOk_sound (hB : BookHolds L fp B) {a b : ℕ} (h : sameOk B a b = true) :
    wd L fp a = wd L fp b := by
  simp only [sameOk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · rfl
  obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
  have hh := hB a x hx
  split at hp
  · obtain ⟨v, h1, h2⟩ := hh
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [wd_of h1, wd_of h2]
    · rw [wd_of h1, wd_of h2]
  · obtain ⟨v, h1, h2⟩ := hh
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [wd_of h1, wd_of h2]
    · rw [wd_of h1, wd_of h2]
  · simp at hp

theorem sameOk_read (hB : BookHolds L fp B) {a b : ℕ} (h : sameOk B a b = true) :
    L.read (fp * addressOfIndex a) = L.read (fp * addressOfIndex b) := by
  simp only [sameOk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · rfl
  obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
  have hh := hB a x hx
  split at hp
  · obtain ⟨v, h1, h2⟩ := hh
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [h1, h2]
    · rw [h1, h2]
  · obtain ⟨v, h1, h2⟩ := hh
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [h1, h2]
    · rw [h1, h2]
  · simp at hp

theorem setSame_sound (hB : BookHolds L fp B) {p q : ℕ} (h : setSame B p q = true) :
    wd L fp p = wd L fp q := by
  simp only [setSame, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · rfl
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  have hh := hB p a ha
  split at hp
  · rename_i pc o k0 k1
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨rfl, hq⟩ := hp
    rw [wd_of hh, wd_of (setImm_sound hB hq)]
  · simp at hp

theorem eqCell_sound (hB : BookHolds L fp B) {a b : ℕ} (h : eqCell B a b = true) :
    wd L fp a = wd L fp b := by
  simp only [eqCell, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact sameOk_sound hB h
  · exact setSame_sound hB h
  · obtain ⟨u, hu, hp⟩ := List.any_eq_true.mp h
    clear h
    have hh := hB a u hu
    split at hp
    · rename_i pc x y z
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨hza, hp⟩ := hp
      obtain ⟨w, hw, hp⟩ := List.any_eq_true.mp hp
      have hh' := hB b w hw
      split at hp
      · rename_i pc' x' y' z'
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hp
        obtain ⟨hzb, hp⟩ := hp
        obtain ⟨vX, vY, hx, hy, hz⟩ := hh
        obtain ⟨vX', vY', hx', hy', hz'⟩ := hh'
        rw [← hza, ← hzb, wd_of hz, wd_of hz', ← wd_of hx, ← wd_of hy, ← wd_of hx', ← wd_of hy']
        rcases hp with ((⟨rfl, hs⟩ | ⟨rfl, hs⟩) | ⟨rfl, hs⟩) | ⟨rfl, hs⟩
        · rw [setSame_sound hB hs]
        · rw [setSame_sound hB hs]
        · rw [setSame_sound hB hs, mul_comm]
        · rw [setSame_sound hB hs, mul_comm]
      · simp at hp
    · simp at hp

/-- **A guard's pair differs**: `fp[c] ≠ 0` and `neAt B c a b` give `fp[a] ≠ fp[b]`. -/
theorem neAt_sound (hB : BookHolds L fp B) {c a b : ℕ} (h : neAt B c a b = true)
    (hc : wd L fp c ≠ 0) : wd L fp a ≠ wd L fp b := by
  obtain ⟨u, hu, hp⟩ := List.any_eq_true.mp h
  have hh := hB c u hu
  split at hp
  · rename_i pc x y z
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hp
    obtain ⟨rfl, hp⟩ := hp
    obtain ⟨vX, vY, hx, hy, hz⟩ := hh
    intro hab
    apply hc
    rw [wd_of hz, ← wd_of hx, ← wd_of hy]
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [eqCell_sound hB h1, eqCell_sound hB h2, hab, CharTwo.add_self_eq_zero]
    · rw [eqCell_sound hB h1, eqCell_sound hB h2, hab, CharTwo.add_self_eq_zero]
  · simp at hp

theorem loadOk_sound (hB : BookHolds L fp B) {d p off : ℕ} (h : loadOk B d p off = true) :
    ∃ pv, L.read (fp * addressOfIndex p) = some pv ∧ IsInK pv ∧
      ∃ v, L.read (fp * addressOfIndex d) = some v ∧ L.read (pv.limb 0 * addressOfIndex off) = some
          v := by
  obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
  have hh := hB d x hx
  split at hp
  · simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp
    obtain ⟨pv, v3, h1, hK, h3, h2⟩ := hh
    exact ⟨pv, h1, hK, v3, h3, h2⟩
  · simp at hp

theorem loadOk_holds (hB : BookHolds L fp B) {d p off : ℕ} (h : loadOk B d p off = true) :
    Core.LoadHolds L.read (wd L fp p) off (wd L fp d) := by
  obtain ⟨pv, h1, hK, v, h3, h2⟩ := loadOk_sound hB h
  rw [wd_of h1, wd_of h3]
  exact ⟨hK, h2⟩

theorem inKOk_sound (hB : BookHolds L fp B) {a b : ℕ} (h : inKOk B a b = true) :
    IsInK (wd L fp a) ∧ IsInK (wd L fp b) := by
  obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
  have hh := hB a x hx
  split at hp
  · simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    obtain ⟨c, d, f, -, h2, h3, -, hd, hf⟩ := hh
    rw [wd_of h2, wd_of h3]
    exact ⟨hd, hf⟩
  · simp at hp

theorem keccakOk_sound (hB : BookHolds L fp B) {ins outs : List ℕ} {inOdd outOdd : Bool}
    (h : keccakOk B ins outs inOdd outOdd = true) :
    ins.length = 13 ∧ ∃ oc : KeccakOutputCells, outs.length = oc.cellCount ∧
      KeccakCellsRelation (Core.cells13 (ins.map (wd L fp))) inOdd (Core.cells13 (outs.map (wd L fp)))
        outOdd oc := by
  unfold keccakOk at h
  split at h
  · exact absurd h Bool.false_ne_true
  rename_i o rest
  obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
  have hh := hB o x hx
  split at hp
  · rename_i pc m0 m1 m2 m3 tail b8 cap out iO oO oC
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨⟨⟨-, rfl⟩, rfl⟩, hins⟩, hout⟩ := hp
    obtain ⟨input, output, hin, hout', hk⟩ := hh
    have hlen : (o :: rest).length = oC.cellCount := by rw [hout, keccakOuts_length]
    have ei : Core.cells13 (ins.map (wd L fp)) = input := by
      funext c
      rw [Core.cells13, hins, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem (by simp [keccakIns]), Option.map_some, Option.getD_some,
        List.getElem_eq_getD 0, keccakIns_getD _ _ _ _ _ _ _ c.isLt]
      exact wd_of (hin c)
    have eo : ∀ c : Fin 13, c.val < oC.cellCount →
        Core.cells13 ((o :: rest).map (wd L fp)) c = output c := by
      intro c hc
      rw [Core.cells13, hout, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem (by simp [keccakOuts]; exact hc), Option.map_some,
        Option.getD_some, List.getElem_eq_getD 0, keccakOuts_getD _ _ hc]
      exact wd_of (hout' c hc)
    refine ⟨by rw [hins, keccakIns_eq]; rfl, oC, hlen, ?_⟩
    rw [ei]
    exact fun c hc ↦ (eo c hc).trans (hk c hc)
  · exact absurd hp Bool.false_ne_true

theorem neOk_sound (hB : BookHolds L fp B) {x i p : ℕ} (h : neOk B x i p = true) :
    wd L fp p = wd L fp x * wd L fp i ∧ wd L fp p = 1 := by
  simp only [neOk, Bool.and_eq_true] at h
  refine ⟨mulOk_wd hB h.1, wd_of ?_⟩
  rw [show (1 : E) = OffsetInstruction.immediateWord 1 0 from (imm_of_ofBits rfl).trans ofK_one
      |>.symm]
  exact setImm_sound hB h.2

theorem rangeOk_sound (hB : BookHolds L fp B) {x y t1 t2 k : ℕ}
    (h : rangeOk B x y t1 t2 k = true) :
    Core.LoadHolds L.read (wd L fp x) 0 (wd L fp t1) ∧ wd L fp k = wd L fp x * wd L fp y ∧
      Core.LoadHolds L.read (wd L fp y) 0 (wd L fp t2) := by
  simp only [rangeOk, Bool.and_eq_true] at h
  exact ⟨loadOk_holds hB h.1.1, mulOk_wd hB h.1.2, loadOk_holds hB h.2⟩

theorem bounceOk_sound (hB : BookHolds L fp B) {x : ℕ} (h : bounceOk B x = true) :
    L.read (fp * addressOfIndex x) = some (ofK fp) := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  have hh := hB x a ha
  split at hp
  · rename_i pc hc x'
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨rfl, hp⟩ := hp
    obtain ⟨b, hb, hq⟩ := List.any_eq_true.mp hp
    have hh' := hB hc b hb
    split at hq
    · rename_i pc' h' o3
      simp only [beq_iff_eq] at hq
      subst hq
      obtain ⟨p, v3, h1, -, h3, h2⟩ := hh
      obtain ⟨p', v3', h1', -, -, h2'⟩ := hh'
      obtain rfl : p' = p := Option.some.inj (h1'.symm.trans h1)
      have hv := Option.some.inj (h2.symm.trans h2')
      simp only [derefSource] at hv
      rw [h3, hv]
    · simp at hq
  · simp at hp

theorem fpgAt_sound (hB : BookHolds L fp B) {ψ : Trie Sym} (hψ : EnvHolds L fp ψ) {x e : ℕ}
    (h : fpgAt B ψ x = some e) : L.read (fp * addressOfIndex x) = some (ofK (fp * addressOfIndex
        e)) := by
  unfold fpgAt at h
  split at h
  · rename_i e' he
    obtain rfl := Option.some.inj h
    exact hψ x _ he
  · simp only [Bool.cond_eq_ite] at h
    split_ifs at h with hb
    obtain rfl := Option.some.inj h
    rw [bounceOk_sound hB hb, gpow_zero', mul_one]

theorem gpAt_sound {F : Exec.Facts} (hF : F.pows.Ok) (hB : BookHolds L fp B) {ψ : Trie Sym}
    (hψ : EnvHolds L fp ψ) {y e : ℕ} (h : gpAt F B ψ y = some e) :
    L.read (fp * addressOfIndex y) = some (ofK (addressOfIndex e)) := by
  unfold gpAt at h
  split at h
  · rename_i e' he
    obtain rfl := Option.some.inj h
    exact hψ y _ he
  · obtain ⟨a, ha, hp⟩ := List.exists_of_findSome?_eq_some h
    have hh := hB y a ha
    split at hp
    · rename_i pc o k0
      simp only [Bool.cond_eq_ite, beq_iff_eq] at hp
      split_ifs at hp with ho
      subst ho
      have := PowTree.find_ok hF hp
      rw [hh, imm_of_ofBits this]
    · simp at hp

theorem fpgChain_sound {F : Exec.Facts} (hF : F.pows.Ok) (hB : BookHolds L fp B) {ψ : Trie Sym}
    (hψ : EnvHolds L fp ψ) : ∀ {n x e : ℕ}, fpgChain F B ψ n x = some e →
      L.read (fp * addressOfIndex x) = some (ofK (fp * addressOfIndex e))
  | 0, x, e, h => fpgAt_sound hB hψ h
  | n + 1, x, e, h => by
    unfold fpgChain at h
    split at h
    · rename_i e' he
      obtain rfl := Option.some.inj h
      exact fpgAt_sound hB hψ he
    · obtain ⟨a, ha, hp⟩ := List.exists_of_findSome?_eq_some h
      have hh := hB x a ha
      split at hp
      · rename_i pc y z w
        simp only [Bool.cond_eq_ite, beq_iff_eq] at hp
        split_ifs at hp with hw
        subst hw
        split at hp
        · rename_i e1 e2 h1 h2
          obtain rfl := Option.some.inj hp
          obtain ⟨vY, vZ, hy, hz, hx⟩ := hh
          rw [fpgChain_sound hF hB hψ h1] at hy
          rw [gpAt_sound hF hB hψ h2] at hz
          obtain rfl := Option.some.inj hy
          obtain rfl := Option.some.inj hz
          rw [hx, ← ofK_mul, mul_assoc, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add]
        · cases hp
      · cases hp

theorem runAt_sound {loc : Trie ℕ} : ∀ {base : ℕ} {vs : List Core.V}, runAt loc base vs = true →
    ∀ i (hi : i < vs.length), cellOf loc vs[i] = base + i
  | _, [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | base, v :: vs, h, i, hi => by
    simp only [runAt, Bool.and_eq_true, beq_iff_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have := runAt_sound h.2 i (by simpa using hi)
      simp only [List.getElem_cons_succ]
      rw [this]
      omega

theorem addrOk_sound {F : Exec.Facts} (hF : F.pows.Ok) (hB : BookHolds L fp B) {ψ : Trie Sym}
    (hψ : EnvHolds L fp ψ) {loc : Trie ℕ} {p : ℕ} {run : List Core.V}
    (h : addrOk F B ψ loc p run = true) :
    IsInK (wd L fp p) ∧ ∀ (k : ℕ) (hk : k < run.length) (w : E),
      L.read ((wd L fp p).limb 0 * addressOfIndex k) = some w → w = val L fp loc run[k] := by
  obtain ⟨a, ha, hq⟩ := List.any_eq_true.mp h
  have hh := hB p a ha
  split at hq
  · rename_i pc x y z
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    obtain ⟨rfl, hq⟩ := hq
    split at hq
    · rename_i e1 e2 h1 h2
      obtain ⟨vX, vY, hx, hy, hz⟩ := hh
      rw [fpgChain_sound hF hB hψ h1] at hx
      rw [gpAt_sound hF hB hψ h2] at hy
      obtain rfl := Option.some.inj hx
      obtain rfl := Option.some.inj hy
      have hp : wd L fp z = ofK (fp * addressOfIndex (e1 + e2)) := by
        rw [wd_of hz, ← ofK_mul, mul_assoc, addressOfIndex, addressOfIndex, addressOfIndex, ←
            pow_add]
      rw [hp]
      refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, fun k hk w hw ↦ ?_⟩
      have hl : (ofK (fp * addressOfIndex (e1 + e2))).limb 0 = fp * addressOfIndex (e1 + e2) :=
          by simp
      have ha : fp * addressOfIndex (e1 + e2) * addressOfIndex k = fp * addressOfIndex (e1 + e2 +
          k) := by
        rw [mul_assoc, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add]
      rw [hl, ha] at hw
      unfold val
      rw [runAt_sound hq k hk]
      exact (wd_of hw).symm
    · simp at hq
  · simp at hq

/-- **A core atom the book implies holds** under the valuation of the check. -/
theorem atomOk_sound {F : Exec.Facts} (hF : F.pows.Ok) (hB : BookHolds L fp B) {ψ : Trie Sym}
    (hψ : EnvHolds L fp ψ) {loc : Trie ℕ} {a : Core.Atom} (h : atomOk F B ψ loc a = true) :
    a.Holds L.read (val L fp loc) := by
  cases a with
  | const d x => exact wd_of (setIs_sound hB h)
  | add d a b => exact addOk_sound hB h
  | mul d a b => exact mulOk_wd hB h
  | copy d s => exact sameOk_sound hB h
  | load d p off => exact loadOk_holds hB h
  | assertEq a b =>
    show wd L fp _ + wd L fp _ = 0
    rw [sameOk_sound hB h, CharTwo.add_self_eq_zero]
  | assertNe x i p => exact neOk_sound hB h
  | rangeCheck x y t1 t2 k => exact rangeOk_sound hB h
  | assertInK a b => exact inKOk_sound hB h
  | keccak ins outs inOdd outOdd =>
    obtain ⟨h1, oc, h2, h3⟩ := keccakOk_sound hB h
    refine ⟨by simpa [cellsOf] using h1, oc, by simpa [cellsOf] using h2, ?_⟩
    simp only [cellsOf, List.map_map] at h3
    exact h3
  | frameAddr p run => exact addrOk_sound hF hB hψ h
  | hint _ => trivial

end Atoms

/-! ## Contracts -/

section Contracts

variable {κ : ℕ} (P : Core.Program) (G : Glob) (L : MemoryImage κ)

/-- The valuation of function `f` at frame `fp`: its certificate's cells (`cert f`). -/
noncomputable def frameVal (cert : String → Cert) (f : String) (fp : K) : Core.Val :=
  valG L fp (cert f)

/-- A frame in a memory of `2^n` words: `fp = g^a`, `a < 2^n`. -/
def InMem (n : ℕ) (fp : K) : Prop := ∃ a < 2 ^ n, fp = addressOfIndex a

/-- **The guest's located call relation**: a callee runs at a frame `fp` with `A f fp args rets`,
its values its certificate's cells there (`Core.Program.RelL`). -/
noncomputable abbrev RL (cert : String → Cert) (A : String → K → List E → List E → Prop) : Core.CallRel :=
  P.RelL L.read (frameVal L cert) A

/-- The jump table holds: slot `s` of the frame of `main` (`fp = 1`) holds `g^t`. -/
def JTHolds : Prop := ∀ s t, G.jt.get s = some t → L.read (addressOfIndex s) = some (ofK
    (addressOfIndex t))

/-- Memory bounded through frame cells: for each `(o, c, n)`, the word at `fp[o]·g^c` is `g^e`
with `e < n`. -/
def MemPre (fp : K) (mem : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ m ∈ mem, ∃ p, L.read (fp * addressOfIndex m.1) = some p ∧ IsInK p ∧
    ∃ e < m.2.2, L.read (p.limb 0 * addressOfIndex m.2.1) = some (ofK (addressOfIndex e))

/-- The relation tagged `t < 2^32` on words: `tagNe`'s is `a ≠ b`, the checker's own (`neAt`); the
others are the program's (`Glob.sem`). -/
def SemRel0 (t : ℕ) (rd : Core.Reader) (ws : List E) : Prop :=
  if t = tagNe then ws.getD 0 0 ≠ ws.getD 1 0 else G.sem t rd ws

/-- The relation tagged `t` on words: `SemRel0`, or for a conditional tag (`impTag`, `2^32` and
above), `SemRel0` of its tag if its position's word is its immediate. -/
def SemRel (t : ℕ) (rd : Core.Reader) (ws : List E) : Prop :=
  if 2 ^ 32 ≤ t then
    ws.getD (impPos t) 0 = OffsetInstruction.immediateWord (impImm t) 0 → SemRel0 G (impBase t) rd ws
  else SemRel0 G t rd ws

/-- The words of each tagged tuple of cells are in the relation of its tag. -/
def SemHolds (fp : K) (sems : List (ℕ × List ℕ)) : Prop :=
  ∀ s ∈ sems, SemRel G s.1 L.read (s.2.map (wd L fp))

/-- **A function's precondition** at frame `fp`: it is one the program checks, the jump table
holds, its self frame pointer cells hold `fp`, its bounded frame cells and memory are bounded,
and its tagged tuples of cells are in their relations. -/
def Pre (j : ℕ) (fp : K) : Prop :=
  G.good j = true ∧ JTHolds G L ∧ EnvHolds L fp (envOf (G.sig j).env) ∧
    BndHolds L fp (G.sig j).pre ∧ MemPre L fp (G.sig j).mem ∧ SemHolds G L fp (G.sig j).sem

/-- **Function `j` was entered at frame `fp` on the run from `(g^0, 1)`**, on the argument words
`args` and the return words `rets` of the frame: the frame is in the memory, `j`'s precondition
holds there, and the run from `(g^0, 1)` reaches `j`'s entry at `fp`. The guest's located calls
run at such frames (`Post`, `RL P L cert (EnteredAt G L)`). -/
def EnteredAt (f : String) (fp : K) (args rets : List E) : Prop :=
  InMem κ fp ∧ ∃ j, (G.sig j).name = f ∧ Pre G L j fp ∧
    Reach guestProgram L ⟨addressOfIndex 0, 1⟩ ⟨addressOfIndex (G.sig j).entry, fp⟩ ∧
    frameWords L fp 2 (G.sig j).nargs = args ∧ frameWords L fp (2 + (G.sig j).nargs) (G.sig j).nret = rets

/-- **The body of `f` holds at frame `fp`** on the argument words `args` and the return words
`rets`: under the frame's valuation, its calls located at frames with `A`. -/
def BodyHoldsAt (cert : String → Cert) (A : String → K → List E → List E → Prop) (f : String) (fp : K)
    (args rets : List E) : Prop :=
  ∃ fn, P.find? f = some fn ∧ fn.params.map (frameVal L cert f fp) = args ∧
    Core.Stmt.HoldsList (RL P L cert A) L.read (frameVal L cert f fp) fn.body False
      (fun rs ↦ rs = rets)

/-- **A function's postcondition** at frame `fp`: its body holds at `fp` of the argument and return
words of the frame, its calls located at frames with `A`; `A` holds of `fp` and those words; and
its bounded frame cells are bounded. -/
def Post (cert : String → Cert) (A : String → K → List E → List E → Prop) (j : ℕ) (fp : K) : Prop :=
  BodyHoldsAt P L cert A (G.sig j).name fp (frameWords L fp 2 (G.sig j).nargs)
      (frameWords L fp (2 + (G.sig j).nargs) (G.sig j).nret) ∧
    A (G.sig j).name fp (frameWords L fp 2 (G.sig j).nargs)
      (frameWords L fp (2 + (G.sig j).nargs) (G.sig j).nret) ∧ BndHolds L fp (G.sig j).post

variable {P G L}

/-- A body holding at a frame with `A` is a located call. -/
theorem BodyHoldsAt.rl {cert : String → Cert} {A : String → K → List E → List E → Prop} {f : String} {fp : K}
    {args rets : List E} (h : BodyHoldsAt P L cert A f fp args rets) (hA : A f fp args rets) :
    RL P L cert A f args rets := by
  obtain ⟨fn, hf, hp, hb⟩ := h
  exact (Core.relL_iff P f args rets).mpr ⟨fn, fp, hf, hA, hp, hb⟩

/-- A postcondition gives the located call on the frame's words. -/
theorem Post.rl {cert : String → Cert} {A : String → K → List E → List E → Prop} {j : ℕ} {fp : K}
    (h : Post P G L cert A j fp) :
    RL P L cert A (G.sig j).name (frameWords L fp 2 (G.sig j).nargs)
      (frameWords L fp (2 + (G.sig j).nargs) (G.sig j).nret) :=
  h.1.rl h.2.1

/-- A postcondition's bounds. -/
theorem Post.bnd {cert : String → Cert} {A : String → K → List E → List E → Prop} {j : ℕ} {fp : K}
    (h : Post P G L cert A j fp) : BndHolds L fp (G.sig j).post :=
  h.2.2

end Contracts

/-! ## Positions of the walk -/

section Pos

variable {κ : ℕ} (L : MemoryImage κ) (fp : K) (f : CompiledFunction) (X : Fx)

/-- **The run is at a position** with `k` steps left, its segment entered with at most `K`: the
segment is the executor's, the book, environment and bounds hold, the rest of the segment's
items is run (`RunK`), its exits are the segment's, and a fresh position is the start of the
segment the index names. -/
structure PosOk (K : ℕ) (st : CS) (k : ℕ) : Prop where
  seg : st.seg ∈ X.segs
  book : BookHolds L fp st.book
  psi : EnvHolds L fp st.psi
  bnd : BndHolds L fp st.bnd
  run : ∃ k₀, k₀ ≤ K ∧ k ≤ k₀ ∧
    RunK L fp guestProgram f.entryPc k₀ (st.seg.exit.Reached L fp guestProgram f.entryPc k₀)
        st.its k
  exits : ∀ x, x = st.seg.exit ∨ x ∈ branchExits st.its → x ∈ st.seg.exits
  fresh : ∀ t, st.fresh = some t →
    X.idx.get t = some st.seg ∧ st.seg.start = t ∧ st.its = st.seg.items ∧ st.psi = st.seg.env ∧
      SafeReached guestProgram L k ⟨addressOfIndex (f.entryPc + t), fp⟩

/-- **The run is at the start of the segment at offset `t`**, with `k` steps left; at the
window's end, where no segment of it starts, in its environment `wenv`. -/
def SegRun (K t k : ℕ) : Prop :=
  SafeReached guestProgram L k ⟨addressOfIndex (f.entryPc + t), fp⟩ ∧
  (∀ s, X.idx.get t = some s → s.start = t → s ∈ X.segs ∧ EnvHolds L fp s.env ∧
    ∃ k₀, k₀ ≤ K ∧ k ≤ k₀ ∧
      RunK L fp guestProgram f.entryPc k₀ (s.exit.Reached L fp guestProgram f.entryPc k₀)
          s.items k) ∧
  (t = X.wJ → X.idx.get t = none → EnvHolds L fp X.wenv)

/-- At a window's end `J`, what it hands on holds. -/
def HandHolds (J : ℕ) : Prop :=
  ∀ J' fs bs, X.win = some (J', fs, bs) → J = J' →
    (∀ p ∈ fs, p.2.Holds L fp) ∧ BndHolds L fp bs

/-- **The run arrives at `t`**: at the start of the segment there, a window's hand-over in
place. -/
def Arrive (K t k : ℕ) : Prop := SegRun L fp f X K t k ∧ HandHolds L fp X t

end Pos

section PosLemmas

variable {κ : ℕ} {L : MemoryImage κ} {fp : K} {f : CompiledFunction} {X : Fx}

theorem fwdL_ok {test : Book → Bool} {e k₀ : ℕ} {Q : ℕ → Prop} :
    ∀ (its : List Exec.Item) (B : Book) (k : ℕ), BookHolds L fp B →
      RunK L fp guestProgram e k₀ Q its k →
      ∃ k' ≤ k, BookHolds L fp (fwdL test its B).2.1 ∧ RunK L fp guestProgram e k₀ Q (fwdL test its B).1 k' ∧
        ((fwdL test its B).2.2 = true → test (fwdL test its B).2.1 = true) ∧
        ∃ pre, pre ++ (fwdL test its B).1 = its
  | [], B, k, hB, h => ⟨k, le_rfl, hB, h, fun h ↦ h, [], rfl⟩
  | it :: its, B, k, hB, h => by
    unfold fwdL
    cases ht : test B
    · simp only [Bool.cond_false]
      cases it with
      | ins a =>
        simp only [Trie.seq_eq]
        obtain ⟨ha, k', rfl, h⟩ := h
        obtain ⟨k'', hk, hB', hr, hok, pre, hpre⟩ := fwdL_ok its _ k' (hB.addFact ha) h
        exact ⟨k'', by omega, hB', hr, hok, .ins a :: pre, by rw [List.cons_append, hpre]⟩
      | fact a =>
        simp only [Trie.seq_eq]
        obtain ⟨ha, h⟩ := h
        obtain ⟨k'', hk, hB', hr, hok, pre, hpre⟩ := fwdL_ok its _ k (hB.addFact ha) h
        exact ⟨k'', hk, hB', hr, hok, .fact a :: pre, by rw [List.cons_append, hpre]⟩
      | branch oc od of x =>
        exact ⟨k, le_rfl, hB, h, fun h ↦ by simp at h, [], rfl⟩
    · simp only [Bool.cond_true]
      exact ⟨k, le_rfl, hB, h, fun _ ↦ ht, [], rfl⟩

theorem exits_suffix {s : Exec.Seg} {its its' pre : List Exec.Item} (h : pre ++ its' = its)
    (hx : ∀ x, x = s.exit ∨ x ∈ branchExits its → x ∈ s.exits) :
    ∀ x, x = s.exit ∨ x ∈ branchExits its' → x ∈ s.exits := by
  intro x hx'
  refine hx x (hx'.imp id fun hm ↦ ?_)
  rw [← h, branchExits_append]
  exact List.mem_append_right _ hm

theorem fwd_eq (test : Book → Bool) (st : CS) : fwd test st =
    bif test st.book then (st, true)
    else match fwdL test st.its st.book with
      | (its, B, ok) => (⟨st.seg, its, B, st.psi, st.bnd, none⟩, ok) := by
  cases st
  rfl

theorem toEnd_eq (st : CS) : toEnd st =
    match fwdL (fun _ ↦ false) st.its st.book with
    | (its, B, _) => ⟨st.seg, its, B, st.psi, st.bnd, none⟩ := by
  cases st
  rfl

theorem fwd_ok {K : ℕ} {test : Book → Bool} {st : CS} {k : ℕ} (h : PosOk L fp f X K st k) :
    ∃ k' ≤ k, PosOk L fp f X K (fwd test st).1 k' ∧
      ((fwd test st).2 = true → test (fwd test st).1.book = true) ∧
      (fwd test st).1.seg = st.seg ∧ (fwd test st).1.psi = st.psi ∧
      (fwd test st).1.bnd = st.bnd := by
  rw [fwd_eq]
  cases ht : test st.book
  · simp only [Bool.cond_false]
    obtain ⟨k₀, hk₀, hk, hr⟩ := h.run
    obtain ⟨k', hk', hB, hr', hok, pre, hpre⟩ := fwdL_ok (test := test) st.its st.book k h.book hr
    refine ⟨k', hk', ⟨h.seg, hB, h.psi, h.bnd, ⟨k₀, hk₀, by omega, hr'⟩,
      exits_suffix hpre h.exits, fun t ht ↦ by simp at ht⟩, hok, by simp, by simp, by simp⟩
  · simp only [Bool.cond_true]
    exact ⟨k, le_rfl, h, fun _ ↦ ht, trivial, trivial, trivial⟩

theorem toEnd_ok {K : ℕ} {st : CS} {k : ℕ} (h : PosOk L fp f X K st k) :
    ∃ k' ≤ k, PosOk L fp f X K (toEnd st) k' ∧ (toEnd st).seg = st.seg ∧
      (toEnd st).psi = st.psi ∧ (toEnd st).bnd = st.bnd := by
  obtain ⟨k₀, hk₀, hk, hr⟩ := h.run
  obtain ⟨k', hk', hB, hr', -, pre, hpre⟩ :=
    fwdL_ok (test := fun _ ↦ false) st.its st.book k h.book hr
  refine ⟨k', hk', ⟨h.seg, hB, h.psi, h.bnd, ⟨k₀, hk₀, by omega, hr'⟩,
    exits_suffix hpre h.exits, fun t ht ↦ by simp [toEnd_eq] at ht⟩, by simp [toEnd_eq],
    by simp [toEnd_eq], by simp [toEnd_eq]⟩

/-- At the end of its segment, the run has reached the segment's exit. -/
theorem endAt_ok {K : ℕ} {st se : CS} {k : ℕ} (h : PosOk L fp f X K st k)
    (he : endAt st = some se) :
    ∃ k' ≤ k, PosOk L fp f X K se k' ∧ se.seg = st.seg ∧ se.psi = st.psi ∧ se.bnd = st.bnd ∧
      ∃ k₀ ≤ K, se.seg.exit.Reached L fp guestProgram f.entryPc k₀ k' := by
  obtain ⟨k', hk', hp, hs, hψ, hb⟩ := toEnd_ok h
  unfold endAt at he
  split at he
  · rename_i s B ψ bnd fr heq
    obtain rfl := Option.some.inj he
    rw [heq] at hp hs hψ hb
    obtain ⟨k₀, hk₀, -, hr⟩ := hp.run
    exact ⟨k', hk', hp, hs, hψ, hb, k₀, hk₀, hr⟩
  · simp at he

/-- At a branch, the run falls through when the condition cell is `0` and leaves by the
branch's exit otherwise. -/
theorem branchAt_ok {K : ℕ} {st st' : CS} {oc : ℕ} {x : Exec.Exit} {k : ℕ}
    (h : PosOk L fp f X K st k) (hb : branchAt st = some (st', oc, x)) :
    ∃ k' < k, ∃ c, L.read (fp * addressOfIndex oc) = some c ∧ IsInK c ∧ x ∈ st.seg.exits ∧
      st'.seg = st.seg ∧ st'.psi = st.psi ∧ st'.bnd = st.bnd ∧ BookHolds L fp st'.book ∧
      ((c = 0 ∧ PosOk L fp f X K st' k') ∨
        (c ≠ 0 ∧ ∃ k₀ ≤ K, x.Reached L fp guestProgram f.entryPc k₀ k')) := by
  obtain ⟨k₁, hk₁, hp, hs, hψ, hbd⟩ := toEnd_ok h
  unfold branchAt at hb
  split at hb
  · rename_i s oc' od of x' its B ψ bnd fr heq
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl, rfl⟩ := hb
    rw [heq] at hp hs hψ hbd
    obtain ⟨k₀, hk₀, hkk, hr⟩ := hp.run
    obtain ⟨⟨c, d, f', hc, -, -, hcK, -, -⟩, k', rfl, hr⟩ := hr
    have hx : x' ∈ s.exits := hp.exits x' (Or.inr (by simp [branchExits]))
    refine ⟨k', by omega, c, hc, hcK, hs ▸ hx, hs, hψ, hbd, hp.book, ?_⟩
    rcases hr with ⟨hc0, hr⟩ | ⟨⟨v, hv, hv0⟩, hr⟩
    · left
      refine ⟨Option.some.inj (hc.symm.trans hc0), hp.seg, hp.book, hp.psi, hp.bnd,
        ⟨k₀, hk₀, by omega, hr⟩, fun y hy ↦ hp.exits y ?_, fun t ht ↦ by simp at ht⟩
      rcases hy with rfl | hy
      · exact Or.inl rfl
      · exact Or.inr (by simp only [branchExits]; exact List.mem_cons_of_mem _ hy)
    · right
      obtain rfl := Option.some.inj (hc.symm.trans hv)
      exact ⟨hv0, k₀, hk₀, hr⟩
  · simp at hb

end PosLemmas

/-! ## Segments -/

section Segs

variable {κ : ℕ} {L : MemoryImage κ} {fp : K} {f : CompiledFunction} {X : Fx}

/-- What a walk assumes of its context: the executor's facts hold of the frame, the code is the
program's, the segments are good (an executor's, `exec_good`, `execWin_good`), and the index and
links are theirs. -/
structure WalkHyp (L : MemoryImage κ) (fp : K) (f : CompiledFunction) (X : Fx) : Prop where
  ctx : Exec.Ctx X.F κ fp
  fetch : Fetches guestProgram f.entryPc f.code
  entry : X.entry = f.entryPc
  good : ∀ s ∈ X.segs, SegGood L fp guestProgram f.entryPc s
  idx : X.idx = index X.segs
  linked : linkedWeak X.idx X.segs X.wJ X.wenv = true

theorem linkedWeak_get {idx : Trie Exec.Seg} {segs : List Exec.Seg} {wJ : ℕ} {wenv : Trie Sym}
    (hl : linkedWeak idx segs wJ wenv = true)
    {s : Exec.Seg} (hs : s ∈ segs) {x : Exec.Exit} (hx : x ∈ s.exits) {t : ℕ} (ht : t ∈ x.succ)
    {s' : Exec.Seg} (h : idx.get t = some s') : s'.start = t ∧ s'.env.sub Sym.beq x.env = true := by
  simp only [linkedWeak, List.all_eq_true] at hl
  have := hl s hs x hx t ht
  rw [getF_eq, h] at this
  simpa using this

theorem linkedWeak_none {idx : Trie Exec.Seg} {segs : List Exec.Seg} {wJ : ℕ} {wenv : Trie Sym}
    (hl : linkedWeak idx segs wJ wenv = true)
    {s : Exec.Seg} (hs : s ∈ segs) {x : Exec.Exit} (hx : x ∈ s.exits) (ht : wJ ∈ x.succ)
    (h : idx.get wJ = none) : wenv.sub Sym.beq x.env = true := by
  simp only [linkedWeak, List.all_eq_true] at hl
  have := hl s hs x hx wJ ht
  rw [getF_eq, h] at this
  simpa using this

/-- A run entering offset `t`, a successor of an exit whose environment holds, is at the start
of the segment there. -/
theorem segRun_of_safe (H : WalkHyp L fp f X) {s : Exec.Seg} (hs : s ∈ X.segs)
    {x : Exec.Exit} (hx : x ∈ s.exits) {t : ℕ} (ht : t ∈ x.succ) (he : EnvHolds L fp x.env)
    {K k : ℕ} (hk : k ≤ K) (h : SafeReached guestProgram L k ⟨addressOfIndex (f.entryPc + t), fp⟩) :
    SegRun L fp f X K t k := by
  refine ⟨h, fun s' hs' hst ↦ ?_, fun htJ hn ↦ ?_⟩
  swap
  · subst htJ
    exact he.sub (linkedWeak_none H.linked hs hx ht hn)
  have hl := linkedWeak_get H.linked hs hx ht hs'
  have hmem : s' ∈ X.segs := by
    rw [H.idx] at hs'
    exact index_get hs'
  have he' := he.sub hl.2
  refine ⟨hmem, he', k, hk, le_rfl, ?_⟩
  exact (H.good s' hmem).1 k he' (by rw [hst]; exact h)

/-- A local jump to `t` leaves into the segment at `t`. -/
theorem segRun_of_next (H : WalkHyp L fp f X) {s : Exec.Seg} (hs : s ∈ X.segs)
    {x : Exec.Exit} (hx : x ∈ s.exits) {t : ℕ} (hk : x.kind = .next t) (ht : x.succ = [t])
    {K k₀ k : ℕ} (hk₀ : k₀ ≤ K) (h : x.Reached L fp guestProgram f.entryPc k₀ k) :
    SegRun L fp f X K t k := by
  obtain ⟨hlt, he, -, r, hr, hsafe⟩ := h
  rw [hk] at hr
  simp only [Kind.Regs] at hr
  subst hr
  exact segRun_of_safe H hs hx (by simp [ht]) he (by omega) hsafe

theorem segAt_ok (H : WalkHyp L fp f X) {t : ℕ} {B : Book} {bnd : List (ℕ × ℕ)} {st : CS}
    (h : segAt X t B bnd = some st) {K k : ℕ} (hr : SegRun L fp f X K t k)
    (hB : BookHolds L fp B) (hb : BndHolds L fp bnd) : PosOk L fp f X K st k := by
  unfold segAt at h
  split at h
  · rename_i s hs
    rw [getF_eq] at hs
    simp only [Bool.cond_eq_ite, beq_iff_eq] at h
    split_ifs at h with hst
    obtain rfl := Option.some.inj h
    obtain ⟨hmem, he, k₀, hk₀, hk, hrun⟩ := hr.2.1 s hs hst
    exact ⟨hmem, hB, he, hb, ⟨k₀, hk₀, hk, hrun⟩,
      fun x hx ↦ (H.good s hmem).2.2 x hx, fun t' ht' ↦ by
        obtain rfl := Option.some.inj ht'
        exact ⟨hs, hst, rfl, rfl, hr.1⟩⟩
  · simp at h

theorem PosOk.segRun {K : ℕ} {st : CS} {k : ℕ} (h : PosOk L fp f X K st k) {t : ℕ}
    (ht : st.fresh = some t) : SegRun L fp f X K t k := by
  obtain ⟨hi, hs, hits, hψ, hsafe⟩ := h.fresh t ht
  refine ⟨hsafe, fun s hs' _ ↦ ?_, fun _ hn ↦ by rw [hi] at hn; cases hn⟩
  obtain rfl := Option.some.inj (hi.symm.trans hs')
  obtain ⟨k₀, hk₀, hk, hr⟩ := h.run
  exact ⟨h.seg, hψ ▸ h.psi, k₀, hk₀, hk, hits ▸ hr⟩

/-- Where a block ends, the run is at the start of that segment. -/
theorem endOf_ok (H : WalkHyp L fp f X) {K : ℕ} {st se : CS} {k J : ℕ} (h : PosOk L fp f X K st k)
    (he : endOf st = some (J, se)) :
    ∃ k' ≤ k, PosOk L fp f X K se k' ∧ SegRun L fp f X K J k' := by
  unfold endOf at he
  split at he
  · rename_i t ht
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨k, le_rfl, h, h.segRun ht⟩
  · split at he
    · rename_i se' hse
      split at he
      · rename_i t hkind
        simp only [Bool.cond_eq_ite, beq_iff_eq] at he
        split_ifs at he with hsucc
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨k', hk', hp, hs, -, -, k₀, hk₀, hr⟩ := endAt_ok h hse
        exact ⟨k', hk', hp, segRun_of_next H hp.seg (hp.exits _ (Or.inl rfl)) hkind hsucc hk₀ hr⟩
      · simp at he
    · simp at he

end Segs

/-! ## Inverting the walk -/

section Inv

variable {X : Fx}

theorem chkL_nil (st : CS) (P : List Core.Atom) : chkL X [] st P = blockEnd X st P := by
  simp only [chkL]

theorem chkL_atom (a : Core.Atom) (ss : List Core.Stmt) (st : CS) (P : List Core.Atom) :
    chkL X (.atom a :: ss) st P =
      match fwd (fun B ↦ atomOk X.F B st.psi X.loc a) st with
      | (st', true) => chkL X ss st' P
      | (st', false) => chkL X ss st' (a :: P) := by
  simp only [chkL, LAtom.seq_eq, atomOkL_locate]
  split <;> (rename_i heq; simp only [CS.seq_eq, heq])

theorem chkL_ite {c : Core.V} {z n ss : List Core.Stmt} {st : CS} {P : List Core.Atom}
    (h : chkL X (.ite c z n :: ss) st P ≠ .fail) :
    ∃ st' x t sn J sj, branchAt st = some (st', cellOf X.loc c, x) ∧ x.kind = .next t ∧
      x.succ = [t] ∧ segAt X t st'.book st'.bnd = some sn ∧ chkL X z st' [] = .join J ∧
      chkL X n sn [] = .join J ∧ segAt X J st'.book st'.bnd = some sj ∧
      chkL X (.ite c z n :: ss) st P = chkL X ss sj P := by
  revert h
  simp only [chkL]
  split
  · rename_i st' oc x hb
    split
    · rename_i t hk
      simp only [Bool.cond_eq_ite, Bool.and_eq_true, beq_iff_eq]
      split_ifs with hc
      · split
        · rename_i sn hsn
          split
          · rename_i J J' hz hn
            split_ifs with hJ
            · subst hJ
              split
              · rename_i sj hsj
                intro _
                exact ⟨st', x, t, sn, J, sj, by rw [hb, hc.1], hk, hc.2, hsn, hz, hn, hsj, rfl⟩
              · simp
            · simp
          · simp
        · simp
      · simp
    · simp
  · simp

theorem chkL_match {v : Core.V} {arms : List (List Core.Stmt)} {ss : List Core.Stmt} {st : CS}
    {P : List Core.Atom} (h : chkL X (.match_ v arms :: ss) st P ≠ .fail) :
    ∃ se t ft t0 ts a0 as base s0, endAt st = some se ∧
      se.seg.exit.kind = .jump (.cell t) ft ∧ se.seg.exit.succ = t0 :: ts ∧ arms = a0 :: as ∧
      X.F.self ft = true ∧ ts.length = as.length ∧
      boundOk X.F se.psi X.mem se.book se.bnd (cellOf X.loc v) (as.length + 1) = true ∧
      tableBase se.book t (cellOf X.loc v) = some base ∧
      armsOk X.G X.entry base 0 (t0 :: ts) = true ∧ segAt X t0 se.book se.bnd = some s0 ∧
      ((∃ J sj, chkL X a0 s0 [] = .join J ∧ chkArms X (.join J) as ts se.book se.bnd = true ∧
          segAt X J se.book se.bnd = some sj ∧ chkL X (.match_ v arms :: ss) st P = chkL X ss sj P) ∨
        (∃ x succ, chkL X a0 s0 [] = .chain x succ ∧
          chkArms X (.chain x succ) as ts se.book se.bnd = true ∧
          chkL X (.match_ v arms :: ss) st P =
            chainTo x succ ss P (chainL X x succ se.book se.psi se.bnd ss P))) := by
  revert h
  simp only [chkL]
  split
  · rename_i se hse
    split
    · rename_i t ft t0 ts a0 as hk hs
      simp only [Bool.cond_eq_ite, Bool.and_eq_true, beq_iff_eq]
      split_ifs with hc
      · split
        · rename_i base hb
          split_ifs with ha
          · split
            · rename_i s0 hs0
              split
              · rename_i J hJ
                split_ifs with harms
                · split
                  · rename_i sj hsj
                    intro _
                    exact ⟨se, t, ft, t0, ts, a0, as, base, s0, hse, hk, hs, rfl, hc.1.1,
                      hc.1.2, hc.2, hb, ha, hs0, Or.inl ⟨J, sj, hJ, harms, hsj, rfl⟩⟩
                  · simp
                · simp
              · rename_i x succ hJ
                split_ifs with harms
                · intro _
                  exact ⟨se, t, ft, t0, ts, a0, as, base, s0, hse, hk, hs, rfl, hc.1.1,
                    hc.1.2, hc.2, hb, ha, hs0, Or.inr ⟨x, succ, hJ, harms, rfl⟩⟩
                · simp
              · simp
            · simp
          · simp
        · simp
      · simp
    · simp
  · simp

/-- A chained `match` from its arms: its selector cell, each arm from its offset, all ending
alike, and the walk after it. -/
theorem chainL_match {x : ℕ} {succ : List ℕ} {B : Book} {ψ : Trie Sym} {bnd : List (ℕ × ℕ)}
    {v : Core.V} {arms : List (List Core.Stmt)} {ss : List Core.Stmt} {P : List Core.Atom}
    (h : chainL X x succ B ψ bnd (.match_ v arms :: ss) P ≠ .fail) :
    ∃ t0 ts a0 as s0, succ = t0 :: ts ∧ arms = a0 :: as ∧ cellOf X.loc v = x ∧
      ts.length = as.length ∧ segAt X t0 B bnd = some s0 ∧
      ((∃ J sj, chkL X a0 s0 [] = .join J ∧ chkArms X (.join J) as ts B bnd = true ∧
          segAt X J B bnd = some sj ∧ chainL X x succ B ψ bnd (.match_ v arms :: ss) P = chkL X ss sj P) ∨
        (∃ x' succ', chkL X a0 s0 [] = .chain x' succ' ∧
          chkArms X (.chain x' succ') as ts B bnd = true ∧
          chainL X x succ B ψ bnd (.match_ v arms :: ss) P =
            chainTo x' succ' ss P (chainL X x' succ' B ψ bnd ss P))) := by
  generalize hr : chainL X x succ B ψ bnd (.match_ v arms :: ss) P = r at h ⊢
  unfold chainL at hr
  split at hr
  · rename_i t0 ts a0 as
    simp only [Bool.cond_eq_ite, Bool.and_eq_true, beq_iff_eq] at hr
    split_ifs at hr with hc
    · split at hr
      · rename_i s0 hs0
        split at hr
        · rename_i J hJ
          split_ifs at hr with harms
          · split at hr
            · rename_i sj hsj
              exact ⟨t0, ts, a0, as, s0, rfl, rfl, hc.1, hc.2, hs0,
                Or.inl ⟨J, sj, hJ, harms, hsj, hr.symm⟩⟩
            · exact absurd hr.symm h
          · exact absurd hr.symm h
        · rename_i x' succ' hJ
          split_ifs at hr with harms
          · exact ⟨t0, ts, a0, as, s0, rfl, rfl, hc.1, hc.2, hs0,
              Or.inr ⟨x', succ', hJ, harms, hr.symm⟩⟩
          · exact absurd hr.symm h
        · exact absurd hr.symm h
      · exact absurd hr.symm h
    · exact absurd hr.symm h
  · exact absurd hr.symm h

theorem chkL_call {f : String} {args rets : List Core.V} {ss : List Core.Stmt} {st : CS}
    {P : List Core.Atom} (h : chkL X (.call f args rets :: ss) st P ≠ .fail) :
    ∃ se e q r j st', endAt st = some se ∧ se.seg.exit.kind = .call (.gp e) q r ∧
      calleeAt X e = some j ∧
      callOk X se.book se.psi se.bnd (fun _ _ ↦ false) (X.G.sig j) f q (cellsOf X.loc args)
        rets.length = true ∧
      X.entry ≤ r ∧ se.seg.exit.succ = [r - X.entry] ∧
      afterCall X (r - X.entry) q (2 + args.length) (cellsOf X.loc rets) se.book se.bnd = some st' ∧
      chkL X (.call f args rets :: ss) st P = chkL X ss ⟨st'.seg, st'.its, st'.book, st'.psi,
        postBnd (cellsOf X.loc args ++ cellsOf X.loc rets) (X.G.sig j).post ++ st'.bnd,
        st'.fresh⟩ P := by
  revert h
  simp only [chkL]
  split
  · rename_i se hse
    split
    · rename_i e q r hk
      split
      · rename_i j hj
        simp only [Bool.cond_eq_ite, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq]
        split_ifs with hc
        · split
          · rename_i st' hst
            intro _
            exact ⟨se, e, q, r, j, st', hse, hk, hj, hc.1.1, hc.1.2, hc.2, hst,
              by simp only [CS.seq_eq]⟩
          · simp
        · simp
      · simp
    · simp
  · simp

theorem chkL_dispatch {v : Core.V} {fs : List String} {args rets : List Core.V}
    {ss : List Core.Stmt} {st : CS} {P : List Core.Atom}
    (h : chkL X (.dispatch v fs args rets :: ss) st P ≠ .fail) :
    ∃ se t q r base st', endAt st = some se ∧ se.seg.exit.kind = .call (.cell t) q r ∧
      tableBase se.book t (cellOf X.loc v) = some base ∧
      boundOk X.F se.psi X.mem se.book se.bnd (cellOf X.loc v) fs.length = true ∧ X.entry ≤ r ∧
      se.seg.exit.succ = [r - X.entry] ∧
      tableCallsOk X base (fun f s ↦ callOk X se.book se.psi se.bnd (fun _ _ ↦ false) s f q
        (cellsOf X.loc args) rets.length && s.post.isEmpty) 0 fs = true ∧
      afterCall X (r - X.entry) q (2 + args.length) (cellsOf X.loc rets) se.book se.bnd = some st' ∧
      chkL X (.dispatch v fs args rets :: ss) st P = chkL X ss st' P := by
  revert h
  simp only [chkL]
  split
  · rename_i se hse
    split
    · rename_i t q r hk
      split
      · rename_i base hb
        simp only [Bool.cond_eq_ite, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq]
        split_ifs with hc
        · split
          · rename_i st' hst
            intro _
            exact ⟨se, t, q, r, base, st', hse, hk, hb, hc.1.1.1, hc.1.1.2, hc.1.2, hc.2, hst,
              by simp only [CS.seq_eq]⟩
          · simp
        · simp
      · simp
    · simp
  · simp

theorem chkL_callIf {c : Core.V} {f : String} {args : List Core.V} {ss : List Core.Stmt}
    {st : CS} {P : List Core.Atom} (h : chkL X (.callIf c f args :: ss) st P ≠ .fail) :
    ∃ st' x, branchAt st = some (st', cellOf X.loc c, x) ∧
      ((∃ e q r j se sr, x.kind = .call (.gp e) q r ∧ calleeAt X e = some j ∧
        callOk X st'.book st'.psi st'.bnd (neAt st'.book (cellOf X.loc c)) (X.G.sig j) f q
          (cellsOf X.loc args) 0 = true ∧
        (X.G.sig j).post = [] ∧ X.entry ≤ r ∧ x.succ = [r - X.entry] ∧
        endOf st' = some (r - X.entry, se) ∧ segAt X (r - X.entry) st'.book st'.bnd = some sr ∧
        chkL X (.callIf c f args :: ss) st P = chkL X ss sr P) ∨
      (∃ e S j, x.kind = .jump (.gp e) (.fpg S) ∧ calleeAt X e = some j ∧ ss = [.ret []] ∧
        tailOk X st' x (cellOf X.loc c) S (X.G.sig j) f (cellsOf X.loc args) P = true ∧
        chkL X (.callIf c f args :: ss) st P = .done)) := by
  revert h
  simp only [chkL]
  split
  · rename_i st' oc x hb
    simp only [Bool.cond_eq_ite, beq_iff_eq]
    split_ifs with hc
    · subst hc
      split
      · rename_i e q r hk
        split
        · rename_i j hj
          simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq, List.isEmpty_iff]
          split_ifs with hc'
          · split
            · rename_i t se sr he hsr
              split_ifs with ht
              · subst ht
                intro _
                exact ⟨st', x, hb, Or.inl ⟨e, q, r, j, se, sr, hk, hj, hc'.1.1.1, hc'.1.1.2,
                  hc'.1.2, hc'.2, he, hsr, rfl⟩⟩
              · simp
            · simp
          · simp
        · simp
      · rename_i e S hk
        split
        · rename_i j hj
          split_ifs with ht
          · intro _
            exact ⟨st', x, hb, Or.inr ⟨e, S, j, hk, hj, rfl, ht, rfl⟩⟩
          · simp
        · simp
      · simp
    · simp
  · simp

theorem chkL_ret {vs : List Core.V} {ss : List Core.Stmt} {st : CS} {P : List Core.Atom}
    (h : chkL X (.ret vs :: ss) st P ≠ .fail) :
    retOk X vs st P = true ∧ chkL X (.ret vs :: ss) st P = .done := by
  revert h
  simp only [chkL, Bool.cond_eq_ite]
  split_ifs with h
  · exact fun _ ↦ ⟨h, rfl⟩
  · simp

theorem blockEnd_join {st : CS} {P : List Core.Atom} (h : blockEnd X st P ≠ .fail) :
    (∃ J se, endOf st = some (J, se) ∧ pendOk X se P = true ∧ handOk X J se = true ∧
      blockEnd X st P = .join J) ∨ (endOf st = none ∧ blockEnd X st P = chainEnd X st P) := by
  revert h
  unfold blockEnd
  split
  · rename_i J se he
    simp only [Bool.cond_eq_ite, Bool.and_eq_true]
    split_ifs with hp
    · exact fun _ ↦ Or.inl ⟨J, se, he, hp.1, hp.2, rfl⟩
    · simp
  · rename_i he
    exact fun _ ↦ Or.inr ⟨he, rfl⟩

theorem chainEnd_dec {st : CS} {P : List Core.Atom} (h : chainEnd X st P ≠ .fail) :
    ∃ se t ft t0 ts x base, endAt st = some se ∧ se.seg.exit.kind = .jump (.cell t) ft ∧
      se.seg.exit.succ = t0 :: ts ∧ tableSrc se.book t = some (x, base) ∧ X.F.self ft = true ∧
      armsOk X.G X.entry base 0 (t0 :: ts) = true ∧
      boundOk X.F se.psi X.mem se.book se.bnd x (ts.length + 1) = true ∧ pendOk X se P = true ∧
      handOk X t0 se = true ∧ (t0 = X.wJ → X.wenv.sub Sym.beq se.seg.exit.env = true) ∧
      chainEnd X st P = .chain x (t0 :: ts) := by
  revert h
  unfold chainEnd
  split
  · rename_i se hse
    split
    · rename_i t ft t0 ts hk hs
      split
      · rename_i x base hsrc
        cases hc : chainOk X se ft t0 ts x base P
        · simp
        · intro _
          simp only [chainOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
            beq_eq_false_iff_ne] at hc
          obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
          refine ⟨se, t, ft, t0, ts, x, base, hse, hk, hs, hsrc, h1, h2, h3, h4, h5, fun hw ↦ ?_, rfl⟩
          rcases h6 with h6 | h6
          · exact absurd hw h6
          · exact h6
      · simp
    · simp
  · simp

end Inv

/-! ## Calls and tables -/

section Calls

variable {κ : ℕ} {L : MemoryImage κ} {fp : K} {B : Book}

theorem storesOk_sound (hB : BookHolds L fp B) {q : ℕ} :
    ∀ {o : ℕ} {cs : List ℕ}, storesOk B q o cs = true → ∀ i (hi : i < cs.length),
      ∃ pv, L.read (fp * addressOfIndex q) = some pv ∧ IsInK pv ∧
        ∃ v, L.read (fp * addressOfIndex cs[i]) = some v ∧ L.read (pv.limb 0 * addressOfIndex (o +
            i)) = some v
  | _, [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | o, c :: cs, h, i, hi => by
    simp only [storesOk, Bool.and_eq_true] at h
    cases i with
    | zero => simpa using loadOk_sound hB h.1
    | succ i =>
      obtain ⟨pv, h1, hK, v, h2, h3⟩ := storesOk_sound hB h.2 i (by simpa using hi)
      exact ⟨pv, h1, hK, v, by simpa using h2, by rw [show o + (i + 1) = o + 1 + i by omega]; exact h3⟩

/-- Stored cells are the callee frame's words. -/
theorem storesOk_words (hB : BookHolds L fp B) {q o : ℕ} {cs : List ℕ} (h : storesOk B q o cs = true)
    {pv : E} (hq : L.read (fp * addressOfIndex q) = some pv) :
    cs.map (wd L fp) = frameWords L (pv.limb 0) o cs.length := by
  apply List.ext_getElem (by simp [frameWords])
  intro i h1 h2
  simp only [List.getElem_map, frameWords, List.getElem_range]
  obtain ⟨pv', hq', -, v, h3, h4⟩ := storesOk_sound hB h i (by simpa using h1)
  obtain rfl := Option.some.inj (hq'.symm.trans hq)
  rw [wd_of h3, wd_of h4]

theorem map_val (loc : Trie ℕ) (vs : List Core.V) :
    vs.map (val L fp loc) = (cellsOf loc vs).map (wd L fp) := by
  simp [cellsOf, val, Function.comp_def]

theorem envOf_holds {env : List (ℕ × Sym)}
    (h : ∀ p ∈ env, L.read (fp * addressOfIndex p.1) = some (p.2.val fp)) : EnvHolds L fp (envOf
        env) := by
  unfold envOf
  suffices ∀ (l : List (ℕ × Sym)) (t : Trie Sym), EnvHolds L fp t → (∀ p ∈ l, L.read (fp * addressOfIndex p.1) = some (p.2.val fp)) →
      EnvHolds L fp (l.foldl (fun t p ↦ t.set p.2 envDepth p.1) t) from this env .nil EnvHolds.nil h
  intro l
  induction l with
  | nil => exact fun _ ht _ ↦ ht
  | cons p l ih =>
    intro t ht hl
    exact ih _ (ht.set (hl p List.mem_cons_self)) fun p' hp' ↦ hl p' (List.mem_cons_of_mem _ hp')

theorem envStoresOk_sound (hB : BookHolds L fp B) {q : ℕ} {env : List (ℕ × Sym)}
    (h : envStoresOk B q env = true) {pv : E} (hq : L.read (fp * addressOfIndex q) = some pv)
    (hK : IsInK pv) : EnvHolds L (pv.limb 0) (envOf env) := by
  apply envOf_holds
  intro p hp
  have := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true] at this
  obtain ⟨hs, hl⟩ := this
  rw [Sym.beq_eq hs]
  obtain ⟨pv', hq', -, v, h1, h2⟩ := loadOk_sound hB hl
  obtain rfl := Option.some.inj (hq'.symm.trans hq)
  obtain rfl := Option.some.inj (h1.symm.trans hq')
  rw [h2]
  simp only [Sym.val, gpow_zero', mul_one]
  exact congrArg some (inK_eq hK)

/-! ### Selectors bounded by booleanity -/

/-- The bits of `1 + g^k`, `1 ≤ k ≤ 63`: `x^k + 1`, `g` being the polynomial `x`. -/
theorem ofBits_onePlusPow : ∀ k < 63, K.ofBits (2 ^ (k + 1) + 1) = 1 + addressOfIndex (k + 1) := by
  decide +kernel

theorem onePlusPow_spec {k0 k : ℕ} (h : onePlusPow k0 = some k) :
    K.ofBits k0 = 1 + addressOfIndex k := by
  obtain ⟨i, hi, hk⟩ := List.exists_of_findSome?_eq_some h
  simp only [Bool.cond_eq_ite, beq_iff_eq] at hk
  split_ifs at hk with he
  obtain rfl := Option.some.inj hk
  rw [← he]
  exact ofBits_onePlusPow i (List.mem_range.mp hi)

theorem orOpt_eq_some {α : Type} {a b : Option α} {x : α} (h : orOpt a b = some x) :
    a = some x ∨ b = some x := by
  cases a with
  | some a => exact .inl h
  | none => exact .inr h

theorem optIf_eq_some {α : Type} {p : Bool} {o : Option α} {x : α} (h : optIf p o = some x) :
    p = true ∧ o = some x := by
  cases p with
  | true => exact ⟨rfl, h⟩
  | false => exact absurd h (by simp [optIf])

theorem selConst_sound (hB : BookHolds L fp B) {q k : ℕ} (h : selConst B q = some k) :
    L.read (fp * addressOfIndex q) = some (ofK (1 + addressOfIndex k)) := by
  obtain ⟨a, ha, hp⟩ := List.exists_of_findSome?_eq_some h
  have hh := hB q a ha
  split at hp
  · rename_i pc o k0 k1
    obtain ⟨ho, hq⟩ := optIf_eq_some hp
    simp only [Bool.and_eq_true, beq_iff_eq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    rw [hh, imm_of_ofBits (onePlusPow_spec hq)]
  · simp at hp

/-- A cell of a `MUL b = b·b` holds `0` or `1`. -/
theorem boolCell_sound (hB : BookHolds L fp B) {b : ℕ} (h : mulOk B b b b = true) :
    ∃ v, L.read (fp * addressOfIndex b) = some v ∧ (v = 0 ∨ v = 1) := by
  obtain ⟨vA, vB, h1, h2, h3⟩ := mulOk_sound hB h
  obtain rfl := Option.some.inj (h1.symm.trans h2)
  have hv : vA * vA = vA := (Option.some.inj (h1.symm.trans h3)).symm
  exact ⟨vA, h1, IsIdempotentElem.iff_eq_zero_or_one.mp hv⟩

theorem boolScaled_sound (hB : BookHolds L fp B) {u k : ℕ} (h : boolScaled B u = some k) :
    ∃ v, L.read (fp * addressOfIndex u) = some v ∧ (v = 0 ∨ v = ofK (1 + addressOfIndex k)) := by
  obtain ⟨a, ha, hp⟩ := List.exists_of_findSome?_eq_some h
  have hh := hB u a ha
  split at hp
  · rename_i pc x y z
    obtain ⟨hz, hq⟩ := optIf_eq_some hp
    obtain rfl : z = u := beq_iff_eq.mp hz
    obtain ⟨vX, vY, hx, hy, hu⟩ := hh
    have key : ∀ {p q : ℕ} {vp vq : E}, L.read (fp * addressOfIndex p) = some vp →
        L.read (fp * addressOfIndex q) = some vq → mulOk B p p p = true → selConst B q = some k →
        vp * vq = 0 ∨ vp * vq = ofK (1 + addressOfIndex k) := by
      intro p q vp vq hp' hq' hb hc
      obtain ⟨v, hv, hv01⟩ := boolCell_sound hB hb
      obtain rfl := Option.some.inj (hp'.symm.trans hv)
      obtain rfl := Option.some.inj (hq'.symm.trans (selConst_sound hB hc))
      rcases hv01 with rfl | rfl
      · exact .inl (zero_mul _)
      · exact .inr (one_mul _)
    refine ⟨_, hu, ?_⟩
    rcases orOpt_eq_some hq with hq | hq
    · obtain ⟨hb, hc⟩ := optIf_eq_some hq
      exact key hx hy hb hc
    · obtain ⟨hb, hc⟩ := optIf_eq_some hq
      rw [mul_comm]
      exact key hy hx hb hc
  · simp at hp

theorem boolSel_sound (hB : BookHolds L fp B) {c n : ℕ} (h : boolSel B c = some n) :
    ∃ e < n, L.read (fp * addressOfIndex c) = some (ofK (addressOfIndex e)) := by
  obtain ⟨a, ha, hp⟩ := List.exists_of_findSome?_eq_some h
  have hh := hB c a ha
  split at hp
  · rename_i pc x y z
    obtain ⟨hz, hq⟩ := optIf_eq_some hp
    obtain rfl : z = c := beq_iff_eq.mp hz
    obtain ⟨vX, vY, hx, hy, hc⟩ := hh
    have hone : OffsetInstruction.immediateWord 1 0 = 1 := (imm_of_ofBits rfl).trans ofK_one
    have key : ∀ {p q : ℕ} {vp vq : E} {k : ℕ}, L.read (fp * addressOfIndex p) = some vp →
        L.read (fp * addressOfIndex q) = some vq → setImm B p 1 0 = true → boolScaled B q =
            some k →
        ∃ e < k + 1, vp + vq = ofK (addressOfIndex e) := by
      intro p q vp vq k hp' hq' h1 hs
      obtain rfl := Option.some.inj (hp'.symm.trans ((setImm_sound hB h1).trans (by rw [hone])))
      obtain ⟨v, hv, hv0⟩ := boolScaled_sound hB hs
      obtain rfl := Option.some.inj (hq'.symm.trans hv)
      rcases hv0 with rfl | rfl
      · exact ⟨0, by omega, by rw [add_zero, gpow_zero', ofK_one]⟩
      · refine ⟨k, by omega, ?_⟩
        rw [ofK_add, ofK_one, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hq
    rcases orOpt_eq_some hk with hk | hk
    · obtain ⟨h1, hs⟩ := optIf_eq_some hk
      obtain ⟨e, he, hs⟩ := key hx hy h1 hs
      exact ⟨e, he, by rw [hc, hs]⟩
    · obtain ⟨h1, hs⟩ := optIf_eq_some hk
      obtain ⟨e, he, hs⟩ := key hy hx h1 hs
      exact ⟨e, he, by rw [hc, add_comm, hs]⟩
  · simp at hp

/-- **A selector bounded by booleanity** is `g^e` with `e` below the bound `selBound` finds. -/
theorem selBound_sound (hB : BookHolds L fp B) :
    ∀ (fuel : ℕ) {c n : ℕ}, selBound B fuel c = some n →
      ∃ e < n, L.read (fp * addressOfIndex c) = some (ofK (addressOfIndex e))
  | 0, _, _, h => boolSel_sound hB h
  | fuel + 1, c, n, h => by
    rcases orOpt_eq_some h with h | h
    · exact boolSel_sound hB h
    · obtain ⟨a, ha, hp⟩ := List.exists_of_findSome?_eq_some h
      have hh := hB c a ha
      split at hp
      · rename_i pc x y z
        obtain ⟨hz, hq⟩ := optIf_eq_some hp
        obtain rfl : z = c := beq_iff_eq.mp hz
        cases h₁ : selBound B fuel x with
        | none => rw [h₁] at hq; exact absurd hq (by simp)
        | some n₁ =>
          cases h₂ : selBound B fuel y with
          | none => rw [h₁, h₂] at hq; exact absurd hq (by simp)
          | some n₂ =>
            rw [h₁, h₂] at hq
            obtain rfl := Option.some.inj hq
            obtain ⟨e₁, he₁, hx⟩ := selBound_sound hB fuel h₁
            obtain ⟨e₂, he₂, hy⟩ := selBound_sound hB fuel h₂
            obtain ⟨vX, vY, hx', hy', hc⟩ := hh
            obtain rfl := Option.some.inj (hx'.symm.trans hx)
            obtain rfl := Option.some.inj (hy'.symm.trans hy)
            exact ⟨e₁ + e₂, by omega, by rw [hc, ofK_gpow_mul]⟩
      · simp at hp

/-- Memory read through frame cells is bounded: for each `(o, c, n)`, a word read at `fp[o]·g^c`
is `g^e` with `e < n` (`Cut.knownIf`; what `MemPre` and `MemKnown` give, `memIf_of_pre`,
`memIf_of_known`). -/
def MemIf (L : MemoryImage κ) (fp : K) (mem : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ m ∈ mem, ∀ v, Core.LoadHolds L.read (wd L fp m.1) m.2.1 v → ∃ e < m.2.2, v = ofK (addressOfIndex e)

theorem MemIf.append {l₁ l₂ : List (ℕ × ℕ × ℕ)} (h₁ : MemIf L fp l₁) (h₂ : MemIf L fp l₂) :
    MemIf L fp (l₁ ++ l₂) := by
  intro m hm
  rcases List.mem_append.mp hm with hm | hm
  · exact h₁ m hm
  · exact h₂ m hm

theorem memIf_of_pre {mem : List (ℕ × ℕ × ℕ)} (h : MemPre L fp mem) : MemIf L fp mem := by
  intro m hm v hv
  obtain ⟨p, hp, -, e, he, hr⟩ := h m hm
  rw [wd_of hp] at hv
  exact ⟨e, he, Option.some.inj (hv.2.symm.trans hr)⟩

theorem boundBase_sound {mem : List (ℕ × ℕ × ℕ)} (hm : MemIf L fp mem) (hB : BookHolds L fp B)
    {bnd : List (ℕ × ℕ)} (hb : BndHolds L fp bnd) {c n : ℕ} (h : boundBase mem B bnd c n = true) :
    ∃ e < n, L.read (fp * addressOfIndex c) = some (ofK (addressOfIndex e)) := by
  simp only [boundBase, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
    have hh := hB c a ha
    split at hp
    · rename_i x y k
      simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hp
      obtain ⟨rfl, hk⟩ := hp
      obtain ⟨e, e', he, hx, -⟩ := hh
      exact ⟨e, by omega, hx⟩
    · rename_i pc o1 o2 o3
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨rfl, hp⟩ := hp
      obtain ⟨m, hmm, hq⟩ := List.any_eq_true.mp hp
      simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hq
      obtain ⟨⟨rfl, ho2⟩, hle⟩ := hq
      obtain ⟨p, v3, h1, hK, h3, h2⟩ := hh
      simp only [derefSource] at h2
      obtain ⟨e, he, hv⟩ := hm m hmm v3 ⟨by rw [wd_of h1]; exact hK, by rw [wd_of h1, ho2]; exact h2⟩
      exact ⟨e, by omega, by rw [h3, hv]⟩
    · simp at hp
  · obtain ⟨p, hp, hq⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hq
    obtain ⟨e, he, hr⟩ := hb p hp
    exact ⟨e, by omega, hq.1 ▸ hr⟩
  · revert h
    cases hm : selBound B selFuel c with
    | none => exact fun h ↦ absurd h Bool.false_ne_true
    | some m =>
      intro h
      obtain ⟨e, he, hr⟩ := selBound_sound hB selFuel hm
      exact ⟨e, by simp only [Nat.ble_eq] at h; omega, hr⟩

theorem boundScaled_sound {F : Exec.Facts} (hF : F.pows.Ok) {ψ : Trie Sym} (hψ : EnvHolds L fp ψ)
    {mem : List (ℕ × ℕ × ℕ)} (hm : MemIf L fp mem) (hB : BookHolds L fp B)
    {bnd : List (ℕ × ℕ)} (hb : BndHolds L fp bnd) {x y n : ℕ}
    (h : boundScaled F ψ mem B bnd x y n = true) {vx vy : E}
    (hx : L.read (fp * addressOfIndex x) = some vx) (hy : L.read (fp * addressOfIndex y) = some vy) :
    ∃ e < n, vx * vy = ofK (addressOfIndex e) := by
  unfold boundScaled at h
  split at h
  · rename_i k hk
    simp only [Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨hkn, h⟩ := h
    obtain ⟨e, he, hr⟩ := boundBase_sound hm hB hb h
    obtain rfl := Option.some.inj (hx.symm.trans hr)
    obtain rfl := Option.some.inj (hy.symm.trans (gpAt_sound hF hB hψ hk))
    exact ⟨e + k, by omega, ofK_gpow_mul _ _⟩
  · exact absurd h Bool.false_ne_true

theorem boundOk0_sound {F : Exec.Facts} (hF : F.pows.Ok) {ψ : Trie Sym} (hψ : EnvHolds L fp ψ)
    {mem : List (ℕ × ℕ × ℕ)} (hm : MemIf L fp mem) (hB : BookHolds L fp B)
    {bnd : List (ℕ × ℕ)} (hb : BndHolds L fp bnd) {c n : ℕ}
    (h : boundOk0 F ψ mem B bnd c n = true) :
    ∃ e < n, L.read (fp * addressOfIndex c) = some (ofK (addressOfIndex e)) := by
  simp only [boundOk0, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact boundBase_sound hm hB hb h
  · revert h
    cases hk : gpAt F B ψ c with
    | none => exact fun h ↦ absurd h Bool.false_ne_true
    | some k =>
      intro h
      exact ⟨k, Nat.blt_eq.mp h, gpAt_sound hF hB hψ hk⟩
  · obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
    have hh := hB c a ha
    split at hp
    · rename_i pc x y z
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hp
      obtain ⟨rfl, hp⟩ := hp
      obtain ⟨vX, vY, hx, hy, hc⟩ := hh
      rcases hp with hp | hp
      · obtain ⟨e, he, hr⟩ := boundScaled_sound hF hψ hm hB hb hp hx hy
        exact ⟨e, he, by rw [hc, hr]⟩
      · obtain ⟨e, he, hr⟩ := boundScaled_sound hF hψ hm hB hb hp hy hx
        exact ⟨e, he, by rw [hc, mul_comm, hr]⟩
    · simp at hp

theorem boundOk_sound {F : Exec.Facts} (hF : F.pows.Ok) {ψ : Trie Sym} (hψ : EnvHolds L fp ψ)
    {mem : List (ℕ × ℕ × ℕ)} (hm : MemIf L fp mem) (hB : BookHolds L fp B)
    {bnd : List (ℕ × ℕ)} (hb : BndHolds L fp bnd) {c n : ℕ}
    (h : boundOk F ψ mem B bnd c n = true) :
    ∃ e < n, L.read (fp * addressOfIndex c) = some (ofK (addressOfIndex e)) := by
  simp only [boundOk, Bool.or_eq_true] at h
  rcases h with h | h
  · exact boundOk0_sound hF hψ hm hB hb h
  · obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
    have hh := hB c a ha
    split at hp
    · rename_i d s
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨v, hs, hd⟩ := hh
      rcases hp with ⟨rfl, hp⟩ | ⟨rfl, hp⟩
      · obtain ⟨e, he, hr⟩ := boundOk0_sound hF hψ hm hB hb hp
        exact ⟨e, he, by rw [hd, ← hs, hr]⟩
      · obtain ⟨e, he, hr⟩ := boundOk0_sound hF hψ hm hB hb hp
        exact ⟨e, he, by rw [hs, ← hd, hr]⟩
    · simp at hp

/-- Memory bounded through cells of the frame: for each `(o, c, n)`, the word at `fp[o]·g^c` is
`g^e` with `e < n`. -/
def MemKnown (L : MemoryImage κ) (fp : K) (known : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ k ∈ known, ∃ e < k.2.2, Core.LoadHolds L.read (wd L fp k.1) k.2.1 (ofK (addressOfIndex e))

theorem memIf_of_known {known : List (ℕ × ℕ × ℕ)} (h : MemKnown L fp known) : MemIf L fp known := by
  intro m hm v hv
  obtain ⟨e, he, hl⟩ := h m hm
  exact ⟨e, he, Option.some.inj (hv.2.symm.trans hl.2)⟩

theorem memOk_sound (hB : BookHolds L fp B) {known : List (ℕ × ℕ × ℕ)} (hk : MemKnown L fp known)
    {args : List ℕ} {mem : List (ℕ × ℕ × ℕ)} (h : memOk known args mem = true) {q : ℕ}
    (hs : storesOk B q 2 args = true) {pv : E} (hq : L.read (fp * addressOfIndex q) = some pv) :
    MemPre L (pv.limb 0) mem := by
  intro m hm
  have := List.all_eq_true.mp h m hm
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at this
  obtain ⟨⟨h2, hlt⟩, hany⟩ := this
  obtain ⟨kk, hkk, hq'⟩ := List.any_eq_true.mp hany
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hq'
  obtain ⟨⟨hc1, hc⟩, hn⟩ := hq'
  obtain ⟨e, he, hK, hr⟩ := hk kk hkk
  obtain ⟨pv', hq'', -, v, h1, h3⟩ := storesOk_sound hB hs (m.1 - 2) hlt
  obtain rfl := Option.some.inj (hq''.symm.trans hq)
  rw [show 2 + (m.1 - 2) = m.1 by omega] at h3
  rw [hc1, nth_eq hlt, wd_of h1] at hK hr
  exact ⟨v, h3, hK, e, by omega, hc ▸ hr⟩

theorem semOk_sound {G : Glob} {fp' : K} {sems : List (ℕ × List ℕ)} (hs : SemHolds G L fp sems)
    {B : Book} (hB : BookHolds L fp B)
    {ne : ℕ → ℕ → Bool} (hne : ∀ a b, ne a b = true → wd L fp a ≠ wd L fp b)
    {args : List ℕ} {sem : List (ℕ × List ℕ)} (h : semOk B ne sems args sem = true)
    (hw : ∀ i (hi : i < args.length), wd L fp' (2 + i) = wd L fp args[i]) : SemHolds G L fp' sem := by
  have hc : ∀ o, 2 ≤ o → o - 2 < args.length → wd L fp' o = wd L fp (frameCell args o) := by
    intro o h2 hl
    have e := hw _ hl
    rw [show 2 + (o - 2) = o by omega] at e
    rw [e, frameCell, nth_eq hl]
  intro s hs'
  have := List.all_eq_true.mp h s hs'
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, Nat.ble_eq, Nat.blt_eq] at this
  obtain ⟨hr, hq | ⟨ht, hm⟩⟩ := this
  · have hmap : s.2.map (wd L fp') = (s.2.map (frameCell args)).map (wd L fp) := by
      rw [List.map_map]
      exact List.map_congr_left fun o ho ↦ hc o (hr o ho).1 (hr o ho).2
    obtain ⟨q, hq, hq'⟩ := List.any_eq_true.mp hq
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Nat.ble_eq, Nat.blt_eq] at hq'
    obtain ⟨hq2, hq1 | ⟨⟨⟨h32, hb⟩, hk⟩, hset⟩⟩ := hq'
    · rw [hmap, ← hq2, ← hq1]
      exact hs q hq
    · have hq := hs q hq
      have hlt : s.1 < 2 ^ 32 := by rw [← hb, impBase]; exact Nat.mod_lt _ (by positivity)
      have hkq : impPos q.1 < q.2.length := by rw [hq2, List.length_map]; exact hk
      have himm : (q.2.map (wd L fp)).getD (impPos q.1) 0 =
          OffsetInstruction.immediateWord (impImm q.1) 0 := by
        rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hkq), List.getElem_map,
          ← nth_eq hkq]
        exact wd_of (setImm_sound hB hset)
      unfold SemRel at hq ⊢
      have hn : ¬ 2 ^ 32 ≤ s.1 := by omega
      simp only [hn, ↓reduceIte] at ⊢
      simp only [h32, ↓reduceIte] at hq
      rw [hmap, ← hq2, ← hb]
      exact hq himm
  · obtain ⟨t, os⟩ := s
    have ht' : t = tagNe := beq_iff_eq.mp ht
    simp only at hm hr ⊢
    rcases os with _ | ⟨a, _ | ⟨b, _ | ⟨c, os⟩⟩⟩
    · simp at hm
    · simp at hm
    · have ha := hr a (by simp)
      have hb := hr b (by simp)
      unfold SemRel SemRel0
      simp only [ht', tagNe, ↓reduceIte, List.map_cons, List.map_nil, List.getD_cons_zero,
        List.getD_cons_succ]
      rw [hc a ha.1 ha.2, hc b hb.1 hb.2]
      exact hne _ _ hm
    · simp at hm

theorem preOk_sound {F : Exec.Facts} (hF : F.pows.Ok) {ψ : Trie Sym} (hψ : EnvHolds L fp ψ)
    {mem : List (ℕ × ℕ × ℕ)} (hm : MemIf L fp mem) (hB : BookHolds L fp B)
    {bnd : List (ℕ × ℕ)} (hb : BndHolds L fp bnd)
    {args : List ℕ} {pre : List (ℕ × ℕ)} (h : preOk F ψ mem B bnd args pre = true) {q : ℕ}
    (hs : storesOk B q 2 args = true) {pv : E} (hq : L.read (fp * addressOfIndex q) = some pv) :
    BndHolds L (pv.limb 0) pre := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at this
  obtain ⟨⟨h2, hlt⟩, hbd⟩ := this
  obtain ⟨e, he, hr⟩ := boundOk_sound hF hψ hm hB hb hbd
  obtain ⟨pv', hq', -, v, h1, h3⟩ := storesOk_sound hB hs (p.1 - 2) hlt
  obtain rfl := Option.some.inj (hq'.symm.trans hq)
  rw [nth_eq hlt, h1] at hr
  obtain rfl := Option.some.inj hr
  refine ⟨e, he, ?_⟩
  rwa [show 2 + (p.1 - 2) = p.1 by omega] at h3

theorem postBnd_sound {ca cr : List ℕ} {post : List (ℕ × ℕ)} {pv : E}
    (hs : ∀ i (hi : i < ca.length), ∃ v, L.read (fp * addressOfIndex ca[i]) = some v ∧
      L.read (pv.limb 0 * addressOfIndex (2 + i)) = some v)
    (hl : ∀ i (hi : i < cr.length), ∃ v, L.read (fp * addressOfIndex cr[i]) = some v ∧
      L.read (pv.limb 0 * addressOfIndex (2 + ca.length + i)) = some v)
    (hpost : ∀ p ∈ post, 2 ≤ p.1 ∧ p.1 < 2 + ca.length + cr.length)
    (hb : BndHolds L (pv.limb 0) post) : BndHolds L fp (postBnd (ca ++ cr) post) := by
  intro p' hp'
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hp'
  obtain ⟨h2, hlt⟩ := hpost p hp
  obtain ⟨e, he, hr⟩ := hb p hp
  refine ⟨e, he, ?_⟩
  simp only [frameCell]
  rw [nth_eq (by simp; omega)]
  by_cases hc : p.1 - 2 < ca.length
  · rw [List.getElem_append_left hc]
    obtain ⟨v, h1, h3⟩ := hs _ hc
    rw [show 2 + (p.1 - 2) = p.1 by omega, hr] at h3
    rw [h1, h3]
  · rw [List.getElem_append_right (by omega)]
    obtain ⟨v, h1, h3⟩ := hl (p.1 - 2 - ca.length) (by omega)
    rw [show 2 + ca.length + (p.1 - 2 - ca.length) = p.1 by omega, hr] at h3
    rw [h1, h3]

theorem calleeAt_some {X : Fx} {pc j : ℕ} (h : calleeAt X pc = some j) :
    X.G.good j = true ∧ (X.G.sig j).entry = pc := by
  have := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this

theorem tableCallsOk_get {X : Fx} {base : ℕ} {ok : String → Sig → Bool} :
    ∀ {i : ℕ} {fs : List String}, tableCallsOk X base ok i fs = true →
      ∀ e (he : e < fs.length), ∃ pc j, X.G.jt.get (base + (i + e)) = some pc ∧
        calleeAt X pc = some j ∧ ok fs[e] (X.G.sig j) = true
  | _, [], _, _, he => absurd he (Nat.not_lt_zero _)
  | i, f :: fs, h, e, he => by
    simp only [tableCallsOk, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases e with
    | zero =>
      split at h1
      · rename_i pc hpc
        split at h1
        · rename_i j hj
          exact ⟨pc, j, by simpa using hpc, hj, h1⟩
        · simp at h1
      · simp at h1
    | succ e =>
      obtain ⟨pc, j, h3, h4, h5⟩ := tableCallsOk_get h2 e (by simpa using he)
      exact ⟨pc, j, by rw [show i + (e + 1) = i + 1 + e by omega]; exact h3, h4, h5⟩

theorem armsOk_get {G : Glob} {entry base : ℕ} :
    ∀ {i : ℕ} {ts : List ℕ}, armsOk G entry base i ts = true →
      ∀ e (he : e < ts.length), G.jt.get (base + (i + e)) = some (entry + ts[e])
  | _, [], _, _, he => absurd he (Nat.not_lt_zero _)
  | i, t :: ts, h, e, he => by
    simp only [armsOk, Bool.and_eq_true, beq_iff_eq] at h
    cases e with
    | zero => simpa using h.1
    | succ e =>
      rw [show i + (e + 1) = i + 1 + e by omega]
      simpa using armsOk_get h.2 e (by simpa using he)

theorem tableBase_sound (hB : BookHolds L fp B) {t c base : ℕ} (h : tableBase B t c = some base) :
    ∃ pv, L.read (fp * addressOfIndex c) = some pv ∧ IsInK pv ∧
      ∃ v, L.read (fp * addressOfIndex t) = some v ∧ L.read (pv.limb 0 * addressOfIndex base) = some
          v := by
  obtain ⟨a, ha, hp⟩ := List.exists_of_findSome?_eq_some h
  have hh := hB t a ha
  split at hp
  · rename_i pc o1 o2 o3
    simp only [Bool.cond_eq_ite, Bool.and_eq_true, beq_iff_eq] at hp
    split_ifs at hp with hc
    obtain rfl := Option.some.inj hp
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨pv, v3, h1, hK, h3, h2⟩ := hh
    exact ⟨pv, h1, hK, v3, h3, h2⟩
  · simp at hp

theorem tableSrc_sound (hB : BookHolds L fp B) {t x base : ℕ} (h : tableSrc B t = some (x, base)) :
    ∃ pv, L.read (fp * addressOfIndex x) = some pv ∧ IsInK pv ∧
      ∃ v, L.read (fp * addressOfIndex t) = some v ∧ L.read (pv.limb 0 * addressOfIndex base) = some
          v := by
  obtain ⟨a, ha, hp⟩ := List.exists_of_findSome?_eq_some h
  have hh := hB t a ha
  split at hp
  · rename_i pc o1 o2 o3
    simp only [Bool.cond_eq_ite, beq_iff_eq] at hp
    split_ifs at hp with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hp)
    subst hc
    obtain ⟨pv, v3, h1, hK, h3, h2⟩ := hh
    exact ⟨pv, h1, hK, v3, h3, h2⟩
  · simp at hp

theorem chkArms_get {X : Fx} {r : Res} :
    ∀ {as : List (List Core.Stmt)} {ts : List ℕ} {B : Book} {bnd : List (ℕ × ℕ)},
      chkArms X r as ts B bnd = true → ts.length = as.length ∧
        ∀ e (he : e < as.length) (ht : e < ts.length), ∃ st, segAt X ts[e] B bnd = some st ∧
          chkL X as[e] st [] = r
  | [], [], _, _, _ => ⟨rfl, fun _ he ↦ absurd he (Nat.not_lt_zero _)⟩
  | a :: as, t :: ts, B, bnd, h => by
    simp only [chkArms, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨hl, ih⟩ := chkArms_get h2
    refine ⟨by simp [hl], fun e he ht ↦ ?_⟩
    cases e with
    | zero =>
      split at h1
      · rename_i st hst
        exact ⟨st, hst, by simpa using h1⟩
      · simp at h1
    | succ e => exact ih e (by simpa using he) (by simpa using ht)
  | [], _ :: _, _, _, h => by simp [chkArms] at h
  | _ :: _, [], _, _, h => by simp [chkArms] at h

theorem afterCall_some {X : Fx} {t q o : ℕ} {cr : List ℕ} {B : Book} {bnd : List (ℕ × ℕ)}
    {st' : CS} (h : afterCall X t q o cr B bnd = some st') :
    ∃ sr, segAt X t B bnd = some sr ∧ fwd (fun B ↦ loadsOk B q o cr) sr = (st', true) := by
  unfold afterCall at h
  split at h
  · rename_i sr hsr
    split at h
    · rename_i st'' heq
      obtain rfl := Option.some.inj h
      exact ⟨sr, hsr, heq⟩
    · simp at h
  · simp at h

theorem cellsOf_length (loc : Trie ℕ) (vs : List Core.V) : (cellsOf loc vs).length = vs.length := by
  simp [cellsOf]

/-- Stored cells, with the frame they are stored in fixed. -/
theorem storesOk_at (hB : BookHolds L fp B) {q o : ℕ} {cs : List ℕ} (h : storesOk B q o cs = true)
    {pv : E} (hq : L.read (fp * addressOfIndex q) = some pv) :
    ∀ i (hi : i < cs.length), ∃ v, L.read (fp * addressOfIndex cs[i]) = some v ∧
      L.read (pv.limb 0 * addressOfIndex (o + i)) = some v := by
  intro i hi
  obtain ⟨pv', hq', -, v, h1, h2⟩ := storesOk_sound hB h i hi
  obtain rfl := Option.some.inj (hq'.symm.trans hq)
  exact ⟨v, h1, h2⟩

theorem tailArgsOk_sound {S : ℕ} : ∀ {o : ℕ} {cs : List ℕ}, tailArgsOk B S o cs = true →
    ∀ i (hi : i < cs.length), sameOk B (S + (o + i)) cs[i] = true
  | _, [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | o, c :: cs, h, i, hi => by
    simp only [tailArgsOk, Bool.and_eq_true, nextHolds] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have := tailArgsOk_sound h.2 i (by simpa using hi)
      rw [show o + (i + 1) = o + 1 + i by omega]
      simpa using this

theorem tailEnvOk_sound (hB : BookHolds L fp B) {env : Trie Sym} (he : EnvHolds L fp env)
    {S o : ℕ} (h : tailEnvOk B env S o = true) :
    L.read (fp * addressOfIndex (S + o)) = some (ofK (fp * addressOfIndex S)) := by
  simp only [tailEnvOk, Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    · rename_i e' he'
      simp only [beq_iff_eq] at h
      subst h
      exact he _ _ he'
    · simp at h
  · obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
    have hh := hB _ a ha
    split at hp
    · rename_i d w
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨rfl, hp⟩ := hp
      split at hp
      · rename_i e' he'
        simp only [beq_iff_eq] at hp
        subst hp
        obtain ⟨v, h1, h2⟩ := hh
        rw [h2, ← h1]
        exact he _ _ he'
      · simp at hp
    · simp at hp

end Calls

/-! ## The walk -/

section Walk

variable {κ : ℕ} {L : MemoryImage κ} {fp : K} {f : CompiledFunction} {X : Fx} {Prog : Core.Program}
  {cert : String → Cert} {A : String → K → List E → List E → Prop}
  {Kb : ℕ}

/-- The words a function returns and what its return does: the frame's return words, back to
the caller with fewer than `Kb` steps left (but `main`), its bounds after. -/
def RetWords (L : MemoryImage κ) (fp : K) (X : Fx) (Kb : ℕ) (rs : List E) : Prop :=
  rs = frameWords L fp (2 + X.nargs) X.nret ∧
    (X.main = false → ∃ k' < Kb, ∃ r, retRegs L fp = some r ∧ SafeReached guestProgram L k' r) ∧
    BndHolds L fp X.post

/-- What a walk of runs with at most `K` steps assumes: its context, the jump table, and every
function's contract for runs shorter than `K`. -/
structure WalkEnv (Prog : Core.Program) (cert : String → Cert) (A : String → K → List E → List E → Prop) (L : MemoryImage κ) (fp : K) (f : CompiledFunction) (X : Fx)
    (Kb : ℕ) : Prop where
  hyp : WalkHyp L fp f X
  jt : JTHolds X.G L
  mem : MemIf L fp X.mem
  known : MemKnown L fp X.known
  sems : SemHolds X.G L fp X.sems
  callees : ∀ j, FunSpecLtReached guestProgram L Kb (X.G.sig j).entry (Pre X.G L j) (Post Prog X.G L cert A j)

/-- What a walk's continuation may assume where the walk ends in a chained `match`'s table jump
through `fp[x]` into the arms `succ`: the run at arm `e`'s offset, `fp[x] = g^e`. -/
def ChainK (L : MemoryImage κ) (fp : K) (f : CompiledFunction) (X : Fx) (Kb x : ℕ) (succ : List ℕ)
    (k : ℕ) (N : Prop) : Prop :=
  ∀ e (he : e < succ.length) k', wd L fp x = ofK (addressOfIndex e) → k' ≤ k →
    SegRun L fp f X Kb succ[e] k' → N

/-- **The run takes a chained `match`'s table jump**: it is at arm `e`'s offset, `fp[x] = g^e`,
with a window's hand-over at the arms' first offset in place, and its environment if that is the
window's end. -/
def ChainArr (L : MemoryImage κ) (fp : K) (f : CompiledFunction) (X : Fx) (Kb x : ℕ) (succ : List ℕ)
    (k : ℕ) : Prop :=
  ∃ e, ∃ _ : e < succ.length, wd L fp x = ofK (addressOfIndex e) ∧ ∃ k' ≤ k,
    SegRun L fp f X Kb succ[e] k' ∧ HandHolds L fp X (succ.headD 0) ∧
      (succ.headD 0 = X.wJ → EnvHolds L fp X.wenv)

theorem ChainK.mono {x : ℕ} {succ : List ℕ} {k k' : ℕ} {N : Prop}
    (h : ChainK L fp f X Kb x succ k N) (hk : k' ≤ k) : ChainK L fp f X Kb x succ k' N :=
  fun e he k'' hx hk'' hr ↦ h e he k'' hx (le_trans hk'' hk) hr

theorem ChainArr.mono {x : ℕ} {succ : List ℕ} {k k' : ℕ} (h : ChainArr L fp f X Kb x succ k')
    (hk : k' ≤ k) : ChainArr L fp f X Kb x succ k := by
  obtain ⟨e, he, hx, k'', hk'', hr⟩ := h
  exact ⟨e, he, hx, k'', le_trans hk'' hk, hr⟩

/-- **What the walk of a block from a position gives**: the block's core semantics under the
check's valuation, with any continuation the run's arrival at the join, or at a chained `match`'s
arm, gives; the pending atoms; and that the run arrives at the join, or at the arm. -/
def WalkGood (Prog : Core.Program) (cert : String → Cert) (A : String → K → List E → List E → Prop) (L : MemoryImage κ) (fp : K) (f : CompiledFunction) (X : Fx) (Kb : ℕ)
    (ss : List Core.Stmt) (st : CS) (P : List Core.Atom) : Prop :=
  ∀ k (N : Prop), PosOk L fp f X Kb st k → chkL X ss st P ≠ .fail →
    (∀ J, chkL X ss st P = .join J → ∀ k', k' ≤ k → SegRun L fp f X Kb J k' → N) →
    (∀ x succ, chkL X ss st P = .chain x succ → ChainK L fp f X Kb x succ k N) →
    Core.Stmt.HoldsList (RL Prog L cert A) L.read (val L fp X.loc) ss N (RetWords L fp X Kb) ∧
      (∀ a ∈ P, a.Holds L.read (val L fp X.loc)) ∧
      (∀ J, chkL X ss st P = .join J → ∃ k' ≤ k, Arrive L fp f X Kb J k') ∧
      (∀ x succ, chkL X ss st P = .chain x succ → ChainArr L fp f X Kb x succ k)

/-- **What the walk of a chained `match` gives** (`chainL`): entered at arm `e`'s offset with
`fp[x] = g^e`, the book, bounds of the chain's first dispatch holding, as `WalkGood`. -/
def ChainGood (Prog : Core.Program) (cert : String → Cert) (A : String → K → List E → List E → Prop) (L : MemoryImage κ) (fp : K) (f : CompiledFunction) (X : Fx) (Kb : ℕ)
    (x : ℕ) (succ : List ℕ) (B : Book) (ψ : Trie Sym) (bnd : List (ℕ × ℕ)) (ss : List Core.Stmt)
    (P : List Core.Atom) : Prop :=
  ∀ k (N : Prop), BookHolds L fp B → BndHolds L fp bnd →
    (∃ e, ∃ _ : e < succ.length, wd L fp x = ofK (addressOfIndex e) ∧ SegRun L fp f X Kb succ[e] k) →
    chainL X x succ B ψ bnd ss P ≠ .fail →
    (∀ J, chainL X x succ B ψ bnd ss P = .join J → ∀ k', k' ≤ k → SegRun L fp f X Kb J k' → N) →
    (∀ x' succ', chainL X x succ B ψ bnd ss P = .chain x' succ' → ChainK L fp f X Kb x' succ' k N) →
    Core.Stmt.HoldsList (RL Prog L cert A) L.read (val L fp X.loc) ss N (RetWords L fp X Kb) ∧
      (∀ a ∈ P, a.Holds L.read (val L fp X.loc)) ∧
      (∀ J, chainL X x succ B ψ bnd ss P = .join J → ∃ k' ≤ k, Arrive L fp f X Kb J k') ∧
      (∀ x' succ', chainL X x succ B ψ bnd ss P = .chain x' succ' → ChainArr L fp f X Kb x' succ' k)

theorem handOk_sound (hF : X.F.pows.Ok) (hm : MemIf L fp X.mem) {st : CS}
    (hψ : EnvHolds L fp st.psi) (hB : BookHolds L fp st.book)
    (hb : BndHolds L fp st.bnd) {J : ℕ} (h : handOk X J st = true) : HandHolds L fp X J := by
  intro J' fs bs hw hJ
  unfold handOk at h
  rw [hw] at h
  simp only [hJ, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    List.all_eq_true, List.contains_iff_mem] at h
  exact ⟨fun p hp ↦ hB p.1 p.2 (by simpa using h.1 p hp),
    fun b hbb ↦ boundOk_sound hF hψ hm hB hb (h.2 b hbb)⟩

theorem pendOk_sound (W : WalkEnv Prog cert A L fp f X Kb) {st : CS} {k : ℕ} (hp : PosOk L fp f X Kb st k)
    {P : List Core.Atom} (h : pendOk X st P = true) : ∀ a ∈ P, a.Holds L.read (val L fp X.loc) :=
  fun a ha ↦ atomOk_sound W.hyp.ctx.pows hp.book hp.psi (List.all_eq_true.mp h a ha)

theorem walk_nil (W : WalkEnv Prog cert A L fp f X Kb) (st : CS) (P : List Core.Atom) :
    WalkGood Prog cert A L fp f X Kb [] st P := by
  intro k N hp hne hj hcn
  rw [chkL_nil] at hne hj hcn ⊢
  rcases blockEnd_join hne with ⟨J, se, he, hpd, hhand, hr⟩ | ⟨-, hce⟩
  · obtain ⟨k', hk', hse, hsr⟩ := endOf_ok W.hyp hp he
    refine ⟨hj J hr k' hk' hsr, pendOk_sound W hse hpd, fun J' hJ' ↦ ⟨k', hk', ?_⟩,
      fun _ _ h ↦ by rw [hr] at h; cases h⟩
    rw [hr] at hJ'
    cases hJ'
    exact ⟨hsr, handOk_sound W.hyp.ctx.pows W.mem hse.psi hse.book hse.bnd hhand⟩
  · rw [hce] at hne hj hcn ⊢
    obtain ⟨se, t, ft, t0, ts, x, base, hse, hk, hs, hsrc, hself, harms, hbd, hpd, hhand, hwenv,
      heq⟩ := chainEnd_dec hne
    rw [heq] at hj hcn ⊢
    obtain ⟨k1, hk1, hpse, -, -, -, k₀, hk₀, hr⟩ := endAt_ok hp hse
    obtain ⟨hlt, henv, -, r, hreg, hsafe⟩ := hr
    rw [hk] at hreg
    obtain ⟨a, b, ⟨w, hw, -, rfl⟩, hb, rfl⟩ := hreg
    obtain rfl := self_is W.hyp.ctx.fpOne hself hb
    obtain ⟨e, he, hce⟩ := boundOk_sound W.hyp.ctx.pows hpse.psi W.mem hpse.book hpse.bnd hbd
    obtain ⟨pv, hpv, -, w', hw', hload⟩ := tableSrc_sound hpse.book hsrc
    obtain rfl := Option.some.inj (hpv.symm.trans hce)
    obtain rfl := Option.some.inj (hw.symm.trans hw')
    have heA : e < (t0 :: ts).length := by simp; omega
    have hslot := W.jt _ _ (armsOk_get harms e heA)
    have hadd : addressOfIndex e * addressOfIndex base = addressOfIndex (base + (0 + e)) := by
      rw [Nat.zero_add, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add, Nat.add_comm]
    rw [limb_ofK0, hadd, hslot] at hload
    obtain rfl := Option.some.inj hload
    rw [limb_ofK0, W.hyp.entry] at hsafe
    have hrun := segRun_of_safe W.hyp hpse.seg (hpse.exits _ (Or.inl rfl))
      (by rw [hs]; exact List.getElem_mem heA) henv (K := Kb) (by omega) hsafe
    have hx := wd_of hce
    refine ⟨hcn x (t0 :: ts) rfl e heA k1 hx hk1 hrun, pendOk_sound W hpse hpd,
      fun _ h ↦ Res.noConfusion h, fun x' s' h ↦ ?_⟩
    obtain ⟨rfl, rfl⟩ := Res.chain.inj h
    refine ⟨e, heA, hx, k1, hk1, hrun,
      handOk_sound W.hyp.ctx.pows W.mem hpse.psi hpse.book hpse.bnd hhand, fun hJ ↦ ?_⟩
    exact henv.sub (hwenv hJ)

theorem walk_atom (W : WalkEnv Prog cert A L fp f X Kb) (a : Core.Atom) (ss : List Core.Stmt) (st : CS)
    (P : List Core.Atom) (ih : ∀ st P, WalkGood Prog cert A L fp f X Kb ss st P) :
    WalkGood Prog cert A L fp f X Kb (.atom a :: ss) st P := by
  intro k N hp hne hj hcn
  rw [chkL_atom] at hne hj hcn ⊢
  obtain ⟨k', hk', hp', htest, -, hpsi, -⟩ :=
    fwd_ok (test := fun B ↦ atomOk X.F B st.psi X.loc a) hp
  revert hne hj hcn htest hp'
  rcases hf : fwd (fun B ↦ atomOk X.F B st.psi X.loc a) st with ⟨st', b⟩
  intro hne hj hcn hp' htest
  simp only at hp' htest hne hj hcn ⊢
  cases b with
  | false =>
    obtain ⟨hl, hP, hr, hrc⟩ := ih st' (a :: P) k' N hp' hne
      (fun J hJ k'' hk'' h ↦ hj J hJ k'' (le_trans hk'' hk') h)
      (fun x s h ↦ (hcn x s h).mono hk')
    refine ⟨⟨hP a List.mem_cons_self, hl⟩, fun b hb ↦ hP b (List.mem_cons_of_mem _ hb),
      fun J hJ ↦ ?_, fun x s h ↦ (hrc x s h).mono hk'⟩
    obtain ⟨k'', hk'', h⟩ := hr J hJ
    exact ⟨k'', le_trans hk'' hk', h⟩
  | true =>
    obtain ⟨hl, hP, hr, hrc⟩ := ih st' P k' N hp' hne
      (fun J hJ k'' hk'' h ↦ hj J hJ k'' (le_trans hk'' hk') h)
      (fun x s h ↦ (hcn x s h).mono hk')
    have ha := atomOk_sound W.hyp.ctx.pows hp'.book hp.psi (htest rfl)
    refine ⟨⟨ha, hl⟩, hP, fun J hJ ↦ ?_, fun x s h ↦ (hrc x s h).mono hk'⟩
    obtain ⟨k'', hk'', h⟩ := hr J hJ
    exact ⟨k'', le_trans hk'' hk', h⟩

/-- What the rest of a walk gives from the join `J`, at `k2 ≤ k` steps. -/
def RestGood (Prog : Core.Program) (cert : String → Cert) (A : String → K → List E → List E → Prop) (L : MemoryImage κ) (fp : K) (f : CompiledFunction) (X : Fx) (Kb : ℕ)
    (r : Res) (ss : List Core.Stmt) (N : Prop) (P : List Core.Atom) (k : ℕ) : Prop :=
  Core.Stmt.HoldsList (RL Prog L cert A) L.read (val L fp X.loc) ss N (RetWords L fp X Kb) ∧
    (∀ a ∈ P, a.Holds L.read (val L fp X.loc)) ∧
    (∀ J, r = .join J → ∃ k' ≤ k, Arrive L fp f X Kb J k') ∧
    (∀ x succ, r = .chain x succ → ChainArr L fp f X Kb x succ k)

theorem walk_ite (W : WalkEnv Prog cert A L fp f X Kb) (c : Core.V) (z n ss : List Core.Stmt) (st : CS)
    (P : List Core.Atom) (ihz : ∀ st P, WalkGood Prog cert A L fp f X Kb z st P)
    (ihn : ∀ st P, WalkGood Prog cert A L fp f X Kb n st P)
    (ih : ∀ st P, WalkGood Prog cert A L fp f X Kb ss st P) :
    WalkGood Prog cert A L fp f X Kb (.ite c z n :: ss) st P := by
  intro k N hp hne hj hcn
  obtain ⟨st', x, t, sn, J, sj, hb, hk, hsucc, hsn, hz, hn, hsj, heq⟩ := chkL_ite hne
  rw [heq] at hne hj hcn ⊢
  obtain ⟨k1, hk1, cv, hc, hcK, hx, hseg, -, hbnd, hB', hcase⟩ := branchAt_ok hp hb
  have rest : ∀ k2, k2 ≤ k → SegRun L fp f X Kb J k2 →
      RestGood Prog cert A L fp f X Kb (chkL X ss sj P) ss N P k := by
    intro k2 hk2 hr
    obtain ⟨h1, h2, h3, h4⟩ := ih sj P k2 N (segAt_ok W.hyp hsj hr hB' (hbnd ▸ hp.bnd)) hne
      (fun J' hJ' k3 hk3 hr3 ↦ hj J' hJ' k3 (by omega) hr3)
      (fun x s h ↦ (hcn x s h).mono hk2)
    exact ⟨h1, h2, fun J' hJ' ↦ (h3 J' hJ').imp fun k' h ↦ ⟨by omega, h.2⟩,
      fun x s h ↦ (h4 x s h).mono hk2⟩
  have hσ : val L fp X.loc c = cv := wd_of hc
  have hblk : ∀ (b : List Core.Stmt) (sb : CS), (∀ st P, WalkGood Prog cert A L fp f X Kb b st P) →
      PosOk L fp f X Kb sb k1 → chkL X b sb [] = .join J →
      Core.Stmt.HoldsList (RL Prog L cert A) L.read (val L fp X.loc) b
          (Core.Stmt.HoldsList (RL Prog L cert A) L.read (val L fp X.loc) ss N
            (RetWords L fp X Kb)) (RetWords L fp X Kb) ∧
        RestGood Prog cert A L fp f X Kb (chkL X ss sj P) [] True P k := by
    intro b sb ihb hpb hjb
    obtain ⟨hl, -, hr, -⟩ := ihb sb [] k1 _ hpb (by rw [hjb]; simp)
      (fun J' hJ' k2 hk2 hr2 ↦ by
        rw [hjb] at hJ'
        cases hJ'
        exact (rest k2 (by omega) hr2).1)
      (fun _ _ h ↦ by rw [hjb] at h; cases h)
    obtain ⟨k2, hk2, hr2⟩ := hr J hjb
    obtain ⟨-, hP, hreach, hrc⟩ := rest k2 (by omega) hr2.1
    exact ⟨hl, trivial, hP, hreach, hrc⟩
  rcases hcase with ⟨rfl, hp'⟩ | ⟨hc0, k₀, hk₀, hr⟩
  · obtain ⟨hl, -, hP, hreach, hrc⟩ := hblk z st' ihz hp' hz
    exact ⟨⟨hσ ▸ hcK, fun _ ↦ hl, fun h0 ↦ absurd hσ h0⟩, hP, hreach, hrc⟩
  · have hrt := segRun_of_next W.hyp hp.seg (hseg ▸ hx) hk hsucc hk₀ hr
    obtain ⟨hl, -, hP, hreach, hrc⟩ :=
      hblk n sn ihn (segAt_ok W.hyp hsn hrt hB' (hbnd ▸ hp.bnd)) hn
    exact ⟨⟨hσ ▸ hcK, fun h0 ↦ absurd (hσ.symm.trans h0) hc0, fun _ ↦ hl⟩, hP, hreach, hrc⟩

/-- A block walked from `sb` to the join `J`, the rest walked from the join's segment `sj`. -/
theorem walk_block (W : WalkEnv Prog cert A L fp f X Kb) {b ss : List Core.Stmt} {sb sj : CS}
    {P : List Core.Atom} {J k k1 : ℕ} {N : Prop} {B : Book} {bnd : List (ℕ × ℕ)}
    (hk1 : k1 ≤ k) (ihb : ∀ st P, WalkGood Prog cert A L fp f X Kb b st P)
    (ih : ∀ st P, WalkGood Prog cert A L fp f X Kb ss st P) (hpb : PosOk L fp f X Kb sb k1)
    (hjb : chkL X b sb [] = .join J) (hsj : segAt X J B bnd = some sj)
    (hB : BookHolds L fp B) (hbnd : BndHolds L fp bnd) (hne : chkL X ss sj P ≠ .fail)
    (hj : ∀ J', chkL X ss sj P = .join J' → ∀ k', k' ≤ k → SegRun L fp f X Kb J' k' → N)
    (hcn : ∀ x succ, chkL X ss sj P = .chain x succ → ChainK L fp f X Kb x succ k N) :
    Core.Stmt.HoldsList (RL Prog L cert A) L.read (val L fp X.loc) b
        (Core.Stmt.HoldsList (RL Prog L cert A) L.read (val L fp X.loc) ss N
          (RetWords L fp X Kb)) (RetWords L fp X Kb) ∧
      RestGood Prog cert A L fp f X Kb (chkL X ss sj P) [] True P k := by
  have rest : ∀ k2, k2 ≤ k1 → SegRun L fp f X Kb J k2 →
      RestGood Prog cert A L fp f X Kb (chkL X ss sj P) ss N P k := by
    intro k2 hk2 hr
    obtain ⟨h1, h2, h3, h4⟩ := ih sj P k2 N (segAt_ok W.hyp hsj hr hB hbnd) hne
      (fun J' hJ' k3 hk3 hr3 ↦ hj J' hJ' k3 (by omega) hr3)
      (fun x s h ↦ (hcn x s h).mono (by omega))
    exact ⟨h1, h2, fun J' hJ' ↦ (h3 J' hJ').imp fun k' h ↦ ⟨by omega, h.2⟩,
      fun x s h ↦ (h4 x s h).mono (by omega)⟩
  obtain ⟨hl, -, hr, -⟩ := ihb sb [] k1 _ hpb (by rw [hjb]; simp)
    (fun J' hJ' k2 hk2 hr2 ↦ by
      rw [hjb] at hJ'
      cases hJ'
      exact (rest k2 hk2 hr2).1)
    (fun _ _ h ↦ by rw [hjb] at h; cases h)
  obtain ⟨k2, hk2, hr2⟩ := hr J hjb
  obtain ⟨-, hP, hreach, hrc⟩ := rest k2 hk2 hr2.1
  exact ⟨hl, trivial, hP, hreach, hrc⟩

/-- A block walked from `sb` into a chained `match`'s table jump, the rest walked by `chainL`, or,
at the end of the statements, that table jump the end. -/
theorem walk_blockC (_W : WalkEnv Prog cert A L fp f X Kb) {b ss : List Core.Stmt} {sb : CS}
    {P : List Core.Atom} {x : ℕ} {succ : List ℕ} {k k1 : ℕ} {N : Prop} {B : Book} {ψ : Trie Sym}
    {bnd : List (ℕ × ℕ)}
    (hk1 : k1 ≤ k) (ihb : ∀ st P, WalkGood Prog cert A L fp f X Kb b st P)
    (ihc : ∀ x succ P, ChainGood Prog cert A L fp f X Kb x succ B ψ bnd ss P)
    (hpb : PosOk L fp f X Kb sb k1) (hjb : chkL X b sb [] = .chain x succ)
    (hB : BookHolds L fp B) (hbnd : BndHolds L fp bnd)
    (hne : chainTo x succ ss P (chainL X x succ B ψ bnd ss P) ≠ .fail)
    (hj : ∀ J', chainTo x succ ss P (chainL X x succ B ψ bnd ss P) = .join J' → ∀ k', k' ≤ k →
      SegRun L fp f X Kb J' k' → N)
    (hcn : ∀ x' s', chainTo x succ ss P (chainL X x succ B ψ bnd ss P) = .chain x' s' →
      ChainK L fp f X Kb x' s' k N) :
    Core.Stmt.HoldsList (RL Prog L cert A) L.read (val L fp X.loc) b
        (Core.Stmt.HoldsList (RL Prog L cert A) L.read (val L fp X.loc) ss N
          (RetWords L fp X Kb)) (RetWords L fp X Kb) ∧
      RestGood Prog cert A L fp f X Kb (chainTo x succ ss P (chainL X x succ B ψ bnd ss P)) [] True
        P k := by
  by_cases hss : ss = []
  · subst hss
    by_cases hP : P = []
    · subst hP
      have hc : chainTo x succ [] [] (chainL X x succ B ψ bnd [] []) = .chain x succ := by
        simp [chainTo]
      rw [hc] at hcn ⊢
      have hK := hcn x succ rfl
      obtain ⟨hl, -, -, hr⟩ := ihb sb [] k1 _ hpb (by rw [hjb]; simp)
        (fun _ h ↦ by rw [hjb] at h; cases h)
        (fun x' s' h ↦ by rw [hjb] at h; cases h; exact hK.mono hk1)
      refine ⟨hl, trivial, by simp, ⟨fun _ h ↦ Res.noConfusion h, fun x' s' h ↦ ?_⟩⟩
      obtain ⟨rfl, rfl⟩ := Res.chain.inj h
      exact (hr x succ hjb).mono hk1
    · exfalso
      apply hne
      simp [chainTo, hP]
  have hc : chainTo x succ ss P (chainL X x succ B ψ bnd ss P) = chainL X x succ B ψ bnd ss P := by
    simp [chainTo, hss]
  rw [hc] at hne hj hcn ⊢
  have rest : ∀ e (he : e < succ.length) k2, wd L fp x = ofK (addressOfIndex e) → k2 ≤ k1 →
      SegRun L fp f X Kb succ[e] k2 →
      RestGood Prog cert A L fp f X Kb (chainL X x succ B ψ bnd ss P) ss N P k := by
    intro e he k2 hx hk2 hr
    obtain ⟨h1, h2, h3, h4⟩ := ihc x succ P k2 N hB hbnd ⟨e, he, hx, hr⟩ hne
      (fun J' hJ' k3 hk3 hr3 ↦ hj J' hJ' k3 (by omega) hr3)
      (fun x' s h ↦ (hcn x' s h).mono (by omega))
    exact ⟨h1, h2, fun J' hJ' ↦ (h3 J' hJ').imp fun k' h ↦ ⟨by omega, h.2⟩,
      fun x' s h ↦ (h4 x' s h).mono (by omega)⟩
  obtain ⟨hl, -, -, hr⟩ := ihb sb [] k1 _ hpb (by rw [hjb]; simp)
    (fun _ h ↦ by rw [hjb] at h; cases h)
    (fun x' s' h ↦ by
      rw [hjb] at h
      cases h
      exact fun e he k2 hx hk2 hr2 ↦ (rest e he k2 hx hk2 hr2).1)
  obtain ⟨e, he, hx, k2, hk2, hr2, -⟩ := hr x succ hjb
  obtain ⟨-, hP, hreach, hrc⟩ := rest e he k2 hx hk2 hr2
  exact ⟨hl, trivial, hP, hreach, hrc⟩

/-- **A `match` entered at arm `e`**, `fp[cellOf v] = g^e`, the arms walked from their offsets
`ts` with the book and bounds `(B, bnd)`, all ending at `r` (a join or a chained `match`'s
table jump), the walk going on as `r` says. -/
theorem walk_enter (W : WalkEnv Prog cert A L fp f X Kb) (v : Core.V) (a0 : List Core.Stmt)
    (as : List (List Core.Stmt)) (ss : List Core.Stmt) (P : List Core.Atom)
    (iha : ∀ e (he : e < (a0 :: as).length) st P, WalkGood Prog cert A L fp f X Kb (a0 :: as)[e] st P)
    (ih : ∀ st P, WalkGood Prog cert A L fp f X Kb ss st P)
    (ihc : ∀ x succ B ψ bnd P, ChainGood Prog cert A L fp f X Kb x succ B ψ bnd ss P)
    {B : Book} {ψ : Trie Sym} {bnd : List (ℕ × ℕ)} (hB : BookHolds L fp B) (hbnd : BndHolds L fp bnd)
    {t0 : ℕ} {ts : List ℕ} {s0 : CS} (hs0 : segAt X t0 B bnd = some s0)
    {e k1 k : ℕ} (hk1 : k1 ≤ k) (heL : e < (a0 :: as).length)
    (hv : wd L fp (cellOf X.loc v) = ofK (addressOfIndex e)) (heT : e < (t0 :: ts).length)
    (hrun : SegRun L fp f X Kb (t0 :: ts)[e] k1) {N : Prop}
    (rest : Res) (hrest : rest ≠ .fail)
    (hcase : (∃ J sj, chkL X a0 s0 [] = .join J ∧ chkArms X (.join J) as ts B bnd = true ∧
          segAt X J B bnd = some sj ∧ rest = chkL X ss sj P) ∨
        (∃ x succ, chkL X a0 s0 [] = .chain x succ ∧
          chkArms X (.chain x succ) as ts B bnd = true ∧
          rest = chainTo x succ ss P (chainL X x succ B ψ bnd ss P)))
    (hj : ∀ J, rest = .join J → ∀ k', k' ≤ k → SegRun L fp f X Kb J k' → N)
    (hcn : ∀ x succ, rest = .chain x succ → ChainK L fp f X Kb x succ k N) :
    Core.Stmt.HoldsList (RL Prog L cert A) L.read (val L fp X.loc) (.match_ v (a0 :: as) :: ss) N
        (RetWords L fp X Kb) ∧
      RestGood Prog cert A L fp f X Kb rest [] True P k := by
  have harm : ∀ r, chkL X a0 s0 [] = r → chkArms X r as ts B bnd = true →
      ∃ sb, segAt X (t0 :: ts)[e] B bnd = some sb ∧ chkL X (a0 :: as)[e] sb [] = r := by
    intro r h0 hch
    cases e with
    | zero => exact ⟨s0, hs0, h0⟩
    | succ e =>
      obtain ⟨-, hg⟩ := chkArms_get hch
      exact hg e (by simp at heL; omega) (by simp at heT; omega)
  have hpb := fun sb (hsb : segAt X (t0 :: ts)[e] B bnd = some sb) ↦ segAt_ok W.hyp hsb hrun hB hbnd
  rcases hcase with ⟨J, sj, h0, hch, hsj, rfl⟩ | ⟨x, succ, h0, hch, rfl⟩
  · obtain ⟨sb, hsb, hjb⟩ := harm _ h0 hch
    obtain ⟨hl, hres⟩ := walk_block W hk1 (iha e heL) ih (hpb sb hsb) hjb hsj hB hbnd hrest hj hcn
    exact ⟨(Core.holds_match_iff _ _ _ _).mpr ⟨e, heL, hv, hl⟩, hres⟩
  · obtain ⟨sb, hsb, hjb⟩ := harm _ h0 hch
    obtain ⟨hl, hres⟩ := walk_blockC W hk1 (iha e heL) (fun x succ P ↦ ihc x succ B ψ bnd P)
      (hpb sb hsb) hjb hB hbnd hrest hj hcn
    exact ⟨(Core.holds_match_iff _ _ _ _).mpr ⟨e, heL, hv, hl⟩, hres⟩

theorem walk_match (W : WalkEnv Prog cert A L fp f X Kb) (v : Core.V) (arms : List (List Core.Stmt))
    (ss : List Core.Stmt) (st : CS) (P : List Core.Atom)
    (iha : ∀ e (he : e < arms.length) st P, WalkGood Prog cert A L fp f X Kb arms[e] st P)
    (ih : ∀ st P, WalkGood Prog cert A L fp f X Kb ss st P)
    (ihc : ∀ x succ B ψ bnd P, ChainGood Prog cert A L fp f X Kb x succ B ψ bnd ss P) :
    WalkGood Prog cert A L fp f X Kb (.match_ v arms :: ss) st P := by
  intro k N hp hne hj hcn
  obtain ⟨se, t, ft, t0, ts, a0, as, base, s0, hse, hk, hs, harms0, hself, hlen, hbd, htb,
    harms, hs0, hcase⟩ := chkL_match hne
  subst harms0
  obtain ⟨k1, hk1, hpse, -, -, -, k₀, hk₀, hr⟩ := endAt_ok hp hse
  obtain ⟨hlt, henv, -, r, hreg, hsafe⟩ := hr
  rw [hk] at hreg
  obtain ⟨a, b, ⟨w, hw, -, rfl⟩, hb, rfl⟩ := hreg
  obtain rfl := self_is W.hyp.ctx.fpOne hself hb
  obtain ⟨e, he, hce⟩ := boundOk_sound W.hyp.ctx.pows hpse.psi W.mem hpse.book hpse.bnd hbd
  obtain ⟨pv, hpv, -, w', hw', hload⟩ := tableBase_sound hpse.book htb
  obtain rfl := Option.some.inj (hpv.symm.trans hce)
  obtain rfl := Option.some.inj (hw.symm.trans hw')
  have heA : e < (t0 :: ts).length := by simp; omega
  have hslot := W.jt _ _ (armsOk_get harms e heA)
  have hadd : addressOfIndex e * addressOfIndex base = addressOfIndex (base + (0 + e)) := by
    rw [Nat.zero_add, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add, Nat.add_comm]
  rw [limb_ofK0, hadd, hslot] at hload
  obtain rfl := Option.some.inj hload
  rw [limb_ofK0, W.hyp.entry] at hsafe
  have hrun := segRun_of_safe W.hyp hpse.seg (hpse.exits _ (Or.inl rfl))
    (by rw [hs]; exact List.getElem_mem heA) henv (K := Kb) (by omega) hsafe
  have heL : e < (a0 :: as).length := by simp; omega
  set rest := chkL X (.match_ v (a0 :: as) :: ss) st P with hrestdef
  have hcase' : (∃ J sj, chkL X a0 s0 [] = .join J ∧ chkArms X (.join J) as ts se.book se.bnd = true ∧
          segAt X J se.book se.bnd = some sj ∧ rest = chkL X ss sj P) ∨
        (∃ x succ, chkL X a0 s0 [] = .chain x succ ∧
          chkArms X (.chain x succ) as ts se.book se.bnd = true ∧
          rest = chainTo x succ ss P (chainL X x succ se.book se.psi se.bnd ss P)) := hcase
  obtain ⟨hl, -, hP, hreach, hrc⟩ := walk_enter W v a0 as ss P iha ih ihc hpse.book hpse.bnd hs0
    hk1 heL (wd_of hce) heA hrun rest hne hcase' hj hcn
  exact ⟨hl, hP, hreach, hrc⟩

/-- **The walk of a chained `match`** (`chainL`) from the arm the run is at. -/
theorem chain_match (W : WalkEnv Prog cert A L fp f X Kb) (v : Core.V) (arms : List (List Core.Stmt))
    (ss : List Core.Stmt) (x : ℕ) (succ : List ℕ) (B : Book) (ψ : Trie Sym) (bnd : List (ℕ × ℕ))
    (P : List Core.Atom)
    (iha : ∀ e (he : e < arms.length) st P, WalkGood Prog cert A L fp f X Kb arms[e] st P)
    (ih : ∀ st P, WalkGood Prog cert A L fp f X Kb ss st P)
    (ihc : ∀ x succ B ψ bnd P, ChainGood Prog cert A L fp f X Kb x succ B ψ bnd ss P) :
    ChainGood Prog cert A L fp f X Kb x succ B ψ bnd (.match_ v arms :: ss) P := by
  intro k N hB hbnd harr hne hj hcn
  obtain ⟨t0, ts, a0, as, s0, rfl, rfl, hv, hlen, hs0, hcase⟩ := chainL_match hne
  obtain ⟨e, heT, hx, hrun⟩ := harr
  have heL : e < (a0 :: as).length := by simp at heT ⊢; omega
  obtain ⟨hl, -, hP, hreach, hrc⟩ := walk_enter W v a0 as ss P iha ih ihc hB hbnd hs0
    le_rfl heL (by rw [hv]; exact hx) heT hrun _ hne hcase hj hcn
  exact ⟨hl, hP, hreach, hrc⟩

theorem chain_other (x : ℕ) (succ : List ℕ) (B : Book) (ψ : Trie Sym) (bnd : List (ℕ × ℕ))
    (P : List Core.Atom) (ss : List Core.Stmt)
    (h : ∀ v arms ss', ss ≠ .match_ v arms :: ss') :
    ChainGood Prog cert A L fp f X Kb x succ B ψ bnd ss P := by
  intro k N _ _ _ hne
  exfalso
  apply hne
  match ss, h with
  | [], _ => simp [chainL]
  | .match_ v arms :: ss', h => exact absurd rfl (h v arms ss')
  | .atom _ :: _, _ => simp [chainL]
  | .ite .. :: _, _ => simp [chainL]
  | .call .. :: _, _ => simp [chainL]
  | .callIf .. :: _, _ => simp [chainL]
  | .dispatch .. :: _, _ => simp [chainL]
  | .ret _ :: _, _ => simp [chainL]

/-- What a call into frame `fp[q] = pv` gives the caller: the callee ran from its entry and came
back to the return point, its contract holding of its frame. -/
theorem call_ok (W : WalkEnv Prog cert A L fp f X Kb) {B : Book} {ψ : Trie Sym} {bnd : List (ℕ × ℕ)}
    (hB : BookHolds L fp B) (hψ : EnvHolds L fp ψ) (hbnd : BndHolds L fp bnd) {j q r k1 : ℕ}
    {f' : String} {ca : List ℕ} {nr : ℕ} (hj : calleeAt X (X.G.sig j).entry = some j)
    {ne : ℕ → ℕ → Bool} (hne : ∀ a b, ne a b = true → wd L fp a ≠ wd L fp b)
    (hco : callOk X B ψ bnd ne (X.G.sig j) f' q ca nr = true) {pv : E}
    (hq : L.read (fp * addressOfIndex q) = some pv) (hpK : IsInK pv)
    (hret : retRegs L (pv.limb 0) = some ⟨addressOfIndex r, fp⟩) (hk1 : k1 < Kb)
    (hsafe : SafeReached guestProgram L k1 ⟨addressOfIndex (X.G.sig j).entry, pv.limb 0⟩) :
    ∃ k2 < k1, Post Prog X.G L cert A j (pv.limb 0) ∧ SafeReached guestProgram L k2 ⟨addressOfIndex
        r, fp⟩ ∧
      f' = (X.G.sig j).name ∧ ca.length = (X.G.sig j).nargs ∧ nr = (X.G.sig j).nret ∧
      ca.map (wd L fp) = frameWords L (pv.limb 0) 2 (X.G.sig j).nargs ∧
      (∀ p ∈ (X.G.sig j).post, 2 ≤ p.1 ∧ p.1 < 2 + (X.G.sig j).nargs + (X.G.sig j).nret) ∧
      storesOk B q 2 ca = true := by
  simp only [callOk, Bool.and_eq_true, beq_iff_eq] at hco
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hname, hna⟩, hnr⟩, hst⟩, henvst⟩, hpre⟩, hmem⟩, hsem⟩, hpost⟩ := hco
  obtain ⟨hgood, -⟩ := calleeAt_some hj
  have hPre : Pre X.G L j (pv.limb 0) :=
    ⟨hgood, W.jt, envStoresOk_sound hB henvst hq hpK, preOk_sound W.hyp.ctx.pows hψ W.mem hB hbnd hpre hst hq,
      memOk_sound hB W.known hmem hst hq, semOk_sound W.sems hB hne hsem fun i hi ↦ by
        obtain ⟨pv', hq', -, v, h1, h2⟩ := storesOk_sound hB hst i hi
        obtain rfl := Option.some.inj (hq'.symm.trans hq)
        rw [wd_of h1, wd_of h2]⟩
  obtain ⟨k2, hk2, hPost, hsafe2⟩ := (W.callees j).call hk1 hPre hret hsafe
  refine ⟨k2, hk2, hPost, hsafe2, hname, hna, hnr, ?_, fun p hp ↦ ?_, hst⟩
  · rw [storesOk_words hB hst hq, hna]
  · have := List.all_eq_true.mp hpost p hp
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at this
    exact this

theorem walk_call (W : WalkEnv Prog cert A L fp f X Kb) (f' : String) (args rets : List Core.V)
    (ss : List Core.Stmt) (st : CS) (P : List Core.Atom)
    (ih : ∀ st P, WalkGood Prog cert A L fp f X Kb ss st P) :
    WalkGood Prog cert A L fp f X Kb (.call f' args rets :: ss) st P := by
  intro k N hp hne hjn hcn
  obtain ⟨se, e, q, r, j, st', hse, hk, hj, hco, hle, hsucc, hac, heq⟩ := chkL_call hne
  rw [heq] at hne hjn hcn ⊢
  obtain ⟨k1, hk1, hpse, -, -, -, k₀, hk₀, hr⟩ := endAt_ok hp hse
  obtain ⟨hlt, henv, hextra, rr, hreg, hsafe⟩ := hr
  rw [hk] at hextra hreg
  obtain ⟨pv, hq, hret⟩ := hextra
  obtain ⟨pv', a, hq', hpK, ha, rfl⟩ := hreg
  obtain rfl := Option.some.inj (hq.symm.trans hq')
  simp only [Tgt.Is] at ha
  subst ha
  obtain ⟨-, hentry⟩ := calleeAt_some hj
  rw [← hentry] at hj hsafe
  obtain ⟨k2, hk2, hPost, hsafe2, hname, hna, hnr, hargs, hpost, hst⟩ :=
    call_ok W hpse.book hpse.psi hpse.bnd hj (fun _ _ h ↦ by simp at h) hco hq hpK hret (by omega)
      hsafe
  have hr2 : SegRun L fp f X Kb (r - X.entry) k2 := by
    refine segRun_of_safe W.hyp hpse.seg (hpse.exits _ (Or.inl rfl)) (by rw [hsucc]; simp) henv
      (by omega) ?_
    rw [← W.hyp.entry, Nat.add_sub_cancel' hle]
    exact hsafe2
  obtain ⟨sr, hsr, hfw⟩ := afterCall_some hac
  obtain ⟨k3, hk3, hp3, htest, -, -, -⟩ :=
    fwd_ok (test := fun B ↦ loadsOk B q (2 + args.length) (cellsOf X.loc rets))
      (segAt_ok W.hyp hsr hr2 hpse.book hpse.bnd)
  rw [hfw] at hp3 htest
  have hloads : storesOk st'.book q (2 + args.length) (cellsOf X.loc rets) = true := htest rfl
  have hca := cellsOf_length X.loc args
  have hcr := cellsOf_length X.loc rets
  have hna' : args.length = (X.G.sig j).nargs := hca ▸ hna
  have hcall : RL Prog L cert A f' (args.map (val L fp X.loc)) (rets.map (val L fp X.loc)) := by
    rw [hname, map_val, map_val, hargs, storesOk_words hp3.book hloads hq, hcr, hnr, hna']
    exact hPost.rl
  have hb4 : BndHolds L fp
      (postBnd (cellsOf X.loc args ++ cellsOf X.loc rets) (X.G.sig j).post ++ st'.bnd) := by
    refine BndHolds.append (postBnd_sound (pv := pv) (storesOk_at hpse.book hst hq)
      (fun i hi ↦ ?_) (fun p hp ↦ ?_) hPost.bnd) hp3.bnd
    · obtain ⟨v, h1, h2⟩ := storesOk_at hp3.book hloads hq i hi
      exact ⟨v, h1, by rw [hca]; exact h2⟩
    · obtain ⟨h1, h2⟩ := hpost p hp
      refine ⟨h1, ?_⟩
      rw [hca, hcr, hna', hnr]
      exact h2
  have hp4 : PosOk L fp f X Kb ⟨st'.seg, st'.its, st'.book, st'.psi,
      postBnd (cellsOf X.loc args ++ cellsOf X.loc rets) (X.G.sig j).post ++ st'.bnd,
      st'.fresh⟩ k3 :=
    ⟨hp3.seg, hp3.book, hp3.psi, hb4, hp3.run, hp3.exits, hp3.fresh⟩
  obtain ⟨hl, hP, hreach, hrc⟩ := ih _ P k3 N hp4 hne
    (fun J hJ k4 hk4 h ↦ hjn J hJ k4 (by omega) h)
    (fun x s h ↦ (hcn x s h).mono (by omega))
  exact ⟨⟨hcall, hl⟩, hP, fun J hJ ↦ (hreach J hJ).imp fun k' h ↦ ⟨by omega, h.2⟩,
    fun x s h ↦ (hrc x s h).mono (by omega)⟩

theorem walk_dispatch (W : WalkEnv Prog cert A L fp f X Kb) (v : Core.V) (fs : List String)
    (args rets : List Core.V) (ss : List Core.Stmt) (st : CS) (P : List Core.Atom)
    (ih : ∀ st P, WalkGood Prog cert A L fp f X Kb ss st P) :
    WalkGood Prog cert A L fp f X Kb (.dispatch v fs args rets :: ss) st P := by
  intro k N hp hne hjn hcn
  obtain ⟨se, t, q, r, base, st', hse, hk, htb, hbd, hle, hsucc, htc, hac, heq⟩ :=
    chkL_dispatch hne
  rw [heq] at hne hjn hcn ⊢
  obtain ⟨k1, hk1, hpse, -, -, -, k₀, hk₀, hr⟩ := endAt_ok hp hse
  obtain ⟨hlt, henv, hextra, rr, hreg, hsafe⟩ := hr
  rw [hk] at hextra hreg
  obtain ⟨pv, hq, hret⟩ := hextra
  obtain ⟨pv', a, hq', hpK, ⟨w, hw, -, rfl⟩, rfl⟩ := hreg
  obtain rfl := Option.some.inj (hq.symm.trans hq')
  obtain ⟨e, he, hce⟩ := boundOk_sound W.hyp.ctx.pows hpse.psi W.mem hpse.book hpse.bnd hbd
  obtain ⟨cv, hcv, -, w', hw', hload⟩ := tableBase_sound hpse.book htb
  obtain rfl := Option.some.inj (hcv.symm.trans hce)
  obtain rfl := Option.some.inj (hw.symm.trans hw')
  obtain ⟨pc, j, hslot, hj, hok⟩ := tableCallsOk_get htc e he
  have hadd : addressOfIndex e * addressOfIndex base = addressOfIndex (base + (0 + e)) := by
    rw [Nat.zero_add, addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add, Nat.add_comm]
  rw [limb_ofK0, hadd, W.jt _ _ hslot] at hload
  obtain rfl := Option.some.inj hload
  rw [limb_ofK0] at hsafe
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hok
  obtain ⟨hco, hpost0⟩ := hok
  obtain ⟨-, hentry⟩ := calleeAt_some hj
  rw [← hentry] at hj hsafe
  obtain ⟨k2, hk2, hPost, hsafe2, hname, hna, hnr, hargs, -, -⟩ :=
    call_ok W hpse.book hpse.psi hpse.bnd hj (fun _ _ h ↦ by simp at h) hco hq hpK hret (by omega)
      hsafe
  have hr2 : SegRun L fp f X Kb (r - X.entry) k2 := by
    refine segRun_of_safe W.hyp hpse.seg (hpse.exits _ (Or.inl rfl)) (by rw [hsucc]; simp) henv
      (by omega) ?_
    rw [← W.hyp.entry, Nat.add_sub_cancel' hle]
    exact hsafe2
  obtain ⟨sr, hsr, hfw⟩ := afterCall_some hac
  obtain ⟨k3, hk3, hp3, htest, -, -, -⟩ :=
    fwd_ok (test := fun B ↦ loadsOk B q (2 + args.length) (cellsOf X.loc rets))
      (segAt_ok W.hyp hsr hr2 hpse.book hpse.bnd)
  rw [hfw] at hp3 htest
  have hloads : storesOk st'.book q (2 + args.length) (cellsOf X.loc rets) = true := htest rfl
  have hca := cellsOf_length X.loc args
  have hcr := cellsOf_length X.loc rets
  have hna' : args.length = (X.G.sig j).nargs := hca ▸ hna
  have hcall : RL Prog L cert A fs[e] (args.map (val L fp X.loc)) (rets.map (val L fp X.loc)) := by
    rw [hname, map_val, map_val, hargs, storesOk_words hp3.book hloads hq, hcr, hnr, hna']
    exact hPost.rl
  obtain ⟨hl, hP, hreach, hrc⟩ := ih st' P k3 N hp3 hne
    (fun J hJ k4 hk4 h ↦ hjn J hJ k4 (by omega) h)
    (fun x s h ↦ (hcn x s h).mono (by omega))
  exact ⟨⟨⟨e, he, wd_of hce, hcall⟩, hl⟩, hP,
    fun J hJ ↦ (hreach J hJ).imp fun k' h ↦ ⟨by omega, h.2⟩, fun x s h ↦ (hrc x s h).mono (by omega)⟩

theorem frameWords_zero (L : MemoryImage κ) (fp : K) (o : ℕ) : frameWords L fp o 0 = [] := rfl

theorem walk_callIf (W : WalkEnv Prog cert A L fp f X Kb) (c : Core.V) (f' : String) (args : List Core.V)
    (ss : List Core.Stmt) (st : CS) (P : List Core.Atom)
    (ih : ∀ st P, WalkGood Prog cert A L fp f X Kb ss st P) :
    WalkGood Prog cert A L fp f X Kb (.callIf c f' args :: ss) st P := by
  intro k N hp hne hjn hcn
  obtain ⟨st', x, hb, hform⟩ := chkL_callIf hne
  obtain ⟨k1, hk1, cv, hc, hcK, hx, hseg, hpsi, hbnd, hB', hcase⟩ := branchAt_ok hp hb
  have hσ : val L fp X.loc c = cv := wd_of hc
  obtain ⟨k₀', hk₀', hkk₀, -⟩ := hp.run
  rcases hform with ⟨e, q, r, j, se, sr, hk, hj, hco, hpost0, hle, hsucc, hend, hsr, heq⟩ |
    ⟨e, S, j, hk, hj, rfl, htail, heq⟩
  · rw [heq] at hne hjn hcn ⊢
    have cont : ∀ k2, k2 < k → SegRun L fp f X Kb (r - X.entry) k2 →
        Core.Stmt.HoldsList (RL Prog L cert A) L.read (val L fp X.loc) ss N (RetWords L fp X Kb) ∧
          (∀ a ∈ P, a.Holds L.read (val L fp X.loc)) ∧
          (∀ J, chkL X ss sr P = .join J → ∃ k' ≤ k, Arrive L fp f X Kb J k') ∧
          (∀ x s, chkL X ss sr P = .chain x s → ChainArr L fp f X Kb x s k) := by
      intro k2 hk2 hr2
      obtain ⟨hl, hP, hreach, hrc⟩ := ih sr P k2 N (segAt_ok W.hyp hsr hr2 hB' (hbnd ▸ hp.bnd)) hne
        (fun J hJ k4 hk4 h ↦ hjn J hJ k4 (by omega) h)
        (fun x s h ↦ (hcn x s h).mono (by omega))
      exact ⟨hl, hP, fun J hJ ↦ (hreach J hJ).imp fun k' h ↦ ⟨by omega, h.2⟩,
        fun x s h ↦ (hrc x s h).mono (by omega)⟩
    rcases hcase with ⟨rfl, hp'⟩ | ⟨hc0, k₀, hk₀, hr⟩
    · obtain ⟨k2, hk2, -, hr2⟩ := endOf_ok W.hyp hp' hend
      obtain ⟨hl, hP, hreach, hrc⟩ := cont k2 (by omega) hr2
      exact ⟨⟨hσ ▸ hcK, fun h0 ↦ absurd hσ h0, hl⟩, hP, hreach, hrc⟩
    · obtain ⟨hlt, henv, hextra, rr, hreg, hsafe⟩ := hr
      rw [hk] at hextra hreg
      obtain ⟨pv, hq, hret⟩ := hextra
      obtain ⟨pv', a, hq', hpK, ha, rfl⟩ := hreg
      obtain rfl := Option.some.inj (hq.symm.trans hq')
      simp only [Tgt.Is] at ha
      subst ha
      obtain ⟨-, hentry⟩ := calleeAt_some hj
      rw [← hentry] at hj hsafe
      obtain ⟨k2, hk2, hPost, hsafe2, hname, hna, hnr, hargs, -, -⟩ :=
        call_ok W hB' (hpsi ▸ hp.psi) (hbnd ▸ hp.bnd) hj
          (fun a b h ↦ neAt_sound hB' h (by rw [wd_of hc]; exact hc0)) hco hq hpK hret (by omega) hsafe
      have hr2 : SegRun L fp f X Kb (r - X.entry) k2 := by
        refine segRun_of_safe W.hyp hp.seg hx (by rw [hsucc]; simp) henv (by omega) ?_
        rw [← W.hyp.entry, Nat.add_sub_cancel' hle]
        exact hsafe2
      obtain ⟨hl, hP, hreach, hrc⟩ := cont k2 (by omega) hr2
      have hcall : RL Prog L cert A f' (args.map (val L fp X.loc)) [] := by
        have h1 := hPost.rl
        rw [← hnr, frameWords_zero, ← hargs, ← map_val, ← hname] at h1
        exact h1
      exact ⟨⟨hσ ▸ hcK, fun _ ↦ hcall, hl⟩, hP, hreach, hrc⟩
  · rw [heq]
    simp only [tailOk, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, Bool.not_eq_true',
      List.all_eq_true] at htail
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hname, hna⟩, hnr⟩, hxnr⟩, hpre⟩, hmem0⟩, hxpost⟩, hsem⟩, hargs⟩, henv⟩,
      hr0⟩, hr1⟩, hpend⟩, hmain⟩, hend⟩ := htail
    have hP : ∀ a ∈ P, a.Holds L.read (val L fp X.loc) := fun a ha ↦
      atomOk_sound W.hyp.ctx.pows hB' (hpsi ▸ hp.psi) (List.all_eq_true.mp hpend a ha)
    have hrw : RetWords L fp X Kb [] → Core.Stmt.HoldsList (RL Prog L cert A) L.read
        (val L fp X.loc) [.ret []] N (RetWords L fp X Kb) := id
    have hwords : ∀ (h : ∃ k' < Kb, ∃ r, retRegs L fp = some r ∧ SafeReached guestProgram L k' r),
        RetWords L fp X Kb [] := fun h ↦
      ⟨by rw [hxnr]; rfl, fun _ ↦ h, by rw [hxpost]; intro p hp; simp at hp⟩
    rcases hcase with ⟨rfl, hp'⟩ | ⟨hc0, k₀, hk₀, hr⟩
    · split at hend
      · rename_i se hse
        obtain ⟨k2, hk2, -, -, -, -, k₀2, hk₀2, hr2⟩ := endAt_ok hp' hse
        have hkind : se.seg.exit.kind = .ret := of_decide_eq_true hend
        obtain ⟨hlt, -, -, rr, hreg, hsafe⟩ := hr2
        rw [hkind] at hreg
        exact ⟨⟨hσ ▸ hcK, fun h0 ↦ absurd hσ h0, hwords ⟨k2, by omega, rr, hreg, hsafe⟩⟩, hP,
          fun J hJ ↦ by simp at hJ, fun _ _ h ↦ by simp at h⟩
      · simp at hend
    · obtain ⟨hlt, hxenv, -, rr, hreg, hsafe⟩ := hr
      rw [hk] at hreg
      obtain ⟨a, b, ha, hb', rfl⟩ := hreg
      simp only [Tgt.Is] at ha hb'
      subst ha hb'
      obtain ⟨hgood, hentry⟩ := calleeAt_some hj
      have hPre : Pre X.G L j (fp * addressOfIndex S) := by
        refine ⟨hgood, W.jt, envOf_holds fun p hp ↦ ?_, fun p hq0 ↦ ?_,
          by rw [hmem0]; intro p hp; simp at hp,
          semOk_sound W.sems hB' (fun a b h ↦ neAt_sound hB' h (by rw [wd_of hc]; exact hc0)) hsem
            fun i hi ↦ ?_⟩
        rotate_left
        · have := List.all_eq_true.mp hpre p hq0
          simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at this
          obtain ⟨⟨h2, hlt⟩, hbd⟩ := this
          obtain ⟨e, he, hr⟩ := boundOk_sound W.hyp.ctx.pows (hpsi ▸ hp.psi) W.mem hB' (hbnd ▸ hp.bnd) hbd
          refine ⟨e, he, ?_⟩
          have hs := sameOk_read hB' (tailArgsOk_sound hargs (p.1 - 2) hlt)
          rw [nth_eq hlt] at hr
          rw [show 2 + (p.1 - 2) = p.1 by omega, hr] at hs
          rw [mul_assoc, addressOfIndex, addressOfIndex, ← pow_add, ← addressOfIndex]
          exact hs
        · have := sameOk_sound hB' (tailArgsOk_sound hargs i hi)
          rw [← this]
          unfold wd
          rw [mul_assoc, addressOfIndex, addressOfIndex, ← pow_add]
        have := henv p hp
        rw [Sym.beq_eq this.1]
        have h2 := tailEnvOk_sound hB' hxenv this.2
        rw [mul_assoc, addressOfIndex, addressOfIndex, ← pow_add, ← addressOfIndex]
        simpa [Sym.val, gpow_zero'] using h2
      have hret : retRegs L (fp * addressOfIndex S) = retRegs L fp := by
        have e0 := sameOk_read hB' hr0
        have e1 := sameOk_read hB' hr1
        unfold retRegs
        rw [mul_assoc, mul_assoc, addressOfIndex, addressOfIndex, ← pow_add, ← pow_add, ←
            addressOfIndex, ← addressOfIndex, e0, e1]
      rw [← hentry] at hsafe
      obtain ⟨k2, hk2, rr, hrr, hPost, hsafe2⟩ :=
        (W.callees j).tail (by omega) hPre hret hsafe
      have hcall : RL Prog L cert A f' (args.map (val L fp X.loc)) [] := by
        have h1 := hPost.rl
        rw [hnr, frameWords_zero, ← hname] at h1
        convert h1 using 1
        rw [map_val]
        apply List.ext_getElem (by simp [frameWords, cellsOf_length] at hna ⊢; omega)
        intro i h1' h2'
        simp only [List.getElem_map, frameWords, List.getElem_range]
        have := sameOk_sound hB' (tailArgsOk_sound hargs i (by simpa using h1'))
        rw [← this]
        unfold wd
        rw [mul_assoc, addressOfIndex, addressOfIndex, ← pow_add]
      exact ⟨⟨hσ ▸ hcK, fun _ ↦ hcall, hwords ⟨k2, by omega, rr, hrr, hsafe2⟩⟩, hP,
        fun J hJ ↦ by simp at hJ, fun _ _ h ↦ by simp at h⟩

theorem runAt_words {loc : Trie ℕ} {base : ℕ} {vs : List Core.V} (h : runAt loc base vs = true) :
    vs.map (val L fp loc) = frameWords L fp base vs.length := by
  apply List.ext_getElem (by simp [frameWords])
  intro i h1 h2
  simp only [List.getElem_map, frameWords, List.getElem_range, val]
  rw [runAt_sound h i (by simpa using h1)]

theorem walk_ret (W : WalkEnv Prog cert A L fp f X Kb) (vs : List Core.V) (ss : List Core.Stmt) (st : CS)
    (P : List Core.Atom) : WalkGood Prog cert A L fp f X Kb (.ret vs :: ss) st P := by
  intro k N hp hne hjn hcn
  obtain ⟨hr, heq⟩ := chkL_ret hne
  rw [heq]
  unfold retOk at hr
  split at hr
  · rename_i se hse
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hr
    obtain ⟨⟨⟨⟨hkind, hlen⟩, hrun⟩, hpend⟩, hpost⟩ := hr
    obtain ⟨k2, hk2, hpse, -, -, -, k₀, hk₀, hreach⟩ := endAt_ok hp hse
    refine ⟨⟨by rw [runAt_words hrun, hlen], fun hm ↦ ?_, fun p hp' ↦
      boundOk_sound W.hyp.ctx.pows hpse.psi W.mem hpse.book hpse.bnd (hpost p hp')⟩, pendOk_sound W hpse hpend,
      fun J hJ ↦ by simp at hJ, fun _ _ h ↦ by simp at h⟩
    rw [hm] at hkind
    simp only [Bool.cond_false, decide_eq_true_eq] at hkind
    obtain ⟨hlt, -, -, rr, hreg, hsafe⟩ := hreach
    rw [hkind] at hreg
    exact ⟨k2, by omega, rr, hreg, hsafe⟩
  · simp at hr

mutual
/-- **The walk is sound.** -/
theorem walk_sound (W : WalkEnv Prog cert A L fp f X Kb) :
    ∀ (ss : List Core.Stmt) (st : CS) (P : List Core.Atom), WalkGood Prog cert A L fp f X Kb ss st P
  | [], st, P => walk_nil W st P
  | .atom a :: ss, st, P => walk_atom W a ss st P (walk_sound W ss)
  | .ite c z n :: ss, st, P =>
    walk_ite W c z n ss st P (walk_sound W z) (walk_sound W n) (walk_sound W ss)
  | .match_ v arms :: ss, st, P =>
    walk_match W v arms ss st P (arms_sound W arms) (walk_sound W ss) (chain_sound W ss)
  | .call f' args rets :: ss, st, P => walk_call W f' args rets ss st P (walk_sound W ss)
  | .callIf c f' args :: ss, st, P => walk_callIf W c f' args ss st P (walk_sound W ss)
  | .dispatch v fs args rets :: ss, st, P => walk_dispatch W v fs args rets ss st P (walk_sound W ss)
  | .ret vs :: ss, st, P => walk_ret W vs ss st P

/-- **The walk of a chained `match` is sound.** -/
theorem chain_sound (W : WalkEnv Prog cert A L fp f X Kb) :
    ∀ (ss : List Core.Stmt) (x : ℕ) (succ : List ℕ) (B : Book) (ψ : Trie Sym) (bnd : List (ℕ × ℕ))
      (P : List Core.Atom), ChainGood Prog cert A L fp f X Kb x succ B ψ bnd ss P
  | [], x, succ, B, ψ, bnd, P => chain_other x succ B ψ bnd P [] (fun _ _ _ h ↦ by cases h)
  | .match_ v arms :: ss, x, succ, B, ψ, bnd, P =>
    chain_match W v arms ss x succ B ψ bnd P (arms_sound W arms) (walk_sound W ss) (chain_sound W ss)
  | .atom a :: ss, x, succ, B, ψ, bnd, P =>
    chain_other x succ B ψ bnd P _ (fun _ _ _ h ↦ by cases h)
  | .ite c z n :: ss, x, succ, B, ψ, bnd, P =>
    chain_other x succ B ψ bnd P _ (fun _ _ _ h ↦ by cases h)
  | .call f' args rets :: ss, x, succ, B, ψ, bnd, P =>
    chain_other x succ B ψ bnd P _ (fun _ _ _ h ↦ by cases h)
  | .callIf c f' args :: ss, x, succ, B, ψ, bnd, P =>
    chain_other x succ B ψ bnd P _ (fun _ _ _ h ↦ by cases h)
  | .dispatch v fs args rets :: ss, x, succ, B, ψ, bnd, P =>
    chain_other x succ B ψ bnd P _ (fun _ _ _ h ↦ by cases h)
  | .ret vs :: ss, x, succ, B, ψ, bnd, P =>
    chain_other x succ B ψ bnd P _ (fun _ _ _ h ↦ by cases h)

theorem arms_sound (W : WalkEnv Prog cert A L fp f X Kb) :
    ∀ (arms : List (List Core.Stmt)) (e : ℕ) (he : e < arms.length) (st : CS)
      (P : List Core.Atom), WalkGood Prog cert A L fp f X Kb arms[e] st P
  | [], _, he, _, _ => absurd he (Nat.not_lt_zero _)
  | a :: _, 0, _, st, P => walk_sound W a st P
  | _ :: as, e + 1, he, st, P => arms_sound W as e (by simpa using he) st P
end

end Walk

/-! ## A function -/

section Reach

variable {C : Core.CallRel} {rd : Core.Reader} {σ : Core.Val}

mutual
/-- A statement holding leads on to its continuation or to a return. -/
theorem holds_reach : ∀ (s : Core.Stmt) {next : Prop} {kret : List E → Prop},
    Core.Stmt.Holds C rd σ s next kret → next ∨ ∃ rs, kret rs
  | .atom _, _, _, h => Or.inl h.2
  | .ite c z n, _, _, h => by
    by_cases hc : σ c = 0
    · exact holdsList_reach z (h.2.1 hc)
    · exact holdsList_reach n (h.2.2 hc)
  | .match_ x arms, _, _, h => holdsArms_reach x arms 0 h
  | .call .., _, _, h => Or.inl h.2
  | .callIf .., _, _, h => Or.inl h.2.2
  | .dispatch .., _, _, h => Or.inl h.2
  | .ret _, _, _, h => Or.inr ⟨_, h⟩

theorem holdsList_reach : ∀ (ss : List Core.Stmt) {next : Prop} {kret : List E → Prop},
    Core.Stmt.HoldsList C rd σ ss next kret → next ∨ ∃ rs, kret rs
  | [], _, _, h => Or.inl h
  | s :: ss, _, _, h => (holds_reach s h).elim (holdsList_reach ss) Or.inr

theorem holdsArms_reach (x : Core.V) : ∀ (arms : List (List Core.Stmt)) (j : ℕ) {next : Prop}
    {kret : List E → Prop}, Core.Stmt.HoldsArms C rd σ x j arms next kret → next ∨ ∃ rs, kret rs
  | [], _, _, _, h => h.elim
  | a :: as, j, _, _, h => h.elim (fun h ↦ holdsList_reach a h.2) (holdsArms_reach x as (j + 1))
end

end Reach

section Fn

variable {κ : ℕ} {L : MemoryImage κ} {G : Glob} {f : CompiledFunction} {cf : Core.Fn} {C : Cert}
  {cert : String → Cert} {A : String → K → List E → List E → Prop}
  {Prog : Core.Program}

theorem blt_false {i n : ℕ} (h : n ≤ i) : Nat.blt i n = false := by
  rw [Bool.eq_false_iff]
  intro h'
  exact absurd (Nat.blt_eq.mp h') (Nat.not_lt.mpr h)

theorem bookOf_holds {fp : K} : ∀ (ps : List (ℕ × Exec.Atom)) {B : Book}, BookHolds L fp B →
    (∀ p ∈ ps, p.2.Holds L fp) → BookHolds L fp (bookOf ps B)
  | [], _, hB, _ => hB
  | p :: ps, B, hB, hp => by
    simp only [bookOf, Trie.seq_eq]
    refine bookOf_holds ps (fun o a ha ↦ ?_) (fun q hq ↦ hp q (List.mem_cons_of_mem _ hq))
    rcases look_addKey ha with rfl | ha
    · exact hp p List.mem_cons_self
    · exact hB o a ha

/-! ### The cells of a window -/

theorem locTrieFrom_get : ∀ (cs : List ℕ) (k : ℕ) (t : Trie ℕ) {v c : ℕ},
    getF (locTrieFrom cs k t) v = some c →
      (∃ m, ∃ h : m < cs.length, v = k + m ∧ cs[m] = c) ∨ getF t v = some c
  | [], _, _, _, _, h => Or.inr h
  | c0 :: cs, k, t, v, c, h => by
    simp only [locTrieFrom, natSeq_eq, Trie.seq_eq] at h
    rcases locTrieFrom_get cs (k + 1) _ h with ⟨m, hm, rfl, hc⟩ | h'
    · exact Or.inl ⟨m + 1, by simpa using hm, by omega, by simpa using hc⟩
    · rw [getF_eq, setF_eq] at h'
      rcases Trie.get_set h' with ⟨rfl, rfl⟩ | h''
      · exact Or.inl ⟨0, by simp, by omega, rfl⟩
      · exact Or.inr (by rwa [getF_eq])

theorem insTrie_get : ∀ (ps : List (ℕ × ℕ × ℕ)) (t : Trie ℕ) {v c : ℕ},
    getF (insTrie ps t) v = some c → (∃ j, (v, c, j) ∈ ps) ∨ getF t v = some c
  | [], _, _, _, h => Or.inr h
  | p :: ps, t, v, c, h => by
    simp only [insTrie, Trie.seq_eq] at h
    rcases insTrie_get ps _ h with ⟨j, hj⟩ | h'
    · exact Or.inl ⟨j, List.mem_cons_of_mem _ hj⟩
    · rw [getF_eq, setF_eq] at h'
      rcases Trie.get_set h' with ⟨rfl, rfl⟩ | h''
      · exact Or.inl ⟨p.2.2, by simp⟩
      · exact Or.inr (by rwa [getF_eq])

theorem locAt_get {i v c : ℕ} (h : getF (C.locAt i) v = some c) :
    (∃ m, ∃ hm : m < (listElementOrDefault C.cells i []).length, v = listElementOrDefault C.los i 0
        + m ∧ (listElementOrDefault C.cells i [])[m] = c) ∨
      ∃ j, (v, c, j) ∈ listElementOrDefault C.ins i [] := by
  unfold Cert.locAt at h
  rw [Trie.seq_eq] at h
  rcases insTrie_get _ _ h with hj | h'
  · exact Or.inr hj
  · rcases locTrieFrom_get _ _ _ h' with hm | h''
    · exact Or.inl hm
    · simp [getF_eq] at h''

/-- The windows' cells are consecutive, up to window `n`. -/
def Cont (C : Cert) (n : ℕ) : Prop :=
  listElementOrDefault C.los 0 0 = 0 ∧ ∀ i < n, listElementOrDefault C.los (i + 1) 0 =
      listElementOrDefault C.los i 0 + (listElementOrDefault C.cells i []).length

theorem nth_of_le {α : Type} : ∀ {l : List α} {n : ℕ} {d : α}, l.length ≤ n → listElementOrDefault l
    n d = d
  | [], _, _, _ => rfl
  | _ :: _, 0, _, h => absurd h (by simp)
  | _ :: as, n + 1, _, h => nth_of_le (l := as) (by simpa using h)

theorem cont_lo {n : ℕ} (h : Cont C n) : ∀ j ≤ n,
    listElementOrDefault C.los j 0 = ((C.cells.take j).map List.length).sum := by
  intro j
  induction j with
  | zero => intro _; simpa using h.1
  | succ j ih =>
    intro hj
    rw [h.2 j (by omega), ih (by omega)]
    rcases Nat.lt_or_ge j C.cells.length with hl | hl
    · rw [List.take_add_one, List.map_append, List.sum_append, List.getElem?_eq_getElem hl, nth_eq hl]
      simp
    · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega), nth_of_le hl]
      simp

theorem flatten_getD : ∀ (Ls : List (List ℕ)) (j : ℕ) (hl : j < Ls.length) (m : ℕ)
    (hm : m < Ls[j].length), Ls.flatten.getD (((Ls.take j).map List.length).sum + m) 0 = Ls[j][m]
  | _ :: _, 0, _, m, hm => by
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatten_cons,
      List.getD_eq_getElem?_getD, List.getElem_cons_zero] at hm ⊢
    rw [List.getElem?_append_left hm, List.getElem?_eq_getElem hm, Option.getD_some]
  | a :: Ls, j + 1, hl, m, hm => by
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons,
      List.getElem_cons_succ] at hm ⊢
    have ih := flatten_getD Ls j (by simpa using hl) m hm
    rw [List.getD_eq_getElem?_getD] at ih ⊢
    rw [List.getElem?_append_right (by omega), show a.length + ((Ls.take j).map List.length).sum + m -
      a.length = ((Ls.take j).map List.length).sum + m by omega, ih]

/-- **The cells of a window are the certificate's**: window `j`'s cell `m` is the cell of value
`los[j] + m`. -/
theorem cont_locs {n : ℕ} (h : Cont C n) {j : ℕ} (hj : j ≤ n) {m : ℕ}
    (hm : m < (listElementOrDefault C.cells j []).length) :
    C.locs.getD (listElementOrDefault C.los j 0 + m) 0 = (listElementOrDefault C.cells j
        [])[m] := by
  have hl : j < C.cells.length := by
    by_contra hc
    rw [nth_of_le (by omega)] at hm
    exact absurd hm (Nat.not_lt_zero _)
  have hc : listElementOrDefault C.cells j [] = C.cells[j] := nth_eq hl
  rw [cont_lo h j hj]
  simp only [hc] at hm ⊢
  exact flatten_getD C.cells j hl m hm


theorem locAt_val {n : ℕ} (hcont : Cont C n) {i : ℕ} (hi : i ≤ n)
    (hins : C.insOk (listElementOrDefault C.ins i []) = true) (hn : C.cuts.length = n) {v : Core.V}
        {c : ℕ}
    (h : getF (C.locAt i) v.idx = some c) : C.locs.getD v.idx 0 = c := by
  rcases locAt_get h with ⟨m, hm, hv, hc⟩ | ⟨j, hj⟩
  · rw [hv, cont_locs hcont hi hm, hc]
  · have := List.all_eq_true.mp hins _ hj
    simp only [Bool.and_eq_true, Nat.ble_eq, beq_iff_eq] at this
    obtain ⟨⟨hjn, hlo⟩, hget⟩ := this
    obtain ⟨hm, hget⟩ := List.getElem?_eq_some_iff.mp hget
    rw [show v.idx = listElementOrDefault C.los j 0 + (v.idx - listElementOrDefault C.los j 0)
        by omega,
      cont_locs hcont (hn ▸ hjn) hm, hget]

/-! ### The valuation of a block -/

section Congr

variable {CR : Core.CallRel} {rd : Core.Reader} {σ σ' : Core.Val}

theorem atom_congr {a : Core.Atom} (h : ∀ v ∈ atomVals a, σ v = σ' v) :
    a.Holds rd σ ↔ a.Holds rd σ' := by
  cases a with
  | frameAddr q run =>
    simp only [atomVals, List.mem_cons, forall_eq_or_imp] at h
    simp only [Core.Atom.Holds, h.1]
    refine and_congr_right fun _ ↦ forall_congr' fun k ↦ forall_congr' fun hk ↦ ?_
    rw [h.2 _ (List.getElem_mem hk)]
  | hint => simp [Core.Atom.Holds]
  | keccak ins outs inOdd outOdd =>
    simp only [atomVals, List.mem_append] at h
    have hi : ins.map σ = ins.map σ' := List.map_congr_left fun v hv ↦ h v (.inl hv)
    have ho : outs.map σ = outs.map σ' := List.map_congr_left fun v hv ↦ h v (.inr hv)
    simp only [Core.Atom.Holds, hi, ho]
  | _ => simp_all [atomVals, Core.Atom.Holds]

mutual
theorem holds_congr : ∀ (s : Core.Stmt) {next : Prop} {kret : List E → Prop},
    (∀ v ∈ stmtVals s, σ v = σ' v) →
      (Core.Stmt.Holds CR rd σ s next kret ↔ Core.Stmt.Holds CR rd σ' s next kret)
  | .atom a, _, _, h => by
    simp only [Core.Stmt.Holds]
    rw [atom_congr (by simpa [stmtVals] using h)]
  | .ite c z n, _, _, h => by
    simp only [stmtVals, List.mem_cons, List.mem_append, forall_eq_or_imp] at h
    simp only [Core.Stmt.Holds, h.1]
    rw [holdsList_congr z fun v hv ↦ h.2 v (Or.inl hv), holdsList_congr n fun v hv ↦ h.2 v (Or.inr hv)]
  | .match_ x arms, _, _, h => by
    simp only [stmtVals, List.mem_cons, forall_eq_or_imp] at h
    simp only [Core.Stmt.Holds]
    exact holdsArms_congr x arms 0 h.1 h.2
  | .call f args rets, _, _, h => by
    simp only [stmtVals, List.mem_append] at h
    simp only [Core.Stmt.Holds]
    rw [List.map_congr_left fun v hv ↦ h v (Or.inl hv), List.map_congr_left fun v hv ↦ h v (Or.inr hv)]
  | .callIf c f args, _, _, h => by
    simp only [stmtVals, List.mem_cons, forall_eq_or_imp] at h
    simp only [Core.Stmt.Holds, h.1]
    rw [List.map_congr_left h.2]
  | .dispatch x fs args rets, _, _, h => by
    simp only [stmtVals, List.mem_cons, List.mem_append, forall_eq_or_imp] at h
    simp only [Core.Stmt.Holds, h.1]
    rw [List.map_congr_left fun v hv ↦ h.2 v (Or.inl hv),
      List.map_congr_left fun v hv ↦ h.2 v (Or.inr hv)]
  | .ret vs, _, _, h => by
    simp only [Core.Stmt.Holds]
    rw [List.map_congr_left fun v hv ↦ h v (by simpa [stmtVals] using hv)]

theorem holdsList_congr : ∀ (ss : List Core.Stmt) {next : Prop} {kret : List E → Prop},
    (∀ v ∈ stmtsVals ss, σ v = σ' v) →
      (Core.Stmt.HoldsList CR rd σ ss next kret ↔ Core.Stmt.HoldsList CR rd σ' ss next kret)
  | [], _, _, _ => Iff.rfl
  | s :: ss, _, _, h => by
    simp only [stmtsVals, List.mem_append] at h
    simp only [Core.Stmt.HoldsList]
    rw [holdsList_congr ss fun v hv ↦ h v (Or.inr hv)]
    exact holds_congr s fun v hv ↦ h v (Or.inl hv)

theorem holdsArms_congr (x : Core.V) : ∀ (arms : List (List Core.Stmt)) (j : ℕ) {next : Prop}
    {kret : List E → Prop}, σ x = σ' x → (∀ v ∈ armsVals arms, σ v = σ' v) →
      (Core.Stmt.HoldsArms CR rd σ x j arms next kret ↔ Core.Stmt.HoldsArms CR rd σ' x j arms next kret)
  | [], _, _, _, _, _ => Iff.rfl
  | a :: as, j, _, _, hx, h => by
    simp only [armsVals, List.mem_append] at h
    simp only [Core.Stmt.HoldsArms, hx]
    rw [holdsList_congr a fun v hv ↦ h v (Or.inl hv), holdsArms_congr x as (j + 1) hx fun v hv ↦ h v (Or.inr hv)]
end

end Congr

/-! ### A window -/

/-- **The run at window `i`'s start** with `k` steps left: there, its environment and the facts
and bounds handed on hold. -/
def WinStart (L : MemoryImage κ) (fp : K) (f : CompiledFunction) (C : Cert) (i k : ℕ) : Prop :=
  (if C.succAt i = [] then
    SafeReached guestProgram L k ⟨addressOfIndex (f.entryPc + (C.cutAt i).J), fp⟩
  else ∃ e, ∃ _ : e < (C.succAt i).length, wd L fp (C.selAt i) = ofK (addressOfIndex e) ∧
    SafeReached guestProgram L k ⟨addressOfIndex (f.entryPc + (C.succAt i)[e]), fp⟩) ∧
    EnvHolds L fp (envOf (C.cutAt i).env) ∧
    (∀ p ∈ (C.cutAt i).facts, p.2.Holds L fp) ∧ BndHolds L fp (C.cutAt i).bnd

/-- What a function's return does, in every window's context. -/
abbrev RetOf (L : MemoryImage κ) (fp : K) (G : Glob) (f : CompiledFunction) (cf : Core.Fn) (C
    : Cert)
    (main : Bool) (Kb : ℕ) : List E → Prop :=
  RetWords L fp (C.fxAt G f cf main 0 [] .nil .nil) Kb

theorem checkWin_parts {main : Bool} {i : ℕ} (hc : checkWin G f cf C main i = true) :
    C.contOk i = true ∧ C.insOk (listElementOrDefault C.ins i []) = true := by
  unfold checkWin at hc
  rcases hR : execWinS C.facts f (C.cutAt i).J (C.cutAt i).env ((C.succAt i).drop 1) (C.endAt f i) with
    ⟨segs, dead⟩
  rw [hR] at hc
  simp only [listSeq_eq, Trie.seq_eq, Bool.and_eq_true] at hc
  exact ⟨hc.1.1.1.1.1, hc.1.1.1.1.2⟩

/-- The first window's check fixes whether the frame is `main`'s. -/
theorem checkWin_fpOne {main : Bool} (hc : checkWin G f cf C main 0 = true) : main = C.facts.fpOne := by
  unfold checkWin at hc
  rcases hR : execWinS C.facts f (C.cutAt 0).J (C.cutAt 0).env ((C.succAt 0).drop 1) (C.endAt f 0) with
    ⟨segs, dead⟩
  rw [hR] at hc
  simp only [listSeq_eq, Trie.seq_eq, Bool.and_eq_true, beq_self_eq_true, Bool.cond_true,
    beq_iff_eq] at hc
  exact hc.1.2.2

/-- **A checked window's run**, from its start with `k ≤ Kb` steps left, the windows' cells
consecutive: its statements hold under the function's valuation, and the run reaches the next
window's start, or, the last window, its statements end by the return; the first window has the
parameters in their cells. -/
theorem checkWin_run {main : Bool} {i : ℕ} (hc : checkWin G f cf C main i = true)
    (hcont : Cont C C.cuts.length) (hiN : i ≤ C.cuts.length)
    (hf : f ∈ Data.functions) (hpows : C.facts.pows.Ok) (hκ : κ ≤ 32) {fp : K}
    (hfp : C.facts.fpOne = true → fp = 1) {Kb : ℕ}
    (hC : ∀ j, FunSpecLtReached guestProgram L Kb (G.sig j).entry (Pre G L j) (Post Prog G L cert A j))
    (hjt : JTHolds G L) (hmem : MemPre L fp C.mem) (hknown : MemKnown L fp (C.cutAt i).known)
    (hknownIf : MemIf L fp (C.cutAt i).knownIf) (hsems : SemHolds G L fp (C.cutAt i).sems) {k : ℕ} (hk : k ≤ Kb) (hs : WinStart L fp f C i k) :
    (i = 0 → ∀ m (hm : m < cf.params.length), C.locs.getD cf.params[m].idx 0 = 2 + m) ∧
    (i < C.cuts.length → Core.Stmt.HoldsList (RL Prog L cert A) L.read (valG L fp C)
        (C.stmtsAt cf i) True (RetOf L fp G f cf C main Kb) ∧
        (C.cutAt i).start ≤ (C.cutAt (i + 1)).start ∧ ∃ k' ≤ k, WinStart L fp f C (i + 1) k') ∧
    (C.cuts.length ≤ i → Core.Stmt.HoldsList (RL Prog L cert A) L.read (valG L fp C)
        (C.stmtsAt cf i) False (RetOf L fp G f cf C main Kb)) := by
  have hins := (checkWin_parts hc).2
  unfold checkWin at hc
  rcases hR : execWinS C.facts f (C.cutAt i).J (C.cutAt i).env ((C.succAt i).drop 1) (C.endAt f i) with
    ⟨segs, dead⟩
  rw [hR] at hc
  simp only [listSeq_eq, Trie.seq_eq, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨-, -⟩, hcov⟩, hlink⟩, h0⟩, hc⟩ := hc
  have hval : ∀ {v : Core.V} {c : ℕ}, getF (C.locAt i) v.idx = some c → C.locs.getD v.idx 0 = c :=
    fun h ↦ locAt_val hcont hiN hins rfl h
  have hcongr : ∀ v ∈ stmtsVals (C.stmtsAt cf i), val L fp (C.locAt i) v = valG L fp C v := by
    intro v hv
    have := List.all_eq_true.mp hcov v hv
    obtain ⟨c, hcv⟩ := Option.isSome_iff_exists.mp this
    simp only [val, valG, cellOf, getF_eq] at hcv ⊢
    rw [hcv, hval (by rwa [getF_eq]), Option.getD_some]
  set X : Fx := C.fxAt G f cf main i segs (index segs) (C.locAt i) with hX
  have hctx : Exec.Ctx C.facts κ fp := ⟨hpows, hfp, hκ⟩
  have H : WalkHyp L fp f X := ⟨hctx, guest_fetches hf, rfl, fun s hs ↦
    execWinS_good hctx (guest_fetches hf) _ _ _ _ s (by rw [hR]; exact hs), rfl, hlink⟩
  have W : WalkEnv Prog cert A L fp f X Kb :=
    ⟨H, hjt, (memIf_of_pre hmem).append ((memIf_of_known hknown).append hknownIf), hknown, hsems, hC⟩
  have hret : RetWords L fp X Kb = RetOf L fp G f cf C main Kb := rfl
  have hconv : ∀ {N : Prop}, Core.Stmt.HoldsList (RL Prog L cert A) L.read (val L fp X.loc)
      (C.stmtsAt cf i) N (RetWords L fp X Kb) →
      Core.Stmt.HoldsList (RL Prog L cert A) L.read (valG L fp C) (C.stmtsAt cf i) N
        (RetOf L fp G f cf C main Kb) := fun h ↦
    hret ▸ (holdsList_congr _ hcongr).mp h
  refine ⟨fun hi m hm ↦ ?_, ?_⟩
  · subst hi
    simp only [beq_self_eq_true, Bool.cond_true, Bool.and_eq_true] at h0
    have := runAt_sound h0.1 m hm
    unfold cellOf at this
    rcases hg : getF (C.locAt 0) cf.params[m].idx with _ | c
    · rw [hg, Option.getD_none] at this; omega
    · rw [hg, Option.getD_some] at this
      rw [hval hg, this]
  split at hc
  · rename_i st hst
    simp only [Bool.and_eq_true] at hc
    obtain ⟨hsub, hend⟩ := hc
    have hstB : st.book = bookOf (C.cutAt i).facts .nil ∧ st.bnd = (C.cutAt i).bnd := by
      unfold segAt at hst
      split at hst
      · simp only [Bool.cond_eq_ite, beq_iff_eq] at hst
        split_ifs at hst
        obtain rfl := Option.some.inj hst
        exact ⟨rfl, rfl⟩
      · cases hst
    have hB0 : BookHolds L fp st.book := hstB.1 ▸ bookOf_holds _ BookHolds.nil hs.2.2.1
    have hb0 : BndHolds L fp st.bnd := hstB.2 ▸ hs.2.2.2
    -- The run at an offset `t` starting a segment of the window, its environment holding there.
    have hrunAt : ∀ t, SafeReached guestProgram L k ⟨addressOfIndex (f.entryPc + t), fp⟩ →
        (∀ s, X.idx.get t = some s → s.start = t → s.env.sub Sym.beq (envOf (C.cutAt i).env) = true) →
        (X.idx.get t ≠ none) → SegRun L fp f X Kb t k := by
      intro t hsafe hsub' hsome
      refine ⟨hsafe, fun s hs' hs0 ↦ ?_, fun _ hn ↦ absurd hn hsome⟩
      have hmem : s ∈ X.segs := index_get hs'
      have he : EnvHolds L fp s.env := hs.2.1.sub (hsub' s hs' hs0)
      refine ⟨hmem, he, k, hk, le_rfl, (H.good s hmem).1 k he ?_⟩
      rw [hs0]
      exact hsafe
    have hwalk : ∀ (N : Prop), walkFrom X (C.cutAt i).env (C.selAt i) (C.succAt i) (C.stmtsAt cf i) st ≠ .fail →
        (∀ J, walkFrom X (C.cutAt i).env (C.selAt i) (C.succAt i) (C.stmtsAt cf i) st = .join J → ∀ k', k' ≤ k →
          SegRun L fp f X Kb J k' → N) →
        (∀ x s, walkFrom X (C.cutAt i).env (C.selAt i) (C.succAt i) (C.stmtsAt cf i) st = .chain x s → ChainK L fp f X Kb x s k N) →
        Core.Stmt.HoldsList (RL Prog L cert A) L.read (val L fp X.loc) (C.stmtsAt cf i) N
            (RetWords L fp X Kb) ∧
          (∀ J, walkFrom X (C.cutAt i).env (C.selAt i) (C.succAt i) (C.stmtsAt cf i) st = .join J → ∃ k' ≤ k, Arrive L fp f X Kb J k') ∧
          (∀ x s, walkFrom X (C.cutAt i).env (C.selAt i) (C.succAt i) (C.stmtsAt cf i) st = .chain x s → ChainArr L fp f X Kb x s k) := by
      intro N hne hj hcn
      by_cases hnil : C.succAt i = []
      · have hw : walkFrom X (C.cutAt i).env (C.selAt i) (C.succAt i) (C.stmtsAt cf i) st = chkL X (C.stmtsAt cf i) st [] := by
          simp [walkFrom, hnil]
        rw [hw] at hne hj hcn ⊢
        have h1 : SafeReached guestProgram L k ⟨addressOfIndex (f.entryPc + (C.cutAt i).J), fp⟩ := by
          have := hs.1
          simp only [hnil, ↓reduceIte] at this
          exact this
        have hrun : SegRun L fp f X Kb (C.cutAt i).J k := by
          refine ⟨h1, fun s hs' hs0 ↦ ?_, fun _ hn ↦ ?_⟩
          swap
          · unfold segAt at hst
            rw [getF_eq, hn] at hst
            cases hst
          have hmem : s ∈ X.segs := index_get hs'
          have hs'' : st.seg = s := by
            unfold segAt at hst
            rw [getF_eq, hs'] at hst
            simp only [hs0, beq_self_eq_true, Bool.cond_true, Option.some.injEq] at hst
            rw [← hst]
          have he : EnvHolds L fp s.env := hs'' ▸ hs.2.1.sub hsub
          refine ⟨hmem, he, k, hk, le_rfl, (H.good s hmem).1 k he ?_⟩
          rw [hs0]
          exact h1
        have hp := segAt_ok H hst hrun (bookOf_holds _ BookHolds.nil hs.2.2.1) hs.2.2.2
        obtain ⟨h1, -, h3, h4⟩ := walk_sound W (C.stmtsAt cf i) st [] k N hp hne hj hcn
        exact ⟨h1, h3, h4⟩
      · have hst' : startsOk X.idx (C.cutAt i).env (C.succAt i) = true := by
          by_contra hn
          apply hne
          simp [walkFrom, hnil, hn]
        have hw : walkFrom X (C.cutAt i).env (C.selAt i) (C.succAt i) (C.stmtsAt cf i) st =
            chainL X (C.selAt i) (C.succAt i) st.book st.psi st.bnd (C.stmtsAt cf i) [] := by
          simp [walkFrom, hnil, hst']
        rw [hw] at hne hj hcn ⊢
        have h1 := hs.1
        simp only [hnil, ↓reduceIte] at h1
        obtain ⟨e, he, hx, hsafe⟩ := h1
        have hrun : SegRun L fp f X Kb (C.succAt i)[e] k := by
          have hok := List.all_eq_true.mp hst' _ (List.getElem_mem he)
          split at hok
          · rename_i s hs'
            simp only [Bool.and_eq_true, beq_iff_eq] at hok
            rw [getF_eq] at hs'
            refine hrunAt _ hsafe (fun s' hs'' _ ↦ ?_) (by rw [hs']; simp)
            rw [hs'] at hs''
            obtain rfl := Option.some.inj hs''
            exact hok.2
          · simp at hok
        obtain ⟨h1, -, h3, h4⟩ := chain_sound W (C.stmtsAt cf i) _ _ _ _ _ [] k N hB0 hb0
          ⟨e, he, hx, hrun⟩ hne hj hcn
        exact ⟨h1, h3, h4⟩
    unfold winEnd at hend
    by_cases hi : i < C.cuts.length
    · have hb : Nat.blt i C.cuts.length = true := Nat.blt_eq.mpr hi
      rw [hb] at hend
      simp only [Bool.cond_true, Bool.and_eq_true, Nat.ble_eq] at hend
      obtain ⟨⟨hchk, hle⟩, henv⟩ := hend
      have hw : X.win = some ((C.cutAt (i + 1)).J, (C.cutAt (i + 1)).facts, (C.cutAt (i + 1)).bnd) := by
        simp only [hX, Cert.fxAt, hb, Bool.cond_true]
      have hwJ : X.wJ = (C.cutAt (i + 1)).J := by simp only [hX, Cert.fxAt, hb, Bool.cond_true]
      have hwenv : X.wenv = envOf (C.cutAt (i + 1)).env := by
        simp only [hX, Cert.fxAt, hb, Bool.cond_true]
      refine ⟨fun _ ↦ ?_, fun h ↦ absurd hi (Nat.not_lt.mpr h)⟩
      by_cases hnil : C.succAt (i + 1) = []
      · simp only [hnil, List.isEmpty_nil, Bool.cond_true, beq_iff_eq] at hchk
        obtain ⟨hl, harr, -⟩ := hwalk True (by rw [hchk]; simp) (fun _ _ _ _ _ ↦ trivial)
          (fun _ _ h ↦ by rw [hchk] at h; cases h)
        obtain ⟨k', hk', ⟨hsafe, hseg, hwend⟩, hhand⟩ := harr _ hchk
        refine ⟨hconv hl, hle, k', hk', ?_, ?_, hhand _ _ _ hw rfl⟩
        · simp only [hnil, ↓reduceIte]
          exact hsafe
        · split at henv
          · rename_i s hs'
            simp only [Bool.and_eq_true, beq_iff_eq] at henv
            rw [getF_eq] at hs'
            exact (hseg s hs' henv.1).2.1.sub henv.2
          · rename_i hs'
            rw [getF_eq] at hs'
            have := hwend hwJ.symm hs'
            rwa [hwenv] at this
      · have hne' : (C.succAt (i + 1)).isEmpty = false := by
          cases h : C.succAt (i + 1) with
          | nil => exact absurd h hnil
          | cons _ _ => rfl
        simp only [hne', Bool.cond_false, Bool.and_eq_true, beq_iff_eq] at hchk
        obtain ⟨hchk, hhead⟩ := hchk
        obtain ⟨hl, -, hrc⟩ := hwalk True (by rw [hchk]; simp)
          (fun _ h ↦ by rw [hchk] at h; cases h) (fun _ _ _ _ _ _ _ _ _ ↦ trivial)
        obtain ⟨e, he, hx, k', hk', hrun, hhand, hen⟩ := hrc _ _ hchk
        have hJ0 : (C.succAt (i + 1)).headD 0 = (C.cutAt (i + 1)).J := by
          cases h : C.succAt (i + 1) with
          | nil => exact absurd h hnil
          | cons a as => rw [h] at hhead; simpa using hhead
        rw [hJ0] at hhand hen
        refine ⟨hconv hl, hle, k', hk', ?_, ?_, hhand _ _ _ hw rfl⟩
        · simp only [hnil, ↓reduceIte]
          exact ⟨e, he, hx, hrun.1⟩
        · have := hen hwJ.symm
          rwa [hwenv] at this
    · have hb : Nat.blt i C.cuts.length = false := blt_false (Nat.not_lt.mp hi)
      rw [hb] at hend
      simp only [Bool.cond_false, beq_iff_eq] at hend
      refine ⟨fun h ↦ absurd h hi, fun _ ↦ ?_⟩
      obtain ⟨hl, -, -⟩ := hwalk False (by rw [hend]; simp) (fun J hJ ↦ by rw [hend] at hJ; cases hJ)
        (fun _ _ h ↦ by rw [hend] at h; cases h)
      exact hconv hl
  · simp at hc

theorem stmtsAt_lt {i : ℕ} (hi : i < C.cuts.length) (hle : (C.cutAt i).start ≤ (C.cutAt (i + 1)).start) :
    cf.body.take (C.cutAt i).start ++ C.stmtsAt cf i = cf.body.take (C.cutAt (i + 1)).start := by
  simp only [Cert.stmtsAt, Nat.blt_eq.mpr hi, Bool.cond_true]
  rw [← List.drop_take, ← Nat.min_eq_left hle, ← List.take_take, Nat.min_eq_left hle,
    List.take_append_drop]

theorem stmtsAt_last {i : ℕ} (hi : C.cuts.length ≤ i) :
    cf.body.take (C.cutAt i).start ++ C.stmtsAt cf i = cf.body := by
  simp only [Cert.stmtsAt, blt_false hi, Bool.cond_false]
  exact List.take_append_drop _ _

theorem cont_of {main : Bool} (hc : ∀ i ≤ C.cuts.length, checkWin G f cf C main i = true) :
    Cont C C.cuts.length := by
  refine ⟨?_, fun i hi ↦ ?_⟩
  · have := (checkWin_parts (hc 0 (Nat.zero_le _))).1
    simp only [Cert.contOk, beq_self_eq_true, Bool.cond_true, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1
  · have := (checkWin_parts (hc i (by omega))).1
    simp only [Cert.contOk, Nat.blt_eq.mpr hi, Bool.cond_true, Bool.and_eq_true, beq_iff_eq] at this
    exact this.2

/-- **A checked function's run**, from its entry with `k` steps left, every window checked and
each window's memory bounds and semantic pairs given by the statements before it: its body holds
at its frame (`BodyHoldsAt`), its calls located at frames with `A`, and a run of a function other
than `main` returns in fewer steps. Its frame is in the memory and its body holds under the frame's valuation, `cert cf.name`
being its certificate. -/
theorem checkWins_run {main : Bool} (hc : ∀ i ≤ C.cuts.length, checkWin G f cf C main i = true)
    (hf : f ∈ Data.functions) (hfind : Prog.find? cf.name = some cf) (hpows : C.facts.pows.Ok)
    (hκ : κ ≤ 32) {fp : K} (hfp : C.facts.fpOne = true → fp = 1) {k : ℕ}
    (hcert : cert cf.name = C)
    (hC : ∀ i, FunSpecLtReached guestProgram L k (G.sig i).entry (Pre G L i) (Post Prog G L cert A i))
    (hjt : JTHolds G L) (henv : EnvHolds L fp C.facts.entryEnv) (hpre : BndHolds L fp C.pre)
    (hmem : MemPre L fp C.mem) (hsem : SemHolds G L fp C.sem)
    (hknown : ∀ i ≤ C.cuts.length, 0 < i → Core.Stmt.HoldsList (RL Prog L cert A) L.read
      (valG L fp C) (cf.body.take (C.cutAt i).start) True (fun _ ↦ True) →
        MemKnown L fp (C.cutAt i).known ∧ MemIf L fp (C.cutAt i).knownIf ∧
          SemHolds G L fp (C.cutAt i).sems)
    (hsafe : SafeReached guestProgram L k ⟨addressOfIndex f.entryPc, fp⟩) :
    BodyHoldsAt Prog L cert A cf.name fp (frameWords L fp 2 cf.params.length)
        (frameWords L fp (2 + cf.params.length) C.nret) ∧ BndHolds L fp C.post ∧
      (main = false → ∃ k' < k, ∃ r, retRegs L fp = some r ∧ SafeReached guestProgram L k' r) ∧
      InMem κ fp ∧ cf.params.map (valG L fp C) = frameWords L fp 2 cf.params.length ∧
      Core.Stmt.HoldsList (RL Prog L cert A) L.read (valG L fp C) cf.body False
        (fun rs ↦ rs = frameWords L fp (2 + cf.params.length) C.nret) := by
  have hcont := cont_of hc
  have run := fun i (hi : i ≤ C.cuts.length) {k'} hk' hs (hkn : _ ∧ _ ∧ _) ↦
    checkWin_run (Prog := Prog) (hc i hi) hcont hi hf hpows hκ hfp hC hjt hmem hkn.1 hkn.2.1 hkn.2.2
      (k := k')
      hk' hs
  have hkn0 : MemKnown L fp (C.cutAt 0).known ∧ MemIf L fp (C.cutAt 0).knownIf ∧
      SemHolds G L fp (C.cutAt 0).sems :=
    ⟨fun _ h ↦ by simp [Cert.cutAt] at h, fun _ h ↦ by simp [Cert.cutAt] at h, hsem⟩
  have hs0 : WinStart L fp f C 0 k :=
    ⟨by simpa [Cert.cutAt, Cert.succAt, Cert.enteredAt] using hsafe, henv, by simp [Cert.cutAt], hpre⟩
  have reach : ∀ i ≤ C.cuts.length, ∃ k' ≤ k, WinStart L fp f C i k' ∧
      Core.Stmt.HoldsList (RL Prog L cert A) L.read (valG L fp C)
        (cf.body.take (C.cutAt i).start) True (RetOf L fp G f cf C main k) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨k, le_rfl, hs0, ?_⟩
      simp [Cert.cutAt, Core.Stmt.HoldsList]
    | succ i ih =>
      intro hi
      obtain ⟨k', hk', hs, hl⟩ := ih (by omega)
      have hkn : MemKnown L fp (C.cutAt i).known ∧ MemIf L fp (C.cutAt i).knownIf ∧
          SemHolds G L fp (C.cutAt i).sems := by
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · exact hkn0
        · exact hknown i (by omega) hi0
            (Core.holdsList_mono (fun _ _ _ h ↦ h) _ id (fun _ _ ↦ trivial) hl)
      obtain ⟨hw, hle, k'', hk'', hs'⟩ := (run i (by omega) hk' hs hkn).2.1 (by omega)
      refine ⟨k'', by omega, hs', ?_⟩
      rw [← stmtsAt_lt (by omega) hle, Core.holdsList_append]
      exact Core.holdsList_mono (fun _ _ _ h ↦ h) _ (fun _ ↦ hw) (fun _ h ↦ h) hl
  obtain ⟨k', hk', hs, hl⟩ := reach _ le_rfl
  have hkn : MemKnown L fp (C.cutAt C.cuts.length).known ∧
      MemIf L fp (C.cutAt C.cuts.length).knownIf ∧ SemHolds G L fp (C.cutAt C.cuts.length).sems := by
    rcases Nat.eq_zero_or_pos C.cuts.length with h0 | hi0
    · rw [h0]; exact hkn0
    · exact hknown _ le_rfl hi0 (Core.holdsList_mono (fun _ _ _ h ↦ h) _ id (fun _ _ ↦ trivial) hl)
  have hr := run _ le_rfl hk' hs hkn
  have hlast := hr.2.2 le_rfl
  have hall : Core.Stmt.HoldsList (RL Prog L cert A) L.read (valG L fp C) cf.body False
      (RetOf L fp G f cf C main k) := by
    rw [← stmtsAt_last (C := C) (i := C.cuts.length) le_rfl, Core.holdsList_append]
    exact Core.holdsList_mono (fun _ _ _ h ↦ h) _ (fun _ ↦ hlast) (fun _ h ↦ h) hl
  have hparams := (run 0 (Nat.zero_le _) le_rfl hs0 hkn0).1 rfl
  obtain ⟨rs, hw, hback, hpost⟩ := (holdsList_reach cf.body hall).resolve_left id
  have hpar : cf.params.map (valG L fp C) = frameWords L fp 2 cf.params.length := by
    apply List.ext_getElem (by simp [frameWords])
    intro m h1 h2
    simp only [List.getElem_map, frameWords, List.getElem_range, valG]
    rw [hparams m (by simpa using h1)]
  have hbody : Core.Stmt.HoldsList (RL Prog L cert A) L.read (valG L fp C) cf.body False
      (fun rs ↦ rs = frameWords L fp (2 + cf.params.length) C.nret) :=
    Core.holdsList_mono (fun _ _ _ h ↦ h) cf.body id (fun rs h ↦ h.1) hall
  have hA : InMem κ fp := by
    cases main with
    | true =>
      have h1 : fp = 1 := hfp (checkWin_fpOne (hc 0 (Nat.zero_le _))).symm
      exact ⟨0, Nat.two_pow_pos _, by rw [h1]; simp [addressOfIndex]⟩
    | false =>
      obtain ⟨-, -, r, hr, -⟩ := hback rfl
      unfold retRegs at hr
      obtain ⟨d, hd, -⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨i, hi, -⟩ := (Core.read_some_iff (by omega) L _ d).mp hd
      exact ⟨i, i.isLt, by simpa [addressOfIndex] using hi⟩
  have hval : frameVal L cert cf.name fp = valG L fp C := by rw [frameVal, hcert]
  exact ⟨⟨cf, hfind, hval ▸ hpar, hval ▸ hbody⟩, hpost, fun hm ↦ hback hm, hA, hpar, hbody⟩

end Fn

end
end LeanVM.Guest.Check
