/-
  LeanVM.Guest.CheckSound

  Soundness of the checker: a function whose check passes satisfies its core IR relation, under
  its callees' contracts.
-/

module

public import LeanVM.Guest.Check

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

variable {κ : ℕ} (L : MemImage κ) (fp : K)

/-- The word in frame cell `o`, `0` if none. -/
noncomputable def wd (o : ℕ) : E := (L.read (fp * gpow o)).getD 0

/-- The valuation of a check: every value is the word in its cell. -/
noncomputable def val (loc : Trie ℕ) : Core.Val := fun v ↦ wd L fp (cellOf loc v)

/-- The `n` words of the frame from cell `o`. -/
noncomputable def frameWords (o n : ℕ) : List E := (List.range n).map fun i ↦ wd L fp (o + i)

/-- The atoms filed in a book hold. -/
def BookHolds (B : Book) : Prop := ∀ o, ∀ a ∈ look B o, a.Holds L fp

/-- The bounds hold: `fp[c] = g^e` with `e < n` for each `(c, n)`. -/
def BndHolds (bnd : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ bnd, ∃ e < p.2, L.read (fp * gpow p.1) = some (ofK (gpow e))

end Words

section Basic

variable {κ : ℕ} {L : MemImage κ} {fp : K}

theorem wd_of {o : ℕ} {v : E} (h : L.read (fp * gpow o) = some v) : wd L fp o = v := by
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

theorem nth_eq {α : Type} {l : List α} {n : ℕ} {d : α} (h : n < l.length) : nth l n d = l[n] :=
  Option.some.inj ((nth_eq_getElem? d h).symm.trans (List.getElem?_eq_getElem h))

theorem limb_ofK0 (a : K) : (ofK a).limb 0 = a := by simp

theorem char2 (a b : E) : a + (a + b) = b := by
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem ofBits_toNat (a : K) : K.ofBits a.toBitVec.toNat = a := by
  simp [K.ofBits, BitVec.ofNat_toNat]

theorem eq_imm_of_limbs {x : E} {k0 k1 k2 : ℕ} (h0 : limbNat x 0 = k0) (h1 : limbNat x 1 = k1)
    (h2 : limbNat x 2 = k2) : x = OInstr.imm k0 k1 k2 := by
  subst h0 h1 h2
  rw [OInstr.imm, limbNat, limbNat, limbNat, ofBits_toNat, ofBits_toNat, ofBits_toNat,
    ofLimbs_limb]

end Basic

/-! ## The atoms of a book -/

section Atoms

variable {κ : ℕ} {L : MemImage κ} {fp : K} {B : Book}

theorem setImm_sound (hB : BookHolds L fp B) {c l0 l1 l2 : ℕ} (h : setImm B c l0 l1 l2 = true) :
    L.read (fp * gpow c) = some (OInstr.imm l0 l1 l2) := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  have hh := hB c a ha
  split at hp
  · rename_i pc o k0 k1 k2
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hp
    exact hh
  · simp at hp

theorem setIs_sound (hB : BookHolds L fp B) {c : ℕ} {x : E} (h : setIs B c x = true) :
    L.read (fp * gpow c) = some x := by
  rw [eq_imm_of_limbs rfl rfl rfl (x := x)]
  exact setImm_sound hB h

theorem perm3_sound {x y z p q r : ℕ} (h : perm3 x y z p q r = true) {vX vY : E}
    (hx : L.read (fp * gpow x) = some vX) (hy : L.read (fp * gpow y) = some vY)
    (hz : L.read (fp * gpow z) = some (vX + vY)) : wd L fp r = wd L fp p + wd L fp q := by
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
    ∃ vA vB, L.read (fp * gpow a) = some vA ∧ L.read (fp * gpow b) = some vB ∧
      L.read (fp * gpow d) = some (vA * vB) := by
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
    L.read (fp * gpow a) = L.read (fp * gpow b) := by
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

theorem loadOk_sound (hB : BookHolds L fp B) {d p off : ℕ} (h : loadOk B d p off = true) :
    ∃ pv, L.read (fp * gpow p) = some pv ∧ IsInK pv ∧
      ∃ v, L.read (fp * gpow d) = some v ∧ L.read (pv.limb 0 * gpow off) = some v := by
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

theorem blakeOk_sound (hB : BookHolds L fp B) {m0 m1 m2 m3 cv0 cv1 o0 o1 md : ℕ}
    (h : blakeOk B m0 m1 m2 m3 cv0 cv1 o0 o1 md = true) :
    CompressCells ![wd L fp m0, wd L fp m1, wd L fp m2, wd L fp m3] (wd L fp cv0) (wd L fp cv1)
      (wd L fp o0) (wd L fp o1) (wd L fp md) := by
  simp only [blakeOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨rfl, rfl⟩, h⟩ := h
  obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
  have hh := hB o0 x hx
  split at hp
  · simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hp
    obtain ⟨w0, w1, w2, w3, c0, c1, d0, d1, v, h0, h1, h2, h3, hc0, hc1, hd0, hd1, hv, hc⟩ := hh
    rw [← gpow_succ] at hc1 hd1
    rw [wd_of h0, wd_of h1, wd_of h2, wd_of h3, wd_of hc0, wd_of hc1, wd_of hd0, wd_of hd1,
      wd_of hv]
    exact hc
  · simp at hp

theorem neOk_sound (hB : BookHolds L fp B) {x i p : ℕ} (h : neOk B x i p = true) :
    wd L fp p = wd L fp x * wd L fp i ∧ wd L fp p = 1 := by
  simp only [neOk, Bool.and_eq_true] at h
  refine ⟨mulOk_wd hB h.1, wd_of ?_⟩
  rw [show (1 : E) = OInstr.imm 1 0 0 from (imm_of_ofBits rfl).trans ofK_one |>.symm]
  exact setImm_sound hB h.2

theorem rangeOk_sound (hB : BookHolds L fp B) {x y t1 t2 k : ℕ}
    (h : rangeOk B x y t1 t2 k = true) :
    Core.LoadHolds L.read (wd L fp x) 0 (wd L fp t1) ∧ wd L fp k = wd L fp x * wd L fp y ∧
      Core.LoadHolds L.read (wd L fp y) 0 (wd L fp t2) := by
  simp only [rangeOk, Bool.and_eq_true] at h
  exact ⟨loadOk_holds hB h.1.1, mulOk_wd hB h.1.2, loadOk_holds hB h.2⟩

theorem bounceOk_sound (hB : BookHolds L fp B) {x : ℕ} (h : bounceOk B x = true) :
    L.read (fp * gpow x) = some (ofK fp) := by
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
    (h : fpgAt B ψ x = some e) : L.read (fp * gpow x) = some (ofK (fp * gpow e)) := by
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
    L.read (fp * gpow y) = some (ofK (gpow e)) := by
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
      L.read ((wd L fp p).limb 0 * gpow k) = some w → w = val L fp loc run[k] := by
  obtain ⟨a, ha, hq⟩ := List.any_eq_true.mp h
  have hh := hB p a ha
  split at hq
  · rename_i pc x y z
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    obtain ⟨rfl, hq⟩ := hq
    split at hq
    · rename_i e1 e2 h1 h2
      obtain ⟨vX, vY, hx, hy, hz⟩ := hh
      rw [fpgAt_sound hB hψ h1] at hx
      rw [gpAt_sound hF hB hψ h2] at hy
      obtain rfl := Option.some.inj hx
      obtain rfl := Option.some.inj hy
      have hp : wd L fp z = ofK (fp * gpow (e1 + e2)) := by
        rw [wd_of hz, ← ofK_mul, mul_assoc, gpow, gpow, gpow, ← pow_add]
      rw [hp]
      refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, fun k hk w hw ↦ ?_⟩
      have hl : (ofK (fp * gpow (e1 + e2))).limb 0 = fp * gpow (e1 + e2) := by simp
      have ha : fp * gpow (e1 + e2) * gpow k = fp * gpow (e1 + e2 + k) := by
        rw [mul_assoc, gpow, gpow, gpow, ← pow_add]
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
  | blake2s m0 m1 m2 m3 cv0 cv1 o0 o1 md => exact blakeOk_sound hB h
  | frameAddr p run => exact addrOk_sound hF hB hψ h
  | hint _ => trivial

end Atoms

/-! ## Contracts -/

section Contracts

variable {κ : ℕ} (P : Core.Program) (G : Glob) (L : MemImage κ)

/-- The jump table holds: slot `s` of the frame of `main` (`fp = 1`) holds `g^t`. -/
def JTHolds : Prop := ∀ s t, G.jt.get s = some t → L.read (gpow s) = some (ofK (gpow t))

/-- Memory bounded through frame cells: for each `(o, len, n)`, the word at `fp[o]·g^c` is `g^e`
with `e < n` for every `c < len`. -/
def MemPre (fp : K) (mem : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ m ∈ mem, ∀ c < m.2.1, ∃ p, L.read (fp * gpow m.1) = some p ∧ IsInK p ∧
    ∃ e < m.2.2, L.read (p.limb 0 * gpow c) = some (ofK (gpow e))

/-- The words of each pair of cells are in the program's semantic relation. -/
def SemHolds (fp : K) (sems : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ sems, G.sem L.read (wd L fp p.1) (wd L fp p.2)

/-- **A function's precondition** at frame `fp`: it is one the program checks, the jump table
holds, its self frame pointer cells hold `fp`, its bounded frame cells and memory are bounded,
and its pairs of cells are in the semantic relation. -/
def Pre (j : ℕ) (fp : K) : Prop :=
  G.good j = true ∧ JTHolds G L ∧ EnvHolds L fp (envOf (G.sig j).env) ∧
    BndHolds L fp (G.sig j).pre ∧ MemPre L fp (G.sig j).mem ∧ SemHolds G L fp (G.sig j).sem

/-- **A function's postcondition** at frame `fp`: its core relation holds of the argument and
return words of the frame, and its bounded frame cells are bounded. -/
def Post (j : ℕ) (fp : K) : Prop :=
  P.Rel L.read (G.sig j).name (frameWords L fp 2 (G.sig j).nargs)
      (frameWords L fp (2 + (G.sig j).nargs) (G.sig j).nret) ∧ BndHolds L fp (G.sig j).post

end Contracts

/-! ## Positions of the walk -/

section Pos

variable {κ : ℕ} (L : MemImage κ) (fp : K) (f : CompiledFn) (X : Fx)

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
    RunK L fp guest f.entry k₀ (st.seg.exit.Reached L fp guest f.entry k₀) st.its k
  exits : ∀ x, x = st.seg.exit ∨ x ∈ branchExits st.its → x ∈ st.seg.exits
  fresh : ∀ t, st.fresh = some t →
    X.idx.get t = some st.seg ∧ st.seg.start = t ∧ st.its = st.seg.items ∧ st.psi = st.seg.env ∧
      Safe guest L k ⟨gpow (f.entry + t), fp⟩

/-- **The run is at the start of the segment at offset `t`**, with `k` steps left; at the
window's end, where no segment of it starts, in its environment `wenv`. -/
def SegRun (K t k : ℕ) : Prop :=
  Safe guest L k ⟨gpow (f.entry + t), fp⟩ ∧
  (∀ s, X.idx.get t = some s → s.start = t → s ∈ X.segs ∧ EnvHolds L fp s.env ∧
    ∃ k₀, k₀ ≤ K ∧ k ≤ k₀ ∧
      RunK L fp guest f.entry k₀ (s.exit.Reached L fp guest f.entry k₀) s.items k) ∧
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

variable {κ : ℕ} {L : MemImage κ} {fp : K} {f : CompiledFn} {X : Fx}

theorem fwdL_ok {test : Book → Bool} {e k₀ : ℕ} {Q : ℕ → Prop} :
    ∀ (its : List Exec.Item) (B : Book) (k : ℕ), BookHolds L fp B →
      RunK L fp guest e k₀ Q its k →
      ∃ k' ≤ k, BookHolds L fp (fwdL test its B).2.1 ∧ RunK L fp guest e k₀ Q (fwdL test its B).1 k' ∧
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
      ∃ k₀ ≤ K, se.seg.exit.Reached L fp guest f.entry k₀ k' := by
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
    ∃ k' < k, ∃ c, L.read (fp * gpow oc) = some c ∧ IsInK c ∧ x ∈ st.seg.exits ∧
      st'.seg = st.seg ∧ st'.psi = st.psi ∧ st'.bnd = st.bnd ∧ BookHolds L fp st'.book ∧
      ((c = 0 ∧ PosOk L fp f X K st' k') ∨
        (c ≠ 0 ∧ ∃ k₀ ≤ K, x.Reached L fp guest f.entry k₀ k')) := by
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

variable {κ : ℕ} {L : MemImage κ} {fp : K} {f : CompiledFn} {X : Fx}

/-- What a walk assumes of its context: the executor's facts hold of the frame, the code is the
program's, the segments are good (an executor's, `exec_good`, `execWin_good`), and the index and
links are theirs. -/
structure WalkHyp (L : MemImage κ) (fp : K) (f : CompiledFn) (X : Fx) : Prop where
  ctx : Exec.Ctx X.F κ fp
  fetch : Fetches guest f.entry f.code
  entry : X.entry = f.entry
  good : ∀ s ∈ X.segs, SegGood L fp guest f.entry s
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
    {K k : ℕ} (hk : k ≤ K) (h : Safe guest L k ⟨gpow (f.entry + t), fp⟩) :
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
    {K k₀ k : ℕ} (hk₀ : k₀ ≤ K) (h : x.Reached L fp guest f.entry k₀ k) :
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
    ∃ se t ft t0 ts a0 as base s0 J sj, endAt st = some se ∧
      se.seg.exit.kind = .jump (.cell t) ft ∧ se.seg.exit.succ = t0 :: ts ∧ arms = a0 :: as ∧
      X.F.self ft = true ∧ ts.length = as.length ∧
      boundOk X.mem se.book se.bnd (cellOf X.loc v) (as.length + 1) = true ∧
      tableBase se.book t (cellOf X.loc v) = some base ∧
      armsOk X.G X.entry base 0 (t0 :: ts) = true ∧ segAt X t0 se.book se.bnd = some s0 ∧
      chkL X a0 s0 [] = .join J ∧ chkArms X J as ts se.book se.bnd = true ∧
      segAt X J se.book se.bnd = some sj ∧ chkL X (.match_ v arms :: ss) st P = chkL X ss sj P := by
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
                    exact ⟨se, t, ft, t0, ts, a0, as, base, s0, J, sj, hse, hk, hs, rfl, hc.1.1,
                      hc.1.2, hc.2, hb, ha, hs0, hJ, harms, hsj, rfl⟩
                  · simp
                · simp
              · simp
            · simp
          · simp
        · simp
      · simp
    · simp
  · simp

theorem chkL_call {f : String} {args rets : List Core.V} {ss : List Core.Stmt} {st : CS}
    {P : List Core.Atom} (h : chkL X (.call f args rets :: ss) st P ≠ .fail) :
    ∃ se e q r j st', endAt st = some se ∧ se.seg.exit.kind = .call (.gp e) q r ∧
      calleeAt X e = some j ∧
      callOk X se.book se.bnd (X.G.sig j) f q (cellsOf X.loc args) rets.length = true ∧
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
      boundOk X.mem se.book se.bnd (cellOf X.loc v) fs.length = true ∧ X.entry ≤ r ∧
      se.seg.exit.succ = [r - X.entry] ∧
      tableCallsOk X base (fun f s ↦ callOk X se.book se.bnd s f q (cellsOf X.loc args) rets.length &&
        s.post.isEmpty) 0 fs = true ∧
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
        callOk X st'.book st'.bnd (X.G.sig j) f q (cellsOf X.loc args) 0 = true ∧
        (X.G.sig j).post = [] ∧ X.entry ≤ r ∧ x.succ = [r - X.entry] ∧
        endOf st' = some (r - X.entry, se) ∧ segAt X (r - X.entry) st'.book st'.bnd = some sr ∧
        chkL X (.callIf c f args :: ss) st P = chkL X ss sr P) ∨
      (∃ e S j, x.kind = .jump (.gp e) (.fpg S) ∧ calleeAt X e = some j ∧ ss = [.ret []] ∧
        tailOk X st' x S (X.G.sig j) f (cellsOf X.loc args) P = true ∧
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
    ∃ J se, endOf st = some (J, se) ∧ pendOk X se P = true ∧ handOk X J se = true ∧
      blockEnd X st P = .join J := by
  revert h
  unfold blockEnd
  split
  · rename_i J se he
    simp only [Bool.cond_eq_ite, Bool.and_eq_true]
    split_ifs with hp
    · exact fun _ ↦ ⟨J, se, he, hp.1, hp.2, rfl⟩
    · simp
  · simp

end Inv

/-! ## Calls and tables -/

section Calls

variable {κ : ℕ} {L : MemImage κ} {fp : K} {B : Book}

theorem storesOk_sound (hB : BookHolds L fp B) {q : ℕ} :
    ∀ {o : ℕ} {cs : List ℕ}, storesOk B q o cs = true → ∀ i (hi : i < cs.length),
      ∃ pv, L.read (fp * gpow q) = some pv ∧ IsInK pv ∧
        ∃ v, L.read (fp * gpow cs[i]) = some v ∧ L.read (pv.limb 0 * gpow (o + i)) = some v
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
    {pv : E} (hq : L.read (fp * gpow q) = some pv) :
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
    (h : ∀ p ∈ env, L.read (fp * gpow p.1) = some (p.2.val fp)) : EnvHolds L fp (envOf env) := by
  unfold envOf
  suffices ∀ (l : List (ℕ × Sym)) (t : Trie Sym), EnvHolds L fp t → (∀ p ∈ l, L.read (fp * gpow p.1) = some (p.2.val fp)) →
      EnvHolds L fp (l.foldl (fun t p ↦ t.set p.2 envDepth p.1) t) from this env .nil EnvHolds.nil h
  intro l
  induction l with
  | nil => exact fun _ ht _ ↦ ht
  | cons p l ih =>
    intro t ht hl
    exact ih _ (ht.set (hl p List.mem_cons_self)) fun p' hp' ↦ hl p' (List.mem_cons_of_mem _ hp')

theorem envStoresOk_sound (hB : BookHolds L fp B) {q : ℕ} {env : List (ℕ × Sym)}
    (h : envStoresOk B q env = true) {pv : E} (hq : L.read (fp * gpow q) = some pv)
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

theorem boundOk_sound {mem : List (ℕ × ℕ × ℕ)} (hm : MemPre L fp mem) (hB : BookHolds L fp B)
    {bnd : List (ℕ × ℕ)} (hb : BndHolds L fp bnd) {c n : ℕ} (h : boundOk mem B bnd c n = true) :
    ∃ e < n, L.read (fp * gpow c) = some (ofK (gpow e)) := by
  simp only [boundOk, Bool.or_eq_true] at h
  rcases h with h | h
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
      simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq, Nat.ble_eq] at hq
      obtain ⟨⟨rfl, hlt⟩, hle⟩ := hq
      obtain ⟨p, v3, h1, -, h3, h2⟩ := hh
      obtain ⟨p', h1', -, e, he, h2'⟩ := hm m hmm o2 hlt
      obtain rfl := Option.some.inj (h1.symm.trans h1')
      have hv := Option.some.inj (h2.symm.trans h2')
      simp only [derefSource] at hv
      exact ⟨e, by omega, by rw [h3, hv]⟩
    · simp at hp
  · obtain ⟨p, hp, hq⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hq
    obtain ⟨e, he, hr⟩ := hb p hp
    exact ⟨e, by omega, hq.1 ▸ hr⟩

/-- Memory bounded through cells of the frame: for each `(c, len, n)`, every word at
`fp[c]·g^i`, `i < len`, is `g^e` with `e < n`. -/
def MemKnown (L : MemImage κ) (fp : K) (known : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ k ∈ known, ∀ c < k.2.1, ∃ e < k.2.2, Core.LoadHolds L.read (wd L fp k.1) c (ofK (gpow e))

theorem memOk_sound (hB : BookHolds L fp B) {known : List (ℕ × ℕ × ℕ)} (hk : MemKnown L fp known)
    {args : List ℕ} {mem : List (ℕ × ℕ × ℕ)} (h : memOk known args mem = true) {q : ℕ}
    (hs : storesOk B q 2 args = true) {pv : E} (hq : L.read (fp * gpow q) = some pv) :
    MemPre L (pv.limb 0) mem := by
  intro m hm c hc
  have := List.all_eq_true.mp h m hm
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at this
  obtain ⟨⟨h2, hlt⟩, hany⟩ := this
  obtain ⟨kk, hkk, hq'⟩ := List.any_eq_true.mp hany
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hq'
  obtain ⟨⟨hc1, hlen⟩, hn⟩ := hq'
  obtain ⟨e, he, hK, hr⟩ := hk kk hkk c (by omega)
  obtain ⟨pv', hq'', -, v, h1, h3⟩ := storesOk_sound hB hs (m.1 - 2) hlt
  obtain rfl := Option.some.inj (hq''.symm.trans hq)
  rw [show 2 + (m.1 - 2) = m.1 by omega] at h3
  rw [hc1, nth_eq hlt, wd_of h1] at hK hr
  exact ⟨v, h3, hK, e, by omega, hr⟩

theorem semOk_sound {G : Glob} {fp' : K} {sems : List (ℕ × ℕ)} (hs : SemHolds G L fp sems)
    {args : List ℕ} {sem : List (ℕ × ℕ)} (h : semOk sems args sem = true)
    (hw : ∀ i (hi : i < args.length), wd L fp' (2 + i) = wd L fp args[i]) : SemHolds G L fp' sem := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at this
  obtain ⟨⟨⟨⟨h1, l1⟩, h2⟩, l2⟩, hany⟩ := this
  obtain ⟨q, hq, hq'⟩ := List.any_eq_true.mp hany
  simp only [Bool.and_eq_true, beq_iff_eq] at hq'
  have e1 := hw _ l1
  have e2 := hw _ l2
  rw [show 2 + (p.1 - 2) = p.1 by omega] at e1
  rw [show 2 + (p.2 - 2) = p.2 by omega] at e2
  rw [e1, e2, ← nth_eq l1, ← nth_eq l2, ← hq'.1, ← hq'.2]
  exact hs q hq

theorem preOk_sound {mem : List (ℕ × ℕ × ℕ)} (hm : MemPre L fp mem) (hB : BookHolds L fp B)
    {bnd : List (ℕ × ℕ)} (hb : BndHolds L fp bnd)
    {args : List ℕ} {pre : List (ℕ × ℕ)} (h : preOk mem B bnd args pre = true) {q : ℕ}
    (hs : storesOk B q 2 args = true) {pv : E} (hq : L.read (fp * gpow q) = some pv) :
    BndHolds L (pv.limb 0) pre := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at this
  obtain ⟨⟨h2, hlt⟩, hbd⟩ := this
  obtain ⟨e, he, hr⟩ := boundOk_sound hm hB hb hbd
  obtain ⟨pv', hq', -, v, h1, h3⟩ := storesOk_sound hB hs (p.1 - 2) hlt
  obtain rfl := Option.some.inj (hq'.symm.trans hq)
  rw [nth_eq hlt, h1] at hr
  obtain rfl := Option.some.inj hr
  refine ⟨e, he, ?_⟩
  rwa [show 2 + (p.1 - 2) = p.1 by omega] at h3

theorem postBnd_sound {ca cr : List ℕ} {post : List (ℕ × ℕ)} {pv : E}
    (hs : ∀ i (hi : i < ca.length), ∃ v, L.read (fp * gpow ca[i]) = some v ∧
      L.read (pv.limb 0 * gpow (2 + i)) = some v)
    (hl : ∀ i (hi : i < cr.length), ∃ v, L.read (fp * gpow cr[i]) = some v ∧
      L.read (pv.limb 0 * gpow (2 + ca.length + i)) = some v)
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
    ∃ pv, L.read (fp * gpow c) = some pv ∧ IsInK pv ∧
      ∃ v, L.read (fp * gpow t) = some v ∧ L.read (pv.limb 0 * gpow base) = some v := by
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

theorem chkArms_get {X : Fx} {J : ℕ} :
    ∀ {as : List (List Core.Stmt)} {ts : List ℕ} {B : Book} {bnd : List (ℕ × ℕ)},
      chkArms X J as ts B bnd = true → ts.length = as.length ∧
        ∀ e (he : e < as.length) (ht : e < ts.length), ∃ st, segAt X ts[e] B bnd = some st ∧
          chkL X as[e] st [] = .join J
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
    {pv : E} (hq : L.read (fp * gpow q) = some pv) :
    ∀ i (hi : i < cs.length), ∃ v, L.read (fp * gpow cs[i]) = some v ∧
      L.read (pv.limb 0 * gpow (o + i)) = some v := by
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
    L.read (fp * gpow (S + o)) = some (ofK (fp * gpow S)) := by
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

variable {κ : ℕ} {L : MemImage κ} {fp : K} {f : CompiledFn} {X : Fx} {Prog : Core.Program}
  {Kb : ℕ}

/-- The words a function returns and what its return does: the frame's return words, back to
the caller with fewer than `Kb` steps left (but `main`), its bounds after. -/
def RetWords (L : MemImage κ) (fp : K) (X : Fx) (Kb : ℕ) (rs : List E) : Prop :=
  rs = frameWords L fp (2 + X.nargs) X.nret ∧
    (X.main = false → ∃ k' < Kb, ∃ r, retRegs L fp = some r ∧ Safe guest L k' r) ∧
    BndHolds L fp X.post

/-- What a walk of runs with at most `K` steps assumes: its context, the jump table, and every
function's contract for runs shorter than `K`. -/
structure WalkEnv (Prog : Core.Program) (L : MemImage κ) (fp : K) (f : CompiledFn) (X : Fx)
    (Kb : ℕ) : Prop where
  hyp : WalkHyp L fp f X
  jt : JTHolds X.G L
  mem : MemPre L fp X.mem
  known : MemKnown L fp X.known
  sems : SemHolds X.G L fp X.sems
  callees : ∀ j, FunSpecLt guest L Kb (X.G.sig j).entry (Pre X.G L j) (Post Prog X.G L j)

/-- **What the walk of a block from a position gives**: the block's core semantics under the
check's valuation, with any continuation the run's arrival at the join gives; the pending atoms;
and that the run arrives at the join. -/
def WalkGood (Prog : Core.Program) (L : MemImage κ) (fp : K) (f : CompiledFn) (X : Fx) (Kb : ℕ)
    (ss : List Core.Stmt) (st : CS) (P : List Core.Atom) : Prop :=
  ∀ k (N : Prop), PosOk L fp f X Kb st k → chkL X ss st P ≠ .fail →
    (∀ J, chkL X ss st P = .join J → ∀ k', k' ≤ k → SegRun L fp f X Kb J k' → N) →
    Core.Stmt.HoldsList (Prog.Rel L.read) L.read (val L fp X.loc) ss N (RetWords L fp X Kb) ∧
      (∀ a ∈ P, a.Holds L.read (val L fp X.loc)) ∧
      (∀ J, chkL X ss st P = .join J → ∃ k' ≤ k, Arrive L fp f X Kb J k')

theorem handOk_sound {st : CS} (hB : BookHolds L fp st.book) (hb : BndHolds L fp st.bnd) {J : ℕ}
    (h : handOk X J st = true) : HandHolds L fp X J := by
  intro J' fs bs hw hJ
  unfold handOk at h
  rw [hw] at h
  simp only [hJ, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    List.all_eq_true, List.contains_iff_mem] at h
  exact ⟨fun p hp ↦ hB p.1 p.2 (by simpa using h.1 p hp), fun b hbb ↦ hb b (by simpa using h.2 b hbb)⟩

theorem pendOk_sound (W : WalkEnv Prog L fp f X Kb) {st : CS} {k : ℕ} (hp : PosOk L fp f X Kb st k)
    {P : List Core.Atom} (h : pendOk X st P = true) : ∀ a ∈ P, a.Holds L.read (val L fp X.loc) :=
  fun a ha ↦ atomOk_sound W.hyp.ctx.pows hp.book hp.psi (List.all_eq_true.mp h a ha)

theorem walk_nil (W : WalkEnv Prog L fp f X Kb) (st : CS) (P : List Core.Atom) :
    WalkGood Prog L fp f X Kb [] st P := by
  intro k N hp hne hj
  rw [chkL_nil] at hne hj ⊢
  obtain ⟨J, se, he, hpd, hhand, hr⟩ := blockEnd_join hne
  obtain ⟨k', hk', hse, hsr⟩ := endOf_ok W.hyp hp he
  refine ⟨hj J hr k' hk' hsr, pendOk_sound W hse hpd, fun J' hJ' ↦ ⟨k', hk', ?_⟩⟩
  rw [hr] at hJ'
  cases hJ'
  exact ⟨hsr, handOk_sound hse.book hse.bnd hhand⟩

theorem walk_atom (W : WalkEnv Prog L fp f X Kb) (a : Core.Atom) (ss : List Core.Stmt) (st : CS)
    (P : List Core.Atom) (ih : ∀ st P, WalkGood Prog L fp f X Kb ss st P) :
    WalkGood Prog L fp f X Kb (.atom a :: ss) st P := by
  intro k N hp hne hj
  rw [chkL_atom] at hne hj ⊢
  obtain ⟨k', hk', hp', htest, -, hpsi, -⟩ :=
    fwd_ok (test := fun B ↦ atomOk X.F B st.psi X.loc a) hp
  revert hne hj htest hp'
  rcases hf : fwd (fun B ↦ atomOk X.F B st.psi X.loc a) st with ⟨st', b⟩
  intro hne hj hp' htest
  simp only at hp' htest hne hj ⊢
  cases b with
  | false =>
    obtain ⟨hl, hP, hr⟩ := ih st' (a :: P) k' N hp' hne
      (fun J hJ k'' hk'' h ↦ hj J hJ k'' (le_trans hk'' hk') h)
    refine ⟨⟨hP a List.mem_cons_self, hl⟩, fun b hb ↦ hP b (List.mem_cons_of_mem _ hb),
      fun J hJ ↦ ?_⟩
    obtain ⟨k'', hk'', h⟩ := hr J hJ
    exact ⟨k'', le_trans hk'' hk', h⟩
  | true =>
    obtain ⟨hl, hP, hr⟩ := ih st' P k' N hp' hne
      (fun J hJ k'' hk'' h ↦ hj J hJ k'' (le_trans hk'' hk') h)
    have ha := atomOk_sound W.hyp.ctx.pows hp'.book hp.psi (htest rfl)
    refine ⟨⟨ha, hl⟩, hP, fun J hJ ↦ ?_⟩
    obtain ⟨k'', hk'', h⟩ := hr J hJ
    exact ⟨k'', le_trans hk'' hk', h⟩

theorem walk_ite (W : WalkEnv Prog L fp f X Kb) (c : Core.V) (z n ss : List Core.Stmt) (st : CS)
    (P : List Core.Atom) (ihz : ∀ st P, WalkGood Prog L fp f X Kb z st P)
    (ihn : ∀ st P, WalkGood Prog L fp f X Kb n st P)
    (ih : ∀ st P, WalkGood Prog L fp f X Kb ss st P) :
    WalkGood Prog L fp f X Kb (.ite c z n :: ss) st P := by
  intro k N hp hne hj
  obtain ⟨st', x, t, sn, J, sj, hb, hk, hsucc, hsn, hz, hn, hsj, heq⟩ := chkL_ite hne
  rw [heq] at hne hj ⊢
  obtain ⟨k1, hk1, cv, hc, hcK, hx, hseg, -, hbnd, hB', hcase⟩ := branchAt_ok hp hb
  have rest : ∀ k2, k2 ≤ k → SegRun L fp f X Kb J k2 →
      Core.Stmt.HoldsList (Prog.Rel L.read) L.read (val L fp X.loc) ss N (RetWords L fp X Kb) ∧
        (∀ a ∈ P, a.Holds L.read (val L fp X.loc)) ∧
        (∀ J', chkL X ss sj P = .join J' → ∃ k' ≤ k, Arrive L fp f X Kb J' k') := by
    intro k2 hk2 hr
    obtain ⟨h1, h2, h3⟩ := ih sj P k2 N (segAt_ok W.hyp hsj hr hB' (hbnd ▸ hp.bnd)) hne
      (fun J' hJ' k3 hk3 hr3 ↦ hj J' hJ' k3 (by omega) hr3)
    exact ⟨h1, h2, fun J' hJ' ↦ (h3 J' hJ').imp fun k' h ↦ ⟨by omega, h.2⟩⟩
  have hσ : val L fp X.loc c = cv := wd_of hc
  have hblk : ∀ (b : List Core.Stmt) (sb : CS), (∀ st P, WalkGood Prog L fp f X Kb b st P) →
      PosOk L fp f X Kb sb k1 → chkL X b sb [] = .join J →
      Core.Stmt.HoldsList (Prog.Rel L.read) L.read (val L fp X.loc) b
          (Core.Stmt.HoldsList (Prog.Rel L.read) L.read (val L fp X.loc) ss N
            (RetWords L fp X Kb)) (RetWords L fp X Kb) ∧
        (∀ a ∈ P, a.Holds L.read (val L fp X.loc)) ∧
        (∀ J', chkL X ss sj P = .join J' → ∃ k' ≤ k, Arrive L fp f X Kb J' k') := by
    intro b sb ihb hpb hjb
    obtain ⟨hl, -, hr⟩ := ihb sb [] k1 _ hpb (by rw [hjb]; simp)
      (fun J' hJ' k2 hk2 hr2 ↦ by
        rw [hjb] at hJ'
        cases hJ'
        exact (rest k2 (by omega) hr2).1)
    obtain ⟨k2, hk2, hr2⟩ := hr J hjb
    obtain ⟨-, hP, hreach⟩ := rest k2 (by omega) hr2.1
    exact ⟨hl, hP, hreach⟩
  rcases hcase with ⟨rfl, hp'⟩ | ⟨hc0, k₀, hk₀, hr⟩
  · obtain ⟨hl, hP, hreach⟩ := hblk z st' ihz hp' hz
    exact ⟨⟨hσ ▸ hcK, fun _ ↦ hl, fun h0 ↦ absurd hσ h0⟩, hP, hreach⟩
  · have hrt := segRun_of_next W.hyp hp.seg (hseg ▸ hx) hk hsucc hk₀ hr
    obtain ⟨hl, hP, hreach⟩ := hblk n sn ihn (segAt_ok W.hyp hsn hrt hB' (hbnd ▸ hp.bnd)) hn
    exact ⟨⟨hσ ▸ hcK, fun h0 ↦ absurd (hσ.symm.trans h0) hc0, fun _ ↦ hl⟩, hP, hreach⟩

/-- A block walked from `sb` to the join `J`, the rest walked from the join's segment `sj`. -/
theorem walk_block (W : WalkEnv Prog L fp f X Kb) {b ss : List Core.Stmt} {sb sj : CS}
    {P : List Core.Atom} {J k k1 : ℕ} {N : Prop} {B : Book} {bnd : List (ℕ × ℕ)}
    (hk1 : k1 ≤ k) (ihb : ∀ st P, WalkGood Prog L fp f X Kb b st P)
    (ih : ∀ st P, WalkGood Prog L fp f X Kb ss st P) (hpb : PosOk L fp f X Kb sb k1)
    (hjb : chkL X b sb [] = .join J) (hsj : segAt X J B bnd = some sj)
    (hB : BookHolds L fp B) (hbnd : BndHolds L fp bnd) (hne : chkL X ss sj P ≠ .fail)
    (hj : ∀ J', chkL X ss sj P = .join J' → ∀ k', k' ≤ k → SegRun L fp f X Kb J' k' → N) :
    Core.Stmt.HoldsList (Prog.Rel L.read) L.read (val L fp X.loc) b
        (Core.Stmt.HoldsList (Prog.Rel L.read) L.read (val L fp X.loc) ss N
          (RetWords L fp X Kb)) (RetWords L fp X Kb) ∧
      (∀ a ∈ P, a.Holds L.read (val L fp X.loc)) ∧
      (∀ J', chkL X ss sj P = .join J' → ∃ k' ≤ k, Arrive L fp f X Kb J' k') := by
  have rest : ∀ k2, k2 ≤ k1 → SegRun L fp f X Kb J k2 →
      Core.Stmt.HoldsList (Prog.Rel L.read) L.read (val L fp X.loc) ss N (RetWords L fp X Kb) ∧
        (∀ a ∈ P, a.Holds L.read (val L fp X.loc)) ∧
        (∀ J', chkL X ss sj P = .join J' → ∃ k' ≤ k, Arrive L fp f X Kb J' k') := by
    intro k2 hk2 hr
    obtain ⟨h1, h2, h3⟩ := ih sj P k2 N (segAt_ok W.hyp hsj hr hB hbnd) hne
      (fun J' hJ' k3 hk3 hr3 ↦ hj J' hJ' k3 (by omega) hr3)
    exact ⟨h1, h2, fun J' hJ' ↦ (h3 J' hJ').imp fun k' h ↦ ⟨by omega, h.2⟩⟩
  obtain ⟨hl, -, hr⟩ := ihb sb [] k1 _ hpb (by rw [hjb]; simp)
    (fun J' hJ' k2 hk2 hr2 ↦ by
      rw [hjb] at hJ'
      cases hJ'
      exact (rest k2 hk2 hr2).1)
  obtain ⟨k2, hk2, hr2⟩ := hr J hjb
  obtain ⟨-, hP, hreach⟩ := rest k2 hk2 hr2.1
  exact ⟨hl, hP, hreach⟩

theorem walk_match (W : WalkEnv Prog L fp f X Kb) (v : Core.V) (arms : List (List Core.Stmt))
    (ss : List Core.Stmt) (st : CS) (P : List Core.Atom)
    (iha : ∀ e (he : e < arms.length) st P, WalkGood Prog L fp f X Kb arms[e] st P)
    (ih : ∀ st P, WalkGood Prog L fp f X Kb ss st P) :
    WalkGood Prog L fp f X Kb (.match_ v arms :: ss) st P := by
  intro k N hp hne hj
  obtain ⟨se, t, ft, t0, ts, a0, as, base, s0, J, sj, hse, hk, hs, harms0, hself, hlen, hbd, htb,
    harms, hs0, hJ, hchk, hsj, heq⟩ := chkL_match hne
  subst harms0
  rw [heq] at hne hj ⊢
  obtain ⟨k1, hk1, hpse, -, -, -, k₀, hk₀, hr⟩ := endAt_ok hp hse
  obtain ⟨hlt, henv, -, r, hreg, hsafe⟩ := hr
  rw [hk] at hreg
  obtain ⟨a, b, ⟨w, hw, -, rfl⟩, hb, rfl⟩ := hreg
  obtain rfl := self_is W.hyp.ctx.fpOne hself hb
  obtain ⟨e, he, hce⟩ := boundOk_sound W.mem hpse.book hpse.bnd hbd
  obtain ⟨pv, hpv, -, w', hw', hload⟩ := tableBase_sound hpse.book htb
  obtain rfl := Option.some.inj (hpv.symm.trans hce)
  obtain rfl := Option.some.inj (hw.symm.trans hw')
  have heA : e < (t0 :: ts).length := by simp; omega
  have hslot := W.jt _ _ (armsOk_get harms e heA)
  have hadd : gpow e * gpow base = gpow (base + (0 + e)) := by
    rw [Nat.zero_add, gpow, gpow, gpow, ← pow_add, Nat.add_comm]
  rw [limb_ofK0, hadd, hslot] at hload
  obtain rfl := Option.some.inj hload
  rw [limb_ofK0, W.hyp.entry] at hsafe
  have hrun := segRun_of_safe W.hyp hpse.seg (hpse.exits _ (Or.inl rfl))
    (by rw [hs]; exact List.getElem_mem heA) henv (K := Kb) (by omega) hsafe
  have harm : ∃ sb, segAt X (t0 :: ts)[e] se.book se.bnd = some sb ∧
      chkL X (a0 :: as)[e] sb [] = .join J := by
    cases e with
    | zero => exact ⟨s0, hs0, hJ⟩
    | succ e =>
      obtain ⟨-, hg⟩ := chkArms_get hchk
      exact hg e (by simp at he; omega) (by simp at heA; omega)
  obtain ⟨sb, hsb, hjb⟩ := harm
  have heL : e < (a0 :: as).length := by simp; omega
  obtain ⟨hl, hP, hreach⟩ := walk_block W hk1 (iha e heL) ih
    (segAt_ok W.hyp hsb hrun hpse.book hpse.bnd) hjb hsj hpse.book hpse.bnd hne hj
  refine ⟨(Core.holds_match_iff _ _ _ _).mpr ⟨e, heL, wd_of hce, hl⟩, hP, hreach⟩

/-- What a call into frame `fp[q] = pv` gives the caller: the callee ran from its entry and came
back to the return point, its contract holding of its frame. -/
theorem call_ok (W : WalkEnv Prog L fp f X Kb) {B : Book} {bnd : List (ℕ × ℕ)}
    (hB : BookHolds L fp B) (hbnd : BndHolds L fp bnd) {j q r k1 : ℕ} {f' : String}
    {ca : List ℕ} {nr : ℕ} (hj : calleeAt X (X.G.sig j).entry = some j)
    (hco : callOk X B bnd (X.G.sig j) f' q ca nr = true) {pv : E}
    (hq : L.read (fp * gpow q) = some pv) (hpK : IsInK pv)
    (hret : retRegs L (pv.limb 0) = some ⟨gpow r, fp⟩) (hk1 : k1 < Kb)
    (hsafe : Safe guest L k1 ⟨gpow (X.G.sig j).entry, pv.limb 0⟩) :
    ∃ k2 < k1, Post Prog X.G L j (pv.limb 0) ∧ Safe guest L k2 ⟨gpow r, fp⟩ ∧
      f' = (X.G.sig j).name ∧ ca.length = (X.G.sig j).nargs ∧ nr = (X.G.sig j).nret ∧
      ca.map (wd L fp) = frameWords L (pv.limb 0) 2 (X.G.sig j).nargs ∧
      (∀ p ∈ (X.G.sig j).post, 2 ≤ p.1 ∧ p.1 < 2 + (X.G.sig j).nargs + (X.G.sig j).nret) ∧
      storesOk B q 2 ca = true := by
  simp only [callOk, Bool.and_eq_true, beq_iff_eq] at hco
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hname, hna⟩, hnr⟩, hst⟩, henvst⟩, hpre⟩, hmem⟩, hsem⟩, hpost⟩ := hco
  obtain ⟨hgood, -⟩ := calleeAt_some hj
  have hPre : Pre X.G L j (pv.limb 0) :=
    ⟨hgood, W.jt, envStoresOk_sound hB henvst hq hpK, preOk_sound W.mem hB hbnd hpre hst hq,
      memOk_sound hB W.known hmem hst hq, semOk_sound W.sems hsem fun i hi ↦ by
        obtain ⟨pv', hq', -, v, h1, h2⟩ := storesOk_sound hB hst i hi
        obtain rfl := Option.some.inj (hq'.symm.trans hq)
        rw [wd_of h1, wd_of h2]⟩
  obtain ⟨k2, hk2, hPost, hsafe2⟩ := (W.callees j).call hk1 hPre hret hsafe
  refine ⟨k2, hk2, hPost, hsafe2, hname, hna, hnr, ?_, fun p hp ↦ ?_, hst⟩
  · rw [storesOk_words hB hst hq, hna]
  · have := List.all_eq_true.mp hpost p hp
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at this
    exact this

theorem walk_call (W : WalkEnv Prog L fp f X Kb) (f' : String) (args rets : List Core.V)
    (ss : List Core.Stmt) (st : CS) (P : List Core.Atom)
    (ih : ∀ st P, WalkGood Prog L fp f X Kb ss st P) :
    WalkGood Prog L fp f X Kb (.call f' args rets :: ss) st P := by
  intro k N hp hne hjn
  obtain ⟨se, e, q, r, j, st', hse, hk, hj, hco, hle, hsucc, hac, heq⟩ := chkL_call hne
  rw [heq] at hne hjn ⊢
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
    call_ok W hpse.book hpse.bnd hj hco hq hpK hret (by omega) hsafe
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
  have hcall : Prog.Rel L.read f' (args.map (val L fp X.loc)) (rets.map (val L fp X.loc)) := by
    rw [hname, map_val, map_val, hargs, storesOk_words hp3.book hloads hq, hcr, hnr, hna']
    exact hPost.1
  have hb4 : BndHolds L fp
      (postBnd (cellsOf X.loc args ++ cellsOf X.loc rets) (X.G.sig j).post ++ st'.bnd) := by
    refine BndHolds.append (postBnd_sound (pv := pv) (storesOk_at hpse.book hst hq)
      (fun i hi ↦ ?_) (fun p hp ↦ ?_) hPost.2) hp3.bnd
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
  obtain ⟨hl, hP, hreach⟩ := ih _ P k3 N hp4 hne
    (fun J hJ k4 hk4 h ↦ hjn J hJ k4 (by omega) h)
  exact ⟨⟨hcall, hl⟩, hP, fun J hJ ↦ (hreach J hJ).imp fun k' h ↦ ⟨by omega, h.2⟩⟩

theorem walk_dispatch (W : WalkEnv Prog L fp f X Kb) (v : Core.V) (fs : List String)
    (args rets : List Core.V) (ss : List Core.Stmt) (st : CS) (P : List Core.Atom)
    (ih : ∀ st P, WalkGood Prog L fp f X Kb ss st P) :
    WalkGood Prog L fp f X Kb (.dispatch v fs args rets :: ss) st P := by
  intro k N hp hne hjn
  obtain ⟨se, t, q, r, base, st', hse, hk, htb, hbd, hle, hsucc, htc, hac, heq⟩ :=
    chkL_dispatch hne
  rw [heq] at hne hjn ⊢
  obtain ⟨k1, hk1, hpse, -, -, -, k₀, hk₀, hr⟩ := endAt_ok hp hse
  obtain ⟨hlt, henv, hextra, rr, hreg, hsafe⟩ := hr
  rw [hk] at hextra hreg
  obtain ⟨pv, hq, hret⟩ := hextra
  obtain ⟨pv', a, hq', hpK, ⟨w, hw, -, rfl⟩, rfl⟩ := hreg
  obtain rfl := Option.some.inj (hq.symm.trans hq')
  obtain ⟨e, he, hce⟩ := boundOk_sound W.mem hpse.book hpse.bnd hbd
  obtain ⟨cv, hcv, -, w', hw', hload⟩ := tableBase_sound hpse.book htb
  obtain rfl := Option.some.inj (hcv.symm.trans hce)
  obtain rfl := Option.some.inj (hw.symm.trans hw')
  obtain ⟨pc, j, hslot, hj, hok⟩ := tableCallsOk_get htc e he
  have hadd : gpow e * gpow base = gpow (base + (0 + e)) := by
    rw [Nat.zero_add, gpow, gpow, gpow, ← pow_add, Nat.add_comm]
  rw [limb_ofK0, hadd, W.jt _ _ hslot] at hload
  obtain rfl := Option.some.inj hload
  rw [limb_ofK0] at hsafe
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hok
  obtain ⟨hco, hpost0⟩ := hok
  obtain ⟨-, hentry⟩ := calleeAt_some hj
  rw [← hentry] at hj hsafe
  obtain ⟨k2, hk2, hPost, hsafe2, hname, hna, hnr, hargs, -, -⟩ :=
    call_ok W hpse.book hpse.bnd hj hco hq hpK hret (by omega) hsafe
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
  have hcall : Prog.Rel L.read fs[e] (args.map (val L fp X.loc)) (rets.map (val L fp X.loc)) := by
    rw [hname, map_val, map_val, hargs, storesOk_words hp3.book hloads hq, hcr, hnr, hna']
    exact hPost.1
  obtain ⟨hl, hP, hreach⟩ := ih st' P k3 N hp3 hne
    (fun J hJ k4 hk4 h ↦ hjn J hJ k4 (by omega) h)
  exact ⟨⟨⟨e, he, wd_of hce, hcall⟩, hl⟩, hP,
    fun J hJ ↦ (hreach J hJ).imp fun k' h ↦ ⟨by omega, h.2⟩⟩

theorem frameWords_zero (L : MemImage κ) (fp : K) (o : ℕ) : frameWords L fp o 0 = [] := rfl

theorem walk_callIf (W : WalkEnv Prog L fp f X Kb) (c : Core.V) (f' : String) (args : List Core.V)
    (ss : List Core.Stmt) (st : CS) (P : List Core.Atom)
    (ih : ∀ st P, WalkGood Prog L fp f X Kb ss st P) :
    WalkGood Prog L fp f X Kb (.callIf c f' args :: ss) st P := by
  intro k N hp hne hjn
  obtain ⟨st', x, hb, hform⟩ := chkL_callIf hne
  obtain ⟨k1, hk1, cv, hc, hcK, hx, hseg, hpsi, hbnd, hB', hcase⟩ := branchAt_ok hp hb
  have hσ : val L fp X.loc c = cv := wd_of hc
  obtain ⟨k₀', hk₀', hkk₀, -⟩ := hp.run
  rcases hform with ⟨e, q, r, j, se, sr, hk, hj, hco, hpost0, hle, hsucc, hend, hsr, heq⟩ |
    ⟨e, S, j, hk, hj, rfl, htail, heq⟩
  · rw [heq] at hne hjn ⊢
    have cont : ∀ k2, k2 < k → SegRun L fp f X Kb (r - X.entry) k2 →
        Core.Stmt.HoldsList (Prog.Rel L.read) L.read (val L fp X.loc) ss N (RetWords L fp X Kb) ∧
          (∀ a ∈ P, a.Holds L.read (val L fp X.loc)) ∧
          (∀ J, chkL X ss sr P = .join J → ∃ k' ≤ k, Arrive L fp f X Kb J k') := by
      intro k2 hk2 hr2
      obtain ⟨hl, hP, hreach⟩ := ih sr P k2 N (segAt_ok W.hyp hsr hr2 hB' (hbnd ▸ hp.bnd)) hne
        (fun J hJ k4 hk4 h ↦ hjn J hJ k4 (by omega) h)
      exact ⟨hl, hP, fun J hJ ↦ (hreach J hJ).imp fun k' h ↦ ⟨by omega, h.2⟩⟩
    rcases hcase with ⟨rfl, hp'⟩ | ⟨hc0, k₀, hk₀, hr⟩
    · obtain ⟨k2, hk2, -, hr2⟩ := endOf_ok W.hyp hp' hend
      obtain ⟨hl, hP, hreach⟩ := cont k2 (by omega) hr2
      exact ⟨⟨hσ ▸ hcK, fun h0 ↦ absurd hσ h0, hl⟩, hP, hreach⟩
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
        call_ok W hB' (hbnd ▸ hp.bnd) hj hco hq hpK hret (by omega) hsafe
      have hr2 : SegRun L fp f X Kb (r - X.entry) k2 := by
        refine segRun_of_safe W.hyp hp.seg hx (by rw [hsucc]; simp) henv (by omega) ?_
        rw [← W.hyp.entry, Nat.add_sub_cancel' hle]
        exact hsafe2
      obtain ⟨hl, hP, hreach⟩ := cont k2 (by omega) hr2
      have hcall : Prog.Rel L.read f' (args.map (val L fp X.loc)) [] := by
        have h1 := hPost.1
        rw [← hnr, frameWords_zero, ← hargs, ← map_val, ← hname] at h1
        exact h1
      exact ⟨⟨hσ ▸ hcK, fun _ ↦ hcall, hl⟩, hP, hreach⟩
  · rw [heq]
    simp only [tailOk, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, Bool.not_eq_true',
      List.all_eq_true] at htail
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hname, hna⟩, hnr⟩, hxnr⟩, hpre⟩, hmem0⟩, hxpost⟩, hsem⟩, hargs⟩, henv⟩,
      hr0⟩, hr1⟩, hpend⟩, hmain⟩, hend⟩ := htail
    have hP : ∀ a ∈ P, a.Holds L.read (val L fp X.loc) := fun a ha ↦
      atomOk_sound W.hyp.ctx.pows hB' (hpsi ▸ hp.psi) (List.all_eq_true.mp hpend a ha)
    have hrw : RetWords L fp X Kb [] → Core.Stmt.HoldsList (Prog.Rel L.read) L.read
        (val L fp X.loc) [.ret []] N (RetWords L fp X Kb) := id
    have hwords : ∀ (h : ∃ k' < Kb, ∃ r, retRegs L fp = some r ∧ Safe guest L k' r),
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
          fun J hJ ↦ by simp at hJ⟩
      · simp at hend
    · obtain ⟨hlt, hxenv, -, rr, hreg, hsafe⟩ := hr
      rw [hk] at hreg
      obtain ⟨a, b, ha, hb', rfl⟩ := hreg
      simp only [Tgt.Is] at ha hb'
      subst ha hb'
      obtain ⟨hgood, hentry⟩ := calleeAt_some hj
      have hPre : Pre X.G L j (fp * gpow S) := by
        refine ⟨hgood, W.jt, envOf_holds fun p hp ↦ ?_, fun p hq0 ↦ ?_,
          by rw [hmem0]; intro p hp; simp at hp, semOk_sound W.sems hsem fun i hi ↦ ?_⟩
        rotate_left
        · have := List.all_eq_true.mp hpre p hq0
          simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at this
          obtain ⟨⟨h2, hlt⟩, hbd⟩ := this
          obtain ⟨e, he, hr⟩ := boundOk_sound W.mem hB' (hbnd ▸ hp.bnd) hbd
          refine ⟨e, he, ?_⟩
          have hs := sameOk_read hB' (tailArgsOk_sound hargs (p.1 - 2) hlt)
          rw [nth_eq hlt] at hr
          rw [show 2 + (p.1 - 2) = p.1 by omega, hr] at hs
          rw [mul_assoc, gpow, gpow, ← pow_add, ← gpow]
          exact hs
        · have := sameOk_sound hB' (tailArgsOk_sound hargs i hi)
          rw [← this]
          unfold wd
          rw [mul_assoc, gpow, gpow, ← pow_add]
        have := henv p hp
        rw [Sym.beq_eq this.1]
        have h2 := tailEnvOk_sound hB' hxenv this.2
        rw [mul_assoc, gpow, gpow, ← pow_add, ← gpow]
        simpa [Sym.val, gpow_zero'] using h2
      have hret : retRegs L (fp * gpow S) = retRegs L fp := by
        have e0 := sameOk_read hB' hr0
        have e1 := sameOk_read hB' hr1
        unfold retRegs
        rw [mul_assoc, mul_assoc, gpow, gpow, ← pow_add, ← pow_add, ← gpow, ← gpow, e0, e1]
      rw [← hentry] at hsafe
      obtain ⟨k2, hk2, rr, hrr, hPost, hsafe2⟩ :=
        (W.callees j).tail (by omega) hPre hret hsafe
      have hcall : Prog.Rel L.read f' (args.map (val L fp X.loc)) [] := by
        have h1 := hPost.1
        rw [hnr, frameWords_zero, ← hname] at h1
        convert h1 using 1
        rw [map_val]
        apply List.ext_getElem (by simp [frameWords, cellsOf_length] at hna ⊢; omega)
        intro i h1' h2'
        simp only [List.getElem_map, frameWords, List.getElem_range]
        have := sameOk_sound hB' (tailArgsOk_sound hargs i (by simpa using h1'))
        rw [← this]
        unfold wd
        rw [mul_assoc, gpow, gpow, ← pow_add]
      exact ⟨⟨hσ ▸ hcK, fun _ ↦ hcall, hwords ⟨k2, by omega, rr, hrr, hsafe2⟩⟩, hP,
        fun J hJ ↦ by simp at hJ⟩

theorem runAt_words {loc : Trie ℕ} {base : ℕ} {vs : List Core.V} (h : runAt loc base vs = true) :
    vs.map (val L fp loc) = frameWords L fp base vs.length := by
  apply List.ext_getElem (by simp [frameWords])
  intro i h1 h2
  simp only [List.getElem_map, frameWords, List.getElem_range, val]
  rw [runAt_sound h i (by simpa using h1)]

theorem walk_ret (W : WalkEnv Prog L fp f X Kb) (vs : List Core.V) (ss : List Core.Stmt) (st : CS)
    (P : List Core.Atom) : WalkGood Prog L fp f X Kb (.ret vs :: ss) st P := by
  intro k N hp hne hjn
  obtain ⟨hr, heq⟩ := chkL_ret hne
  rw [heq]
  unfold retOk at hr
  split at hr
  · rename_i se hse
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hr
    obtain ⟨⟨⟨⟨hkind, hlen⟩, hrun⟩, hpend⟩, hpost⟩ := hr
    obtain ⟨k2, hk2, hpse, -, -, -, k₀, hk₀, hreach⟩ := endAt_ok hp hse
    refine ⟨⟨by rw [runAt_words hrun, hlen], fun hm ↦ ?_, fun p hp' ↦
      boundOk_sound W.mem hpse.book hpse.bnd (hpost p hp')⟩, pendOk_sound W hpse hpend,
      fun J hJ ↦ by simp at hJ⟩
    rw [hm] at hkind
    simp only [Bool.cond_false, decide_eq_true_eq] at hkind
    obtain ⟨hlt, -, -, rr, hreg, hsafe⟩ := hreach
    rw [hkind] at hreg
    exact ⟨k2, by omega, rr, hreg, hsafe⟩
  · simp at hr

mutual
/-- **The walk is sound.** -/
theorem walk_sound (W : WalkEnv Prog L fp f X Kb) :
    ∀ (ss : List Core.Stmt) (st : CS) (P : List Core.Atom), WalkGood Prog L fp f X Kb ss st P
  | [], st, P => walk_nil W st P
  | .atom a :: ss, st, P => walk_atom W a ss st P (walk_sound W ss)
  | .ite c z n :: ss, st, P =>
    walk_ite W c z n ss st P (walk_sound W z) (walk_sound W n) (walk_sound W ss)
  | .match_ v arms :: ss, st, P => walk_match W v arms ss st P (arms_sound W arms) (walk_sound W ss)
  | .call f' args rets :: ss, st, P => walk_call W f' args rets ss st P (walk_sound W ss)
  | .callIf c f' args :: ss, st, P => walk_callIf W c f' args ss st P (walk_sound W ss)
  | .dispatch v fs args rets :: ss, st, P => walk_dispatch W v fs args rets ss st P (walk_sound W ss)
  | .ret vs :: ss, st, P => walk_ret W vs ss st P

theorem arms_sound (W : WalkEnv Prog L fp f X Kb) :
    ∀ (arms : List (List Core.Stmt)) (e : ℕ) (he : e < arms.length) (st : CS)
      (P : List Core.Atom), WalkGood Prog L fp f X Kb arms[e] st P
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

variable {κ : ℕ} {L : MemImage κ} {G : Glob} {f : CompiledFn} {cf : Core.Fn} {C : Cert}
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
    (∃ m, ∃ hm : m < (nth C.cells i []).length, v = nth C.los i 0 + m ∧ (nth C.cells i [])[m] = c) ∨
      ∃ j, (v, c, j) ∈ nth C.ins i [] := by
  unfold Cert.locAt at h
  rw [Trie.seq_eq] at h
  rcases insTrie_get _ _ h with hj | h'
  · exact Or.inr hj
  · rcases locTrieFrom_get _ _ _ h' with hm | h''
    · exact Or.inl hm
    · simp [getF_eq] at h''

/-- The windows' cells are consecutive, up to window `n`. -/
def Cont (C : Cert) (n : ℕ) : Prop :=
  nth C.los 0 0 = 0 ∧ ∀ i < n, nth C.los (i + 1) 0 = nth C.los i 0 + (nth C.cells i []).length

theorem nth_of_le {α : Type} : ∀ {l : List α} {n : ℕ} {d : α}, l.length ≤ n → nth l n d = d
  | [], _, _, _ => rfl
  | _ :: _, 0, _, h => absurd h (by simp)
  | _ :: as, n + 1, _, h => nth_of_le (l := as) (by simpa using h)

theorem cont_lo {n : ℕ} (h : Cont C n) : ∀ j ≤ n,
    nth C.los j 0 = ((C.cells.take j).map List.length).sum := by
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
    (hm : m < (nth C.cells j []).length) :
    C.locs.getD (nth C.los j 0 + m) 0 = (nth C.cells j [])[m] := by
  have hl : j < C.cells.length := by
    by_contra hc
    rw [nth_of_le (by omega)] at hm
    exact absurd hm (Nat.not_lt_zero _)
  have hc : nth C.cells j [] = C.cells[j] := nth_eq hl
  rw [cont_lo h j hj]
  simp only [hc] at hm ⊢
  exact flatten_getD C.cells j hl m hm

/-- The valuation of a function's check: every value is the word in its cell. -/
noncomputable def valG (L : MemImage κ) (fp : K) (C : Cert) : Core.Val :=
  fun v ↦ wd L fp (C.locs.getD v.idx 0)

theorem locAt_val {n : ℕ} (hcont : Cont C n) {i : ℕ} (hi : i ≤ n)
    (hins : C.insOk (nth C.ins i []) = true) (hn : C.cuts.length = n) {v : Core.V} {c : ℕ}
    (h : getF (C.locAt i) v.idx = some c) : C.locs.getD v.idx 0 = c := by
  rcases locAt_get h with ⟨m, hm, hv, hc⟩ | ⟨j, hj⟩
  · rw [hv, cont_locs hcont hi hm, hc]
  · have := List.all_eq_true.mp hins _ hj
    simp only [Bool.and_eq_true, Nat.ble_eq, beq_iff_eq] at this
    obtain ⟨⟨hjn, hlo⟩, hget⟩ := this
    obtain ⟨hm, hget⟩ := List.getElem?_eq_some_iff.mp hget
    rw [show v.idx = nth C.los j 0 + (v.idx - nth C.los j 0) by omega,
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
def WinStart (L : MemImage κ) (fp : K) (f : CompiledFn) (C : Cert) (i k : ℕ) : Prop :=
  Safe guest L k ⟨gpow (f.entry + (C.cutAt i).J), fp⟩ ∧ EnvHolds L fp (envOf (C.cutAt i).env) ∧
    (∀ p ∈ (C.cutAt i).facts, p.2.Holds L fp) ∧ BndHolds L fp (C.cutAt i).bnd

/-- What a function's return does, in every window's context. -/
abbrev RetOf (L : MemImage κ) (fp : K) (G : Glob) (f : CompiledFn) (cf : Core.Fn) (C : Cert)
    (main : Bool) (Kb : ℕ) : List E → Prop :=
  RetWords L fp (C.fxAt G f cf main 0 [] .nil .nil) Kb

theorem checkWin_parts {main : Bool} {i : ℕ} (hc : checkWin G f cf C main i = true) :
    C.contOk i = true ∧ C.insOk (nth C.ins i []) = true := by
  unfold checkWin at hc
  rcases hR : execWin C.facts f (C.cutAt i).J (C.cutAt i).env (C.endAt f i) with ⟨segs, dead⟩
  rw [hR] at hc
  simp only [listSeq_eq, Trie.seq_eq, Bool.and_eq_true] at hc
  exact ⟨hc.1.1.1.1.1, hc.1.1.1.1.2⟩

/-- The first window's check fixes whether the frame is `main`'s. -/
theorem checkWin_fpOne {main : Bool} (hc : checkWin G f cf C main 0 = true) : main = C.facts.fpOne := by
  unfold checkWin at hc
  rcases hR : execWin C.facts f (C.cutAt 0).J (C.cutAt 0).env (C.endAt f 0) with ⟨segs, dead⟩
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
    (hC : ∀ j, FunSpecLt guest L Kb (G.sig j).entry (Pre G L j) (Post Prog G L j))
    (hjt : JTHolds G L) (hmem : MemPre L fp C.mem) (hknown : MemKnown L fp (C.cutAt i).known)
    (hsems : SemHolds G L fp (C.cutAt i).sems) {k : ℕ} (hk : k ≤ Kb) (hs : WinStart L fp f C i k) :
    (i = 0 → ∀ m (hm : m < cf.params.length), C.locs.getD cf.params[m].idx 0 = 2 + m) ∧
    (i < C.cuts.length → Core.Stmt.HoldsList (Prog.Rel L.read) L.read (valG L fp C)
        (C.stmtsAt cf i) True (RetOf L fp G f cf C main Kb) ∧
        (C.cutAt i).start ≤ (C.cutAt (i + 1)).start ∧ ∃ k' ≤ k, WinStart L fp f C (i + 1) k') ∧
    (C.cuts.length ≤ i → Core.Stmt.HoldsList (Prog.Rel L.read) L.read (valG L fp C)
        (C.stmtsAt cf i) False (RetOf L fp G f cf C main Kb)) := by
  have hins := (checkWin_parts hc).2
  unfold checkWin at hc
  rcases hR : execWin C.facts f (C.cutAt i).J (C.cutAt i).env (C.endAt f i) with ⟨segs, dead⟩
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
    execWin_good hctx (guest_fetches hf) _ _ _ s (by rw [hR]; exact hs), rfl, hlink⟩
  have W : WalkEnv Prog L fp f X Kb := ⟨H, hjt, hmem, hknown, hsems, hC⟩
  have hret : RetWords L fp X Kb = RetOf L fp G f cf C main Kb := rfl
  have hconv : ∀ {N : Prop}, Core.Stmt.HoldsList (Prog.Rel L.read) L.read (val L fp X.loc)
      (C.stmtsAt cf i) N (RetWords L fp X Kb) →
      Core.Stmt.HoldsList (Prog.Rel L.read) L.read (valG L fp C) (C.stmtsAt cf i) N
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
    have hrun : SegRun L fp f X Kb (C.cutAt i).J k := by
      refine ⟨hs.1, fun s hs' hs0 ↦ ?_, fun _ hn ↦ ?_⟩
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
      exact hs.1
    have hp := segAt_ok H hst hrun (bookOf_holds _ BookHolds.nil hs.2.2.1) hs.2.2.2
    unfold winEnd at hend
    by_cases hi : i < C.cuts.length
    · have hb : Nat.blt i C.cuts.length = true := Nat.blt_eq.mpr hi
      rw [hb] at hend
      simp only [Bool.cond_true, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at hend
      obtain ⟨⟨hchk, hle⟩, henv⟩ := hend
      refine ⟨fun _ ↦ ?_, fun h ↦ absurd hi (Nat.not_lt.mpr h)⟩
      obtain ⟨hl, -, harr⟩ := walk_sound W (C.stmtsAt cf i) st [] k True hp
        (by rw [hchk]; simp) (fun _ _ _ _ _ ↦ trivial)
      obtain ⟨k', hk', ⟨hsafe, hseg, hwend⟩, hhand⟩ := harr _ hchk
      refine ⟨hconv hl, hle, k', hk', hsafe, ?_, ?_⟩
      · split at henv
        · rename_i s hs'
          simp only [Bool.and_eq_true, beq_iff_eq] at henv
          rw [getF_eq] at hs'
          exact (hseg s hs' henv.1).2.1.sub henv.2
        · rename_i hs'
          rw [getF_eq] at hs'
          have := hwend (by simp only [hX, Cert.fxAt, hb, Bool.cond_true]) hs'
          simpa only [hX, Cert.fxAt, hb, Bool.cond_true] using this
      · have hw : X.win = some ((C.cutAt (i + 1)).J, (C.cutAt (i + 1)).facts, (C.cutAt (i + 1)).bnd) := by
          simp only [hX, Cert.fxAt, hb, Bool.cond_true]
        exact hhand _ _ _ hw rfl
    · have hb : Nat.blt i C.cuts.length = false := blt_false (Nat.not_lt.mp hi)
      rw [hb] at hend
      simp only [Bool.cond_false, beq_iff_eq] at hend
      refine ⟨fun h ↦ absurd h hi, fun _ ↦ ?_⟩
      obtain ⟨hl, -, -⟩ := walk_sound W (C.stmtsAt cf i) st [] k False hp
        (by rw [hend]; simp) (fun J hJ ↦ by rw [hend] at hJ; cases hJ)
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
each window's memory bounds and semantic pairs given by the statements before it: its core
relation holds of its frame, and a run of a function other than `main` returns in fewer steps. -/
theorem checkWins_run {main : Bool} (hc : ∀ i ≤ C.cuts.length, checkWin G f cf C main i = true)
    (hf : f ∈ Data.functions) (hfind : Prog.find? cf.name = some cf) (hpows : C.facts.pows.Ok)
    (hκ : κ ≤ 32) {fp : K} (hfp : C.facts.fpOne = true → fp = 1) {k : ℕ}
    (hC : ∀ i, FunSpecLt guest L k (G.sig i).entry (Pre G L i) (Post Prog G L i))
    (hjt : JTHolds G L) (henv : EnvHolds L fp C.facts.entryEnv) (hpre : BndHolds L fp C.pre)
    (hmem : MemPre L fp C.mem) (hsem : SemHolds G L fp C.sem)
    (hknown : ∀ i ≤ C.cuts.length, 0 < i → Core.Stmt.HoldsList (Prog.Rel L.read) L.read
      (valG L fp C) (cf.body.take (C.cutAt i).start) True (fun _ ↦ True) →
        MemKnown L fp (C.cutAt i).known ∧ SemHolds G L fp (C.cutAt i).sems)
    (hsafe : Safe guest L k ⟨gpow f.entry, fp⟩) :
    Prog.Rel L.read cf.name (frameWords L fp 2 cf.params.length)
        (frameWords L fp (2 + cf.params.length) C.nret) ∧ BndHolds L fp C.post ∧
      (main = false → ∃ k' < k, ∃ r, retRegs L fp = some r ∧ Safe guest L k' r) := by
  have hcont := cont_of hc
  have run := fun i (hi : i ≤ C.cuts.length) {k'} hk' hs (hkn : _ ∧ _) ↦
    checkWin_run (Prog := Prog) (hc i hi) hcont hi hf hpows hκ hfp hC hjt hmem hkn.1 hkn.2 (k := k')
      hk' hs
  have hkn0 : MemKnown L fp (C.cutAt 0).known ∧ SemHolds G L fp (C.cutAt 0).sems :=
    ⟨fun _ h ↦ by simp [Cert.cutAt] at h, hsem⟩
  have hs0 : WinStart L fp f C 0 k :=
    ⟨by simpa [Cert.cutAt] using hsafe, henv, by simp [Cert.cutAt], hpre⟩
  have reach : ∀ i ≤ C.cuts.length, ∃ k' ≤ k, WinStart L fp f C i k' ∧
      Core.Stmt.HoldsList (Prog.Rel L.read) L.read (valG L fp C)
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
      have hkn : MemKnown L fp (C.cutAt i).known ∧ SemHolds G L fp (C.cutAt i).sems := by
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
      SemHolds G L fp (C.cutAt C.cuts.length).sems := by
    rcases Nat.eq_zero_or_pos C.cuts.length with h0 | hi0
    · rw [h0]; exact hkn0
    · exact hknown _ le_rfl hi0 (Core.holdsList_mono (fun _ _ _ h ↦ h) _ id (fun _ _ ↦ trivial) hl)
  have hr := run _ le_rfl hk' hs hkn
  have hlast := hr.2.2 le_rfl
  have hall : Core.Stmt.HoldsList (Prog.Rel L.read) L.read (valG L fp C) cf.body False
      (RetOf L fp G f cf C main k) := by
    rw [← stmtsAt_last (C := C) (i := C.cuts.length) le_rfl, Core.holdsList_append]
    exact Core.holdsList_mono (fun _ _ _ h ↦ h) _ (fun _ ↦ hlast) (fun _ h ↦ h) hl
  have hparams := (run 0 (Nat.zero_le _) le_rfl hs0 hkn0).1 rfl
  obtain ⟨rs, hw, hback, hpost⟩ := (holdsList_reach cf.body hall).resolve_left id
  refine ⟨(Core.rel_iff Prog _ _ _).mpr ⟨cf, hfind, valG L fp C, ?_, ?_⟩, hpost,
    fun hm ↦ hback hm⟩
  · apply List.ext_getElem (by simp [frameWords])
    intro m h1 h2
    simp only [List.getElem_map, frameWords, List.getElem_range, valG]
    rw [hparams m (by simpa using h1)]
  · exact Core.holdsList_mono (fun _ _ _ h ↦ h) cf.body id (fun rs h ↦ h.1) hall

end Fn

end
end LeanVM.Guest.Check
