/-
  LeanVM.Guest.Backend.Sound.Pool

  The valuation by places, the facts an instruction gives about frame words, and what the pools
  of a scope claim.
-/

module

public import LeanVM.Guest.Backend.Sound.Sem
public import LeanVM.Guest.Backend.Sound.Asm
public import LeanVM.Guest.Backend.Place
public import LeanVM.Guest.CoreLoc

/-!
# Frame words, places and pools

* `wd L fp o` is the word of frame cell `o` (`0` if the cell is no memory), and `valP L fp locs`
  the valuation by places: a value is the word of its cell, or for an `addr` pointer the word of
  its cell times `g^exp`. It replaces the certificates' `valG`.
* `holds_*`: what `Guest.Holds` of each resolved instruction says about `wd`. The memory is one
  fixed image, so a fact about a cell, once an instruction has checked it, stays.
* `PoolOK`: every entry of a scope's pools names a cell that holds the pooled relation (P3). It
  holds of the scope a function starts with, and it is the invariant of the placement walk.
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

variable {κ : ℕ} (L : MemoryImage κ) (fp : K)

/-- The word in frame cell `o`, `0` if none. -/
noncomputable def wd (o : ℕ) : E := (L.read (fp * addressOfIndex o)).getD 0

/-- The word of a place. -/
noncomputable def locVal : Loc → E
  | .cell n => wd L fp n
  | .shifted n exp => wd L fp n * ofK (addressOfIndex exp)

/-- **The valuation by places**: every value is the word of its place. -/
noncomputable def valP (locs : VMap Loc) : Val := fun v =>
  match locs[v]? with
  | some l => locVal L fp l
  | none => 0

/-- The `n` words of the frame from cell `o`. -/
noncomputable def frameWords (o n : ℕ) : List E := (List.range n).map fun i => wd L fp (o + i)

variable {L fp}

theorem wd_of_read {o : ℕ} {w : E} (h : L.read (fp * addressOfIndex o) = some w) :
    wd L fp o = w := by
  rw [wd, h]
  rfl

/-! ## Words -/

theorem word_one : Guest.word 1 0 = 1 := by
  rw [Guest.word, show K.ofBits 1 = 1 from rfl, show K.ofBits 0 = 0 from rfl, ← ofK_eq_ofLimbs]
  exact map_one (algebraMap K E)

theorem word_zero : Guest.word 0 0 = 0 := by
  rw [Guest.word, show K.ofBits 0 = 0 from rfl]
  exact (ofLimbs_eq_zero_iff _).mpr rfl

theorem word_limbsOf (c : E) : Guest.word (limbsOf c).1 (limbsOf c).2 = c := by
  rw [Guest.word, limbsOf, ofBits_toNat, ofBits_toNat, ofLimbs_limb]

theorem word_gpow {e : ℕ} (he : e < 2 ^ 128) :
    Guest.word (gpowLimbs e).1 (gpowLimbs e).2 = ofK (addressOfIndex e) := by
  rw [Guest.word, gpowLimbs, ofBits_toNat, gpowK_eq he, ofK_eq_ofLimbs]
  rfl

theorem ofK_one : ofK (1 : K) = 1 := map_one (algebraMap K E)

theorem isInK_ofK (a : K) : IsInK (ofK a) := (isInK_iff _).mpr ⟨a, rfl⟩

theorem isInK_mul {x z : E} (hx : IsInK x) (hz : IsInK z) : IsInK (x * z) := by
  obtain ⟨a, rfl⟩ := (isInK_iff _).mp hx
  obtain ⟨b, rfl⟩ := (isInK_iff _).mp hz
  rw [← ofK_mul]
  exact isInK_ofK _

theorem limb_mul_ofK {x : E} (hx : IsInK x) (b : K) : (x * ofK b).limb 0 = x.limb 0 * b := by
  obtain ⟨a, rfl⟩ := (isInK_iff _).mp hx
  rw [← ofK_mul]
  simp

theorem ofK_gpow_add (a b : ℕ) :
    ofK (addressOfIndex a) * ofK (addressOfIndex b) = ofK (addressOfIndex (a + b)) := by
  rw [← ofK_mul, addressOfIndex, addressOfIndex, addressOfIndex, pow_add]

/-! ## What an instruction says of the frame's words -/

variable {Γ : Site κ} {pc : ℕ}

theorem holds_set_const {o c0 c1 : ℕ}
    (h : Holds Γ.L pc fp (Γ.R (.set o (.const c0 c1)))) : wd Γ.L fp o = Guest.word c0 c1 :=
  wd_of_read h

theorem holds_xor {a b c : ℕ} (h : Holds Γ.L pc fp (Γ.R (.xor a b c))) :
    wd Γ.L fp c = wd Γ.L fp a + wd Γ.L fp b := by
  obtain ⟨va, vb, ha, hb, hc⟩ := h
  rw [wd_of_read ha, wd_of_read hb, wd_of_read hc]

theorem holds_mul {a b c : ℕ} (h : Holds Γ.L pc fp (Γ.R (.mul a b c))) :
    wd Γ.L fp c = wd Γ.L fp a * wd Γ.L fp b := by
  obtain ⟨va, vb, ha, hb, hc⟩ := h
  rw [wd_of_read ha, wd_of_read hb, wd_of_read hc]

/-- A `DEREF` of a cell: its pointer is in `K` and the word it points at is the cell's. -/
theorem holds_deref {p off o : ℕ} (h : Holds Γ.L pc fp (Γ.R (.deref p off o .cell))) :
    IsInK (wd Γ.L fp p) ∧
      Γ.L.read ((wd Γ.L fp p).limb 0 * addressOfIndex off) = some (wd Γ.L fp o) := by
  obtain ⟨pw, v, hp, hK, ho, hr⟩ := h
  rw [wd_of_read hp, wd_of_read ho]
  exact ⟨hK, hr⟩

/-- A `DEREF` storing the frame pointer. -/
theorem holds_deref_fp {p off o : ℕ} (h : Holds Γ.L pc fp (Γ.R (.deref p off o .fp))) :
    IsInK (wd Γ.L fp p) ∧
      Γ.L.read ((wd Γ.L fp p).limb 0 * addressOfIndex off) = some (ofK fp) := by
  obtain ⟨pw, v, hp, hK, ho, hr⟩ := h
  rw [wd_of_read hp]
  exact ⟨hK, hr⟩

/-! ## Pools -/

/-- **What the pools of a scope claim** (P3): every entry's cell holds the pooled relation on
its key's cells. `main`'s frame is at `1`, where its pooled `1` is its own pointer. -/
structure PoolOK (L : MemoryImage κ) (fp : K) (sc : Scope) : Prop where
  consts : ∀ k o, sc.consts.get? k = some o → wd L fp o = Guest.word k.1 k.2
  xors : ∀ k o, sc.xors.get? k = some o → wd L fp o = wd L fp k.1 + wd L fp k.2
  muls : ∀ k o, sc.muls.get? k = some o → wd L fp o = wd L fp k.1 * wd L fp k.2
  loads : ∀ k o, sc.loads.get? k = some o →
    IsInK (wd L fp k.1) ∧ L.read ((wd L fp k.1).limb 0 * addressOfIndex k.2) = some (wd L fp o)
  mats : ∀ c l, sc.mats.get? c = some l → ∀ p ∈ l,
    wd L fp p.2 = wd L fp c * ofK (addressOfIndex p.1)
  selfFp : ∀ o, sc.selfFp = some o → wd L fp o = ofK fp

/-- Places only grow, and a value's place never changes (P1). -/
def Sub (m₁ m₂ : VMap Loc) : Prop := ∀ (v : V) (l : Loc), m₁[v]? = some l → m₂[v]? = some l

theorem Sub.refl (m : VMap Loc) : Sub m m := fun _ _ h => h

theorem Sub.trans {m₁ m₂ m₃ : VMap Loc} (h₁ : Sub m₁ m₂) (h₂ : Sub m₂ m₃) : Sub m₁ m₃ :=
  fun v l h => h₂ v l (h₁ v l h)

theorem Sub.insert {m : VMap Loc} {v : V} (l : Loc) (h : m.contains v = false) :
    Sub m (m.insert v l) := by
  intro a la ha
  rw [KMap.getElem?_insert]
  split
  · next heq =>
    subst heq
    rw [KMap.getElem?_eq_none_of_contains_eq_false h] at ha
    cases ha
  · exact ha

/-- Under the final places, a value placed during the walk has its place's word. -/
theorem valP_of_sub {m F : VMap Loc} (h : Sub m F) {v : V} {l : Loc}
    (hv : m[v]? = some l) : valP L fp F v = locVal L fp l := by
  rw [valP, h v l hv]

end
end LeanVM.Guest.Backend
