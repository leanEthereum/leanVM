/-
  LeanVM.Guest.B1.Sig.Merkle

  A 64-byte `keccak` of four cells is their hash, and `merkle_path` (`merkleT`) folds a node up its
  hinted children: each child check makes the node the child the level's bit names.
-/

module

public import LeanVM.Guest.B1.Sig.WotsSound
public import LeanVM.Guest.B1.Sig.XmssScheme

/-!
# Merkle paths, sound

* `k64_sound`: `keccak([m0, m1], [m2, m3], out)` writes `hcell` of the four cells into `out`;
* `merkleT_sound`: the node a path reaches is `mFold` of the start, level `l` hashing `P`, the
  level's address and the pair in the order of its bit (`bit = 0`: the node then its sibling), the
  sibling being the hinted child the node is not (`mSib`); `mFold_eq_xFold` reads it as the
  schemes' `xFold`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **A 64-byte `keccak` of four cells** writes their hash. -/
theorem k64_sound {pad : Nat} (hp : PadOK σ pad) {m0 m1 m2 m3 : V} {c o : Nat}
    (h : AtomsHold rd σ (k64 pad m0 m1 m2 m3 c o)) :
    σ (.n o) = (hcell [σ m0, σ m1, σ m2, σ m3]).1 := by
  rw [k64_eq] at h
  have := kMsg_sound (cells := [.cell m0, .cell m1, .cell m2, .cell m3]) (len := 64) (tailRun := false)
    (out := some o) hp (fun h => by simp at h) h (by simp) (fun j hj => by
      simp only [List.map, KC.val, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl)
  have ho : (kMsg pad [.cell m0, .cell m1, .cell m2, .cell m3] 64 false (some o) c).2.2 = o := rfl
  rw [ho] at this
  rw [this]
  simp only [hcell, List.map, KC.val, cellsBytes_eq_flatMap]
  congr 2

/-! ## Merkle paths -/

/-- The levels `l ..< l + m` of a path from `x`, forward: level `l` hashes `P`, its address `A l`
and the pair in the order of bit `l`. -/
def mFold (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) : Nat → Nat → E → E
  | 0, _, x => x
  | m + 1, l, x => mFold pp A bits sibs m (l + 1)
      (hcell [pp, A l, if bits l then sibs l else x, if bits l then x else sibs l]).1

theorem mFold_succ (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) :
    ∀ (m l : Nat) (x : E), mFold pp A bits sibs (m + 1) l x =
      (hcell [pp, A (l + m), if bits (l + m) then sibs (l + m) else mFold pp A bits sibs m l x,
        if bits (l + m) then mFold pp A bits sibs m l x else sibs (l + m)]).1
  | 0, l, x => by simp [mFold]
  | m + 1, l, x => by
      rw [mFold, mFold_succ pp A bits sibs m (l + 1), show l + 1 + m = l + (m + 1) by omega]
      rfl

/-- **The forward fold is the schemes' fold.** -/
theorem mFold_eq_xFold (pp : E) (A : Nat → E) (bits : Nat → Bool) (sibs : Nat → E) :
    ∀ (m : Nat) (x : E), mFold pp A bits sibs m 0 x = xFold pp A bits sibs m x
  | 0, x => rfl
  | m + 1, x => by
      rw [mFold_succ, mFold_eq_xFold pp A bits sibs m x, Nat.zero_add]
      rfl

theorem mFold_congr {pp : E} {A A' : Nat → E} {bits bits' : Nat → Bool} {sibs sibs' : Nat → E} :
    ∀ (m l : Nat), (∀ l', l ≤ l' → A l' = A' l' ∧ bits l' = bits' l' ∧ sibs l' = sibs' l') →
      ∀ x, mFold pp A bits sibs m l x = mFold pp A' bits' sibs' m l x
  | 0, _, _, _ => rfl
  | m + 1, l, h, x => by
      simp only [mFold]
      obtain ⟨h1, h2, h3⟩ := h l le_rfl
      rw [h1, h2, h3]
      exact mFold_congr m (l + 1) (fun l' hl' => h l' (by omega)) _

/-- The base after level `l` of a path from base `b`. -/
def mNext (nodeOf : Nat → Option V) (l b : Nat) : Nat :=
  (match nodeOf l with
    | none => b + 5
    | some _ => b + 6) + 2

/-- The base of level `l + j` of a path from level `l` at base `b`. -/
def mBase (nodeOf : Nat → Option V) : Nat → Nat → Nat → Nat
  | _, 0, b => b
  | l, j + 1, b => mBase nodeOf (l + 1) j (mNext nodeOf l b)

/-- The address cell of level `l` at base `b`. -/
def mAdr (nodeOf : Nat → Option V) (l b : Nat) : V :=
  match nodeOf l with
  | none => .n (b + 4)
  | some _ => .n (b + 5)

/-- The sibling of level `l` at base `b`: the hinted child the node is not. -/
def mSib (σ : Val) (bitOf : Nat → V) (l b : Nat) : E :=
  if σ (bitOf l) = 1 then σ (.n b) else σ (.n (b + 1))

/-- A bit pinned Boolean. -/
def IsBit (x : E) : Prop := x * x = x

theorem isBit_cases {x : E} (h : IsBit x) : x = 0 ∨ x = 1 := by
  have : x * (x - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

theorem merkleT_atoms (pad : Nat) (pp : V) (bitOf : Nat → V) (nodeOf : Nat → Option V)
    (addrOf : Nat → Nat) : ∀ m l cur b, atomsOnly (merkleT pad pp bitOf nodeOf addrOf m l cur b).1 = true
  | 0, _, _, _ => rfl
  | m + 1, l, cur, b => by
      simp only [merkleT]
      rw [atomsOnly_append, atomsOnly_append, atomsOnly_append, merkleT_atoms pad pp bitOf nodeOf addrOf m]
      split <;> rfl

/-- One level: the child check makes the node the child its bit names. -/
theorem merkle_level {pad : Nat} (hp : PadOK σ pad) {pp bit cur adr : V} {b c : Nat}
    (hbit : IsBit (σ bit))
    (h1 : AtomsHold rd σ [hintW "siblings" [.n b, .n (b + 1)], addS (.n (b + 2)) cur (.n b),
      addS (.n (b + 3)) (.n b) (.n (b + 1)), mulS (.n (b + 2)) bit (.n (b + 3))])
    (hk : AtomsHold rd σ (k64 pad pp adr (.n b) (.n (b + 1)) c (c + 1))) :
    σ (.n (c + 1)) = (hcell [σ pp, σ adr,
      if decide (σ bit = 1) then (if σ bit = 1 then σ (.n b) else σ (.n (b + 1))) else σ cur,
      if decide (σ bit = 1) then σ cur else (if σ bit = 1 then σ (.n b) else σ (.n (b + 1)))]).1 := by
  have e1 := h1.atom (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have e2 := h1.atom (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have e3 := h1.atom (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_self ..))))
  simp only [Atom.Holds] at e1 e2 e3
  have hk2 := k64_sound hp hk
  rw [hk2]
  rcases isBit_cases hbit with h0 | h1'
  · rw [h0, zero_mul, e1] at e3
    have : σ cur = σ (.n b) := (Value.e_add_eq_zero_iff).mp e3
    simp [h0, this]
  · rw [h1', one_mul, e1, e2] at e3
    have : σ cur = σ (.n (b + 1)) := add_left_cancel (a := σ (.n b)) (by rw [add_comm (σ (.n b))]; exact e3)
    simp [h1', this]

/-- **A Merkle path, sound**: from `cur`, `m` levels from `l` reach `mFold` of `cur`'s value, each
level's sibling `mSib` and its address `mAdr`. -/
theorem merkleT_sound {pad : Nat} (hp : PadOK σ pad) {pp : V} {bitOf : Nat → V}
    {nodeOf : Nat → Option V} {addrOf : Nat → Nat} {bound : Nat}
    (hbit : ∀ l < bound, IsBit (σ (bitOf l))) :
    ∀ (m l : Nat) (cur : V) (b : Nat), l + m ≤ bound →
      AtomsHold rd σ (merkleT pad pp bitOf nodeOf addrOf m l cur b).1 →
      σ (merkleT pad pp bitOf nodeOf addrOf m l cur b).2.2 =
        mFold (σ pp) (fun l' => σ (mAdr nodeOf l' (mBase nodeOf l (l' - l) b)))
          (fun l' => decide (σ (bitOf l') = 1)) (fun l' => mSib σ bitOf l' (mBase nodeOf l (l' - l) b))
          m l (σ cur)
  | 0, l, cur, b, _, _ => rfl
  | m + 1, l, cur, b, hm, h => by
      have step : ∀ c : Nat, mNext nodeOf l b = c + 2 → V.n (c - 1) = mAdr nodeOf l b →
          AtomsHold rd σ ([hintW "siblings" [.n b, .n (b + 1)], addS (.n (b + 2)) cur (.n b),
            addS (.n (b + 3)) (.n b) (.n (b + 1)), mulS (.n (b + 2)) (bitOf l) (.n (b + 3))]) →
          AtomsHold rd σ (k64 pad pp (.n (c - 1)) (.n b) (.n (b + 1)) c (c + 1)) →
          AtomsHold rd σ (merkleT pad pp bitOf nodeOf addrOf m (l + 1) (.n (c + 1)) (c + 2)).1 →
          σ (merkleT pad pp bitOf nodeOf addrOf m (l + 1) (.n (c + 1)) (c + 2)).2.2 =
            mFold (σ pp) (fun l' => σ (mAdr nodeOf l' (mBase nodeOf l (l' - l) b)))
              (fun l' => decide (σ (bitOf l') = 1)) (fun l' => mSib σ bitOf l' (mBase nodeOf l (l' - l) b))
              (m + 1) l (σ cur) := by
        intro c hc hadr h1 hk hr
        rw [merkleT_sound hp hbit m (l + 1) (.n (c + 1)) (c + 2) (by omega) hr]
        simp only [mFold, Nat.sub_self, mBase]
        rw [merkle_level hp (hbit l (by omega)) h1 hk, hadr]
        apply mFold_congr
        intro l' hl'
        have hb : mBase nodeOf (l + 1) (l' - (l + 1)) (c + 2) = mBase nodeOf l (l' - l) b := by
          rw [show l' - l = l' - (l + 1) + 1 by omega, mBase, hc]
        simp only [hb, and_self]
      simp only [merkleT] at h ⊢
      cases hn : nodeOf l with
      | none =>
          simp only [hn] at h ⊢
          exact step (b + 5) (by unfold mNext; rw [hn]) (by unfold mAdr; rw [hn]; rfl)
            (h.left.left.left.sub fun x hx => by simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto)
            h.left.right h.right
      | some nd =>
          simp only [hn] at h ⊢
          exact step (b + 6) (by unfold mNext; rw [hn]) (by unfold mAdr; rw [hn]; rfl)
            (h.left.left.left.sub fun x hx => by simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto)
            h.left.right h.right

/-- **A path's addresses**: level `l`'s address cell holds its constant, plus the parent's index
unless it is a root. -/
theorem merkleT_adr {pad : Nat} {pp : V} {bitOf : Nat → V} {nodeOf : Nat → Option V}
    {addrOf : Nat → Nat} : ∀ (m l : Nat) (cur : V) (b : Nat),
    AtomsHold rd σ (merkleT pad pp bitOf nodeOf addrOf m l cur b).1 → ∀ j < m,
      σ (mAdr nodeOf (l + j) (mBase nodeOf l j b)) = word (addrOf (l + j)) 0 +
        (match nodeOf (l + j) with
          | none => 0
          | some nd => σ nd)
  | 0, _, _, _, _, j, hj => absurd hj (by omega)
  | m + 1, l, cur, b, h, j, hj => by
      simp only [merkleT] at h
      rcases j with _ | j
      · simp only [Nat.add_zero, mBase]
        cases hn : nodeOf l with
        | none =>
            simp only [hn] at h
            have e := h.atom (a := .const (.n (b + 4)) (word (addrOf l) 0)) (by simp [cst])
            simp only [Atom.Holds] at e
            simp [mAdr, hn, e]
        | some nd =>
            simp only [hn] at h
            have e1 := h.atom (a := .const (.n (b + 4)) (word (addrOf l) 0)) (by simp [cst])
            have e2 := h.atom (a := .add (.n (b + 5)) (.n (b + 4)) nd) (by simp [addS])
            simp only [Atom.Holds] at e1 e2
            simp [mAdr, hn, e1, e2]
      · have hr : AtomsHold rd σ (merkleT pad pp bitOf nodeOf addrOf m (l + 1)
            (.n ((match nodeOf l with | none => b + 5 | some _ => b + 6) + 1)) (mNext nodeOf l b)).1 :=
          h.right
        have := merkleT_adr m (l + 1) _ _ hr j (by omega)
        rw [show l + 1 + j = l + (j + 1) by omega] at this
        simpa [mBase] using this

end
end LeanVM.Guest.B1.Sig
