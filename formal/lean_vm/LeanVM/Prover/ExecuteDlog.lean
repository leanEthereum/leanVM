module

public import LeanVM.Prover.ExecuteMem
public import LeanVM.Semantics.Lemmas
public import LeanVM.Parameters.Generator
import Mathlib.Data.List.Forall2
import Mathlib.Tactic.Ring

/-!
# The executor's logarithms are right

`Dlog.Ok`: every entry of the table's indices maps a lane to an exponent of that lane, and
`top = g^cover`. `grow`, `note` and `log` keep it, and a logarithm found is one
(`Dlog.log_ok`): `baby` is such an index (`fill_ok`), the baby-step giant-step and the coarse
search keep `y · g^j = x` (`bsgs_ok`, `resolve_ok`). `decode_ok`: a decoded instruction's offsets
are the exponents of its operands (`OpOf`).
-/

namespace LeanVM.Prover.Exec

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-! ## Indices -/

/-- Every entry maps a lane to an exponent of that lane. -/
def IdxOk (I : Idx) : Prop := ∀ w k, I[w]? = some k → (g ^ k).lane = w

theorem idxOk_empty : IdxOk ∅ := fun w k h ↦ by simp at h

theorem IdxOk.insert {I : Idx} (hI : IdxOk I) {y : K} {k : ℕ} (hy : g ^ k = y) :
    IdxOk (I.insert y.lane k) := by
  intro w j h
  rw [Std.HashMap.getElem?_insert] at h
  split_ifs at h with hw
  · cases h; rw [hy]; exact beq_iff_eq.mp hw
  · exact hI w j h

theorem IdxOk.get {I : Idx} (hI : IdxOk I) {y : K} {k : ℕ} (h : I[y.lane]? = some k) : g ^ k = y :=
  K.lane_injective (hI _ _ h)

theorem fill_ok (gs : K) (step : ℕ) (hgs : gs = g ^ step) :
    ∀ (n k : ℕ) (y : K) (I : Idx), y = g ^ k → IdxOk I → IdxOk (fill gs step n k y I)
  | 0, _, _, _, _, hI => hI
  | n + 1, k, y, I, hy, hI =>
    fill_ok gs step hgs n (k + step) (y * gs) _ (by rw [hy, hgs, pow_add]) (hI.insert hy.symm)

theorem baby_ok : IdxOk baby := fill_ok g 1 (pow_one g).symm _ 0 1 ∅ (pow_zero g).symm idxOk_empty

/-! ## Searches -/

theorem gInv_mul_g : gInv * g = 1 := by rw [mul_comm]; exact g_mul_inv_word

theorem giant_mul : giant * g ^ 2 ^ 17 = 1 := by
  rw [giant, ← mul_pow, gInv_mul_g, one_pow]

theorem bsgs_ok : ∀ (n a : ℕ) (y : K) (k : ℕ), bsgs n a y = some k → g ^ k = y * g ^ (2 ^ 17 * a)
  | 0, _, _, _, h => by rw [bsgs.eq_1] at h; cases h
  | n + 1, a, y, k, h => by
    rw [bsgs.eq_2] at h
    split at h
    · rename_i j hj
      cases h
      rw [pow_add, baby_ok.get hj, mul_comm]
    · rw [bsgs_ok n (a + 1) _ k h, mul_add, mul_one, pow_add]
      calc y * giant * (g ^ (2 ^ 17 * a) * g ^ 2 ^ 17)
          = y * g ^ (2 ^ 17 * a) * (giant * g ^ 2 ^ 17) := by ring
        _ = y * g ^ (2 ^ 17 * a) := by rw [giant_mul, mul_one]

theorem boundedDlog_ok {x : K} {nbits k : ℕ} (h : boundedDlog x nbits = some k) : g ^ k = x := by
  unfold boundedDlog at h
  rw [bsgs_ok _ 0 x k h, mul_zero, pow_zero, mul_one]

theorem resolve_ok {coarse : Idx} (hc : IdxOk coarse) :
    ∀ (n j : ℕ) (y : K) (k : ℕ), resolve coarse n j y = some k → g ^ k = y * g ^ j
  | 0, _, _, _, h => by rw [resolve.eq_1] at h; cases h
  | n + 1, j, y, k, h => by
    rw [resolve.eq_2] at h
    split at h
    · rename_i k0 hk0
      cases h
      rw [pow_add, hc.get hk0]
    · rw [resolve_ok hc n (j + 1) _ k h, pow_succ]
      calc y * gInv * (g ^ j * g) = y * g ^ j * (gInv * g) := by ring
        _ = y * g ^ j := by rw [gInv_mul_g, mul_one]

/-! ## The table -/

/-- The table's invariant. -/
structure Dlog.Ok (D : Dlog) : Prop where
  noted : IdxOk D.noted
  coarse : IdxOk D.coarse
  top : D.top = g ^ D.cover

theorem Dlog.ok_empty : Dlog.empty.Ok := ⟨idxOk_empty, idxOk_empty, (pow_zero g).symm⟩

theorem Dlog.Ok.grow {D : Dlog} (h : D.Ok) (n : ℕ) : (D.grow n).Ok := by
  unfold Dlog.grow
  split_ifs
  · obtain ⟨noted, coarse, cover, top⟩ := D
    exact ⟨h.noted, fill_ok (g ^ 64) 64 rfl _ _ _ _ h.top h.coarse, rfl⟩
  · exact h

theorem Dlog.Ok.note {D : Dlog} (h : D.Ok) (k : ℕ) : (D.note k).Ok := by
  obtain ⟨noted, coarse, cover, top⟩ := D
  exact ⟨h.noted.insert rfl, h.coarse, h.top⟩

theorem orElse_some {o : Option ℕ} {f : Unit → Option ℕ} {k : ℕ} (h : o.orElse f = some k) :
    o = some k ∨ f () = some k := by
  cases o with
  | none => exact Or.inr h
  | some a => exact Or.inl h

/-- `log` keeps the invariant, and a logarithm it finds is one, below the bound. -/
theorem Dlog.log_ok {D : Dlog} (h : D.Ok) (x : K) (b : ℕ) :
    (D.log x b).2.Ok ∧ ∀ k, (D.log x b).1 = some k → g ^ k = x ∧ k < b := by
  unfold Dlog.log
  split
  · rename_i k hk
    refine ⟨h, fun k' hk' ↦ ?_⟩
    dsimp only at hk'
    split_ifs at hk' with hb
    cases hk'
    exact ⟨h.noted.get hk, hb⟩
  · split
    · rename_i k hk
      have hx : g ^ k = x := by
        rcases orElse_some hk with hk | hk
        · rw [resolve_ok h.coarse _ _ _ _ hk, pow_zero, mul_one]
        · exact boundedDlog_ok hk
      split_ifs with hb
      · exact ⟨h.note k, fun k' hk' ↦ by cases hk'; exact ⟨hx, hb⟩⟩
      · exact ⟨h, fun k' hk' ↦ by cases hk'⟩
    · exact ⟨h, fun k' hk' ↦ by cases hk'⟩

/-! ## Decoding -/

theorem offOf_ok {o : K} {k : ℕ} (h : offOf o = some k) : g ^ k = o := boundedDlog_ok h

theorem optMapM_ok {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (l' : List β), l.mapM f = some l' → List.Forall₂ (fun a b ↦ f a = some b) l l'
  | [], l', h => by simp only [List.mapM_nil] at h; cases h; exact List.Forall₂.nil
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    exact List.Forall₂.cons hb (optMapM_ok f l bs hbs)

/-- The instruction an `Op` decodes: its offsets are the exponents of the operands. -/
def OpOf : LeanIsaInstruction → Op → Prop
  | .xor oA oB oC, .xor a b c => g ^ a = oA ∧ g ^ b = oB ∧ g ^ c = oC
  | .mulNative oA oB oC, .mul a b c => g ^ a = oA ∧ g ^ b = oB ∧ g ^ c = oC
  | .setConstant o k, .set a k' => g ^ a = o ∧ k' = k
  | .deref o1 o2 o3 mode, .deref a1 a2 a3 mode' =>
    g ^ a1 = o1 ∧ g ^ a2 = o2 ∧ g ^ a3 = o3 ∧ mode' = mode
  | .jump oc od of, .jump c d f => g ^ c = oc ∧ g ^ d = od ∧ g ^ f = of
  | .keccak om otail ob8 ocap oout inOdd outOdd outCells, .keccak ins out inOdd' outOdd' count =>
    inOdd' = inOdd ∧ outOdd' = outOdd ∧ count = outCells.cellCount ∧ g ^ out = oout ∧
      ∃ l : List ℕ, ins = l.toArray ∧
        List.Forall₂ (fun c k ↦ g ^ k = keccakInputCellOffset om otail ob8 ocap c)
          (List.finRange 13) l
  | _, _ => False

theorem decode_ok {ins : LeanIsaInstruction} {op : Op} (h : decode ins = some op) :
    OpOf ins op := by
  cases ins with
  | keccak om otail ob8 ocap oout inOdd outOdd outCells =>
    simp only [decode, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨l, hl, k, hk, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, offOf_ok hk, l, rfl,
      (optMapM_ok _ _ _ hl).imp fun _ _ h ↦ offOf_ok h⟩
  | _ =>
    simp only [decode, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, ha, h⟩ := h
    first
    | (obtain ⟨b, hb, c, hc, rfl⟩ := h; exact ⟨offOf_ok ha, offOf_ok hb, offOf_ok hc⟩)
    | (obtain ⟨b, hb, c, hc, rfl⟩ := h; exact ⟨offOf_ok ha, offOf_ok hb, offOf_ok hc, rfl⟩)
    | (obtain rfl := h; exact ⟨offOf_ok ha, rfl⟩)

end

end LeanVM.Prover.Exec
