/-
  LeanVM.Guest.B1.KeccakGkr.Lib

  The vocabulary of B1-d's proofs: functions found by index, a `KECCAK` atom in the even layouts
  as a squeeze of the carried sponge, the rate cells of waiting scalars, and `fs_next`'s cells.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.Interface
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Common.Atoms

/-!
# B1-d: shared lemmas

* `keccak_outs`: a `KECCAK` atom in the even layouts writes the cells of the permutation of the
  cells it reads (`permOf`), output `k` its cell `k`;
* `rateOf_nil` … `rateOf_four`: the rate cells of `k ≤ 4` waiting scalars (`Keccak.scalarCells`);
* `squeeze_atom`: the atom on the rate cells of `s.pend` and the capacity `s.cap`, followed by
  `challenge_from_state` on its output `0`, is `s.squeeze`: the challenge, and the capacity
  cells `8..12` of its outputs;
* `fsNext_scalar`: `fs_next`'s two cells are the scalar's rate cells.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## A `KECCAK` atom -/

/-- **A `KECCAK` atom in the even layouts**: it reads thirteen cells and writes, as output `k`,
cell `k` of their permutation. -/
theorem keccak_outs {ins outs : List V} (h : (Atom.keccak ins outs false false).Holds rd σ)
    (ho : outs.length = 13 := by first | rfl | simp) :
    ins.length = 13 ∧ outs.length = 13 ∧
      ∀ k (hk : k < 13), σ (outs.getD k default) = cellsOfState (permOf (ins.map σ)) false ⟨k, hk⟩ := by
  obtain ⟨hi, -, hout⟩ := keccakA_perm h ho
  refine ⟨hi, ho, fun k hk => ?_⟩
  have := congrFun hout ⟨k, hk⟩
  simp only [cells13, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (show k < outs.length by omega), Option.map_some,
    Option.getD_some] at this ⊢
  exact this

/-! ## Rate cells -/

theorem range8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl

theorem rateCell_fst (ps : List (E × ℕ)) (k : ℕ) (hk : k < ps.length) :
    Keccak.rateCell ps (2 * k) = (Keccak.scalarCells ps[k].1 ps[k].2).1 :=
  congrArg Prod.fst (Keccak.rateCell_scalar ps k hk)

theorem rateCell_snd (ps : List (E × ℕ)) (k : ℕ) (hk : k < ps.length) :
    Keccak.rateCell ps (2 * k + 1) = (Keccak.scalarCells ps[k].1 ps[k].2).2 :=
  congrArg Prod.snd (Keccak.rateCell_scalar ps k hk)

theorem rateOf_nil : rateOf [] = [0, 0, 0, 0, 0, 0, 0, 0] := by
  simp only [rateOf, range8, List.map_cons, List.map_nil,
    Keccak.rateCell_past [] (Nat.zero_le _)]

theorem rateOf_two (a b : E × ℕ) :
    rateOf [a, b] = [(Keccak.scalarCells a.1 a.2).1, (Keccak.scalarCells a.1 a.2).2,
      (Keccak.scalarCells b.1 b.2).1, (Keccak.scalarCells b.1 b.2).2, 0, 0, 0, 0] := by
  have h0 : Keccak.rateCell [a, b] 0 = (Keccak.scalarCells a.1 a.2).1 :=
    rateCell_fst [a, b] 0 (by simp)
  have h1 : Keccak.rateCell [a, b] 1 = (Keccak.scalarCells a.1 a.2).2 :=
    rateCell_snd [a, b] 0 (by simp)
  have h2 : Keccak.rateCell [a, b] 2 = (Keccak.scalarCells b.1 b.2).1 :=
    rateCell_fst [a, b] 1 (by simp)
  have h3 : Keccak.rateCell [a, b] 3 = (Keccak.scalarCells b.1 b.2).2 :=
    rateCell_snd [a, b] 1 (by simp)
  have h4 : Keccak.rateCell [a, b] 4 = 0 := Keccak.rateCell_past [a, b] (by simp)
  have h5 : Keccak.rateCell [a, b] 5 = 0 := Keccak.rateCell_past [a, b] (by simp)
  have h6 : Keccak.rateCell [a, b] 6 = 0 := Keccak.rateCell_past [a, b] (by simp)
  have h7 : Keccak.rateCell [a, b] 7 = 0 := Keccak.rateCell_past [a, b] (by simp)
  simp only [rateOf, range8, List.map_cons, List.map_nil, h0, h1, h2, h3, h4, h5, h6, h7]

theorem rateOf_three (a b c : E × ℕ) :
    rateOf [a, b, c] = [(Keccak.scalarCells a.1 a.2).1, (Keccak.scalarCells a.1 a.2).2,
      (Keccak.scalarCells b.1 b.2).1, (Keccak.scalarCells b.1 b.2).2,
      (Keccak.scalarCells c.1 c.2).1, (Keccak.scalarCells c.1 c.2).2, 0, 0] := by
  have h0 : Keccak.rateCell [a, b, c] 0 = (Keccak.scalarCells a.1 a.2).1 :=
    rateCell_fst [a, b, c] 0 (by simp)
  have h1 : Keccak.rateCell [a, b, c] 1 = (Keccak.scalarCells a.1 a.2).2 :=
    rateCell_snd [a, b, c] 0 (by simp)
  have h2 : Keccak.rateCell [a, b, c] 2 = (Keccak.scalarCells b.1 b.2).1 :=
    rateCell_fst [a, b, c] 1 (by simp)
  have h3 : Keccak.rateCell [a, b, c] 3 = (Keccak.scalarCells b.1 b.2).2 :=
    rateCell_snd [a, b, c] 1 (by simp)
  have h4 : Keccak.rateCell [a, b, c] 4 = (Keccak.scalarCells c.1 c.2).1 :=
    rateCell_fst [a, b, c] 2 (by simp)
  have h5 : Keccak.rateCell [a, b, c] 5 = (Keccak.scalarCells c.1 c.2).2 :=
    rateCell_snd [a, b, c] 2 (by simp)
  have h6 : Keccak.rateCell [a, b, c] 6 = 0 := Keccak.rateCell_past [a, b, c] (by simp)
  have h7 : Keccak.rateCell [a, b, c] 7 = 0 := Keccak.rateCell_past [a, b, c] (by simp)
  simp only [rateOf, range8, List.map_cons, List.map_nil, h0, h1, h2, h3, h4, h5, h6, h7]

theorem rateOf_four (a b c d : E × ℕ) :
    rateOf [a, b, c, d] = [(Keccak.scalarCells a.1 a.2).1, (Keccak.scalarCells a.1 a.2).2,
      (Keccak.scalarCells b.1 b.2).1, (Keccak.scalarCells b.1 b.2).2,
      (Keccak.scalarCells c.1 c.2).1, (Keccak.scalarCells c.1 c.2).2,
      (Keccak.scalarCells d.1 d.2).1, (Keccak.scalarCells d.1 d.2).2] := by
  have h0 : Keccak.rateCell [a, b, c, d] 0 = (Keccak.scalarCells a.1 a.2).1 :=
    rateCell_fst [a, b, c, d] 0 (by simp)
  have h1 : Keccak.rateCell [a, b, c, d] 1 = (Keccak.scalarCells a.1 a.2).2 :=
    rateCell_snd [a, b, c, d] 0 (by simp)
  have h2 : Keccak.rateCell [a, b, c, d] 2 = (Keccak.scalarCells b.1 b.2).1 :=
    rateCell_fst [a, b, c, d] 1 (by simp)
  have h3 : Keccak.rateCell [a, b, c, d] 3 = (Keccak.scalarCells b.1 b.2).2 :=
    rateCell_snd [a, b, c, d] 1 (by simp)
  have h4 : Keccak.rateCell [a, b, c, d] 4 = (Keccak.scalarCells c.1 c.2).1 :=
    rateCell_fst [a, b, c, d] 2 (by simp)
  have h5 : Keccak.rateCell [a, b, c, d] 5 = (Keccak.scalarCells c.1 c.2).2 :=
    rateCell_snd [a, b, c, d] 2 (by simp)
  have h6 : Keccak.rateCell [a, b, c, d] 6 = (Keccak.scalarCells d.1 d.2).1 :=
    rateCell_fst [a, b, c, d] 3 (by simp)
  have h7 : Keccak.rateCell [a, b, c, d] 7 = (Keccak.scalarCells d.1 d.2).2 :=
    rateCell_snd [a, b, c, d] 3 (by simp)
  simp only [rateOf, range8, List.map_cons, List.map_nil, h0, h1, h2, h3, h4, h5, h6, h7]

/-! ## A squeeze -/

/-- **A squeeze as atoms**: a `KECCAK` atom in the even layouts on the rate cells of the waiting
scalars and the capacity, then `challenge_from_state` on its output `0` into the value `b`: the
challenge is `s.squeeze`'s, and the outputs `8..12` its capacity. -/
theorem squeeze_atom {ins outs : List V} {b : ℕ} {s : Fs}
    (hk : (Atom.keccak ins outs false false).Holds rd σ) (hin : ins.map σ = rateOf s.pend ++ s.cap)
    (hch : ChallengeOk σ (outs.getD 0 default) b)
    (ho : outs.length = 13 := by first | rfl | simp) :
    σ (.n b) = s.squeeze.1 ∧ (outs.drop 8).map σ = s.squeeze.2.cap := by
  obtain ⟨-, -, hout⟩ := keccak_outs hk ho
  rw [hin] at hout
  refine ⟨challengeT_value hch (hout 0 (by omega)), ?_⟩
  apply List.ext_getElem
  · simp [ho, Fs.squeeze, capOf]
  · intro i h1 h2
    simp only [List.length_map, List.length_drop, ho] at h1
    simp only [List.getElem_map, List.getElem_drop]
    have e := hout (8 + i) (by omega)
    rw [List.getD_eq_getElem _ _ (by omega)] at e
    rw [e]
    simp only [Fs.squeeze, Fs.perm]
    interval_cases i <;> rfl

/-! ## Words -/

theorem word_gen_sq : word 4 0 = gen ^ 2 := by
  rw [show (4 : ℕ) = 2 ^ 2 from rfl]; exact word_two_pow (by decide)

/-! ## Records and runs -/

/-- Five capacity cells `16` words apart. -/
theorem capAt_five {rec : E} {k : ℕ} {c0 c1 c2 c3 c4 : E} (h0 : LoadHolds rd rec k c0)
    (h1 : LoadHolds rd rec (k + 16) c1) (h2 : LoadHolds rd rec (k + 32) c2)
    (h3 : LoadHolds rd rec (k + 48) c3) (h4 : LoadHolds rd rec (k + 64) c4) :
    CapAt rd rec k krCap [c0, c1, c2, c3, c4] := by
  refine ⟨rfl, fun j hj => ?_⟩
  simp only [List.length_cons, List.length_nil] at hj
  interval_cases j
  · simpa [krCap] using h0
  · simpa [krCap] using h1
  · simpa [krCap] using h2
  · simpa [krCap] using h3
  · simpa [krCap] using h4

/-- Words read at `p·g^a` are words read at `p` from offset `a`. -/
theorem readsAt_gen_pow_mul {p : E} {a : ℕ} {xs : List E} :
    ReadsAt rd (p * gen ^ a) xs ↔ ∀ k (hk : k < xs.length), LoadHolds rd p (a + k) xs[k] := by
  simp only [ReadsAt, loadHolds_mul_gen_pow]

/-- Two runs of words, one after the other. -/
theorem readsAt_append {p : E} {xs ys : List E} :
    ReadsAt rd p (xs ++ ys) ↔ ReadsAt rd p xs ∧ ReadsAt rd (p * gen ^ xs.length) ys := by
  rw [readsAt_gen_pow_mul]
  constructor
  · intro h
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · have := h k (by simp; omega)
      rwa [List.getElem_append_left hk] at this
    · have := h (xs.length + k) (by simp; omega)
      rw [List.getElem_append_right (by omega)] at this
      simpa using this
  · rintro ⟨hx, hy⟩ k hk
    by_cases h : k < xs.length
    · rw [List.getElem_append_left h]; exact hx k h
    · rw [List.getElem_append_right (by omega)]
      have := hy (k - xs.length) (by simp at hk; omega)
      rwa [show xs.length + (k - xs.length) = k by omega] at this

theorem readsAt_two {p a b : E} (ha : LoadHolds rd p 0 a) (hb : LoadHolds rd p 1 b) :
    ReadsAt rd p [a, b] := by
  intro k hk
  simp only [List.length_cons, List.length_nil] at hk
  interval_cases k
  · exact ha
  · exact hb

/-! ## Statement lists without `ret` -/

theorem noRetList_append : ∀ (a b : List Stmt),
    Stmt.noRetList (a ++ b) = (Stmt.noRetList a && Stmt.noRetList b)
  | [], b => by simp [Stmt.noRetList]
  | s :: a, b => by
    simp only [List.cons_append, Stmt.noRetList, noRetList_append a b, Bool.and_assoc]

theorem noRetList_flatten_map (f : ℕ → List Stmt) (h : ∀ i, Stmt.noRetList (f i) = true) :
    ∀ l : List ℕ, Stmt.noRetList (l.map f).flatten = true
  | [] => rfl
  | i :: l => by
    rw [List.map_cons, List.flatten_cons, noRetList_append, h i, noRetList_flatten_map f h l]; rfl

/-! ## Facts by position

A body's statements without `ret`, `pre`, hold one by one: the statement at position `k`, found
by kernel evaluation (`stmtEqb`), holds. `body_pre` splits a body into its statements and its
final `ret`. -/

/-! ## Blocks of atoms, by kernel evaluation -/

/-- An atom statement. -/
def isAtom : Stmt → Bool
  | .atom _ => true
  | _ => false

theorem allAtoms_of_all {ss : List Stmt} (h : ss.all isAtom = true) : AllAtoms ss := by
  intro s hs
  have := List.all_eq_true.1 h s hs
  cases s <;> simp_all [isAtom]

/-- **An atom of a block of atoms holds**, found by kernel evaluation. -/
theorem atom_of_block {ss : List Stmt} (hall : ss.all isAtom = true) {next : Prop}
    {kret : List E → Prop} (hb : Stmt.HoldsList C rd σ ss next kret) (a : Atom)
    (hm : ss.any (fun s ↦ stmtEqb s (.atom a)) = true) : a.Holds rd σ := by
  obtain ⟨hall', -⟩ := (holdsList_atoms (allAtoms_of_all hall) next kret).1 hb
  obtain ⟨s, hs, he⟩ := List.any_eq_true.1 hm
  rw [stmtEqb_sound he] at hs
  exact hall' a hs

/-! ## Loops -/

/-- **A `mul_range` loop, soundness**: if the helper's relation at depth `d + 1` at `x` gives the
body's meaning `B x` and, when `x·g ≠ N`, the call at `x·g` one level shallower, then from `g^k`
to `N = g^m` (`m` below the order of `g`) the body holds at every `g^j`, `k ≤ j < m`. -/
theorem loop_sound {P : Core.Program} {f : String} {ps : List E} {N : E} {B : E → Prop} {m : ℕ}
    (hstep : ∀ d x, P.relN rd (d + 1) f (x :: ps) [] →
      B x ∧ (x * gen + N ≠ 0 → P.relN rd d f (x * gen :: ps) []))
    (hN : N = gen ^ m) (hm : m < ordG) :
    ∀ k, P.Rel rd f (gen ^ k :: ps) [] → ∀ j, k ≤ j → j < m → B (gen ^ j) := by
  rintro k ⟨d, hd⟩
  induction d generalizing k with
  | zero => exact hd.elim
  | succ d ih =>
    obtain ⟨hB, hnext⟩ := hstep d _ hd
    intro j hkj hjm
    rcases Nat.eq_or_lt_of_le hkj with rfl | hlt
    · exact hB
    · have hne : gen ^ k * gen + N ≠ 0 := by
        intro h0
        rw [gen_pow_add_eq_zero_iff, hN] at h0
        have := gen_pow_inj hm (by unfold ordG at hm; omega) h0
        omega
      have := hnext hne
      rw [gen_pow_mul_gen] at this
      exact ih (k + 1) this j hlt hjm

/-! ## `fs_pack`'s cells -/

/-- **`fs_next`'s cells** (`fsNextT cur off b`): the cells `b + 1`, `b + 2` are the read word's
rate cells with the tag `DS_OBSERVE`. -/
theorem fsNext_scalar {b : ℕ} (h : FsPackOk σ (.n b) (b + 1) dsObserve) :
    (σ (.n (b + 1)), σ (.n (b + 2))) = Keccak.scalarCells (σ (.n b)) dsObserve :=
  fsPackT_cells h

end
end LeanVM.Guest.B1.VerifySub
