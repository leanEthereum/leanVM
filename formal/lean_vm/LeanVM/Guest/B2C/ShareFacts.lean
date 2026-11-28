/-
  LeanVM.Guest.B2C.ShareFacts

  The facts of the sharing check's definitions: bit sets, keys and what they say, paths that do
  not return, the atoms of a body.
-/

module

public import LeanVM.Guest.B2C.ShareDefs
public import LeanVM.Guest.Local.Pos

/-!
# The sharing check's facts

Bit sets' facts (`bitN_eq`, `testBit_bitsOf`, `bitsNodup_spec`, `apart_spec`); an atom's facts as
keys (`KeyHolds`: a sum, a product, a load, a `KECCAK` output cell, each a function of its inputs,
`KeyHolds.unique`); paths that do not return (`walk_noRet`) and the atoms of a body (`lAtoms`,
`walk_atoms`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check

@[expose] public section

/-! ## Bit sets -/

@[simp] theorem nbeq_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h ↦ h ▸ Nat.beq_refl a⟩

theorem bitN_eq (s n : ℕ) : bitN s n = s.testBit n := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  show Nat.beq ((s >>> n) % 2) 1 = _
  rw [Nat.shiftRight_eq_div_pow]
  cases h : Nat.beq (s / 2 ^ n % 2) 1
  · simp only [Bool.false_eq, decide_eq_false_iff_not]
    exact fun h' ↦ by rw [nbeq_iff.mpr h'] at h; cases h
  · exact (decide_eq_true (nbeq_iff.mp h)).symm

theorem testBit_setBit (s n m : ℕ) : (setBit s n).testBit m = (s.testBit m || decide (n = m)) := by
  show (s ||| 1 <<< n).testBit m = _
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem testBit_foldl_setBit {α : Type} (g : α → ℕ) : ∀ (l : List α) (s n : ℕ),
    (l.foldl (fun s x ↦ setBit s (g x)) s).testBit n = true ↔ s.testBit n = true ∨ ∃ x ∈ l, g x = n
  | [], s, n => by simp
  | x :: l, s, n => by
    rw [List.foldl_cons, testBit_foldl_setBit g l, testBit_setBit]
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, exists_eq_or_imp]
    tauto

theorem testBit_bitsOf (l : List ℕ) (n : ℕ) : (bitsOf l).testBit n = true ↔ n ∈ l := by
  have := testBit_foldl_setBit id l 0 n
  simp only [id, Nat.zero_testBit, Bool.false_eq_true, false_or, exists_eq_right] at this
  exact this

theorem testBit_lor' (x y i : ℕ) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) :=
  Nat.testBit_or x y i

theorem testBit_land' (x y i : ℕ) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) :=
  Nat.testBit_and x y i


/-! ## Keys -/

/-- **What a key says** of an output word and its inputs' words: a sum (`0`), a product (`1`), a
load at offset `op - 56`, or written cell `k` of a `KECCAK` in the layouts `inOdd`, `outOdd`
(`keccakOp k inOdd outOdd`) of its thirteen read cells. -/
def KeyHolds (rd : Reader) (out : E) (op : ℕ) (ins : List E) : Prop :=
  (op = 0 ∧ ∃ a b, ins = [a, b] ∧ out = a + b) ∨
  (op = 1 ∧ ∃ a b, ins = [a, b] ∧ out = a * b) ∨
  (56 ≤ op ∧ ∃ p, ins = [p] ∧ LoadHolds rd p (op - 56) out) ∨
  (∃ (k : Fin 13) (inOdd outOdd : Bool), op = keccakOp k inOdd outOdd ∧
    ∃ output : Fin 13 → E, KeccakCellsRelation (cells13 ins) inOdd output outOdd .all ∧ output k = out)

theorem keccakOp_lt (k : Fin 13) (inOdd outOdd : Bool) : 4 ≤ keccakOp k inOdd outOdd ∧
    keccakOp k inOdd outOdd < 56 := by
  have := k.isLt
  unfold keccakOp
  cases inOdd <;> cases outOdd <;> simp <;> omega

theorem keccakOp_inj {k k' : Fin 13} {a b a' b' : Bool}
    (h : keccakOp k a b = keccakOp k' a' b') : k = k' ∧ a = a' ∧ b = b' := by
  unfold keccakOp at h
  cases a <;> cases b <;> cases a' <;> cases b' <;> simp at h <;>
    first | exact ⟨Fin.ext (by omega), rfl, rfl⟩ | omega

theorem keyHolds_add {rd : Reader} {out a b : E} : KeyHolds rd out 0 [a, b] ↔ out = a + b := by
  unfold KeyHolds
  constructor
  · rintro (⟨-, a', b', h, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨k, i, o, h, -⟩)
    · simp only [List.cons.injEq, and_true] at h; rw [h.1, h.2]
    · cases h
    · omega
    · have := keccakOp_lt k i o; omega
  · exact fun h ↦ .inl ⟨rfl, a, b, rfl, h⟩

theorem keyHolds_mul {rd : Reader} {out a b : E} : KeyHolds rd out 1 [a, b] ↔ out = a * b := by
  unfold KeyHolds
  constructor
  · rintro (⟨h, -⟩ | ⟨-, a', b', h, rfl⟩ | ⟨h, -⟩ | ⟨k, i, o, h, -⟩)
    · cases h
    · simp only [List.cons.injEq, and_true] at h; rw [h.1, h.2]
    · omega
    · have := keccakOp_lt k i o; omega
  · exact fun h ↦ .inr (.inl ⟨rfl, a, b, rfl, h⟩)

theorem keyHolds_load {rd : Reader} {out p : E} {off : ℕ} :
    KeyHolds rd out (off + 56) [p] ↔ LoadHolds rd p off out := by
  unfold KeyHolds
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨-, p', h, hl⟩ | ⟨k, i, o, h, -⟩)
    · omega
    · omega
    · simp only [List.cons.injEq, and_true] at h
      rw [h, Nat.add_sub_cancel] at *
      exact hl
    · have := keccakOp_lt k i o; omega
  · exact fun h ↦ .inr (.inr (.inl ⟨by omega, p, rfl, by rwa [Nat.add_sub_cancel]⟩))

theorem keyHolds_keccak {rd : Reader} {out : E} {ins : List E} {k : Fin 13} {inOdd outOdd : Bool}
    (output : Fin 13 → E) (h : KeccakCellsRelation (cells13 ins) inOdd output outOdd .all)
    (ho : output k = out) :
    KeyHolds rd out (keccakOp k inOdd outOdd) ins :=
  .inr (.inr (.inr ⟨k, inOdd, outOdd, rfl, output, h, ho⟩))

/-- `KECCAK`'s written cells are a function of the cells it reads. -/
theorem keccakCells_output {input output output' : Fin 13 → E} {inOdd outOdd : Bool}
    (h : KeccakCellsRelation input inOdd output outOdd .all)
    (h' : KeccakCellsRelation input inOdd output' outOdd .all) :
    output = output' := funext fun c ↦ (h c c.isLt).trans (h' c c.isLt).symm

/-- **A key's output is a function of its inputs.** -/
theorem KeyHolds.unique {rd : Reader} {x y : E} {op : ℕ} {ins : List E}
    (hx : KeyHolds rd x op ins) (hy : KeyHolds rd y op ins) : x = y := by
  rcases hx with ⟨rfl, a, b, rfl, rfl⟩ | ⟨rfl, a, b, rfl, rfl⟩ | ⟨hop, p, rfl, hl⟩ |
      ⟨k, i, o, rfl, out, hk, rfl⟩
  · rcases hy with ⟨-, a', b', h, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨k, i, o, h, -⟩
    · simp only [List.cons.injEq, and_true] at h; rw [h.1, h.2]
    · cases h
    · omega
    · have := keccakOp_lt k i o; omega
  · rcases hy with ⟨h, -⟩ | ⟨-, a', b', h, rfl⟩ | ⟨h, -⟩ | ⟨k, i, o, h, -⟩
    · cases h
    · simp only [List.cons.injEq, and_true] at h; rw [h.1, h.2]
    · omega
    · have := keccakOp_lt k i o; omega
  · rcases hy with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, p', h, hl'⟩ | ⟨k, i, o, h, -⟩
    · omega
    · omega
    · simp only [List.cons.injEq, and_true] at h
      subst h
      exact Option.some.inj (hl.2.symm.trans hl'.2)
    · have := keccakOp_lt k i o; omega
  · have := keccakOp_lt k i o
    rcases hy with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨k', i', o', h, out', hk', rfl⟩
    · omega
    · omega
    · omega
    · obtain ⟨rfl, rfl, rfl⟩ := keccakOp_inj h
      rw [keccakCells_output hk hk']

/-- A sum's and a product's inputs in either order. -/
theorem keyHolds_keyCells {rd : Reader} {x : E} {Ψ : ℕ → E} (op : ℕ) (cs : List ℕ) :
    KeyHolds rd x op ((keyCells op cs).map Ψ) ↔ KeyHolds rd x op (cs.map Ψ) := by
  match op, cs with
  | 0, [a, b] =>
    simp only [keyCells]
    cases Nat.ble a b <;> simp [keyHolds_add, add_comm]
  | 1, [a, b] =>
    simp only [keyCells]
    cases Nat.ble a b <;> simp [keyHolds_mul, mul_comm]
  | 0, [] => simp [keyCells]
  | 0, [_] => simp [keyCells]
  | 0, _ :: _ :: _ :: _ => simp [keyCells]
  | 1, [] => simp [keyCells]
  | 1, [_] => simp [keyCells]
  | 1, _ :: _ :: _ :: _ => simp [keyCells]
  | n + 2, cs => simp [keyCells]


theorem mem_keyCells {c op : ℕ} {cs : List ℕ} : c ∈ keyCells op cs ↔ c ∈ cs := by
  match op, cs with
  | 0, [a, b] => simp only [keyCells]; cases Nat.ble a b <;> simp [or_comm]
  | 1, [a, b] => simp only [keyCells]; cases Nat.ble a b <;> simp [or_comm]
  | 0, [] => simp [keyCells]
  | 0, [_] => simp [keyCells]
  | 0, _ :: _ :: _ :: _ => simp [keyCells]
  | 1, [] => simp [keyCells]
  | 1, [_] => simp [keyCells]
  | 1, _ :: _ :: _ :: _ => simp [keyCells]
  | n + 2, cs => simp [keyCells]

/-! ## Paths -/

section Paths

open LeanVM.Guest.Memory

variable {σ : Val}

mutual
theorem walk1_noRet : ∀ (s : Stmt), Stmt.noRet s = true → ∀ es vs, walk1 σ s ≠ .ret es vs
  | .atom _, _, _, _, h => by simp [walk1] at h
  | .ite c z n, hn, es, vs, h => by
      simp only [Stmt.noRet, Bool.and_eq_true] at hn
      rw [walk1] at h
      split_ifs at h
      · cases hz : walk σ z <;> rw [hz] at h <;> simp only [Out.pre, reduceCtorEq] at h
        exact walk_noRet z hn.1 _ _ hz
      · cases hz : walk σ n <;> rw [hz] at h <;> simp only [Out.pre, reduceCtorEq] at h
        exact walk_noRet n hn.2 _ _ hz
  | .match_ x arms, hn, es, vs, h => by
      simp only [Stmt.noRet] at hn
      rw [walk1] at h
      exact walkArms_noRet x arms hn 0 es vs h
  | .call .., _, _, _, h => by simp [walk1] at h
  | .callIf .., _, _, _, h => by simp [walk1] at h
  | .dispatch x fs args rets, _, es, vs, h => by
      rw [walk1] at h
      exact Local.pick_ret fs 0 h
  | .ret _, hn, _, _, _ => by simp [Stmt.noRet] at hn

theorem walk_noRet : ∀ (ss : List Stmt), Stmt.noRetList ss = true → ∀ es vs, walk σ ss ≠ .ret es vs
  | [], _, _, _, h => by simp [walk] at h
  | s :: ss, hn, es, vs, h => by
      simp only [Stmt.noRetList, Bool.and_eq_true] at hn
      rw [walk] at h
      cases h1 : walk1 σ s with
      | fall es1 =>
        rw [h1] at h
        cases h2 : walk σ ss <;> rw [h2] at h <;> simp only [Out.seq, Out.pre, reduceCtorEq] at h
        exact walk_noRet ss hn.2 _ _ h2
      | ret es1 vs1 => exact walk1_noRet s hn.1 es1 vs1 h1
      | stuck => rw [h1] at h; simp [Out.seq] at h

theorem walkArms_noRet (x : V) : ∀ (arms : List (List Stmt)), Stmt.noRetArms arms = true →
    ∀ (j : ℕ) es vs, walkArms σ x j arms ≠ .ret es vs
  | [], _, _, _, _, h => by simp [walkArms] at h
  | a :: as, hn, j, es, vs, h => by
      simp only [Stmt.noRetArms, Bool.and_eq_true] at hn
      unfold walkArms at h
      split_ifs at h
      · exact walk_noRet a hn.1 _ _ h
      · exact walkArms_noRet x as hn.2 (j + 1) _ _ h
end

end Paths

/-! ## Atoms of a body -/

mutual
/-- The atoms of a statement, at any depth. -/
def sAtoms : Stmt → List Core.Atom
  | .atom a => [a]
  | .ite _ z n => lAtoms z ++ lAtoms n
  | .match_ _ arms => aAtoms arms
  | _ => []

/-- The atoms of a block. -/
def lAtoms : List Stmt → List Core.Atom
  | [] => []
  | s :: ss => sAtoms s ++ lAtoms ss

/-- The atoms of arms. -/
def aAtoms : List (List Stmt) → List Core.Atom
  | [] => []
  | a :: as => lAtoms a ++ aAtoms as
end

section Atoms2

open LeanVM.Guest.Memory

variable {σ : Val}

theorem pick_atoms {x : V} {args rets : List V} : ∀ (fs : List String) (j : ℕ) {a : Core.Atom},
    Ev.atom a ∉ (pick σ x args rets j fs).evs
  | [], _, _, h => by simp [pick, Out.evs] at h
  | f :: fs, j, a, h => by
      unfold pick at h
      split_ifs at h
      · simp [Out.evs] at h
      · exact pick_atoms fs (j + 1) h

mutual
/-- **Every atom a path runs is an atom of the body.** -/
theorem walk1_atoms : ∀ (s : Stmt) {a : Core.Atom}, Ev.atom a ∈ (walk1 σ s).evs → a ∈ sAtoms s
  | .atom a', a, h => by simp [walk1, Out.evs] at h; simp [sAtoms, h]
  | .ite c z n, a, h => by
      simp only [walk1] at h
      rcases Local.evs_pre h with h | h
      · simp at h
      · simp only [sAtoms, List.mem_append]
        split_ifs at h
        · exact Or.inl (walk_atoms z h)
        · exact Or.inr (walk_atoms n h)
  | .match_ x arms, a, h => by simp only [walk1] at h; exact walkArms_atoms x arms 0 h
  | .call .., a, h => by simp [walk1, Out.evs] at h
  | .callIf .., a, h => by simp only [walk1, Out.evs] at h; split_ifs at h <;> simp at h
  | .dispatch x fs args rets, a, h => by simp only [walk1] at h; exact absurd h (pick_atoms fs 0)
  | .ret _, a, h => by simp [walk1, Out.evs] at h

theorem walk_atoms : ∀ (ss : List Stmt) {a : Core.Atom}, Ev.atom a ∈ (walk σ ss).evs → a ∈ lAtoms ss
  | [], a, h => by simp [walk, Out.evs] at h
  | s :: ss, a, h => by
      simp only [walk] at h
      simp only [lAtoms, List.mem_append]
      rcases (Local.evs_seq h).imp_right And.right with h | h
      · exact Or.inl (walk1_atoms s h)
      · exact Or.inr (walk_atoms ss h)

theorem walkArms_atoms (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) {a : Core.Atom},
    Ev.atom a ∈ (walkArms σ x j arms).evs → a ∈ aAtoms arms
  | [], _, a, h => by simp [walkArms, Out.evs] at h
  | b :: as, j, a, h => by
      unfold walkArms at h
      simp only [aAtoms, List.mem_append]
      split_ifs at h
      · exact Or.inl (walk_atoms b h)
      · exact Or.inr (walkArms_atoms x as (j + 1) h)
end

end Atoms2

/-! ## Bit sets apart -/

section Bits

theorem bitsNodup_spec : ∀ (l : List ℕ) (s : ℕ), bitsNodup l s = true → l.Nodup ∧ ∀ c ∈ l, s.testBit c = false
  | [], _, _ => ⟨List.nodup_nil, fun _ h ↦ absurd h List.not_mem_nil⟩
  | c :: cs, s, h => by
    simp only [bitsNodup, Bool.and_eq_true, Bool.not_eq_true', bitN_eq] at h
    obtain ⟨h1, h2⟩ := bitsNodup_spec cs _ h.2
    refine ⟨List.nodup_cons.mpr ⟨fun hc ↦ ?_, h1⟩, fun c' hc' ↦ ?_⟩
    · have := h2 c hc
      rw [testBit_setBit] at this
      simp at this
    · rcases List.mem_cons.mp hc' with rfl | hc'
      · exact h.1
      · have := h2 c' hc'
        rw [testBit_setBit, Bool.or_eq_false_iff] at this
        exact this.1

theorem apart_spec {s t c : ℕ} (h : apart s t = true) (hs : s.testBit c = true) : t.testBit c = false := by
  simp only [apart, nbeq_iff] at h
  have := congrArg (fun x ↦ x.testBit c) h
  simp only [testBit_land', hs, Bool.true_and, Nat.zero_testBit] at this
  exact this

theorem lt_of_testBit_lt {x c n : ℕ} (hx : x < 2 ^ n) (h : x.testBit c = true) : c < n := by
  by_contra hc
  have : x < 2 ^ c := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [Nat.testBit_lt_two_pow this] at h
  cases h

theorem mem_bitsOf {l : List ℕ} {c : ℕ} (h : c ∈ l) : (bitsOf l).testBit c = true := (testBit_bitsOf l c).mpr h

theorem testBit_lor_l {x y c : ℕ} (h : x.testBit c = true) : (Nat.lor x y).testBit c = true := by
  rw [testBit_lor', h, Bool.true_or]

theorem testBit_lor_r {x y c : ℕ} (h : y.testBit c = true) : (Nat.lor x y).testBit c = true := by
  rw [testBit_lor', h, Bool.or_true]

theorem land_beq_iff (x y : ℕ) : Nat.beq (Nat.land x y) x = true ↔ ∀ i, x.testBit i → y.testBit i := by
  rw [Nat.beq_eq]
  constructor
  · intro h i hi
    rw [← h, testBit_land'] at hi
    simp only [Bool.and_eq_true] at hi
    exact hi.2
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [testBit_land']
    cases hx : x.testBit i
    · simp
    · simp [h i hx]

end Bits

end
end LeanVM.Guest.B2C
