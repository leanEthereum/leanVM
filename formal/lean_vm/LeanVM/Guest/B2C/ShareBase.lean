/-
  LeanVM.Guest.B2C.ShareBase

  What the sharing check and its consumers share: bit sets, the keys of atoms and what they say,
  the certificate's lists of fixed cells, temporaries and frame runs, and the atoms of a body.
-/

module

public import LeanVM.Guest.B2C.CplCheck
public import LeanVM.Guest.B2C.KernelList

/-!
# The sharing check's base

Bit sets (`bitN`, `setBit`, `bitsOf`) and their facts; an atom's facts as keys (`KeyHolds`: a
sum, a product, a load, a `KECCAK` output cell, each a function of its inputs, `KeyHolds.unique`)
and their input cells (`keyCells`, `packCells`); the certificate's lists (`listsOk`: the fixed
cells, temporaries and frame runs in the frame, one value per cell; `listed`, `listedT`); the
cells kept apart (`apart`, `bitsNodup`, `siteCells`); paths that do not return
(`walk_noRet`) and the atoms of a body (`lAtoms`, `walk_atoms`, `tmpsList_atoms`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check

@[expose] public section

/-! ## Bit sets -/

/-- Bit `n` of `s`. -/
def bitN (s n : ℕ) : Bool := Nat.beq (Nat.mod (Nat.shiftRight s n) 2) 1

/-- `s` with bit `n` set. -/
def setBit (s n : ℕ) : ℕ := Nat.lor s (Nat.shiftLeft 1 n)

/-- The bit set of a list. -/
def bitsOf (l : List ℕ) : ℕ := l.foldl setBit 0

/-- The cells of a list packed, cell `m` in the `m`-th base-`2^16` digit. -/
def packCells : List ℕ → ℕ
  | [] => 0
  | c :: cs => Nat.add c (Nat.mul (packCells cs) 65536)

/-! ## Atoms -/

/-- The constant an atom gives value `v`. -/
noncomputable def constOf (a : Core.Atom) (v : ℕ) : Option (ℕ × ℕ) :=
  match a with
  | .const d x => bif Nat.beq d.idx v then some (limbNat x 0, limbNat x 1) else none
  | .assertNe _ _ p => bif Nat.beq p.idx v then some (1, 0) else none
  | _ => none

/-- The key of written cell `k` of a `KECCAK` in the layouts `inOdd`, `outOdd`: `4` to `55` for
`k < 13`. -/
def keccakOp (k : ℕ) (inOdd outOdd : Bool) : ℕ := 4 + 4 * k + 2 * inOdd.toNat + outOdd.toNat

/-- The keys an atom gives value `v` as an output: `0` a sum, `1` a product, `keccakOp k …` the
`k`-th written cell of a `KECCAK` (over its read cells), `off + 56` a load at offset `off`. -/
def keysOf (a : Core.Atom) (v : ℕ) : List (ℕ × List ℕ) :=
  match a with
  | .add d x y => (bif Nat.beq d.idx v then [(0, [x.idx, y.idx])] else []) ++
      (bif Nat.beq x.idx v then [(0, [d.idx, y.idx])] else []) ++
      (bif Nat.beq y.idx v then [(0, [d.idx, x.idx])] else [])
  | .mul d x y => bif Nat.beq d.idx v then [(1, [x.idx, y.idx])] else []
  | .keccak ins outs inOdd outOdd =>
    outs.zipIdx.filterMap fun q ↦
      bif Nat.beq q.1.idx v then some (keccakOp q.2 inOdd outOdd, ins.map V.idx) else none
  | .load d p off => bif Nat.beq d.idx v then [(off + 56, [p.idx])] else []
  | _ => []

/-- The values an atom says `v` equals. -/
def eqsOf (a : Core.Atom) (v : ℕ) : List ℕ :=
  match a with
  | .copy d x => (bif Nat.beq d.idx v then [x.idx] else []) ++ (bif Nat.beq x.idx v then [d.idx] else [])
  | .assertEq d x => (bif Nat.beq d.idx v then [x.idx] else []) ++ (bif Nat.beq x.idx v then [d.idx] else [])
  | _ => []

/-- A key's input cells, a sum's and a product's two in order. -/
def keyCells (op : ℕ) (cs : List ℕ) : List ℕ :=
  match op, cs with
  | 0, [a, b] => bif Nat.ble a b then [a, b] else [b, a]
  | 1, [a, b] => bif Nat.ble a b then [a, b] else [b, a]
  | _, cs => cs

/-! ## What the certificate lists -/

/-- The certificate lists a value with its cell. -/
noncomputable def listed (l : List (ℕ × ℕ)) (v : V) (c : ℕ) : Bool :=
  v == V.n v.idx && l.any fun p ↦ Nat.beq p.1 v.idx && Nat.beq p.2 c

/-- The certificate lists a temporary with its cell: `tt` is its temporaries by cell. -/
noncomputable def listedT (tt : Trie ℕ) (v : V) (c : ℕ) : Bool :=
  v == V.n v.idx && getF tt c == some v.idx

/-- The fixed cells' constants, by cell. -/
noncomputable def statCst (P : Plumb) : Trie (ℕ × ℕ) :=
  P.stat.foldl (fun t q ↦ match q.2 with
    | .k a b => setF (a, b) envDepth t q.1
    | .fpg _ => t) .nil

/-- The temporaries' cells. -/
noncomputable def tmpCells (P : Plumb) : ℕ := bitsOf (P.tmps.map Prod.snd)

/-- The fixed cells holding a frame pointer product. -/
noncomputable def fpgCells (P : Plumb) : ℕ :=
  bitsOf (P.stat.filterMap fun q ↦ match q.2 with
    | .fpg _ => some q.1
    | .k .. => none)

/-- The cells a list of `(value, cell)` pairs gives, by cell. -/
noncomputable def byCell (l : List (ℕ × ℕ)) : Trie ℕ := l.foldl (fun t p ↦ setF p.1 envDepth t p.2) .nil

/-- A list of `(value, cell)` pairs with one value per cell, the cells in `[2, n)`. -/
noncomputable def pairsOk (l : List (ℕ × ℕ)) (n : ℕ) : Bool :=
  (byCell l).seq fun t ↦ l.all fun p ↦ getF t p.2 == some p.1 && Nat.ble 2 p.2 && Nat.blt p.2 n

/-- The certificate's lists: the fixed cells as the walk starts with them, in the frame; the
temporaries' and runs' cells one value each, apart; the call sites' and table targets' cells in
the frame; no table selector a temporary. -/
noncomputable def listsOk (P : Plumb) (n : ℕ) : Bool :=
  (statCst P).seq fun cst ↦ natSeq (tmpCells P) fun tc ↦
  P.stat.all (fun q ↦ Nat.ble 2 q.1 && Nat.blt q.1 n && match q.2 with
    | .k a b => getF cst q.1 == some (a, b)
    | .fpg _ => true) &&
  pairsOk P.tmps n && pairsOk P.runs n && P.runs.all (fun p ↦ !bitN tc p.2) &&
  P.sites.all (fun s ↦ Nat.ble 2 s.q && Nat.blt s.q n) &&
  P.arms.all (fun a ↦ Nat.ble 2 a.2.1 && Nat.blt a.2.1 n && !(P.tmps.any fun p ↦ Nat.beq p.1 a.1))

/-- `s` has none of `t`'s bits. -/
def apart (s t : ℕ) : Bool := Nat.beq (Nat.land s t) 0

/-- No cell twice, `s` the cells seen. -/
def bitsNodup : List ℕ → ℕ → Bool
  | [], _ => true
  | c :: cs, s => !bitN s c && bitsNodup cs (setBit s c)

/-- The cells of the call sites: the callee frame pointers' and the fused dispatches' targets. -/
def siteCells (P : Plumb) : List ℕ := P.sites.flatMap fun s ↦ s.q :: (bif Nat.beq s.tgt 0 then [] else [s.tgt])

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

theorem keyCells_of_ge {op : ℕ} (h : 2 ≤ op) (cs : List ℕ) : keyCells op cs = cs := by
  obtain ⟨n, rfl⟩ : ∃ n, op = n + 2 := ⟨op - 2, by omega⟩
  simp [keyCells]

/-! ## Paths -/

section Paths

open LeanVM.Guest.Memory

variable {σ : Val}

theorem pick_noRet {x : V} {args rets : List V} : ∀ (fs : List String) (j : ℕ) {es : List Ev}
    {vs : List V}, pick σ x args rets j fs ≠ .ret es vs
  | [], _, _, _, h => by simp [pick] at h
  | f :: fs, j, _, _, h => by
      unfold pick at h
      split_ifs at h
      exact pick_noRet fs (j + 1) h

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
      exact pick_noRet fs 0 h
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

theorem evs_seq_sub {o1 o2 : Out} {e : Ev} (h : e ∈ (o1.seq o2).evs) : e ∈ o1.evs ∨ e ∈ o2.evs := by
  cases o1 <;> cases o2 <;> simp_all [Out.seq, Out.pre, Out.evs]

theorem evs_pre_sub {es : List Ev} {o : Out} {e : Ev} (h : e ∈ (o.pre es).evs) : e ∈ es ∨ e ∈ o.evs := by
  cases o <;> simp_all [Out.pre, Out.evs]

mutual
/-- **Every atom a path runs is an atom of the body.** -/
theorem walk1_atoms : ∀ (s : Stmt) {a : Core.Atom}, Ev.atom a ∈ (walk1 σ s).evs → a ∈ sAtoms s
  | .atom a', a, h => by simp [walk1, Out.evs] at h; simp [sAtoms, h]
  | .ite c z n, a, h => by
      simp only [walk1] at h
      rcases evs_pre_sub h with h | h
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
      rcases evs_seq_sub h with h | h
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

mutual
/-- **Every temporary is a range check's.** -/
theorem tmps_atoms : ∀ (s : Stmt) {t : V}, t ∈ Stmt.tmps s → ∃ a ∈ sAtoms s, t ∈ atomTmps a
  | .atom a, t, h => ⟨a, by simp [sAtoms], h⟩
  | .ite c z n, t, h => by
      simp only [Stmt.tmps, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨a, ha, ht⟩ := tmpsList_atoms z h; exact ⟨a, by simp [sAtoms, ha], ht⟩
      · obtain ⟨a, ha, ht⟩ := tmpsList_atoms n h; exact ⟨a, by simp [sAtoms, ha], ht⟩
  | .match_ x arms, t, h => by
      obtain ⟨a, ha, ht⟩ := tmpsArms_atoms arms h; exact ⟨a, by simpa [sAtoms] using ha, ht⟩
  | .call .., _, h => by simp [Stmt.tmps] at h
  | .callIf .., _, h => by simp [Stmt.tmps] at h
  | .dispatch .., _, h => by simp [Stmt.tmps] at h
  | .ret _, _, h => by simp [Stmt.tmps] at h

theorem tmpsList_atoms : ∀ (ss : List Stmt) {t : V}, t ∈ Stmt.tmpsList ss → ∃ a ∈ lAtoms ss, t ∈ atomTmps a
  | [], _, h => by simp [Stmt.tmpsList] at h
  | s :: ss, t, h => by
      simp only [Stmt.tmpsList, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨a, ha, ht⟩ := tmps_atoms s h; exact ⟨a, by simp [lAtoms, ha], ht⟩
      · obtain ⟨a, ha, ht⟩ := tmpsList_atoms ss h; exact ⟨a, by simp [lAtoms, ha], ht⟩

theorem tmpsArms_atoms : ∀ (arms : List (List Stmt)) {t : V}, t ∈ Stmt.tmpsArms arms →
    ∃ a ∈ aAtoms arms, t ∈ atomTmps a
  | [], _, h => by simp [Stmt.tmpsArms] at h
  | b :: as, t, h => by
      simp only [Stmt.tmpsArms, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨a, ha, ht⟩ := tmpsList_atoms b h; exact ⟨a, by simp [aAtoms, ha], ht⟩
      · obtain ⟨a, ha, ht⟩ := tmpsArms_atoms as h; exact ⟨a, by simp [aAtoms, ha], ht⟩
end
end Atoms2

section Chain

open LeanVM.Guest.Memory

variable {σ : Val}

theorem out_seq_assoc_sh : ∀ (o k l : Out), (o.seq k).seq l = o.seq (k.seq l)
  | .fall es, .fall es', l => by cases l <;> simp [Out.seq, Out.pre, List.append_assoc]
  | .fall es, .ret es' vs, l => by simp [Out.seq, Out.pre]
  | .fall es, .stuck, l => by simp [Out.seq, Out.pre]
  | .ret es vs, k, l => by simp [Out.seq]
  | .stuck, k, l => by simp [Out.seq]

theorem walk_append_sh : ∀ (l l' : List Stmt), walk σ (l ++ l') = (walk σ l).seq (walk σ l')
  | [], l' => by
      rw [List.nil_append, walk]
      cases walk σ l' <;> simp [Out.seq, Out.pre]
  | s :: l, l' => by rw [List.cons_append, walk, walk, walk_append_sh l l', out_seq_assoc_sh]

end Chain

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
