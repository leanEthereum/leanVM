module

public import LeanVMCircuits.Blake2s.Compress
public import LeanVMCircuits.Gates

@[expose] public section

/-!
What the BLAKE2s Clean circuit lowers to, in closed form.
-/

namespace LeanVMCircuits.Blake2s

open LeanVMCircuits Gates Flock Rfc7693

/-- The carry into bit `i` of a ripple adder whose products start at `n`: the sum of the products below. -/
def carryAffine (n : ℕ) (carry : Affine) : ℕ → Affine
  | 0 => carry
  | i + 1 => .xor (.var (n + i)) (carryAffine n carry i)

def adderSteps (n k : ℕ) (x y : ℕ → Affine) (carry : Affine) : List Step :=
  (List.range k).map fun i =>
    .product (n + i) (.xor (x i) (carryAffine n carry i)) (.xor (y i) (carryAffine n carry i))

def sumAffine (n : ℕ) (x y : ℕ → Affine) (carry : Affine) (i : ℕ) : Affine :=
  .xor (.xor (x i) (carryAffine n carry i)) (y i)

theorem fullAdder_flat (n : ℕ) (input : Var FullAdder.Input Bit) :
    Operations.toFlat (FullAdder.main input n).2 =
      [.witness 1 (.ofFExpr (.expr ((input.x + input.carry) * (input.y + input.carry)))),
        .assert (var ⟨n⟩ - (input.x + input.carry) * (input.y + input.carry))] := by
  simp only [FullAdder.main, circuit_norm]

theorem lower_product (m : ℕ) (w : WitgenIR Bit 1) (a b : Expression Bit) (la lb : Affine)
    (ha : lowerAffine a = .ok la) (hb : lowerAffine b = .ok lb) (ba : la.bounded m) (bb : lb.bounded m) :
    Gates.lower m [.witness 1 w, .assert (var ⟨m⟩ - a * b)] = .ok [.product m la lb] := by
  show Gates.lower m [_, .assert (.add (var ⟨m⟩) (.mul (.const (-1)) (.mul a b)))] = _
  simp [Gates.lower, ha, hb, ba, bb]

theorem lower_define (m : ℕ) (w : WitgenIR Bit 1) (e : Expression Bit) (la : Affine)
    (he : lowerAffine e = .ok la) (ba : la.bounded m) :
    Gates.lower m [.witness 1 w, .assert (var ⟨m⟩ - e)] = .ok [.define m la] := by
  show Gates.lower m [_, .assert (.add (var ⟨m⟩) (.mul (.const (-1)) e))] = _
  cases e with
  | mul a b => simp [lowerAffine] at he
  | _ => simp_all [Gates.lower]

theorem Affine.bounded_mono (a : Affine) {m m' : ℕ} (h : a.bounded m) (hm : m ≤ m') : a.bounded m' := by
  induction a with
  | zero | one => rfl
  | var i => simp [Affine.bounded] at h ⊢; omega
  | xor l r il ir => simp only [Affine.bounded, Bool.and_eq_true] at h ⊢; exact ⟨il h.1, ir h.2⟩

theorem carryAffine_bounded (n : ℕ) (c : Affine) (hc : c.bounded n) (i : ℕ) :
    (carryAffine n c i).bounded (n + i) := by
  induction i with
  | zero => simpa [carryAffine] using hc
  | succ i ih =>
    simp only [carryAffine, Affine.bounded, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by omega, Affine.bounded_mono _ ih (by omega)⟩

theorem toSubcircuit_toFlat {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : FormalCircuit Bit Input Output) (n : ℕ) (input : Var Input Bit) :
    (circuit.toSubcircuit n input).ops.toFlat = Operations.toFlat ((circuit.main input) n).2 := by
  simp [FormalCircuit.toSubcircuit, Operations.toNested_toFlat]

theorem adder_lower (k n : ℕ) (x y : Vector (Expression Bit) k) (c : Expression Bit) (ax ay : ℕ → Affine)
    (ac : Affine) (hx : ∀ i (h : i < k), lowerAffine x[i] = .ok (ax i))
    (hy : ∀ i (h : i < k), lowerAffine y[i] = .ok (ay i)) (hc : lowerAffine c = .ok ac)
    (bx : ∀ i, i < k → (ax i).bounded n) (bY : ∀ i, i < k → (ay i).bounded n) (bc : ac.bounded n) :
    Gates.lower n (Operations.toFlat ((Adder.certified k).circuit.main { x, y, carry := c } n).2) =
        .ok (adderSteps n k ax ay ac) ∧
      (∀ i (h : i < k), lowerAffine ((Adder.certified k).circuit.output { x, y, carry := c } n).sum[i] =
        .ok (sumAffine n ax ay ac i)) ∧
      lowerAffine ((Adder.certified k).circuit.output { x, y, carry := c } n).carry = .ok (carryAffine n ac k) := by
  induction k with
  | zero =>
    refine ⟨rfl, fun i h => absurd h (by omega), ?_⟩
    simpa [Adder.certified, Adder.zero, circuit_norm, carryAffine] using hc
  | succ k ih =>
    obtain ⟨hl, hs, hcar⟩ := ih x.pop y.pop (fun i h => by simpa using hx i (by omega))
      (fun i h => by simpa using hy i (by omega)) (fun i h => bx i (by omega)) (fun i h => bY i (by omega))
    have hlen : (Adder.certified k).circuit.localLength { x := x.pop, y := y.pop, carry := c } = k :=
      (Adder.certified k).length_eq _
    have hout : (Adder.certified k).circuit.elaborated.output { x := x.pop, y := y.pop, carry := c } n =
        (Adder.certified k).circuit.output { x := x.pop, y := y.pop, carry := c } n := rfl
    simp only [Adder.certified, Adder.step, circuit_norm, FullAdder.circuit]
    rw [hout]
    have hxk : lowerAffine (x[k] + ((Adder.certified k).circuit.output { x := x.pop, y := y.pop, carry := c } n).carry)
        = .ok (.xor (ax k) (carryAffine n ac k)) := by
      show lowerAffine (.add _ _) = _
      simp [lowerAffine, hx k (by omega), hcar]
    have hyk : lowerAffine (y[k] + ((Adder.certified k).circuit.output { x := x.pop, y := y.pop, carry := c } n).carry)
        = .ok (.xor (ay k) (carryAffine n ac k)) := by
      show lowerAffine (.add _ _) = _
      simp [lowerAffine, hy k (by omega), hcar]
    have hbk := carryAffine_bounded n ac bc k
    refine ⟨?_, ?_, ?_⟩
    · rw [toSubcircuit_toFlat, toSubcircuit_toFlat, Gates.lower_append _ _ _ _ hl, hlen, fullAdder_flat]
      simp only [adderSteps, List.length_map, List.length_range, Nat.add_zero]
      rw [lower_product _ _ _ _ _ _ hxk hyk (by simp [Affine.bounded, Affine.bounded_mono _ (bx k (by omega))
        (Nat.le_add_right n k), hbk]) (by simp [Affine.bounded, Affine.bounded_mono _ (bY k (by omega))
        (Nat.le_add_right n k), hbk])]
      simp [Except.map, List.range_succ]
    · intro i hi
      split
      · rename_i h
        simpa using hs i h
      · have : i = k := by omega
        subst this
        show lowerAffine (.add (.add _ _) _) = _
        simp only [lowerAffine, hx i (by omega), hy i (by omega), hcar, sumAffine]
    · show lowerAffine (.add _ _) = _
      simp [lowerAffine, hcar, carryAffine]

theorem wrapping_lower (m n : ℕ) (x y : Vector (Expression Bit) (m + 1)) (ax ay : ℕ → Affine)
    (hx : ∀ i (h : i < m + 1), lowerAffine x[i] = .ok (ax i))
    (hy : ∀ i (h : i < m + 1), lowerAffine y[i] = .ok (ay i))
    (bx : ∀ i, i < m + 1 → (ax i).bounded n) (bY : ∀ i, i < m + 1 → (ay i).bounded n) :
    Gates.lower n (Operations.toFlat ((WrappingAdder.circuit m).main { x, y } n).2) =
        .ok (adderSteps n m ax ay .zero) ∧
      ∀ i (h : i < m + 1), lowerAffine ((WrappingAdder.circuit m).output { x, y } n)[i] =
        .ok (sumAffine n ax ay .zero i) := by
  obtain ⟨hl, hs, hcar⟩ := adder_lower m n x.pop y.pop 0 ax ay .zero
    (fun i h => by simpa using hx i (by omega)) (fun i h => by simpa using hy i (by omega)) rfl
    (fun i h => bx i (by omega)) (fun i h => bY i (by omega)) rfl
  refine ⟨?_, ?_⟩
  · simp only [WrappingAdder.circuit, WrappingAdder.main, circuit_norm]
    rw [toSubcircuit_toFlat]
    exact hl
  · intro i hi
    simp only [WrappingAdder.circuit, circuit_norm]
    split
    · rename_i h
      exact hs i h
    · have : i = m := by omega
      subst this
      show lowerAffine (.add (.add _ _) _) = _
      simp only [lowerAffine, hx i (by omega), hy i (by omega)]
      erw [hcar]
      rfl

def defines (n k : ℕ) (a : ℕ → Affine) : List Step := (List.range k).map fun i => .define (n + i) (a i)

theorem toFlat_append (a b : Operations Bit) : Operations.toFlat (a ++ b) = a.toFlat ++ b.toFlat := by
  induction a with
  | nil => rfl
  | cons op ops ih => cases op <;> simp [Operations.toFlat, ih]

theorem defines_succ (n k : ℕ) (a : ℕ → Affine) :
    defines n (k + 1) a = defines n k a ++ [.define (n + k) (a k)] := by
  simp [defines, List.range_succ]

theorem defineAll_lower (n k : ℕ) (g : Fin k → Expression Bit) (a : ℕ → Affine)
    (hg : ∀ i : Fin k, lowerAffine (g i) = .ok (a i.val)) (ba : ∀ i, i < k → (a i).bounded n) :
    Gates.lower n (Operations.toFlat (List.ofFn fun i : Fin k =>
      [Operation.witness 1 (Witgen.WitgenIR.ofFExpr (Witgen.FExpr.expr (g i))),
        Operation.assert (var ⟨n + i.val * 1⟩ - g i)]).flatten) = .ok (defines n k a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.ofFn_succ_last, List.flatten_append, toFlat_append]
    simp only [Fin.val_castSucc]
    rw [Gates.lower_append _ _ _ _ (ih (fun i => g i.castSucc) (fun i => hg i.castSucc) (fun i h => ba i (by omega)))]
    have hlen : (defines n k a).length = k := by simp [defines]
    rw [hlen, defines_succ]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, Operations.toFlat, Fin.val_last, Nat.mul_one]
    rw [lower_define _ _ _ _ (hg (Fin.last k)) (Affine.bounded_mono _ (ba k (by omega)) (by omega))]
    rfl

theorem define_output (e : Vector (Expression Bit) 32) (m i : ℕ) (hi : i < 32) :
    ((Define.main e) m).1[i] = var ⟨m + i⟩ := by
  simp [Define.main, defineBit, circuit_norm]

theorem define_lower (n : ℕ) (e : Vector (Expression Bit) 32) (a : ℕ → Affine)
    (he : ∀ i (h : i < 32), lowerAffine e[i] = .ok (a i)) (ba : ∀ i, i < 32 → (a i).bounded n) :
    Gates.lower n (Operations.toFlat ((Define.main e) n).2) = .ok (defines n 32 a) ∧
      ∀ i (h : i < 32), (Define.circuit.output e n)[i] = var ⟨n + i⟩ := by
  refine ⟨?_, ?_⟩
  · simp only [Define.main, Circuit.map.operations_eq, defineBit, circuit_norm]
    exact defineAll_lower n 32 (fun i => e[i.val]) a (fun i => he i.val i.isLt) ba
  · intro i h
    simp [Define.circuit, Define.main, defineBit, circuit_norm]

abbrev Affs := List (Vector Affine 32)

/-- Bit `i` of register `r`, a structural zero past the registers, as the lowering names it. -/
def affGet (affs : Affs) (r i : ℕ) : Affine :=
  if h : i < 32 then (affs.getD r (Vector.replicate 32 .zero))[i] else .zero

def literalAffine {w : ℕ} (k : BitVec w) (i : ℕ) : Affine := if k.getLsbD i then .one else .zero

/-- An operation's steps, at its first variable `n`, on the registers' affine bits. -/
def Op.steps (affs : Affs) (n : ℕ) : Op → List Step
  | .add x y =>
    adderSteps n 31 (affGet affs x) (affGet affs y) .zero ++
      defines (n + 31) 32 (sumAffine n (affGet affs x) (affGet affs y) .zero)
  | .addOdd k y =>
    adderSteps n 31 (literalAffine k) (affGet affs y) .zero ++
      defines (n + 31) 32 (sumAffine n (literalAffine k) (affGet affs y) .zero)
  | .addEven k y =>
    adderSteps n 30 (literalAffine (BitVec.ofNat 31 (k.toNat / 2))) (fun i => affGet affs y (i + 1)) .zero ++
      defines (n + 30) 32 fun i => if i = 0 then affGet affs y 0 else
        sumAffine n (literalAffine (BitVec.ofNat 31 (k.toNat / 2))) (fun i => affGet affs y (i + 1)) .zero (i - 1)
  | .xorRotr r x y =>
    defines n 32 fun i => .xor (affGet affs x ((i + r.val) % 32)) (affGet affs y ((i + r.val) % 32))

/-- The registers' bits lower to `affs`, every one naming only variables below `n`. -/
def Rel (registers : List Reg) (affs : Affs) (n : ℕ) : Prop :=
  registers.length = affs.length ∧
    ∀ r i (h : i < 32), lowerAffine (get registers r)[i] = .ok (affGet affs r i) ∧ (affGet affs r i).bounded n

theorem sumAffine_bounded (n m : ℕ) (x y : ℕ → Affine) (i : ℕ) (hi : i ≤ m) (hx : (x i).bounded n)
    (hy : (y i).bounded n) : (sumAffine n x y .zero i).bounded (n + m) := by
  simp only [sumAffine, Affine.bounded, Bool.and_eq_true]
  exact ⟨⟨Affine.bounded_mono _ hx (by omega),
    Affine.bounded_mono _ (carryAffine_bounded n .zero rfl i) (by omega)⟩, Affine.bounded_mono _ hy (by omega)⟩

theorem add_lower (registers : List Reg) (affs : Affs) (n x y : ℕ) (h : Rel registers affs n) :
    Gates.lower n (Operations.toFlat (((Op.add x y).circuit registers) n).2) = .ok ((Op.add x y).steps affs n) ∧
      ∀ i (hi : i < 32), (((Op.add x y).circuit registers).output n)[i] = var ⟨n + 31 + i⟩ := by
  have hlen : ∀ (input : Var (WrappingAdder.Input 32) Bit),
      (WrappingAdder.circuit 31).elaborated.localLength input = 31 :=
    WrappingAdder.circuit_length 31
  have hflat : Operations.toFlat (((Op.add x y).circuit registers) n).2 =
      Operations.toFlat ((WrappingAdder.circuit 31).main { x := get registers x, y := get registers y } n).2 ++
      Operations.toFlat ((Define.main ((WrappingAdder.circuit 31).output
        { x := get registers x, y := get registers y } n)) (n + 31)).2 := by
    simp only [Op.circuit, Add32.circuit, circuit_norm]
    rw [toSubcircuit_toFlat]
    simp only [Add32.main, circuit_norm]
    rw [toSubcircuit_toFlat, toSubcircuit_toFlat, show (WrappingAdder.circuit 31).localLength
      { x := get registers x, y := get registers y } = 31 from hlen _]
    rfl
  obtain ⟨_, hrel⟩ := h
  have hW := wrapping_lower 31 n (get registers x) (get registers y) (affGet affs x) (affGet affs y)
    (fun i hi => (hrel x i hi).1) (fun i hi => (hrel y i hi).1) (fun i hi => (hrel x i hi).2)
    (fun i hi => (hrel y i hi).2)
  have hD := define_lower (n + 31) ((WrappingAdder.circuit 31).output
      { x := get registers x, y := get registers y } n) (sumAffine n (affGet affs x) (affGet affs y) .zero)
    (fun i hi => hW.2 i hi)
    (fun i hi => sumAffine_bounded n 31 _ _ i (by omega) (hrel x i hi).2 (hrel y i hi).2)
  refine ⟨?_, ?_⟩
  · rw [hflat, Gates.lower_append _ _ _ _ hW.1]
    have : (adderSteps n 31 (affGet affs x) (affGet affs y) .zero).length = 31 := by simp [adderSteps]
    rw [this, hD.1]
    rfl
  · intro i hi
    simp only [Op.circuit, Add32.circuit, circuit_norm]
    rw [define_output]

theorem lower_literal {w : ℕ} (k : BitVec w) (i : ℕ) (hi : i < w) :
    lowerAffine (literal k : Vector (Expression Bit) w)[i] = .ok (literalAffine k i) := by
  simp only [literal, Vector.getElem_ofFn, literalAffine]
  split <;> rfl

theorem literalAffine_bounded {w : ℕ} (k : BitVec w) (i n : ℕ) : (literalAffine k i).bounded n := by
  unfold literalAffine; split <;> rfl

theorem addOdd_lower (registers : List Reg) (affs : Affs) (n : ℕ) (k : Word) (y : ℕ) (h : Rel registers affs n) :
    Gates.lower n (Operations.toFlat (((Op.addOdd k y).circuit registers) n).2) =
        .ok ((Op.addOdd k y).steps affs n) ∧
      ∀ i (hi : i < 32), (((Op.addOdd k y).circuit registers).output n)[i] = var ⟨n + 31 + i⟩ := by
  have hflat : Operations.toFlat (((Op.addOdd k y).circuit registers) n).2 =
      Operations.toFlat ((WrappingAdder.circuit 31).main { x := literal k, y := get registers y } n).2 ++
      Operations.toFlat ((Define.main ((WrappingAdder.circuit 31).output
        { x := literal k, y := get registers y } n)) (n + 31)).2 := by
    simp only [Op.circuit, AddOdd.circuit, circuit_norm]
    rw [toSubcircuit_toFlat]
    simp only [AddOdd.main, circuit_norm]
    rw [toSubcircuit_toFlat, toSubcircuit_toFlat, WrappingAdder.circuit_length]
    rfl
  obtain ⟨_, hrel⟩ := h
  have hW := wrapping_lower 31 n (literal k) (get registers y) (literalAffine k) (affGet affs y)
    (fun i hi => lower_literal k i hi) (fun i hi => (hrel y i hi).1) (fun i _ => literalAffine_bounded k i n)
    (fun i hi => (hrel y i hi).2)
  have hD := define_lower (n + 31) ((WrappingAdder.circuit 31).output
      { x := literal k, y := get registers y } n) (sumAffine n (literalAffine k) (affGet affs y) .zero)
    (fun i hi => hW.2 i hi)
    (fun i hi => sumAffine_bounded n 31 _ _ i (by omega) (literalAffine_bounded k i n) (hrel y i hi).2)
  refine ⟨?_, ?_⟩
  · rw [hflat, Gates.lower_append _ _ _ _ hW.1]
    have : (adderSteps n 31 (literalAffine k) (affGet affs y) .zero).length = 31 := by simp [adderSteps]
    rw [this, hD.1]
    rfl
  · intro i hi
    simp only [Op.circuit, AddOdd.circuit, circuit_norm]
    rw [define_output]

theorem addEven_lower (registers : List Reg) (affs : Affs) (n : ℕ) (k : Word) (y : ℕ) (h : Rel registers affs n) :
    Gates.lower n (Operations.toFlat (((Op.addEven k y).circuit registers) n).2) =
        .ok ((Op.addEven k y).steps affs n) ∧
      ∀ i (hi : i < 32), (((Op.addEven k y).circuit registers).output n)[i] = var ⟨n + 30 + i⟩ := by
  set q : BitVec 31 := BitVec.ofNat 31 (k.toNat / 2)
  have hflat : Operations.toFlat (((Op.addEven k y).circuit registers) n).2 =
      Operations.toFlat ((WrappingAdder.circuit 30).main { x := literal q, y := upper (get registers y) } n).2 ++
      Operations.toFlat ((Define.main (consLow (get registers y)[0] ((WrappingAdder.circuit 30).output
        { x := literal q, y := upper (get registers y) } n))) (n + 30)).2 := by
    simp only [Op.circuit, AddEven.circuit, circuit_norm]
    rw [toSubcircuit_toFlat]
    simp only [AddEven.main, circuit_norm]
    rw [toSubcircuit_toFlat, toSubcircuit_toFlat, WrappingAdder.circuit_length]
    rfl
  obtain ⟨_, hrel⟩ := h
  have hW := wrapping_lower 30 n (literal q) (upper (get registers y)) (literalAffine q)
    (fun i => affGet affs y (i + 1))
    (fun i hi => lower_literal q i hi) (fun i hi => by simpa [upper] using (hrel y (i + 1) (by omega)).1)
    (fun i _ => literalAffine_bounded q i n) (fun i hi => (hrel y (i + 1) (by omega)).2)
  have hD := define_lower (n + 30) (consLow (get registers y)[0] ((WrappingAdder.circuit 30).output
      { x := literal q, y := upper (get registers y) } n)) (fun i => if i = 0 then affGet affs y 0 else
        sumAffine n (literalAffine q) (fun i => affGet affs y (i + 1)) .zero (i - 1))
    (fun i hi => by
      rcases i with _ | i
      · simpa [consLow] using (hrel y 0 (by omega)).1
      · simpa [consLow] using hW.2 i (by omega))
    (fun i hi => by
      rcases i with _ | i
      · simpa using Affine.bounded_mono _ (hrel y 0 (by omega)).2 (by omega)
      · simpa using sumAffine_bounded n 30 _ _ i (by omega) (literalAffine_bounded q i n)
          (hrel y (i + 1) (by omega)).2)
  refine ⟨?_, ?_⟩
  · rw [hflat, Gates.lower_append _ _ _ _ hW.1]
    have : (adderSteps n 30 (literalAffine q) (fun i => affGet affs y (i + 1)) .zero).length = 30 := by
      simp [adderSteps]
    rw [this, hD.1]
    rfl
  · intro i hi
    simp only [Op.circuit, AddEven.circuit, circuit_norm]
    rw [define_output]

theorem xorRotr_lower (registers : List Reg) (affs : Affs) (n : ℕ) (r : Fin 32) (x y : ℕ)
    (h : Rel registers affs n) :
    Gates.lower n (Operations.toFlat (((Op.xorRotr r x y).circuit registers) n).2) =
        .ok ((Op.xorRotr r x y).steps affs n) ∧
      ∀ i (hi : i < 32), (((Op.xorRotr r x y).circuit registers).output n)[i] = var ⟨n + i⟩ := by
  obtain ⟨_, hrel⟩ := h
  have hD := define_lower n (rotr (xorBits (get registers x) (get registers y)) r.val)
    (fun i => .xor (affGet affs x ((i + r.val) % 32)) (affGet affs y ((i + r.val) % 32)))
    (fun i hi => by
      simp only [rotr, xorBits, Vector.getElem_ofFn, Vector.getElem_zipWith]
      show lowerAffine (.add _ _) = _
      simp [lowerAffine, (hrel x _ (Nat.mod_lt _ (by omega))).1, (hrel y _ (Nat.mod_lt _ (by omega))).1])
    (fun i hi => by
      simp [Affine.bounded, (hrel x _ (Nat.mod_lt _ (by omega))).2, (hrel y _ (Nat.mod_lt _ (by omega))).2])
  refine ⟨?_, ?_⟩
  · simp only [Op.circuit, XorRotr.circuit, circuit_norm]
    rw [toSubcircuit_toFlat]
    simp only [XorRotr.main, circuit_norm]
    rw [toSubcircuit_toFlat]
    exact hD.1
  · intro i hi
    simp only [Op.circuit, XorRotr.circuit, circuit_norm]
    rw [define_output]

/-- The result register's bits: the operation's last 32 variables. -/
def outputAffines (op : Op) (n : ℕ) : Vector Affine 32 := Vector.ofFn fun i => .var (n + op.length - 32 + i.val)

theorem op_lower (op : Op) (registers : List Reg) (affs : Affs) (n : ℕ) (h : Rel registers affs n) :
    Gates.lower n (Operations.toFlat ((op.circuit registers) n).2) = .ok (op.steps affs n) ∧
      ∀ i (hi : i < 32), ((op.circuit registers).output n)[i] = var ⟨n + op.length - 32 + i⟩ := by
  cases op with
  | add x y => simpa [Op.length] using add_lower registers affs n x y h
  | addOdd k y => simpa [Op.length] using addOdd_lower registers affs n k y h
  | addEven k y => simpa [Op.length] using addEven_lower registers affs n k y h
  | xorRotr r x y => simpa [Op.length] using xorRotr_lower registers affs n r x y h

theorem op_length_ge (op : Op) : 32 ≤ op.length := by cases op <;> simp [Op.length]

theorem rel_append (registers : List Reg) (affs : Affs) (n : ℕ) (op : Op) (h : Rel registers affs n)
    (result : Reg) (hres : ∀ i (hi : i < 32), result[i] = var ⟨n + op.length - 32 + i⟩) :
    Rel (registers ++ [result]) (affs ++ [outputAffines op n]) (n + op.length) := by
  obtain ⟨hlen, hrel⟩ := h
  have hge := op_length_ge op
  refine ⟨by simp [hlen], fun r i hi => ?_⟩
  rcases Nat.lt_trichotomy r registers.length with hr | hr | hr
  · have hg : get (registers ++ [result]) r = get registers r := by
      simp [get, List.getD_eq_getElem?_getD, List.getElem?_append_left hr]
    have ha : affGet (affs ++ [outputAffines op n]) r i = affGet affs r i := by
      simp [affGet, hi, List.getD_eq_getElem?_getD, List.getElem?_append_left (hlen ▸ hr)]
    rw [hg, ha]
    exact ⟨(hrel r i hi).1, Affine.bounded_mono _ (hrel r i hi).2 (by omega)⟩
  · subst hr
    have hg : get (registers ++ [result]) registers.length = result := by
      simp [get, List.getD_eq_getElem?_getD]
    have ha : affGet (affs ++ [outputAffines op n]) registers.length i = .var (n + op.length - 32 + i) := by
      simp [affGet, hi, List.getD_eq_getElem?_getD, hlen, outputAffines]
    rw [hg, ha, hres i hi]
    refine ⟨rfl, ?_⟩
    simp [Affine.bounded]
    omega
  · have hg : get (registers ++ [result]) r = Vector.replicate 32 0 := by
      simp [get, List.getD_eq_getElem?_getD, List.getElem?_eq_none (show (registers ++ [result]).length ≤ r by
        simp; omega)]
    have ha : affGet (affs ++ [outputAffines op n]) r i = .zero := by
      simp [affGet, hi, List.getD_eq_getElem?_getD, List.getElem?_eq_none (show (affs ++ [outputAffines op n]).length ≤ r by
        simp; omega)]
    rw [hg, ha]
    exact ⟨by simp; rfl, rfl⟩

theorem steps_length (op : Op) (affs : Affs) (n : ℕ) : (op.steps affs n).length = op.length := by
  cases op <;> simp [Op.steps, adderSteps, defines, Op.length]

def modelSteps : List Op → Affs → ℕ → List Step
  | [], _, _ => []
  | op :: ops, affs, n => op.steps affs n ++ modelSteps ops (affs ++ [outputAffines op n]) (n + op.length)

def modelAffs : List Op → Affs → ℕ → Affs
  | [], affs, _ => affs
  | op :: ops, affs, n => modelAffs ops (affs ++ [outputAffines op n]) (n + op.length)

theorem run_lower (ops : List Op) (registers : List Reg) (affs : Affs) (n : ℕ) (h : Rel registers affs n) :
    Gates.lower n (Operations.toFlat ((run ops registers) n).2) = .ok (modelSteps ops affs n) ∧
      Rel ((run ops registers).output n) (modelAffs ops affs n) (n + (ops.map Op.length).sum) := by
  induction ops generalizing registers affs n with
  | nil => exact ⟨rfl, by simpa [run, modelAffs, circuit_norm] using h⟩
  | cons op ops ih =>
    obtain ⟨hop, hres⟩ := op_lower op registers affs n h
    have hrel := rel_append registers affs n op h _ hres
    have hlen := op_localLength op registers n
    obtain ⟨hrest, hfinal⟩ := ih _ _ _ hrel
    simp only [run, circuit_norm] at hlen ⊢
    rw [hlen]
    refine ⟨?_, ?_⟩
    · rw [toFlat_append, Gates.lower_append _ _ _ _ hop, steps_length]
      erw [hrest]
      rfl
    · simp only [modelAffs, List.sum_cons, ← Nat.add_assoc]
      exact hfinal

/-! The whole compression. -/

namespace Compress

attribute [local irreducible] program

/-- The ports as variables: `t` at 0, `f0` at 64, `h` at 96 and `m` at 352, 864 in all. -/
def inputs : Var Input Bit :=
  { t := Vector.ofFn fun i => var ⟨i.val⟩, f0 := Vector.ofFn fun i => var ⟨64 + i.val⟩,
    h := Vector.ofFn fun i => var ⟨96 + i.val⟩, m := Vector.ofFn fun i => var ⟨352 + i.val⟩ }

def inputBits : ℕ := 864

/-- The initial registers' bits, as `register` builds them from `inputs`. -/
def registerAffines (r : Fin 32) : Vector Affine 32 :=
  if r.val < 8 then Vector.ofFn fun j => .var (96 + 32 * r.val + j.val)
  else if r.val < 24 then Vector.ofFn fun j => .var (352 + 32 * (r.val - 8) + j.val)
  else match r.val - 24 with
    | 4 => Vector.ofFn fun j => .xor (literalAffine IV[4] j) (.var j.val)
    | 5 => Vector.ofFn fun j => .xor (literalAffine IV[5] j) (.var (32 + j.val))
    | 6 => Vector.ofFn fun j => .xor (literalAffine IV[6] j) (.var (64 + j.val))
    | 7 => Vector.ofFn fun j => literalAffine IV[7] j
    | i => Vector.ofFn fun j => literalAffine IV[i % 8] j

def initialAffines : Affs := List.ofFn registerAffines

theorem initial_rel : Rel (registers inputs) initialAffines inputBits := by
  refine ⟨by simp [registers, initialAffines], fun r i hi => ?_⟩
  by_cases hr : r < 32
  · have hg : get (registers inputs) r = register inputs ⟨r, hr⟩ := by
      simp only [get, registers, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hr, dite_true, Option.getD_some]
    have ha : affGet initialAffines r i = (registerAffines ⟨r, hr⟩)[i] := by
      simp only [affGet, hi, dite_true, initialAffines, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hr,
        Option.getD_some]
    rw [hg, ha]
    have hadd : ∀ (a b : Expression Bit) (la lb : Affine), lowerAffine a = .ok la → lowerAffine b = .ok lb →
        lowerAffine (a + b) = .ok (.xor la lb) := by
      intro a b la lb ha hb
      show lowerAffine (.add _ _) = _
      simp [lowerAffine, ha, hb]
    interval_cases r <;>
      simp only [register, registerAffines, chunk, inputs, low, high, xorBits, Vector.getElem_ofFn] <;>
      try norm_num
    all_goals refine ⟨?_, ?_⟩
    all_goals first
      | (simp only [lowerAffine]; done)
      | (simp only [lowerAffine]; congr 2; omega)
      | (simp only [Affine.bounded, inputBits]; exact decide_eq_true (by omega))
      | exact lower_literal _ _ hi
      | exact literalAffine_bounded _ _ _
      | exact hadd _ _ _ _ (lower_literal _ _ hi) rfl
      | (simp only [Affine.bounded, literalAffine_bounded, inputBits, Bool.true_and]
         exact decide_eq_true (by omega))
  · have hg : get (registers inputs) r = Vector.replicate 32 0 := by
      simp only [get, registers, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hr, dite_false, Option.getD_none]
    have ha : affGet initialAffines r i = .zero := by
      simp only [affGet, hi, dite_true, initialAffines, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hr,
        dite_false, Option.getD_none, Vector.getElem_replicate]
    rw [hg, ha]
    exact ⟨by simp; rfl, rfl⟩

/-- The output bits' affine forms: `h_i ^ v_i ^ v_{i+8}`, bit by bit, through the final lanes. -/
def outputAffine (final : Affs) (k : Fin 256) : Affine :=
  .xor (.xor (.var (96 + 32 * (k.val / 32) + k.val % 32)) (affGet final program.lanes[k.val / 32] (k.val % 32)))
    (affGet final program.lanes[k.val / 32 + 8] (k.val % 32))

theorem lowerOutputs_ofFn {k : ℕ} (f : Fin k → Expression Bit) (g : Fin k → Affine)
    (h : ∀ i, lowerAffine (f i) = .ok (g i)) : lowerOutputs (List.ofFn f) = .ok (List.ofFn g) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.ofFn_succ, List.ofFn_succ, lowerOutputs, h 0, ih (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ)]

/-- The exact artifact the Clean compression lowers to, at the ports' variables. -/
def artifact : Gates.Artifact :=
  { start := inputBits, steps := modelSteps program.ops initialAffines inputBits,
    outputs := List.ofFn (outputAffine (modelAffs program.ops initialAffines inputBits)) }

theorem lowered : Gates.lowerCircuit Compress.circuit inputBits inputs = .ok artifact := by
  obtain ⟨hrun, hfinal⟩ := run_lower program.ops (registers inputs) initialAffines inputBits initial_rel
  simp only [Gates.lowerCircuit, Gates.lowerAt]
  rw [toSubcircuit_toFlat]
  simp only [Compress.circuit, Compress.main, circuit_norm]
  rw [hrun]
  have hout : lowerOutputs (toElements (M := fields 256)
      (output inputs (run program.ops (registers inputs) inputBits).1)).toList =
      .ok (List.ofFn (outputAffine (modelAffs program.ops initialAffines inputBits))) := by
    show lowerOutputs (Vector.ofFn _).toList = _
    rw [Vector.toList_ofFn]
    apply lowerOutputs_ofFn
    intro k
    have hk : k.val < 256 := k.isLt
    have h1 := (hfinal.2 (program.lanes[k.val / 32]'(by omega)) (k.val % 32) (Nat.mod_lt _ (by omega))).1
    have h2 := (hfinal.2 (program.lanes[k.val / 32 + 8]'(by omega)) (k.val % 32) (Nat.mod_lt _ (by omega))).1
    show lowerAffine (.add (.add _ _) _) = _
    simp only [lowerAffine, chunk, inputs, Vector.getElem_ofFn]
    erw [h1, h2]
    have h0 : (Vector.ofFn fun j : Fin 32 => (var ⟨96 + (32 * (k.val / 32) + j.val)⟩ : Expression Bit))[(⟨k.val % 32,
        Nat.mod_lt _ (by omega)⟩ : Fin 32)] = var ⟨96 + 32 * (k.val / 32) + k.val % 32⟩ := by
      simp only [Fin.getElem_fin, Vector.getElem_ofFn]; congr 2; omega
    erw [h0]
    rfl
  rw [hout]
  rfl

end Compress

end LeanVMCircuits.Blake2s
