module

public import Quantum.Sponge.Oracle.Event
public import Quantum.Sponge.Oracle.Hardwired.Mixed

@[expose] public section

/-!
# The hardwired runtime

The register `HwReg X Z M = DbReg X Z × Hw X Z × M` holds the three compressed databases, the
classical *hardwired cells* `W : Hw X Z` (cells of `h`, `k`, `k'` whose value is fixed), and a
classical memory `m : M`. The ports (`hwSpec X Z M`):

* `h`, `k`, `k'` (`spongeHardwired`): the compressed oracle on cells that are not hardwired, the
  fixed function on hardwired ones. Each is the table oracle of `(W a).getD (D.lookup a)`
  conjugated by the compression of every database cell (`hwPort`); on the block of `(W, m)` it is
  `(1 - Π_W) O + Π_W (S_W ⊗ 1)` with `O` the compressed oracle of `spongeCompressed`, `Π_W` the
  projector on hardwired query inputs and `S_W` the oracle unitary of the hardwired values
  (`Quantum.Sponge.spongeHardwired_U`).
* `readH z upd`, `readK x upd`, `readK' x upd` (`HwRead`): the projective read of a cell in the
  decompressed basis, `Comp_a |o⟩⟨o| Comp_a` (`cellRead`), or the hardwired value; the outcome
  `o` and the memory `m` before the read are returned, and the memory becomes `upd m o`.
* `programH z v`, `programK x v`, `programK' x v` (`HwProg`): hardwire a cell to `v`, discarding
  the database content of the cell (`cellDiscard`); the old database content and old hardwired
  value are returned.

Runtime 1 (`spongeHardwiredReadRuntime`, signature `hwReadSpec`) has the sponge and read ports;
the hardwired runtime (`spongeHardwiredRuntime`, signature `hwSpec`) adds the program ports. Every
classical port is a complete family of Kraus operators classical on `Hw × M` (`clsKraus`).
-/

open Matrix
open scoped Kronecker ENNReal

universe u v w

namespace Quantum.Sponge

open Quantum

/-! ## Classical Kraus operators -/

section classical

variable {T B : Type} [Fintype T] [DecidableEq T] [Fintype B] [DecidableEq B]

/-- A Kraus operator classical on the factor `B`: on the classical states `b` with `p b` it moves
`b` to `φ b` and applies `R b` to the factor `T`; it annihilates the other classical states. -/
def clsKraus (p : B → Prop) [DecidablePred p] (φ : B → B) (R : B → Matrix T T ℂ) :
    Matrix (T × B) (T × B) ℂ :=
  Matrix.of fun s' s ↦ if p s.2 ∧ s'.2 = φ s.2 then R s.2 s'.1 s.1 else 0

omit [Fintype T] [DecidableEq T] [Fintype B] in
theorem clsKraus_apply (p : B → Prop) [DecidablePred p] (φ : B → B) (R : B → Matrix T T ℂ)
    (s' s : T × B) :
    clsKraus p φ R s' s = if p s.2 ∧ s'.2 = φ s.2 then R s.2 s'.1 s.1 else 0 :=
  rfl

omit [DecidableEq T] in
/-- If `φ` is injective on `p`, the Gram operator of a classical Kraus operator is block
diagonal. -/
theorem conjTranspose_clsKraus_mul_self (p : B → Prop) [DecidablePred p] (φ : B → B)
    (R : B → Matrix T T ℂ) (hφ : ∀ b b', p b → p b' → φ b = φ b' → b = b') :
    (clsKraus p φ R)ᴴ * clsKraus p φ R =
      blockDiagonal fun b ↦ if p b then (R b)ᴴ * R b else 0 := by
  ext ⟨t, b⟩ ⟨t'', b''⟩
  simp only [Matrix.mul_apply, conjTranspose_apply, clsKraus_apply, blockDiagonal_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  by_cases hb : p b
  · rw [Finset.sum_eq_single (φ b) (fun b' _ hb' ↦ by
        have : ¬ (p b ∧ b' = φ b) := fun h ↦ hb' h.2
        simp [this]) (fun h ↦ absurd (Finset.mem_univ _) h)]
    by_cases hb'' : p b'' ∧ φ b = φ b''
    · obtain ⟨hp'', he⟩ := hb''
      obtain rfl := hφ b b'' hb hp'' he
      simp [hb, Matrix.mul_apply, conjTranspose_apply]
    · have hne : b ≠ b'' := fun h ↦ hb'' ⟨h ▸ hb, h ▸ rfl⟩
      simp only [hb, true_and, ↓reduceIte, hne]
      refine Finset.sum_eq_zero fun t' _ ↦ ?_
      have : ¬ (p b'' ∧ φ b = φ b'') := hb''
      simp only [this, ↓reduceIte, mul_zero]
  · simp [hb]

/-- **Completeness of a classical Kraus family.** If every `φ r` is injective on `p r` and, for
every classical state, the Gram operators of the branches that accept it add up to the identity,
the Kraus operators (with a trivial public register) form a complete family. -/
theorem sum_conjTranspose_clsKraus_mul_self {ι : Type} [Fintype ι] (p : ι → B → Prop)
    [∀ r, DecidablePred (p r)] (φ : ι → B → B) (R : ι → B → Matrix T T ℂ)
    (hφ : ∀ r b b', p r b → p r b' → φ r b = φ r b' → b = b')
    (hR : ∀ b, ∑ r, (if p r b then (R r b)ᴴ * R r b else 0) = 1) :
    ∑ r, ((1 : Matrix Unit Unit ℂ) ⊗ₖ clsKraus (p r) (φ r) (R r))ᴴ *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ clsKraus (p r) (φ r) (R r)) = 1 := by
  simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul,
    conjTranspose_clsKraus_mul_self _ _ _ (hφ _)]
  ext ⟨u, t, b⟩ ⟨u', t', b'⟩
  have h := congrFun (congrFun (hR b) t) t'
  simp only [Matrix.sum_apply, kroneckerMap_apply, blockDiagonal_apply] at h ⊢
  rw [← Finset.mul_sum, Matrix.one_apply, Matrix.one_apply]
  by_cases hbb : b = b'
  · subst hbb
    simp only [↓reduceIte, h, Matrix.one_apply, Prod.mk.injEq, Subsingleton.elim u u', true_and,
      one_mul, and_true]
  · simp [hbb]

end classical

/-- A sum of Kronecker products with a common right factor. -/
theorem sum_kronecker_left {ι l m : Type*} (s : Finset ι) (A : ι → Matrix l l ℂ)
    (B : Matrix m m ℂ) : ∑ r ∈ s, A r ⊗ₖ B = (∑ r ∈ s, A r) ⊗ₖ B := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp [Matrix.sum_apply, kroneckerMap_apply, Finset.sum_mul]

/-- A sum of Kronecker products with a common left factor. -/
theorem sum_kronecker_right {ι l m : Type*} (s : Finset ι) (A : Matrix l l ℂ)
    (B : ι → Matrix m m ℂ) : ∑ r ∈ s, A ⊗ₖ B r = A ⊗ₖ ∑ r ∈ s, B r := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp [Matrix.sum_apply, kroneckerMap_apply, Finset.mul_sum]

/-! ## One-cell operators on a database -/

section cell

variable {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]

/-- The read of cell `a` in the decompressed basis with outcome `o`, on a database whose cell `a`
is hardwired to `w a`: the projector `Comp_a |o⟩⟨o| Comp_a` when `a` is not hardwired; when it is
hardwired to `v`, the identity on the outcome `some v` and zero on the others. -/
noncomputable def cellRead (w : Database A Y) (a : A) (o : Option Y) :
    Matrix (Database A Y) (Database A Y) ℂ :=
  match w a with
  | some v => if o = some v then 1 else 0
  | none => compressAt Y a * diagonal (fun D ↦ if D a = o then 1 else 0) * compressAt Y a

/-- Discarding the content `o` of cell `a`: `|D[a ↦ ⊥]⟩⟨D|` on the databases with `D a = o`. -/
def cellDiscard (a : A) (o : Option Y) : Matrix (Database A Y) (Database A Y) ℂ :=
  Matrix.of fun D' D ↦ if D a = o ∧ D' = Function.update D a none then 1 else 0

theorem conjTranspose_cellRead (w : Database A Y) (a : A) (o : Option Y) :
    (cellRead w a o)ᴴ = cellRead w a o := by
  unfold cellRead
  split
  · split_ifs <;> simp
  · have hd : (diagonal fun D : Database A Y ↦ if D a = o then (1 : ℂ) else 0)ᴴ =
        diagonal fun D ↦ if D a = o then 1 else 0 := by
      rw [diagonal_conjTranspose]
      congr 1
      funext D
      simp only [Pi.star_apply]
      split_ifs <;> simp
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_compressAt, hd, Matrix.mul_assoc]

variable [Nonempty Y]

/-- The reads of a cell form a complete projective measurement. -/
theorem sum_conjTranspose_cellRead_mul_self (w : Database A Y) (a : A) :
    ∑ o, (cellRead w a o)ᴴ * cellRead w a o = 1 := by
  simp only [conjTranspose_cellRead]
  unfold cellRead
  split
  · next v _ =>
    rw [Finset.sum_eq_single (some v) (fun o _ ho ↦ by simp [ho]) (by simp)]
    simp
  · have hd : ∀ o : Option Y, diagonal (fun D : Database A Y ↦ if D a = o then (1 : ℂ) else 0) *
        diagonal (fun D ↦ if D a = o then 1 else 0) = diagonal fun D ↦ if D a = o then 1 else 0 :=
      fun o ↦ by
        rw [diagonal_mul_diagonal]
        congr 1
        funext D
        split_ifs <;> simp
    have hsum : ∑ o : Option Y, diagonal (fun D : Database A Y ↦
        if D a = o then (1 : ℂ) else 0) = 1 := by
      ext D D'
      by_cases he : D = D'
      · subst he
        simp [Matrix.sum_apply]
      · simp [Matrix.sum_apply, he]
    calc ∑ o, compressAt Y a * diagonal (fun D ↦ if D a = o then 1 else 0) * compressAt Y a *
          (compressAt Y a * diagonal (fun D ↦ if D a = o then 1 else 0) * compressAt Y a)
        = ∑ o, compressAt Y a * diagonal (fun D : Database A Y ↦ if D a = o then (1 : ℂ) else 0) *
            compressAt Y a := by
          refine Finset.sum_congr rfl fun o _ ↦ ?_
          calc _ = compressAt Y a * diagonal (fun D ↦ if D a = o then 1 else 0) *
                (compressAt Y a * compressAt Y a) *
                diagonal (fun D ↦ if D a = o then 1 else 0) * compressAt Y a := by
                simp only [Matrix.mul_assoc]
            _ = _ := by
                rw [compressAt_mul_self, Matrix.mul_one, Matrix.mul_assoc
                  (compressAt Y a), hd]
      _ = 1 := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, hsum, Matrix.mul_one, compressAt_mul_self]

omit [Nonempty Y] in
/-- Discarding the content of a cell is a complete family. -/
theorem sum_conjTranspose_cellDiscard_mul_self (a : A) :
    ∑ o, (cellDiscard (Y := Y) a o)ᴴ * cellDiscard a o = 1 := by
  ext D D''
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, cellDiscard, of_apply]
  rw [Finset.sum_comm, Finset.sum_eq_single (Function.update D a none)]
  · rw [Finset.sum_eq_single (D a) (fun o _ ho ↦ by simp [Ne.symm ho]) (by simp)]
    by_cases he : D = D''
    · subst he
      simp
    · have : ¬ (D'' a = D a ∧ Function.update D a none = Function.update D'' a none) := by
        rintro ⟨h₁, h₂⟩
        refine he (funext fun x ↦ ?_)
        by_cases hx : x = a
        · subst hx
          exact h₁.symm
        · simpa [Function.update_of_ne hx] using congrFun h₂ x
      simp [this, he]
  · intro D' _ hD'
    refine Finset.sum_eq_zero fun o _ ↦ ?_
    have : ¬ (D a = o ∧ D' = Function.update D a none) := fun h ↦ hD' h.2
    simp [this]
  · simp

omit [Nonempty Y] in
/-- A nonzero entry of a one-cell compression leaves the other cells unchanged. -/
theorem compressAt_apply_ne_zero {a : A} {D D' : Database A Y} (h : compressAt Y a D D' ≠ 0)
    (x : A) (hx : x ≠ a) : D x = D' x := by
  rw [compressAt, piKron_apply] at h
  have h' := (Finset.prod_ne_zero_iff.mp h) x (Finset.mem_univ x)
  rw [Pi.mulSingle_eq_of_ne hx, Matrix.one_apply] at h'
  by_contra hne
  exact h' (by simp [hne])

omit [Nonempty Y] in
/-- A nonzero entry of a read leaves the other cells unchanged. -/
theorem cellRead_apply_ne_zero {w : Database A Y} {a : A} {o : Option Y} {D' D : Database A Y}
    (h : cellRead w a o D' D ≠ 0) (x : A) (hx : x ≠ a) : D' x = D x := by
  rcases hw : w a with _ | v
  · simp only [cellRead, hw] at h
    rw [Matrix.mul_apply] at h
    obtain ⟨D₁, -, h₁⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    rw [mul_diagonal] at h₁
    have ha := left_ne_zero_of_mul (left_ne_zero_of_mul h₁)
    have hb := right_ne_zero_of_mul h₁
    rw [compressAt_apply_ne_zero ha x hx, compressAt_apply_ne_zero hb x hx]
  · simp only [cellRead, hw] at h
    split_ifs at h
    · rw [Matrix.one_apply] at h
      split_ifs at h with hD
      · rw [hD]
      · exact absurd rfl h
    · exact absurd rfl h

omit [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- A database that differs from `D` at most at `a` has at most one more entry. -/
theorem size_le_of_eq_off {a : A} {D D' : Database A Y} (h : ∀ x, x ≠ a → D' x = D x) :
    D'.size ≤ D.size + 1 := by
  have hD : D' = Function.update D a (D' a) := by
    funext x
    by_cases hx : x = a
    · subst hx
      simp
    · rw [Function.update_of_ne hx, h x hx]
  rw [hD]
  exact Database.size_update_le D a _

omit [Fintype Y] [Nonempty Y] in
theorem cellDiscard_apply_ne_zero {a : A} {o : Option Y} {D' D : Database A Y}
    (h : cellDiscard a o D' D ≠ 0) (x : A) (hx : x ≠ a) : D' x = D x := by
  simp only [cellDiscard, of_apply] at h
  split_ifs at h with hD
  · rw [hD.2, Function.update_of_ne hx]
  · exact absurd rfl h

end cell

/-! ## Hardwired cells and the register -/

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

variable (X Z) in
/-- The hardwired cells of `h`, `k`, `k'`, with their values: three classical partial functions,
in the order of `DbReg`. -/
abbrev Hw := DbReg X Z

variable (X Z) in
/-- The register of the hardwired runtime: the databases, the hardwired cells, and a classical
memory. -/
abbrev HwReg (M : Type) := DbReg X Z × Hw X Z × M

/-- The hardwired cells over the database cells. -/
def hwView (W : Hw X Z) (D : DbReg X Z) : DbReg X Z :=
  (fun z ↦ (W.1 z).or (D.1 z), fun x ↦ (W.2.1 x).or (D.2.1 x), fun x ↦ (W.2.2 x).or (D.2.2 x))

/-- The hardwired cells over the database cells, as database triples. -/
def union (W : Hw X Z) (D : DbReg X Z) : Dbs X Z :=
  (hwView W D).toDbs

/-- The database triples of an event of the hardwired register at the classical data `(W, m)`. -/
def slice {M : Type} (S : Set (HwReg X Z M)) (W : Hw X Z) (m : M) : Set (Dbs X Z) :=
  {D | ((D.h, D.k, D.k'), W, m) ∈ S}

/-! ## The classical ports -/

variable (X Z) in
/-- The read ports of the hardwired runtime. -/
inductive HwRead (M : Type) where
  /-- Read cell `z` of `h`, updating the memory with `upd`. -/
  | readH (z : Z) (upd : M → Option X → M)
  /-- Read cell `x` of `k`, updating the memory with `upd`. -/
  | readK (x : X) (upd : M → Option Z → M)
  /-- Read cell `x` of `k'`, updating the memory with `upd`. -/
  | readK' (x : X) (upd : M → Option Z → M)

/-- The classical result of a read: the outcome and the memory before the read. -/
@[reducible]
def HwRead.Result {M : Type} : HwRead X Z M → Type
  | .readH .. => Option X × M
  | .readK .. => Option Z × M
  | .readK' .. => Option Z × M

variable (X Z) in
/-- The program ports of the hardwired runtime. -/
inductive HwProg where
  /-- Hardwire cell `z` of `h` to `v`. -/
  | programH (z : Z) (v : X)
  /-- Hardwire cell `x` of `k` to `v`. -/
  | programK (x : X) (v : Z)
  /-- Hardwire cell `x` of `k'` to `v`. -/
  | programK' (x : X) (v : Z)

/-- The classical result of programming a cell: its database content and hardwired value
before. -/
@[reducible]
def HwProg.Result : HwProg X Z → Type
  | .programH .. => Option X × Option X
  | .programK .. => Option Z × Option Z
  | .programK' .. => Option Z × Option Z

variable (X Z) in
/-- The signature of the read ports: trivial public registers, classical results. -/
@[reducible]
def hwReadCmdSpec (M : Type) : QuantumOracleSpec.{0, 0} where
  Port := HwRead X Z M
  In _ := QReg.of Unit
  Out _ := QReg.of Unit
  Result := HwRead.Result

variable (X Z) in
/-- The signature of the program ports: trivial public registers, classical results. -/
@[reducible]
def hwProgSpec : QuantumOracleSpec.{0, 0} where
  Port := HwProg X Z
  In _ := QReg.of Unit
  Out _ := QReg.of Unit
  Result := HwProg.Result

variable (X Z) in
/-- The signature of runtime 1: the three sponge ports, then the read ports. -/
@[reducible]
def hwReadSpec (M : Type) : QuantumOracleSpec.{0, 0} :=
  (spongeSpec X Z).sum (hwReadCmdSpec X Z M)

variable (X Z) in
/-- The signature of the hardwired runtime: the sponge and read ports, then the program ports. -/
@[reducible]
def hwSpec (M : Type) : QuantumOracleSpec.{0, 0} :=
  (hwReadSpec X Z M).sum (hwProgSpec X Z)

/-- The classical ports: `false` on the sponge ports, `true` on the read and program ports. -/
def hwCls {M : Type} : (hwSpec X Z M).Port → Bool
  | .inl (.inl _) => false
  | .inl (.inr _) => true
  | .inr _ => true

variable {M : Type} [Fintype M] [DecidableEq M]

/-- Decidable equality of the hardwired register, named so that instance search stays small. -/
instance (priority := high) HwReg.instDecidableEq : DecidableEq (HwReg X Z M) :=
  inferInstanceAs (DecidableEq (DbReg X Z × DbReg X Z × M))

/-- The hardwired register is finite. -/
instance (priority := high) HwReg.instFintype : Fintype (HwReg X Z M) :=
  inferInstanceAs (Fintype (DbReg X Z × DbReg X Z × M))

/-- The Kraus operator of a read of cell `z` of `h` with outcome `r = (o, m)`. -/
noncomputable def readKrausH (z : Z) (upd : M → Option X → M) (r : Option X × M) :
    Matrix (DbReg X Z × Hw X Z × M) (DbReg X Z × Hw X Z × M) ℂ :=
  clsKraus (fun b : Hw X Z × M ↦ b.2 = r.2) (fun b ↦ (b.1, upd r.2 r.1))
    fun b ↦ cellRead b.1.1 z r.1 ⊗ₖ (1 : Matrix (Database X Z × Database X Z) _ ℂ)

/-- The Kraus operator of a read of cell `x` of `k` with outcome `r = (o, m)`. -/
noncomputable def readKrausK (x : X) (upd : M → Option Z → M) (r : Option Z × M) :
    Matrix (DbReg X Z × Hw X Z × M) (DbReg X Z × Hw X Z × M) ℂ :=
  clsKraus (fun b : Hw X Z × M ↦ b.2 = r.2) (fun b ↦ (b.1, upd r.2 r.1))
    fun b ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
      (cellRead b.1.2.1 x r.1 ⊗ₖ (1 : Matrix (Database X Z) (Database X Z) ℂ))

/-- The Kraus operator of a read of cell `x` of `k'` with outcome `r = (o, m)`. -/
noncomputable def readKrausK' (x : X) (upd : M → Option Z → M) (r : Option Z × M) :
    Matrix (DbReg X Z × Hw X Z × M) (DbReg X Z × Hw X Z × M) ℂ :=
  clsKraus (fun b : Hw X Z × M ↦ b.2 = r.2) (fun b ↦ (b.1, upd r.2 r.1))
    fun b ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
      ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ cellRead b.1.2.2 x r.1)

/-- The Kraus operator of hardwiring cell `z` of `h` to `v`, with outcome `r = (oD, oW)`. -/
noncomputable def programKrausH (z : Z) (v : X) (r : Option X × Option X) :
    Matrix (DbReg X Z × Hw X Z × M) (DbReg X Z × Hw X Z × M) ℂ :=
  clsKraus (fun b : Hw X Z × M ↦ b.1.1 z = r.2)
    (fun b ↦ ((Function.update b.1.1 z (some v), b.1.2), b.2))
    fun _ ↦ cellDiscard z r.1 ⊗ₖ (1 : Matrix (Database X Z × Database X Z) _ ℂ)

/-- The Kraus operator of hardwiring cell `x` of `k` to `v`, with outcome `r = (oD, oW)`. -/
noncomputable def programKrausK (x : X) (v : Z) (r : Option Z × Option Z) :
    Matrix (DbReg X Z × Hw X Z × M) (DbReg X Z × Hw X Z × M) ℂ :=
  clsKraus (fun b : Hw X Z × M ↦ b.1.2.1 x = r.2)
    (fun b ↦ ((b.1.1, Function.update b.1.2.1 x (some v), b.1.2.2), b.2))
    fun _ ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
      (cellDiscard x r.1 ⊗ₖ (1 : Matrix (Database X Z) (Database X Z) ℂ))

/-- The Kraus operator of hardwiring cell `x` of `k'` to `v`, with outcome `r = (oD, oW)`. -/
noncomputable def programKrausK' (x : X) (v : Z) (r : Option Z × Option Z) :
    Matrix (DbReg X Z × Hw X Z × M) (DbReg X Z × Hw X Z × M) ℂ :=
  clsKraus (fun b : Hw X Z × M ↦ b.1.2.2 x = r.2)
    (fun b ↦ ((b.1.1, b.1.2.1, Function.update b.1.2.2 x (some v)), b.2))
    fun _ ↦ (1 : Matrix (Database Z X) (Database Z X) ℂ) ⊗ₖ
      ((1 : Matrix (Database X Z) (Database X Z) ℂ) ⊗ₖ cellDiscard x r.1)

/-- The Kraus operators of a read of `h` form a complete family. -/
theorem sum_readKrausH [Nonempty X] (z : Z) (upd : M → Option X → M) :
    ∑ r, ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausH z upd r)ᴴ *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausH z upd r) = 1 := by
  refine sum_conjTranspose_clsKraus_mul_self _ _ _
    (fun r b b' hb hb' he ↦ Prod.ext (Prod.mk.inj he).1 (hb.trans hb'.symm)) fun b ↦ ?_
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
  rw [sum_kronecker_left, sum_conjTranspose_cellRead_mul_self, one_kronecker_one]

omit [Fintype M] [DecidableEq M] in
/-- Updating a cell to a fixed value is injective on the functions with a fixed value there. -/
theorem update_eq_update_iff {α β : Type*} [DecidableEq α] {f g : α → β} {a : α} {v : β}
    (ha : f a = g a) (h : Function.update f a v = Function.update g a v) : f = g := by
  funext x
  by_cases hx : x = a
  · subst hx
    exact ha
  · simpa [Function.update_of_ne hx] using congrFun h x

/-- The Kraus operators of a read of `k` form a complete family. -/
theorem sum_readKrausK [Nonempty Z] (x : X) (upd : M → Option Z → M) :
    ∑ r, ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausK x upd r)ᴴ *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausK x upd r) = 1 := by
  refine sum_conjTranspose_clsKraus_mul_self _ _ _
    (fun r b b' hb hb' he ↦ Prod.ext (Prod.mk.inj he).1 (hb.trans hb'.symm)) fun b ↦ ?_
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
  rw [sum_kronecker_right, sum_kronecker_left, sum_conjTranspose_cellRead_mul_self,
    one_kronecker_one, one_kronecker_one]

/-- The Kraus operators of a read of `k'` form a complete family. -/
theorem sum_readKrausK' [Nonempty Z] (x : X) (upd : M → Option Z → M) :
    ∑ r, ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausK' x upd r)ᴴ *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausK' x upd r) = 1 := by
  refine sum_conjTranspose_clsKraus_mul_self _ _ _
    (fun r b b' hb hb' he ↦ Prod.ext (Prod.mk.inj he).1 (hb.trans hb'.symm)) fun b ↦ ?_
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
  rw [sum_kronecker_right, sum_kronecker_right, sum_conjTranspose_cellRead_mul_self,
    one_kronecker_one, one_kronecker_one]

omit [Fintype M] in
/-- The Kraus operators of programming a cell of `h` form a complete family. -/
theorem sum_programKrausH [Fintype M] (z : Z) (v : X) :
    ∑ r, ((1 : Matrix Unit Unit ℂ) ⊗ₖ programKrausH (M := M) z v r)ᴴ *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ programKrausH z v r) = 1 := by
  refine sum_conjTranspose_clsKraus_mul_self _ _ _
    (fun r b b' hb hb' he ↦ ?_) fun b ↦ ?_
  · obtain ⟨h₁₂, h₃⟩ := Prod.mk.inj he
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h₁₂
    exact Prod.ext (Prod.ext (update_eq_update_iff (hb.trans hb'.symm) h₁) h₂) h₃
  · rw [Fintype.sum_prod_type]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
    rw [sum_kronecker_left, sum_conjTranspose_cellDiscard_mul_self, one_kronecker_one]

omit [Fintype M] in
/-- The Kraus operators of programming a cell of `k` form a complete family. -/
theorem sum_programKrausK [Fintype M] (x : X) (v : Z) :
    ∑ r, ((1 : Matrix Unit Unit ℂ) ⊗ₖ programKrausK (M := M) x v r)ᴴ *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ programKrausK x v r) = 1 := by
  refine sum_conjTranspose_clsKraus_mul_self _ _ _
    (fun r b b' hb hb' he ↦ ?_) fun b ↦ ?_
  · obtain ⟨h₁, h₃⟩ := Prod.mk.inj he
    obtain ⟨h₀, h₁⟩ := Prod.mk.inj h₁
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h₁
    exact Prod.ext (Prod.ext h₀ (Prod.ext (update_eq_update_iff (hb.trans hb'.symm) h₁) h₂)) h₃
  · rw [Fintype.sum_prod_type]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
    rw [sum_kronecker_right, sum_kronecker_left, sum_conjTranspose_cellDiscard_mul_self,
      one_kronecker_one, one_kronecker_one]

omit [Fintype M] in
/-- The Kraus operators of programming a cell of `k'` form a complete family. -/
theorem sum_programKrausK' [Fintype M] (x : X) (v : Z) :
    ∑ r, ((1 : Matrix Unit Unit ℂ) ⊗ₖ programKrausK' (M := M) x v r)ᴴ *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ programKrausK' x v r) = 1 := by
  refine sum_conjTranspose_clsKraus_mul_self _ _ _
    (fun r b b' hb hb' he ↦ ?_) fun b ↦ ?_
  · obtain ⟨h₁, h₃⟩ := Prod.mk.inj he
    obtain ⟨h₀, h₁⟩ := Prod.mk.inj h₁
    obtain ⟨h₂, h₁⟩ := Prod.mk.inj h₁
    exact Prod.ext (Prod.ext h₀ (Prod.ext h₂ (update_eq_update_iff (hb.trans hb'.symm) h₁))) h₃
  · rw [Fintype.sum_prod_type]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
    rw [sum_kronecker_right, sum_kronecker_right, sum_conjTranspose_cellDiscard_mul_self,
      one_kronecker_one, one_kronecker_one]

/-- The Kraus operators of the read ports, with their trivial public register. -/
noncomputable def hwReadKraus : (c : HwRead X Z M) → c.Result →
    Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ
  | .readH z upd, r => (1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausH z upd r
  | .readK x upd, r => (1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausK x upd r
  | .readK' x upd, r => (1 : Matrix Unit Unit ℂ) ⊗ₖ readKrausK' x upd r

/-- The Kraus operators of the program ports, with their trivial public register. -/
noncomputable def hwProgKraus : (c : HwProg X Z) → c.Result →
    Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ
  | .programH z v, r => (1 : Matrix Unit Unit ℂ) ⊗ₖ programKrausH z v r
  | .programK x v, r => (1 : Matrix Unit Unit ℂ) ⊗ₖ programKrausK x v r
  | .programK' x v, r => (1 : Matrix Unit Unit ℂ) ⊗ₖ programKrausK' x v r

/-- The read ports as subinstruments: complete families of Kraus operators. -/
noncomputable def hwReadStep [Nonempty X] [Nonempty Z] :
    (c : HwRead X Z M) → SubInstrument (Unit × HwReg X Z M) (Unit × HwReg X Z M) c.Result
  | .readH z upd => SubInstrument.ofKraus (hwReadKraus (.readH z upd)) (sum_readKrausH z upd)
  | .readK x upd => SubInstrument.ofKraus (hwReadKraus (.readK x upd)) (sum_readKrausK x upd)
  | .readK' x upd => SubInstrument.ofKraus (hwReadKraus (.readK' x upd)) (sum_readKrausK' x upd)

/-- The program ports as subinstruments: complete families of Kraus operators. -/
noncomputable def hwProgStep :
    (c : HwProg X Z) → SubInstrument (Unit × HwReg X Z M) (Unit × HwReg X Z M) c.Result
  | .programH z v => SubInstrument.ofKraus (hwProgKraus (.programH z v)) (sum_programKrausH z v)
  | .programK x v => SubInstrument.ofKraus (hwProgKraus (.programK x v)) (sum_programKrausK x v)
  | .programK' x v => SubInstrument.ofKraus (hwProgKraus (.programK' x v))
      (sum_programKrausK' x v)

/-- The branches of a read port are the Kraus maps of `hwReadKraus`. -/
theorem hwReadStep_branch [Nonempty X] [Nonempty Z] (c : HwRead X Z M) (r : c.Result) :
    (hwReadStep c).branch r = MatrixMap.conj (hwReadKraus c r) := by
  cases c <;> rfl

/-- The branches of a program port are the Kraus maps of `hwProgKraus`. -/
theorem hwProgStep_branch (c : HwProg X Z) (r : c.Result) :
    (hwProgStep (M := M) c).branch r = MatrixMap.conj (hwProgKraus c r) := by
  cases c <;> rfl

/-! ## The sponge ports -/

variable [AddCommGroup X] [AddCommGroup Z]

variable (X Z M) in
/-- Compressing every database cell of the hardwired register. -/
noncomputable def compressReg : Matrix (HwReg X Z M) (HwReg X Z M) ℂ :=
  compressDbs X Z ⊗ₖ (1 : Matrix (Hw X Z × M) (Hw X Z × M) ℂ)

omit [Fintype M] [DecidableEq M] [AddCommGroup X] [AddCommGroup Z] in
theorem conjTranspose_compressReg [Fintype M] [DecidableEq M] :
    (compressReg X Z M)ᴴ = compressReg X Z M := by
  rw [compressReg, conjTranspose_kronecker, conjTranspose_compressDbs, conjTranspose_one]

theorem compressReg_mul_self : compressReg X Z M * compressReg X Z M = 1 := by
  rw [compressReg, ← mul_kronecker_mul, compressDbs_mul_self, Matrix.one_mul, one_kronecker_one]

/-- A port of the hardwired runtime: the table oracle of `read` conjugated by the compression of
every database cell. -/
noncomputable def hwPort {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] (read : HwReg X Z M → A → Y) :
    Matrix ((A × Y) × HwReg X Z M) ((A × Y) × HwReg X Z M) ℂ :=
  ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M) * tableOracle read *
    ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M)

theorem hwPort_mem_unitaryGroup {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y]
    [DecidableEq Y] [AddCommGroup Y] (read : HwReg X Z M → A → Y) :
    hwPort read ∈ unitaryGroup ((A × Y) × HwReg X Z M) ℂ := by
  have hCh : ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M)ᴴ =
      (1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M := by
    rw [conjTranspose_kronecker, conjTranspose_one, conjTranspose_compressReg]
  have hCC : ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M) *
      ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M) = 1 := by
    rw [← mul_kronecker_mul, Matrix.one_mul, compressReg_mul_self, one_kronecker_one]
  have hC : ∀ N : Matrix ((A × Y) × HwReg X Z M) ((A × Y) × HwReg X Z M) ℂ,
      ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M) *
        (((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M) * N) = N := fun N ↦ by
    rw [← Matrix.mul_assoc, hCC, Matrix.one_mul]
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, hwPort]
  simp only [conjTranspose_mul, hCh, Matrix.mul_assoc, hC]
  rw [← Matrix.mul_assoc (tableOracle read)ᴴ, conjTranspose_tableOracle_mul_self, Matrix.one_mul,
    hCC]

variable (X Z) in
/-- **The hardwired sponge oracles.** The register holds the databases, the hardwired cells and the
memory, started at `(∅, W₀, m₀)`; port `h` answers `|z, x⟩ ↦ |z, x + W z⟩` on a hardwired cell `z`
and as the compressed oracle on the others, and likewise `k` and `k'`. -/
@[reducible]
noncomputable def spongeHardwired (W₀ : Hw X Z) (m₀ : M) :
    EmulatedOracle SpongePort (spongeIn X Z) where
  S := QReg.of (HwReg X Z M)
  init := SubState.basis ((Database.empty, Database.empty, Database.empty), W₀, m₀)
  U
    | .h => hwPort fun s : HwReg X Z M ↦ fun z ↦ (s.2.1.1 z).getD (s.1.1.lookup z)
    | .k => hwPort fun s : HwReg X Z M ↦ fun x ↦ (s.2.1.2.1 x).getD (s.1.2.1.lookup x)
    | .k' => hwPort fun s : HwReg X Z M ↦ fun x ↦ (s.2.1.2.2 x).getD (s.1.2.2.lookup x)
  unitary
    | .h => hwPort_mem_unitaryGroup _
    | .k => hwPort_mem_unitaryGroup _
    | .k' => hwPort_mem_unitaryGroup _

variable (X Z) in
/-- **Runtime 1.** The sponge ports of `spongeHardwired` and the read ports of `hwReadStep`, on
one register started at `(∅, W₀, m₀)`. -/
noncomputable def spongeHardwiredReadRuntime (W₀ : Hw X Z) (m₀ : M) :
    QuantumRuntime (hwReadSpec X Z M) :=
  ((spongeHardwired X Z W₀ m₀).toRuntime : QuantumRuntime (spongeSpec X Z)).extend
    (t := hwReadCmdSpec X Z M) hwReadStep

variable (X Z) in
/-- **The hardwired runtime.** Runtime 1 with the program ports of `hwProgStep`. -/
noncomputable def spongeHardwiredRuntime (W₀ : Hw X Z) (m₀ : M) : QuantumRuntime (hwSpec X Z M) :=
  (spongeHardwiredReadRuntime X Z W₀ m₀).extend (t := hwProgSpec X Z) hwProgStep

theorem spongeHardwiredRuntime_step_sponge (W₀ : Hw X Z) (m₀ : M) (i : SpongePort) (r : Unit) :
    ((spongeHardwiredRuntime X Z W₀ m₀).step (.inl (.inl i))).branch r =
      MatrixMap.conj ((spongeHardwired X Z W₀ m₀).U i) :=
  (spongeHardwired X Z W₀ m₀).toRuntime_step_branch i r

theorem spongeHardwiredRuntime_step_read (W₀ : Hw X Z) (m₀ : M) (c : HwRead X Z M)
    (r : c.Result) :
    ((spongeHardwiredRuntime X Z W₀ m₀).step (.inl (.inr c))).branch r =
      MatrixMap.conj (hwReadKraus c r) :=
  hwReadStep_branch c r

theorem spongeHardwiredRuntime_step_prog (W₀ : Hw X Z) (m₀ : M) (c : HwProg X Z)
    (r : c.Result) :
    ((spongeHardwiredRuntime X Z W₀ m₀).step (.inr c)).branch r =
      MatrixMap.conj (hwProgKraus c r) :=
  hwProgStep_branch c r

end Quantum.Sponge

end
