module

public import LeanVMCircuits.Rec.Relax
public import LeanVMCircuits.Rec.TreeSound

@[expose] public section

/-!
The tree's edges, from the dumps: a node's circuit reads each child's statement words as the claims that statement makes on the polynomials and matrices, scaled as the child's kind requires.

A node circuit hints each child's statement (`Design::node`), one `E` word per position of the statement's layout (`StatementLayout`: the kind, the digest's two halves, the dense point, each dense polynomial's value, the matrices' row and column points, each flock circuit's two matrix values), and its reduction takes, with the claims of its own proofs, the claims the child's statement carries (`Design::carried`): on each dense polynomial, at its prefix of the point, its value, scaled for the circuits' fixed polynomials by whether the child is a node; on each flock circuit's two matrices, at its prefixes of the row and column points, their values. A dump marks the layout (`edge layout`), each child's statement words (`edge child`) and the claims the reduction takes (`edge dense`, `edge term`, `edge matrix`, `edge row`, `edge col`).

An edge certificate (`EdgeCert`) records them with the calls that compute each child's scale from its kind word (`ScaleCert`) and the call that reads its digest. `EdgeCert.accepts` checks the layout fits, each child has the layout's words, its scale is computed from its kind word as the tier computes it, its digest is read from its digest words, and every claim the child's words make (`stmtClaims`, at the scale's wire) is one the reduction takes.

`EdgeCert.edge`: in any assignment satisfying the circuit the calls build, if a child's words carry statement `st`, every claim `st` makes at its kind's scale (`nodeScale`) is among the claims the reduction takes, and the digest the circuit reads is `st`'s. `EdgeCert.edge_holds`: when those claims hold, `st`'s do. `hedge_of_certs` gives `TreeSound.tree_sound`'s edge premise for a tree whose circuits have accepted certificates, reading a node's input claims as its reduction's and a node's statement as its words' claims; `tree_sound_certs` is `tree_sound` with it.

The parent verifies the child's proof with these words as its statement: `InstCert` names the calls by which the child's verifier (`RecShape::verify`) absorbs them as its transcript's instance and reads them into its public table's columns (`FixedHints::statement_at`), and `InstCert.verifies` proves that in any satisfying assignment those are the words' instance and limbs (`InstCert.VerifiesAt`). A child's statement is therefore the words its parent's verifier reads (`treeStmt`), and `tree_sound_certs` assumes, in place of a link between those words and the child's statement, the recursive verifier's soundness at the statement it reads (`hrec`); `sat_tree` gives every node's circuit satisfied at its `treeStmt`.
-/

namespace LeanVMCircuits.Rec.Edges

open LeanVMCircuits.Rec Model

/-! Claims, over wires or values. -/

/-- One claim on a dense polynomial (`DenseTerm`): the shared prefix's first `nLow` coordinates, then public bits, then `top`, scaled by `scale` when present. -/
structure Term (α : Type) where
  nLow : ℕ
  bits : ℕ
  bitsLen : ℕ
  top : List α
  scale : Option α
  value : α
  deriving DecidableEq, Repr

/-- Claims on one dense polynomial at points sharing a prefix (`DenseClaim`). -/
structure Dense (α : Type) where
  poly : ℕ
  low : List α
  terms : List (Term α)
  deriving DecidableEq, Repr

/-- A matrix's coefficient in a matrix claim (`Coefficient`). -/
inductive Coef (α : Type) where
  | zero
  | one
  | of (x : α)
  deriving DecidableEq, Repr

/-- A matrix claim's row weight (`RowWeight`). -/
inductive RowW (α : Type) where
  | skip (z : α) (rest : List α)
  | point (p : List α)
  deriving DecidableEq, Repr

/-- A matrix claim's column weight (`ColWeight`). -/
inductive ColW (α : Type) where
  | slices (s rest : List α)
  | point (p : List α)
  deriving DecidableEq, Repr

/-- A claim on a flock circuit's matrices (`MatrixClaim`). -/
structure Matrix (α : Type) where
  circuit : ℕ
  row : RowW α
  col : ColW α
  coefs : Coef α × Coef α
  value : α
  deriving DecidableEq, Repr

/-- What a reduction takes: its dense and matrix claims (`NodeClaims`, without the bound values). -/
structure Claims (α : Type) where
  dense : List (Dense α) := []
  matrices : List (Matrix α) := []
  deriving DecidableEq, Repr

variable {α β : Type}

def Term.map (f : α → β) (t : Term α) : Term β := ⟨t.nLow, t.bits, t.bitsLen, t.top.map f, t.scale.map f, f t.value⟩
def Dense.map (f : α → β) (d : Dense α) : Dense β := ⟨d.poly, d.low.map f, d.terms.map (Term.map f)⟩
def Coef.map (f : α → β) : Coef α → Coef β
  | .zero => .zero
  | .one => .one
  | .of x => .of (f x)
def RowW.map (f : α → β) : RowW α → RowW β
  | .skip z rest => .skip (f z) (rest.map f)
  | .point p => .point (p.map f)
def ColW.map (f : α → β) : ColW α → ColW β
  | .slices s rest => .slices (s.map f) (rest.map f)
  | .point p => .point (p.map f)
def Matrix.map (f : α → β) (m : Matrix α) : Matrix β :=
  ⟨m.circuit, m.row.map f, m.col.map f, (m.coefs.1.map f, m.coefs.2.map f), f m.value⟩
def Claims.map (f : α → β) (c : Claims α) : Claims β := ⟨c.dense.map (Dense.map f), c.matrices.map (Matrix.map f)⟩

/-- Claims are true under a reading `tD`, `tM` of each dense and matrix claim: the polynomials' and matrices' values at an outcome. -/
def Claims.Holds (tD : Dense β → Prop) (tM : Matrix β → Prop) (c : Claims β) : Prop :=
  (∀ d ∈ c.dense, tD d) ∧ ∀ m ∈ c.matrices, tM m

/-- Every claim of `a` is one of `b`'s. -/
def Claims.Sub (a b : Claims β) : Prop := (∀ d ∈ a.dense, d ∈ b.dense) ∧ ∀ m ∈ a.matrices, m ∈ b.matrices

theorem Claims.Holds.of_sub {tD : Dense β → Prop} {tM : Matrix β → Prop} {a b : Claims β} (h : b.Holds tD tM)
    (hs : a.Sub b) : a.Holds tD tM :=
  ⟨fun d hd => h.1 d (hs.1 d hd), fun m hm => h.2 m (hs.2 m hm)⟩

/-! A statement's layout and the claims its words make. -/

/-- `StatementLayout` with the prefixes its claims are at: the dense point's and matrix points' widths, how many dense polynomials and flock circuits, each dense polynomial's variables and each flock circuit's matrix variables. -/
structure Layout where
  nDense : ℕ
  nPolys : ℕ
  nMatrix : ℕ
  nFlocks : ℕ
  vars : List ℕ
  klog : List ℕ
  deriving DecidableEq, Repr, Inhabited

namespace Layout

/-- Where the dense values start: after the kind, the digest's two halves and the dense point. -/
def dv (L : Layout) : ℕ := 3 + L.nDense
def rowsAt (L : Layout) : ℕ := L.dv + L.nPolys
def colsAt (L : Layout) : ℕ := L.rowsAt + L.nMatrix
def matsAt (L : Layout) : ℕ := L.colsAt + L.nMatrix
/-- How many words a statement has. -/
def len (L : Layout) : ℕ := L.matsAt + 2 * L.nFlocks

/-- A prefix length for each dense polynomial and flock circuit, within its point. -/
def ok (L : Layout) : Bool :=
  L.vars.length == L.nPolys && L.klog.length == L.nFlocks && L.vars.all (· ≤ L.nDense) &&
    L.klog.all (· ≤ L.nMatrix)

end Layout

/-- Whether a dense polynomial holds circuits' fixed columns (`DensePoly::is_fixed`: `Fixed` and `Wide`). -/
def isFixed (p : ℕ) : Bool := 2 ≤ p

/-- The claim words `x` make on dense polynomial `p` (`Design::carried`): at the point's first `vars p` coordinates, its value, scaled by `σ` on a fixed polynomial. -/
def stmtDense (L : Layout) (x : ℕ → β) (σ : β) (p : ℕ) : Dense β where
  poly := p
  low := (List.range (L.vars.getD p 0)).map fun i => x (3 + i)
  terms := [{ nLow := L.vars.getD p 0, bits := 0, bitsLen := 0, top := [],
              scale := if isFixed p then some σ else none, value := x (L.dv + p) }]

/-- The claim words `x` make on flock circuit `f`'s matrix `k` (`MatrixClaim::carried`): at the row and column points' first `klog f` coordinates, its value. -/
def stmtMatrix (L : Layout) (x : ℕ → β) (f k : ℕ) : Matrix β where
  circuit := f
  row := .point ((List.range (L.klog.getD f 0)).map fun i => x (L.rowsAt + i))
  col := .point ((List.range (L.klog.getD f 0)).map fun i => x (L.colsAt + i))
  coefs := if k = 0 then (.one, .zero) else (.zero, .one)
  value := x (L.matsAt + 2 * f + k)

/-- Every claim a statement's words `x` make, fixed polynomials' claims scaled by `σ`. -/
def stmtClaims (L : Layout) (x : ℕ → β) (σ : β) : Claims β where
  dense := (List.range L.nPolys).map (stmtDense L x σ)
  matrices := (List.range L.nFlocks).flatMap fun f => [stmtMatrix L x f 0, stmtMatrix L x f 1]

theorem stmtClaims_map (L : Layout) (x : ℕ → α) (σ : α) (f : α → β) :
    (stmtClaims L x σ).map f = stmtClaims L (f ∘ x) (f σ) := by
  simp only [Claims.map, stmtClaims, List.map_map, List.map_flatMap, List.map_cons, List.map_nil, Claims.mk.injEq]
  constructor
  · apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply, Dense.map, stmtDense, List.map_map, List.map_cons, List.map_nil, Term.map,
      Dense.mk.injEq, true_and, List.cons.injEq, Term.mk.injEq, and_true]
    refine ⟨rfl, ?_⟩
    split <;> rfl
  · apply List.flatMap_congr
    intro g _
    simp only [Matrix.map, stmtMatrix, RowW.map, ColW.map, List.map_map, Function.comp_apply]
    congr 2

theorem getD_le {xs : List ℕ} {n i : ℕ} (h : xs.all (· ≤ n) = true) : xs.getD i 0 ≤ n := by
  rw [List.getD_eq_getElem?_getD]
  cases hx : xs[i]? with
  | none => simp
  | some a =>
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    exact h a (List.mem_of_getElem? hx)

/-- A statement's claims read only its words. -/
theorem stmtClaims_congr {L : Layout} (hL : L.ok = true) {x y : ℕ → β} (σ : β) (h : ∀ i < L.len, x i = y i) :
    stmtClaims L x σ = stmtClaims L y σ := by
  simp only [Layout.ok, Bool.and_eq_true, beq_iff_eq] at hL
  obtain ⟨⟨⟨-, -⟩, hv⟩, hk⟩ := hL
  simp only [Layout.len, Layout.matsAt, Layout.colsAt, Layout.rowsAt, Layout.dv] at h
  simp only [stmtClaims, Claims.mk.injEq]
  constructor
  · apply List.map_congr_left
    intro p hp
    rw [List.mem_range] at hp
    have hvp := getD_le (i := p) hv
    simp only [stmtDense, Dense.mk.injEq, List.cons.injEq, Term.mk.injEq, and_true, true_and]
    refine ⟨List.map_congr_left fun i hi => h _ ?_, h _ (by simp only [Layout.dv]; omega)⟩
    rw [List.mem_range] at hi
    omega
  · apply List.flatMap_congr
    intro f hf
    rw [List.mem_range] at hf
    have hkf := getD_le (i := f) hk
    have hm : ∀ k < 2, stmtMatrix L x f k = stmtMatrix L y f k := by
      intro k hk2
      simp only [stmtMatrix, Matrix.mk.injEq, RowW.point.injEq, ColW.point.injEq, true_and]
      refine ⟨List.map_congr_left fun i hi => h _ ?_, List.map_congr_left fun i hi => h _ ?_, h _ ?_⟩
      · rw [List.mem_range] at hi; simp only [Layout.rowsAt, Layout.dv]; omega
      · rw [List.mem_range] at hi; simp only [Layout.colsAt, Layout.rowsAt, Layout.dv]; omega
      · simp only [Layout.matsAt, Layout.colsAt, Layout.rowsAt, Layout.dv]; omega
    rw [hm 0 (by omega), hm 1 (by omega)]

/-! A child's scale: one, or whether it is a node, from its kind word. -/

/-- How a tier computes a child's scale from its kind word (`Design::kind_bits`). -/
inductive Mode where
  /-- Two kinds: the kind word is the bit. -/
  | kind
  /-- The large tier, whose children are all nodes: one. -/
  | one
  /-- `b` index bits: one plus the product of each low bit plus one. -/
  | bits (b : ℕ)
  deriving DecidableEq, Repr

/-- Bit `k` of a word's first limb, in `K`. -/
noncomputable def bitK (x : Fin 4 → K) (k : ℕ) : K := if (toWord (x 0)).testBit k then 1 else 0

/-- The product of each of the first `k` bits plus one: one when they are all zero, else zero. -/
noncomputable def firstProd (x : Fin 4 → K) : ℕ → E
  | 0 => 1
  | k + 1 => firstProd x k * (emb (bitK x k) + 1)

/-- The scale of a child of kind word `x`. -/
noncomputable def nodeScale : Mode → (Fin 4 → K) → E
  | .kind, x => toE (x 0) (x 1) (x 2)
  | .one, _ => 1
  | .bits b, x => firstProd x b + 1

/-- A statement word's `E` element. -/
noncomputable def stE (st : ℕ → Fin 4 → K) (i : ℕ) : E := toE (st i 0) (st i 1) (st i 2)

/-- Output `k` of call `j`. -/
def out (os : Array (List ℕ)) (j k : ℕ) : ℕ := (os.getD j []).getD k 0

/-- Where a circuit computes a child's scale: its kind word itself, a `one` call's output, or for `bits` the `one` call, the kind's `e_to_k` and its first limb's `split`, per bit its `k_to_e1`, the `add` of one and the `mul` into the product, and the last `add` of one. -/
inductive ScaleCert where
  | kind
  | one (call : ℕ)
  | bits (one eToK split last : ℕ) (steps : List (ℕ × ℕ × ℕ))
  deriving DecidableEq, Repr, Inhabited

def ScaleCert.mode : ScaleCert → Mode
  | .kind => .kind
  | .one _ => .one
  | .bits _ _ _ _ steps => .bits steps.length

/-- The product's wire after `k` bits, from the one wire `o`. -/
def accAt (os : Array (List ℕ)) (o : ℕ) (steps : List (ℕ × ℕ × ℕ)) : ℕ → ℕ
  | 0 => o
  | k + 1 => out os (steps.getD k (0, 0, 0)).2.2 0

/-- The scale's wire, for kind word `kw`. -/
def ScaleCert.wire (os : Array (List ℕ)) (kw : ℕ) : ScaleCert → ℕ
  | .kind => kw
  | .one c => out os c 0
  | .bits _ _ _ last _ => out os last 0

/-- The named calls compute the scale from kind word `kw`. -/
def ScaleCert.ok (cs : Array Call) (os : Array (List ℕ)) (kw : ℕ) : ScaleCert → Bool
  | .kind => true
  | .one c => cs[c]? == some .one
  | .bits o e s last steps =>
    let one := out os o 0
    cs[o]? == some .one && cs[e]? == some (.eToK kw) && cs[s]? == some (.split (out os e 0)) &&
      steps.length ≤ 64 &&
      (List.range steps.length).all (fun k =>
        let (a, p, m) := steps.getD k (0, 0, 0)
        cs[a]? == some (.kToE1 (out os s k)) && cs[p]? == some (.add (out os a 0) one) &&
          cs[m]? == some (.mul (accAt os one steps k) (out os p 0))) &&
      cs[last]? == some (.add (accAt os one steps steps.length) one)

/-- Every call holds its contract. -/
def AllHold (cs : Array Call) (os : Array (List ℕ)) (st : ℕ → Fin 4 → K) (val : Val) : Prop :=
  ∀ j (hj : j < cs.size), cs[j].Holds st val (os.getD j [])

theorem holds_at {cs : Array Call} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val} (hF : AllHold cs os st val)
    {j : ℕ} {c : Call} (h : cs[j]? = some c) : c.Holds st val (os.getD j []) := by
  obtain ⟨hj, rfl⟩ := Array.getElem?_eq_some_iff.mp h
  exact hF j hj

/-- The scale's wire carries `nodeScale` of the kind word. -/
theorem ScaleCert.sem {cs : Array Call} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}
    (hF : AllHold cs os st val) (sc : ScaleCert) (kw : ℕ) (h : sc.ok cs os kw = true) :
    Model.ev val (sc.wire os kw) = nodeScale sc.mode (val kw) := by
  cases sc with
  | kind => rfl
  | one c =>
    simp only [ScaleCert.ok, beq_iff_eq] at h
    exact holds_at hF h
  | bits o e s last steps =>
    simp only [ScaleCert.ok, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range]
      at h
    obtain ⟨⟨⟨⟨⟨ho, he⟩, hs⟩, h64⟩, hsteps⟩, hlast⟩ := h
    have hone : Model.ev val (out os o 0) = 1 := holds_at hF ho
    have hE : ∀ i : Fin 4, i.val < 3 → val (out os e i) 0 = val kw i := holds_at hF he
    obtain ⟨hbit, hword⟩ : (∀ i < 64, val (out os s i) 0 = 0 ∨ val (out os s i) 0 = 1) ∧
        toWord (val (out os e 0) 0) = num (fun i => if val (out os s i) 0 = 1 then 1 else 0) 64 :=
      holds_at hF hs
    have hw : toWord (val kw 0) = num (fun i => if val (out os s i) 0 = 1 then 1 else 0) 64 := by
      rw [← hword]; exact congrArg toWord (hE 0 (by decide)).symm
    have hacc : ∀ k ≤ steps.length, Model.ev val (accAt os (out os o 0) steps k) = firstProd (val kw) k := by
      intro k hk
      induction k with
      | zero => exact hone
      | succ k ih =>
        have hk' : k < steps.length := by omega
        obtain ⟨⟨ha, hp⟩, hm⟩ := hsteps k hk'
        have hA : Model.ev val (out os (steps.getD k (0, 0, 0)).1 0) = emb (val (out os s k) 0) := holds_at hF ha
        have hP : Model.ev val (out os (steps.getD k (0, 0, 0)).2.1 0) =
            Model.ev val (out os (steps.getD k (0, 0, 0)).1 0) + Model.ev val (out os o 0) := holds_at hF hp
        have hM : Model.ev val (out os (steps.getD k (0, 0, 0)).2.2 0) =
            Model.ev val (accAt os (out os o 0) steps k) * Model.ev val (out os (steps.getD k (0, 0, 0)).2.1 0) :=
          holds_at hF hm
        have hb : val (out os s k) 0 = bitK (val kw) k := by
          have hk64 : k < 64 := by omega
          have ht := congrArg (fun n => Nat.testBit n k) hw
          simp only [testBit_num _ 64 k hk64] at ht
          have z1 : (0 : ZMod 2) ≠ 1 := by decide
          unfold bitK
          rcases hbit k hk64 with e | e <;> simp_all
        show Model.ev val (out os (steps.getD k (0, 0, 0)).2.2 0) =
          firstProd (val kw) k * (emb (bitK (val kw) k) + 1)
        rw [hM, ih (by omega), hP, hA, hone, hb]
    show Model.ev val (out os last 0) = firstProd (val kw) steps.length + 1
    have hL : Model.ev val (out os last 0) =
        Model.ev val (accAt os (out os o 0) steps steps.length) + Model.ev val (out os o 0) :=
      holds_at hF hlast
    rw [hL, hacc _ le_rfl, hone]

/-! The child's verifier reads the child's words as its statement. -/

/-- Limb `c` of a statement word as `Design::node` passes it to the child's verifier (`[c0, c1, c2, zero]`): its first three limbs, then zero. -/
noncomputable def limbK (x : Fin 4 → K) (c : ℕ) : K := if h : c < 3 then x ⟨c, by omega⟩ else ofWord 0

/-- Word `i` of the instance a verifier absorbs for a statement `s` of `n` words (`RecShape::verify`'s, the native verifier's `instance`): the limb count `4 n`, then each word's four limbs. -/
noncomputable def instAt (s : ℕ → Fin 4 → K) (n i : ℕ) : BitVec 64 :=
  if i = 0 then BitVec.ofNat 64 (4 * n) else BitVec.ofNat 64 (toWord (limbK (s ((i - 1) / 4)) ((i - 1) % 4)))

/-- Where a parent's verifier of a child (`RecShape::verify`) reads the child's words as its statement: each word's `e_to_k` call, the `k_const` calls of the limb count and of the zero limb, the `d_const` call starting its transcript, the `leaf_block` calls absorbing the instance, and the statement's shares of the public table's columns (`FixedHints::statement_at`), each a limb, the `zero` call it starts from and one `mul_k_add` call per word. -/
structure InstCert where
  limbs : List ℕ
  count : ℕ
  zero : ℕ
  seed : ℕ
  blocks : List ℕ
  shares : List (ℕ × ℕ × List ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- The wire of word `z`'s limb `c`. -/
def InstCert.limbWire (ic : InstCert) (os : Array (List ℕ)) (z c : ℕ) : ℕ :=
  if c < 3 then out os (ic.limbs.getD z 0) c else out os ic.zero 0

/-- The wire of the instance's word `i`. -/
def InstCert.msg (ic : InstCert) (os : Array (List ℕ)) (i : ℕ) : ℕ :=
  if i = 0 then out os ic.count 0 else ic.limbWire os ((i - 1) / 4) ((i - 1) % 4)

/-- The chaining value block `b` of the transcript starts from: the `d_const`'s output, then the previous block's. -/
def InstCert.cvIn (ic : InstCert) (os : Array (List ℕ)) (b : ℕ) : ℕ :=
  if b = 0 then out os ic.seed 0 else out os (ic.blocks.getD (b - 1) 0) 0

/-- A share's accumulator after `z` words: its `zero` call's output, then the `z`th `mul_k_add`'s. -/
def accW (os : Array (List ℕ)) (z0 : ℕ) (ms : List ℕ) (z : ℕ) : ℕ :=
  if z = 0 then out os z0 0 else out os (ms.getD (z - 1) 0) 0

/-- The weight a share's `z`th `mul_k_add` gives its word. -/
def weightW (cs : Array Call) (ms : List ℕ) (z : ℕ) : ℕ :=
  match cs[ms.getD z 0]? with
  | some (.mulKAdd a _ _) => a
  | _ => 0

/-- Whether call `j` starts the transcript at a constant. -/
def isDConst (cs : Array Call) (j : ℕ) : Bool :=
  match cs[j]? with
  | some (.dConst _) => true
  | _ => false

/-- Block `b` is a `leaf_block` from its chaining value. -/
def InstCert.blockOk (cs : Array Call) (os : Array (List ℕ)) (ic : InstCert) (b : ℕ) : Bool :=
  match cs[ic.blocks.getD b 0]? with
  | some (.leafBlock h _ _ _) => h == ic.cvIn os b
  | _ => false

/-- The instance's word `i` is the `i % 8`th message word of block `i / 8`. -/
def InstCert.msgOk (cs : Array Call) (os : Array (List ℕ)) (ic : InstCert) (i : ℕ) : Bool :=
  match cs[ic.blocks.getD (i / 8) 0]? with
  | some (.leafBlock _ m _ _) => m.getD (i % 8) 0 == ic.msg os i
  | _ => false

/-- A share reads limb `c` of each word, in order, from a `zero`. -/
def shareOk (cs : Array Call) (os : Array (List ℕ)) (ic : InstCert) (n : ℕ) (sh : ℕ × ℕ × List ℕ) : Bool :=
  cs[sh.2.1]? == some .zero && sh.2.2.length == n &&
    (List.range n).all fun z => match cs[sh.2.2.getD z 0]? with
      | some (.mulKAdd _ k d) => k == ic.limbWire os z sh.1 && d == accW os sh.2.1 sh.2.2 z
      | _ => false

/-- The certificate checks against the child's words: each word's limbs are its `e_to_k`'s, the count is `4 n`, the transcript starts at a constant and its blocks chain, the instance is their first `4 n + 1` message words, and each of the four limbs has a share reading it. -/
def InstCert.ok (cs : Array Call) (os : Array (List ℕ)) (words : List ℕ) (ic : InstCert) : Bool :=
  let n := words.length
  ic.limbs.length == n && decide (4 * n < 2 ^ 64) &&
    (List.range n).all (fun z => cs[ic.limbs.getD z 0]? == some (.eToK (words.getD z 0))) &&
    cs[ic.count]? == some (.kConst (4 * n)) && cs[ic.zero]? == some (.kConst 0) && isDConst cs ic.seed &&
    (List.range ic.blocks.length).all (ic.blockOk cs os) && (List.range (4 * n + 1)).all (ic.msgOk cs os) &&
    (List.range 4).all (fun c => ic.shares.any (·.1 == c)) && ic.shares.all (shareOk cs os ic n)

/-- What the parent's verifier reads as the child's statement is `s`: the transcript's first `4 n + 1` absorbed words are `s`'s instance, and each share is the sum over `s`'s words of their limb at the share's weights. -/
def InstCert.VerifiesAt (cs : Array Call) (os : Array (List ℕ)) (ic : InstCert) (val : Val) (s : ℕ → Fin 4 → K)
    (n : ℕ) : Prop :=
  (∀ i < 4 * n + 1, w64 val (ic.msg os i) = instAt s n i) ∧
    ∀ sh ∈ ic.shares, Model.ev val (accW os sh.2.1 sh.2.2 n) =
      ∑ z ∈ Finset.range n, Model.ev val (weightW cs sh.2.2 z) * emb (limbK (s z) sh.1)

theorem InstCert.limb_sem {cs : Array Call} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}
    (hF : AllHold cs os st val) {words : List ℕ} {ic : InstCert} (h : ic.ok cs os words = true) {z c : ℕ}
    (hz : z < words.length) : val (ic.limbWire os z c) 0 = limbK (val (words.getD z 0)) c := by
  simp only [InstCert.ok, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hl⟩, -⟩, hzero⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  unfold InstCert.limbWire limbK
  split_ifs with hc
  · have H : ∀ i : Fin 4, i.val < 3 → val (out os (ic.limbs.getD z 0) i) 0 = val (words.getD z 0) i :=
      holds_at hF (hl z hz)
    exact H ⟨c, by omega⟩ hc
  · have H : val (out os ic.zero 0) = limbsOf [0, 0, 0, 0] := holds_at hF hzero
    rw [H]; rfl

/-- A checked certificate's words are what the parent's verifier reads as the child's statement. -/
theorem InstCert.verifies {cs : Array Call} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}
    (hF : AllHold cs os st val) {words : List ℕ} {ic : InstCert} (h : ic.ok cs os words = true) :
    ic.VerifiesAt cs os val (fun z => val (words.getD z 0)) words.length := by
  have h' := h
  simp only [InstCert.ok, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, h64⟩, -⟩, hcount⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hsh⟩ := h'
  refine ⟨fun i hi => ?_, fun sh hm => ?_⟩
  · unfold InstCert.msg instAt
    split_ifs with h0
    · have H : val (out os ic.count 0) = limbsOf [4 * words.length, 0, 0, 0] := holds_at hF hcount
      simp only [w64, H, limbsOf]
      exact congrArg (BitVec.ofNat 64) (toWord_ofWord _ h64)
    · simp only [w64]
      rw [ic.limb_sem hF h (by omega)]
  · have hs := hsh sh hm
    simp only [shareOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hs
    obtain ⟨⟨hz, -⟩, hms⟩ := hs
    have key : ∀ z ≤ words.length, Model.ev val (accW os sh.2.1 sh.2.2 z) =
        ∑ z' ∈ Finset.range z, Model.ev val (weightW cs sh.2.2 z') * emb (limbK (val (words.getD z' 0)) sh.1) := by
      intro z hzl
      induction z with
      | zero =>
        have H : Model.ev val (out os sh.2.1 0) = 0 := holds_at hF hz
        simpa [accW] using H
      | succ z ih =>
        have hm := hms z (by omega)
        rw [Finset.sum_range_succ, ← ih (by omega)]
        revert hm
        unfold weightW
        split
        · next a k d heq =>
          intro hm
          simp only [Bool.and_eq_true, beq_iff_eq] at hm
          obtain ⟨rfl, rfl⟩ := hm
          have H : Model.ev val (out os (sh.2.2.getD z 0) 0) =
              Model.ev val a * emb (val (ic.limbWire os z sh.1) 0) + Model.ev val (accW os sh.2.1 sh.2.2 z) :=
            holds_at hF heq
          have hA : accW os sh.2.1 sh.2.2 (z + 1) = out os (sh.2.2.getD z 0) 0 := by simp [accW]
          rw [hA, H, ic.limb_sem hF h (by omega), add_comm]
        · intro hm; simp at hm
    exact key _ le_rfl

/-! The certificate. -/

/-- A child's edge: its statement's words, the calls computing its scale, the `halves_to_d` call reading its digest, and where its verifier reads its words. -/
structure ChildEdge where
  words : List ℕ
  scale : ScaleCert
  digest : ℕ
  inst : InstCert
  deriving DecidableEq, Repr, Inhabited

/-- A circuit's edges: its calls, its statement's layout, the claims its reduction takes and its children. -/
structure EdgeCert where
  calls : Array Call
  layout : Layout
  claims : Claims ℕ
  children : List ChildEdge

/-- The claims a child's words make, at its scale's wire. -/
def ChildEdge.claims (L : Layout) (os : Array (List ℕ)) (ch : ChildEdge) : Claims ℕ :=
  stmtClaims L (fun i => ch.words.getD i 0) (ch.scale.wire os (ch.words.getD 0 0))

/-- A child's edge checks: its words are the layout's, its scale is computed from its kind word, its digest is read from its digest words, and the claims its words make are among those the reduction takes. -/
def ChildEdge.ok (c : EdgeCert) (os : Array (List ℕ)) (ch : ChildEdge) : Bool :=
  ch.words.length == c.layout.len && ch.scale.ok c.calls os (ch.words.getD 0 0) &&
    c.calls[ch.digest]? == some (.halvesToD (ch.words.getD 1 0) (ch.words.getD 2 0)) &&
    (ch.claims c.layout os).dense.all (fun d => decide (d ∈ c.claims.dense)) &&
    (ch.claims c.layout os).matrices.all (fun m => decide (m ∈ c.claims.matrices))

/-- The verdict on the outputs `os` of the certificate's calls. -/
def EdgeCert.accepts (c : EdgeCert) (os : Array (List ℕ)) : Bool :=
  c.layout.ok && c.children.all (ChildEdge.ok c os)

/-- Each child's verifier reads the child's words as its statement. -/
def EdgeCert.verifies (c : EdgeCert) (os : Array (List ℕ)) : Bool :=
  c.children.all fun ch => ch.inst.ok c.calls os ch.words

/-- The replay's verdict: the calls replay with every equality, building a circuit of the layout's statement length, the certificate accepts their outputs, and each child's verifier reads its words. -/
def EdgeCert.check (c : EdgeCert) : Bool :=
  match replayR c.calls #[] 0 {} #[] with
  | some (t, os) => t.statement == c.layout.len && c.accepts os && c.verifies os
  | none => false

theorem allHold_of_replay {cs : Array Call} {t : State} {os : Array (List ℕ)}
    (hr : replayR cs #[] 0 {} #[] = some (t, os)) {st : ℕ → Fin 4 → K} {val : Val} (hsat : Sat st t val) :
    AllHold cs os st val := by
  obtain ⟨-, -, -, hfacts⟩ := replayR_sound cs #[] 0 {} #[] t os inv_empty rfl (Nat.zero_le _)
    (fun j hj => absurd hj (Nat.not_lt_zero _)) hr
  intro j hj
  exact ((hfacts j hj) hj).1 st val hsat (by simp)

/-- An accepted edge: in an assignment satisfying the circuit, if a child's words carry statement `st`, every claim `st` makes at its kind's scale is one the reduction takes, and the digest the circuit reads is `st`'s two halves. -/
theorem EdgeCert.edge (c : EdgeCert) {t : State} {os : Array (List ℕ)}
    (hr : replayR c.calls #[] 0 {} #[] = some (t, os)) (hacc : c.accepts os = true)
    {stP : ℕ → Fin 4 → K} {val : Val} (hsat : Sat stP t val) {ch : ChildEdge} (hch : ch ∈ c.children)
    (st : ℕ → Fin 4 → K) (hpub : ∀ i < c.layout.len, val (ch.words.getD i 0) = st i) :
    (stmtClaims c.layout (stE st) (nodeScale ch.scale.mode (st 0))).Sub (c.claims.map (Model.ev val)) ∧
      (val (out os ch.digest 0) 0 = st 1 0 ∧ val (out os ch.digest 0) 1 = st 1 1 ∧
        val (out os ch.digest 0) 2 = st 2 0 ∧ val (out os ch.digest 0) 3 = st 2 1) := by
  have hF := allHold_of_replay hr hsat
  simp only [EdgeCert.accepts, Bool.and_eq_true, List.all_eq_true] at hacc
  obtain ⟨hL, hall⟩ := hacc
  have hok := hall ch hch
  simp only [ChildEdge.ok, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hlen, hsc⟩, hdig⟩, hd⟩, hm⟩ := hok
  have hlen3 : 3 ≤ c.layout.len := by
    simp only [Layout.len, Layout.matsAt, Layout.colsAt, Layout.rowsAt, Layout.dv]; omega
  have h0 := hpub 0 (by omega)
  have hσ : Model.ev val (ch.scale.wire os (ch.words.getD 0 0)) = nodeScale ch.scale.mode (st 0) := by
    rw [ch.scale.sem hF _ hsc, h0]
  have hx : stmtClaims c.layout (stE st) (nodeScale ch.scale.mode (st 0)) =
      (ch.claims c.layout os).map (Model.ev val) := by
    rw [ChildEdge.claims, stmtClaims_map, hσ]
    exact stmtClaims_congr hL _ fun i hi => by simp only [Function.comp_apply, Model.ev, hpub i hi, stE]
  refine ⟨?_, ?_⟩
  · rw [hx]
    refine ⟨fun d hd' => ?_, fun m hm' => ?_⟩
    · simp only [Claims.map, List.mem_map] at hd' ⊢
      obtain ⟨d', hd'', rfl⟩ := hd'
      exact ⟨d', hd d' hd'', rfl⟩
    · simp only [Claims.map, List.mem_map] at hm' ⊢
      obtain ⟨m', hm'', rfl⟩ := hm'
      exact ⟨m', hm m' hm'', rfl⟩
  · have H : Call.Holds stP val (os.getD ch.digest []) (.halvesToD (ch.words.getD 1 0) (ch.words.getD 2 0)) :=
      holds_at hF hdig
    obtain ⟨e0, e1, e2, e3, -, -⟩ := H
    rw [hpub 1 (by omega)] at e0 e1
    rw [hpub 2 (by omega)] at e2 e3
    exact ⟨e0, e1, e2, e3⟩

/-- When the reduction's claims hold, the child's statement's claims do. -/
theorem EdgeCert.edge_holds (c : EdgeCert) {t : State} {os : Array (List ℕ)}
    (hr : replayR c.calls #[] 0 {} #[] = some (t, os)) (hacc : c.accepts os = true)
    {stP : ℕ → Fin 4 → K} {val : Val} (hsat : Sat stP t val) {ch : ChildEdge} (hch : ch ∈ c.children)
    (st : ℕ → Fin 4 → K) (hpub : ∀ i < c.layout.len, val (ch.words.getD i 0) = st i)
    (tD : Dense E → Prop) (tM : Matrix E → Prop) (hin : (c.claims.map (Model.ev val)).Holds tD tM) :
    (stmtClaims c.layout (stE st) (nodeScale ch.scale.mode (st 0))).Holds tD tM :=
  hin.of_sub (c.edge hr hacc hsat hch st hpub).1

/-! Over a tree. -/

section Tree

variable {ι Ω : Type}

/-- A node's input claims: its reduction's, at its assignment. -/
def ins (cert : ι → EdgeCert) (val : ι → Ω → Val) (tD : Dense E → Prop) (tM : Matrix E → Prop) (v : ι) (ω : Ω) :
    Prop :=
  ((cert v).claims.map (Model.ev (val v ω))).Holds tD tM

/-- A node's statement: its words' claims, at the scale its parent's tier gives its kind. -/
def stmt (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (slot : ι → ℕ) (L : Layout) (st : ι → Ω → ℕ → Fin 4 → K)
    (tD : Dense E → Prop) (tM : Matrix E → Prop) (v : ι) (ω : Ω) : Prop :=
  (stmtClaims L (stE (st v ω))
    (nodeScale ((cert (T.parent v)).children.getD (slot v) default).scale.mode (st v ω 0))).Holds tD tM

/-- The edge premise at one outcome: each node's circuit replays to `t v` with outputs `os v` and its certificate accepts, every certificate has layout `L`, each node but the root is child `slot v` of its parent's, at that outcome each node's assignment satisfies its circuit with its statement, and a parent's words for a child carry the child's statement (`hpub`). -/
theorem hedge_at (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State) (os : ι → Array (List ℕ))
    (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (st : ι → Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val) (ω : Ω) (hsat : ∀ v ∈ T.nodes, Sat (st v ω) (t v) (val v ω))
    (hpub : ∀ v ∈ T.nodes, v ≠ T.root → ∀ i < L.len,
      val (T.parent v) ω (((cert (T.parent v)).children.getD (slot v) default).words.getD i 0) = st v ω i)
    (tD : Dense E → Prop) (tM : Matrix E → Prop) :
    ∀ v ∈ T.nodes, v ≠ T.root → ins cert val tD tM (T.parent v) ω → stmt T cert slot L st tD tM v ω := by
  intro v hv hne hin
  have hp := (T.parent_mem v hv hne).1
  have hch : (cert (T.parent v)).children.getD (slot v) default ∈ (cert (T.parent v)).children := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hslot v hv hne), Option.getD_some]
    exact List.getElem_mem _
  have := (cert (T.parent v)).edge_holds (hr _ hp) (hacc _ hp) (hsat _ hp) hch (st v ω)
    (fun i hi => hpub v hv hne i (by rw [hL _ hp] at hi; exact hi)) tD tM hin
  rw [hL _ hp] at this
  exact this

/-- `TreeSound.tree_sound`'s edge premise, from accepted certificates: `hedge_at` at every outcome. -/
theorem hedge_of_certs (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State) (os : ι → Array (List ℕ))
    (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (st : ι → Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val) (hsat : ∀ v ∈ T.nodes, ∀ ω, Sat (st v ω) (t v) (val v ω))
    (hpub : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, ∀ i < L.len,
      val (T.parent v) ω (((cert (T.parent v)).children.getD (slot v) default).words.getD i 0) = st v ω i)
    (tD : Dense E → Prop) (tM : Matrix E → Prop) :
    ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, ins cert val tD tM (T.parent v) ω → stmt T cert slot L st tD tM v ω :=
  fun v hv hne ω => hedge_at T cert t os hr hacc L hL slot hslot st val ω (fun u hu => hsat u hu ω)
    (fun u hu hne' => hpub u hu hne' ω) tD tM v hv hne

open Classical in
/-- A node's statement: the root's `stRoot`, every other node's the words its parent's verifier reads as its statement. -/
noncomputable def treeStmt (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K)
    (val : ι → Ω → Val) (v : ι) (ω : Ω) : ℕ → Fin 4 → K :=
  if v = T.root then stRoot ω
  else fun i => val (T.parent v) ω (((cert (T.parent v)).children.getD (slot v) default).words.getD i 0)

/-- `sat_tree` at one outcome: every node's circuit is satisfied at its `treeStmt` when the root's is and each child's is whenever its parent's verifier reads the statement at that outcome. -/
theorem sat_tree_at (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State) (os : ι → Array (List ℕ))
    (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (hver : ∀ v ∈ T.nodes, (cert v).verifies (os v) = true)
    (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val) (ω : Ω)
    (hsroot : Sat (stRoot ω) (t T.root) (val T.root ω))
    (hrec : ∀ v ∈ T.nodes, v ≠ T.root →
      Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v)) (val (T.parent v) ω) →
      ((cert (T.parent v)).children.getD (slot v) default).inst.VerifiesAt (cert (T.parent v)).calls
        (os (T.parent v)) (val (T.parent v) ω) (treeStmt T cert slot stRoot val v ω) L.len →
      Sat (treeStmt T cert slot stRoot val v ω) (t v) (val v ω)) :
    ∀ v ∈ T.nodes, Sat (treeStmt T cert slot stRoot val v ω) (t v) (val v ω) := by
  have key : ∀ k, ∀ v ∈ T.nodes, T.depth v = k → Sat (treeStmt T cert slot stRoot val v ω) (t v) (val v ω) := by
    intro k
    induction k with
    | zero =>
      intro v hv hd
      obtain rfl := T.root_of_depth v hv hd
      simpa [treeStmt] using hsroot
    | succ k ih =>
      intro v hv hd
      have hne : v ≠ T.root := by
        rintro rfl
        rw [T.depth_root] at hd
        omega
      obtain ⟨hp, hpd⟩ := T.parent_mem v hv hne
      refine hrec v hv hne (ih _ hp (by omega)) ?_
      have hF := allHold_of_replay (hr _ hp) (ih _ hp (by omega))
      have hch : (cert (T.parent v)).children.getD (slot v) default ∈ (cert (T.parent v)).children := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hslot v hv hne), Option.getD_some]
        exact List.getElem_mem _
      have hi := List.all_eq_true.mp (hver _ hp) _ hch
      have hok : ChildEdge.ok (cert (T.parent v)) (os (T.parent v))
          ((cert (T.parent v)).children.getD (slot v) default) = true := by
        have := hacc _ hp
        simp only [EdgeCert.accepts, Bool.and_eq_true, List.all_eq_true] at this
        exact this.2 _ hch
      have hlen : ((cert (T.parent v)).children.getD (slot v) default).words.length = L.len := by
        simp only [ChildEdge.ok, Bool.and_eq_true, beq_iff_eq] at hok
        rw [hok.1.1.1.1, hL _ hp]
      have := InstCert.verifies hF hi
      rw [hlen] at this
      have hst : treeStmt T cert slot stRoot val v ω =
          fun i => val (T.parent v) ω (((cert (T.parent v)).children.getD (slot v) default).words.getD i 0) := by
        simp [treeStmt, hne]
      rw [hst]
      exact this
  exact fun v hv => key _ v hv rfl

/-- Every node's circuit is satisfied at its `treeStmt` when the root's is and each child's is whenever its parent's verifier reads the statement (`hrec`, the recursive verifier's soundness): the parent's satisfied circuit makes its verifier of the child read `treeStmt` (`InstCert.verifies`). -/
theorem sat_tree (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State) (os : ι → Array (List ℕ))
    (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (hver : ∀ v ∈ T.nodes, (cert v).verifies (os v) = true)
    (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (hsroot : ∀ ω, Sat (stRoot ω) (t T.root) (val T.root ω))
    (hrec : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω,
      ((cert (T.parent v)).children.getD (slot v) default).inst.VerifiesAt (cert (T.parent v)).calls
        (os (T.parent v)) (val (T.parent v) ω) (treeStmt T cert slot stRoot val v ω) L.len →
      Sat (treeStmt T cert slot stRoot val v ω) (t v) (val v ω)) (ω : Ω) :
    ∀ v ∈ T.nodes, Sat (treeStmt T cert slot stRoot val v ω) (t v) (val v ω) :=
  sat_tree_at T cert t os hr hacc hver L hL slot hslot stRoot val ω (hsroot ω) fun v hv hne _ => hrec v hv hne ω

/-- `TreeSound.tree_sound` with its edges from accepted certificates: off every node's `bad`, every node's statement and input claims hold. A node's statement is its `treeStmt`: a child's is the words its parent's verifier reads as its statement, which `EdgeCert.verifies` checks are the instance its transcript absorbs and the statement its public table reads. The premise on a child is the recursive verifier's soundness (`hrec`): its circuit is satisfied at the statement its parent's verifier reads. -/
theorem tree_sound_certs (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State) (os : ι → Array (List ℕ))
    (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (hver : ∀ v ∈ T.nodes, (cert v).verifies (os v) = true)
    (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (hsroot : ∀ ω, Sat (stRoot ω) (t T.root) (val T.root ω))
    (hrec : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω,
      ((cert (T.parent v)).children.getD (slot v) default).inst.VerifiesAt (cert (T.parent v)).calls
        (os (T.parent v)) (val (T.parent v) ω) (treeStmt T cert slot stRoot val v ω) L.len →
      Sat (treeStmt T cert slot stRoot val v ω) (t v) (val v ω))
    (tD : Dense E → Prop) (tM : Matrix E → Prop) (bad : ι → Set Ω)
    (hstep : ∀ v ∈ T.nodes, ∀ ω, ω ∉ bad v →
      stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω → ins cert val tD tM v ω)
    (hroot : ∀ ω, stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM T.root ω) (ω : Ω)
    (hω : ∀ v ∈ T.nodes, ω ∉ bad v) :
    ∀ v ∈ T.nodes, stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω ∧ ins cert val tD tM v ω :=
  TreeSound.tree_sound T _ _ bad hstep
    (hedge_of_certs T cert t os hr hacc L hL slot hslot _ val
      (fun v hv ω => sat_tree T cert t os hr hacc hver L hL slot hslot stRoot val hsroot hrec ω v hv)
      (fun v _ hne ω i _ => by simp [treeStmt, hne]) tD tM) hroot ω hω

/-- `tree_sound_certs` with the recursive verifier's soundness off an event, as a verifier's soundness is: off `badRec v`, child `v`'s circuit is satisfied at the statement its parent's verifier reads, the parent's circuit being satisfied at its own (`hrec`). Off every node's `bad` and `badRec`, every node's statement and input claims hold. -/
theorem tree_sound_certs_off (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State) (os : ι → Array (List ℕ))
    (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (hver : ∀ v ∈ T.nodes, (cert v).verifies (os v) = true)
    (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (hsroot : ∀ ω, Sat (stRoot ω) (t T.root) (val T.root ω)) (badRec : ι → Set Ω)
    (hrec : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, ω ∉ badRec v →
      Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v)) (val (T.parent v) ω) →
      ((cert (T.parent v)).children.getD (slot v) default).inst.VerifiesAt (cert (T.parent v)).calls
        (os (T.parent v)) (val (T.parent v) ω) (treeStmt T cert slot stRoot val v ω) L.len →
      Sat (treeStmt T cert slot stRoot val v ω) (t v) (val v ω))
    (tD : Dense E → Prop) (tM : Matrix E → Prop) (bad : ι → Set Ω)
    (hstep : ∀ v ∈ T.nodes, ∀ ω, ω ∉ bad v →
      stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω → ins cert val tD tM v ω)
    (hroot : ∀ ω, stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM T.root ω) (ω : Ω)
    (hω : ∀ v ∈ T.nodes, ω ∉ bad v) (hωr : ∀ v ∈ T.nodes, ω ∉ badRec v) :
    ∀ v ∈ T.nodes, stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω ∧ ins cert val tD tM v ω := by
  -- The outcomes at which every node's circuit is satisfied at its `treeStmt`, `ω` among them.
  let G : Set Ω := {ω' | ∀ v ∈ T.nodes, Sat (treeStmt T cert slot stRoot val v ω') (t v) (val v ω')}
  have hG : ω ∈ G := sat_tree_at T cert t os hr hacc hver L hL slot hslot stRoot val ω (hsroot ω)
    fun v hv hne hps => hrec v hv hne ω (hωr v hv) hps
  have key := TreeSound.tree_sound T
    (fun v ω' => ω' ∈ G → stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω')
    (fun v ω' => ω' ∈ G → ins cert val tD tM v ω') bad
    (fun v hv ω' h hs hG' => hstep v hv ω' h (hs hG'))
    (fun v hv hne ω' hin hG' => hedge_at T cert t os hr hacc L hL slot hslot _ val ω' hG'
      (fun u _ hne' i _ => by simp [treeStmt, hne']) tD tM v hv hne (hin hG'))
    (fun ω' _ => hroot ω') ω hω
  exact fun v hv => ⟨(key v hv).1 hG, (key v hv).2 hG⟩

open Classical in
/-- The outcomes at which some node's statement or input claims are false are at most the sum of the nodes' `bad` and `badRec` fractions: each reduction's test (`Bind.sumcheck_test_sound`) and each child's verifier in its parent. -/
theorem tree_sound_certs_frac [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (hver : ∀ v ∈ T.nodes, (cert v).verifies (os v) = true)
    (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (hsroot : ∀ ω, Sat (stRoot ω) (t T.root) (val T.root ω)) (badRec : ι → Finset Ω)
    (hrec : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, ω ∉ badRec v →
      Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v)) (val (T.parent v) ω) →
      ((cert (T.parent v)).children.getD (slot v) default).inst.VerifiesAt (cert (T.parent v)).calls
        (os (T.parent v)) (val (T.parent v) ω) (treeStmt T cert slot stRoot val v ω) L.len →
      Sat (treeStmt T cert slot stRoot val v ω) (t v) (val v ω))
    (tD : Dense E → Prop) (tM : Matrix E → Prop) (bad : ι → Finset Ω)
    (hstep : ∀ v ∈ T.nodes, ∀ ω, ω ∉ bad v →
      stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω → ins cert val tD tM v ω)
    (hroot : ∀ ω, stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM T.root ω) :
    (Finset.card {ω | ∃ v ∈ T.nodes, ¬ (stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω ∧
        ins cert val tD tM v ω)} : ℚ≥0) / Fintype.card Ω ≤
      ∑ v ∈ T.nodes, ((bad v).card + (badRec v).card : ℚ≥0) / Fintype.card Ω := by
  have hsub : ({ω | ∃ v ∈ T.nodes, ¬ (stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω ∧
      ins cert val tD tM v ω)} : Finset Ω) ⊆ T.nodes.biUnion fun v => bad v ∪ badRec v := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    by_contra hn
    simp only [Finset.mem_biUnion, Finset.mem_union, not_exists, not_and, not_or] at hn
    obtain ⟨v, hv, hf⟩ := hω
    exact hf (tree_sound_certs_off T cert t os hr hacc hver L hL slot hslot stRoot val hsroot (fun v => badRec v)
      hrec tD tM (fun v => bad v) hstep hroot ω (fun u hu => (hn u hu).1) (fun u hu => (hn u hu).2) v hv)
  rw [← Finset.sum_div]
  gcongr
  calc ((Finset.card {ω | ∃ v ∈ T.nodes, ¬ (stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω ∧
        ins cert val tD tM v ω)} : ℕ) : ℚ≥0)
      ≤ ((T.nodes.biUnion fun v => bad v ∪ badRec v).card : ℚ≥0) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ v ∈ T.nodes, ((bad v ∪ badRec v).card : ℚ≥0) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ v ∈ T.nodes, ((bad v).card + (badRec v).card : ℚ≥0) := by
      gcongr with v
      exact_mod_cast Finset.card_union_le _ _

end Tree

end LeanVMCircuits.Rec.Edges
