module

public import LeanVMCircuits.Rec.Closure
public import LeanVMCircuits.Rec.Contracts

@[expose] public section

/-!
Justified determination rules of a recursion circuit.

A node is a wire's limb. Each rule `CheckBind` uses carries a justification `Just`, and `Just.ok` checks it against
the circuit: the rule's premises and conclusions are exactly the nodes the justification names, in a row, an equality
or a public row of the circuit. `Just.valid`: two assignments that satisfy every constraint but the tests (`Holds`)
and agree on a justified rule's premises agree on its conclusions, given the explicit premises

- `HashCR`: two hash rows given the same output ports, one by each assignment, are given the same input ports,
  collision resistance of the compression;
- `WindowCR`: four consecutive output words of two output blocks of one chaining value fix that chaining value,
  collision resistance of the duplex's output window;
- `UnionsValid`: a union product is a function of its pool's digests, begin and selection bits and its point (the
  union's parse uniqueness), which `Bind.unionsValid` proves from the rows under `HashCR`.

`LeanVMCircuits.Rec.Verdict` checks the rules and the transcripts.
-/

namespace LeanVMCircuits.Rec

mutual
/-- The columns a form reads. -/
def Form.cols : Form → List ℕ
  | .const _ => []
  | .col c => [c]
  | .prod a b => [a, b]
  | .sum ts => Form.colsSum ts

def Form.colsSum : List Form → List ℕ
  | [] => []
  | t :: ts => t.cols ++ Form.colsSum ts
end

mutual
theorem Form.eval_congr (row row' : ℕ → K) : (f : Form) → (∀ c ∈ f.cols, row c = row' c) →
    f.eval row = f.eval row'
  | .const _, _ => rfl
  | .col c, h => h c (by simp [Form.cols])
  | .prod a b, h => by
    simp only [Form.eval]
    rw [h a (by simp [Form.cols]), h b (by simp [Form.cols])]
  | .sum ts, h => by
    simp only [Form.eval]
    exact Form.evalSum_congr row row' ts (fun c hc => h c (by simpa [Form.cols] using hc))

theorem Form.evalSum_congr (row row' : ℕ → K) : (ts : List Form) → (∀ c ∈ Form.colsSum ts, row c = row' c) →
    Form.evalSum row ts = Form.evalSum row' ts
  | [], _ => rfl
  | t :: ts, h => by
    simp only [Form.evalSum]
    rw [Form.eval_congr row row' t (fun c hc => h c (by simp [Form.colsSum, hc])),
      Form.evalSum_congr row row' ts (fun c hc => h c (by simp [Form.colsSum, hc]))]
end

/-- The column a form is, if it is one. -/
def Form.colOf : Form → Option ℕ
  | .col c => some c
  | _ => none

theorem Form.eq_of_colOf {f : Form} {c : ℕ} (h : f.colOf = some c) : f = .col c := by
  cases f <;> simp_all [Form.colOf]

end LeanVMCircuits.Rec

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model

attribute [local irreducible] LeanVMCircuits.Blake2s.program

/-! Nodes. -/

/-- A limb's node: wire `w`'s limb `i`. -/
def limb (w i : ℕ) : ℕ := 4 * w + i

/-- A wire's four limb nodes. -/
def limbs4 (w : ℕ) : List ℕ := [limb w 0, limb w 1, limb w 2, limb w 3]

/-- A wire's `E` limb nodes. -/
def limbs3 (w : ℕ) : List ℕ := [limb w 0, limb w 1, limb w 2]

/-- An assignment's value at a node. -/
def nu (val : Val) (n : ℕ) : K := val (n / 4) ⟨n % 4, Nat.mod_lt _ (by norm_num)⟩

theorem nu_limb (val : Val) (w i : ℕ) (hi : i < 4) : nu val (limb w i) = val w ⟨i, hi⟩ := by
  have h1 : (4 * w + i) / 4 = w := by omega
  have h2 : (⟨(4 * w + i) % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) = ⟨i, hi⟩ := Fin.ext (by simp only; omega)
  simp only [nu, limb]
  rw [h2, h1]

theorem eq_of_limbs4 {val val' : Val} {w : ℕ} (h : ∀ n ∈ limbs4 w, nu val n = nu val' n) : val w = val' w := by
  funext i
  have := h (limb w i) (by fin_cases i <;> simp [limbs4])
  rwa [nu_limb val w i i.isLt, nu_limb val' w i i.isLt] at this

theorem limbs4_of_eq {val val' : Val} {w : ℕ} (h : val w = val' w) : ∀ n ∈ limbs4 w, nu val n = nu val' n := by
  intro n hn
  simp only [limbs4, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> rw [nu_limb _ _ _ (by norm_num), nu_limb _ _ _ (by norm_num), h]

/-! Rows. -/

/-- A row table's forms. -/
def formsOf : Table → List (List Form)
  | .emul => Rec.emul
  | .exk => Rec.exk
  | .hash => Rec.hash
  | .split => Rec.split
  | .cast => Rec.cast
  | .pub => []

/-- A row table's rows. -/
def rowsOf (s : State) : Table → Array (List ℕ)
  | .emul => s.emul
  | .exk => s.exk
  | .hash => s.hash
  | .split => s.split
  | .cast => s.cast
  | .pub => #[]

/-- What a row table's columns satisfy. -/
def holdsOf : Table → (ℕ → K) → Prop
  | .hash => HashRow
  | .split => fun col => ∀ id ∈ splitIdentities, id.eval col = 0
  | _ => fun _ => True

theorem Sat.row {st : ℕ → Fin 4 → K} {s : State} {val : Val} (h : Sat st s val) {t : Table} {r : List ℕ}
    (hr : r ∈ rowsOf s t) : RowSat (formsOf t) (holdsOf t) val r := by
  cases t
  · exact h.emul r hr
  · exact h.exk r hr
  · exact h.hash r hr
  · exact h.split r hr
  · exact h.cast r hr
  · simp [rowsOf] at hr

/-- Limb `i` of slot `s`'s form. -/
def formAt (t : Table) (s i : ℕ) : Form := ((formsOf t).getD s []).getD i .zero

/-- The node of a row's slot `src.1`'s limb `src.2`. -/
def colNode (row : List ℕ) (src : ℕ × ℕ) : ℕ := limb (row.getD src.1 0) src.2

/-- A row's columns, read off its slots: a slot limb whose form is column `c` carries `c`. -/
theorem col_eq {t : Table} {val : Val} {row : List ℕ} {col : ℕ → K}
    (hl : ∀ s < (formsOf t).length, ∀ i : Fin 4, limbs (formsOf t) s col i = val (row.getD s 0) i)
    {src : ℕ × ℕ} (h1 : src.1 < (formsOf t).length) (h2 : src.2 < 4) {c : ℕ}
    (hc : (formAt t src.1 src.2).colOf = some c) : col c = nu val (colNode row src) := by
  have := hl src.1 h1 ⟨src.2, h2⟩
  simp only [limbs] at this
  rw [colNode, nu_limb val _ _ h2, ← this]
  change col c = (formAt t src.1 src.2).eval col
  rw [Form.eq_of_colOf hc]
  rfl

/-! `HASH`'s columns. -/

/-- The slot and limb carrying `HASH`'s column `c` as itself: the counter and finalization in slot 1, the chaining
value in slot 0, the message words in slots 8 to 15, the output in slot 6, the mux bit in slot 3. -/
def hashSrc (c : ℕ) : ℕ × ℕ :=
  if c < 2 then (1, c) else if c < 6 then (0, c - 2) else if c < 14 then (2 + c, 0) else if c < 18 then (6, c - 14)
  else (3, 0)

theorem hashSrc_col (c : ℕ) (hc : c < 19) :
    (hashSrc c).1 < (formsOf .hash).length ∧ (hashSrc c).2 < 4 ∧
      (formAt .hash (hashSrc c).1 (hashSrc c).2).colOf = some c := by
  interval_cases c <;> exact ⟨by decide, by decide, rfl⟩

/-- A hash row's input port nodes: counter, finalization, chaining value, message. -/
def hashIn (row : List ℕ) : List ℕ := (List.range 14).map fun c => colNode row (hashSrc c)

/-- A hash row's output port nodes. -/
def hashOut (row : List ℕ) : List ℕ := (List.range 4).map fun k => colNode row (hashSrc (14 + k))

/-- A hash row's chaining value nodes. -/
def hashH (row : List ℕ) : List ℕ := (List.range 4).map fun k => colNode row (hashSrc (2 + k))

/-- The output stream window from word `j` of one output block into the next: `ra`'s output words `j..4`, then
`rb`'s `0..j`. -/
def windowIn (ra rb : List ℕ) (j : ℕ) : List ℕ :=
  (List.range (4 - j)).map (fun k => colNode ra (hashSrc (14 + j + k))) ++
    (List.range j).map fun k => colNode rb (hashSrc (14 + k))

/-- A hash row's input words other than its chaining value: counter, finalization and message. -/
def restIdx : Fin 10 → ℕ := ![0, 1, 6, 7, 8, 9, 10, 11, 12, 13]

/-- A hash row's input port nodes other than its chaining value (`restIdx`). -/
def hashRest (row : List ℕ) : List ℕ := List.ofFn fun i => colNode row (hashSrc (restIdx i))

/-- The nodes of a split row's bits. -/
def splitBitNodes (row : List ℕ) : List ℕ := (List.range 64).map fun b => limb (row.getD (1 + b) 0) 0

/-- A finalization word: a `HASH` row's `f` column at it is RFC 7693's, all ones or zero in its low half. -/
def finalOk (v : ℕ) : Bool := v < 2 ^ 64 && (v % 2 ^ 32 == 0 || v % 2 ^ 32 == 2 ^ 32 - 1)

/-! Justifications. -/

/-- A union product's premises: the wires its value is a function of (its pool's digests, begin and selection bits,
the point), and its output. -/
structure UnionClaim where
  inputs : List ℕ
  out : ℕ
  deriving Repr, Inhabited, DecidableEq

/-- Why a rule holds. -/
inductive Just where
  /-- Limb `i` of slot `sl` of row `k` of table `t` is its form of the columns, each read off one of the slot limbs
  `srcs` whose form is that column. -/
  | form (t : Table) (k sl i : ℕ) (srcs : List (ℕ × ℕ))
  /-- Limb `i` of public row `p`, a constant. -/
  | pubConst (p i : ℕ)
  /-- Limb `i` of equality `u`, one side from the other. -/
  | eq (u i : ℕ) (fwd : Bool)
  /-- A split row's word from its bits. -/
  | splitWord (k : ℕ)
  /-- A split row's bits from its word. -/
  | splitBits (k : ℕ)
  /-- At a constant mux bit (public row `p`), a hash row's mux limb `i` is a message word. -/
  | mux (k i p : ℕ)
  /-- A hash row's output from its inputs, at a constant final word (public row `p`). -/
  | compress (k p : ℕ)
  /-- A hash row's inputs from its output (`HashCR`). -/
  | collision (k : ℕ)
  /-- A chaining value from a window of its output stream (`WindowCR`). -/
  | window (ka kb j : ℕ)
  /-- `inv`'s product: `EMUL` row `k` is `a · x + 0`, held to one by equality `u`, its zero and one public rows
  `pz` and `po`; each of `a`, `x` gives the other. -/
  | inv (k u pz po : ℕ) (fwd : Bool)
  /-- Union product `c` (`UnionsValid`). -/
  | union (c : ℕ)
  deriving Repr

instance : Inhabited Just := ⟨.union 0⟩

/-- A squeeze row: its counter word is a constant at the duplex's output role. In a transcript's random-oracle view its
output is the oracle's answer, a challenge (`Bind.chalSeeds`), and no rule reads the transcript's own rows
(`HoldsP` with `Bind.dropOf`). -/
def isSqueezeRow (s : State) (row : List ℕ) : Bool :=
  s.pub.any fun e => e.1 == row.getD 1 0 && match e.2 with
    | .const v => v.headD 0 / 2 ^ 56 == 6
    | .statement _ => false

/-- A row a rule may read: any row but a dropped hash row. -/
def liveRow (drop : List ℕ → Bool) : Table → List ℕ → Bool
  | .hash, row => !drop row
  | _, _ => true

/-- A justification names exactly the rule's premises and conclusions, in the circuit. -/
def Just.ok (s : State) (isTest : ℕ → Bool) (claims : Array UnionClaim) (drop : List ℕ → Bool) (prem concl : List ℕ) :
    Just → Bool
  | .form t k sl i srcs =>
    match (rowsOf s t)[k]? with
    | none => false
    | some row =>
      liveRow drop t row && sl < (formsOf t).length && i < 4 && concl == [limb (row.getD sl 0) i] &&
        prem == srcs.map (colNode row) &&
        srcs.all (fun src => src.1 < (formsOf t).length && src.2 < 4 && (formAt t src.1 src.2).colOf.isSome) &&
        (formAt t sl i).cols.all fun c => srcs.any fun src => (formAt t src.1 src.2).colOf == some c
  | .pubConst p i =>
    match s.pub[p]? with
    | some (w, .const _) => i < 4 && prem.isEmpty && concl == [limb w i]
    | _ => false
  | .eq u i fwd =>
    match s.unions[u]? with
    | some (a, b) => !isTest u && i < 4 &&
      (if fwd then prem == [limb a i] && concl == [limb b i] else prem == [limb b i] && concl == [limb a i])
    | none => false
  | .splitWord k =>
    match s.split[k]? with
    | some row => prem == splitBitNodes row && concl == [limb (row.getD 0 0) 0]
    | none => false
  | .splitBits k =>
    match s.split[k]? with
    | some row => prem == [limb (row.getD 0 0) 0] && concl == splitBitNodes row
    | none => false
  | .mux k i p =>
    match s.hash[k]?, s.pub[p]? with
    | some row, some (w, .const v) =>
      !drop row && w == row.getD 3 0 && i < 4 && prem == [limb (row.getD 2 0) i] &&
        (if v == [0, 0, 0, 0] then concl == [colNode row (hashSrc (6 + i))]
        else v == [1, 0, 0, 0] && concl == [colNode row (hashSrc (10 + i))])
    | _, _ => false
  | .compress k p =>
    match s.hash[k]?, s.pub[p]? with
    | some row, some (w, .const v) =>
      !drop row && w == row.getD 1 0 && finalOk (v.getD 1 0) && prem == hashIn row && concl == hashOut row
    | _, _ => false
  | .collision k =>
    match s.hash[k]? with
    | some row => !drop row && prem == hashOut row && concl == hashIn row
    | none => false
  | .window ka kb j =>
    match s.hash[ka]?, s.hash[kb]? with
    | some ra, some rb => !drop ra && !drop rb && ra.getD 0 0 == rb.getD 0 0 && 1 ≤ j && j < 4 &&
      prem == windowIn ra rb j ++ hashRest ra ++ hashRest rb && concl == hashH ra
    | _, _ => false
  | .inv k u pz po fwd =>
    match s.emul[k]?, s.unions[u]?, s.pub[pz]?, s.pub[po]? with
    | some row, some (p, o), some (z, .const vz), some (o', .const vo) =>
      !isTest u && row.length == 4 && row.getD 2 0 == z && row.getD 3 0 == p && o == o' && vz == [0, 0, 0, 0] &&
        vo == [1, 0, 0, 0] &&
        (if fwd then prem == limbs3 (row.getD 0 0) && concl == limbs3 (row.getD 1 0)
        else prem == limbs3 (row.getD 1 0) && concl == limbs3 (row.getD 0 0))
    | _, _, _, _ => false
  | .union c =>
    match claims[c]? with
    | some uc => prem == uc.inputs.flatMap limbs4 && concl == limbs3 uc.out
    | none => false

/-- Every rule is justified. -/
def rulesOk (s : State) (isTest : ℕ → Bool) (claims : Array UnionClaim) (drop : List ℕ → Bool) (r : Rules Just) : Bool :=
  (List.range r.size).all fun i => (r.why.getD i default).ok s isTest claims drop (r.prem i) (r.concl i)

/-! Assignments and premises. -/

/-- The circuit without its tests. -/
def keep (s : State) (isTest : ℕ → Bool) : State :=
  { s with unions := ((List.range s.unions.size).filterMap fun u => if isTest u then none else s.unions[u]?).toArray }

/-- An assignment satisfying every constraint of the circuit but the tests. -/
def Holds (statement : ℕ → Fin 4 → K) (s : State) (isTest : ℕ → Bool) (val : Val) : Prop :=
  Sat statement (keep s isTest) val

theorem Sat.holds {st : ℕ → Fin 4 → K} {s : State} {val : Val} (h : Sat st s val) (isTest : ℕ → Bool) :
    Holds st s isTest val := by
  refine ⟨fun p hp => h.unions p ?_, h.emul, h.exk, h.hash, h.split, h.cast, h.pub⟩
  simp only [keep, List.mem_toArray, List.mem_filterMap, List.mem_range] at hp
  obtain ⟨u, -, hu⟩ := hp
  split at hu
  · simp at hu
  · exact Array.mem_of_getElem? hu

theorem Holds.union {st : ℕ → Fin 4 → K} {s : State} {isTest : ℕ → Bool} {val : Val} (h : Holds st s isTest val)
    {u a b : ℕ} (hu : s.unions[u]? = some (a, b)) (ht : isTest u = false) : val a = val b := by
  refine h.unions (a, b) ?_
  simp only [keep, List.mem_toArray, List.mem_filterMap, List.mem_range]
  refine ⟨u, ?_, by simp [ht, hu]⟩
  by_contra hn
  rw [Array.getElem?_eq_none (by omega)] at hu
  simp at hu

/-- The circuit without its tests and the hash rows `drop` names. -/
def keepP (s : State) (isTest : ℕ → Bool) (drop : List ℕ → Bool) : State :=
  { keep s isTest with hash := s.hash.filter fun row => !drop row }

/-- An assignment satisfying every constraint of the circuit but the tests and the squeezes: the random-oracle view,
in which a squeeze's output is the oracle's answer rather than the compression of its chaining value. -/
def HoldsP (statement : ℕ → Fin 4 → K) (s : State) (isTest : ℕ → Bool) (drop : List ℕ → Bool) (val : Val) : Prop :=
  Sat statement (keepP s isTest drop) val

theorem Holds.toP {st : ℕ → Fin 4 → K} {s : State} {isTest : ℕ → Bool} {val : Val} (h : Holds st s isTest val)
    (drop : List ℕ → Bool) : HoldsP st s isTest drop val :=
  ⟨h.unions, h.emul, h.exk, fun r hr => h.hash r (Array.mem_of_mem_filter hr), h.split, h.cast, h.pub⟩

theorem mem_keepP_hash {s : State} {isTest : ℕ → Bool} {drop : List ℕ → Bool} {row : List ℕ} (h : row ∈ s.hash)
    (hs : drop row = false) : row ∈ (keepP s isTest drop).hash :=
  Array.mem_filter.mpr ⟨h, by simp [hs]⟩

theorem HoldsP.union {st : ℕ → Fin 4 → K} {s : State} {isTest : ℕ → Bool} {drop : List ℕ → Bool} {val : Val}
    (h : HoldsP st s isTest drop val) {u a b : ℕ} (hu : s.unions[u]? = some (a, b)) (ht : isTest u = false) :
    val a = val b := by
  refine h.unions (a, b) ?_
  simp only [keepP, keep, List.mem_toArray, List.mem_filterMap, List.mem_range]
  refine ⟨u, ?_, by simp [ht, hu]⟩
  by_contra hn
  rw [Array.getElem?_eq_none (by omega)] at hu
  simp at hu

/-- Collision resistance of the compression, as a premise on two assignments: two hash rows given the same output
ports, one by each assignment, are given the same input ports. -/
def HashCR (s : State) (val val' : Val) : Prop :=
  ∀ row ∈ s.hash, ∀ row' ∈ s.hash, (hashOut row).map (nu val) = (hashOut row').map (nu val') →
    (hashIn row).map (nu val) = (hashIn row').map (nu val')

/-- A hash row is live on nodes `L` when one of its output ports is among them: a rule firing on `L` reads it. -/
def RowLive (L : ℕ → Prop) (row : List ℕ) : Prop := ∃ n ∈ hashOut row, L n

/-- `HashCR` on the live rows (`RowLive L`) that are not squeezes: what the rules firing on `L` need. Two answers of a
random oracle at different chaining values may share an output, so a premise over many oracles' answers cannot ask more;
and the rows a rule fires on before a challenge are the ones a prover's queries before it decide. -/
def HashCRP (s : State) (drop : List ℕ → Bool) (L : ℕ → Prop) (val val' : Val) : Prop :=
  ∀ row ∈ s.hash, ∀ row' ∈ s.hash, drop row = false → drop row' = false → RowLive L row → RowLive L row' →
    (hashOut row).map (nu val) = (hashOut row').map (nu val') → (hashIn row).map (nu val) = (hashIn row').map (nu val')

theorem HashCR.toP {s : State} {val val' : Val} (h : HashCR s val val') (drop : List ℕ → Bool) (L : ℕ → Prop) :
    HashCRP s drop L val val' :=
  fun row hr row' hr' _ _ _ _ => h row hr row' hr'

/-- Collision resistance of the duplex's output window, as a premise on two assignments: two hash rows of one
chaining value, given the same window of output words and the same input words but the chaining value (their counter,
finalization and message, constants in an output block), are given the same chaining value. -/
def WindowCR (s : State) (val val' : Val) : Prop :=
  ∀ ra ∈ s.hash, ∀ rb ∈ s.hash, ra.getD 0 0 = rb.getD 0 0 → ∀ j, 1 ≤ j → j < 4 →
    (∀ n ∈ windowIn ra rb j ++ hashRest ra ++ hashRest rb, nu val n = nu val' n) → ∀ n ∈ hashH ra, nu val n = nu val' n

/-- `WindowCR` on the live rows that are not squeezes. -/
def WindowCRP (s : State) (drop : List ℕ → Bool) (L : ℕ → Prop) (val val' : Val) : Prop :=
  ∀ ra ∈ s.hash, ∀ rb ∈ s.hash, drop ra = false → drop rb = false → RowLive L ra → RowLive L rb →
    ra.getD 0 0 = rb.getD 0 0 → ∀ j, 1 ≤ j → j < 4 →
    (∀ n ∈ windowIn ra rb j ++ hashRest ra ++ hashRest rb, nu val n = nu val' n) → ∀ n ∈ hashH ra, nu val n = nu val' n

theorem WindowCR.toP {s : State} {val val' : Val} (h : WindowCR s val val') (drop : List ℕ → Bool) (L : ℕ → Prop) :
    WindowCRP s drop L val val' :=
  fun ra ha rb hb _ _ _ _ => h ra ha rb hb

/-- The union's parse uniqueness, as a premise on two assignments: a union product is a function of its inputs. -/
def UnionsValid (claims : Array UnionClaim) (val val' : Val) : Prop :=
  ∀ uc ∈ claims, (∀ w ∈ uc.inputs, val w = val' w) → Model.ev val uc.out = Model.ev val' uc.out

/-! Each justification is valid. -/

theorem ofNat_toWord_inj {x y : K} (h : BitVec.ofNat 64 (toWord x) = BitVec.ofNat 64 (toWord y)) : x = y := by
  apply toWord_injective
  have hx : toWord x < 2 ^ 64 := num_lt _ _
  have hy : toWord y < 2 ^ 64 := num_lt _ _
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

theorem final_of_ok {v : ℕ} (hv : finalOk v = true) : ∃ f : Bool,
    (BitVec.ofNat 64 (toWord (ofWord v))).setWidth 32 = if f then BitVec.allOnes 32 else 0 := by
  simp only [finalOk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hv
  obtain ⟨hlt, h | h⟩ := hv
  · refine ⟨false, ?_⟩
    rw [toWord_ofWord v hlt]
    apply BitVec.eq_of_toNat_eq
    norm_num at h
    simp [BitVec.toNat_ofNat, h]
  · refine ⟨true, ?_⟩
    rw [toWord_ofWord v hlt]
    apply BitVec.eq_of_toNat_eq
    norm_num at h
    simp [BitVec.toNat_ofNat, h]

section

variable {st st' : ℕ → Fin 4 → K} {s : State} {isTest : ℕ → Bool} {claims : Array UnionClaim} {drop : List ℕ → Bool}
  {val val' : Val}

theorem ok_form {t : Table} {k sl i : ℕ} {srcs : List (ℕ × ℕ)} {prem concl : List ℕ}
    (hok : (Just.form t k sl i srcs).ok s isTest claims drop prem concl = true)
    (h : HoldsP st s isTest drop val) (h' : HoldsP st' s isTest drop val') :
    (∀ p ∈ prem, nu val p = nu val' p) → ∀ c ∈ concl, nu val c = nu val' c := by
  intro hp n hn
  simp only [Just.ok] at hok
  split at hok
  · simp at hok
  rename_i row hrow
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.any_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨hlive, hsl⟩, hi⟩, rfl⟩, rfl⟩, hsrcs⟩, hcols⟩ := hok
  simp only [List.mem_singleton] at hn
  subst hn
  have hmem : row ∈ rowsOf (keepP s isTest drop) t := by
    cases t
    case hash => exact mem_keepP_hash (Array.mem_of_getElem? hrow) (by simpa [liveRow] using hlive)
    all_goals exact Array.mem_of_getElem? hrow
  obtain ⟨col, -, hl⟩ := Sat.row h hmem
  obtain ⟨col', -, hl'⟩ := Sat.row h' hmem
  have hcol : ∀ c ∈ (formAt t sl i).cols, col c = col' c := by
    intro c hc
    obtain ⟨src, hsrc, hsc⟩ := hcols c hc
    obtain ⟨⟨h1, h2⟩, -⟩ := hsrcs src hsrc
    have hsc : (formAt t src.1 src.2).colOf = some c := by simpa using hsc
    rw [col_eq hl h1 h2 hsc, col_eq hl' h1 h2 hsc]
    exact hp _ (List.mem_map_of_mem hsrc)
  have e := hl sl hsl ⟨i, hi⟩
  have e' := hl' sl hsl ⟨i, hi⟩
  simp only [limbs] at e e'
  rw [nu_limb val _ _ hi, nu_limb val' _ _ hi, ← e, ← e']
  exact Form.eval_congr col col' _ hcol

theorem nu_limb0 (val : Val) (w : ℕ) : nu val (limb w 0) = val w 0 := nu_limb val w 0 (by norm_num)

theorem ok_pubConst {p i : ℕ} {prem concl : List ℕ} (hok : (Just.pubConst p i).ok s isTest claims drop prem concl = true)
    (h : HoldsP st s isTest drop val) (h' : HoldsP st' s isTest drop val') :
    (∀ q ∈ prem, nu val q = nu val' q) → ∀ c ∈ concl, nu val c = nu val' c := by
  intro _ n hn
  cases hq : s.pub[p]? with
  | none => simp [Just.ok, hq] at hok
  | some e =>
    obtain ⟨w, src⟩ := e
    cases src with
    | statement _ => simp [Just.ok, hq] at hok
    | const v =>
      simp only [Just.ok, hq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
      obtain ⟨⟨hi, -⟩, rfl⟩ := hok
      simp only [List.mem_singleton] at hn
      subst hn
      have hm : (w, PubSource.const v) ∈ (keepP s isTest drop).pub := Array.mem_of_getElem? hq
      rw [nu_limb val _ _ hi, nu_limb val' _ _ hi, h.pub w _ hm, h'.pub w _ hm]
      rfl

theorem ok_eq {u i : ℕ} {fwd : Bool} {prem concl : List ℕ}
    (hok : (Just.eq u i fwd).ok s isTest claims drop prem concl = true)
    (h : HoldsP st s isTest drop val) (h' : HoldsP st' s isTest drop val') :
    (∀ q ∈ prem, nu val q = nu val' q) → ∀ c ∈ concl, nu val c = nu val' c := by
  intro hp n hn
  cases hu : s.unions[u]? with
  | none => simp [Just.ok, hu] at hok
  | some e =>
    obtain ⟨a, b⟩ := e
    simp only [Just.ok, hu, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hok
    obtain ⟨⟨ht, hi⟩, hfb⟩ := hok
    have hab := h.union hu ht
    have hab' := h'.union hu ht
    cases fwd
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hfb
      obtain ⟨rfl, rfl⟩ := hfb
      simp only [List.mem_singleton] at hn
      subst hn
      have := hp _ (List.mem_singleton_self _)
      rw [nu_limb val _ _ hi, nu_limb val' _ _ hi] at this ⊢
      rw [hab, hab', this]
    · simp only [↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hfb
      obtain ⟨rfl, rfl⟩ := hfb
      simp only [List.mem_singleton] at hn
      subst hn
      have := hp _ (List.mem_singleton_self _)
      rw [nu_limb val _ _ hi, nu_limb val' _ _ hi] at this ⊢
      rw [← hab, ← hab', this]

theorem ok_splitWord {k : ℕ} {prem concl : List ℕ} (hok : (Just.splitWord k).ok s isTest claims drop prem concl = true)
    (h : HoldsP st s isTest drop val) (h' : HoldsP st' s isTest drop val') :
    (∀ q ∈ prem, nu val q = nu val' q) → ∀ c ∈ concl, nu val c = nu val' c := by
  intro hp n hn
  cases hr : s.split[k]? with
  | none => simp [Just.ok, hr] at hok
  | some row =>
    simp only [Just.ok, hr, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨rfl, rfl⟩ := hok
    simp only [List.mem_singleton] at hn
    subst hn
    have hm : row ∈ (keepP s isTest drop).split := Array.mem_of_getElem? hr
    obtain ⟨-, hw⟩ := split_sem h hm
    obtain ⟨-, hw'⟩ := split_sem h' hm
    have hb : ∀ b < 64, val (row.getD (1 + b) 0) 0 = val' (row.getD (1 + b) 0) 0 := by
      intro b hb
      have := hp (limb (row.getD (1 + b) 0) 0)
        (by simp only [splitBitNodes, List.mem_map, List.mem_range]; exact ⟨b, hb, rfl⟩)
      rwa [nu_limb0, nu_limb0] at this
    rw [nu_limb0, nu_limb0]
    apply toWord_injective
    rw [hw, hw']
    exact num_congr _ _ 64 fun b hb' => by simp only [hb b hb']

theorem ok_splitBits {k : ℕ} {prem concl : List ℕ} (hok : (Just.splitBits k).ok s isTest claims drop prem concl = true)
    (h : HoldsP st s isTest drop val) (h' : HoldsP st' s isTest drop val') :
    (∀ q ∈ prem, nu val q = nu val' q) → ∀ c ∈ concl, nu val c = nu val' c := by
  intro hp n hn
  cases hr : s.split[k]? with
  | none => simp [Just.ok, hr] at hok
  | some row =>
    simp only [Just.ok, hr, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨rfl, rfl⟩ := hok
    have hm : row ∈ (keepP s isTest drop).split := Array.mem_of_getElem? hr
    obtain ⟨hb, hw⟩ := split_sem h hm
    obtain ⟨hb', hw'⟩ := split_sem h' hm
    have hword : toWord (val (row.getD 0 0) 0) = toWord (val' (row.getD 0 0) 0) := by
      have := hp _ (List.mem_singleton_self _)
      rw [nu_limb0, nu_limb0] at this
      rw [this]
    simp only [splitBitNodes, List.mem_map, List.mem_range] at hn
    obtain ⟨b, hb64, rfl⟩ := hn
    rw [nu_limb0, nu_limb0]
    have ht := congrArg (fun n => Nat.testBit n b) (hw.symm.trans (hword.trans hw'))
    simp only [testBit_num _ 64 b hb64, decide_eq_decide] at ht
    have z1 : (0 : ZMod 2) ≠ 1 := by decide
    rcases hb b hb64 with e | e <;> rcases hb' b hb64 with e' | e' <;> simp_all

/-- A hash row's column `c` is its source slot limb. -/
theorem hash_col {val : Val} {row : List ℕ} {col : ℕ → K}
    (hl : ∀ s < Rec.hash.length, ∀ i : Fin 4, limbs Rec.hash s col i = val (row.getD s 0) i) (c : ℕ)
    (hc : c < 19) : col c = nu val (colNode row (hashSrc c)) :=
  col_eq (t := .hash) hl (hashSrc_col c hc).1 (hashSrc_col c hc).2.1 (hashSrc_col c hc).2.2

theorem ok_mux {k i p : ℕ} {prem concl : List ℕ} (hok : (Just.mux k i p).ok s isTest claims drop prem concl = true)
    (h : HoldsP st s isTest drop val) (h' : HoldsP st' s isTest drop val') :
    (∀ q ∈ prem, nu val q = nu val' q) → ∀ c ∈ concl, nu val c = nu val' c := by
  intro hp n hn
  cases hr : s.hash[k]? with
  | none => simp [Just.ok, hr] at hok
  | some row =>
  cases hq : s.pub[p]? with
  | none => simp [Just.ok, hr, hq] at hok
  | some e =>
    obtain ⟨w, src⟩ := e
    cases src with
    | statement _ => simp [Just.ok, hr, hq] at hok
    | const v =>
      simp only [Just.ok, hr, hq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at hok
      obtain ⟨⟨⟨⟨hsq, rfl⟩, hi⟩, rfl⟩, hv⟩ := hok
      have hm : row ∈ (keepP s isTest drop).hash := mem_keepP_hash (Array.mem_of_getElem? hr) hsq
      have hpub : (row.getD 3 0, PubSource.const v) ∈ (keepP s isTest drop).pub := Array.mem_of_getElem? hq
      have hp0 := hp _ (List.mem_singleton_self _)
      rw [nu_limb val _ _ hi, nu_limb val' _ _ hi] at hp0
      -- In each assignment the mux limb is the message word the constant bit picks.
      have pick : ∀ {st : ℕ → Fin 4 → K} {val : Val}, HoldsP st s isTest drop val → ∀ c ∈ concl,
          nu val c = val (row.getD 2 0) ⟨i, hi⟩ := by
        intro st val h c hc
        obtain ⟨col, hrow, hl⟩ := h.hash row hm
        obtain ⟨hmux, -⟩ := hash_mux col hrow.identities i hi
        have hlimb := hl 2 (by decide) ⟨i, hi⟩
        simp only [limbs] at hlimb
        rw [← hlimb, hmux]
        have hsel : col hashSel = limbsOf v 0 := by
          rw [show hashSel = 18 from rfl, hash_col hl 18 (by norm_num)]
          show nu val (limb (row.getD 3 0) 0) = _
          rw [nu_limb0, h.pub _ _ hpub]
          rfl
        split at hv
        · rename_i hv0
          subst hv0
          simp only [beq_iff_eq] at hv
          subst hv
          simp only [List.mem_singleton] at hc
          subst hc
          have h0 : col hashSel = 0 := by rw [hsel]; simp [limbsOf, ofWord_zero]
          rw [if_pos h0, show hashM + i = 6 + i from by simp [hashM], hash_col hl (6 + i) (by omega)]
        · simp only [Bool.and_eq_true, beq_iff_eq] at hv
          obtain ⟨rfl, rfl⟩ := hv
          simp only [List.mem_singleton] at hc
          subst hc
          have h1 : col hashSel ≠ 0 := by rw [hsel]; simp [limbsOf, ofWord_one]
          rw [if_neg h1, show hashM + 4 + i = 10 + i from by simp [hashM], hash_col hl (10 + i) (by omega)]
      rw [pick h n hn, pick h' n hn, hp0]

theorem ok_compress {k p : ℕ} {prem concl : List ℕ}
    (hok : (Just.compress k p).ok s isTest claims drop prem concl = true)
    (h : HoldsP st s isTest drop val) (h' : HoldsP st' s isTest drop val') :
    (∀ q ∈ prem, nu val q = nu val' q) → ∀ c ∈ concl, nu val c = nu val' c := by
  intro hp n hn
  cases hr : s.hash[k]? with
  | none => simp [Just.ok, hr] at hok
  | some row =>
  cases hq : s.pub[p]? with
  | none => simp [Just.ok, hr, hq] at hok
  | some e =>
    obtain ⟨w, src⟩ := e
    cases src with
    | statement _ => simp [Just.ok, hr, hq] at hok
    | const v =>
      simp only [Just.ok, hr, hq, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hok
      obtain ⟨⟨⟨⟨hsq, rfl⟩, hf⟩, rfl⟩, rfl⟩ := hok
      have hm : row ∈ (keepP s isTest drop).hash := mem_keepP_hash (Array.mem_of_getElem? hr) hsq
      have hpub : (row.getD 1 0, PubSource.const v) ∈ (keepP s isTest drop).pub := Array.mem_of_getElem? hq
      obtain ⟨f, hfw⟩ := final_of_ok hf
      obtain ⟨col, hrow, hl⟩ := h.hash row hm
      obtain ⟨col', hrow', hl'⟩ := h'.hash row hm
      have hin : ∀ c < 14, col c = col' c := by
        intro c hc
        rw [hash_col hl c (by omega), hash_col hl' c (by omega)]
        exact hp _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)
      have hF : ∀ {st : ℕ → Fin 4 → K} {val : Val} {col : ℕ → K}, HoldsP st s isTest drop val →
          (∀ s < Rec.hash.length, ∀ i : Fin 4, limbs Rec.hash s col i = val (row.getD s 0) i) →
          (columnWord col hashF).setWidth 32 = if f then BitVec.allOnes 32 else 0 := by
        intro st val col h hl
        have : col hashF = ofWord (v.getD 1 0) := by
          rw [show hashF = 1 from rfl, hash_col hl 1 (by norm_num)]
          show nu val (limb (row.getD 1 0) 1) = _
          rw [nu_limb val _ 1 (by norm_num), h.pub _ _ hpub]
          rfl
        rw [columnWord, this]
        exact hfw
      obtain ⟨a, ha, hain, haout⟩ := hrow.witness
      obtain ⟨a', ha', hain', haout'⟩ := hrow'.witness
      have hP : (fun j : Fin 14 => columnWord col j) = fun j : Fin 14 => columnWord col' j :=
        funext fun j => congrArg (fun x => BitVec.ofNat 64 (toWord x)) (hin j j.isLt)
      have hT : columnWord col hashT = columnWord col' hashT :=
        congrArg (fun x => BitVec.ofNat 64 (toWord x)) (hin 0 (by norm_num))
      have hhalf : ∀ r : Fin 8, half (columnWord col (hashO + r.val / 2)) (r.val % 2) =
          half (columnWord col' (hashO + r.val / 2)) (r.val % 2) := by
        intro r
        have e := congrArg₂ (fun (P : Fin 14 → BitVec 64) (T : BitVec 64) =>
          (LeanVMCircuits.Blake2s.Rfc7693.F (hWords P) (mWords P) T f)[r]) hP hT
        exact (hash_row_compress col a ha hain haout f (hF h hl) r).trans
          (e.trans (hash_row_compress col' a' ha' hain' haout' f (hF h' hl') r).symm)
      have hout : ∀ k < 4, col (14 + k) = col' (14 + k) := by
        intro k hk
        apply ofNat_toWord_inj
        have h0 := hhalf ⟨2 * k, by omega⟩
        have h1 := hhalf ⟨2 * k + 1, by omega⟩
        dsimp only at h0 h1
        rw [show 2 * k / 2 = k by omega, show 2 * k % 2 = 0 by omega] at h0
        rw [show (2 * k + 1) / 2 = k by omega, show (2 * k + 1) % 2 = 1 by omega] at h1
        exact eq_of_halves _ _ h0 h1
      simp only [hashOut, List.mem_map, List.mem_range] at hn
      obtain ⟨k, hk, rfl⟩ := hn
      rw [← hash_col hl (14 + k) (by omega), ← hash_col hl' (14 + k) (by omega)]
      exact hout k hk

theorem ok_collision {k : ℕ} {prem concl : List ℕ} {L : ℕ → Prop}
    (hok : (Just.collision k).ok s isTest claims drop prem concl = true) (hcr : HashCRP s drop L val val')
    (hL : ∀ q ∈ prem, L q) : (∀ q ∈ prem, nu val q = nu val' q) → ∀ c ∈ concl, nu val c = nu val' c := by
  intro hp
  cases hr : s.hash[k]? with
  | none => simp [Just.ok, hr] at hok
  | some row =>
    simp only [Just.ok, hr, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hok
    obtain ⟨⟨hsq, rfl⟩, rfl⟩ := hok
    have hm := Array.mem_of_getElem? hr
    have hlive : RowLive L row :=
      ⟨_, List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩, hL _ (List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩)⟩
    exact List.map_inj_left.mp (hcr row hm row hm hsq hsq hlive hlive (List.map_inj_left.mpr hp))

theorem ok_window {ka kb j : ℕ} {prem concl : List ℕ} {L : ℕ → Prop}
    (hok : (Just.window ka kb j).ok s isTest claims drop prem concl = true) (hw : WindowCRP s drop L val val')
    (hL : ∀ q ∈ prem, L q) : (∀ q ∈ prem, nu val q = nu val' q) → ∀ c ∈ concl, nu val c = nu val' c := by
  intro hp
  cases ha : s.hash[ka]? with
  | none => simp [Just.ok, ha] at hok
  | some ra =>
  cases hb : s.hash[kb]? with
  | none => simp [Just.ok, ha, hb] at hok
  | some rb =>
    simp only [Just.ok, ha, hb, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at hok
    obtain ⟨⟨⟨⟨⟨⟨hsa, hsb⟩, hh⟩, hj1⟩, hj4⟩, rfl⟩, rfl⟩ := hok
    -- each row gives the window a word: `ra` its word `j`, `rb` its word `0`
    have hla : RowLive L ra := by
      refine ⟨colNode ra (hashSrc (14 + j)), List.mem_map.mpr ⟨j, List.mem_range.mpr hj4, rfl⟩, hL _ ?_⟩
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
      exact List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩
    have hlb : RowLive L rb := by
      refine ⟨colNode rb (hashSrc (14 + 0)), List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩, hL _ ?_⟩
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      exact List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩
    exact hw ra (Array.mem_of_getElem? ha) rb (Array.mem_of_getElem? hb) hsa hsb hla hlb hh j hj1 hj4 hp

theorem nu_limbF (val : Val) (w : ℕ) (i : Fin 4) : nu val (limb w i) = val w i := nu_limb val w i i.isLt

theorem agree_limb {val val' : Val} {w : ℕ} (i : Fin 4) (h : nu val (limb w i) = nu val' (limb w i)) :
    val w i = val' w i :=
  (nu_limbF val w i).symm.trans (h.trans (nu_limbF val' w i))

theorem ev_eq_of_limbs3 {val val' : Val} {w : ℕ} (h : ∀ n ∈ limbs3 w, nu val n = nu val' n) :
    Model.ev val w = Model.ev val' w := by
  have h0 : val w 0 = val' w 0 := agree_limb 0 (h (limb w 0) (by simp [limbs3]))
  have h1 : val w 1 = val' w 1 := agree_limb 1 (h (limb w 1) (by simp [limbs3]))
  have h2 : val w 2 = val' w 2 := agree_limb 2 (h (limb w 2) (by simp [limbs3]))
  simp only [Model.ev]
  rw [h0, h1, h2]

theorem limbs3_of_ev {val val' : Val} {w : ℕ} (h : Model.ev val w = Model.ev val' w) :
    ∀ n ∈ limbs3 w, nu val n = nu val' n := by
  obtain ⟨h0, h1, h2⟩ := toE_injective _ _ _ _ _ _ h
  intro n hn
  simp only [limbs3, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl
  · exact (nu_limbF val w 0).trans (h0.trans (nu_limbF val' w 0).symm)
  · exact (nu_limbF val w 1).trans (h1.trans (nu_limbF val' w 1).symm)
  · exact (nu_limbF val w 2).trans (h2.trans (nu_limbF val' w 2).symm)

theorem inv_unique {a x x' : E} (h : a * x = 1) (h' : a * x' = 1) : x = x' :=
  calc x = x * (a * x') := by rw [h', mul_one]
    _ = (a * x) * x' := by ring
    _ = x' := by rw [h, one_mul]

theorem list_eq_four {l : List ℕ} (h : l.length = 4) : l = [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0] := by
  match l, h with
  | [_, _, _, _], _ => rfl

theorem ok_inv {k u pz po : ℕ} {fwd : Bool} {prem concl : List ℕ}
    (hok : (Just.inv k u pz po fwd).ok s isTest claims drop prem concl = true)
    (h : HoldsP st s isTest drop val) (h' : HoldsP st' s isTest drop val') :
    (∀ q ∈ prem, nu val q = nu val' q) → ∀ c ∈ concl, nu val c = nu val' c := by
  intro hp
  cases hr : s.emul[k]? with
  | none => simp [Just.ok, hr] at hok
  | some row =>
  cases hu : s.unions[u]? with
  | none => simp [Just.ok, hr, hu] at hok
  | some e =>
  obtain ⟨p, o⟩ := e
  cases hz : s.pub[pz]? with
  | none => simp [Just.ok, hr, hu, hz] at hok
  | some ez =>
  obtain ⟨z, sz⟩ := ez
  cases ho : s.pub[po]? with
  | none => cases sz <;> simp [Just.ok, hr, hu, hz, ho] at hok
  | some eo =>
  obtain ⟨o', so⟩ := eo
  cases sz with
  | statement _ => simp [Just.ok, hr, hu, hz, ho] at hok
  | const vz =>
  cases so with
  | statement _ => simp [Just.ok, hr, hu, hz, ho] at hok
  | const vo =>
    simp only [Just.ok, hr, hu, hz, ho, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨ht, hlen⟩, hzw⟩, hpw⟩, hoo⟩, rfl⟩, rfl⟩, hfwd⟩ := hok
    subst hzw hpw hoo
    have hrow : [row.getD 0 0, row.getD 1 0, row.getD 2 0, row.getD 3 0] ∈ (keepP s isTest drop).emul := by
      rw [← list_eq_four hlen]; exact Array.mem_of_getElem? hr
    have hprod : ∀ {st : ℕ → Fin 4 → K} {val : Val}, HoldsP st s isTest drop val →
        Model.ev val (row.getD 0 0) * Model.ev val (row.getD 1 0) = 1 := by
      intro st val h
      have := emul_row_ev h hrow
      rwa [ev_zero_const val _ (h.pub _ _ (Array.mem_of_getElem? hz)), add_zero,
        show Model.ev val (row.getD 3 0) = 1 from by
          simp only [Model.ev, h.union hu ht]
          exact ev_one_const val _ (h.pub _ _ (Array.mem_of_getElem? ho)), eq_comm] at this
    cases fwd
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hfwd
      obtain ⟨rfl, rfl⟩ := hfwd
      have hx := ev_eq_of_limbs3 hp
      apply limbs3_of_ev
      have p1 := hprod h
      have p2 := hprod h'
      rw [← hx, mul_comm] at p2
      rw [mul_comm] at p1
      exact inv_unique p1 p2
    · simp only [↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hfwd
      obtain ⟨rfl, rfl⟩ := hfwd
      have ha := ev_eq_of_limbs3 hp
      apply limbs3_of_ev
      have p2 := hprod h'
      rw [← ha] at p2
      exact inv_unique (hprod h) p2

theorem ok_union {c : ℕ} {prem concl : List ℕ} (hok : (Just.union c).ok s isTest claims drop prem concl = true)
    (hu : UnionsValid claims val val') :
    (∀ q ∈ prem, nu val q = nu val' q) → ∀ n ∈ concl, nu val n = nu val' n := by
  intro hp
  cases hc : claims[c]? with
  | none => simp [Just.ok, hc] at hok
  | some uc =>
    simp only [Just.ok, hc, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨rfl, rfl⟩ := hok
    refine limbs3_of_ev (hu uc (Array.mem_of_getElem? hc) fun w hw => eq_of_limbs4 fun n hn => hp n ?_)
    exact List.mem_flatMap.mpr ⟨w, hw, hn⟩

/-- A justified rule is valid on two assignments holding every constraint but the tests, under the premises, its
premises among the nodes `L` the collision premises are asked on. -/
theorem Just.valid (j : Just) {prem concl : List ℕ} {L : ℕ → Prop} (hok : j.ok s isTest claims drop prem concl = true)
    (h : HoldsP st s isTest drop val) (h' : HoldsP st' s isTest drop val') (hcr : HashCRP s drop L val val')
    (hw : WindowCRP s drop L val val') (hu : UnionsValid claims val val') (hL : ∀ q ∈ prem, L q) :
    (∀ q ∈ prem, nu val q = nu val' q) → ∀ c ∈ concl, nu val c = nu val' c := by
  cases j with
  | form => exact ok_form hok h h'
  | pubConst => exact ok_pubConst hok h h'
  | eq => exact ok_eq hok h h'
  | splitWord => exact ok_splitWord hok h h'
  | splitBits => exact ok_splitBits hok h h'
  | mux => exact ok_mux hok h h'
  | compress => exact ok_compress hok h h'
  | collision => exact ok_collision hok hcr hL
  | window => exact ok_window hok hw hL
  | inv => exact ok_inv hok h h'
  | union => exact ok_union hok hu

/-- Every rule whose premises are among the nodes `L` is valid, the collision premises asked only of the rows live on
`L`. -/
theorem rules_valid {r : Rules Just} {L : ℕ → Prop} (hok : rulesOk s isTest claims drop r = true)
    (h : HoldsP st s isTest drop val) (h' : HoldsP st' s isTest drop val') (hcr : HashCRP s drop L val val')
    (hw : WindowCRP s drop L val val') (hu : UnionsValid claims val val') :
    ∀ i < r.size, (∀ q ∈ r.prem i, L q) → Valid r (nu val) (nu val') i := by
  intro i hi hL
  simp only [rulesOk, List.all_eq_true, List.mem_range] at hok
  exact Just.valid _ (hok i hi) h h' hcr hw hu hL

end

/-- Mutation test of the window rule: two blocks of one chaining value, a window from word 1 with both blocks' other
input words as premises passes; the window alone, or one block's other words missing, fails; rows of two chaining
values fail. -/
example :
    (Just.window 0 1 1).ok ({ hash := #[[5, 6], [5, 7]] } : State) (fun _ => false) #[] (fun _ => false)
        (windowIn [5, 6] [5, 7] 1 ++ hashRest [5, 6] ++ hashRest [5, 7]) (hashH [5, 6]) = true ∧
      (Just.window 0 1 1).ok ({ hash := #[[5, 6], [5, 7]] } : State) (fun _ => false) #[] (fun _ => false)
        (windowIn [5, 6] [5, 7] 1) (hashH [5, 6]) = false ∧
      (Just.window 0 1 1).ok ({ hash := #[[5, 6], [5, 7]] } : State) (fun _ => false) #[] (fun _ => false)
        (windowIn [5, 6] [5, 7] 1 ++ hashRest [5, 6]) (hashH [5, 6]) = false ∧
      (Just.window 0 1 1).ok ({ hash := #[[5, 6], [8, 7]] } : State) (fun _ => false) #[] (fun _ => false)
        (windowIn [5, 6] [8, 7] 1 ++ hashRest [5, 6] ++ hashRest [8, 7]) (hashH [5, 6]) = false := by
  decide

end LeanVMCircuits.Rec.Bind
