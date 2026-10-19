/-
  LeanVM.Guest.B1.Whir.CapAgrees

  The openings of one query step agree wherever they meet: the hypothesis `open_stacked`'s
  completeness takes for its shared Merkle caps, and its discharge when the openings are one
  tree's.
-/

module

public import LeanVM.Guest.B1.Whir.Queries
public import LeanVM.Guest.B1.VerifySub.Interface

/-!
# Openings that agree where they meet

`open_stacked` keeps one cap per committed tree, a heap run that every query of the level writes
its path's top into, and whose nodes `verify_merkle_cap` hashes up to the root (TRIAGE #29, #30).
Memory is write-once, so two queries meeting at a node of the cap must climb to the same digest
there, a sibling included. The specification checks each opening alone against the root, so an
opening set can pass it while two of its openings disagree at a node: the root's preimages would
then collide. The honest prover's openings are one tree's, which never disagree.

* `queriesOf p s`: every query step of the run of `p` from `s` (`Compile.run`, deployed hash), each
  as its tree's height and its positions with their openings;
* `NodeIs depth (q, o) v d`: the opening `o` at `q` gives the heap node `v` (the root `1`, the
  children of `v` at `2v`, `2v + 1`) the digest `d`, on its climb or as a sibling;
* `CapAgrees μ r root cv xs os target`: at every query step of `whirOpen μ r target`, two openings
  giving one node a digest give it the same;
* `capAgrees_of_tree`: it holds when every step's openings are the openings of one hash-consistent
  labelling of a tree at the step's positions.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-- **The query steps of a run**: `Compile.run` on the deployed hash, each `query` step listed as
the height of its tree and its positions, each with the opening it consumes. -/
def queriesOf {α : Type} : Prog α → St → List (ℕ × List (ℕ × Opening))
  | .ret _, _ => []
  | .fail, _ => []
  | .read k, s => match s.stream with
    | [] => []
    | x :: xs => queriesOf (k x)
        { s with cv := absorbBlock (m := Id) blake2sBytes s.cv (blockOf x 1), stream := xs }
  | .sample k, s =>
    let cv := absorbBlock (m := Id) blake2sBytes s.cv (blockOf 0 2)
    queriesOf (k (challengeOf cv)) { s with cv := cv }
  | .grind bits k, s => match s.stream with
    | [] => []
    | n :: xs =>
      let base := absorbBlock (m := Id) blake2sBytes s.cv (blockOf 0 3)
      let d := absorbBlock (m := Id) blake2sBytes base (blockOf n 4)
      let cv := absorbBlock (m := Id) blake2sBytes s.cv (blockOf n 4)
      if powOk bits n d then queriesOf k { s with cv := cv, stream := xs } else []
  | .commit height width k, s => match s.stream with
    | x0 :: x1 :: xs =>
      let cv0 := absorbBlock (m := Id) blake2sBytes s.cv (blockOf x0 1)
      let cv1 := absorbBlock (m := Id) blake2sBytes cv0 (blockOf x1 1)
      match digestOfScalars (x0, x1) with
      | some root =>
        queriesOf k { s with cv := cv1, stream := xs, roots := s.roots ++ [(root, height, width)] }
      | none => []
    | _ => []
  | .query i ps k, s => match s.roots[i]? with
    | none => []
    | some (root, height, width) =>
      match openAll (m := Id) blake2sBytes root height width ps s.openings with
      | some (rows, rest) => (height, ps.zip s.openings) :: queriesOf (k rows) { s with openings := rest }
      | none => []

/-- The heap index of the node at level `l` (the leaves at `0`) above the leaf `q` of a tree of
height `depth`. -/
def heapNode (depth q l : ℕ) : ℕ := 2 ^ (depth - l) + q / 2 ^ l

/-- The heap index of the sibling of the node at level `l < depth` above the leaf `q`. -/
def sibNode (depth q l : ℕ) : ℕ := 2 * heapNode depth q (l + 1) + (!q.testBit l).toNat

/-- **The opening `o` at `q` gives the heap node `v` the digest `d`**: `v` is on its climb, with
the climb's digest there, or is the sibling it carries at a level. -/
def NodeIs (depth : ℕ) (a : ℕ × Opening) (v : ℕ) (d : Digest) : Prop :=
  (∃ l ≤ depth, v = heapNode depth a.1 l ∧ d = climbAt (hashWords a.2.leaf) a.1 a.2.path l) ∨
    ∃ l < depth, v = sibNode depth a.1 l ∧ d = a.2.path.getD l default

/-- The openings of one step agree wherever they meet. -/
def BatchAgrees (depth : ℕ) (qs : List (ℕ × Opening)) : Prop :=
  ∀ a ∈ qs, ∀ b ∈ qs, ∀ v d d', NodeIs depth a v d → NodeIs depth b v d' → d = d'

/-- **The shared caps' hypothesis**: at every query step of `whirOpen μ r target` from the chain
state `cv`, the words `xs`, the openings `os` and the committed root, the step's openings agree
wherever they meet. -/
def CapAgrees (μ r : ℕ) (root cv : Digest) (xs : List E) (os : List Opening) (target : E) : Prop :=
  ∀ b ∈ queriesOf (whirOpen μ r target) ⟨cv, xs, os, [(root, stackShape μ r)]⟩, BatchAgrees b.1 b.2

/-! ## One tree's openings agree -/

/-- A labelling of a tree of height `depth` (heap indices) whose inner nodes hash their
children. -/
def TreeLabel (depth : ℕ) (N : ℕ → Digest) : Prop :=
  ∀ v, 1 ≤ v → v < 2 ^ depth → N v = hashPair (N (2 * v)) (N (2 * v + 1))

/-- The opening at `q` is the labelling's: the leaf's digest is the leaf's label and every
sibling is its node's label. -/
def TreeOpening (depth : ℕ) (N : ℕ → Digest) (a : ℕ × Opening) : Prop :=
  a.1 < 2 ^ depth ∧ a.2.path.length = depth ∧ N (2 ^ depth + a.1) = hashWords a.2.leaf ∧
    ∀ l < depth, a.2.path.getD l default = N (sibNode depth a.1 l)

theorem heapNode_succ {depth q l : ℕ} (hl : l < depth) :
    heapNode depth q l = 2 * heapNode depth q (l + 1) + (q.testBit l).toNat := by
  unfold heapNode
  have h2 : 2 ^ (depth - l) = 2 * 2 ^ (depth - (l + 1)) := by
    rw [← pow_succ']; congr 1; omega
  have hd : q / 2 ^ (l + 1) = q / 2 ^ l / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  have hb : (q.testBit l).toNat = q / 2 ^ l % 2 := by
    rw [Nat.toNat_testBit]
  rw [h2, hd, hb]
  have := Nat.div_add_mod (q / 2 ^ l) 2
  omega

/-- On a labelling's opening, the climb's digest at level `l` is the node's label. -/
theorem climbAt_label {depth : ℕ} {N : ℕ → Digest} (hN : TreeLabel depth N) {a : ℕ × Opening}
    (ha : TreeOpening depth N a) : ∀ l ≤ depth,
      climbAt (hashWords a.2.leaf) a.1 a.2.path l = N (heapNode depth a.1 l) := by
  obtain ⟨hq, hlen, hleaf, hsib⟩ := ha
  intro l
  induction l with
  | zero => intro _; rw [climbAt_zero, heapNode, Nat.sub_zero, pow_zero, Nat.div_one, hleaf]
  | succ l ih =>
    intro hl
    have hv1 : 1 ≤ heapNode depth a.1 (l + 1) := Nat.le_add_right_of_le Nat.one_le_two_pow
    have hv2 : heapNode depth a.1 (l + 1) < 2 ^ depth := by
      unfold heapNode
      have h1 : a.1 / 2 ^ (l + 1) < 2 ^ (depth - (l + 1)) := by
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show depth - (l + 1) + (l + 1) = depth by omega]
        exact hq
      have h2 : 2 ^ (depth - (l + 1)) * 2 ≤ 2 ^ depth := by
        rw [← pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hl' : l < a.2.path.length := by omega
    rw [climbAt_succ _ _ _ hl', ih (by omega), hsib l (by omega), hN _ hv1 hv2,
      heapNode_succ (l := l) (by omega), sibNode]
    cases a.1.testBit l <;> rfl

/-- What an opening of the labelling gives a node is its label. -/
theorem nodeIs_label {depth : ℕ} {N : ℕ → Digest} (hN : TreeLabel depth N) {a : ℕ × Opening}
    (ha : TreeOpening depth N a) {v : ℕ} {d : Digest} (h : NodeIs depth a v d) : d = N v := by
  rcases h with ⟨l, hl, rfl, rfl⟩ | ⟨l, hl, rfl, rfl⟩
  · exact climbAt_label hN ha l hl
  · exact ha.2.2.2 l hl

/-- **One tree's openings agree**: when every query step's openings are, at the step's
positions, the openings of one hash-consistent labelling of a tree of the step's height, the
shared caps' hypothesis holds. -/
theorem capAgrees_of_tree {μ r : ℕ} {root cv : Digest} {xs : List E} {os : List Opening} {target : E}
    (h : ∀ b ∈ queriesOf (whirOpen μ r target) ⟨cv, xs, os, [(root, stackShape μ r)]⟩,
      ∃ N, TreeLabel b.1 N ∧ ∀ a ∈ b.2, TreeOpening b.1 N a) :
    CapAgrees μ r root cv xs os target := by
  intro b hb a ha a' ha' v d d' hd hd'
  obtain ⟨N, hN, hall⟩ := h b hb
  rw [nodeIs_label hN (hall a ha) hd, nodeIs_label hN (hall a' ha') hd']

end
end LeanVM.Guest.B1
