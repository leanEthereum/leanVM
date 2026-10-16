module

public import LeanVMCircuits.Rec.DesignClaims

@[expose] public section

/-!
A node's statement digest, from the dumps (`Design::node`'s digest and `Reduced::statement`'s halves): a wrap states its only child's digest; a node of a tree of outputs states `Kind::Node::digest_rows` of its children's digests, each read from the child's statement words with `halves_to_d` and split with `d_to_k`; either digest is exposed as `digest_halves_rows` writes it, at statement positions 1 and 2.

A `DigestCert` names those calls and `DigestCert.ok` checks them against a dump's calls and outputs. `DigestCert.exposed`: in any assignment where every call holds, the statement's digest words are the digest wire's limbs, top limbs zero. `DigestCert.wrap_states`: a wrap's statement digest is its child's. `DigestCert.node_states`: a node's statement digest is the tree statement digest (`treeDigest`) of the node's tag and its children's digests. `checkedges` finds and checks the certificate for every wrap and every node of a tree of outputs among the dumps. `wrap_mutations` and `node_mutations`: the check rejects the halves exposed swapped or at the other positions, a nonzero top limb, another child count, a wrong header count, the children hashed out of order and a digest read from another child's words.
-/

namespace LeanVMCircuits.Rec.Edges

open LeanVMCircuits.Rec Model

/-- Where a node's statement digest comes from: a wrap's `halves_to_d` of its child's digest words, or a node's `chain` over its header's `k_const`s and each child's `halves_to_d` and `d_to_k`. -/
inductive DigestSrc where
  | wrap (hd : ℕ)
  | node (ch : ℕ) (header : List ℕ) (reads : List (ℕ × ℕ))
  deriving DecidableEq, Repr

/-- The calls by which a node exposes its digest: the digest's `d_to_k`, the `k_const 0`, the halves' `k_to_e`s and their `expose_e`s. -/
structure DigestCert where
  src : DigestSrc
  dk : ℕ
  z : ℕ
  h0 : ℕ
  h1 : ℕ
  e1 : ℕ
  e2 : ℕ
  deriving DecidableEq, Repr

/-- The digest's wire. -/
def DigestSrc.wire (os : Array (List ℕ)) : DigestSrc → ℕ
  | .wrap hd => out os hd 0
  | .node ch _ _ => out os ch 0

/-- A child's digest read: `halves_to_d` of its statement words 1 and 2, then `d_to_k`. -/
def readOk (cs : Array Call) (os : Array (List ℕ)) (ws : List ℕ) (r : ℕ × ℕ) : Bool :=
  cs[r.1]? == some (.halvesToD (ws.getD 1 0) (ws.getD 2 0)) && cs[r.2]? == some (.dToK (out os r.1 0))

/-- The header `Kind::Node::header` writes for `n` items. -/
def nodeHeader (n : ℕ) : List ℕ := [DesignClaims.tagNode, n, 0, 0, 0, 0, 0, 0]

/-- The words a node's `chain` hashes: its header's wires, then each child's digest words. -/
def chainWords (os : Array (List ℕ)) (header : List ℕ) (reads : List (ℕ × ℕ)) : List ℕ :=
  header.map (out os · 0) ++ reads.flatMap fun r => (List.range 4).map (out os r.2 ·)

def DigestSrc.ok (cs : Array Call) (os : Array (List ℕ)) (children : List (List ℕ)) : DigestSrc → Bool
  | .wrap hd => children.length == 1 &&
      cs[hd]? == some (.halvesToD ((children.headD []).getD 1 0) ((children.headD []).getD 2 0))
  | .node ch header reads => header.length == 8 && reads.length == children.length &&
      (List.range 8).all (fun i => cs[header.getD i 0]? == some (.kConst ((nodeHeader children.length).getD i 0))) &&
      (children.zip reads).all (fun p => readOk cs os p.1 p.2) && cs[ch]? == some (.chain (chainWords os header reads))

/-- The certificate checks: its source, the digest's `d_to_k`, the zero, the halves and their exposures at statement positions 1 and 2. -/
def DigestCert.ok (cs : Array Call) (os : Array (List ℕ)) (children : List (List ℕ)) (c : DigestCert) : Bool :=
  c.src.ok cs os children && cs[c.dk]? == some (.dToK (c.src.wire os)) && cs[c.z]? == some (.kConst 0) &&
    cs[c.h0]? == some (.kToE (out os c.dk 0) (out os c.dk 1) (out os c.z 0)) &&
    cs[c.h1]? == some (.kToE (out os c.dk 2) (out os c.dk 3) (out os c.z 0)) &&
    cs[c.e1]? == some (.exposeE (out os c.h0 0)) && out os c.e1 0 == 1 &&
    cs[c.e2]? == some (.exposeE (out os c.h1 0)) && out os c.e2 0 == 2

section

variable {cs : Array Call} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}

theorem ofWord_zero_limb : limbsOf [0, 0, 0, 0] 0 = 0 := by simp [limbsOf, ofWord_zero]

/-- The statement's digest words are the digest wire's limbs, each half's top limb zero. -/
theorem DigestCert.exposed (hF : AllHold cs os st val) {children : List (List ℕ)} {c : DigestCert}
    (hok : c.ok cs os children = true) :
    (st 1 0 = val (c.src.wire os) 0 ∧ st 1 1 = val (c.src.wire os) 1 ∧ st 1 2 = 0) ∧
      (st 2 0 = val (c.src.wire os) 2 ∧ st 2 1 = val (c.src.wire os) 3 ∧ st 2 2 = 0) := by
  simp only [DigestCert.ok, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hdk⟩, hz⟩, hh0⟩, hh1⟩, he1⟩, ho1⟩, he2⟩, ho2⟩ := hok
  have Hdk : ∀ i : Fin 4, val (out os c.dk i) 0 = val (c.src.wire os) i := holds_at hF hdk
  have D0 : val (out os c.dk 0) 0 = val (c.src.wire os) 0 := Hdk 0
  have D1 : val (out os c.dk 1) 0 = val (c.src.wire os) 1 := Hdk 1
  have D2 : val (out os c.dk 2) 0 = val (c.src.wire os) 2 := Hdk 2
  have D3 : val (out os c.dk 3) 0 = val (c.src.wire os) 3 := Hdk 3
  have Hz : val (out os c.z 0) = limbsOf [0, 0, 0, 0] := holds_at hF hz
  have Hh0 : Model.ev val (out os c.h0 0) = toE (val (out os c.dk 0) 0) (val (out os c.dk 1) 0) (val (out os c.z 0) 0) :=
    holds_at hF hh0
  have Hh1 : Model.ev val (out os c.h1 0) = toE (val (out os c.dk 2) 0) (val (out os c.dk 3) 0) (val (out os c.z 0) 0) :=
    holds_at hF hh1
  have He1 : val (out os c.h0 0) = st (out os c.e1 0) := holds_at hF he1
  have He2 : val (out os c.h1 0) = st (out os c.e2 0) := holds_at hF he2
  rw [ho1] at He1
  rw [ho2] at He2
  rw [Hz, ofWord_zero_limb, Model.ev, He1, D0, D1] at Hh0
  rw [Hz, ofWord_zero_limb, Model.ev, He2, D2, D3] at Hh1
  obtain ⟨a0, a1, a2⟩ := toE_injective _ _ _ _ _ _ Hh0
  obtain ⟨b0, b1, b2⟩ := toE_injective _ _ _ _ _ _ Hh1
  exact ⟨⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩⟩

/-- A wrap states its child's digest: where the child's words carry statement `stc`, the wrap's statement digest words are `stc`'s. -/
theorem DigestCert.wrap_states (hF : AllHold cs os st val) {ws : List ℕ} {c : DigestCert} {hd : ℕ}
    (hsrc : c.src = .wrap hd) (hok : c.ok cs os [ws] = true) (stc : ℕ → Fin 4 → K)
    (hpub : ∀ i < 3, val (ws.getD i 0) = stc i) :
    st 1 0 = stc 1 0 ∧ st 1 1 = stc 1 1 ∧ st 2 0 = stc 2 0 ∧ st 2 1 = stc 2 1 := by
  obtain ⟨⟨e0, e1, -⟩, ⟨e2, e3, -⟩⟩ := c.exposed hF hok
  simp only [DigestCert.ok, Bool.and_eq_true] at hok
  have hs := hok.1.1.1.1.1.1.1.1
  rw [hsrc] at hs e0 e1 e2 e3
  simp only [DigestSrc.ok, Bool.and_eq_true, beq_iff_eq, List.headD_cons] at hs
  obtain ⟨H0, H1, H2, H3, -, -⟩ := holds_at hF hs.2
  simp only [DigestSrc.wire] at e0 e1 e2 e3
  rw [hpub 1 (by norm_num)] at H0 H1
  rw [hpub 2 (by norm_num)] at H2 H3
  exact ⟨e0.trans H0, e1.trans H1, e2.trans H2, e3.trans H3⟩

/-- A node of a tree of outputs states the tree statement digest of its tag and its children's digests, each the `d_to_k` of its read: where every call holds, the statement's digest is `digest (treeDigest tag items)`, the items the reads' words. -/
theorem DigestCert.node_states (hF : AllHold cs os st val) {children : List (List ℕ)} {c : DigestCert} {ch : ℕ}
    {header : List ℕ} {reads : List (ℕ × ℕ)} (hsrc : c.src = .node ch header reads) (hok : c.ok cs os children = true)
    (hn : children.length < 2 ^ 64) :
    words4 (val (out os ch 0)) = digest (treeDigest (BitVec.ofNat 64 DesignClaims.tagNode)
      (reads.map fun r (k : Fin 4) => w64 val (out os r.2 k))) := by
  simp only [DigestCert.ok, Bool.and_eq_true] at hok
  have hs := hok.1.1.1.1.1.1.1.1
  rw [hsrc] at hs
  simp only [DigestSrc.ok, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hs
  obtain ⟨⟨⟨⟨hl8, hlr⟩, hhead⟩, -⟩, hch⟩ := hs
  have H : words4 (val (out os ch 0)) = digest (hashWords ((chainWords os header reads).map (w64 val))) :=
    holds_at hF hch
  rw [H, treeDigest, List.length_map, hlr]
  congr 2
  rw [chainWords, List.map_append]
  congr 1
  · apply List.ext_getElem (by simp [hl8])
    intro i h1 h2
    have h8 : i < 8 := by simpa using h2
    have hc := hhead i h8
    have Hc : val (out os (header.getD i 0) 0) = limbsOf [(nodeHeader children.length).getD i 0, 0, 0, 0] :=
      holds_at hF (by simpa using hc)
    have hi : i < header.length := by simpa using h1
    rw [List.getElem_map, List.getElem_map]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at Hc
    have htag : DesignClaims.tagNode < 2 ^ 64 := by decide
    interval_cases i <;> simp only [nodeHeader, List.getD_cons_zero, List.getD_cons_succ] at Hc <;>
      first
      | exact DesignClaims.w64_const Hc htag
      | exact DesignClaims.w64_const Hc hn
      | exact (DesignClaims.w64_const Hc (by norm_num)).trans rfl
  · rw [List.map_flatMap, List.flatMap_map]
    congr 1

end

/-! Mutations `DigestCert.ok` rejects, on small call lists. -/

/-- A wrap of a child of words `0, 1, 2`: the read, the digest's `d_to_k`, the zero, the halves and their exposures. -/
def wrapCalls : Array Call :=
  #[.halvesToD 1 2, .dToK 3, .kConst 0, .kToE 4 5 8, .kToE 6 7 8, .exposeE 9, .exposeE 10]

def wrapOuts : Array (List ℕ) := #[[3], [4, 5, 6, 7], [8], [9], [10], [1], [2]]

def wrapCert : DigestCert := ⟨.wrap 0, 1, 2, 3, 4, 5, 6⟩

/-- The wrap's certificate checks; it fails with the halves exposed swapped, the zero another constant, the halves at statement positions 2 and 1, or a second child. -/
theorem wrap_mutations :
    wrapCert.ok wrapCalls wrapOuts [[0, 1, 2]] = true ∧
      wrapCert.ok (#[.halvesToD 1 2, .dToK 3, .kConst 0, .kToE 6 7 8, .kToE 4 5 8, .exposeE 9, .exposeE 10])
        wrapOuts [[0, 1, 2]] = false ∧
      wrapCert.ok (wrapCalls.set! 2 (.kConst 1)) wrapOuts [[0, 1, 2]] = false ∧
      wrapCert.ok wrapCalls ((wrapOuts.set! 5 [2]).set! 6 [1]) [[0, 1, 2]] = false ∧
      wrapCert.ok wrapCalls wrapOuts [[0, 1, 2], [0, 1, 2]] = false := by
  decide

/-- A node of two children of words `0, 1, 2` and `3, 4, 5`: each child's read, the header, the `chain`, then the exposure as for a wrap. -/
def nodeCalls (count : ℕ) (reads : List ℕ) : Array Call :=
  #[.halvesToD 1 2, .dToK 6, .halvesToD 4 5, .dToK 11,
    .kConst DesignClaims.tagNode, .kConst count, .kConst 0, .kConst 0, .kConst 0, .kConst 0, .kConst 0, .kConst 0,
    .chain ([16, 17, 18, 19, 20, 21, 22, 23] ++ reads), .dToK 24, .kConst 0, .kToE 25 26 29, .kToE 27 28 29,
    .exposeE 30, .exposeE 31]

def nodeOuts : Array (List ℕ) :=
  #[[6], [7, 8, 9, 10], [11], [12, 13, 14, 15], [16], [17], [18], [19], [20], [21], [22], [23], [24],
    [25, 26, 27, 28], [29], [30], [31], [1], [2]]

def nodeCert : DigestCert := ⟨.node 12 [4, 5, 6, 7, 8, 9, 10, 11] [(0, 1), (2, 3)], 13, 14, 15, 16, 17, 18⟩

/-- The node's certificate checks; it fails with the header's count wrong, the children's digests hashed in the other order, or one child's digest read from the other's words. -/
theorem node_mutations :
    nodeCert.ok (nodeCalls 2 [7, 8, 9, 10, 12, 13, 14, 15]) nodeOuts [[0, 1, 2], [3, 4, 5]] = true ∧
      nodeCert.ok (nodeCalls 3 [7, 8, 9, 10, 12, 13, 14, 15]) nodeOuts [[0, 1, 2], [3, 4, 5]] = false ∧
      nodeCert.ok (nodeCalls 2 [12, 13, 14, 15, 7, 8, 9, 10]) nodeOuts [[0, 1, 2], [3, 4, 5]] = false ∧
      nodeCert.ok (nodeCalls 2 [7, 8, 9, 10, 12, 13, 14, 15]) nodeOuts [[0, 1, 2], [0, 1, 2]] = false := by
  decide

end LeanVMCircuits.Rec.Edges
