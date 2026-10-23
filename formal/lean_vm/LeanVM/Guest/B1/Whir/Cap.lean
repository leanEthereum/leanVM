/-
  LeanVM.Guest.B1.Whir.Cap

  B1 for the Merkle cap: `hash_cap_node` as a block, `verify_merkle_cap` at its five depths with
  its loops, and the cap's root at the end of every path its flags mark.
-/

module

public import LeanVM.Guest.B1.FiatShamir

/-!
# The Merkle cap (TRIAGE #29, #30)

The cap of a level's tree is a heap run `cap` of two cells per node, node `i` (the root `1`, the
children of `i` at `2i`, `2i + 1`) at `cap·g^(2i)`, `cap·g^(2i+1)`, and a run `flags` of one word
per node, both hinted (`merkle_caps`, `merkle_cap_active`). `opening_queries` stores each queried
path's top at its cap leaf and `flags[parent] = 1` (G:1032-1043).

* `hash_cap_node(cap, c)` (G:919-926) hashes node `c`'s children into it: `hashCapNodeT` at a
  runtime index, `HashCapSem`, which at `c = g^i` is `CapHashed rd cap i`, node `i` the
  `hashPair` (`Spec/Blake2s.lean:205`) of its children's digests.
* `verify_merkle_cap(cap, flags, D)` (G:929-940) hashes the root and sets `flags[1] = 1`, then
  for every node `c` in `[2, 2^D)` whose flag is nonzero sets its parent's flag to `1` and hashes
  it (`CapFlagged`). Its loop `__loopK` runs over the parents `g^p`, `1 ≤ p < 2^(D-1)`, both
  sides unrolled (`capLoopBody`, one helper per depth, all with that body).
* **The refutation argument** (`cap_climb`): a flag the prover hints as `0` on a queried path
  would leave that path unchecked, but its child's flag is nonzero, so the parent's flag is
  written `1`, and memory is write-once. So from a cap leaf whose parent's flag is `1`, every
  ancestor is hashed, and `climb` (V:526) from the leaf over the cap's siblings ends at the root.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Memory words -/

/-- The word at `p·g^k`, or `0`: the honest value of a load. -/
def memAt (rd : Reader) (p : E) (k : ℕ) : E := (rd (p.limb 0 * Parameters.gpow k)).getD 0

theorem memAt_of_load {p w : E} {k : ℕ} (h : LoadHolds rd p k w) : memAt rd p k = w := by
  simp [memAt, h.2]

theorem loadHolds_memAt {p w : E} {k : ℕ} (h : LoadHolds rd p k w) : LoadHolds rd p k (memAt rd p k) := by
  rwa [memAt_of_load h]

theorem gen_pow_mul_gen_pow (a b : ℕ) : gen ^ a * gen ^ b = gen ^ (a + b) := (pow_add gen a b).symm

theorem loadHolds_gen_pow (rd : Reader) (p : E) (j : ℕ) (w : E) :
    LoadHolds rd (p * gen ^ j) 0 w ↔ LoadHolds rd p j w := by
  rw [loadHolds_mul_gen_pow, Nat.add_zero]

/-! ## Cap nodes -/

/-- The cells of cap node `i` are the digest `d`'s. -/
def CapCell (rd : Reader) (cap : E) (i : ℕ) (d : Digest) : Prop :=
  LoadHolds rd cap (2 * i) (digestScalars d).1 ∧ LoadHolds rd cap (2 * i + 1) (digestScalars d).2

/-- Cap node `i` is the `hashPair` of its children's digests. -/
def CapHashed (rd : Reader) (cap : E) (i : ℕ) : Prop :=
  ∃ l r : Digest, CapCell rd cap (2 * i) l ∧ CapCell rd cap (2 * i + 1) r ∧
    CapCell rd cap i (hashPair l r)

theorem CapCell.unique {cap : E} {i : ℕ} {d d' : Digest} (h : CapCell rd cap i d)
    (h' : CapCell rd cap i d') : d = d' := by
  have e0 := Option.some.inj (h.1.2.symm.trans h'.1.2)
  have e1 := Option.some.inj (h.2.2.symm.trans h'.2.2)
  exact digestScalars_injective (Prod.ext e0 e1)

/-- The bytes of a block of two digests' cells. -/
theorem blockBytes_digests (l r : Digest) :
    blockBytes ![(digestScalars l).1, (digestScalars l).2, (digestScalars r).1, (digestScalars r).2] =
      digestBytes l ++ digestBytes r := by
  rw [digestBytes_eq, digestBytes_eq]
  simp only [blockBytes, List.append_assoc]
  rfl

/-- **One cap node, hashed**: a compression of four cells under the IV is the `hashPair` of
the two digests they are. -/
theorem compress_hashPair {m : Fin 4 → E} {o0 o1 : E}
    (hc : CompressCells m Value.ivCells.1 Value.ivCells.2 o0 o1 (metadataCell 64 true)) :
    ∃ l r : Digest, (m 0, m 1) = digestScalars l ∧ (m 2, m 3) = digestScalars r ∧
      (o0, o1) = digestScalars (hashPair l r) := by
  obtain ⟨l, hl⟩ := exists_digest (hc.1 0) (hc.1 1)
  obtain ⟨r, hr⟩ := exists_digest (hc.1 2) (hc.1 3)
  refine ⟨l, r, hl, hr, ?_⟩
  have hm : m = ![(digestScalars l).1, (digestScalars l).2, (digestScalars r).1,
      (digestScalars r).2] := by
    funext i
    fin_cases i
    · exact congrArg Prod.fst hl
    · exact congrArg Prod.snd hl
    · exact congrArg Prod.fst hr
    · exact congrArg Prod.snd hr
  rw [blake2s_default hc, hm, blockBytes_digests]
  rfl

theorem compress_of_hashPair (l r : Digest) :
    CompressCells ![(digestScalars l).1, (digestScalars l).2, (digestScalars r).1, (digestScalars r).2]
      Value.ivCells.1 Value.ivCells.2 (digestScalars (hashPair l r)).1 (digestScalars (hashPair l r)).2
      (metadataCell 64 true) := by
  refine (blake2s_default_iff fun i => ?_).mpr ?_
  · fin_cases i
    exacts [(isCanonical128_digestScalars l).1, (isCanonical128_digestScalars l).2,
      (isCanonical128_digestScalars r).1, (isCanonical128_digestScalars r).2]
  · rw [blockBytes_digests]
    rfl

/-! ## `hash_cap_node` -/

/-- `hash_cap_node(cap, c)` (G:919-926) at a runtime index `c`, its first value `b`: the
children at `cap·c^4`, the parent stored at `cap·c²`, `cap·g·c²`. -/
def hashCapNodeT (cap c : V) (b : ℕ) : List Stmt :=
  [.atom (.mul (.n b) c c), .atom (.mul (.n (b + 1)) (.n b) (.n b)),
    .atom (.mul (.n (b + 2)) cap (.n (b + 1))),
    .atom (.load (.n (b + 3)) (.n (b + 2)) 0), .atom (.load (.n (b + 4)) (.n (b + 2)) 1),
    .atom (.load (.n (b + 5)) (.n (b + 2)) 2), .atom (.load (.n (b + 6)) (.n (b + 2)) 3),
    .atom (.const (.n (b + 7)) (word 13503953895743350343 11912009169889063794 0)),
    .atom (.const (.n (b + 8)) (word 11170449402626986623 6620516960021240235 0)),
    .atom (.const (.n (b + 9)) (word 64 4294967295 0)),
    .atom (.blake2s (.n (b + 3)) (.n (b + 4)) (.n (b + 5)) (.n (b + 6)) (.n (b + 7)) (.n (b + 8))
      (.n (b + 10)) (.n (b + 11)) (.n (b + 9))),
    .atom (.mul (.n (b + 12)) c c), .atom (.mul (.n (b + 13)) cap (.n (b + 12))),
    .atom (.load (.n (b + 10)) (.n (b + 13)) 0),
    .atom (.const (.n (b + 14)) (word 2 0 0)), .atom (.mul (.n (b + 15)) (.n (b + 14)) c),
    .atom (.mul (.n (b + 16)) (.n (b + 15)) c), .atom (.mul (.n (b + 17)) cap (.n (b + 16))),
    .atom (.load (.n (b + 11)) (.n (b + 17)) 0)]

/-- What `hash_cap_node(cap, c)` asks of memory: the four children cells at `cap·c^4`
compress, under the IV, to the two cells at `cap·c²` and `cap·g·c²`. -/
def HashCapSem (rd : Reader) (cap c : E) : Prop :=
  ∃ m0 m1 m2 m3 o0 o1 : E, LoadHolds rd (cap * (c * c * (c * c))) 0 m0 ∧
    LoadHolds rd (cap * (c * c * (c * c))) 1 m1 ∧ LoadHolds rd (cap * (c * c * (c * c))) 2 m2 ∧
    LoadHolds rd (cap * (c * c * (c * c))) 3 m3 ∧
    CompressCells ![m0, m1, m2, m3] Value.ivCells.1 Value.ivCells.2 o0 o1 (metadataCell 64 true) ∧
    LoadHolds rd (cap * (c * c)) 0 o0 ∧ LoadHolds rd (cap * (gen * c * c)) 0 o1

/-- The children cells `hash_cap_node` reads. -/
def hcnBlock (rd : Reader) (cap c : E) : Fin 4 → E :=
  ![memAt rd (cap * (c * c * (c * c))) 0, memAt rd (cap * (c * c * (c * c))) 1,
    memAt rd (cap * (c * c * (c * c))) 2, memAt rd (cap * (c * c * (c * c))) 3]

/-- The honest values of `hashCapNodeT`, from its first. -/
def hcnVals (rd : Reader) (cap c : E) : List E :=
  [c * c, c * c * (c * c), cap * (c * c * (c * c)), memAt rd (cap * (c * c * (c * c))) 0,
    memAt rd (cap * (c * c * (c * c))) 1, memAt rd (cap * (c * c * (c * c))) 2,
    memAt rd (cap * (c * c * (c * c))) 3, Value.ivCells.1, Value.ivCells.2, metadataCell 64 true,
    (digestScalars (blake2sBytes (blockBytes (hcnBlock rd cap c)))).1,
    (digestScalars (blake2sBytes (blockBytes (hcnBlock rd cap c)))).2,
    c * c, cap * (c * c), gen, gen * c, gen * c * c, cap * (gen * c * c)]

theorem length_hcnVals (rd : Reader) (cap c : E) : (hcnVals rd cap c).length = 18 := rfl

theorem hashCapNodeT_sound {cap c : V} {b : ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (hashCapNodeT cap c b) next kret) :
    HashCapSem rd (σ cap) (σ c) ∧ next := by
  simp only [hashCapNodeT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_iv0, word_iv1, word_md64,
    word_gen] at h
  obtain ⟨h0, h1, h2, l3, l4, l5, l6, h7, h8, h9, hc, h12, h13, l10, h14, h15, h16, h17, l11, hn⟩ := h
  rw [h1, h0] at h2
  rw [h2] at l3 l4 l5 l6
  rw [h7, h8, h9] at hc
  rw [h13, h12] at l10
  rw [h17, h16, h15, h14] at l11
  exact ⟨⟨_, _, _, _, _, _, l3, l4, l5, l6, hc, l10, l11⟩, hn⟩

theorem hashCapNodeT_complete {cap c : V} {b : ℕ} {next : Prop} {kret : List E → Prop}
    (hv : ∀ k < 18, σ (.n (b + k)) = (hcnVals rd (σ cap) (σ c)).getD k 0)
    (hs : HashCapSem rd (σ cap) (σ c)) (hn : next) :
    Stmt.HoldsList C rd σ (hashCapNodeT cap c b) next kret := by
  obtain ⟨m0, m1, m2, m3, o0, o1, a0, a1, a2, a3, hc, l0, l1⟩ := hs
  have hmb : hcnBlock rd (σ cap) (σ c) = ![m0, m1, m2, m3] := by
    rw [hcnBlock, memAt_of_load a0, memAt_of_load a1, memAt_of_load a2, memAt_of_load a3]
  have ho := blake2s_default hc
  have v : ∀ k (hk : k < 18), σ (.n (b + k)) = (hcnVals rd (σ cap) (σ c)).getD k 0 := hv
  have v0 := v 0 (by omega)
  have v1 := v 1 (by omega)
  have v2 := v 2 (by omega)
  have v3 := v 3 (by omega)
  have v4 := v 4 (by omega)
  have v5 := v 5 (by omega)
  have v6 := v 6 (by omega)
  have v7 := v 7 (by omega)
  have v8 := v 8 (by omega)
  have v9 := v 9 (by omega)
  have v10 := v 10 (by omega)
  have v11 := v 11 (by omega)
  have v12 := v 12 (by omega)
  have v13 := v 13 (by omega)
  have v14 := v 14 (by omega)
  have v15 := v 15 (by omega)
  have v16 := v 16 (by omega)
  have v17 := v 17 (by omega)
  simp only [hcnVals, List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero, hmb, ← ho,
    memAt_of_load a0, memAt_of_load a1, memAt_of_load a2, memAt_of_load a3] at v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
  simp only [hashCapNodeT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, word_iv0, word_iv1, word_md64,
    word_gen]
  rw [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17]
  exact ⟨rfl, rfl, rfl, a0, a1, a2, a3, rfl, rfl, rfl, hc, rfl, rfl, l0, rfl, rfl, rfl, rfl, l1, hn⟩

/-- **`hash_cap_node` at `g^i`**: node `i` is the `hashPair` of its children. -/
theorem hashCapSem_gen_pow (rd : Reader) (cap : E) (i : ℕ) :
    HashCapSem rd cap (gen ^ i) ↔ CapHashed rd cap i := by
  have e4 : gen ^ i * gen ^ i * (gen ^ i * gen ^ i) = gen ^ (4 * i) := by
    simp only [gen_pow_mul_gen_pow]; congr 1; ring
  have e2 : gen ^ i * gen ^ i = gen ^ (2 * i) := by rw [gen_pow_mul_gen_pow]; congr 1; ring
  have e2' : gen * gen ^ i * gen ^ i = gen ^ (2 * i + 1) := by
    rw [← pow_succ', gen_pow_mul_gen_pow]; congr 1; ring
  simp only [HashCapSem, CapHashed, CapCell]
  rw [e4, e2', e2]
  simp only [loadHolds_mul_gen_pow, Nat.add_zero, show 4 * i = 2 * (2 * i) by ring,
    show 2 * (2 * i) + 2 = 2 * (2 * i + 1) by ring, show 2 * (2 * i) + 3 = 2 * (2 * i + 1) + 1 by ring]
  constructor
  · rintro ⟨m0, m1, m2, m3, o0, o1, a0, a1, a2, a3, hc, l0, l1⟩
    obtain ⟨l, r, hl, hr, ho⟩ := compress_hashPair hc
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three] at hl hr
    rw [show m0 = _ from congrArg Prod.fst hl] at a0
    rw [show m1 = _ from congrArg Prod.snd hl] at a1
    rw [show m2 = _ from congrArg Prod.fst hr] at a2
    rw [show m3 = _ from congrArg Prod.snd hr] at a3
    rw [show o0 = _ from congrArg Prod.fst ho] at l0
    rw [show o1 = _ from congrArg Prod.snd ho] at l1
    exact ⟨l, r, ⟨a0, a1⟩, ⟨a2, a3⟩, l0, l1⟩
  · rintro ⟨l, r, ⟨l0, l1⟩, ⟨r0, r1⟩, h0, h1⟩
    exact ⟨_, _, _, _, _, _, l0, l1, r0, r1, compress_of_hashPair l r, h0, h1⟩

/-! ## The loop of `verify_merkle_cap` -/

/-- One side of the loop's body (G:935-939) at the child `c` of the parent `x`, first value
`b`: load the child's flag; if nonzero, set the parent's and hash the child. -/
def capSideT (flags cap x c : V) (b : ℕ) : List Stmt :=
  [.atom (.mul (.n b) flags c), .atom (.load (.n (b + 1)) (.n b) 0),
    .ite (.n (b + 1)) [] ([.atom (.const (.n (b + 2)) (word 1 0 0)), .atom (.mul (.n (b + 3)) flags x),
      .atom (.load (.n (b + 2)) (.n (b + 3)) 0)] ++ hashCapNodeT cap c (b + 4))]

/-- What one side asks: the child's flag is in `K`, and if nonzero the parent's flag is `1` and
the child is hashed. -/
def CapSideSem (rd : Reader) (flags cap x c : E) : Prop :=
  ∃ f, LoadHolds rd (flags * c) 0 f ∧ IsInK f ∧
    (f ≠ 0 → LoadHolds rd (flags * x) 0 1 ∧ HashCapSem rd cap c)

/-- The honest values of `capSideT`, from its first. -/
def capSideVals (rd : Reader) (flags cap x c : E) : List E :=
  [flags * c, memAt rd (flags * c) 0, 1, flags * x] ++ hcnVals rd cap c

theorem length_capSideVals (rd : Reader) (flags cap x c : E) :
    (capSideVals rd flags cap x c).length = 22 := rfl

theorem holds_capSideT (flags cap x c : V) (b : ℕ) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (capSideT flags cap x c b) next kret ↔
      Stmt.HoldsList C rd σ (capSideT flags cap x c b) True kret ∧ next :=
  holdsList_noRet _ rfl next kret

theorem capSideT_sound {flags cap x c : V} {b : ℕ} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (capSideT flags cap x c b) True kret) :
    CapSideSem rd (σ flags) (σ cap) (σ x) (σ c) := by
  simp only [capSideT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, holdsList_append, word_one] at h
  obtain ⟨h0, l1, hK, -, hnz⟩ := h
  refine ⟨σ (.n (b + 1)), by rwa [h0] at l1, hK, fun hf => ?_⟩
  obtain ⟨h2, h3, l2, hh⟩ := hnz hf
  rw [h3, h2] at l2
  exact ⟨l2, (hashCapNodeT_sound hh).1⟩

theorem capSideT_complete {flags cap x c : V} {b : ℕ} {kret : List E → Prop}
    (hv : ∀ k < 22, σ (.n (b + k)) = (capSideVals rd (σ flags) (σ cap) (σ x) (σ c)).getD k 0)
    (hs : CapSideSem rd (σ flags) (σ cap) (σ x) (σ c)) :
    Stmt.HoldsList C rd σ (capSideT flags cap x c b) True kret := by
  obtain ⟨f, lf, hK, hnz⟩ := hs
  have v0 : σ (.n b) = σ flags * σ c := hv 0 (by omega)
  have v1 : σ (.n (b + 1)) = f := by rw [hv 1 (by omega)]; exact memAt_of_load lf
  have v2 : σ (.n (b + 2)) = 1 := hv 2 (by omega)
  have v3 : σ (.n (b + 3)) = σ flags * σ x := hv 3 (by omega)
  simp only [capSideT, Stmt.HoldsList, Stmt.Holds, Atom.Holds, holdsList_append, word_one]
  refine ⟨v0, by rw [v0, v1]; exact lf, by rw [v1]; exact hK, fun _ => trivial, fun hf => ?_⟩
  rw [v1] at hf
  obtain ⟨l1, hh⟩ := hnz hf
  refine ⟨v2, v3, by rw [v3, v2]; exact l1, hashCapNodeT_complete (fun k hk => ?_) hh trivial⟩
  rw [show b + 4 + k = b + (k + 4) by ring, hv (k + 4) (by omega), capSideVals,
    List.getD_append_right _ _ _ _ (by simp)]
  rfl

/-- The body of `verify_merkle_cap`'s loop helper `loop` (G:933-939): both sides of the parent
`x`, then the call at `x·g` while it is not the end. -/
def capLoopBody (loop : String) : List Stmt :=
  [.atom (.mul (.n 4) (.n 0) (.n 0))] ++ capSideT (.n 2) (.n 3) (.n 0) (.n 4) 5 ++
    [.atom (.mul (.n 27) (.n 0) (.n 0)), .atom (.const (.n 28) (word 2 0 0)),
      .atom (.mul (.n 29) (.n 27) (.n 28))] ++
    capSideT (.n 2) (.n 3) (.n 0) (.n 29) 30 ++
    [.atom (.const (.n 52) (word 2 0 0)), .atom (.mul (.n 53) (.n 0) (.n 52)),
      .atom (.add (.n 54) (.n 53) (.n 1)), .atom (.const (.n 55) (word 2 0 0)),
      .atom (.mul (.n 56) (.n 0) (.n 55)), .callIf (.n 54) loop [.n 56, .n 1, .n 2, .n 3], .ret []]

/-- The loop's body at the parent `x`: both children `x²`, `x²·g`. -/
def CapLoopBody (rd : Reader) (flags cap x : E) : Prop :=
  CapSideSem rd flags cap x (x * x) ∧ CapSideSem rd flags cap x (x * x * gen)

/-- The honest valuation of one iteration. -/
def capLoopSig (rd : Reader) (x N flags cap : E) : Val :=
  setl (setl (setl (setl (setl (Val.ofArgs [x, N, flags, cap]) 4 [x * x]) 5
    (capSideVals rd flags cap x (x * x))) 27 [x * x, gen, x * x * gen]) 30
    (capSideVals rd flags cap x (x * x * gen))) 52 [gen, x * gen, x * gen + N, gen, x * gen]

theorem capLoop_step {loop : String} {fn : Fn} (hfind : coreProgram.find? loop = some fn)
    (hp : fn.params = [.n 0, .n 1, .n 2, .n 3]) (hb : fn.body = capLoopBody loop)
    (rd : Reader) (N flags cap : E) (d : ℕ) (x : E) :
    coreProgram.relN rd (d + 1) loop (x :: [N, flags, cap]) [] ↔
      CapLoopBody rd flags cap x ∧ IsInK (x * gen + N) ∧
        (x * gen + N ≠ 0 → coreProgram.relN rd d loop (x * gen :: [N, flags, cap]) []) := by
  rw [relN_succ_iff hfind, hp, hb, capLoopBody]
  simp only [holdsList_append, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons,
    List.map_nil, and_true, word_gen]
  constructor
  · rintro ⟨σ, hp, h4, hs⟩
    rw [holds_capSideT] at hs
    obtain ⟨hs0, h27, h28, h29, hs⟩ := hs
    rw [holds_capSideT] at hs
    obtain ⟨hs1, h52, h53, h54, h55, h56, hK, hcall⟩ := hs
    simp only [List.cons.injEq] at hp
    obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hp
    have s0 := capSideT_sound hs0
    have s1 := capSideT_sound hs1
    rw [h4] at s0
    rw [h29, h28, h27] at s1
    refine ⟨⟨s0, s1⟩, by rwa [h54, h53, h52] at hK, fun hne => ?_⟩
    have := hcall (by rwa [h54, h53, h52])
    rwa [h56, h55] at this
  · rintro ⟨⟨s0, s1⟩, hK, hcall⟩
    set τ := capLoopSig rd x N flags cap
    have hv0 : ∀ k < 22, τ (.n (5 + k)) = (capSideVals rd flags cap x (x * x)).getD k 0 :=
      fun k hk => by
        simp only [τ, capLoopSig, setl, length_capSideVals]
        rw [set_n_lt (by omega), set_n_lt (by omega), set_n_lt (by omega),
          set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
    have hv1 : ∀ k < 22, τ (.n (30 + k)) = (capSideVals rd flags cap x (x * x * gen)).getD k 0 :=
      fun k hk => by
        simp only [τ, capLoopSig, setl, length_capSideVals]
        rw [set_n_lt (by omega), set_n_in (by omega) (by omega), Nat.add_sub_cancel_left]
    have a0 : τ (.n 0) = x := by simp only [τ, capLoopSig]; b1_look
    have a1 : τ (.n 1) = N := by simp only [τ, capLoopSig]; b1_look
    have a2 : τ (.n 2) = flags := by simp only [τ, capLoopSig]; b1_look
    have a3 : τ (.n 3) = cap := by simp only [τ, capLoopSig]; b1_look
    have a4 : τ (.n 4) = x * x := by simp only [τ, capLoopSig]; b1_look
    have a27 : τ (.n 27) = x * x := by simp only [τ, capLoopSig]; b1_look
    have a28 : τ (.n 28) = gen := by simp only [τ, capLoopSig]; b1_look
    have a29 : τ (.n 29) = x * x * gen := by simp only [τ, capLoopSig]; b1_look
    have a52 : τ (.n 52) = gen := by simp only [τ, capLoopSig]; b1_look
    have a53 : τ (.n 53) = x * gen := by simp only [τ, capLoopSig]; b1_look
    have a54 : τ (.n 54) = x * gen + N := by simp only [τ, capLoopSig]; b1_look
    have a55 : τ (.n 55) = gen := by simp only [τ, capLoopSig]; b1_look
    have a56 : τ (.n 56) = x * gen := by simp only [τ, capLoopSig]; b1_look
    refine ⟨τ, by rw [a0, a1, a2, a3], by rw [a4, a0], (holds_capSideT _ _ _ _ _ _ _).mpr
      ⟨capSideT_complete ?_ ?_, by rw [a27, a0], by rw [a28], by rw [a29, a27, a28],
        (holds_capSideT _ _ _ _ _ _ _).mpr ⟨capSideT_complete ?_ ?_, by rw [a52], by rw [a53, a0, a52],
          by rw [a54, a53, a1], by rw [a55], by rw [a56, a0, a55], by rw [a54]; exact hK,
          by rw [a54, a56, a1, a2, a3]; exact hcall⟩⟩⟩
    · intro k hk; rw [hv0 k hk, a2, a3, a0, a4]
    · rw [a2, a3, a0, a4]; exact s0
    · intro k hk; rw [hv1 k hk, a2, a3, a0, a29]
    · rw [a2, a3, a0, a29]; exact s1

/-! ## `verify_merkle_cap` -/

/-- The expansion of `verify_merkle_cap(cap, flags, D)` (G:929-940), the loop's end
`W = g^(2^(D-1))` folded: hash the root, set `flags[1]`, run the loop from `g`, return the root's
cells. -/
def vmcBody (W : E) (loop : String) : List Stmt :=
  [.atom (.const (.n 2) (word 16 0 0)), .atom (.mul (.n 3) (.n 0) (.n 2)),
    .atom (.load (.n 4) (.n 3) 0), .atom (.load (.n 5) (.n 3) 1), .atom (.load (.n 6) (.n 3) 2),
    .atom (.load (.n 7) (.n 3) 3),
    .atom (.const (.n 8) (word 13503953895743350343 11912009169889063794 0)),
    .atom (.const (.n 9) (word 11170449402626986623 6620516960021240235 0)),
    .atom (.const (.n 10) (word 64 4294967295 0)),
    .atom (.blake2s (.n 4) (.n 5) (.n 6) (.n 7) (.n 8) (.n 9) (.n 11) (.n 12) (.n 10)),
    .atom (.load (.n 11) (.n 0) 2), .atom (.load (.n 12) (.n 0) 3),
    .atom (.const (.n 13) (word 1 0 0)), .atom (.load (.n 13) (.n 1) 1),
    .atom (.const (.n 14) (word 2 0 0)), .atom (.const (.n 15) W), .atom (.add (.n 16) (.n 14) (.n 15)),
    .atom (.const (.n 17) (word 2 0 0)), .atom (.const (.n 18) W),
    .callIf (.n 16) loop [.n 17, .n 18, .n 1, .n 0],
    .atom (.load (.n 19) (.n 0) 2), .atom (.load (.n 20) (.n 0) 3), .ret [.n 19, .n 20]]

/-- Node `c` of the cap's interior: its flag is in `K`, and if nonzero its parent's flag is `1`
and it is hashed. -/
def CapFlagged (rd : Reader) (flags cap : E) (c : ℕ) : Prop :=
  ∃ f, LoadHolds rd flags c f ∧ IsInK f ∧ (f ≠ 0 → LoadHolds rd flags (c / 2) 1 ∧ CapHashed rd cap c)

/-- **`verify_merkle_cap(cap, flags, D)`** (G:929-940; TRIAGE #30): the root is hashed and
flagged, every interior node `c ∈ [2, 2^D)` is `CapFlagged`, and the function returns the root's
cells. -/
def MeaningVerifyMerkleCap (D : ℕ) (rd : Reader) : List E → List E → Prop
  | [cap, flags], rets =>
      LoadHolds rd flags 1 1 ∧ CapHashed rd cap 1 ∧
        (∀ c, 2 ≤ c → c < 2 ^ D → CapFlagged rd flags cap c) ∧
        ∃ r, CapCell rd cap 1 r ∧ rets = [(digestScalars r).1, (digestScalars r).2]
  | _, _ => False

/-- One side at the parent `g^p`: the child `2p + s`. -/
theorem capSideSem_gen_pow (rd : Reader) (flags cap : E) (p s : ℕ) (hs : s < 2) :
    CapSideSem rd flags cap (gen ^ p) (gen ^ (2 * p + s)) ↔ CapFlagged rd flags cap (2 * p + s) := by
  have hdiv : (2 * p + s) / 2 = p := by omega
  simp only [CapSideSem, CapFlagged, loadHolds_gen_pow, hashCapSem_gen_pow, hdiv]

theorem capLoopBody_gen_pow (rd : Reader) (flags cap : E) (p : ℕ) :
    CapLoopBody rd flags cap (gen ^ p) ↔
      CapFlagged rd flags cap (2 * p) ∧ CapFlagged rd flags cap (2 * p + 1) := by
  have e0 : gen ^ p * gen ^ p = gen ^ (2 * p + 0) := by rw [gen_pow_mul_gen_pow]; congr 1; ring
  have e1 : gen ^ p * gen ^ p * gen = gen ^ (2 * p + 1) := by
    rw [gen_pow_mul_gen_pow, ← pow_succ]; congr 1; ring
  rw [CapLoopBody, e1, e0, capSideSem_gen_pow rd flags cap p 0 (by omega),
    capSideSem_gen_pow rd flags cap p 1 (by omega), Nat.add_zero]

theorem interior_iff (P : ℕ → Prop) (D : ℕ) (hD : 1 ≤ D) :
    (∀ j, 1 ≤ j → j < 2 ^ (D - 1) → P (2 * j) ∧ P (2 * j + 1)) ↔ ∀ c, 2 ≤ c → c < 2 ^ D → P c := by
  have h2 : 2 ^ D = 2 * 2 ^ (D - 1) := by
    rw [← pow_succ']; congr 1; omega
  constructor
  · intro h c h1 h2'
    rcases Nat.even_or_odd c with ⟨j, hj⟩ | ⟨j, hj⟩
    · have := (h j (by omega) (by omega)).1
      rwa [show 2 * j = c by omega] at this
    · have := (h j (by omega) (by omega)).2
      rwa [show 2 * j + 1 = c by omega] at this
  · intro h j h1 h2'
    exact ⟨h _ (by omega) (by omega), h _ (by omega) (by omega)⟩

theorem word_gSquares {j : ℕ} (hj : j < sizeBits) : word (gSquaresBits.getD j 0) 0 0 = gen ^ 2 ^ j := by
  rw [word_eOfNat, eOfNat_gSquaresBits j hj]

/-- **`verify_merkle_cap` at a depth `2 ≤ D ≤ 8`**, for a compiled function whose body is
`vmcBody` with its loop helper's body `capLoopBody`. -/
theorem verify_merkle_cap_iff {name loop : String} {f lf : Fn} (D : ℕ) (hD : 2 ≤ D) (hD8 : D ≤ 8)
    (hfind : coreProgram.find? name = some f) (hp : f.params = [.n 0, .n 1])
    (hb : f.body = vmcBody (word (gSquaresBits.getD (D - 1) 0) 0 0) loop)
    (hlf : coreProgram.find? loop = some lf) (hlp : lf.params = [.n 0, .n 1, .n 2, .n 3])
    (hlb : lf.body = capLoopBody loop) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd name args rets ↔ MeaningVerifyMerkleCap D rd args rets := by
  have hW : word (gSquaresBits.getD (D - 1) 0) 0 0 = gen ^ 2 ^ (D - 1) :=
    word_gSquares (by simp only [sizeBits]; omega)
  have hm1 : 1 < 2 ^ (D - 1) := Nat.one_lt_two_pow (by omega)
  have hmo : 2 ^ (D - 1) < ordG := by
    have : 2 ^ (D - 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    simp only [ordG]; omega
  have hall : ∀ flags cap, coreProgram.Rel rd loop [gen, gen ^ 2 ^ (D - 1), flags, cap] [] ↔
      ∀ c, 2 ≤ c → c < 2 ^ D → CapFlagged rd flags cap c := by
    intro flags cap
    have hl := loop_iff (P := coreProgram) (rd := rd) (f := loop)
      (ps := [gen ^ 2 ^ (D - 1), flags, cap]) (N := gen ^ 2 ^ (D - 1))
      (B := fun x => CapLoopBody rd flags cap x) (capLoop_step hlf hlp hlb rd _ flags cap) 1
    rw [pow_one] at hl
    rw [hl, ← interior_iff _ D (by omega)]
    constructor
    · rintro ⟨m, hm, hN, hfirst, hB⟩ j h1 h2
      have hm' : m = 2 ^ (D - 1) := by
        rcases Nat.lt_trichotomy m (2 ^ (D - 1)) with h | h | h
        · have := gen_pow_inj (a := 2 ^ (D - 1)) (b := m) (by simp only [ordG] at hmo; omega)
            (by simp only [ordG] at hmo; omega) hN
          omega
        · exact h
        · exact absurd rfl (hfirst (2 ^ (D - 1)) hm1 h)
      subst hm'
      exact (capLoopBody_gen_pow rd flags cap j).mp (hB j h1 h2)
    · intro h
      exact ⟨2 ^ (D - 1), hm1, rfl, first_hit_of_lt hmo rfl, fun j h1 h2 =>
        (capLoopBody_gen_pow rd flags cap j).mpr (h j h1 h2)⟩
  have hroot_iff : ∀ cap : E, HashCapSem rd cap gen ↔ CapHashed rd cap 1 := fun cap => by
    rw [← hashCapSem_gen_pow, pow_one]
  have e4 : ∀ cap : E, cap * (gen * gen * (gen * gen)) = cap * gen ^ 4 := fun cap => by ring
  have e2 : ∀ cap : E, cap * (gen * gen) = cap * gen ^ 2 := fun cap => by ring
  have e3 : ∀ cap : E, cap * (gen * gen * gen) = cap * gen ^ 3 := fun cap => by ring
  rw [rel_iff_sem hfind, hb, hp, vmcBody]
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil, word_iv0, word_iv1,
    word_md64, word_one, word_gen, word_sixteen, hW]
  constructor
  · rintro ⟨σ, hp, h2, h3, l4, l5, l6, l7, h8, h9, h10, hc, l11, l12, h13, l13, h14, h15, h16, h17, h18,
      hK, hcall, l19, l20, hret⟩
    subst hp hret
    simp only [MeaningVerifyMerkleCap]
    rw [h3, h2] at l4 l5 l6 l7
    rw [h8, h9, h10] at hc
    rw [h13] at l13
    have hroot : CapHashed rd (σ (.n 0)) 1 := by
      rw [← hroot_iff]
      refine ⟨_, _, _, _, _, _, ?_, ?_, ?_, ?_, hc, ?_, ?_⟩
      · rw [e4]; exact l4
      · rw [e4]; exact l5
      · rw [e4]; exact l6
      · rw [e4]; exact l7
      · rw [e2, loadHolds_gen_pow]; exact l11
      · rw [e3, loadHolds_gen_pow]; exact l12
    have hne : σ (.n 16) ≠ 0 := by
      rw [h16, h14, h15]
      intro h0
      have := gen_pow_inj (a := 1) (b := 2 ^ (D - 1)) (by decide)
        (by simp only [ordG] at hmo; omega) (by rw [pow_one]; exact e_add_eq_zero_iff.mp h0)
      omega
    have hl := hcall hne
    rw [h17, h18] at hl
    obtain ⟨l, r, hl2, hr3, hlr⟩ := hroot
    refine ⟨l13, ⟨l, r, hl2, hr3, hlr⟩, (hall _ _).mp hl, hashPair l r, hlr, ?_⟩
    rw [Option.some.inj (l19.2.symm.trans hlr.1.2), Option.some.inj (l20.2.symm.trans hlr.2.2)]
  · intro hm
    obtain ⟨cap, flags, rfl⟩ : ∃ cap flags, args = [cap, flags] := by
      match args, hm with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    obtain ⟨l13, ⟨l, r, ⟨a0, a1⟩, ⟨b0, b1⟩, ⟨o0, o1⟩⟩, hint, rt, hrt, hret⟩ := hm
    have hrt' := hrt.unique ⟨o0, o1⟩
    subst hrt' hret
    refine ⟨setl (Val.ofArgs [cap, flags]) 2 [gen ^ 4, cap * gen ^ 4, (digestScalars l).1,
      (digestScalars l).2, (digestScalars r).1, (digestScalars r).2, Value.ivCells.1,
      Value.ivCells.2, metadataCell 64 true, (digestScalars (hashPair l r)).1,
      (digestScalars (hashPair l r)).2, 1, gen, gen ^ 2 ^ (D - 1), gen + gen ^ 2 ^ (D - 1), gen,
      gen ^ 2 ^ (D - 1), (digestScalars (hashPair l r)).1, (digestScalars (hashPair l r)).2],
      by b1_look, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    all_goals b1_look
    · simpa [loadHolds_mul_gen_pow] using a0
    · simpa [loadHolds_mul_gen_pow] using a1
    · simpa [loadHolds_mul_gen_pow] using b0
    · simpa [loadHolds_mul_gen_pow] using b1
    · exact compress_of_hashPair l r
    · simpa using o0
    · simpa using o1
    · exact l13
    · have h1 := isInK_add (gen_pow_isInK 1) (gen_pow_isInK (2 ^ (D - 1)))
      rwa [pow_one] at h1
    · intro _; exact (hall flags cap).mpr hint
    · simpa using o0
    · simpa using o1

/-! ## The root at the end of a flagged path -/

/-- The digest at cap node `i`, when its cells are one. -/
noncomputable def capNode (rd : Reader) (cap : E) (i : ℕ) : Digest :=
  Classical.epsilon fun d => CapCell rd cap i d

theorem capNode_eq {cap : E} {i : ℕ} {d : Digest} (h : CapCell rd cap i d) : capNode rd cap i = d :=
  (Classical.epsilon_spec (p := fun d => CapCell rd cap i d) ⟨d, h⟩).unique h

/-- The other child of node `c`'s parent. -/
def capSib (c : ℕ) : ℕ := if c % 2 = 0 then c + 1 else c - 1

/-- The siblings of node `c` up `h` levels of the cap: the other child at each level. -/
noncomputable def capSibs (rd : Reader) (cap : E) : ℕ → ℕ → List Digest
  | 0, _ => []
  | h + 1, c => capNode rd cap (capSib c) :: capSibs rd cap h (c / 2)

theorem length_capSibs (rd : Reader) (cap : E) (h c : ℕ) : (capSibs rd cap h c).length = h := by
  induction h generalizing c with
  | zero => rfl
  | succ h ih => simp [capSibs, ih]

/-- `climb` (V:526) over the deployed hash, one level. -/
theorem climb_cons (node s : Digest) (q : ℕ) (ss : List Digest) :
    climb (m := Id) blake2sBytes node q (s :: ss) =
      climb (m := Id) blake2sBytes (if q % 2 = 0 then hashPair node s else hashPair s node) (q / 2) ss := by
  simp only [climb]
  split <;> rfl

/-- A hashed node, from either child: the parent is the hash of the child and its sibling in
order. -/
theorem capHashed_climb {cap : E} {c : ℕ} (hh : CapHashed rd cap (c / 2)) :
    (if c % 2 = 0 then hashPair (capNode rd cap c) (capNode rd cap (capSib c))
      else hashPair (capNode rd cap (capSib c)) (capNode rd cap c)) = capNode rd cap (c / 2) := by
  obtain ⟨l, r, hl, hr, hp⟩ := hh
  rw [capNode_eq hp]
  by_cases he : c % 2 = 0
  · simp only [he, ↓reduceIte, capSib]
    rw [capNode_eq (show CapCell rd cap c l by rw [show c = 2 * (c / 2) by omega]; exact hl),
      capNode_eq (show CapCell rd cap (c + 1) r by rw [show c + 1 = 2 * (c / 2) + 1 by omega]; exact hr)]
  · simp only [he, ↓reduceIte, capSib]
    rw [capNode_eq (show CapCell rd cap (c - 1) l by rw [show c - 1 = 2 * (c / 2) by omega]; exact hl),
      capNode_eq (show CapCell rd cap c r by rw [show c = 2 * (c / 2) + 1 by omega]; exact hr)]

/-- **The refutation argument**: in a cap of depth `D` whose interior nodes are `CapFlagged`
and whose root is hashed, from a node `c` of level `h ≤ D` whose parent's flag is `1`, `climb`
(V:526) over the cap's siblings ends at the root. -/
theorem cap_climb {flags cap : E} {D : ℕ} (hroot : CapHashed rd cap 1)
    (hint : ∀ c, 2 ≤ c → c < 2 ^ D → CapFlagged rd flags cap c) :
    ∀ h c, 1 ≤ h → h ≤ D → 2 ^ h ≤ c → c < 2 ^ (h + 1) → LoadHolds rd flags (c / 2) 1 →
      climb (m := Id) blake2sBytes (capNode rd cap c) (c - 2 ^ h) (capSibs rd cap h c) =
        capNode rd cap 1 := by
  intro h
  induction h with
  | zero => intro c h1; omega
  | succ h ih =>
    intro c _ hD hlo hhi hf
    have hp1 : 2 ^ (h + 1) = 2 * 2 ^ h := by ring
    have hp2 : 2 ^ (h + 1 + 1) = 2 * 2 ^ (h + 1) := by ring
    have hpar : CapHashed rd cap (c / 2) ∧ (1 ≤ h → LoadHolds rd flags (c / 2 / 2) 1) := by
      rcases Nat.eq_zero_or_pos h with h0 | hpos
      · subst h0
        rw [show c / 2 = 1 by simp at hlo hhi; omega]
        exact ⟨hroot, fun h => absurd h (by omega)⟩
      · have hpos' : 1 ≤ 2 ^ h := Nat.one_le_two_pow
        have hle : 2 ^ (h + 1) ≤ 2 ^ D := Nat.pow_le_pow_right (by decide) hD
        have hh2 : 2 ≤ 2 ^ h := by
          have := Nat.pow_le_pow_right (show 0 < 2 by decide) hpos; simpa using this
        obtain ⟨fv, lf, -, hnz⟩ := hint (c / 2) (by omega) (by omega)
        have : fv = 1 := Option.some.inj (lf.2.symm.trans hf.2)
        obtain ⟨hf', hh⟩ := hnz (by rw [this]; exact one_ne_zero)
        exact ⟨hh, fun _ => hf'⟩
    have hq : (c - 2 ^ (h + 1)) % 2 = c % 2 := by omega
    have hq2 : (c - 2 ^ (h + 1)) / 2 = c / 2 - 2 ^ h := by omega
    rw [capSibs, climb_cons, hq, hq2, capHashed_climb hpar.1]
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · subst h0
      rw [show c / 2 = 1 by simp at hlo hhi; omega]
      rfl
    · exact ih (c / 2) hpos (by omega) (by omega) (by omega) (hpar.2 hpos)

/-! ## The specializations -/

set_option maxRecDepth 100000 in
theorem verify_merkle_cap_L4_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "verify_merkle_cap__L4" args rets ↔ MeaningVerifyMerkleCap 4 rd args rets :=
  verify_merkle_cap_iff (loop := "__loop454") 4 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 674) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1006) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem verify_merkle_cap_L5_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "verify_merkle_cap__L5" args rets ↔ MeaningVerifyMerkleCap 5 rd args rets :=
  verify_merkle_cap_iff (loop := "__loop433") 5 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 586) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 978) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem verify_merkle_cap_L6_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "verify_merkle_cap__L6" args rets ↔ MeaningVerifyMerkleCap 6 rd args rets :=
  verify_merkle_cap_iff (loop := "__loop431") 6 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 583) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 975) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem verify_merkle_cap_L7_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "verify_merkle_cap__L7" args rets ↔ MeaningVerifyMerkleCap 7 rd args rets :=
  verify_merkle_cap_iff (loop := "__loop456") 7 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 683) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1008) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

set_option maxRecDepth 100000 in
theorem verify_merkle_cap_L8_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "verify_merkle_cap__L8" args rets ↔ MeaningVerifyMerkleCap 8 rd args rets :=
  verify_merkle_cap_iff (loop := "__loop429") 8 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 579) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 972) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets

end
end LeanVM.Guest.B1
