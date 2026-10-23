/-
  LeanVM.Guest.B1.Sig.HashValues

  `hash_values` (G:2345-2360): `Th(P, A, values)` over `n` cells as a chain of compressions, four
  cells a block, sound and complete for BLAKE2s of the cells' bytes.
-/

module

public import LeanVM.Guest.B1.Sig.Group

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## Blocks in a sequence over a range -/

theorem holdsList_flatMap_range (f : Nat → List Stmt) (hf : ∀ j, Stmt.noRetList (f j) = true) (q : Nat)
    (next : Prop) (kret : List E → Prop) (σ : Val) :
    Stmt.HoldsList C rd σ ((List.range q).flatMap f) next kret ↔
      (∀ j < q, Stmt.HoldsList C rd σ (f j) True kret) ∧ next := by
  rw [List.flatMap_def, holdsList_flatten _ (by simp [hf])]
  simp

theorem Completes.flatMap_range {f : Nat → List Stmt} {base : Nat → Nat} {Inv : Nat → Val → Prop}
    (hbase : ∀ j, base j ≤ base (j + 1)) :
    ∀ (q : Nat), (∀ j < q, NumBelow (base (j + 1)) (Stmt.valsList (f j))) →
      (∀ j < q, ∀ σ, Inv j σ → Completes C rd (base j) (base (j + 1)) (f j) σ (Inv (j + 1))) →
      ∀ σ, Inv 0 σ → Completes C rd (base 0) (base q) ((List.range q).flatMap f) σ (Inv q)
  | 0, _, _, σ, h0 => ⟨σ, Ext.refl _ _ _, h0, fun _ _ hn => hn⟩
  | q + 1, hbelow, h, σ, h0 => by
      have hmono : ∀ j k, j ≤ k → base j ≤ base k := fun j k hjk => by
        induction hjk with
        | refl => exact le_rfl
        | step _ ih => exact le_trans ih (hbase _)
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      refine Completes.append (m := base q) (hmono 0 q (by omega)) (hbase q) ?_
        (Completes.flatMap_range hbase q (fun j hj => hbelow j (by omega)) (fun j hj => h j (by omega)) σ h0)
        fun σ' _ hp => h q (by omega) σ' hp
      exact numBelow_valsList_flatMap _ _ fun j hj =>
        (hbelow j (by simp at hj; omega)).mono (hmono _ _ (by simp at hj; omega))

/-! ## The blocks of `hash_values` -/

/-- Block `j` of `hash_values` over `P`, `A` and the values `vs`. -/
def hvBlock (pp a : E) (vs : Nat → E) (j : Nat) : Fin 4 → E :=
  if j = 0 then ![pp, a, vs 0, vs 1] else ![vs (4 * j - 2), vs (4 * j - 1), vs (4 * j), vs (4 * j + 1)]

theorem hvBlock_bytes_succ (pp a : E) (vs : Nat → E) (j : Nat) :
    blockBytes (hvBlock pp a vs (j + 1)) = [vs (4 * j + 2), vs (4 * j + 3), vs (4 * j + 4), vs (4 * j + 5)].flatMap cellBytes := by
  simp only [hvBlock, Nat.add_one_ne_zero, ↓reduceIte, blockBytes]
  rw [show 4 * (j + 1) - 2 = 4 * j + 2 by omega, show 4 * (j + 1) - 1 = 4 * j + 3 by omega,
    show 4 * (j + 1) = 4 * j + 4 by ring]
  simp

theorem hvBlocks_bytes (pp a : E) (vs : Nat → E) :
    ∀ q, (List.range (q + 1)).flatMap (fun j => blockBytes (hvBlock pp a vs j)) =
      (pp :: a :: (List.range (4 * q + 2)).map vs).flatMap cellBytes
  | 0 => by simp [hvBlock, blockBytes, List.range_succ]
  | q + 1 => by
      have hY : (List.range (4 * (q + 1) + 2)).map vs = (List.range (4 * q + 2)).map vs ++
          [vs (4 * q + 2), vs (4 * q + 3), vs (4 * q + 4), vs (4 * q + 5)] := by
        rw [show 4 * (q + 1) + 2 = (4 * q + 2) + 4 by ring, List.range_add, List.map_append]
        simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
          List.map_append, List.cons_append]
      rw [List.range_succ, List.flatMap_append, hvBlocks_bytes pp a vs q, List.flatMap_singleton,
        hvBlock_bytes_succ, hY]
      simp

/-! ## Soundness -/

/-- The middle block `j` of `hash_values` from base `b`. -/
def hvMid (val : Nat → V) (b j : Nat) : List Stmt :=
  let c := b + 5 + 3 * j
  [cst c (mdw (64 * (j + 2)) false),
    b2s (val (4 * j + 2)) (val (4 * j + 3)) (val (4 * j + 4)) (val (4 * j + 5)) (.n (c - 2)) (.n (c - 1))
      (.n (c + 1)) (.n (c + 2)) (.n c)]

theorem hashValues_eq (pp a : V) (val : Nat → V) (n b : Nat) :
    hashValues pp a val n b =
      let q := (n + 1) / 4 - 1
      let c := b + 5 + 3 * q
      let first := ivs b ++ [cst (b + 2) (mdw 64 false),
        b2s pp a (val 0) (val 1) (.n b) (.n (b + 1)) (.n (b + 3)) (.n (b + 4)) (.n (b + 2))]
      if n % 4 = 0 then
        (first ++ (List.range q).flatMap (hvMid val b) ++ [cst c (word 0 0 0), cst (c + 1) (word 0 0 0),
          cst (c + 2) (mdw (16 * (n + 2)) true),
          b2s (val (n - 2)) (val (n - 1)) (.n c) (.n (c + 1)) (.n (c - 2)) (.n (c - 1)) (.n (c + 3))
            (.n (c + 4)) (.n (c + 2))], .n (c + 3))
      else
        (first ++ (List.range q).flatMap (hvMid val b) ++ [cst c (mdw (16 * (n + 2)) true),
          b2s (val (n - 4)) (val (n - 3)) (val (n - 2)) (val (n - 1)) (.n (c - 2)) (.n (c - 1))
            (.n (c + 1)) (.n (c + 2)) (.n c)], .n (c + 1)) := rfl

theorem hvMid_noRet (val : Nat → V) (b j : Nat) : Stmt.noRetList (hvMid val b j) = true := rfl

/-- The chaining value after the first `j` blocks, and the metadata of block `j`, as `hash_values`
from base `b` holds them. -/
def hvSt (σ : Val) (b j : Nat) : E × E :=
  if j = 0 then digestScalars paramIv else (σ (.n (b + 3 * j)), σ (.n (b + 3 * j + 1)))

theorem hashValues_prefix {σ : Val} {pp a : V} {val : Nat → V} {b q : Nat} {X : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ ((ivs b ++ [cst (b + 2) (mdw 64 false),
        b2s pp a (val 0) (val 1) (.n b) (.n (b + 1)) (.n (b + 3)) (.n (b + 4)) (.n (b + 2))]) ++
        (List.range q).flatMap (hvMid val b)) X kret) :
    hvSt σ b (q + 1) = digestScalars (absorbBlocks paramIv 0 ((List.range (q + 1)).map fun j =>
      blockBytes (hvBlock (σ pp) (σ a) (fun i => σ (val i)) j))) ∧ X := by
  rw [holdsList_append, holdsList_flatMap_range _ (hvMid_noRet val b)] at h
  simp only [ivs, cst, b2s, List.cons_append, List.nil_append, holdsList_cons_atom, holdsList_nil,
    Atom.Holds] at h
  obtain ⟨h0, h1, h2, h3, hmid, hX⟩ := h
  refine ⟨chain_nonfinal (n := q + 1) (h := paramIv) (t := 0) (st := hvSt σ b)
    (md := fun j => σ (.n (b + 3 * j + 2))) (blocks := hvBlock (σ pp) (σ a) (fun i => σ (val i)))
    (by simp [hvSt]) (fun j hj => ?_) (fun j hj => ?_), hX⟩
  · rcases j with _ | j
    · simp [h2, mdw_eq]
    · have := (hmid j (by omega)).1
      rw [show b + 3 * (j + 1) + 2 = b + 5 + 3 * j by ring, this, mdw_eq]
      congr 1; ring
  · rcases j with _ | j
    · have hiv := ivCells_eq_iv
      simp only [Value.ivCells] at hiv
      simp only [hvSt, hvBlock, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
      rw [hiv, ← h0, ← h1]
      exact h3
    · have := (hmid j (by omega)).2.1
      rw [show b + 5 + 3 * j - 2 = b + 3 * (j + 1) by omega, show b + 5 + 3 * j - 1 = b + 3 * (j + 1) + 1 by omega,
        show b + 5 + 3 * j + 1 = b + 3 * (j + 1 + 1) by ring, show b + 5 + 3 * j + 2 = b + 3 * (j + 1 + 1) + 1 by ring,
        show b + 5 + 3 * j = b + 3 * (j + 1) + 2 by ring] at this
      simp only [hvSt, hvBlock, Nat.add_one_ne_zero, ↓reduceIte]
      rw [show 4 * (j + 1) - 2 = 4 * j + 2 by omega, show 4 * (j + 1) - 1 = 4 * j + 3 by omega,
        show 4 * (j + 1) + 1 = 4 * j + 5 by ring, show 4 * (j + 1) = 4 * j + 4 by ring]
      exact this

/-- The bytes `hash_values` hashes: its first `4q + 2` values in whole blocks, then the rest. -/
theorem hv_bytes_split (pp a : E) (vs : Nat → E) (q k : Nat) :
    (pp :: a :: (List.range (4 * q + 2 + k)).map vs).flatMap cellBytes =
      ((List.range (q + 1)).map fun j => blockBytes (hvBlock pp a vs j)).flatten ++
        ((List.range k).map fun i => vs (4 * q + 2 + i)).flatMap cellBytes := by
  rw [← List.flatMap_def, hvBlocks_bytes, List.range_add, List.map_append, List.map_map]
  simp [Function.comp_def]

theorem hv_final {pp a : E} {vs : Nat → E} {q k : Nat} {m : Fin 4 → E} {cv0 cv1 o0 o1 md : E}
    (hk : 1 ≤ k) (hk4 : k ≤ 4)
    (hm : blockBytes m = ((List.range k).map fun i => vs (4 * q + 2 + i)).flatMap cellBytes ++
      List.replicate (64 - 16 * k) 0)
    (hcv : (cv0, cv1) = digestScalars (absorbBlocks paramIv 0 ((List.range (q + 1)).map fun j =>
      blockBytes (hvBlock pp a vs j))))
    (hmd : md = metadataCell (64 * (q + 1) + 16 * k) true) (hc : CompressCells m cv0 cv1 o0 o1 md) :
    (o0, o1) = hcell (pp :: a :: (List.range (4 * q + 2 + k)).map vs) := by
  set h := absorbBlocks paramIv 0 ((List.range (q + 1)).map fun j => blockBytes (hvBlock pp a vs j))
  have e0 : cv0 = (digestScalars h).1 := congrArg Prod.fst hcv
  have e1 : cv1 = (digestScalars h).2 := congrArg Prod.snd hcv
  rw [e0, e1] at hc
  have hlen : (((List.range k).map fun i => vs (4 * q + 2 + i)).flatMap cellBytes).length = 16 * k := by
    rw [length_flatMap_cellBytes]; simp
  have := chain_final (h := h) (t := 64 * (q + 1)) (r := ((List.range k).map fun i => vs (4 * q + 2 + i)).flatMap cellBytes)
    (by rw [hm, hlen]) (by rw [hmd, hlen]) hc
  rw [this, hcell, hb, hv_bytes_split]
  have hbs : ∀ x ∈ ((List.range (q + 1)).map fun j => blockBytes (hvBlock pp a vs j)), x.length = 64 := by
    intro x hx; obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx; exact length_blockBytes _
  have hfl := length_flatten_of_64 _ hbs
  simp only [List.length_map, List.length_range] at hfl
  rw [blake2sBytes, List.length_append, hfl, hlen,
    show (64 * (q + 1) + 16 * k - 1) / 64 = ((List.range (q + 1)).map fun j => blockBytes (hvBlock pp a vs j)).length + 0
      by simp; omega, absorb_split paramIv 0 _ hbs]
  simp only [List.length_map, List.length_range, Nat.zero_add]
  rfl

/-- **`hash_values` is sound**: its output is the first cell of BLAKE2s of `P`, `A` and the `n`
values, for `n` a multiple of two above 2. -/
theorem hashValues_sound {σ : Val} {pp a : V} {val : Nat → V} {n b : Nat}
    (hn : n % 4 = 0 ∨ n % 4 = 2) (hn4 : 4 ≤ n) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (hashValues pp a val n b).1 next kret) :
    σ (hashValues pp a val n b).2 = (hcell (σ pp :: σ a :: (List.range n).map fun i => σ (val i))).1 ∧ next := by
  rw [hashValues_eq] at h ⊢
  dsimp only at h ⊢
  set q := (n + 1) / 4 - 1 with hq
  split_ifs at h ⊢ with h4
  · have hnq : n = 4 * q + 2 + 2 := by omega
    rw [holdsList_append] at h
    obtain ⟨hst, h⟩ := hashValues_prefix h
    simp only [cst, b2s, holdsList_cons_atom, holdsList_nil, Atom.Holds] at h
    obtain ⟨h0, h1, h2, h3, hn'⟩ := h
    refine ⟨?_, hn'⟩
    have hcv : (σ (.n (b + 5 + 3 * q - 2)), σ (.n (b + 5 + 3 * q - 1))) = hvSt σ b (q + 1) := by
      simp only [hvSt, Nat.add_one_ne_zero, ↓reduceIte, Prod.mk.injEq]
      constructor <;> congr 2 <;> omega
    rw [h0, h1, word_zero, h2, mdw_eq] at h3
    have := hv_final (k := 2) (vs := fun i => σ (val i)) (by norm_num) (by norm_num) ?_ (hcv.trans hst) ?_ h3
    · rw [hnq]; exact congrArg Prod.fst this
    · rw [blockBytes_two, show n - 2 = 4 * q + 2 + 0 by omega, show n - 1 = 4 * q + 2 + 1 by omega]
      simp [List.range_succ]
    · rw [hnq]; congr 1; ring
  · have hnq : n = 4 * q + 2 + 4 := by omega
    rw [holdsList_append] at h
    obtain ⟨hst, h⟩ := hashValues_prefix h
    simp only [cst, b2s, holdsList_cons_atom, holdsList_nil, Atom.Holds] at h
    obtain ⟨h2, h3, hn'⟩ := h
    refine ⟨?_, hn'⟩
    have hcv : (σ (.n (b + 5 + 3 * q - 2)), σ (.n (b + 5 + 3 * q - 1))) = hvSt σ b (q + 1) := by
      simp only [hvSt, Nat.add_one_ne_zero, ↓reduceIte, Prod.mk.injEq]
      constructor <;> congr 2 <;> omega
    rw [h2, mdw_eq] at h3
    have := hv_final (k := 4) (vs := fun i => σ (val i)) (by norm_num) (by norm_num) ?_ (hcv.trans hst) ?_ h3
    · rw [hnq]; exact congrArg Prod.fst this
    · simp only [blockBytes, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
      rw [show n - 4 = 4 * q + 2 + 0 by omega, show n - 3 = 4 * q + 2 + 1 by omega,
        show n - 2 = 4 * q + 2 + 2 by omega, show n - 1 = 4 * q + 2 + 3 by omega]
      simp [List.range_succ]
    · rw [hnq]; congr 1; ring

/-! ## Completeness -/

/-- The chaining value after `j` blocks over canonical cells. -/
def hvState (pp a : E) (vs : Nat → E) (j : Nat) : Digest :=
  absorbBlocks paramIv 0 ((List.range j).map fun i => blockBytes (hvBlock pp a vs i))

theorem hvState_succ (pp a : E) (vs : Nat → E) (j : Nat) :
    hvState pp a vs (j + 1) = compress (hvState pp a vs j) (blockWords (blockBytes (hvBlock pp a vs j)))
      (64 * (j + 1) : Nat).toUInt64 0 0 := by
  rw [hvState, hvState, List.range_succ, List.map_append, absorbBlocks_append]
  simp only [List.map_cons, List.map_nil, absorbBlocks, List.length_map, List.length_range]
  congr 2
  ring

theorem canonical_hvBlock {pp a : E} {vs : Nat → E} {n : Nat} (hpp : IsCanonical128 pp)
    (ha : IsCanonical128 a) (hvs : ∀ i < n, IsCanonical128 (vs i)) {j : Nat} (hj : 4 * j + 1 < n) :
    ∀ i, IsCanonical128 (hvBlock pp a vs j i) := by
  intro i
  unfold hvBlock
  split
  · fin_cases i
    · exact hpp
    · exact ha
    · exact hvs 0 (by omega)
    · exact hvs 1 (by omega)
  · fin_cases i <;> exact hvs _ (by omega)

/-- One non-final block after the first: its metadata at `c`, its output cells at `c + 1`,
`c + 2`. -/
theorem hvBlock_complete {σ : Val} {m0 m1 m2 m3 : V} {c : Nat} {h : Digest} {blk : Fin 4 → E} {j : Nat}
    (hin : Out c (c + 3) m0 ∧ Out c (c + 3) m1 ∧ Out c (c + 3) m2 ∧ Out c (c + 3) m3)
    (hblk : ![σ m0, σ m1, σ m2, σ m3] = blk) (hcan : ∀ i, IsCanonical128 (blk i))
    (hcv : (σ (.n (c - 2)), σ (.n (c - 1))) = digestScalars h) (hc2 : 2 ≤ c) :
    Completes C rd c (c + 3)
      [cst c (mdw (64 * (j + 1)) false), b2s m0 m1 m2 m3 (.n (c - 2)) (.n (c - 1)) (.n (c + 1)) (.n (c + 2)) (.n c)]
      σ (fun σ' => (σ' (.n (c + 1)), σ' (.n (c + 2))) =
        digestScalars (compress h (blockWords (blockBytes blk)) (64 * (j + 1) : Nat).toUInt64 0 0)) := by
  set o := digestScalars (compress h (blockWords (blockBytes blk)) (64 * (j + 1) : Nat).toUInt64 0 0)
  let σ' := upds σ [(c, mdw (64 * (j + 1)) false), (c + 1, o.1), (c + 2, o.2)]
  have he : Ext c (c + 3) σ σ' := upds_ext σ _ (by simp)
  have hv : ∀ {v : V}, Out c (c + 3) v → σ' v = σ v := fun hv => he.out hv
  have hm : σ' (.n c) = mdw (64 * (j + 1)) false := upds_cons_self σ c _ _
  have ho1 : σ' (.n (c + 1)) = o.1 := by
    simp only [σ']; rw [upds_cons_ne _ _ _ (by omega), upds_cons_self]
  have ho2 : σ' (.n (c + 2)) = o.2 := by
    simp only [σ']; rw [upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega), upds_cons_self]
  have hcv' : (σ' (.n (c - 2)), σ' (.n (c - 1))) = digestScalars h := by
    rw [hv (out_of_lt ⟨c - 2, by omega, rfl⟩), hv (out_of_lt ⟨c - 1, by omega, rfl⟩), hcv]
  refine ⟨σ', he, by show (σ' _, σ' _) = o; rw [ho1, ho2], fun next kret hn => ?_⟩
  simp only [cst, b2s, holdsList_cons_atom, holdsList_nil, Atom.Holds]
  refine ⟨hm, ?_, hn⟩
  rw [hv hin.1, hv hin.2.1, hv hin.2.2.1, hv hin.2.2.2, hblk, ho1, ho2, hm,
    show σ' (.n (c - 2)) = (digestScalars h).1 from congrArg Prod.fst hcv',
    show σ' (.n (c - 1)) = (digestScalars h).2 from congrArg Prod.snd hcv', mdw_eq]
  refine (compressCells_iff hcan (isCanonical128_metadataCell _ _)).mpr ?_
  rw [unpackMetadata_metadataCell]
  rfl

/-- The final block's compression from the chaining value `h`: its data bytes `r`, zero-filled. -/
theorem hvFinal_compress {blk : Fin 4 → E} {h : Digest} {r : List UInt8} (hr : blockBytes blk = r ++
    List.replicate (64 - r.length) 0) (hcan : ∀ i, IsCanonical128 (blk i)) (t : Nat) :
    CompressCells blk (digestScalars h).1 (digestScalars h).2 (digestScalars (absorb h t 0 r)).1
      (digestScalars (absorb h t 0 r)).2 (mdw (t + r.length) true) := by
  rw [mdw_eq]
  refine (compressCells_iff hcan (isCanonical128_metadataCell _ _)).mpr ?_
  rw [unpackMetadata_metadataCell, hr, blockWords_append_zeros, absorb]
  rfl

theorem hcell_split (pp a : E) (vs : Nat → E) (q k : Nat) (hk : 1 ≤ k) (hk4 : k ≤ 4) :
    hcell (pp :: a :: (List.range (4 * q + 2 + k)).map vs) =
      digestScalars (absorb (hvState pp a vs (q + 1)) (64 * (q + 1)) 0
        (((List.range k).map fun i => vs (4 * q + 2 + i)).flatMap cellBytes)) := by
  have hlen : (((List.range k).map fun i => vs (4 * q + 2 + i)).flatMap cellBytes).length = 16 * k := by
    rw [length_flatMap_cellBytes]; simp
  have hbs : ∀ x ∈ ((List.range (q + 1)).map fun j => blockBytes (hvBlock pp a vs j)), x.length = 64 := by
    intro x hx; obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx; exact length_blockBytes _
  have hfl := length_flatten_of_64 _ hbs
  simp only [List.length_map, List.length_range] at hfl
  rw [hcell, hb, hv_bytes_split, blake2sBytes, List.length_append, hfl, hlen,
    show (64 * (q + 1) + 16 * k - 1) / 64 = ((List.range (q + 1)).map fun j => blockBytes (hvBlock pp a vs j)).length + 0
      by simp; omega, absorb_split paramIv 0 _ hbs]
  simp only [List.length_map, List.length_range, Nat.zero_add]
  rfl

/-- **`hash_values` is complete**: over canonical inputs below its base. -/
theorem hashValues_complete {σ : Val} {pp a : V} {val : Nat → V} {n b : Nat}
    (hn : n % 4 = 0 ∨ n % 4 = 2) (hn4 : 4 ≤ n)
    (hin : NB b pp ∧ NB b a ∧ ∀ i < n, NB b (val i))
    (hcan : IsCanonical128 (σ pp) ∧ IsCanonical128 (σ a) ∧ ∀ i < n, IsCanonical128 (σ (val i))) :
    Completes C rd b (b + hashValuesSize n) (hashValues pp a val n b).1 σ
      (fun σ' => σ' (hashValues pp a val n b).2 = (hcell (σ pp :: σ a :: (List.range n).map fun i => σ (val i))).1) := by
  set vs : Nat → E := fun i => σ (val i)
  set q := (n + 1) / 4 - 1 with hq
  have hqn : 4 * q + 2 + (if n % 4 = 0 then 2 else 4) = n := by split_ifs <;> omega
  have hcanB : ∀ j, 4 * j + 1 < n → ∀ i, IsCanonical128 (hvBlock (σ pp) (σ a) vs j i) :=
    fun j hj => canonical_hvBlock hcan.1 hcan.2.1 hcan.2.2 hj
  -- the first block
  set o := digestScalars (hvState (σ pp) (σ a) vs 1)
  let σ1 := upds σ [(b, iv0), (b + 1, iv1), (b + 2, mdw 64 false), (b + 3, o.1), (b + 4, o.2)]
  have he1 : Ext b (b + 5) σ σ1 := upds_ext σ _ (by simp)
  have hag1 : AgreeBelow b σ σ1 := he1.agree
  have hb0 : σ1 (.n b) = iv0 := upds_cons_self σ _ _ _
  have hb1 : σ1 (.n (b + 1)) = iv1 := by simp only [σ1]; rw [upds_cons_ne _ _ _ (by omega), upds_cons_self]
  have hb2 : σ1 (.n (b + 2)) = mdw 64 false := by
    simp only [σ1]; rw [upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega), upds_cons_self]
  have hb3 : σ1 (.n (b + 3)) = o.1 := by
    simp only [σ1]; rw [upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega),
      upds_cons_self]
  have hb4 : σ1 (.n (b + 4)) = o.2 := by
    simp only [σ1]; rw [upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega),
      upds_cons_ne _ _ _ (by omega), upds_cons_self]
  have hk : ∀ {v : V}, NB b v → σ1 v = σ v := fun hv => he1.below hv
  have hiv := ivCells_eq_iv
  simp only [Value.ivCells] at hiv
  -- the middle blocks
  have hMid : ∀ σ', AgreeBelow b σ σ' → (σ' (.n (b + 3)), σ' (.n (b + 4))) = digestScalars (hvState (σ pp) (σ a) vs 1) →
      Completes C rd (b + 5) (b + 5 + 3 * q) ((List.range q).flatMap (hvMid val b)) σ' (fun σ'' =>
        (σ'' (.n (b + 3 * (q + 1))), σ'' (.n (b + 3 * (q + 1) + 1))) = digestScalars (hvState (σ pp) (σ a) vs (q + 1)) ∧
        AgreeBelow b σ σ'') := by
    intro σ' hag hst
    have := Completes.flatMap_range (C := C) (rd := rd) (f := hvMid val b) (base := fun j => b + 5 + 3 * j)
      (Inv := fun j σ'' => (σ'' (.n (b + 3 * (j + 1))), σ'' (.n (b + 3 * (j + 1) + 1))) =
        digestScalars (hvState (σ pp) (σ a) vs (j + 1)) ∧ AgreeBelow b σ σ'') (fun j => by omega) q
      (fun j hjq => by
        simp only [hvMid, cst, b2s, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.cons_append,
          List.nil_append, List.append_nil]
        have hv := fun i (hi : i < n) => NB.mono (hin.2.2 i hi) (show b ≤ b + 5 + 3 * (j + 1) by omega)
        exact .cons ⟨_, by omega, rfl⟩ (.cons (hv _ (by omega)) (.cons (hv _ (by omega)) (.cons (hv _ (by omega))
          (.cons (hv _ (by omega)) (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
          (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _)))))))))))
      (fun j hj σ'' ⟨hst'', hag''⟩ => by
        set c := b + 5 + 3 * j
        have hj' : 4 * (j + 1) + 1 < n := by omega
        have hc := hvBlock_complete (C := C) (rd := rd) (σ := σ'') (m0 := val (4 * j + 2)) (m1 := val (4 * j + 3))
          (m2 := val (4 * j + 4)) (m3 := val (4 * j + 5)) (c := c) (h := hvState (σ pp) (σ a) vs (j + 1))
          (blk := hvBlock (σ pp) (σ a) vs (j + 1)) (j := j + 1)
          ⟨out_of_lt ((hin.2.2 _ (by omega)).mono (by omega)), out_of_lt ((hin.2.2 _ (by omega)).mono (by omega)),
            out_of_lt ((hin.2.2 _ (by omega)).mono (by omega)), out_of_lt ((hin.2.2 _ (by omega)).mono (by omega))⟩
          ?_ (hcanB (j + 1) hj') ?_ (by omega)
        · refine (hc.withExt.mono le_rfl (by omega) fun σ3 h3 => ⟨?_, fun k hk' => (hag'' k hk').trans
            (h3.2.agree k (by omega))⟩)
          rw [hvState_succ, show b + 3 * (j + 1 + 1) + 1 = c + 2 by omega,
            show b + 3 * (j + 1 + 1) = c + 1 by omega]
          exact h3.1
        · simp only [hvBlock, Nat.add_one_ne_zero, ↓reduceIte]
          rw [show 4 * (j + 1) - 2 = 4 * j + 2 by omega, show 4 * (j + 1) - 1 = 4 * j + 3 by omega,
            show 4 * (j + 1) + 1 = 4 * j + 5 by ring, show 4 * (j + 1) = 4 * j + 4 by ring]
          simp only [vs]
          rw [hag''.apply (hin.2.2 _ (by omega)), hag''.apply (hin.2.2 _ (by omega)),
            hag''.apply (hin.2.2 _ (by omega)), hag''.apply (hin.2.2 _ (by omega))]
        · rw [show c - 2 = b + 3 * (j + 1) by omega, show c - 1 = b + 3 * (j + 1) + 1 by omega]
          exact hst'') σ' ⟨by simpa using hst, hag⟩
    simpa using this
  -- the first block
  have hFirst : Completes C rd b (b + 5) (ivs b ++ [cst (b + 2) (mdw 64 false),
      b2s pp a (val 0) (val 1) (.n b) (.n (b + 1)) (.n (b + 3)) (.n (b + 4)) (.n (b + 2))]) σ
      (fun σ' => AgreeBelow b σ σ' ∧
        (σ' (.n (b + 3)), σ' (.n (b + 4))) = digestScalars (hvState (σ pp) (σ a) vs 1)) := by
    refine ⟨σ1, he1, ⟨hag1, by rw [hb3, hb4]⟩, fun next kret hn => ?_⟩
    simp only [ivs, cst, b2s, List.cons_append, List.nil_append, holdsList_cons_atom, holdsList_nil, Atom.Holds]
    refine ⟨hb0, hb1, hb2, ?_, hn⟩
    rw [hk hin.1, hk hin.2.1, hk (hin.2.2 0 (by omega)), hk (hin.2.2 1 (by omega)), hb0, hb1, hb2, hb3, hb4,
      show iv0 = (digestScalars paramIv).1 by rw [hiv], show iv1 = (digestScalars paramIv).2 by rw [hiv], mdw_eq]
    have hc0 := hcanB 0 (by omega)
    simp only [hvBlock, ↓reduceIte] at hc0
    refine (compressCells_iff hc0 (isCanonical128_metadataCell _ _)).mpr ?_
    rw [unpackMetadata_metadataCell]
    simp only [o, hvState, hvBlock]
    rfl
  rw [hashValues_eq]
  dsimp only
  have hFM := Completes.append (m := b + 5) (by omega) (by omega) ?_ hFirst
    (fun σ' _ hp => hMid σ' hp.1 hp.2)
  rotate_left
  · simp only [ivs, cst, b2s, List.cons_append, List.nil_append, valsList_cons, valsList_nil, Stmt.vals,
      Atom.vals, List.append_nil]
    exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons (hin.1.mono (by omega))
      (.cons (hin.2.1.mono (by omega)) (.cons ((hin.2.2 0 (by omega)).mono (by omega))
      (.cons ((hin.2.2 1 (by omega)).mono (by omega)) (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
      (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _))))))))))))
  have hFMb : NumBelow (b + 5 + 3 * q) (Stmt.valsList ((ivs b ++ [cst (b + 2) (mdw 64 false),
      b2s pp a (val 0) (val 1) (.n b) (.n (b + 1)) (.n (b + 3)) (.n (b + 4)) (.n (b + 2))]) ++
      (List.range q).flatMap (hvMid val b))) := by
    rw [valsList_append]
    refine NumBelow.append ?_ (numBelow_valsList_flatMap _ _ fun j hj => ?_)
    · simp only [ivs, cst, b2s, List.cons_append, List.nil_append, valsList_cons, valsList_nil, Stmt.vals,
        Atom.vals, List.append_nil]
      exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons (hin.1.mono (by omega))
        (.cons (hin.2.1.mono (by omega)) (.cons ((hin.2.2 0 (by omega)).mono (by omega))
        (.cons ((hin.2.2 1 (by omega)).mono (by omega)) (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
        (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _))))))))))))
    · simp only [List.mem_range] at hj
      simp only [hvMid, cst, b2s, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.cons_append,
        List.nil_append, List.append_nil]
      have hv := fun i (hi : i < n) => NB.mono (hin.2.2 i hi) (show b ≤ b + 5 + 3 * q by omega)
      exact .cons ⟨_, by omega, rfl⟩ (.cons (hv _ (by omega)) (.cons (hv _ (by omega)) (.cons (hv _ (by omega))
        (.cons (hv _ (by omega)) (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
        (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _))))))))))
  have hsz : hashValuesSize n = 5 + 3 * q + (if n % 4 = 0 then 5 else 3) := rfl
  set out := hcell (σ pp :: σ a :: (List.range n).map fun i => σ (val i)) with hout
  split_ifs with h4
  · have hnq : n = 4 * q + 2 + 2 := by omega
    simp only [h4, ↓reduceIte] at hsz
    refine (Completes.append (m := b + 5 + 3 * q) (hi := b + 5 + 3 * q + 5) (by omega) (by omega) hFMb hFM ?_).mono le_rfl
      (by omega) fun _ h => h
    rintro σ'' - ⟨hst, hag⟩
    set c := b + 5 + 3 * q with hc
    let σf := upds σ'' [(c, 0), (c + 1, 0), (c + 2, mdw (16 * (n + 2)) true), (c + 3, out.1), (c + 4, out.2)]
    have hef : Ext c (c + 5) σ'' σf := upds_ext _ _ (by simp)
    have hf0 : σf (.n c) = 0 := upds_cons_self _ _ _ _
    have hf1 : σf (.n (c + 1)) = 0 := by simp only [σf]; rw [upds_cons_ne _ _ _ (by omega), upds_cons_self]
    have hf2 : σf (.n (c + 2)) = mdw (16 * (n + 2)) true := by
      simp only [σf]; rw [upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega), upds_cons_self]
    have hf3 : σf (.n (c + 3)) = out.1 := by
      simp only [σf]; rw [upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega),
        upds_cons_ne _ _ _ (by omega), upds_cons_self]
    have hf4 : σf (.n (c + 4)) = out.2 := by
      simp only [σf]; rw [upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega),
        upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega), upds_cons_self]
    have hcv1 : σf (.n (c - 2)) = (digestScalars (hvState (σ pp) (σ a) vs (q + 1))).1 := by
      rw [hef.apply (Or.inl (by omega)), show c - 2 = b + 3 * (q + 1) by omega]; exact congrArg Prod.fst hst
    have hcv2 : σf (.n (c - 1)) = (digestScalars (hvState (σ pp) (σ a) vs (q + 1))).2 := by
      rw [hef.apply (Or.inl (by omega)), show c - 1 = b + 3 * (q + 1) + 1 by omega]; exact congrArg Prod.snd hst
    have hvv : ∀ i < n, σf (val i) = vs i := fun i hi =>
      (hef.below ((hin.2.2 i hi).mono (by omega))).trans (hag.apply (hin.2.2 i hi))
    refine ⟨σf, hef, by show σf (.n (c + 3)) = out.1; exact hf3, fun next kret hn => ?_⟩
    simp only [cst, b2s, holdsList_cons_atom, holdsList_nil, Atom.Holds]
    refine ⟨by rw [hf0, word_zero], by rw [hf1, word_zero], hf2, ?_, hn⟩
    rw [hvv _ (by omega), hvv _ (by omega), hf0, hf1, hf2, hf3, hf4, hcv1, hcv2,
      show n - 2 = 4 * q + 2 + 0 by omega, show n - 1 = 4 * q + 2 + 1 by omega]
    have hsplit := hcell_split (σ pp) (σ a) vs q 2 (by norm_num) (by norm_num)
    rw [show 4 * q + 2 + 2 = n by omega] at hsplit
    rw [hout, hsplit]
    have := hvFinal_compress (blk := ![vs (4 * q + 2 + 0), vs (4 * q + 2 + 1), 0, 0])
      (h := hvState (σ pp) (σ a) vs (q + 1))
      (r := ((List.range 2).map fun i => vs (4 * q + 2 + i)).flatMap cellBytes) ?_ ?_ (64 * (q + 1))
    · rw [length_flatMap_cellBytes, List.length_map, List.length_range,
        show 64 * (q + 1) + 16 * 2 = 16 * (n + 2) by omega] at this
      exact this
    · rw [blockBytes_two, length_flatMap_cellBytes]; simp [List.range_succ]
    · intro i; fin_cases i
      · exact hcan.2.2 _ (by omega)
      · exact hcan.2.2 _ (by omega)
      · exact isCanonical128_zero
      · exact isCanonical128_zero
  · have hnq : n = 4 * q + 2 + 4 := by omega
    simp only [h4, ↓reduceIte] at hsz
    refine (Completes.append (m := b + 5 + 3 * q) (hi := b + 5 + 3 * q + 3) (by omega) (by omega) hFMb hFM ?_).mono le_rfl
      (by omega) fun _ h => h
    rintro σ'' - ⟨hst, hag⟩
    set c := b + 5 + 3 * q with hc
    let σf := upds σ'' [(c, mdw (16 * (n + 2)) true), (c + 1, out.1), (c + 2, out.2)]
    have hef : Ext c (c + 3) σ'' σf := upds_ext _ _ (by simp)
    have hf0 : σf (.n c) = mdw (16 * (n + 2)) true := upds_cons_self _ _ _ _
    have hf1 : σf (.n (c + 1)) = out.1 := by simp only [σf]; rw [upds_cons_ne _ _ _ (by omega), upds_cons_self]
    have hf2 : σf (.n (c + 2)) = out.2 := by
      simp only [σf]; rw [upds_cons_ne _ _ _ (by omega), upds_cons_ne _ _ _ (by omega), upds_cons_self]
    have hcv1 : σf (.n (c - 2)) = (digestScalars (hvState (σ pp) (σ a) vs (q + 1))).1 := by
      rw [hef.apply (Or.inl (by omega)), show c - 2 = b + 3 * (q + 1) by omega]; exact congrArg Prod.fst hst
    have hcv2 : σf (.n (c - 1)) = (digestScalars (hvState (σ pp) (σ a) vs (q + 1))).2 := by
      rw [hef.apply (Or.inl (by omega)), show c - 1 = b + 3 * (q + 1) + 1 by omega]; exact congrArg Prod.snd hst
    have hvv : ∀ i < n, σf (val i) = vs i := fun i hi =>
      (hef.below ((hin.2.2 i hi).mono (by omega))).trans (hag.apply (hin.2.2 i hi))
    refine ⟨σf, hef.mono le_rfl (by omega), by show σf (.n (c + 1)) = out.1; exact hf1, fun next kret hn => ?_⟩
    simp only [cst, b2s, holdsList_cons_atom, holdsList_nil, Atom.Holds]
    refine ⟨hf0, ?_, hn⟩
    rw [hvv _ (by omega), hvv _ (by omega), hvv _ (by omega), hvv _ (by omega), hf0, hf1, hf2, hcv1, hcv2,
      show n - 4 = 4 * q + 2 + 0 by omega, show n - 3 = 4 * q + 2 + 1 by omega,
      show n - 2 = 4 * q + 2 + 2 by omega, show n - 1 = 4 * q + 2 + 3 by omega]
    have hsplit := hcell_split (σ pp) (σ a) vs q 4 (by norm_num) (by norm_num)
    rw [show 4 * q + 2 + 4 = n by omega] at hsplit
    rw [hout, hsplit]
    have := hvFinal_compress (blk := ![vs (4 * q + 2 + 0), vs (4 * q + 2 + 1), vs (4 * q + 2 + 2), vs (4 * q + 2 + 3)])
      (h := hvState (σ pp) (σ a) vs (q + 1))
      (r := ((List.range 4).map fun i => vs (4 * q + 2 + i)).flatMap cellBytes) ?_ ?_ (64 * (q + 1))
    · rw [length_flatMap_cellBytes, List.length_map, List.length_range,
        show 64 * (q + 1) + 16 * 4 = 16 * (n + 2) by omega] at this
      exact this
    · rw [length_flatMap_cellBytes]; simp [blockBytes, List.range_succ]
    · intro i; fin_cases i <;> exact hcan.2.2 _ (by omega)

theorem hashValues_below {pp a : V} {val : Nat → V} {n b : Nat} (hn4 : 4 ≤ n)
    (hin : NB b pp ∧ NB b a ∧ ∀ i < n, NB b (val i)) :
    NumBelow (b + hashValuesSize n) (Stmt.valsList (hashValues pp a val n b).1) := by
  set q := (n + 1) / 4 - 1 with hq
  have hsz : hashValuesSize n = 5 + 3 * q + (if n % 4 = 0 then 5 else 3) := rfl
  have hv := fun i (hi : i < n) => NB.mono (hin.2.2 i hi) (show b ≤ b + hashValuesSize n by omega)
  have hpre : NumBelow (b + hashValuesSize n) (Stmt.valsList ((ivs b ++ [cst (b + 2) (mdw 64 false),
      b2s pp a (val 0) (val 1) (.n b) (.n (b + 1)) (.n (b + 3)) (.n (b + 4)) (.n (b + 2))]) ++
      (List.range q).flatMap (hvMid val b))) := by
    rw [valsList_append]
    refine NumBelow.append ?_ (numBelow_valsList_flatMap _ _ fun j hj => ?_)
    · simp only [ivs, cst, b2s, List.cons_append, List.nil_append, valsList_cons, valsList_nil, Stmt.vals,
        Atom.vals, List.append_nil]
      exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons (hin.1.mono (by omega))
        (.cons (hin.2.1.mono (by omega)) (.cons (hv 0 (by omega)) (.cons (hv 1 (by omega))
        (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
        (.cons ⟨_, by omega, rfl⟩ (.nil _))))))))))))
    · simp only [List.mem_range] at hj
      simp only [hvMid, cst, b2s, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.cons_append,
        List.nil_append, List.append_nil]
      exact .cons ⟨_, by omega, rfl⟩ (.cons (hv _ (by omega)) (.cons (hv _ (by omega)) (.cons (hv _ (by omega))
        (.cons (hv _ (by omega)) (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
        (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _))))))))))
  rw [hashValues_eq]
  dsimp only
  split_ifs with h4 <;> simp only [h4, ↓reduceIte] at hsz <;> rw [valsList_append] <;> refine hpre.append ?_ <;>
    simp only [cst, b2s, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.cons_append, List.nil_append,
      List.append_nil]
  · exact .cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons (hv _ (by omega))
      (.cons (hv _ (by omega)) (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
      (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
      (.nil _))))))))))))
  · exact .cons ⟨_, by omega, rfl⟩ (.cons (hv _ (by omega)) (.cons (hv _ (by omega)) (.cons (hv _ (by omega))
      (.cons (hv _ (by omega)) (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩
      (.cons ⟨_, by omega, rfl⟩ (.cons ⟨_, by omega, rfl⟩ (.nil _))))))))))

end
end LeanVM.Guest.B1.Sig
