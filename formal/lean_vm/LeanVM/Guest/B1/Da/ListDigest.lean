/-
  LeanVM.Guest.B1.Da.ListDigest

  B1 for the DA root list: `da_hash_roots` (17 specializations), `da_list_digest` and
  `cover_da_root` (G:3088-3116; TRIAGE #73-75).
-/

module

public import LeanVM.Guest.B1.Digest.Common
public import LeanVM.Spec.Node

/-!
# The DA root list

`da_hash_roots__L{n}` hashes the `n ≤ 16` DA claims at `roots`, four cells a claim (its root's two
cells, then its vector digest's), as one BLAKE2s with compile-time counters: `daListDigest`
(`Spec/Node.lean`). `da_list_digest` dispatches on `n_g = g^n`. `cover_da_root` reads the claim
at a hinted index below `log n_slots_g` and marks its coverage slot.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Node

@[expose] public section

/-! ## The claims as cells -/

/-- The DA claims at `p`, four cells a claim: the root's two cells, the vector digest's two. -/
def DaClaimsAt (rd : Reader) (p : E) (claims : List DaClaim) : Prop :=
  ∀ i (h : i < claims.length), LoadHolds rd p (4 * i) (digestScalars claims[i].1).1 ∧
    LoadHolds rd p (4 * i + 1) (digestScalars claims[i].1).2 ∧
    LoadHolds rd p (4 * i + 2) (digestScalars claims[i].2).1 ∧
    LoadHolds rd p (4 * i + 3) (digestScalars claims[i].2).2

/-- **`da_hash_roots__L{n}`**: the `n` DA claims at `roots` hash to their list digest. -/
def Meaning_da_hash_roots (n : ℕ) (rd : Reader) (args rets : List E) : Prop :=
  ∃ roots d0 d1, args = [roots] ∧ rets = [d0, d1] ∧ ∃ claims : List DaClaim,
    claims.length = n ∧ DaClaimsAt rd roots claims ∧ (d0, d1) = digestScalars (daListDigest claims)

/-! ## The template of `da_hash_roots__L{n}`, `n ≥ 1` -/

/-- Block `i` of `n`: the claim's four cells, its metadata cell, its compression. -/
def hrBlock (n i : ℕ) : List Atom :=
  [.load (.n (3 + 7 * i)) (.n 0) (4 * i), .load (.n (4 + 7 * i)) (.n 0) (4 * i + 1),
   .load (.n (5 + 7 * i)) (.n 0) (4 * i + 2), .load (.n (6 + 7 * i)) (.n 0) (4 * i + 3),
   .const (.n (7 + 7 * i)) (word (64 * (i + 1)) (if i + 1 = n then 4294967295 else 0) 0),
   .blake2s (.n (3 + 7 * i)) (.n (4 + 7 * i)) (.n (5 + 7 * i)) (.n (6 + 7 * i)) (.n (1 + 7 * i))
     (.n (2 + 7 * i)) (.n (1 + 7 * (i + 1))) (.n (2 + 7 * (i + 1))) (.n (7 + 7 * i))]

/-- `da_hash_roots__L{n}`'s body, `n ≥ 1`. -/
def hrBody (n : ℕ) : List Stmt :=
  (([.const (.n 1) (word 13503953895743350343 11912009169889063794 0),
    .const (.n 2) (word 11170449402626986623 6620516960021240235 0)] : List Atom) ++
    (List.range n).flatMap (hrBlock n) ++
    ([.copy (.n (3 + 7 * n)) (.n (1 + 7 * n)), .copy (.n (4 + 7 * n)) (.n (2 + 7 * n)),
     .copy (.n (5 + 7 * n)) (.n (3 + 7 * n)), .copy (.n (6 + 7 * n)) (.n (4 + 7 * n))] : List Atom)).map .atom ++
  [.ret [.n (5 + 7 * n), .n (6 + 7 * n)]]

/-- `da_hash_roots__L0`'s body: the empty input's one compression. -/
def hrBody0 : List Stmt :=
  ([.const (.n 1) (word 0 0 0), .const (.n 2) (word 0 0 0), .const (.n 3) (word 0 0 0),
    .const (.n 4) (word 0 0 0), .const (.n 5) (word 13503953895743350343 11912009169889063794 0),
    .const (.n 6) (word 11170449402626986623 6620516960021240235 0),
    .const (.n 7) (word 0 4294967295 0),
    .blake2s (.n 1) (.n 2) (.n 3) (.n 4) (.n 5) (.n 6) (.n 8) (.n 9) (.n 7),
    .copy (.n 10) (.n 8), .copy (.n 11) (.n 9)] : List Atom).map .atom ++ [.ret [.n 10, .n 11]]

/-- The specializations' names, as `da_list_digest` dispatches on them. -/
def hrNames : List String :=
  ["da_hash_roots__L0", "da_hash_roots__L1", "da_hash_roots__L2", "da_hash_roots__L3",
   "da_hash_roots__L4", "da_hash_roots__L5", "da_hash_roots__L6", "da_hash_roots__L7",
   "da_hash_roots__L8", "da_hash_roots__L9", "da_hash_roots__L10", "da_hash_roots__L11",
   "da_hash_roots__L12", "da_hash_roots__L13", "da_hash_roots__L14", "da_hash_roots__L15",
   "da_hash_roots__L16"]

set_option maxRecDepth 100000 in
theorem find_da_hash_roots (n : ℕ) (hn : n ≤ 16) :
    coreProgram.find? (hrNames.getD n "") =
      some ⟨hrNames.getD n "", [.n 0], if n = 0 then hrBody0 else hrBody n⟩ := by
  obtain ⟨j, hj⟩ : ∃ j, j = 549 + n := ⟨_, rfl⟩
  interval_cases n
  all_goals exact Program.find?_of_indexOf? (j := j) (by subst hj; decide +kernel) (by subst hj; rfl)

/-! ## The chain over the claims -/

/-- The four cells of a DA claim, as a block. -/
def daBlock (c : DaClaim) : Fin 4 → E :=
  ![(digestScalars c.1).1, (digestScalars c.1).2, (digestScalars c.2).1, (digestScalars c.2).2]

theorem blockBytes_daBlock (c : DaClaim) :
    blockBytes (daBlock c) = digestBytes c.1 ++ digestBytes c.2 := by
  rw [digestBytes_eq, digestBytes_eq]
  simp [blockBytes, daBlock]

theorem daBlock_canonical (c : DaClaim) (r : Fin 4) : IsCanonical128 (daBlock c r) := by
  fin_cases r <;> simp [daBlock, isCanonical128_digestScalars]

theorem range_map_getD {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem?_eq_getElem h2]

/-- The chain of `da_hash_roots__L{n}` is the list digest. -/
theorem chainRun_daList (claims : List DaClaim) (n : ℕ) (hlen : claims.length = n) (hn : 1 ≤ n) :
    chainRun paramIv (fun i => daBlock (claims.getD i default))
        (fun i => metadataCell (64 * (i + 1)) (decide (i + 1 = n))) n =
      daListDigest claims := by
  subst hlen
  obtain ⟨m, hm⟩ : ∃ m, claims.length = m + 1 := ⟨claims.length - 1, by omega⟩
  rw [hm, chainRun_blocks (n := m) (fun j _ r => daBlock_canonical _ r)
    (fun j hj => by congr 1; simp only [decide_eq_false_iff_not]; omega)
    (by simp)]
  unfold daListDigest
  congr 1
  rw [← hm]
  conv_rhs => rw [← range_map_getD claims default]
  rw [List.flatMap_map]
  exact List.flatMap_congr fun i _ => blockBytes_daBlock _

/-! ## `da_hash_roots__L{n}`, `n ≥ 1` -/

/-- Block `i` of the honest run. -/
noncomputable def hrB (claims : List DaClaim) (i : ℕ) : Fin 4 → E := daBlock (claims.getD i default)

/-- Metadata cell `i` of `n`. -/
def hrM (n i : ℕ) : E := metadataCell (64 * (i + 1)) (decide (i + 1 = n))

/-- The state after `i` blocks. -/
noncomputable def hrS (n : ℕ) (claims : List DaClaim) (i : ℕ) : E × E :=
  digestScalars (chainRun paramIv (hrB claims) (hrM n) i)

/-- Cell `r` of a block, `r < 4`. -/
def blockAt (b : Fin 4 → E) (r : ℕ) : E := if r = 0 then b 0 else if r = 1 then b 1 else if r = 2 then b 2 else b 3

/-- The honest values of `da_hash_roots__L{n}`. -/
noncomputable def hrVals (n : ℕ) (roots : E) (claims : List DaClaim) (k : ℕ) : E :=
  if k = 0 then roots else
  if (k - 1) % 7 = 0 then (hrS n claims ((k - 1) / 7)).1 else
  if (k - 1) % 7 = 1 then (hrS n claims ((k - 1) / 7)).2 else
  if (k - 1) % 7 = 6 then hrM n ((k - 1) / 7) else
  if (k - 1) / 7 < n then blockAt (hrB claims ((k - 1) / 7)) ((k - 1) % 7 - 2) else
  if (k - 1) % 7 % 2 = 0 then (hrS n claims ((k - 1) / 7)).1 else (hrS n claims ((k - 1) / 7)).2

section
variable {n : ℕ} {roots : E} {claims : List DaClaim} (i : ℕ)

theorem hrVals_0 : hrVals n roots claims 0 = roots := rfl

theorem hrVals_1 : hrVals n roots claims (1 + 7 * i) = (hrS n claims i).1 := by
  simp only [hrVals, show ¬(1 + 7 * i = 0) by omega, show (1 + 7 * i - 1) / 7 = i by omega,
    show (1 + 7 * i - 1) % 7 = 0 by omega, ↓reduceIte]

theorem hrVals_2 : hrVals n roots claims (2 + 7 * i) = (hrS n claims i).2 := by
  simp only [hrVals, show ¬(2 + 7 * i = 0) by omega, show (2 + 7 * i - 1) / 7 = i by omega,
    show (2 + 7 * i - 1) % 7 = 1 by omega, ↓reduceIte, one_ne_zero]

theorem hrVals_7 : hrVals n roots claims (7 + 7 * i) = hrM n i := by
  simp only [hrVals, show ¬(7 + 7 * i = 0) by omega, show (7 + 7 * i - 1) / 7 = i by omega,
    show (7 + 7 * i - 1) % 7 = 6 by omega, ↓reduceIte]
  simp

theorem hrVals_cell (r : ℕ) (hr : r < 4) (hi : i < n) :
    hrVals n roots claims (3 + r + 7 * i) = blockAt (hrB claims i) r := by
  simp only [hrVals, show ¬(3 + r + 7 * i = 0) by omega, show (3 + r + 7 * i - 1) / 7 = i by omega,
    show (3 + r + 7 * i - 1) % 7 = r + 2 by omega, show r + 2 ≠ 0 by omega,
    show r + 2 ≠ 1 by omega, show r + 2 ≠ 6 by omega, hi, ↓reduceIte, Nat.add_sub_cancel]

theorem hrVals_tail (r : ℕ) (hr : r < 4) :
    hrVals n roots claims (3 + r + 7 * n) =
      if r % 2 = 0 then (hrS n claims n).1 else (hrS n claims n).2 := by
  simp only [hrVals, show ¬(3 + r + 7 * n = 0) by omega, show (3 + r + 7 * n - 1) / 7 = n by omega,
    show (3 + r + 7 * n - 1) % 7 = r + 2 by omega, show r + 2 ≠ 0 by omega,
    show r + 2 ≠ 1 by omega, show r + 2 ≠ 6 by omega, lt_irrefl, ↓reduceIte, Nat.add_mod_right]

end

theorem da_hash_roots_succ_iff (n : ℕ) (hn1 : 1 ≤ n) (rd : Reader) (args rets : List E) :
    Fn.Sem (coreProgram.Rel rd) rd ⟨hrNames.getD n "", [.n 0], hrBody n⟩ args rets ↔
      Meaning_da_hash_roots n rd args rets := by
  simp only [Fn.Sem, hrBody, holdsList_atoms, holdsList_ret, List.forall_mem_append,
    forall_mem_flatMap_range, hrBlock, List.forall_mem_cons, Atom.Holds,
    List.map_cons, List.map_nil, forall_mem_nil_iff, and_true, Meaning_da_hash_roots]
  constructor
  · rintro ⟨σ, hp, ⟨⟨⟨h1, h2⟩, hblk⟩, h3, h4, h5, h6⟩, hr⟩
    have hcan : ∀ i < n, IsCanonical128 (σ (.n (3 + 7 * i))) ∧ IsCanonical128 (σ (.n (4 + 7 * i))) ∧
        IsCanonical128 (σ (.n (5 + 7 * i))) ∧ IsCanonical128 (σ (.n (6 + 7 * i))) := fun i hi =>
      ⟨(hblk i hi).2.2.2.2.2.1 0, (hblk i hi).2.2.2.2.2.1 1, (hblk i hi).2.2.2.2.2.1 2,
        (hblk i hi).2.2.2.2.2.1 3⟩
    have hch := chain_eq_chainRun (n := n) (h := paramIv)
      (blocks := fun i => ![σ (.n (3 + 7 * i)), σ (.n (4 + 7 * i)), σ (.n (5 + 7 * i)),
        σ (.n (6 + 7 * i))]) (md := fun i => σ (.n (7 + 7 * i)))
      (st := fun i => (σ (.n (1 + 7 * i)), σ (.n (2 + 7 * i))))
      (by show (σ (.n 1), σ (.n 2)) = _; rw [h1, h2, iv0_word, iv1_word])
      (fun j hj => (hblk j hj).2.2.2.2.2) n le_rfl
    let claims : List DaClaim := (List.range n).map fun i =>
      (cellsDigest (σ (.n (3 + 7 * i))) (σ (.n (4 + 7 * i))),
        cellsDigest (σ (.n (5 + 7 * i))) (σ (.n (6 + 7 * i))))
    have hlen : claims.length = n := by simp [claims]
    have hget : ∀ i (hi : i < n), claims.getD i default =
        (cellsDigest (σ (.n (3 + 7 * i))) (σ (.n (4 + 7 * i))),
          cellsDigest (σ (.n (5 + 7 * i))) (σ (.n (6 + 7 * i)))) := by
      intro i hi
      simp [claims, List.getD_eq_getElem?_getD, hi]
    refine ⟨σ (.n 0), σ (.n (5 + 7 * n)), σ (.n (6 + 7 * n)), hp.symm, hr.symm, claims, hlen,
      ?_, ?_⟩
    · intro i hi
      have hi' : i < n := hlen ▸ hi
      have hc := hcan i hi'
      rw [← List.getD_eq_getElem _ default hi, hget i hi',
        digestScalars_cellsDigest hc.1 hc.2.1, digestScalars_cellsDigest hc.2.2.1 hc.2.2.2]
      exact ⟨(hblk i hi').1, (hblk i hi').2.1, (hblk i hi').2.2.1, (hblk i hi').2.2.2.1⟩
    · rw [h5, h6, h3, h4, hch, ← chainRun_daList claims n hlen hn1]
      congr 1
      refine chainRun_congr n (fun i hi => ?_) (fun i hi => ?_)
      · have hc := hcan i hi
        rw [hget i hi, daBlock, digestScalars_cellsDigest hc.1 hc.2.1,
          digestScalars_cellsDigest hc.2.2.1 hc.2.2.2]
      · rw [(hblk i hi).2.2.2.2.1, word_metadata]
  · rintro ⟨roots, d0, d1, rfl, rfl, claims, hlen, hroots, hd⟩
    have hS : hrS n claims n = (d0, d1) := by
      rw [hd, hrS]
      congr 1
      exact chainRun_daList claims n hlen hn1
    refine ⟨fun v => hrVals n roots claims v.idx, rfl, ⟨⟨⟨?_, ?_⟩, fun i hi => ?_⟩, ?_⟩, ?_⟩
    · show (hrS n claims 0).1 = _
      rw [iv0_word]; rfl
    · show (hrS n claims 0).2 = _
      rw [iv1_word]; rfl
    · have hc : ∀ r (hr : r < 4), hrVals n roots claims (3 + r + 7 * i) = blockAt (hrB claims i) r :=
        fun r hr => hrVals_cell i r hr hi
      have hcl : claims.getD i default = claims[i]'(hlen ▸ hi) := List.getD_eq_getElem _ _ _
      have hR := hroots i (hlen ▸ hi)
      dsimp only
      rw [hrVals_7, hrVals_1, hrVals_2, hrVals_1, hrVals_2, show 3 + 7 * i = 3 + 0 + 7 * i by rfl,
        show 4 + 7 * i = 3 + 1 + 7 * i by omega, show 5 + 7 * i = 3 + 2 + 7 * i by omega,
        show 6 + 7 * i = 3 + 3 + 7 * i by omega, hc 0 (by omega), hc 1 (by omega), hc 2 (by omega),
        hc 3 (by omega)]
      have hb : ∀ r, blockAt (hrB claims i) r = blockAt (daBlock claims[i]) r := by
        intro r; rw [hrB, hcl]
      rw [hrVals_0, hb, hb, hb, hb]
      refine ⟨hR.1, hR.2.1, hR.2.2.1, hR.2.2.2, by rw [word_metadata]; rfl, ?_⟩
      rw [← hb, ← hb, ← hb, ← hb, show ![blockAt (hrB claims i) 0, blockAt (hrB claims i) 1,
        blockAt (hrB claims i) 2, blockAt (hrB claims i) 3] = hrB claims i by
          funext r; fin_cases r <;> rfl]
      exact (compressCells_chainRun (daBlock_canonical _) (isCanonical128_metadataCell _ _)).mpr rfl
    · dsimp only
      rw [show 3 + 7 * n = 3 + 0 + 7 * n by rfl, show 4 + 7 * n = 3 + 1 + 7 * n by omega,
        show 5 + 7 * n = 3 + 2 + 7 * n by omega, show 6 + 7 * n = 3 + 3 + 7 * n by omega,
        hrVals_tail 0 (by omega), hrVals_tail 1 (by omega), hrVals_tail 2 (by omega),
        hrVals_tail 3 (by omega), hrVals_1, hrVals_2]
      simp
    · dsimp only
      rw [show 5 + 7 * n = 3 + 2 + 7 * n by omega, show 6 + 7 * n = 3 + 3 + 7 * n by omega,
        hrVals_tail 2 (by omega), hrVals_tail 3 (by omega), hS]
      simp

theorem da_hash_roots_zero_iff (rd : Reader) (args rets : List E) :
    Fn.Sem (coreProgram.Rel rd) rd ⟨hrNames.getD 0 "", [.n 0], hrBody0⟩ args rets ↔
      Meaning_da_hash_roots 0 rd args rets := by
  simp only [Fn.Sem, hrBody0, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    Stmt.HoldsList, Stmt.Holds, Atom.Holds, Meaning_da_hash_roots, List.length_eq_zero_iff]
  constructor
  · rintro ⟨σ, hp, h1, h2, h3, h4, h5, h6, h7, hc, h10, h11, hr⟩
    refine ⟨σ (.n 0), σ (.n 10), σ (.n 11), hp.symm, hr.symm, [], rfl, fun _ h => absurd h (by simp), ?_⟩
    rw [h1, h2, h3, h4, h5, h6, h7, word_zero, iv0_word, iv1_word] at hc
    rw [h10, h11]
    exact blake2s_empty hc
  · rintro ⟨roots, d0, d1, rfl, rfl, claims, rfl, -, hd⟩
    have hc : CompressCells ![0, 0, 0, 0] (digestScalars paramIv).1 (digestScalars paramIv).2
        (digestScalars (chainRun paramIv (fun _ => ![0, 0, 0, 0]) (fun _ => metadataCell 0 true) 1)).1
        (digestScalars (chainRun paramIv (fun _ => ![0, 0, 0, 0]) (fun _ => metadataCell 0 true) 1)).2
        (metadataCell 0 true) :=
      (compressCells_chainRun (h := paramIv) (blocks := fun _ => ![0, 0, 0, 0])
        (md := fun _ => metadataCell 0 true) (i := 0)
        (fun r => by fin_cases r <;> exact isCanonical128_zero)
        (isCanonical128_metadataCell _ _)).mpr rfl
    have he := blake2s_empty hc
    rw [Prod.mk.eta] at he
    rw [he, show blake2sBytes [] = daListDigest [] from rfl, ← hd] at hc
    refine ⟨listVal [roots, 0, 0, 0, 0, (digestScalars paramIv).1, (digestScalars paramIv).2,
      metadataCell 0 true, d0, d1, d0, d1], rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    all_goals simp only [listVal, List.getD_cons_succ, List.getD_cons_zero]
    · exact word_zero.symm
    · exact word_zero.symm
    · exact word_zero.symm
    · exact word_zero.symm
    · exact iv0_word.symm
    · exact iv1_word.symm
    · rfl
    · exact hc

/-- **`da_hash_roots__L{n}`** is the list digest of the `n` claims it reads. -/
theorem da_hash_roots_iff (n : ℕ) (hn : n ≤ 16) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (hrNames.getD n "") args rets ↔ Meaning_da_hash_roots n rd args rets := by
  rw [rel_of_find (find_da_hash_roots n hn)]
  rcases Nat.eq_zero_or_pos n with rfl | h
  · exact da_hash_roots_zero_iff rd args rets
  · simp only [show n ≠ 0 by omega, ↓reduceIte]
    exact da_hash_roots_succ_iff n h rd args rets

/-! ## `da_list_digest` -/

/-- **`da_list_digest(roots, n_g)`**: `n_g = g^n` for the `n ≤ 16` claims at `roots`, hashed to
their list digest. -/
def Meaning_da_list_digest (rd : Reader) (args rets : List E) : Prop :=
  ∃ roots n_g d0 d1, args = [roots, n_g] ∧ rets = [d0, d1] ∧ ∃ claims : List DaClaim,
    claims.length ≤ 16 ∧ n_g = gen ^ claims.length ∧ DaClaimsAt rd roots claims ∧
      (d0, d1) = digestScalars (daListDigest claims)

set_option maxRecDepth 100000 in
theorem find_da_list_digest : coreProgram.find? "da_list_digest" = some ⟨"da_list_digest",
    [.n 0, .n 1], [.dispatch (.n 1) hrNames [.n 0] [.n 2, .n 3], .atom (.copy (.n 4) (.n 2)),
      .atom (.copy (.n 5) (.n 3)), .ret [.n 4, .n 5]]⟩ :=
  Program.find?_of_indexOf? (j := 27) (by decide +kernel) rfl

theorem da_list_digest_iff (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd "da_list_digest" args rets ↔ Meaning_da_list_digest rd args rets := by
  rw [rel_of_find find_da_list_digest]
  simp only [Fn.Sem, List.map_cons, List.map_nil, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    Meaning_da_list_digest]
  constructor
  · rintro ⟨σ, hp, ⟨⟨j, hj, hx, hc⟩, h4, h5, hr⟩⟩
    have hj' : j ≤ 16 := by simp [hrNames] at hj; omega
    rw [← List.getD_eq_getElem _ "" hj, da_hash_roots_iff j hj'] at hc
    obtain ⟨roots, d0, d1, hr0, hr1, claims, hlen, hcl, hd⟩ := hc
    simp only [List.cons.injEq, and_true] at hr0 hr1
    refine ⟨σ (.n 0), σ (.n 1), σ (.n 4), σ (.n 5), hp.symm, hr.symm, claims, hlen ▸ hj', ?_, ?_, ?_⟩
    · rw [hx, hlen, gen_pow_eq_ofK]
    · rw [hr0]; exact hcl
    · rw [h4, h5, hr1.1, hr1.2]; exact hd
  · rintro ⟨roots, n_g, d0, d1, rfl, rfl, claims, hlen, rfl, hcl, hd⟩
    refine ⟨listVal [roots, gen ^ claims.length, d0, d1, d0, d1], rfl,
      ⟨claims.length, by simp [hrNames]; omega, by simp [listVal, gen_pow_eq_ofK], ?_⟩, rfl, rfl,
      rfl⟩
    rw [← List.getD_eq_getElem _ "" _, da_hash_roots_iff _ hlen]
    exact ⟨roots, d0, d1, rfl, rfl, claims, rfl, hcl, hd⟩

/-! ## `cover_da_root` -/

/-- **`cover_da_root(roots, cover, n_slots_g, mark)`**: for a slot `i` below `log n_slots_g`, the
mark is in the coverage table at `cover·g^i` and the four returned cells are the claim at
`roots·g^(4i)`. -/
def Meaning_cover_da_root (rd : Reader) (args rets : List E) : Prop :=
  ∃ roots cover nslots mark r0 r1 r2 r3, args = [roots, cover, nslots, mark] ∧
    rets = [r0, r1, r2, r3] ∧ ∃ i M, M < 2 ^ 33 ∧ i < M ∧ nslots = gen ^ M ∧
      LoadHolds rd (cover * gen ^ i) 0 mark ∧ CellsAt rd (roots * gen ^ (4 * i)) [r0, r1, r2, r3]

/-- `cover_da_root`'s body. -/
def coverBody : List Stmt :=
  [.atom (.hint (.witness "da_index" (.stack [.n 4]))),
   .atom (.const (.n 5) (word 9223372036854775821 0 0)), .atom (.mul (.n 6) (.n 2) (.n 5)),
   .atom (.rangeCheck (.n 4) (.n 7) (.n 8) (.n 9) (.n 6)), .atom (.mul (.n 10) (.n 1) (.n 4)),
   .atom (.load (.n 3) (.n 10) 0), .atom (.mul (.n 11) (.n 4) (.n 4)),
   .atom (.mul (.n 12) (.n 11) (.n 11)), .atom (.mul (.n 13) (.n 0) (.n 12)),
   .atom (.load (.n 14) (.n 13) 0), .atom (.load (.n 15) (.n 13) 1),
   .atom (.load (.n 16) (.n 13) 2), .atom (.load (.n 17) (.n 13) 3),
   .ret [.n 14, .n 15, .n 16, .n 17]]

set_option maxRecDepth 100000 in
theorem find_cover_da_root : coreProgram.find? "cover_da_root" =
    some ⟨"cover_da_root", [.n 0, .n 1, .n 2, .n 3], coverBody⟩ :=
  Program.find?_of_indexOf? (j := 28) (by decide +kernel) rfl

theorem gen_pow_four_mul (a : E) : a * a * (a * a) = a ^ 4 := by ring

theorem cover_da_root_sound {rd : Reader} (hm : MemOk rd) {args rets : List E}
    (h : coreProgram.Rel rd "cover_da_root" args rets) : Meaning_cover_da_root rd args rets := by
  rw [rel_of_find find_cover_da_root] at h
  simp only [Fn.Sem, coverBody, List.map_cons, List.map_nil, Stmt.HoldsList, Stmt.Holds,
    Atom.Holds] at h
  obtain ⟨σ, hp, -, h5, h6, hrc, h10, hmk, h11, h12, h13, l0, l1, l2, l3, hr⟩ := h
  obtain ⟨e, e', he, he', hx, -, hk⟩ := rangeCheck_sound hm hrc
  have hM : σ (.n 2) = gen ^ (e + e' + 1) := by
    have : σ (.n 2) = σ (.n 2) * (word 9223372036854775821 0 0 * gen) := by
      rw [ginv_mul_gen, mul_one]
    rw [this, ← mul_assoc, ← h5, ← h6, hk, pow_succ]
  refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 14), σ (.n 15), σ (.n 16), σ (.n 17),
    hp.symm, hr.symm, e, e + e' + 1, by omega, by omega, hM, ?_, ?_⟩
  · rw [← hx, ← h10]; exact hmk
  · rw [cellsAt_four, pow_mul', ← gen_pow_four_mul, ← hx, ← h11, ← h12, ← h13]
    exact ⟨l0, l1, l2, l3⟩

theorem cover_da_root_complete {rd : Reader} (hm : MemOk rd) {roots cover mark r0 r1 r2 r3 : E}
    {i M : ℕ} (hM : M ≤ 2 ^ 16) (hi : i < M) (hmark : LoadHolds rd (cover * gen ^ i) 0 mark)
    (hroot : CellsAt rd (roots * gen ^ (4 * i)) [r0, r1, r2, r3]) :
    coreProgram.Rel rd "cover_da_root" [roots, cover, gen ^ M, mark] [r0, r1, r2, r3] := by
  rw [rel_of_find find_cover_da_root]
  obtain ⟨t1, t2, l1, hk, l2⟩ := rangeCheck_complete hm (e := i) (e' := M - 1 - i) (by omega)
    (by omega)
  rw [cellsAt_four] at hroot
  have hk' : gen ^ M * word 9223372036854775821 0 0 = gen ^ i * gen ^ (M - 1 - i) := by
    rw [← hk, show i + (M - 1 - i) = M - 1 by omega,
      show gen ^ M = gen ^ (M - 1) * gen by rw [← pow_succ]; congr 1; omega, mul_assoc,
      mul_comm gen, ginv_mul_gen, mul_one]
  refine ⟨listVal [roots, cover, gen ^ M, mark, gen ^ i, word 9223372036854775821 0 0,
    gen ^ M * word 9223372036854775821 0 0, gen ^ (M - 1 - i), t1, t2, cover * gen ^ i,
    gen ^ i * gen ^ i, gen ^ i * gen ^ i * (gen ^ i * gen ^ i),
    roots * (gen ^ i * gen ^ i * (gen ^ i * gen ^ i)), r0, r1, r2, r3], rfl, ?_⟩
  rw [pow_mul', ← gen_pow_four_mul] at hroot
  simp only [coverBody, List.map_cons, List.map_nil, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
    listVal, List.getD_cons_succ, List.getD_cons_zero, true_and, and_true]
  exact ⟨⟨l1, hk', l2⟩, hmark, hroot.1, hroot.2.1, hroot.2.2.1, hroot.2.2.2⟩

end
end LeanVM.Guest.B1.Digest

namespace LeanVM.Guest.B1
export Digest (DaClaimsAt Meaning_da_hash_roots da_hash_roots_iff hrNames Meaning_da_list_digest da_list_digest_iff Meaning_cover_da_root cover_da_root_sound cover_da_root_complete)
end LeanVM.Guest.B1
