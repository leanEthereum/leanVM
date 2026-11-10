/-
  LeanVM.Guest.B1.Digest.ChildMono

  B1 for `child_claim_list_mono` (G:4234-4302; TRIAGE #89): a child's claim list walked through
  this node's table by hinted gaps, every claim marked with the list's base, its slots strictly
  increasing, and its digest.
-/

module

public import LeanVM.Guest.B1.Digest.ChildList
public import LeanVM.Guest.B1.Digest.Mono0
public import LeanVM.Guest.B1.Digest.Mono1
public import LeanVM.Guest.B1.Digest.Mono2
public import LeanVM.Guest.B1.Digest.Mono3
public import LeanVM.Guest.B1.Digest.MonoLasts

/-!
# `child_claim_list_mono`

The walk (`child_claims_mono`, G:4234-4252) keeps a coverage pointer `region · g^P` and a table
pointer `entries · g^(4P)`; claim `j` of a frame moves `P` on by its hinted gap `e < 2^32`
(`assert_gpow`) and sits at slot `P + j`, so the slots of a frame from offset `O` are
`O + e_0 + … + e_j + j`, strictly increasing, and the frame ends at `O' = o_last + 1`
(`MonoWalk O os O'`). The frames carry `P` across in their records (`MONO_REC`, the pointers at
13 and 14). The last specialization checks `region · g^O_end = t · region` with `t = g^e`
range-checked against `limit = g^(e + e')` (G:4301): every slot lies below `e`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Walks -/

/-- **A gap walk from offset `O` to `O'`**: the slots strictly increasing, in `[O, O')`, and
`O' ≤ O + |os| · 2^32`. -/
def MonoWalk (O : ℕ) (os : List ℕ) (O' : ℕ) : Prop :=
  (∀ i j, i < j → j < os.length → os.getD i 0 < os.getD j 0) ∧
    (∀ j < os.length, O ≤ os.getD j 0 ∧ os.getD j 0 < O') ∧ O ≤ O' ∧
    O' ≤ O + os.length * 2 ^ 32

theorem monoWalk_nil (O : ℕ) : MonoWalk O [] O :=
  ⟨fun _ _ _ h => absurd h (by simp), fun _ h => absurd h (by simp), le_rfl, by simp⟩

theorem monoWalk_single {O e : ℕ} (he : e < 2 ^ 32) : MonoWalk O [O + e] (O + e + 1) := by
  refine ⟨fun i j hij hj => by simp at hj; omega, fun j hj => ?_, by omega, by simp; omega⟩
  simp only [List.length_singleton, Nat.lt_one_iff] at hj
  subst hj
  simp

theorem monoWalk_append {O O' O'' : ℕ} {os os' : List ℕ} (h1 : MonoWalk O os O')
    (h2 : MonoWalk O' os' O'') : MonoWalk O (os ++ os') O'' := by
  obtain ⟨m1, b1, l1, u1⟩ := h1
  obtain ⟨m2, b2, l2, u2⟩ := h2
  refine ⟨fun i j hij hj => ?_, fun j hj => ?_, by omega, ?_⟩
  · rw [List.length_append] at hj
    by_cases hj1 : j < os.length
    · rw [getD_append_left'' os os' (i := j) 0 hj1,
        getD_append_left'' os os' (i := i) 0 (by omega)]
      exact m1 i j hij hj1
    · rw [getD_append_right'' os os' (i := j) 0 (by omega)]
      by_cases hi1 : i < os.length
      · rw [getD_append_left'' os os' (i := i) 0 hi1]
        have := (b1 i hi1).2
        have := (b2 (j - os.length) (by omega)).1
        omega
      · rw [getD_append_right'' os os' (i := i) 0 (by omega)]
        exact m2 _ _ (by omega) (by omega)
  · rw [List.length_append] at hj
    by_cases hj1 : j < os.length
    · rw [getD_append_left'' os os' (i := j) 0 hj1]
      have := b1 j hj1
      omega
    · rw [getD_append_right'' os os' (i := j) 0 (by omega)]
      have := b2 (j - os.length) (by omega)
      omega
  · rw [List.length_append, Nat.add_mul]
    omega

/-- **The claims of a walk**: claim `j` at slot `os j`, the mark in the region's coverage slot,
its four cells at `entries · g^(4 os j)`. -/
def MonoAt (rd : Reader) (region entries mark : E) (os : List ℕ) (cells : List E) : Prop :=
  cells.length = 4 * os.length ∧ ∀ j < os.length, LoadHolds rd region (os.getD j 0) mark ∧
    ∀ c < 4, LoadHolds rd entries (4 * os.getD j 0 + c) (cells.getD (4 * j + c) 0)

theorem monoAt_nil (rd : Reader) (region entries mark : E) : MonoAt rd region entries mark [] [] :=
  ⟨rfl, fun _ h => absurd h (by simp)⟩

theorem monoAt_append {rd : Reader} {region entries mark : E} {os os' : List ℕ}
    {cells cells' : List E} (h1 : MonoAt rd region entries mark os cells)
    (h2 : MonoAt rd region entries mark os' cells') :
    MonoAt rd region entries mark (os ++ os') (cells ++ cells') := by
  obtain ⟨l1, c1⟩ := h1
  obtain ⟨l2, c2⟩ := h2
  refine ⟨by rw [List.length_append, List.length_append, l1, l2]; ring, fun j hj => ?_⟩
  rw [List.length_append] at hj
  by_cases hj1 : j < os.length
  · rw [getD_append_left'' _ _ _ hj1]
    refine ⟨(c1 j hj1).1, fun c hc => ?_⟩
    rw [getD_append_left'' _ _ _ (by omega)]
    exact (c1 j hj1).2 c hc
  · rw [getD_append_right'' _ _ _ (by omega)]
    obtain ⟨h1, h2⟩ := c2 (j - os.length) (by omega)
    refine ⟨h1, fun c hc => ?_⟩
    rw [getD_append_right'' _ _ _ (by omega),
      show 4 * j + c - cells.length = 4 * (j - os.length) + c by omega]
    exact h2 c hc

/-! ## One claim -/

theorem isDerefOf_sound {rd : Reader} {σ : Val} {atoms : List Atom} {p : V}
    (h : atoms.any (isDerefOf p) = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    ∃ t, LoadHolds rd (σ p) 0 t := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  have := hat a ha
  cases a <;> simp only [isDerefOf, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  exact ⟨_, this⟩

/-- **Claim `j` of the walk**: from the pointers `region · g^P`, `entries · g^(4P)`, a gap
`e < 2^32` moves them to `P + e`, the mark sits at slot `P + e + j`, the cells at its entry. -/
theorem monoClaim_sound {rd : Reader} (hm : MemOk rd) {σ : Val} {atoms : List Atom}
    {j gap pc pe : ℕ} {mark : V} (h : monoClaimOk atoms j gap pc pe mark = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) {region entries : E} {P : ℕ}
    (hpc : σ (.n pc) = region * gen ^ P) (hpe : σ (.n pe) = entries * gen ^ (4 * P)) :
    ∃ e < 2 ^ 32, σ (.n (gap + 2)) = region * gen ^ (P + e) ∧
      σ (.n (gap + 5)) = entries * gen ^ (4 * (P + e)) ∧
      LoadHolds rd region (P + e + j) (σ mark) ∧
      ∀ c < 4, LoadHolds rd entries (4 * (P + e + j) + c) (σ (.n (gap + 6 + c))) := by
  simp only [monoClaimOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨hd, hc⟩, h3⟩, h4⟩, h5⟩, hmk⟩, hcl⟩ := h
  obtain ⟨t, ht⟩ := isDerefOf_sound hd hat
  obtain ⟨e, he, hg⟩ := load_gpow hm ht
  have hcov : σ (.n (gap + 2)) = region * gen ^ (P + e) := by
    rw [mulOf_sound hc hat, hpc, hg, pow_add, mul_assoc]
  have hent : σ (.n (gap + 5)) = entries * gen ^ (4 * (P + e)) := by
    rw [mulOf_sound h5 hat, mulOf_sound h4 hat, mulOf_sound h3 hat, hpe, hg]
    ring
  refine ⟨e, he, hcov, hent, ?_, fun c hc' => ?_⟩
  · have := load_sound hmk hat
    rwa [hcov, loadHolds_mul_gen_pow] at this
  · have := load_sound (hcl c hc') hat
    rw [hent, loadHolds_mul_gen_pow] at this
    rwa [show 4 * (P + e) + (4 * j + c) = 4 * (P + e + j) + c by ring] at this

theorem monoWin_holds {rd : Reader} {σ : Val} {atoms : List Atom}
    (hat : ∀ a ∈ atoms, a.Holds rd σ) (p0 j : ℕ) : ∀ a ∈ monoWin atoms p0 j, a.Holds rd σ :=
  fun a ha => hat a (List.mem_of_mem_drop (List.mem_of_mem_take ha))

theorem mCov_succ (g0 cov0 j : ℕ) : mCov g0 cov0 (j + 1) = g0 + 10 * j + 2 := by
  simp [mCov]

theorem mEnt_succ (g0 ent0 j : ℕ) : mEnt g0 ent0 (j + 1) = g0 + 10 * j + 5 := by
  simp [mEnt]

/-- **The walk's claims**: after `j ≤ n` claims from offset `O`, the slots `os` (a walk to
`P + j`), the pointers at `P`, each claim's mark and cells. -/
theorem monoRecs_sound {rd : Reader} (hm : MemOk rd) {σ : Val} {atoms : List Atom}
    {p0 g0 cov0 ent0 : ℕ} {mark : V} {n : ℕ}
    (h : monoRecs atoms p0 g0 cov0 ent0 mark n 0 n = true) (hat : ∀ a ∈ atoms, a.Holds rd σ)
    {region entries : E} {O : ℕ} (hc0 : σ (.n cov0) = region * gen ^ O)
    (he0 : σ (.n ent0) = entries * gen ^ (4 * O)) :
    ∀ j ≤ n, ∃ (os : List ℕ) (P : ℕ), os.length = j ∧ MonoWalk O os (P + j) ∧
      σ (.n (mCov g0 cov0 j)) = region * gen ^ P ∧ σ (.n (mEnt g0 ent0 j)) = entries * gen ^ (4 * P) ∧
      ∀ i < j, LoadHolds rd region (os.getD i 0) (σ mark) ∧
        ∀ c < 4, LoadHolds rd entries (4 * os.getD i 0 + c) (σ (.n (g0 + 10 * i + 6 + c))) := by
  simp only [monoRecs, List.all_eq_true, List.mem_range', Bool.or_eq_true,
    decide_eq_true_eq] at h
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨[], O, rfl, by simpa using monoWalk_nil O, by simpa [mCov] using hc0,
      by simpa [mEnt] using he0, fun i hi => absurd hi (by omega)⟩
  | succ j ih =>
    intro hj
    obtain ⟨os, P, hlen, hw, hcv, hev, hcl⟩ := ih (by omega)
    have hok : monoClaimOk (monoWin atoms p0 j) j (g0 + 10 * j) (mCov g0 cov0 j)
        (mEnt g0 ent0 j) mark = true := by
      rcases h j ⟨j, by omega, by omega⟩ with h' | h'
      · omega
      · exact h'
    obtain ⟨e, he, hcov, hent, hmk, hcells⟩ :=
      monoClaim_sound hm hok (monoWin_holds hat p0 j) hcv hev
    refine ⟨os ++ [P + e + j], P + e, by simp [hlen], ?_, by rw [mCov_succ]; exact hcov,
      by rw [mEnt_succ]; exact hent, fun i hi => ?_⟩
    · have := monoWalk_append hw (monoWalk_single (O := P + j) he)
      rwa [show P + j + e + 1 = P + e + (j + 1) by ring, show P + j + e = P + e + j by ring] at this
    · by_cases hij : i < j
      · rw [getD_append_left'' _ _ _ (by omega)]
        exact hcl i hij
      · have hi' : i = j := by omega
        subst hi'
        rw [getD_append_right'' _ _ _ (by omega), hlen, Nat.sub_self]
        exact ⟨hmk, hcells⟩

theorem monoMsg_getD {g0 n i c : ℕ} (hi : i < n) (hc : c < 4) (σ : Val) :
    ((monoMsg g0 n).map (srcVal σ)).getD (4 * i + c) 0 = σ (.n (g0 + 10 * i + 6 + c)) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, monoMsg, List.getElem?_map,
    List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some, srcVal]
  rw [show (4 * i + c) / 4 = i by omega, show (4 * i + c) % 4 = c by omega]

theorem length_monoMsg (g0 n : ℕ) : (monoMsg g0 n).length = 4 * n := by simp [monoMsg]

/-- The walk's `n` claims, as `MonoAt` over the message's values. -/
theorem monoRecs_at {rd : Reader} (hm : MemOk rd) {σ : Val} {atoms : List Atom}
    {p0 g0 cov0 ent0 : ℕ} {mark : V} {n : ℕ}
    (h : monoRecs atoms p0 g0 cov0 ent0 mark n 0 n = true) (hat : ∀ a ∈ atoms, a.Holds rd σ)
    {region entries : E} {O : ℕ} (hc0 : σ (.n cov0) = region * gen ^ O)
    (he0 : σ (.n ent0) = entries * gen ^ (4 * O)) :
    ∃ (os : List ℕ) (P : ℕ), os.length = n ∧ MonoWalk O os (P + n) ∧
      σ (.n (mCov g0 cov0 n)) = region * gen ^ P ∧ σ (.n (mEnt g0 ent0 n)) = entries * gen ^ (4 * P) ∧
      MonoAt rd region entries (σ mark) os ((monoMsg g0 n).map (srcVal σ)) := by
  obtain ⟨os, P, hlen, hw, hcv, hev, hcl⟩ := monoRecs_sound hm h hat hc0 he0 n le_rfl
  refine ⟨os, P, hlen, hw, hcv, hev, by rw [List.length_map, length_monoMsg, hlen],
    fun i hi => ⟨(hcl i (by omega)).1, fun c hc => ?_⟩⟩
  rw [monoMsg_getD (by omega) hc]
  exact (hcl i (by omega)).2 c hc

theorem outOk_sound {rd : Reader} {σ : Val} {atoms : List Atom} {rec : V} {off o last w : ℕ}
    (h : outOk atoms rec off o last w = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    LoadHolds rd (σ rec) off (σ (.n o)) ∧ σ (.n o) = σ (.n last) * word w 0 := by
  unfold outOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hl, hm⟩ := h
  refine ⟨load_sound hl hat, ?_⟩
  split at hm
  · rename_i a c hac
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
    obtain ⟨rfl, hc⟩ := hm
    rw [mulOf_sound hac hat, const_sound hc hat]
  · exact absurd hm (by simp)

/-! ## The frame loops -/

/-- **One frame of `m` claims of the walk, `nb` blocks**: from the record at `chain · x^15`
(the state after whole blocks `pre`, the pointers at `O`), `m` claims marked `mark` at slots
walking from `O` to `O'`, absorbed, the next record at offset 15 (the state, the pointers at
`O'`). -/
def MonoStep (rd : Reader) (m nb : ℕ) (chain mark x : E) : Prop :=
  ∀ (region entries : E) (n O : ℕ) (pre : List UInt8), pre.length = rate * n →
    StateAt rd (chain * x ^ 15) 0 (absorbChunks n zeroState pre) →
    LoadHolds rd (chain * x ^ 15) 13 (region * gen ^ O) →
    LoadHolds rd (chain * x ^ 15) 14 (entries * gen ^ (4 * O)) →
    ∃ (os : List ℕ) (cells : List E) (O' : ℕ), os.length = m ∧ MonoWalk O os O' ∧
      MonoAt rd region entries mark os cells ∧
      StateAt rd (chain * x ^ 15) 15 (absorbChunks (n + nb) zeroState (pre ++ cellsBytes cells)) ∧
      LoadHolds rd (chain * x ^ 15) 28 (region * gen ^ O') ∧
      LoadHolds rd (chain * x ^ 15) 29 (entries * gen ^ (4 * O'))

theorem mono_step {rd : Reader} (hm : MemOk rd) {f : String} {j m p0 st0 cw ew nb : ℕ}
    (hidx : coreProgram.indexOf? f = some j) (hj : j < 1055)
    (hok : monoOk (coreProgram.getD j default) f m p0 st0 cw ew = true)
    (hcw : word cw 0 = gen ^ m) (hew : word ew 0 = gen ^ (4 * m))
    (hnb : (monoSpec m st0 (loopAtoms (coreProgram.getD j default))).nb = nb)
    {x : E} {ps : List E} (h : coreProgram.Rel rd f (x :: ps) []) :
    (∀ N chain mark, ps = [N, chain, mark] → MonoStep rd m nb chain mark x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd f (x * gen :: ps) []) := by
  have hf := find_of_idx hidx (by rw [coreProgram_length]; omega)
  simp only [monoOk, monoHead, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hshape, hlen4⟩, -⟩, hst⟩, hout⟩, hm10⟩, hl11⟩, hl12⟩, hoc⟩, hoe⟩, hc⟩,
    hrec⟩ := hok
  obtain ⟨σ, hx, hps, hat, hnext⟩ := loop_step hf hshape h
  refine ⟨fun N chain mark hN region entries n O pre hpre hS hc13 he14 => ?_, hnext⟩
  have hpar : (coreProgram.getD j default).params = [V.n 0, V.n 1, V.n 2, V.n 3] := by
    have hs := hshape
    simp only [loopShape, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen4]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, hchain, hmark⟩ := hps
  have h10 : σ (V.n 10) = chain * x ^ 15 := by rw [monoIs_sound hm10 hat, hchain, hx]
  rw [← h10] at hS hc13 he14
  have h11 : σ (.n 11) = region * gen ^ O := loadHolds_unique (load_sound hl11 hat) hc13
  have h12 : σ (.n 12) = entries * gen ^ (4 * O) := loadHolds_unique (load_sound hl12 hat) he14
  obtain ⟨os, P, hlen, hw, hcv, hev, hat'⟩ := monoRecs_at hm hrec hat (O := O) (region := region)
    (entries := entries) (by simpa using h11) (by simpa using h12)
  obtain ⟨hwo, -⟩ := chain_whole hc rfl hat hpre (initCell_of_loads rfl hst hat hS)
  obtain ⟨hlc, hcc⟩ := outOk_sound hoc hat
  obtain ⟨hle, hce⟩ := outOk_sound hoe hat
  refine ⟨os, _, P + m, hlen, hw, by rwa [hmark] at hat', fun c => ?_, ?_, ?_⟩
  · have hout' := stLoads_sound hout hat c
    have hw' := hwo c
    rw [hnb] at hw' hout'
    rw [getD_map_range _ c.isLt, hw', h10] at hout'
    exact hout'
  · rw [← h10]
    rw [hcc, hcv, hcw, mul_assoc, ← pow_add] at hlc
    exact hlc
  · rw [← h10]
    rw [hce, hev, hew, mul_assoc, ← pow_add, show 4 * P + 4 * m = 4 * (P + m) by ring] at hle
    exact hle

/-- **The frames of the walk**: after `q ≤ a` frames of `m` claims from the record at `chain`
(the pointers at `O0`), the slots walk from `O0` to `O`, and the record at `chain · g^(15q)`
holds the sponge after their cells and the pointers at `O`. -/
theorem monoFrames_sound {rd : Reader} {m nb : ℕ} (hmn : 64 * m = 136 * nb)
    {chain entries region mark : E} {a n0 O0 : ℕ} {pre : List UInt8}
    (hpre0 : pre.length = rate * n0) (h0 : StateAt rd chain 0 (absorbChunks n0 zeroState pre))
    (hc0 : LoadHolds rd chain 13 (region * gen ^ O0))
    (he0 : LoadHolds rd chain 14 (entries * gen ^ (4 * O0)))
    (hstep : ∀ q < a, MonoStep rd m nb chain mark (gen ^ q)) :
    ∀ q ≤ a, ∃ (os : List ℕ) (cells : List E) (O : ℕ), os.length = m * q ∧ MonoWalk O0 os O ∧
      MonoAt rd region entries mark os cells ∧ StateAt rd (chain * gen ^ (15 * q)) 0
        (absorbChunks (n0 + nb * q) zeroState (pre ++ cellsBytes cells)) ∧
      LoadHolds rd (chain * gen ^ (15 * q)) 13 (region * gen ^ O) ∧
      LoadHolds rd (chain * gen ^ (15 * q)) 14 (entries * gen ^ (4 * O)) := by
  intro q
  induction q with
  | zero =>
    intro _
    refine ⟨[], [], O0, rfl, monoWalk_nil O0, monoAt_nil rd _ _ _,
      by simpa using h0, by simpa using hc0, by simpa using he0⟩
  | succ q ih =>
    intro hq
    obtain ⟨os, cells, O, hlen, hw, hat, hS, hc, he⟩ := ih (by omega)
    have hpre : (pre ++ cellsBytes cells).length = rate * (n0 + nb * q) := by
      rw [List.length_append, length_cellsBytes, hat.1, hlen, hpre0]
      show 136 * n0 + 16 * (4 * (m * q)) = 136 * (n0 + nb * q)
      have : 16 * (4 * (m * q)) = (64 * m) * q := by ring
      rw [this, hmn]; ring
    rw [show chain * gen ^ (15 * q) = chain * (gen ^ q) ^ 15 by rw [gen_pow_pow]] at hS hc he
    obtain ⟨os2, c2, O', hlen2, hw2, hat2, hS2, hc2, he2⟩ :=
      hstep q (by omega) region entries _ O _ hpre hS hc he
    rw [gen_pow_pow, loadHolds_mul_gen_pow] at hc2 he2
    refine ⟨os ++ os2, cells ++ c2, O', by rw [List.length_append, hlen, hlen2]; ring,
      monoWalk_append hw hw2, monoAt_append hat hat2, ?_, ?_, ?_⟩
    · intro c
      have := hS2 c
      rw [gen_pow_pow, loadHolds_mul_gen_pow] at this
      rw [loadHolds_mul_gen_pow, cellsBytes_append, ← List.append_assoc,
        show 15 * (q + 1) + (0 + c.val) = 15 * q + (15 + c.val) by ring,
        show n0 + nb * (q + 1) = n0 + nb * q + nb by ring]
      exact this
    · rw [loadHolds_mul_gen_pow, show 15 * (q + 1) + 13 = 15 * q + 28 by ring]
      exact hc2
    · rw [loadHolds_mul_gen_pow, show 15 * (q + 1) + 14 = 15 * q + 29 by ring]
      exact he2

/-- **A loop of frames of the walk**, called as `callIf (1 + N) f [1, N, chain, mark]` with
`N = g^a`, `a < 2^34`. -/
theorem monoFrames_of_loop {rd : Reader} (hm : MemOk rd) {f : String} {j m p0 st0 cw ew nb : ℕ}
    (hidx : coreProgram.indexOf? f = some j) (hj : j < 1055)
    (hok : monoOk (coreProgram.getD j default) f m p0 st0 cw ew = true)
    (hcw : word cw 0 = gen ^ m) (hew : word ew 0 = gen ^ (4 * m))
    (hnb : (monoSpec m st0 (loopAtoms (coreProgram.getD j default))).nb = nb)
    {N chain mark : E} {a : ℕ} (ha : a < 2 ^ 34) (hN : N = gen ^ a)
    (hloop : 1 + N ≠ 0 → coreProgram.Rel rd f [1, N, chain, mark] []) :
    ∀ q < a, MonoStep rd m nb chain mark (gen ^ q) :=
  loop_sound (f := f) (ps := [N, chain, mark]) (N := N)
    (B := MonoStep rd m nb chain mark) (by unfold ordG; omega) hN
    (fun x hx => by
      obtain ⟨h1, h2⟩ := mono_step hm hidx hj hok hcw hew hnb hx
      exact ⟨h1 _ _ _ rfl, h2⟩)
    hloop

/-! ## The loops, checked -/

-- `__loop19`: 136 claims a frame, 64 blocks; its head here, its sixteen windows in `Mono{q}`.
set_option maxRecDepth 100000 in
theorem mono136_idx : coreProgram.indexOf? "__loop19" = some 397 := by decide +kernel

set_option maxRecDepth 100000 in
theorem mono136_nb : (monoSpec 136 1377 (loopAtoms (coreProgram.getD 397 default))).nb = 64 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mono136_head :
    monoHead (coreProgram.getD 397 default) "__loop19" 136 1377 83200 72058697844523035 = true := by
  decide +kernel

theorem mono136_ok :
    monoOk (coreProgram.getD 397 default) "__loop19" 136 9 1377 83200 72058697844523035 = true := by
  have hw : ∀ i < 16, monoWinOk i = true := by
    intro i hi
    interval_cases i
    exacts [monoWin_0, monoWin_1, monoWin_2, monoWin_3, monoWin_4, monoWin_5, monoWin_6,
      monoWin_7, monoWin_8, monoWin_9, monoWin_10, monoWin_11, monoWin_12, monoWin_13, monoWin_14,
      monoWin_15]
  simp only [monoWinOk, mono136Spec, mono136Atoms, Bool.and_eq_true] at hw
  exact monoOk_of_parts (w := 4) (W := 16) (v := 9) (U := 16) mono136_head (by rw [mono136_nb])
    (fun i hi => (hw i hi).1) (by norm_num) (fun i hi => (hw i hi).2)

-- `__loop20`: 17 claims a frame, 8 blocks.
set_option maxRecDepth 100000 in
theorem mono17_idx : coreProgram.indexOf? "__loop20" = some 398 := by decide +kernel

set_option maxRecDepth 100000 in
theorem mono17_nb : (monoSpec 17 187 (loopAtoms (coreProgram.getD 398 default))).nb = 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mono17_ok : monoOk (coreProgram.getD 398 default) "__loop20" 17 9 187 131072 432 = true := by
  decide +kernel

theorem word_g17 : word 131072 0 = gen ^ 17 := word_two_pow (a := 17) (by decide)

set_option maxRecDepth 100000 in
theorem word_g68 : word 432 0 = gen ^ (4 * 17) := by
  rw [word_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  congr 1

set_option maxRecDepth 100000 in
theorem word_g136 : word 83200 0 = gen ^ 136 := by
  rw [word_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  congr 1

set_option maxRecDepth 100000 in
theorem word_g544 : word 72058697844523035 0 = gen ^ (4 * 136) := by
  rw [word_eOfNat, gen_pow_eq_ofK, eOfNat, ← gpowK_eq (by unfold u128Bound; omega)]
  congr 1

/-! ## `child_claim_list_mono_last__L{k}` -/

theorem endOf_sound {rd : Reader} {σ : Val} {atoms : List Atom} {ce t : V}
    (h : endOf atoms ce = some t) (hat : ∀ a ∈ atoms, a.Holds rd σ) : σ ce = σ t * σ (V.n 1) := by
  obtain ⟨a, ha, hs⟩ := List.exists_of_findSome?_eq_some h
  have := hat a ha
  cases a <;> simp only [reduceCtorEq] at hs
  split at hs
  · rename_i hd
    obtain rfl := Option.some.inj hs
    obtain ⟨rfl, rfl⟩ := hd
    exact this
  · exact absurd hs (by simp)

/-- **`child_claim_list_mono_last__L{k}`** `[rec, region, mark, limit]`: from the record at `rec`
(the state after whole blocks `pre`, the pointers at `O`), `k` claims marked `mark` walking from
`O` to `O'`, the digest of `pre` and their cells, and the bound `region · g^O' = g^e · region`,
`limit = g^(e + e')` with `e, e' < 2^32` (G:4301). -/
theorem monoLast_sound {rd : Reader} (hm : MemOk rd) {k : ℕ} (hk : k < 17) {args rets : List E}
    (h : coreProgram.Rel rd (mlNames.getD k "") args rets) :
    ∃ rec region mark limit, args = [rec, region, mark, limit] ∧
      ∀ (entries : E) (n O : ℕ) (pre : List UInt8), pre.length = rate * n →
      StateAt rd rec 0 (absorbChunks n zeroState pre) →
      LoadHolds rd rec 13 (region * gen ^ O) → LoadHolds rd rec 14 (entries * gen ^ (4 * O)) →
      ∃ (os : List ℕ) (cells : List E) (O' : ℕ), os.length = k ∧ MonoWalk O os O' ∧
        MonoAt rd region entries mark os cells ∧
        rets = digestCells (keccak256 (pre ++ cellsBytes cells)) ∧
        ∃ e e', e < 2 ^ 32 ∧ e' < 2 ^ 32 ∧ region * gen ^ O' = gen ^ e * region ∧
          limit = gen ^ (e + e') := by
  have hf := find_of_idx (ml_idx k hk) (by rw [coreProgram_length]; omega)
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem hf args rets).mp h
  have hok := ml_all k hk
  set f := coreProgram.getD (399 + k) default
  simp only [mlOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hpar, hok⟩ := hok
  rw [hpar] at hp
  refine ⟨σ (V.n 0), σ (V.n 1), σ (V.n 2), σ (V.n 3), by rw [← hp]; rfl,
    fun entries n O pre hpre hS hc13 he14 => ?_⟩
  split at hok
  · rename_i atoms r0 r1 hsb
    simp only [Bool.and_eq_true] at hok
    obtain ⟨⟨⟨⟨hc, hr⟩, hst⟩, hwalk⟩, hend⟩ := hok
    rw [splitBody_eq hsb, holdsList_atoms_ret] at hb
    obtain ⟨hat, hret⟩ := hb
    have hd := chain_final hc rfl hat hpre (initCell_of_loads rfl hst hat hS)
    have hbound : ∀ O', σ (.n (mlEnd k)) = σ (V.n 1) * gen ^ O' → ∃ e e', e < 2 ^ 32 ∧
        e' < 2 ^ 32 ∧ σ (V.n 1) * gen ^ O' = gen ^ e * σ (V.n 1) ∧ σ (V.n 3) = gen ^ (e + e') := by
      intro O' hO'
      split at hend
      · rename_i t ht
        simp only [decide_eq_true_eq] at hend
        obtain ⟨y, t1, t2, h1, h2, h3⟩ := rcOf_sound hend hat
        obtain ⟨e, e', he, he', hx, hk'⟩ := rc_sound hm ⟨h1, h2, h3⟩
        exact ⟨e, e', he, he', by rw [← hO', endOf_sound ht hat, hx], hk'⟩
      · exact absurd hend (by simp)
    have hlen : ((mlSpec k atoms).vals σ).length = 4 * k := by
      simp [ChainSpec.vals, mlSpec, length_monoMsg]
    have htake : ((mlSpec k atoms).vals σ).take ((mlSpec k atoms).len / 16) =
        (mlSpec k atoms).vals σ := by
      rw [List.take_of_length_le]
      rw [hlen]; simp only [mlSpec]; omega
    rw [htake] at hd
    have hdig : rets = digestCells (keccak256 (pre ++ cellsBytes ((mlSpec k atoms).vals σ))) := by
      simp only [retOk, Bool.and_eq_true] at hr
      rw [← hret, List.map_cons, List.map_cons, List.map_nil, copy_sound hr.1 hat,
        copy_sound hr.2 hat, digestCells, ← hd]
    by_cases hk0 : k = 0
    · subst hk0
      simp only [↓reduceIte] at hwalk
      have h38 : σ (.n 27) = σ (V.n 1) * gen ^ O := loadHolds_unique (load_sound hwalk hat) hc13
      have hv : (mlSpec 0 atoms).vals σ = [] := by simp [ChainSpec.vals, mlSpec, monoMsg]
      rw [hv] at hdig
      exact ⟨[], [], O, rfl, monoWalk_nil O, monoAt_nil rd _ _ _, hdig, hbound O h38⟩
    · simp only [hk0, ↓reduceIte, Bool.and_eq_true] at hwalk
      obtain ⟨⟨⟨hl4, hl5⟩, hrec⟩, hmul⟩ := hwalk
      have h4 : σ (.n 4) = σ (V.n 1) * gen ^ O := loadHolds_unique (load_sound hl4 hat) hc13
      have h5 : σ (.n 5) = entries * gen ^ (4 * O) := loadHolds_unique (load_sound hl5 hat) he14
      obtain ⟨os, P, hlen', hw, hcv, -, hat'⟩ := monoRecs_at hm hrec hat (O := O)
        (by simpa [mCov] using h4) (by simpa [mEnt] using h5)
      have hce : σ (.n (mlEnd k)) = σ (V.n 1) * gen ^ (P + k) := by
        split at hmul
        · rename_i a c hac
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hmul
          obtain ⟨rfl, hc⟩ := hmul
          rw [mulOf_sound hac hat, const_sound hc hat, word_two_pow (by omega), hcv, mul_assoc,
            ← pow_add]
        · exact absurd hmul (by simp)
      exact ⟨os, _, P + k, hlen', hw, hat', hdig, hbound _ hce⟩
  · exact absurd hok (by simp)

/-! ## `child_claim_list_mono` -/

/-- `child_claim_list_mono`'s body before its `ret`. -/
noncomputable def monoFlat : List Stmt := (Fn.body Data.core26).dropLast

set_option maxRecDepth 100000 in
theorem core26_shape : Fn.body Data.core26 = monoFlat ++ [.ret [.n 52, .n 53]] :=
  stmtsEqb_sound (by decide +kernel)

/-- The body: the zero state at `chain = .n 16`, `region` and `entries` at `chain · g^13`,
`chain · g^14`, the big frames' loop, `mid = chain · bigs^15`, the groups' loop,
`last = mid · groups^15`, the dispatch on the rest. -/
noncomputable def monoBodyOk : Bool :=
  monoFlat.all Stmt.flat &&
  monoFlat.any (stmtEqb · (.callIf (.n 31) "__loop19" [.n 32, .n 4, .n 16, .n 2])) &&
  monoFlat.any (stmtEqb · (.callIf (.n 41) "__loop20" [.n 42, .n 5, .n 39, .n 2])) &&
  monoFlat.any (stmtEqb · (.dispatch (.n 6) mlNames [.n 49, .n 1, .n 2, .n 3] [.n 50, .n 51])) &&
  (atomsIn monoFlat).any (isConstAt (.n 32) 1 0) &&
  (atomsIn monoFlat).any (isAddAt (.n 31) (.n 30) (.n 4)) &&
  (atomsIn monoFlat).any (isConstAt (.n 30) 1 0) &&
  (atomsIn monoFlat).any (isConstAt (.n 42) 1 0) &&
  (atomsIn monoFlat).any (isAddAt (.n 41) (.n 40) (.n 5)) &&
  (atomsIn monoFlat).any (isConstAt (.n 40) 1 0) &&
  (List.range 13).all (fun c => (atomsIn monoFlat).any (isLoadAt (.n (17 + c)) (.n 16) c) &&
    (atomsIn monoFlat).any (isConstAt (.n (17 + c)) 0 0)) &&
  (atomsIn monoFlat).any (isLoadAt (.n 1) (.n 16) 13) &&
  (atomsIn monoFlat).any (isLoadAt (.n 0) (.n 16) 14) &&
  monoIs (atomsIn monoFlat) (.n 39) (.n 16) (.n 4) 15 &&
  mono2Is (atomsIn monoFlat) (.n 49) (.n 16) (.n 4) 15 (.n 5) 15 &&
  (atomsIn monoFlat).any (isCopyAt (.n 52) (.n 50)) &&
  (atomsIn monoFlat).any (isCopyAt (.n 53) (.n 51))

set_option maxRecDepth 100000 in
theorem monoBody_ok : monoBodyOk = true := by decide +kernel

theorem find_child_claim_list_mono :
    coreProgram.find? "child_claim_list_mono" = some Data.core26 :=
  Program.find?_of_indexOf? (j := 26) (by decide +kernel) rfl

/-- **`child_claim_list_mono`** (G:4255-4286): on `bigs = g^a`, `groups = g^b`, `rest = g^c`, the
`136a + 17b + c` claims walked by hinted gaps from slot 0 to `O`, every claim marked `base`, their
digest, and the bound on `O`: `region · g^O = g^e · region`, `limit = g^(e + e')`. -/
theorem child_claim_list_mono_sound {rd : Reader} (hm : MemOk rd) {args rets : List E}
    (h : coreProgram.Rel rd "child_claim_list_mono" args rets) :
    ∃ entries region base limit bigs groups rest,
      args = [entries, region, base, limit, bigs, groups, rest] ∧
      ∀ a b c, a < 2 ^ 16 → b < 8 → c < 17 → bigs = gen ^ a → groups = gen ^ b → rest = gen ^ c →
        ∃ (os : List ℕ) (cells : List E) (O : ℕ), os.length = 136 * a + 17 * b + c ∧
          MonoWalk 0 os O ∧ MonoAt rd region entries base os cells ∧
          rets = digestCells (keccak256 (cellsBytes cells)) ∧
          ∃ e e', e < 2 ^ 32 ∧ e' < 2 ^ 32 ∧ region * gen ^ O = gen ^ e * region ∧
            limit = gen ^ (e + e') := by
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem find_child_claim_list_mono args rets).mp h
  refine ⟨σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6),
    by rw [← hp]; rfl, fun a b c ha hb' hc h4 h5 h6 => ?_⟩
  rw [core26_shape, holdsList_append] at hb
  have hok := monoBody_ok
  simp only [monoBodyOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hfl, hl19⟩, hl20⟩, hdis⟩, h32⟩, h31⟩, h30⟩, h42⟩, h41⟩, h40⟩, hzs⟩,
    hl1⟩, hl0⟩, hm39⟩, hm49⟩, hc52⟩, hc53⟩ := hok
  obtain ⟨hall, hret⟩ := holdsList_flat _ (List.all_eq_true.mpr hfl) _ _ hb
  simp only [Stmt.HoldsList, Stmt.Holds, List.map_cons, List.map_nil] at hret
  have hat := atoms_of_flat hall
  -- the zero record
  have h0 : StateAt rd (σ (.n 16)) 0 (absorbChunks 0 zeroState []) := by
    intro c
    have hl := load_sound (hzs c c.isLt).1 hat
    rw [const_sound (hzs c c.isLt).2 hat, word_zero] at hl
    rw [Nat.zero_add, absorbChunks, cellsOfState_zero]
    exact hl
  have hc0 : LoadHolds rd (σ (.n 16)) 13 (σ (.n 1) * gen ^ 0) := by
    rw [pow_zero, mul_one]; exact load_sound hl1 hat
  have he0 : LoadHolds rd (σ (.n 16)) 14 (σ (.n 0) * gen ^ (4 * 0)) := by
    rw [mul_zero, pow_zero, mul_one]; exact load_sound hl0 hat
  -- the big frames
  have hbig := monoFrames_of_loop hm mono136_idx (by norm_num) mono136_ok word_g136 word_g544
    mono136_nb (chain := σ (.n 16)) (mark := σ (.n 2)) (by omega) h4 (fun hne => by
      have := (callIf_of_flat hall hl19).2
        (by rw [add_sound h31 hat, const_sound h30 hat, word_one]; exact hne)
      simpa [const_sound h32 hat, word_one] using this)
  obtain ⟨osa, ca, Oa, hla, hwa, hata, hSa, hca, hea⟩ :=
    monoFrames_sound (by norm_num) (n0 := 0) (pre := []) rfl h0 hc0 he0 hbig a le_rfl
  -- the groups
  have h39 : σ (.n 39) = σ (.n 16) * gen ^ (15 * a) := by
    rw [monoIs_sound hm39 hat, h4, gen_pow_pow]
  have hgrp := monoFrames_of_loop hm mono17_idx (by norm_num) mono17_ok word_g17 word_g68
    mono17_nb (chain := σ (.n 39)) (mark := σ (.n 2)) (by omega) h5 (fun hne => by
      have := (callIf_of_flat hall hl20).2
        (by rw [add_sound h41 hat, const_sound h40 hat, word_one]; exact hne)
      simpa [const_sound h42 hat, word_one] using this)
  have hpa : ([] ++ cellsBytes ca).length = rate * (0 + 64 * a) := by
    rw [List.nil_append, length_cellsBytes, hata.1, hla]
    show 16 * (4 * (136 * a)) = 136 * (0 + 64 * a)
    ring
  obtain ⟨osb, cb, Ob, hlb, hwb, hatb, hSb, hcb, heb⟩ :=
    monoFrames_sound (by norm_num) hpa (by rw [h39]; exact hSa) (by rw [h39]; exact hca)
      (by rw [h39]; exact hea) hgrp b le_rfl
  -- the rest
  obtain ⟨j, hj, hsel, hcall⟩ := dispatch_of_flat hall hdis
  have hj17 : j < 17 := hj
  have hjc : j = c := by
    rw [h6, gen_pow_eq_ofK] at hsel
    exact (gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
      (ofK_injective hsel)).symm
  subst hjc
  rw [show mlNames[j] = mlNames.getD j "" by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl] at hcall
  obtain ⟨rec, reg, mk, lim, hargs, hlast⟩ := monoLast_sound hm hj17 hcall
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hargs
  obtain ⟨hrec, hreg, hmk, hlim⟩ := hargs
  have h49 : σ (.n 49) = σ (.n 39) * gen ^ (15 * b) := by
    rw [mono2Is_sound hm49 hat, h39, h4, h5]; simp only [gen_pow_pow]
  have hpre : ([] ++ cellsBytes ca ++ cellsBytes cb).length = rate * (0 + 64 * a + 8 * b) := by
    rw [List.length_append, List.nil_append, length_cellsBytes, length_cellsBytes, hata.1, hla,
      hatb.1, hlb]
    show 16 * (4 * (136 * a)) + 16 * (4 * (17 * b)) = 136 * (0 + 64 * a + 8 * b)
    ring
  rw [← hreg, ← hmk] at hlast
  obtain ⟨osc, cc, Oc, hlc, hwc, hatc, hd, hbd⟩ := hlast (σ (.n 0)) _ Ob _ hpre
    (by rw [← hrec, h49]; exact hSb) (by rw [← hrec, h49]; exact hcb)
    (by rw [← hrec, h49]; exact heb)
  refine ⟨osa ++ osb ++ osc, ca ++ cb ++ cc, Oc, ?_,
    monoWalk_append (monoWalk_append hwa hwb) hwc, monoAt_append (monoAt_append hata hatb) hatc,
    ?_, by rw [hlim]; exact hbd⟩
  · rw [List.length_append, List.length_append, hla, hlb, hlc]
  · simp only [List.map_cons, List.map_nil] at hd
    rw [← hret, copy_sound hc52 hat, copy_sound hc53 hat, hd, cellsBytes_append,
      cellsBytes_append]
    simp

/-- **The walk's bound gives the slots' bound**: with the claims marked in the region (so
`region ≠ 0`), `region · g^O = g^e · region` puts `O = e`, and every slot below `O` lies below
the log of `limit = g^(e + e')`. -/
theorem monoSlots {rd : Reader} (hm : MemOk rd) {region entries mark limit : E} {os : List ℕ}
    {cells : List E} {O : ℕ} (hw : MonoWalk 0 os O) (hat : MonoAt rd region entries mark os cells)
    (hn : os.length < 2 ^ 24)
    (hb : ∃ e e', e < 2 ^ 32 ∧ e' < 2 ^ 32 ∧ region * gen ^ O = gen ^ e * region ∧
      limit = gen ^ (e + e')) :
    ∀ j < os.length, SlotBelow limit (os.getD j 0) := by
  intro j hj
  obtain ⟨e, e', he, he', hreg, hlim⟩ := hb
  have hl := (hat.2 j hj).1
  rw [← Nat.add_zero (os.getD j 0), ← loadHolds_mul_gen_pow] at hl
  obtain ⟨f, -, hf⟩ := load_gpow hm hl
  have hr0 : region ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hf
    exact pow_ne_zero f gen_ne_zero hf.symm
  have hO : gen ^ O = gen ^ e := by
    rw [mul_comm] at hreg
    exact mul_right_cancel₀ hr0 hreg
  have hOb : O < 2 ^ 56 := by
    have := hw.2.2.2
    have h56 : os.length * 2 ^ 32 < 2 ^ 56 := by
      calc os.length * 2 ^ 32 < 2 ^ 24 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right hn (by positivity)
        _ = 2 ^ 56 := by norm_num
    omega
  have hOe : O = e := gen_pow_inj (by omega) (by omega) hO
  have := (hw.2.1 j hj).2
  exact ⟨e + e', by omega, hlim, by omega⟩

end
end LeanVM.Guest.B1.Digest
