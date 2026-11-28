/-
  LeanVM.Wire.HonestCost

  The stream the leanVM verifier program reads in its phases that commit and open nothing: a
  bound per phase, over every size the verifier accepts.
-/

module

public import LeanVM.Protocol.Verifier.Defers

/-!
# The stream of the phases that commit and open nothing

`CostLE p n`: `p` commits and opens nothing, and every run of it reads at most `n` stream elements
(a scalar one, a packed message its length, a nonce one). It composes over a bind, the
continuation at the values the first part may return (`CostLE.bind`, `CostLE.seq`). Every phase of
`verify_execution` but the stack's commitment and the stacked opening is costed here, over the
sizes the verifier accepts (`SizesOK`: a layout of `tables()` with table log-heights at most
`MAX_TABLE_LOG`, the `KECCAK` table's at least `PACK_BITS`), each by a constant:

* the sizes: `8`; the stack's out-of-domain sample: `2`;
* the link up to the program's split (`linkPre`): `122`, the width at most `MAX_WIDTH = 24`;
* the link after it (`linkSufOf`): `linkSufCost`, its rows at most `30`, its chunks at most `25`;
* `KECCAK`'s reduction (`verifyKeccak`): `keccakStream`, at a point of at most `30` coordinates;
* ring switching: `1`; the public input and the memory term: `0`.
-/

@[expose] public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Verifier.Defers

variable {α β : Type}

/-! ## The calculus -/

/-- **`p` commits and opens nothing, and reads at most `n` stream elements** on every run. -/
def CostLE : VerifierProgram α → ℕ → Prop
  | .ret _, _ => True
  | .fail, _ => True
  | .read k, n => 1 ≤ n ∧ ∀ x, CostLE (k x) (n - 1)
  | .sample k, n => ∀ x, CostLE (k x) n
  | .readPacked m k, n => m ≤ n ∧ ∀ xs, CostLE (k xs) (n - m)
  | .samplePacked _ k, n => ∀ xs, CostLE (k xs) n
  | .grind _ k, n => 1 ≤ n ∧ CostLE k (n - 1)
  | .commit _ _ _, _ => False
  | .query _ _ _, _ => False

namespace CostLE

theorem mono {p : VerifierProgram α} {n m : ℕ} (h : CostLE p n) (hnm : n ≤ m) : CostLE p m := by
  induction p generalizing n m with
  | ret a => trivial
  | fail => trivial
  | read k ih => exact ⟨by have := h.1; omega, fun x ↦ ih x (h.2 x) (by omega)⟩
  | sample k ih => exact fun x ↦ ih x (h x) hnm
  | readPacked k_n k ih => exact ⟨by have := h.1; omega, fun x ↦ ih x (h.2 x) (by omega)⟩
  | samplePacked _ k ih => exact fun x ↦ ih x (h x) hnm
  | grind b k ih => exact ⟨by have := h.1; omega, ih h.2 (by omega)⟩
  | commit _ _ _ _ => exact h.elim
  | query _ _ _ _ => exact h.elim

/-- **Sequencing**: the costs add, the continuation at the values the first part may return. -/
theorem bind {p : VerifierProgram α} {f : α → VerifierProgram β} {a b : ℕ} (hp : CostLE p a)
    (hf : ∀ x, VerifierProgram.ReturnsAny p x → CostLE (f x) b) : CostLE (p.bind f) (a + b) := by
  induction p generalizing a with
  | ret x => exact (hf x (.ret x)).mono (by omega)
  | fail => trivial
  | read k ih =>
    refine ⟨by have := hp.1; omega, fun x ↦ ?_⟩
    have := ih x (hp.2 x) fun y hy ↦ hf y (.read x hy)
    rwa [show a - 1 + b = a + b - 1 by have := hp.1; omega] at this
  | sample k ih => exact fun x ↦ ih x (hp x) fun y hy ↦ hf y (.sample x hy)
  | readPacked m k ih =>
    refine ⟨by have := hp.1; omega, fun xs ↦ ?_⟩
    have := ih xs (hp.2 xs) fun y hy ↦ hf y (.readPacked m xs hy)
    rwa [show a - m + b = a + b - m by have := hp.1; omega] at this
  | samplePacked m k ih => exact fun xs ↦ ih xs (hp xs) fun y hy ↦ hf y (.samplePacked m xs hy)
  | grind bits k ih =>
    refine ⟨by have := hp.1; omega, ?_⟩
    have := ih hp.2 fun y hy ↦ hf y (.grind bits hy)
    rwa [show a - 1 + b = a + b - 1 by have := hp.1; omega] at this
  | commit _ _ _ _ => exact hp.elim
  | query _ _ _ _ => exact hp.elim

/-- Sequencing against a fixed budget: the first part spends `a` of `n`. -/
theorem seq {p : VerifierProgram α} {f : α → VerifierProgram β} {a n : ℕ} (hp : CostLE p a)
    (hf : ∀ x, VerifierProgram.ReturnsAny p x → CostLE (f x) (n - a)) (ha : a ≤ n) :
    CostLE (p >>= f) n :=
  (bind hp hf).mono (by omega)

theorem ret' (a : α) (n : ℕ) : CostLE (VerifierProgram.ret a) n := trivial

theorem pure' (a : α) (n : ℕ) : CostLE (pure a : VerifierProgram α) n := trivial

theorem readE : CostLE VerifierProgram.readScalar 1 := ⟨le_rfl, fun _ ↦ trivial⟩

theorem sampleE : CostLE VerifierProgram.sampleChallenge 0 := fun _ ↦ trivial

theorem readN : ∀ n, CostLE (VerifierProgram.readScalars n) n
  | 0 => trivial
  | n + 1 => seq readE (fun _ _ ↦ seq (readN n) (fun _ _ ↦ trivial) (by omega)) (by omega)

theorem sampleN : ∀ n, CostLE (VerifierProgram.sampleChallenges n) 0
  | 0 => trivial
  | n + 1 => seq sampleE (fun _ _ ↦ seq (sampleN n) (fun _ _ ↦ trivial) (by omega)) (by omega)

theorem readPackedP (m : ℕ) : CostLE (VerifierProgram.readScalarsPacked m) m :=
  ⟨le_rfl, fun _ ↦ trivial⟩

theorem samplePackedP (m : ℕ) : CostLE (VerifierProgram.sampleChallengesPacked m) 0 :=
  fun _ ↦ trivial

theorem grindP (bits : ℕ) : CostLE (VerifierProgram.grindProofOfWork bits) 1 := by
  unfold VerifierProgram.grindProofOfWork
  split
  · trivial
  · exact ⟨le_rfl, trivial⟩

theorem require (c : Prop) [Decidable c] : CostLE (VerifierProgram.require c) 0 := by
  unfold VerifierProgram.require
  split <;> trivial

theorem liftOptionP (o : Option α) : CostLE (liftOption o) 0 := by
  cases o <;> trivial

theorem sumcheckRoundPolyP (count : ℕ) (claim : E) (e : Option E) :
    CostLE (sumcheckRoundPoly count claim e) (count + 2) := by
  cases e with
  | none =>
    exact seq readE (fun _ _ ↦ seq (readN _) (fun _ _ ↦ seq (grindP _) (fun _ _ ↦ trivial)
      (by omega)) (by omega)) (by omega)
  | some r =>
    exact seq (readN _) (fun _ _ ↦ seq (grindP _) (fun _ _ ↦ trivial) (by omega)) (by omega)

theorem sumcheckP (count : ℕ) : ∀ (claim : E) (eqs : List (Option E)),
    CostLE (sumcheck claim count eqs) (eqs.length * (count + 2))
  | _, [] => trivial
  | claim, e :: es => by
    have hl : (e :: es).length * (count + 2) = es.length * (count + 2) + (count + 2) := by
      simp only [List.length_cons, Nat.succ_mul]
    refine seq (sumcheckRoundPolyP count claim e) (fun _ _ ↦ seq sampleE (fun _ _ ↦
      seq (sumcheckP count _ es) (fun _ _ ↦ trivial) ?_) (Nat.zero_le _)) ?_ <;> omega

end CostLE

/-! ## The sizes the verifier accepts -/

theorem log2Ceil_le {v k : ℕ} (h : v ≤ 2 ^ k) : log2Ceil v ≤ k := by
  unfold log2Ceil bitLength
  split
  · exact Nat.zero_le _
  · rename_i hv
    have := (Nat.log2_lt hv).mpr (by omega : v - 1 < 2 ^ k)
    omega

/-- The sizes a layout the verifier accepts has: the program's layout of `tables()`, every table's
log-height at most `MAX_TABLE_LOG = 30` and one per table, and the stack's log-size in
`MIN_STACKED_LOG ..= MAX_STACKED_LOG`. -/
structure SizesOK (layout : Layout) : Prop where
  tables_eq : layout.tables = tables
  heights_le : ∀ h ∈ layout.tableLogHeights, h ≤ 30
  stack_ge : Whir.minLogStack ≤ layout.stackLog
  stack_le : layout.stackLog ≤ Whir.maxLogStack

theorem mem_zipWith_max_le : ∀ {rows floors : List ℕ}, (∀ r ∈ rows, r ≤ 2 ^ maxTableLog) →
    (∀ f ∈ floors, f ≤ 30) → ∀ {x : ℕ},
      x ∈ List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) rows floors → x ≤ 30
  | [], _, _, _, _, hx => by simp at hx
  | _ :: _, [], _, _, _, hx => by simp at hx
  | r :: rs, f :: fs, hr, hf, x, hx => by
    rw [List.zipWith_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · have h1 := log2Ceil_le (hr r List.mem_cons_self)
      have h2 := hf f List.mem_cons_self
      unfold maxTableLog at h1
      omega
    · exact mem_zipWith_max_le (fun r h ↦ hr r (List.mem_cons_of_mem _ h))
        (fun f h ↦ hf f (List.mem_cons_of_mem _ h)) hx

theorem buildLayout_sizes {bytecode : List K} {logMemory : ℕ} {tableRows : List ℕ}
    {layout : Layout} (h : buildLayout bytecode logMemory tableRows = some layout) :
    layout.tables = tables ∧ ∀ x ∈ layout.tableLogHeights, x ≤ 30 := by
  unfold buildLayout at h
  split at h
  · cases h
  · split at h
    · next hc =>
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨rfl, fun x hx ↦ ?_⟩
      have hrows : ∀ r ∈ tableRows, r ≤ 2 ^ maxTableLog := by
        have := hc.2.2.1
        simpa using this
      have hfl : ∀ f ∈ tableLogFloors, f ≤ 30 := by decide
      exact mem_zipWith_max_le hrows hfl hx
    · cases h

/-- What `readAnnouncedSizes` returns: a layout the verifier accepts, and a rate in `1..4`. -/
theorem readSizes_ok {bytecode : List K} {x : Layout × ℕ}
    (h : VerifierProgram.ReturnsAny (readAnnouncedSizes bytecode) x) :
    SizesOK x.1 ∧ 1 ≤ x.2 ∧ x.2 ≤ 4 := by
  unfold readAnnouncedSizes at h
  obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
  obtain ⟨_, hr, h⟩ := VerifierProgram.returnsAny_bind h
  obtain ⟨layout, hl, h⟩ := VerifierProgram.returnsAny_bind h
  obtain ⟨_, hs, h⟩ := VerifierProgram.returnsAny_bind h
  rw [VerifierProgram.returnsAny_ret h]
  have hr := VerifierProgram.returnsAny_require hr
  have hs := VerifierProgram.returnsAny_require hs
  obtain ⟨ht, hh⟩ := buildLayout_sizes (returnsAny_liftOption hl)
  exact ⟨⟨ht, hh, hs.1, hs.2⟩, hr⟩

theorem readSizesP (bytecode : List K) : CostLE (readAnnouncedSizes bytecode) 8 := by
  unfold readAnnouncedSizes
  exact CostLE.seq (CostLE.readN _) (fun _ _ ↦ CostLE.seq (CostLE.require _) (fun _ _ ↦
    CostLE.seq (CostLE.require _) (fun _ _ ↦ CostLE.seq (CostLE.liftOptionP _) (fun _ _ ↦
      CostLE.seq (CostLE.require _) (fun _ _ ↦ trivial) (by omega)) (by omega)) (by omega))
    (by omega)) (by decide)

theorem readOodP (stackLog : ℕ) : CostLE (readOod stackLog) 2 := by
  unfold readOod
  exact CostLE.seq (CostLE.grindP _) (fun _ _ ↦ CostLE.seq (CostLE.sampleN _) (fun _ _ ↦
    CostLE.seq CostLE.readE (fun _ _ ↦ trivial) (by omega)) (by omega)) (by omega)

theorem CostLE.ite {c : Prop} [Decidable c] {p q : VerifierProgram α} {n : ℕ} (hp : CostLE p n)
    (hq : CostLE q n) : CostLE (if c then p else q) n := by
  split
  · exact hp
  · exact hq

theorem returns_sampleN : ∀ {n : ℕ} {xs : List E},
    VerifierProgram.ReturnsAny (VerifierProgram.sampleChallenges n) xs → xs.length = n
  | 0, xs, h => by rw [VerifierProgram.returnsAny_ret h]; rfl
  | n + 1, xs, h => by
    unfold VerifierProgram.sampleChallenges at h
    obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
    obtain ⟨ys, hys, h⟩ := VerifierProgram.returnsAny_bind h
    rw [VerifierProgram.returnsAny_ret h, List.length_cons, returns_sampleN hys]

/-! ## The link -/

/-- `Chunks::new` refuses a width over `MAX_WIDTH`, and makes at most `25` chunks. -/
theorem Chunks.new_le {w : ℕ} {c : Chunks} (h : Chunks.new w = some c) :
    c.width ≤ maxPointerWidth ∧ c.d ≤ 25 := by
  unfold Chunks.new at h
  split at h
  · next hw =>
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨hw.2, ?_⟩
    simp only [Chunks.d, List.length_cons]
    have hrest : w - min w windowBits ≤ 24 := by unfold maxPointerWidth at hw; omega
    suffices ht : ∀ rest ≤ 24, ∀ (p : List ℕ → Bool),
        (((((List.range rest).map (· + 1)).map fun d ↦ (List.range d).map fun i ↦
          rest / d + if i < rest % d then 1 else 0).find? p).getD []).length ≤ 24 by
      split
      · exact Nat.succ_le_succ (ht _ hrest _)
      · simp
    intro rest hr p
    rcases hf : (((List.range rest).map (· + 1)).map fun d ↦ (List.range d).map fun i ↦
        rest / d + if i < rest % d then 1 else 0).find? p with _ | x
    · simp
    · have hm := List.mem_of_find?_eq_some hf
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hm
      obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
      simp only [Option.getD_some, List.length_map, List.length_range]
      have := List.mem_range.mp hd'
      omega
  · cases h

/-- **The link up to the program's split** reads at most `122` stream elements. -/
theorem linkPreP (layout : Layout) : CostLE (linkPre layout) 122 := by
  unfold linkPre
  refine CostLE.seq (CostLE.liftOptionP _) (fun chunks hc ↦ ?_) (Nat.zero_le _)
  have hw := (Chunks.new_le (returnsAny_liftOption hc)).1
  unfold maxPointerWidth at hw
  refine CostLE.seq (CostLE.grindP _) (fun _ _ ↦ ?_) (by omega)
  refine CostLE.seq CostLE.sampleE (fun _ _ ↦ ?_) (Nat.zero_le _)
  refine CostLE.seq (CostLE.samplePackedP _) (fun _ _ ↦ ?_) (Nat.zero_le _)
  refine CostLE.seq (CostLE.sumcheckP 3 _ _) (fun _ _ ↦ ?_) ?_
  · refine CostLE.seq CostLE.readE (fun _ _ ↦ ?_) ?_
    · exact CostLE.seq (CostLE.samplePackedP _) (fun _ _ ↦ trivial) (Nat.zero_le _)
    · simp only [List.length_replicate]; omega
  · simp only [List.length_replicate]; omega

/-- The chunks the link's prefix returns: `Chunks::new`'s. -/
theorem linkPre_chunks {layout : Layout} {y : LinkPre}
    (h : VerifierProgram.ReturnsAny (linkPre layout) y) : ∃ w, Chunks.new w = some y.chunks := by
  unfold linkPre at h
  obtain ⟨chunks, hc, h⟩ := VerifierProgram.returnsAny_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
  rw [VerifierProgram.returnsAny_ret h]
  exact ⟨_, returnsAny_liftOption hc⟩

theorem foldl_max_le {l : List ℕ} {b : ℕ} (h : ∀ x ∈ l, x ≤ b) : ∀ a ≤ b, l.foldl max a ≤ b := by
  induction l with
  | nil => intro a ha; exact ha
  | cons x l ih =>
    intro a ha
    exact ih (fun y hy ↦ h y (List.mem_cons_of_mem _ hy)) _
      (max_le ha (h x List.mem_cons_self))

/-- The stream the link reads after the program's split, at most. -/
def linkSufCost : ℕ := 30 * 30 + 6 * 29 + 80 + kBits

/-- **The link after the program's split** reads at most `linkSufCost` stream elements, on a
layout the verifier accepts. -/
theorem linkSufOfP {layout : Layout} (hs : SizesOK layout) {y : LinkPre} {w : ℕ}
    (hc : Chunks.new w = some y.chunks) (ps : E × E) :
    CostLE (linkSufOf layout y ps) linkSufCost := by
  have hd := (Chunks.new_le hc).2
  have hrows : layout.tableLogHeights.foldl max 0 ≤ 30 := foldl_max_le hs.heights_le 0 (by omega)
  have hq : log2Ceil ((layout.tables.map (·.links.pointers)).map List.length).sum = 6 := by
    rw [hs.tables_eq]; decide
  have hv : ((layout.tables.zipIdx.map fun (x : Table × ℕ) ↦ ((List.range x.1.width).filter
      fun c ↦ !((layout.tables.map (·.links.pointers)).getD x.2 []).contains c).length).sum) =
        80 := by
    rw [hs.tables_eq]; decide
  obtain ⟨p1, p2⟩ := ps
  have hk : kBits = 64 := rfl
  have hX : layout.tableLogHeights.foldl max 0 * (max (y.chunks.d + 2) 4 + 1 + 2) ≤ 900 :=
    le_trans (Nat.mul_le_mul hrows (show max (y.chunks.d + 2) 4 + 1 + 2 ≤ 30 by omega))
      (by norm_num)
  unfold linkSufOf
  refine CostLE.seq (CostLE.sumcheckP _ _ _) (fun _ _ ↦ ?_) ?_
  · refine CostLE.seq (CostLE.sumcheckP _ _ _) (fun _ _ ↦ ?_) ?_
    · refine CostLE.seq (CostLE.readPackedP _) (fun _ _ ↦ ?_) ?_
      · exact CostLE.seq (CostLE.require _) (fun _ _ ↦ trivial) (Nat.zero_le _)
      · simp only [List.length_replicate, hq, hv, linkSufCost, hk] at hX ⊢; omega
    · simp only [List.length_replicate, hq, linkSufCost, hk] at hX ⊢; omega
  · simp only [List.length_replicate, linkSufCost, hk] at hX ⊢; omega

/-! ## `KECCAK`'s reduction, ring switching, the public input, the memory term -/

/-- The stream one layer of the Keccak reduction reads, at a point of `L` coordinates. -/
def keccakLayerStream (L : ℕ) : ℕ := productBits + 1 + L * 5 + keccakLocalBits * 6 + 3 + 1

theorem verifyKeccakLayerP (logSteps step : ℕ) (claim : KeccakClaim) :
    CostLE (verifyKeccakLayer logSteps step claim) (keccakLayerStream claim.point.length) := by
  unfold verifyKeccakLayer
  refine CostLE.seq (CostLE.readN _) (fun _ _ ↦ ?_) (by unfold keccakLayerStream; omega)
  refine CostLE.seq (CostLE.require _) (fun _ _ ↦ ?_) (Nat.zero_le _)
  refine CostLE.seq (CostLE.grindP _) (fun _ _ ↦ ?_) (by unfold keccakLayerStream; omega)
  refine CostLE.seq CostLE.sampleE (fun _ _ ↦ ?_) (Nat.zero_le _)
  refine CostLE.seq (CostLE.sumcheckP 3 _ _) (fun r _ ↦ ?_) ?_
  · obtain ⟨point, value⟩ := r
    refine CostLE.seq (CostLE.sumcheckP 4 _ _) (fun r _ ↦ ?_) ?_
    · obtain ⟨localPoint, value⟩ := r
      refine CostLE.seq (CostLE.readN 3) (fun _ _ ↦ ?_) ?_
      · exact CostLE.seq (CostLE.require _) (fun _ _ ↦ CostLE.seq (CostLE.grindP _)
          (fun _ _ ↦ CostLE.seq CostLE.sampleE (fun _ _ ↦ trivial) (Nat.zero_le _)) (by
            simp only [List.length_map, List.length_replicate, keccakLayerStream]; omega))
          (Nat.zero_le _)
      · simp only [List.length_map, List.length_replicate, keccakLayerStream]; omega
    · simp only [List.length_map, List.length_replicate, keccakLayerStream]; omega
  · simp only [List.length_map, keccakLayerStream]; omega

theorem verifyKeccakLayer_point {logSteps step : ℕ} {claim c : KeccakClaim}
    (h : VerifierProgram.ReturnsAny (verifyKeccakLayer logSteps step claim) c) :
    c.point.length = claim.point.length := by
  unfold verifyKeccakLayer at h
  obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
  obtain ⟨⟨point, value⟩, hp, h⟩ := VerifierProgram.returnsAny_bind h
  obtain ⟨⟨_, _⟩, -, h⟩ := VerifierProgram.returnsAny_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returnsAny_bind h
  rw [VerifierProgram.returnsAny_ret h]
  have := returnsAny_sumcheck hp
  simpa using this

theorem keccakLayersP (logSteps : ℕ) : ∀ (steps : List ℕ) (claim : KeccakClaim),
    CostLE (keccakLayers logSteps steps claim)
      (steps.length * keccakLayerStream claim.point.length)
  | [], _ => trivial
  | s :: ss, claim => by
    refine CostLE.seq (verifyKeccakLayerP logSteps s claim) (fun c hc ↦ ?_) ?_
    · rw [show (s :: ss).length * keccakLayerStream claim.point.length -
        keccakLayerStream claim.point.length = ss.length * keccakLayerStream c.point.length by
        rw [verifyKeccakLayer_point hc, List.length_cons, Nat.succ_mul, Nat.add_sub_cancel]]
      exact keccakLayersP logSteps ss c
    · simp only [List.length_cons, Nat.succ_mul]; omega

theorem keccakOpenP (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    CostLE (keccakOpen logSteps claim first count value) (qkeccakSlotBits * 5) := by
  unfold keccakOpen
  exact CostLE.seq (CostLE.sumcheckP 3 _ _) (fun _ _ ↦ trivial)
    (by simp only [List.length_replicate]; omega)

/-- The stream `KECCAK`'s reduction reads, at most, its layers at a point of at most `L`
coordinates. -/
def keccakStreamOf (L : ℕ) : ℕ :=
  1 + 1 + keccakDepth * keccakLayerStream L + (qkeccakSlotBits * 5 + 1) + 4 * 5 +
    qkeccakSlotBits * 5 + kBits

/-- The stream `KECCAK`'s reduction reads, at most, at an instance point of at most `30`
coordinates. -/
def keccakStream : ℕ := keccakStreamOf 27

theorem verifyKeccakP' (logSteps L : ℕ) (inst output : List E) (hl : logSteps ≤ L + 3) :
    CostLE (verifyKeccak logSteps inst output) (keccakStreamOf L) := by
  have h1 : 1 < keccakSegments := by decide
  have hseg : keccakSegmentBits = 1 := by decide
  unfold verifyKeccak
  simp only [h1, ↓reduceIte]
  refine CostLE.seq (CostLE.require _) (fun _ hreq ↦ ?_) (Nat.zero_le _)
  have hreq := VerifierProgram.returnsAny_require hreq
  refine CostLE.seq (CostLE.grindP _) (fun _ _ ↦ ?_) (by unfold keccakStreamOf; omega)
  refine CostLE.seq (CostLE.sampleN _) (fun segment hs ↦ ?_) (Nat.zero_le _)
  have hs := returns_sampleN hs
  refine CostLE.seq (CostLE.sampleN _) (fun lanePoint _ ↦ ?_) (Nat.zero_le _)
  refine CostLE.seq CostLE.readE (fun committed _ ↦ ?_) (by unfold keccakStreamOf; omega)
  have hL : (keccakFirstClaim inst segment lanePoint output committed).point.length ≤ L := by
    simp only [keccakFirstClaim, List.length_append, List.length_drop, hs, hseg]
    omega
  have hlay : keccakDepth * keccakLayerStream
      (keccakFirstClaim inst segment lanePoint output committed).point.length ≤
        keccakDepth * keccakLayerStream L := by
    refine Nat.mul_le_mul_left _ ?_
    unfold keccakLayerStream
    omega
  have hstream : keccakStreamOf L = 2 + keccakDepth * keccakLayerStream L + 31 + 20 + 30 + 64 := by
    unfold keccakStreamOf; rw [show qkeccakSlotBits = 6 by decide, show kBits = 64 from rfl]
  have hq6 : qkeccakSlotBits = 6 := by decide
  have ho : ∀ (c : KeccakClaim) (f c' : ℕ) (v : E), CostLE (keccakOpen logSteps c f c' v) 30 :=
    fun c f c' v ↦ by have := keccakOpenP logSteps c f c' v; rwa [hq6] at this
  refine CostLE.seq (keccakLayersP logSteps (List.range keccakDepth) _) (fun claim _ ↦ ?_) ?_
  · refine CostLE.seq (ho _ _ _ _) (fun _ _ ↦ ?_) ?_
    · refine CostLE.seq CostLE.readE (fun _ _ ↦ ?_) ?_
      · refine CostLE.seq (CostLE.require _) (fun _ _ ↦ ?_) (Nat.zero_le _)
        refine CostLE.seq (CostLE.pure' _ 0) (fun _ _ ↦ ?_) (Nat.zero_le _)
        refine CostLE.seq (CostLE.sumcheckP 3 _ _) (fun _ _ ↦ ?_) ?_
        · refine CostLE.seq (ho _ _ _ _) (fun _ _ ↦ ?_) ?_
          · exact CostLE.seq (CostLE.readN _) (fun _ _ ↦ CostLE.seq (CostLE.require _)
              (fun _ _ ↦ trivial) (Nat.zero_le _)) (by
                rw [List.length_range, hstream] at *
                rw [List.length_replicate, show kBits = 64 from rfl]; omega)
          · rw [List.length_range, hstream] at *; rw [List.length_replicate]; omega
        · rw [List.length_range, hstream] at *; rw [List.length_replicate]; omega
      · rw [List.length_range, hstream] at *; omega
    · rw [List.length_range, hstream] at *; omega
  · rw [List.length_range, hstream]
    omega

theorem verifyKeccakP (logSteps : ℕ) (inst output : List E) (hl : logSteps ≤ 30) :
    CostLE (verifyKeccak logSteps inst output) keccakStream :=
  verifyKeccakP' logSteps 27 inst output (by omega)

theorem keccakValidityP {layout : Layout} (hs : SizesOK layout) (link : LinkEnd) :
    CostLE (keccakValidity layout link) keccakStream := by
  have hl : layout.tableLogHeights.getD opKeccak 0 ≤ 30 := by
    rw [List.getD_eq_getElem?_getD]
    rcases he : layout.tableLogHeights[opKeccak]? with _ | x
    · simp
    · exact hs.heights_le x (List.mem_of_getElem? he)
  unfold keccakValidity
  exact CostLE.seq (CostLE.liftOptionP _) (fun _ _ ↦ verifyKeccakP _ _ _ hl) (Nat.zero_le _)

theorem keccakValidityP' (layout : Layout) (link : LinkEnd) :
    CostLE (keccakValidity layout link)
      (keccakStreamOf (layout.tableLogHeights.getD opKeccak 0)) := by
  unfold keccakValidity
  exact CostLE.seq (CostLE.liftOptionP _) (fun _ _ ↦ verifyKeccakP' _ _ _ _ (by omega))
    (Nat.zero_le _)

theorem ringSwitchP (claims : List RingClaim) : CostLE (ringSwitch claims) 1 := by
  unfold ringSwitch
  exact CostLE.seq (CostLE.grindP _) (fun _ _ ↦ CostLE.seq (CostLE.samplePackedP _)
    (fun _ _ ↦ trivial) (Nat.zero_le _)) le_rfl

theorem bindPublicInputP (layout : Layout) (publicInput : Digest) :
    CostLE (bindPublicInput layout publicInput) 0 := by
  unfold bindPublicInput
  exact CostLE.seq CostLE.sampleE (fun _ _ ↦ CostLE.seq (CostLE.liftOptionP _)
    (fun _ _ ↦ trivial) le_rfl) le_rfl

theorem memoryTermClaimP (layout : Layout) (link : LinkEnd) :
    CostLE (memoryTermClaim layout link) 0 := by
  unfold memoryTermClaim
  exact CostLE.seq (CostLE.liftOptionP _) (fun _ _ ↦ CostLE.seq (CostLE.liftOptionP _)
    (fun _ _ ↦ trivial) le_rfl) le_rfl

end LeanVM.Wire

end
