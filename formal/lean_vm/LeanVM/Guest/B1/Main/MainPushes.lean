/-
  LeanVM.Guest.B1.Main.MainPushes

  On an honest run, `main`'s entries (`mainOwnPops`) are `Hints.honestPushes`', stream by stream, given its callees' entries against their segments.
-/

module

public import LeanVM.Guest.B1.Main.MainPops
public import LeanVM.Guest.B1.Main.RawPushes
public import LeanVM.Guest.B1.Main.MainHonestFit

/-!
# `main`'s entries against the honest pushes

* `levelHints_names`, `childSeg_names`: the children's segment pops no LeanDA stream;
* `main_pops_honest`: `main`'s entries at the honest oracle, its callees' agreeing with their segments of `honestPushes`, agree with `honestPushes` stream by stream.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Node

@[expose] public section

/-- A push on both sides keeps them agreeing. -/
theorem SameStreams.cons {a b : List Pop} (x : Pop) (e : SameStreams a b) : SameStreams (x :: a) (x :: b) :=
  (SameStreams.refl [x]).append e

/-! ## Stream names -/

/-- LeanDA's streams. -/
def daNames : List String := ["da_challenge", "da_n_blobs", "da_symbols"]

theorem daHints_names (c : DaClaim) (w : Da.MatrixWitness) : ∀ p ∈ Hints.daHints c w, p.1 ∈ daNames := by
  intro p hp
  rw [Hints.daHints, List.cons_append, List.cons_append, List.nil_append] at hp
  rcases List.mem_cons.mp hp with rfl | hp
  · simp [daNames]
  rcases List.mem_cons.mp hp with rfl | hp
  · simp [daNames]
  obtain ⟨j, -, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨row, -, rfl⟩ := List.mem_map.mp hp
  simp [daNames]

/-- The children's streams. -/
def childNames : List String :=
  ["child_meta", "signers_split", "child_mono", "child_claim_gap", "child_claim_index", "child_defer", "child_da",
    "stream", "zc_tau_max", "table_logs", "col_group_order", "block_group_order", "merkle_leaf_rows",
    "merkle_children", "merkle_caps", "merkle_cap_active"]

theorem levelHints_names (first : Bool) (depth count : ℕ) (phase : List Opening) :
    ∀ p ∈ Hints.levelHints first depth count phase, p.1 ∈ childNames := by
  intro p hp
  simp only [Hints.levelHints, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ⟨_, _, rfl | rfl⟩ | rfl | rfl <;> simp [childNames]

theorem merkleHints_names : ∀ (first : Bool) (qs : List (ℕ × List ℕ)) (phases : List (List Opening)),
    ∀ p ∈ Hints.merkleHints first qs phases, p.1 ∈ childNames
  | first, (d, ps) :: rest, ph :: phs, p, hp => by
    rw [Hints.merkleHints] at hp
    rcases List.mem_append.mp hp with hp | hp
    · exact levelHints_names first d ps.length ph p hp
    · exact merkleHints_names false rest phs p hp
  | _, [], _, p, hp => by unfold Hints.merkleHints at hp; simp at hp
  | _, _ :: _, [], p, hp => by unfold Hints.merkleHints at hp; simp at hp

theorem childHints_names (bytecode : List K) (seed : Digest) (c : Child) :
    ∀ p ∈ Hints.childHints bytecode seed c, p.1 ∈ childNames := by
  intro p hp
  unfold Hints.childHints at hp
  split at hp
  · simp at hp
  · have hq := merkleHints_names true (Hints.childQueries bytecode seed c) c.proof.openings
    dsimp only at hp
    rcases List.mem_append.mp hp with hp | hp
    · revert hp
      revert p
      simp only [childNames] at hq ⊢
      simp
      intro a b h _
      simpa using hq (a, b) h
    · exact hq p hp

theorem childSlotPushes_names (offsets : List ℕ) : ∀ p ∈ Hints.childSlotPushes offsets, p.1 ∈ childNames := by
  intro p hp
  unfold Hints.childSlotPushes at hp
  split at hp
  · simp at hp
  · simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp [childNames]
    split at hp <;> simp only [List.mem_cons, List.mem_map] at hp <;>
      rcases hp with rfl | ⟨_, _, rfl⟩ <;> simp [childNames]

/-- **The children's segment of `honestPushes`.** -/
def childSeg (bytecode : List K) (seed : Digest) (s : NodeStatement) (w : NodeWitness) : List Pop :=
  ((w.children.zip (xPlan s w).childSlots).zip (sPlan s w).childSlots).flatMap (fun ((c, xs), ss) ↦
    ("child_meta", [Hints.count c.statement.claims.xmss.length, Hints.count c.statement.claims.sphincs.length]) ::
      Hints.childSlotPushes xs ++ Hints.childSlotPushes ss ++
      [("child_defer", c.statement.deferredClaim.cells), ("child_da", Hints.digestCells c.statement.claims.daDigest)] ++
      Hints.childHints bytecode seed c)

theorem childSeg_names (bytecode : List K) (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    ∀ p ∈ childSeg bytecode seed s w, p.1 ∈ childNames := by
  intro p hp
  obtain ⟨⟨⟨c, xs⟩, ss⟩, -, hp⟩ := List.mem_flatMap.mp hp
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · rcases List.mem_cons.mp hp with rfl | hp
        · simp [childNames]
        · exact childSlotPushes_names xs p hp
      · exact childSlotPushes_names ss p hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp [childNames]
  · exact childHints_names bytecode seed c p hp

theorem not_da_of_child {x : String} (h : x ∈ childNames) : x ∉ daNames := by
  simp only [childNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [daNames]

/-! ## `main`'s entries -/

theorem gen_pow_count {n : ℕ} (h : n < 2 ^ 64) : gen ^ n = Hints.count n :=
  (gen_pow_eq_ofK n).trans (Sig.count_eq h).symm

variable {bytecode : List K} {seed : Digest} {s : NodeStatement} {w : NodeWitness}

/-- The batching's or the leaf's segment of `honestPushes`. -/
def leafSeg (s : NodeStatement) (w : NodeWitness) : List Pop :=
  if w.children = [] then [("leaf_defer", [s.deferredClaim.bytecodeValue])] else Hints.batchPushes w.batchingHints

/-- The DA check's segment of `honestPushes`. -/
def daSeg (w : NodeWitness) : List Pop := (w.daMatrix.map fun c ↦ Hints.daHints c.1 c.2).getD []

theorem leafSeg_names : ∀ p ∈ leafSeg s w, p.1 ∉ daNames ∧ p.1 ≠ "da_pick" := by
  intro p hp
  unfold leafSeg at hp
  split at hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; subst hp; simp [daNames]
  · simp only [Hints.batchPushes, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [daNames]

theorem daSeg_names : ∀ p ∈ daSeg w, p.1 ∈ daNames := by
  intro p hp
  unfold daSeg at hp
  cases hm : w.daMatrix with
  | none => rw [hm] at hp; simp at hp
  | some c => rw [hm] at hp; exact daHints_names c.1 c.2 p hp

/-- **The LeanDA segment and `da_pick` move past the children's and the batching's**, stream by stream. -/
theorem tail_sameStreams :
    SameStreams (daSeg w ++ (childSeg bytecode seed s w ++ (("da_pick", [Hints.count (Hints.daPick s w)]) :: leafSeg s w)))
      (childSeg bytecode seed s w ++ (leafSeg s w ++ (daSeg w ++ [("da_pick", [Hints.count (Hints.daPick s w)])]))) := by
  have hda : ∀ p ∈ daSeg w, p.1 ≠ "da_pick" := fun p hp h => by
    have := daSeg_names p hp; rw [h] at this; simp [daNames] at this
  refine (sameStreams_append_comm fun p hp q hq => ?_).trans ?_
  · have hp' := daSeg_names p hp
    rcases List.mem_append.mp hq with hq | hq
    · exact fun e => not_da_of_child (childSeg_names bytecode seed s w q hq) (e ▸ hp')
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact hda p hp
      · exact fun e => (leafSeg_names q hq).1 (e ▸ hp')
  · rw [List.append_assoc]
    refine (SameStreams.refl _).append ?_
    rw [List.cons_append, ← List.singleton_append]
    refine (sameStreams_append_comm fun p hp q hq => ?_).trans (SameStreams.of_eq (by rw [List.append_assoc]))
    rw [List.mem_singleton] at hp
    subst hp
    rcases List.mem_append.mp hq with hq | hq
    · exact fun e => (leafSeg_names q hq).2 e.symm
    · exact fun e => hda q hq e.symm

/-- **`main`'s entries are the honest pushes**, stream by stream, its callees' agreeing with their segments: the claim
lists', the duplicates', the raw signatures', the DA check's, the children's, the batching's; `exponent_tables` and
`statement_digest` popping nothing. -/
theorem main_pops_honest (fs : String → ℕ) (fp : ℕ) (hl : GuestLimits s w)
    {pe px ps p0 p1 p2 p3 pd p5 pa pst : List Pop} (he : pe = []) (hst : pst = [])
    (hx : SameStreams px (Hints.listPushes "claims"
      (s.claims.xmss.map fun c ↦ Hints.claimCells c.1.root c.1.parameter c.2)))
    (hs : SameStreams ps (Hints.listPushes "claims"
      (s.claims.sphincs.map fun c ↦ Hints.claimCells c.1.publicSeed c.1.root c.2)))
    (h0 : SameStreams p0 ((xPlan s w).duplicates.map fun c ↦ ("dup_claims", Hints.claimCells c.1.root c.1.parameter c.2)))
    (h1 : SameStreams p1
      ((sPlan s w).duplicates.map fun c ↦ ("dup_claims", Hints.claimCells c.1.publicSeed c.1.root c.2)))
    (h2 : SameStreams p2 ((w.xmssSignatures.zip (xPlan s w).directSlots).flatMap
      (fun (c, slot) ↦ ("raw_index", [Hints.count slot]) :: Hints.xmssHints c.1.1 c.1.2 c.2)))
    (h3 : SameStreams p3 ((w.sphincsSignatures.zip (sPlan s w).directSlots).flatMap
      (fun (c, slot) ↦ ("sp_raw_index", [Hints.count slot]) :: Hints.sphincsHints c.1.1 c.1.2 c.2)))
    (hd : w.daMatrix.isSome → SameStreams pd (daSeg w))
    (h5 : SameStreams p5 (childSeg bytecode seed s w))
    (ha : w.children ≠ [] → SameStreams pa (Hints.batchPushes w.batchingHints)) :
    SameStreams (mainOwnPops (hm fs fp seed s w) pe px ps p0 p1 p2 p3 pd p5 pa pst)
      (Hints.honestPushes bytecode seed s w) := by
  have hb : MainBounds (2 ^ 23) (hm fs fp seed s w) := hData_bounds hl fs fp
  have hmeta : (hm fs fp seed s w).cnt.map (gen ^ ·) = [Hints.count s.claims.xmss.length,
      Hints.count (xPlan s w).duplicates.length, Hints.count w.xmssSignatures.length, Hints.count s.claims.sphincs.length,
      Hints.count (sPlan s w).duplicates.length, Hints.count w.sphincsSignatures.length,
      Hints.count w.children.length, Hints.count ((w.daMatrix.map fun _ ↦ 1).getD 0)] := by
    have := hb.nc
    have := hb.nd
    simp only [MainIn.cnt, List.map_cons, List.map_nil]
    rw [gen_pow_count (by have := hb.lx; omega), gen_pow_count (by have := hb.xd; omega),
      gen_pow_count (by have := hb.rx; omega), gen_pow_count (by have := hb.ls; omega),
      gen_pow_count (by have := hb.sd; omega), gen_pow_count (by have := hb.rs; omega),
      gen_pow_count (by omega), gen_pow_count (by omega)]
    rfl
  have hpick : gen ^ (hm fs fp seed s w).pick = Hints.count (Hints.daPick s w) := by
    have := hb.pick
    have := hb.nc
    exact gen_pow_count (by omega)
  have hPD : SameStreams (if (hm fs fp seed s w).nd = 1 then pd else []) (daSeg w) := by
    show SameStreams (if (w.daMatrix.map fun _ ↦ 1).getD 0 = 1 then pd else []) _
    by_cases hs : w.daMatrix.isSome
    · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
      have e : (w.daMatrix.map fun _ ↦ 1).getD 0 = 1 := by rw [hc]; rfl
      simp only [e, ↓reduceIte]
      exact hd hs
    · have hn : w.daMatrix = none := Option.not_isSome_iff_eq_none.mp hs
      simp only [zero_ne_one, ↓reduceIte, daSeg, hn, Option.map_none, Option.getD_none]
      exact SameStreams.refl _
  have hLB : SameStreams (if (hm fs fp seed s w).nc = 0 then [("leaf_defer", [(hm fs fp seed s w).leaf])] else pa)
      (leafSeg s w) := by
    show SameStreams (if w.children.length = 0 then [("leaf_defer", [s.deferredClaim.bytecodeValue])] else pa) _
    unfold leafSeg
    by_cases hc : w.children = []
    · simp only [hc, List.length_nil, ↓reduceIte]; exact SameStreams.refl _
    · rw [ite_neg' (fun h => hc (List.eq_nil_of_length_eq_zero h)), ite_neg' hc]; exact ha hc
  have hH : Hints.honestPushes bytecode seed s w = [("meta", [Hints.count s.claims.xmss.length,
      Hints.count (xPlan s w).duplicates.length, Hints.count w.xmssSignatures.length, Hints.count s.claims.sphincs.length,
      Hints.count (sPlan s w).duplicates.length, Hints.count w.sphincsSignatures.length,
      Hints.count w.children.length, Hints.count ((w.daMatrix.map fun _ ↦ 1).getD 0)]),
      ("fs_seed", Hints.digestCells seed)] ++
    Hints.listPushes "claims" (s.claims.xmss.map fun c ↦ Hints.claimCells c.1.root c.1.parameter c.2) ++
    Hints.listPushes "claims" (s.claims.sphincs.map fun c ↦ Hints.claimCells c.1.publicSeed c.1.root c.2) ++
    ((xPlan s w).duplicates.map (fun c ↦ Hints.claimCells c.1.root c.1.parameter c.2) ++
      (sPlan s w).duplicates.map (fun c ↦ Hints.claimCells c.1.publicSeed c.1.root c.2)).map ("dup_claims", ·) ++
    (w.xmssSignatures.zip (xPlan s w).directSlots).flatMap
      (fun (c, slot) ↦ ("raw_index", [Hints.count slot]) :: Hints.xmssHints c.1.1 c.1.2 c.2) ++
    (w.sphincsSignatures.zip (sPlan s w).directSlots).flatMap
      (fun (c, slot) ↦ ("sp_raw_index", [Hints.count slot]) :: Hints.sphincsHints c.1.1 c.1.2 c.2) ++
    childSeg bytecode seed s w ++ leafSeg s w ++ daSeg w ++ [("da_pick", [Hints.count (Hints.daPick s w)])] := by
    rfl
  rw [hH, mainOwnPops, he, hst, List.nil_append, List.append_nil, hmeta, hpick]
  simp only [List.map_append, List.map_map, List.append_assoc, List.cons_append, List.nil_append]
  refine SameStreams.cons _ (SameStreams.cons _ ?_)
  refine (hx.append (hs.append (h0.append (h1.append (h2.append (h3.append
    (hPD.append (h5.append (SameStreams.cons _ hLB))))))))).trans ?_
  refine (SameStreams.refl _).append ((SameStreams.refl _).append ((SameStreams.refl _).append
    ((SameStreams.refl _).append ((SameStreams.refl _).append ((SameStreams.refl _).append ?_)))))
  exact tail_sameStreams

/-- **`main`'s node on an honest run pops the honest pushes**, stream by stream: at a valuation
with `main`'s honest values, its callees popping entries agreeing with their segments (`main_pops_honest`). -/
theorem main_tree_pops_honest (fs : String → ℕ) (fp : ℕ) (hl : GuestLimits s w) {rd : Reader} {σ : Val}
    {bufs : List ℕ} {ks : List Tree} {pe px ps p0 p1 p2 p3 pd p5 pa pst : List Pop}
    (hv : MVals rd σ (hm fs fp seed s w))
    (hk : Tree.popsKids coreProgram rd ks = mainKidPops (hm fs fp seed s w) pe px ps p0 p1 p2 p3 pd p5 pa pst)
    (he : pe = []) (hst : pst = [])
    (hx : SameStreams px (Hints.listPushes "claims"
      (s.claims.xmss.map fun c ↦ Hints.claimCells c.1.root c.1.parameter c.2)))
    (hs : SameStreams ps (Hints.listPushes "claims"
      (s.claims.sphincs.map fun c ↦ Hints.claimCells c.1.publicSeed c.1.root c.2)))
    (h0 : SameStreams p0 ((xPlan s w).duplicates.map fun c ↦ ("dup_claims", Hints.claimCells c.1.root c.1.parameter c.2)))
    (h1 : SameStreams p1
      ((sPlan s w).duplicates.map fun c ↦ ("dup_claims", Hints.claimCells c.1.publicSeed c.1.root c.2)))
    (h2 : SameStreams p2 ((w.xmssSignatures.zip (xPlan s w).directSlots).flatMap
      (fun (c, slot) ↦ ("raw_index", [Hints.count slot]) :: Hints.xmssHints c.1.1 c.1.2 c.2)))
    (h3 : SameStreams p3 ((w.sphincsSignatures.zip (sPlan s w).directSlots).flatMap
      (fun (c, slot) ↦ ("sp_raw_index", [Hints.count slot]) :: Hints.sphincsHints c.1.1 c.1.2 c.2)))
    (hd : w.daMatrix.isSome → SameStreams pd (daSeg w))
    (h5 : SameStreams p5 (childSeg bytecode seed s w))
    (ha : w.children ≠ [] → SameStreams pa (Hints.batchPushes w.batchingHints)) :
    SameStreams ((Memory.Tree.node "main" σ bufs ks).pops coreProgram rd)
      (Hints.honestPushes bytecode seed s w) := by
  have hb : MainBounds (2 ^ 23) (hm fs fp seed s w) := hData_bounds hl fs fp
  rw [main_pops hb.nd hb.nc hv hk]
  exact main_pops_honest fs fp hl he hst hx hs h0 h1 h2 h3 hd h5 ha

end
end LeanVM.Guest.B1.Main
