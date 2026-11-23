/-
  LeanVM.Guest.Child.Collision

  A query step of the deferring verifier's run whose openings disagree at a node of their tree
  exhibits a Keccak-256 collision between the bytes two of its openings' climbs hash.
-/

module

public import LeanVM.Guest.Child.Merkle
public import LeanVM.Guest.Child.Accepted
public import LeanVM.Guest.Child.Range
public import LeanVM.Guest.Limits

/-!
# Disagreeing openings give a Keccak-256 collision

`capsAgree_or_collide`: at every query step of the deferring verifier's run on a child's proof,
the step's openings agree wherever they meet (`Limits.OpeningsAgree`), or the proof's openings
exhibit a Keccak-256 collision (`OpeningsCollide`). So a node `NodeRelation` admits has children the
guest program accepts, or a child's proof exhibits one (`acceptableChildren_or_collide`).

A query step opens one phase of the proof against a root of the step's height, at positions below
`2^height` (`queryStepsOf_opened`, from `inRange_deferringProgram`), so each of its openings climbs
to that root (`openPhase_climbs`). Two openings giving one heap node different digests give it at
one level (`givesNode_cases`, `heapIndex_level`), as one of the two digests their climbs hash
there (`climbPair`). Climbing on, the bytes they hash differ at each level until their digests
agree, which they do at the root at the latest: there the bytes differ and the digests agree
(`collide_of_pair_ne`).
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Node
open LeanVM.Guest.Completeness LeanVM.Guest.B1.VerifySub

@[expose] public section

/-! ## The deferring program opens in range -/

theorem noCommit_verifyBusBalance_claimed (c : BytecodeClaim) (layout : Layout) :
    NoCommit (verifyBusBalance (claimedBytecodeValue c) layout) := by
  rw [verifyBusBalance_split]
  exact NoCommit.bind (noCommit_require _) fun _ ↦ NoCommit.bind (noCommit_grind _) fun _ ↦
    NoCommit.bind (noCommit_sampleN _) fun _ ↦ NoCommit.bind noCommit_sampleE fun _ ↦
    NoCommit.bind (noCommit_gkrPhase _) fun _ ↦ noCommit_busRest c _ _ _ _ _

/-- **The deferring verifier program opens in range**, from no commitment. -/
theorem inRange_deferringProgram (c : BytecodeClaim) (bytecode : List K) (publicInput : Digest) :
    InRange (deferringVerifierProgram c bytecode publicInput) [] fun _ _ ↦ True := by
  rw [deferredProgram_eq]
  exact InRange.bind (Q := fun _ _ ↦ True)
    (inRange_verifyExecutionClaims (noCommit_verifyBusBalance_claimed c) _ _) fun _ _ _ ↦ trivial

/-! ## A query step opens a phase -/

/-- **Every query step opens a phase of the state's openings** against a root of the step's
height, at positions below `2^` its height, along a program in range from the state's roots'
heights. -/
theorem queryStepsOf_opened {α : Type} {Q : α → List ℕ → Prop} :
    ∀ (p : VerifierProgram α) (hs : List ℕ) (state : VerifierProgramState),
      InRange p hs Q → ∀ step ∈ Limits.queryStepsOf p state, state.roots.map (·.2.1) = hs →
      ∃ phase ∈ state.openings, ∃ root width ps rows,
        openPhase (m := Id) keccakF1600 root step.1 width ps phase = some rows ∧
        (∀ q ∈ ps, q < 2 ^ step.1) ∧ step.2 = ps.zip phase
  | .ret _, _, _, _, _, h, _ => by simp [Limits.queryStepsOf] at h
  | .fail, _, _, _, _, h, _ => by simp [Limits.queryStepsOf] at h
  | .read k, hs, ⟨⟨S0, P0, g⟩, stream, os, R⟩, hir, step, h, hR => by
    match stream, g, h with
    | [], _, h => simp [Limits.queryStepsOf] at h
    | _ :: _, some _, h => simp [Limits.queryStepsOf] at h
    | x :: xs, none, h =>
      have h' := queryStepsOf_opened (k x) hs _ (hir x) step h hR
      exact h'
  | .sample k, hs, state, hir, step, h, hR => by
    have e : Limits.queryStepsOf (VerifierProgram.sample k) state =
        Limits.queryStepsOf (k (Id.run (squeeze keccakF1600 state.sponge)).1)
          { state with sponge := (Id.run (squeeze keccakF1600 state.sponge)).2 } := rfl
    rw [e] at h
    have h' := queryStepsOf_opened _ hs _ (hir _) step h hR
    exact h'
  | .grind bits k, hs, ⟨⟨S0, P0, g⟩, stream, os, R⟩, hir, step, h, hR => by
    match stream, g, h with
    | [], _, h => simp [Limits.queryStepsOf] at h
    | _ :: _, some _, h => simp [Limits.queryStepsOf] at h
    | n :: xs, none, h =>
      simp only [Limits.queryStepsOf] at h
      generalize absorbNonce (m := Id) keccakF1600 ⟨S0, P0, none⟩ n = N at h
      obtain ⟨pw, sp'⟩ := N
      change step ∈ (if powOk bits pw = true then _ else _) at h
      split at h
      · have h' := queryStepsOf_opened k hs _ hir step h hR
        exact h'
      · simp at h
  | .commit height width k, hs, ⟨⟨S0, P0, g⟩, stream, os, R⟩, hir, step, h, hR => by
    match stream, g, h with
    | [], _, h => simp [Limits.queryStepsOf] at h
    | [_], _, h => simp [Limits.queryStepsOf] at h
    | _ :: _ :: _, some _, h => simp [Limits.queryStepsOf] at h
    | x0 :: x1 :: xs, none, h =>
      have h' := queryStepsOf_opened k (hs ++ [height]) _ hir step h (by simp [hR])
      exact h'
  | .query i ps k, hs, ⟨sp, stream, os, R⟩, hir, step, h, hR => by
    simp only [Limits.queryStepsOf] at h
    cases hr : R[i]? with
    | none => simp [hr] at h
    | some t =>
      obtain ⟨root, height, width⟩ := t
      cases os with
      | nil => simp [hr] at h
      | cons phase rest =>
        simp only [hr] at h
        generalize ho : Id.run (openPhase (m := Id) keccakF1600 root height width ps phase) = o at h
        cases o with
        | none => simp at h
        | some rows =>
          simp only at h
          have hgi : hs.getD i 0 = height := by
            rw [← hR]
            simp [List.getD_eq_getElem?_getD, hr]
          rcases List.mem_cons.mp h with rfl | h
          · refine ⟨phase, List.mem_cons_self .., root, width, ps, rows, ho, fun q hq ↦ ?_, rfl⟩
            rw [← hgi]
            exact hir.1 q hq
          · obtain ⟨phase', hp, h'⟩ := queryStepsOf_opened (k rows) hs _ (hir.2 rows) step h hR
            exact ⟨phase', List.mem_cons_of_mem _ hp, h'⟩

/-- An opening the verifier accepts climbs to the root. -/
theorem climbTo_of_openOne {root : Digest} {height width q : ℕ} {o : Opening}
    (h : Id.run (openOne (m := Id) keccakF1600 root height width q o) = true) :
    Limits.climbTo (merkleLeafDigest o.leaf) q o.path = root := by
  unfold openOne at h
  split at h
  · have h' : decide ((Limits.climbTo (merkleLeafDigest o.leaf) q o.path).toList = root.toList) =
        true := h
    exact Vector.toList_inj.mp (of_decide_eq_true h')
  · cases h

theorem openAll_climbs {root : Digest} {height width : ℕ} :
    ∀ (phase : List Opening) {x : List (List K) × List Opening},
      openAll (m := Id) keccakF1600 root height width (phase.map Opening.leafIndex) phase = some x →
      ∀ o ∈ phase, Limits.climbTo (merkleLeafDigest o.leaf) o.leafIndex o.path = root
  | [], _, _, o, ho => absurd ho List.not_mem_nil
  | o :: os, x, h, o', ho' => by
    have h' : (if Id.run (openOne (m := Id) keccakF1600 root height width o.leafIndex o) = true then
        (Id.run (openAll (m := Id) keccakF1600 root height width (os.map Opening.leafIndex) os)).map
          (fun r ↦ (o.leaf :: r.1, r.2))
        else none) = some x := h
    split at h'
    · rename_i hone
      obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.mp h'
      rcases List.mem_cons.mp ho' with rfl | ho'
      · exact climbTo_of_openOne hone
      · exact openAll_climbs os hy o' ho'
    · cases h'

/-- **An opened phase**: every path of the tree's height, the positions its openings', each opening
climbing to the root. -/
theorem openPhase_climbs {root : Digest} {height width : ℕ} {ps : List ℕ} {phase : List Opening}
    {rows : List (List K)}
    (h : openPhase (m := Id) keccakF1600 root height width ps phase = some rows) :
    (∀ o ∈ phase, o.path.length = height) ∧ ps = phase.map Opening.leafIndex ∧
      ∀ o ∈ phase, Limits.climbTo (merkleLeafDigest o.leaf) o.leafIndex o.path = root := by
  unfold openPhase at h
  split_ifs at h with hc
  refine ⟨fun o ho ↦ (hc.1 o ho).2, hc.2.symm, ?_⟩
  rw [← hc.2] at h
  generalize hx : openAll (m := Id) keccakF1600 root height width (phase.map Opening.leafIndex)
    phase = r at h
  cases r with
  | none => cases h
  | some x => exact openAll_climbs phase hx

/-! ## Climbs -/

/-- The two digests an opening's climb hashes at `level`, the left one first. -/
def climbPair (o : Opening) (level : ℕ) : Digest × Digest :=
  let node := Limits.climbTo (merkleLeafDigest o.leaf) o.leafIndex (o.path.take level)
  let sibling := o.path.getD level default
  if o.leafIndex / 2 ^ level % 2 = 0 then (node, sibling) else (sibling, node)

theorem climbInput_eq (o : Opening) (level : ℕ) :
    climbInput o level = digestBytes (climbPair o level).1 ++ digestBytes (climbPair o level).2 := by
  unfold climbInput climbPair
  split <;> rfl

theorem climbPair_eq_of_climbInput_eq {a b : Opening} {la lb : ℕ}
    (h : climbInput a la = climbInput b lb) : climbPair a la = climbPair b lb := by
  rw [climbInput_eq, climbInput_eq] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by rw [digestBytes_length, digestBytes_length])
  exact Prod.ext (digestBytes_injective h1) (digestBytes_injective h2)

theorem climbTo_nil (node : Digest) (q : ℕ) : Limits.climbTo node q [] = node := rfl

theorem climbTo_cons (node : Digest) (q : ℕ) (s : Digest) (ss : List Digest) :
    Limits.climbTo node q (s :: ss) = Limits.climbTo
      (keccak256 (if q % 2 = 0 then digestBytes node ++ digestBytes s
        else digestBytes s ++ digestBytes node)) (q / 2) ss := by
  by_cases h : q % 2 = 0 <;> (simp only [Limits.climbTo, climb, h, ↓reduceIte]) <;> rfl

/-- A climb's step at `level`. -/
theorem climbTo_take_succ : ∀ (node : Digest) (q : ℕ) (path : List Digest) (l : ℕ),
    l < path.length →
    Limits.climbTo node q (path.take (l + 1)) =
      keccak256 (if q / 2 ^ l % 2 = 0 then
        digestBytes (Limits.climbTo node q (path.take l)) ++ digestBytes (path.getD l default)
      else digestBytes (path.getD l default) ++ digestBytes (Limits.climbTo node q (path.take l)))
  | _, _, [], _, h => absurd h (Nat.not_lt_zero _)
  | node, q, s :: ss, 0, _ => by
    simp only [List.take_succ_cons, List.take_zero, climbTo_cons, climbTo_nil, pow_zero,
      Nat.div_one, List.getD_cons_zero]
  | node, q, s :: ss, l + 1, h => by
    rw [List.take_succ_cons, climbTo_cons,
      climbTo_take_succ _ (q / 2) ss l (by simp only [List.length_cons] at h; omega),
      List.take_succ_cons, climbTo_cons, List.getD_cons_succ, pow_succ', ←
      Nat.div_div_eq_div_mul]

/-- The node a climb reaches one level up is the digest of the bytes it hashes there. -/
theorem climbTo_succ_eq (o : Opening) {l : ℕ} (hl : l < o.path.length) :
    Limits.climbTo (merkleLeafDigest o.leaf) o.leafIndex (o.path.take (l + 1)) =
      keccak256 (climbInput o l) := by
  rw [climbTo_take_succ _ _ _ _ hl]
  rfl

/-! ## Heap indices -/

theorem div_pow_lt {D q l : ℕ} (hq : q < 2 ^ D) (hl : l ≤ D) : q / 2 ^ l < 2 ^ (D - l) := by
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.sub_add_cancel hl]
  exact hq

/-- A heap index fixes the level and the position. -/
theorem heapIndex_level {D q q' l l' : ℕ} (hq : q < 2 ^ D) (hq' : q' < 2 ^ D) (hl : l ≤ D)
    (hl' : l' ≤ D) (h : Limits.merkleHeapIndex D q l = Limits.merkleHeapIndex D q' l') :
    l = l' ∧ q / 2 ^ l = q' / 2 ^ l' := by
  obtain ⟨h1, h2⟩ := heap_inj (div_pow_lt hq hl) (div_pow_lt hq' hl') h
  exact ⟨by omega, h2⟩

/-- **The digest an opening gives a heap node** is the root's, at the root, or one of the two its
climb hashes at a level below, the left one at an even index. -/
theorem givesNode_cases {D : ℕ} {o : Opening} (hq : o.leafIndex < 2 ^ D) {N : ℕ} {d : Digest}
    (h : Limits.OpeningGivesNode D (o.leafIndex, o) N d) :
    (N = 1 ∧ d = Limits.climbTo (merkleLeafDigest o.leaf) o.leafIndex (o.path.take D)) ∨
      ∃ l < D, N / 2 = Limits.merkleHeapIndex D o.leafIndex (l + 1) ∧
        d = if N % 2 = 0 then (climbPair o l).1 else (climbPair o l).2 := by
  rcases h with ⟨l, hl, hN, hd⟩ | ⟨l, hl, hN, hd⟩
  · dsimp only at hN hd
    rcases Nat.lt_or_ge l D with hlt | hge
    · right
      have h2 : 2 ^ (D - l) = 2 * 2 ^ (D - (l + 1)) := by
        rw [← pow_succ']
        congr 1
        omega
      have hdiv : o.leafIndex / 2 ^ (l + 1) = o.leafIndex / 2 ^ l / 2 := by
        rw [pow_succ, Nat.div_div_eq_div_mul]
      have hN' : N = 2 * 2 ^ (D - (l + 1)) + o.leafIndex / 2 ^ l := by
        rw [hN, Limits.merkleHeapIndex, h2]
      refine ⟨l, hlt, ?_, ?_⟩
      · rw [Limits.merkleHeapIndex, hdiv, hN']
        generalize o.leafIndex / 2 ^ l = x
        generalize 2 ^ (D - (l + 1)) = e
        omega
      · have hmod : N % 2 = o.leafIndex / 2 ^ l % 2 := by
          rw [hN']
          generalize o.leafIndex / 2 ^ l = x
          generalize 2 ^ (D - (l + 1)) = e
          omega
        rw [hmod, hd]
        by_cases hc : o.leafIndex / 2 ^ l % 2 = 0 <;> simp [climbPair, hc]
    · left
      have hlD : l = D := by omega
      subst hlD
      refine ⟨?_, hd⟩
      rw [hN, Limits.merkleHeapIndex, Nat.sub_self, pow_zero, Nat.div_eq_of_lt hq]
  · dsimp only at hN hd
    right
    have hbit : (!o.leafIndex.testBit l).toNat = if o.leafIndex / 2 ^ l % 2 = 0 then 1 else 0 := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      split <;> simp_all
    have hN' : N = 2 * Limits.merkleHeapIndex D o.leafIndex (l + 1) +
        (if o.leafIndex / 2 ^ l % 2 = 0 then 1 else 0) := by
      rw [hN, Limits.siblingHeapIndex, hbit]
    refine ⟨l, hl, ?_, ?_⟩
    · rw [hN']
      split <;> omega
    · have hmod : N % 2 = if o.leafIndex / 2 ^ l % 2 = 0 then 1 else 0 := by
        rw [hN']
        split <;> omega
      rw [hmod, hd]
      by_cases hc : o.leafIndex / 2 ^ l % 2 = 0 <;> simp [climbPair, hc]

/-! ## The collision -/

/-- Two openings of `phase` whose climbs hash, at one level of their paths, different bytes to one
digest. -/
def ClimbsCollide (phase : List Opening) : Prop :=
  ∃ a ∈ phase, ∃ b ∈ phase, ∃ level < a.path.length, level < b.path.length ∧
    climbInput a level ≠ climbInput b level ∧
      keccak256 (climbInput a level) = keccak256 (climbInput b level)

section Phase

variable {D : ℕ} {root : Digest} {phase : List Opening}
  (hlen : ∀ o ∈ phase, o.path.length = D) (hq : ∀ o ∈ phase, o.leafIndex < 2 ^ D)
  (hroot : ∀ o ∈ phase, Limits.climbTo (merkleLeafDigest o.leaf) o.leafIndex o.path = root)
include hlen hroot

theorem climbTo_take_depth {o : Opening} (ho : o ∈ phase) :
    Limits.climbTo (merkleLeafDigest o.leaf) o.leafIndex (o.path.take D) = root := by
  rw [List.take_of_length_le (le_of_eq (hlen o ho)), hroot o ho]

/-- **Two openings climbing to one root from one node whose climbs hash different digests there
exhibit a collision**: at the first level above where their digests agree. -/
theorem collide_of_pair_ne {a b : Opening} (ha : a ∈ phase) (hb : b ∈ phase) :
    ∀ k l, l + k + 1 = D → a.leafIndex / 2 ^ (l + 1) = b.leafIndex / 2 ^ (l + 1) →
      climbPair a l ≠ climbPair b l → ClimbsCollide phase := by
  intro k
  induction k with
  | zero =>
    intro l hl _ hne
    by_cases hk : keccak256 (climbInput a l) = keccak256 (climbInput b l)
    · exact ⟨a, ha, b, hb, l, by rw [hlen a ha]; omega, by rw [hlen b hb]; omega,
        fun h ↦ hne (climbPair_eq_of_climbInput_eq h), hk⟩
    · exfalso
      apply hk
      rw [← climbTo_succ_eq a (by rw [hlen a ha]; omega),
        ← climbTo_succ_eq b (by rw [hlen b hb]; omega), show l + 1 = D by omega,
        climbTo_take_depth hlen hroot ha, climbTo_take_depth hlen hroot hb]
  | succ k ih =>
    intro l hl hdiv hne
    by_cases hk : keccak256 (climbInput a l) = keccak256 (climbInput b l)
    · exact ⟨a, ha, b, hb, l, by rw [hlen a ha]; omega, by rw [hlen b hb]; omega,
        fun h ↦ hne (climbPair_eq_of_climbInput_eq h), hk⟩
    · refine ih (l + 1) (by omega) ?_ ?_
      · rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hdiv]
      · intro hp
        apply hk
        rw [← climbTo_succ_eq a (by rw [hlen a ha]; omega),
          ← climbTo_succ_eq b (by rw [hlen b hb]; omega)]
        simp only [climbPair, hdiv] at hp
        by_cases hc : b.leafIndex / 2 ^ (l + 1) % 2 = 0 <;> simp [hc] at hp
        · exact hp.1
        · exact hp.2

include hq

/-- **Openings of one tree that disagree at a node exhibit a collision.** -/
theorem climbsCollide_of_not_agree
    (hd : ¬ Limits.OpeningsAgree D (phase.map fun o ↦ (o.leafIndex, o))) :
    ClimbsCollide phase := by
  unfold Limits.OpeningsAgree at hd
  push Not at hd
  obtain ⟨a', ha', b', hb', N, d, d', hda, hdb, hne⟩ := hd
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hb'
  rcases givesNode_cases (hq a ha) hda with ⟨hN, hd1⟩ | ⟨la, hla, hNa, hd1⟩ <;>
    rcases givesNode_cases (hq b hb) hdb with ⟨hN', hd2⟩ | ⟨lb, hlb, hNb, hd2⟩
  · exact absurd (hd1.trans ((climbTo_take_depth hlen hroot ha).trans
      (climbTo_take_depth hlen hroot hb).symm) |>.trans hd2.symm) hne
  · exfalso
    rw [hN, Limits.merkleHeapIndex] at hNb
    have := Nat.two_pow_pos (D - (lb + 1))
    generalize 2 ^ (D - (lb + 1)) = e at hNb this
    generalize b.leafIndex / 2 ^ (lb + 1) = x at hNb
    omega
  · exfalso
    rw [hN', Limits.merkleHeapIndex] at hNa
    have := Nat.two_pow_pos (D - (la + 1))
    generalize 2 ^ (D - (la + 1)) = e at hNa this
    generalize a.leafIndex / 2 ^ (la + 1) = x at hNa
    omega
  · obtain ⟨hl, hdiv⟩ := heapIndex_level (hq a ha) (hq b hb) (by omega) (by omega)
      (hNa.symm.trans hNb)
    have hll : la = lb := by omega
    subst hll
    refine collide_of_pair_ne hlen hroot ha hb (D - la - 1) la (by omega) hdiv fun hp ↦ hne ?_
    rw [hd1, hd2, hp]

end Phase

/-! ## A child's query steps -/

/-- **A query step whose openings disagree exhibits a Keccak-256 collision** in the child proof's
openings. -/
theorem openingsCollide_of_step {bytecode : List K} {seed : Digest} {child : Child}
    {step : ℕ × List (ℕ × Opening)}
    (hstep : step ∈ Limits.queryStepsOf
      (deferringVerifierProgram child.freshClaim bytecode (statementDigest seed child.statement))
        (Coverage.childVerifierStart seed child))
    (hd : ¬ Limits.OpeningsAgree step.1 step.2) : OpeningsCollide child.proof := by
  obtain ⟨phase, hphase, root, width, ps, rows, hop, hps, hstep2⟩ :=
    queryStepsOf_opened _ [] _ (inRange_deferringProgram _ _ _) step hstep rfl
  obtain ⟨hlen, rfl, hroot⟩ := openPhase_climbs hop
  rw [hstep2, ← List.map_prod_right_eq_zip] at hd
  obtain ⟨a, ha, b, hb, l, hla, hlb, hne, hk⟩ := climbsCollide_of_not_agree hlen
    (fun o ho ↦ hps _ (List.mem_map_of_mem ho)) hroot hd
  exact ⟨phase, hphase, a, ha, b, hb, l, hla, hlb, hne, hk⟩

/-- **A child's openings agree in the caps, or its proof exhibits a Keccak-256 collision**: at
every query step of its deferring verifier's run the step's openings agree wherever they meet, or
two openings of one phase hash different bytes to one digest. -/
theorem capsAgree_or_collide (bytecode : List K) (seed : Digest) (child : Child) :
    (∀ step ∈ Limits.queryStepsOf
      (deferringVerifierProgram child.freshClaim bytecode (statementDigest seed child.statement))
        (Coverage.childVerifierStart seed child),
      Limits.OpeningsAgree step.1 step.2) ∨ OpeningsCollide child.proof := by
  refine or_iff_not_imp_left.mpr fun h ↦ ?_
  push Not at h
  obtain ⟨step, hs, hd⟩ := h
  exact openingsCollide_of_step hs hd

/-- **The children of a node `NodeRelation` admits are children the guest program accepts, or one
of their proofs exhibits a Keccak-256 collision**, for a bytecode of `2^23` words. -/
theorem acceptableChildren_or_collide {bytecode : List K} (hbl : bytecode.length = 2 ^ 23)
    {seed : Digest} {statement : NodeStatement} {witness : NodeWitness}
    (hrel : NodeRelation bytecode seed statement witness) :
    ChildrenOk bytecode seed witness ∨ ∃ child ∈ witness.children, OpeningsCollide child.proof := by
  refine or_iff_not_imp_right.mpr fun hc child hchild ↦ ?_
  unfold NodeRelation at hrel
  obtain ⟨hshape, hv⟩ := hrel.2.2.1 child hchild
  exact acceptableChild_of_accepted hbl hshape hv <|
    (capsAgree_or_collide bytecode seed child).resolve_right fun h ↦ hc ⟨child, hchild, h⟩

end
end LeanVM.Guest.Child
