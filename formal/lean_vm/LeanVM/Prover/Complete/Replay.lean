/-
  LeanVM.Prover.Complete.Replay

  The compiled verifier accepts the proof a winning script makes, for every hash function and
  permutation: the verifier's run replays the prover's.
-/

module

public import LeanVM.Prover.Complete.Wins
public import LeanVM.Wire.HonestTree
import LeanVM.Protocol.KeccakHash

/-!
# The verifier replays the honest run

For a hash function `H` and a permutation `F` (in `Id`), the run of a script against a program
(`runFromWithHash`) and the verifier's run of the program on the proof it makes (`runWithHash`)
make the same sponge moves: the verifier absorbs the scalars the script sent, squeezes the
challenges the script received, finds the nonce the search found passing (`powOk_of_findNonceM`),
reads the roots of the trees the prover built (`digestOfScalars_digestScalars`), and authenticates
the openings read off them (`climb_opening`: an opening of the built tree climbs to its root, at any
position, the low `height` bits of which it opens). So where the script wins the program (`Wins`),
the verifier's run returns what the program does on the script's moves, with exactly the stream and
openings the run made consumed (`runWithHash_of_runFrom`), and accepts the proof of a script that
wins with `true` (`runProof_of_wins`).
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile
open LeanVM.Wire (honestNode getD_buildTree sibling_lt div_pow_lt)

variable {α β : Type}

/-! ## The Merkle trees -/

section Merkle

variable (H : Bytes → Digest)

/-- The tree the honest run builds for a committed matrix. -/
def treeOf (c : Committed) : Tree := Id.run (buildTreeWithHash (m := Id) H c.height c.word)

/-- The root the verifier holds for a committed matrix, with its shape. -/
def rootOf (c : Committed) : Digest × ℕ × ℕ := ((treeOf H c).root, c.height, c.width)

theorem height_treeOf (c : Committed) : (treeOf H c).height = c.height := rfl

theorem word_treeOf (c : Committed) : (treeOf H c).word = c.word := rfl

/-- The siblings of the node `x` at level `l`, from it up `n` levels. -/
def honestPath (word : Word) (l x n : ℕ) : List Digest :=
  (List.range n).map fun j ↦ honestNode H word (l + j) (sibling (x / 2 ^ j))

variable {H}

theorem honestPath_succ (word : Word) (l x n : ℕ) :
    honestPath H word l x (n + 1) =
      honestNode H word l (sibling x) :: honestPath H word (l + 1) (x / 2) n := by
  simp only [honestPath, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero,
    pow_zero, Nat.div_one]
  congr 1
  refine List.map_congr_left fun j _ ↦ ?_
  simp only [Function.comp_apply]
  rw [Nat.div_div_eq_div_mul, ← pow_succ', show l + (j + 1) = l + 1 + j by omega]

theorem climbWithHash_cons (node : Digest) (q : ℕ) (s : Digest) (ss : List Digest) :
    Id.run (climbWithHash (m := Id) H node q (s :: ss)) =
      Id.run (climbWithHash (m := Id) H (if q % 2 = 0 then H (digestBytes node ++ digestBytes s)
        else H (digestBytes s ++ digestBytes node)) (q / 2) ss) := by
  simp only [climbWithHash, Id.run, bind]
  split <;> rfl

/-- Climbing a path of the tree's siblings from a node climbs to its ancestor, at any position
that agrees with the node's index on the levels climbed. -/
theorem climb_honest (word : Word) :
    ∀ (n l x q : ℕ), x % 2 ^ n = q % 2 ^ n →
      Id.run (climbWithHash (m := Id) H (honestNode H word l x) q (honestPath H word l x n)) =
        honestNode H word (l + n) (x / 2 ^ n)
  | 0, l, x, q, _ => by
    simp only [honestPath, List.range_zero, List.map_nil, Nat.add_zero, pow_zero, Nat.div_one]
    rfl
  | n + 1, l, x, q, hxq => by
    have hpar : x % 2 = q % 2 := by
      have h1 := congrArg (· % 2) hxq
      simp only [Nat.mod_mod_of_dvd _ (Dvd.intro_left (2 ^ n) (pow_succ 2 n).symm)] at h1
      exact h1
    have hparent : (if q % 2 = 0 then H (digestBytes (honestNode H word l x) ++
        digestBytes (honestNode H word l (sibling x)))
        else H (digestBytes (honestNode H word l (sibling x)) ++
          digestBytes (honestNode H word l x))) = honestNode H word (l + 1) (x / 2) := by
      rw [← hpar]
      simp only [honestNode, sibling]
      rcases Nat.mod_two_eq_zero_or_one x with h0 | h0
      · simp only [h0, ↓reduceIte]
        rw [show 2 * (x / 2) = x by omega]
      · simp only [h0, one_ne_zero, ↓reduceIte]
        rw [show 2 * (x / 2) = x - 1 by omega, show x - 1 + 1 = x by omega]
    have hxq' : x / 2 % 2 ^ n = q / 2 % 2 ^ n := by
      rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self, ← pow_succ', hxq]
    rw [honestPath_succ, climbWithHash_cons, hparent, climb_honest word n (l + 1) (x / 2) (q / 2)
      hxq', Nat.div_div_eq_div_mul, ← pow_succ', show l + 1 + n = l + (n + 1) by omega]

/-- **An opening of the built tree climbs to its root**, at every position: the tree opens the
position's low `height` bits, and the climb reads no higher bit. -/
theorem climb_opening (ht : ℕ) (word : Word) (q : ℕ) :
    Id.run (climbWithHash (m := Id) H
        (H ((((Id.run (buildTreeWithHash (m := Id) H ht word)).opening q).leaf).flatMap K.toBytes))
        q ((Id.run (buildTreeWithHash (m := Id) H ht word)).opening q).path) =
      (Id.run (buildTreeWithHash (m := Id) H ht word)).root := by
  have hilt : q % 2 ^ ht < 2 ^ ht := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hpath : ((Id.run (buildTreeWithHash (m := Id) H ht word)).opening q).path =
      honestPath H word 0 (q % 2 ^ ht) ht := by
    simp only [Tree.opening, LeanVM.Wire.height_buildTree, honestPath]
    refine List.map_congr_left fun j hj ↦ ?_
    have hj' := List.mem_range.mp hj
    rw [Nat.zero_add]
    refine getD_buildTree hj'.le ?_
    have h1 := div_pow_lt hilt hj'.le
    obtain ⟨n, hn⟩ : ∃ n, ht - j = n + 1 := ⟨ht - j - 1, by omega⟩
    rw [hn] at h1 ⊢
    exact sibling_lt h1
  have hleaf : H ((((Id.run (buildTreeWithHash (m := Id) H ht word)).opening q).leaf).flatMap
      K.toBytes) = honestNode H word 0 (q % 2 ^ ht) := by
    simp only [Tree.opening, LeanVM.Wire.height_buildTree, LeanVM.Wire.word_buildTree, honestNode]
  have hroot : (Id.run (buildTreeWithHash (m := Id) H ht word)).root = honestNode H word ht 0 := by
    have := getD_buildTree (h := H) (word := word) (le_refl ht) (j := 0)
      (by rw [Nat.sub_self]; exact Nat.one_pos)
    simp only [Tree.root, LeanVM.Wire.height_buildTree]
    exact this
  rw [hpath, hleaf, climb_honest word ht 0 (q % 2 ^ ht) q (Nat.mod_mod q _), hroot, Nat.zero_add,
    Nat.div_eq_of_lt hilt]

end Merkle

/-! ## The sponge's waiting challenge -/

section Sponge

variable (F : KeccakState → KeccakState)

theorem ground_duplex (sp : Sponge) : Sponge.ground (duplex (m := Id) F sp) = sp.ground := rfl

theorem ground_absorb (sp : Sponge) (x : E) (tag : ℕ) :
    Sponge.ground (absorb (m := Id) F sp x tag) = sp.ground := by
  simp only [absorb, bind, pure]
  split <;> rfl

theorem ground_squeeze (sp : Sponge) : Sponge.ground (squeeze (m := Id) F sp).2 = none := by
  simp only [squeeze, bind, pure]
  split
  · rfl
  · next h => simp [duplex, bind, pure, h]

theorem ground_observePacked (sp : Sponge) (xs : List E) :
    Sponge.ground (observePacked (m := Id) F sp xs) = sp.ground := by
  simp only [observePacked, bind, pure]
  split <;> rfl

theorem squeezePackedChunks_spec :
    ∀ (fuel : ℕ) (sp : Sponge) (missing : ℕ), missing ≤ fuel →
      (squeezePackedChunks (m := Id) F fuel sp missing).1.length = missing ∧
        Sponge.ground (squeezePackedChunks (m := Id) F fuel sp missing).2 = sp.ground
  | 0, sp, missing, h => by
    obtain rfl : missing = 0 := by omega
    exact ⟨rfl, rfl⟩
  | _ + 1, sp, 0, _ => ⟨rfl, rfl⟩
  | fuel + 1, sp, missing + 1, h => by
    have ih := squeezePackedChunks_spec fuel (duplex (m := Id) F sp)
      (missing + 1 - min 8 (missing + 1)) (by omega)
    revert ih
    simp only [squeezePackedChunks, bind, pure]
    generalize squeezePackedChunks (m := Id) F fuel (duplex (m := Id) F sp)
      (missing + 1 - min 8 (missing + 1)) = r
    obtain ⟨rest, sp'⟩ := r
    intro ih
    refine ⟨?_, ih.2⟩
    simp only [List.length_append, List.length_map, List.length_range, ih.1]
    omega

/-- **A packed draw draws as many challenges as asked**, and leaves no challenge waiting unless it
asked for none. -/
theorem samplesPacked_spec (sp : Sponge) (n : ℕ) :
    (samplesPacked (m := Id) F sp n).1.length = n ∧
      Sponge.ground (samplesPacked (m := Id) F sp n).2 = if n = 0 then sp.ground else none := by
  unfold samplesPacked
  rcases n with _ | c
  · exact squeezePackedChunks_spec F 0 sp 0 le_rfl
  · rcases hg : sp.ground with _ | gr
    · have := squeezePackedChunks_spec F (c + 1) sp (c + 1) le_rfl
      revert this
      simp only [bind, pure, List.length_nil, Nat.sub_zero]
      generalize squeezePackedChunks (m := Id) F (c + 1) sp (c + 1) = r
      obtain ⟨rest, sp'⟩ := r
      intro h
      exact ⟨h.1, by rw [h.2, hg]; simp⟩
    · have := squeezePackedChunks_spec F (c + 1 - (min c 6 + 1)) { sp with ground := none }
        (c + 1 - (min c 6 + 1)) le_rfl
      revert this
      simp only [bind, pure, List.length_cons, List.length_map, List.length_take,
        List.length_range]
      generalize squeezePackedChunks (m := Id) F (c + 1 - (min c 6 + 1)) { sp with ground := none }
        (c + 1 - (min c 6 + 1)) = r
      obtain ⟨rest, sp'⟩ := r
      intro h
      refine ⟨?_, by rw [h.2]; simp⟩
      simp only [List.length_cons, List.length_append, List.length_map, List.length_take,
        List.length_range, h.1]
      omega

theorem ground_absorbNonce (sp : Sponge) (n : E) :
    (Sponge.ground (absorbNonce (m := Id) F sp n).2).isSome = true := rfl

/-- The nonce the search returns passes the proof of work. -/
theorem powOk_of_searchM {bits : ℕ} {o : Bool} {sp : Sponge} :
    ∀ (n count : ℕ) {x : E}, Id.run (searchM (m := Id) F bits o sp n count) = some x →
      powOk bits (Id.run (absorbNonce (m := Id) F sp x)).1 = true
  | _, 0, _, h => by simp [searchM, Id.run, pure] at h
  | n, count + 1, x, h => by
    simp only [searchM, Id.run, bind, pure] at h
    split at h
    · next hp =>
      cases h
      exact (Bool.and_eq_true _ _).mp hp |>.1
    · exact powOk_of_searchM (n + 1) count h

theorem powOk_of_findNonceM {bits : ℕ} {o : Bool} {sp : Sponge} {fuel : ℕ} {x : E}
    (h : Id.run (findNonceM (m := Id) F bits o sp fuel) = some x) :
    powOk bits (Id.run (absorbNonce (m := Id) F sp x)).1 = true :=
  powOk_of_searchM F 0 fuel h

end Sponge

/-! ## The replay -/

section Replay

variable (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ) {B : ℕ}

/-- The openings of a committed matrix's tree are its rows, and they authenticate. -/
theorem openPhase_treeOf {c : Committed} (hc : WellShaped c.width c.word) (ps : List ℕ) :
    Id.run (openPhaseWithHash (m := Id) H (treeOf H c).root c.height c.width ps
      (ps.map (treeOf H c).opening)) = some (c.rows ps) := by
  have hshape : ∀ o ∈ ps.map (treeOf H c).opening, o.leaf.length = c.width ∧
      o.path.length = c.height := by
    intro o ho
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp ho
    exact ⟨hc _, LeanVM.Wire.length_path_opening _ _ _⟩
  have hidx : (ps.map (treeOf H c).opening).map Opening.leafIndex = ps := by
    simp [List.map_map, Function.comp_def, treeOf, LeanVM.Wire.leafIndex_opening]
  have hall : ∀ (qs : List ℕ) (rest : List Opening),
      Id.run (openAllWithHash (m := Id) H (treeOf H c).root c.height c.width qs
        (qs.map (treeOf H c).opening ++ rest)) = some (c.rows qs, rest) := by
    intro qs rest
    induction qs with
    | nil => rfl
    | cons q qs ih =>
      have hone : Id.run (openOneWithHash (m := Id) H (treeOf H c).root c.height c.width q
          ((treeOf H c).opening q)) = true := by
        simp only [openOneWithHash]
        rw [ite_eq_left ⟨hc _, LeanVM.Wire.length_path_opening _ _ _⟩]
        have := climb_opening (H := H) c.height c.word q
        simp only [treeOf, Id.run, bind, pure] at this ⊢
        exact decide_eq_true (congrArg _ this)
      simp only [List.map_cons, List.cons_append, openAllWithHash, Id.run, bind, pure] at ih hone ⊢
      rw [hone]
      simp only [↓reduceIte]
      rw [ih]
      simp [Committed.rows, Tree.opening, treeOf, LeanVM.Wire.height_buildTree,
        LeanVM.Wire.word_buildTree]
  simp only [openPhaseWithHash]
  rw [ite_eq_left ⟨hshape, hidx⟩]
  have := hall ps []
  rw [List.append_nil] at this
  simp only [Id.run, bind, pure] at this ⊢
  rw [this]

/-- **The verifier replays a winning script's run.** From a sponge whose waiting challenge the flag
`g` records and the trees of the matrices committed so far, if the script wins the program and its
run makes the scalars `xs` and the openings `os`, then the verifier's run of the program on them,
followed by anything, returns what the program returns on the script's moves, a value the
postcondition holds of, with exactly the rest left. -/
theorem runWithHash_of_runFrom {Q : α → β → Bool → List Committed → Prop} :
    ∀ (p : VerifierProgram α) (s : Script β) (g : Bool) (cs : List Committed) (sp : Sponge)
      (xs : List E) (os : List (List Opening)),
      Wins B Q p s g cs → (∀ c ∈ cs, WellShaped c.width c.word) → sp.ground.isSome = g →
      Id.run (runFromWithHash (m := Id) H F fuel p (some s) sp (cs.map (treeOf H))) =
        some (xs, os) →
      ∀ (rest : List E) (restO : List (List Opening)), ∃ a b g' cs' sp', Q a b g' cs' ∧
        Id.run (runWithHash (m := Id) H F p ⟨sp, xs ++ rest, os ++ restO, cs.map (rootOf H)⟩) =
          some (a, ⟨sp', rest, restO, cs'.map (rootOf H)⟩)
  | .ret a, .ret b, g, cs, sp, xs, os, hw, _, _, hp, rest, restO => by
    simp only [runFromWithHash, Id.run, pure, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨a, b, g, cs, sp, hw, rfl⟩
  | .read k, .send x s, g, cs, sp, xs, os, hw, hcs, hg, hp, rest, restO => by
    obtain ⟨rfl, hw⟩ := hw
    have hg' : sp.ground = none := by simpa using hg
    simp only [runFromWithHash, Id.run, bind, pure, Option.map_eq_some_iff] at hp
    obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨a, b, g', cs', sp', hQ, hrun⟩ := runWithHash_of_runFrom (k x) s false cs _ xs' os' hw
      hcs (by rw [ground_absorb, hg']; rfl) hp rest restO
    refine ⟨a, b, g', cs', sp', hQ, ?_⟩
    simp only [runWithHash, List.cons_append, hg', Id.run, bind] at hrun ⊢
    exact hrun
  | .sample k, .sample s, g, cs, sp, xs, os, hw, hcs, hg, hp, rest, restO => by
    simp only [runFromWithHash, Id.run, bind] at hp
    obtain ⟨a, b, g', cs', sp', hQ, hrun⟩ := runWithHash_of_runFrom _ _ false cs _ xs os (hw _)
      hcs (by rw [ground_squeeze]; rfl) hp rest restO
    exact ⟨a, b, g', cs', sp', hQ, by simpa only [runWithHash, Id.run, bind] using hrun⟩
  | .readPacked n k, .sendPacked ys s, g, cs, sp, xs, os, hw, hcs, hg, hp, rest, restO => by
    obtain ⟨rfl, hlen, hw⟩ := hw
    have hg' : sp.ground = none := by simpa using hg
    have hpk : Script.packedOf n (some (Script.sendPacked ys s)) = ys := by
      simp only [Script.packedOf]
      subst hlen
      exact List.ext_getElem (by simp) fun i h1 h2 ↦ by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    simp only [runFromWithHash, hpk, Id.run, bind, pure, Option.map_eq_some_iff] at hp
    obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨a, b, g', cs', sp', hQ, hrun⟩ := runWithHash_of_runFrom (k ys) s false cs _ xs' os'
      hw hcs (by rw [ground_observePacked, hg']; rfl) hp rest restO
    refine ⟨a, b, g', cs', sp', hQ, ?_⟩
    have htake : (ys ++ xs' ++ rest).take n = ys := by
      rw [List.append_assoc, List.take_append_of_le_length (by omega), List.take_of_length_le
        (by omega)]
    have hdrop : (ys ++ xs' ++ rest).drop n = xs' ++ rest := by
      rw [List.append_assoc, List.drop_append_of_le_length (by omega), List.drop_of_length_le
        (by omega), List.nil_append]
    simp only [runWithHash, hg', Option.isNone_none, true_and, List.length_append]
    rw [ite_eq_left (by omega)]
    simp only [htake, hdrop, Id.run, bind] at hrun ⊢
    exact hrun
  | .samplePacked n k, .samplePacked _ s, g, cs, sp, xs, os, hw, hcs, hg, hp, rest, restO => by
    simp only [runFromWithHash, Id.run, bind] at hp
    obtain ⟨hlen, hgr⟩ := samplesPacked_spec F sp n
    obtain ⟨a, b, g', cs', sp', hQ, hrun⟩ := runWithHash_of_runFrom _ _ (g && n == 0) cs _ xs os
      (hw _ hlen) hcs (by rw [hgr]; split <;> simp_all) hp rest restO
    exact ⟨a, b, g', cs', sp', hQ, by simpa only [runWithHash, Id.run, bind] using hrun⟩
  | .grind bits k, .grind o s, g, cs, sp, xs, os, hw, hcs, hg, hp, rest, restO => by
    obtain ⟨rfl, -, hw⟩ := hw
    have hg' : sp.ground = none := by simpa using hg
    simp only [runFromWithHash, Id.run, bind, pure] at hp
    split at hp
    · cases hp
    · next nonce hnonce =>
      simp only [Option.map_eq_some_iff] at hp
      obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨a, b, g', cs', sp', hQ, hrun⟩ := runWithHash_of_runFrom k s true cs _ xs' os' hw hcs
        (ground_absorbNonce F sp nonce) hp rest restO
      refine ⟨a, b, g', cs', sp', hQ, ?_⟩
      have hpow := powOk_of_findNonceM F hnonce
      simp only [runWithHash, List.cons_append, hg', Id.run, bind] at hrun hpow ⊢
      revert hrun hpow
      generalize absorbNonce (m := Id) F sp nonce = r
      obtain ⟨pow, sp2⟩ := r
      intro hrun hpow
      simp only at hrun hpow ⊢
      rw [ite_eq_left hpow]
      exact hrun
  | .commit ht w k, .commit word s, g, cs, sp, xs, os, hw, hcs, hg, hp, rest, restO => by
    obtain ⟨rfl, hws, hw⟩ := hw
    have hg' : sp.ground = none := by simpa using hg
    set c : Committed := ⟨ht, w, word⟩ with hc
    simp only [runFromWithHash, Script.wordOf, Script.afterCommit, Id.run, bind, pure,
      Option.map_eq_some_iff] at hp
    obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hp' : Id.run (runFromWithHash (m := Id) H F fuel k (some s)
        (absorb (m := Id) F (absorb (m := Id) F sp (digestHalves (treeOf H c).root).1 dsObserve)
          (digestHalves (treeOf H c).root).2 dsObserve) ((cs ++ [c]).map (treeOf H))) =
        some (xs', os') := by
      rw [List.map_append, List.map_singleton]
      exact hp
    have hcs' : ∀ c' ∈ cs ++ [c], WellShaped c'.width c'.word := by
      intro c' hc'
      rcases List.mem_append.mp hc' with hc' | hc'
      · exact hcs c' hc'
      · rw [List.mem_singleton] at hc'; subst hc'; exact hws
    obtain ⟨a, b, g', cs', sp', hQ, hrun⟩ := runWithHash_of_runFrom k s false _ _ xs' os' hw hcs'
      (by rw [ground_absorb, ground_absorb, hg']; rfl) hp' rest restO
    refine ⟨a, b, g', cs', sp', hQ, ?_⟩
    have hrc : rootOf H c = (digestFromHalves ((digestHalves (treeOf H c).root).1,
        (digestHalves (treeOf H c).root).2), ht, w) := by
      rw [Prod.mk.eta, digestOfScalars_digestScalars]; rfl
    rw [List.map_append, List.map_singleton, hrc] at hrun
    simp only [runWithHash, List.cons_append, hg', Id.run, bind] at hrun ⊢
    exact hrun
  | .query i ps k, .query s, g, cs, sp, xs, os, hw, hcs, hg, hp, rest, restO => by
    obtain ⟨c, hc, hw⟩ := hw
    have htree : (cs.map (treeOf H))[i]? = some (treeOf H c) := by
      rw [List.getElem?_map, hc]; rfl
    have hroot : (cs.map (rootOf H))[i]? = some (rootOf H c) := by
      rw [List.getElem?_map, hc]; rfl
    have hrows : (ps.map fun q ↦ (treeOf H c).word (q % 2 ^ (treeOf H c).height)) = c.rows ps :=
      rfl
    simp only [runFromWithHash, htree, hrows, Script.afterQuery, Id.run, bind, pure,
      Option.map_eq_some_iff] at hp
    obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨a, b, g', cs', sp', hQ, hrun⟩ := runWithHash_of_runFrom _ _ g cs sp xs' os' hw hcs hg
      hp rest restO
    refine ⟨a, b, g', cs', sp', hQ, ?_⟩
    have hopen := openPhase_treeOf H (hcs c (List.mem_of_getElem? hc)) ps
    simp only [runWithHash, hroot, List.cons_append, rootOf, Id.run, bind] at hrun hopen ⊢
    rw [hopen]
    exact hrun
  | .ret _, .send _ _, _, _, _, _, _, hw, _, _, _, _, _ | .ret _, .sample _, _, _, _, _, _, hw, _, _, _, _, _
  | .ret _, .sendPacked _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .ret _, .samplePacked _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .ret _, .grind _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .ret _, .commit _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .ret _, .query _, _, _, _, _, _, hw, _, _, _, _, _ => hw.elim
  | .fail, _, _, _, _, _, _, hw, _, _, _, _, _ => hw.elim
  | .read _, .ret _, _, _, _, _, _, hw, _, _, _, _, _ | .read _, .sample _, _, _, _, _, _, hw, _, _, _, _, _
  | .read _, .sendPacked _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .read _, .samplePacked _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .read _, .grind _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .read _, .commit _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .read _, .query _, _, _, _, _, _, hw, _, _, _, _, _ => hw.elim
  | .sample _, .ret _, _, _, _, _, _, hw, _, _, _, _, _
  | .sample _, .send _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .sample _, .sendPacked _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .sample _, .samplePacked _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .sample _, .grind _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .sample _, .commit _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .sample _, .query _, _, _, _, _, _, hw, _, _, _, _, _ => hw.elim
  | .readPacked _ _, .ret _, _, _, _, _, _, hw, _, _, _, _, _
  | .readPacked _ _, .send _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .readPacked _ _, .sample _, _, _, _, _, _, hw, _, _, _, _, _
  | .readPacked _ _, .samplePacked _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .readPacked _ _, .grind _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .readPacked _ _, .commit _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .readPacked _ _, .query _, _, _, _, _, _, hw, _, _, _, _, _ => hw.elim
  | .samplePacked _ _, .ret _, _, _, _, _, _, hw, _, _, _, _, _
  | .samplePacked _ _, .send _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .samplePacked _ _, .sample _, _, _, _, _, _, hw, _, _, _, _, _
  | .samplePacked _ _, .sendPacked _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .samplePacked _ _, .grind _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .samplePacked _ _, .commit _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .samplePacked _ _, .query _, _, _, _, _, _, hw, _, _, _, _, _ => hw.elim
  | .grind _ _, .ret _, _, _, _, _, _, hw, _, _, _, _, _
  | .grind _ _, .send _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .grind _ _, .sample _, _, _, _, _, _, hw, _, _, _, _, _
  | .grind _ _, .sendPacked _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .grind _ _, .samplePacked _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .grind _ _, .commit _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .grind _ _, .query _, _, _, _, _, _, hw, _, _, _, _, _ => hw.elim
  | .commit _ _ _, .ret _, _, _, _, _, _, hw, _, _, _, _, _
  | .commit _ _ _, .send _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .commit _ _ _, .sample _, _, _, _, _, _, hw, _, _, _, _, _
  | .commit _ _ _, .sendPacked _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .commit _ _ _, .samplePacked _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .commit _ _ _, .grind _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .commit _ _ _, .query _, _, _, _, _, _, hw, _, _, _, _, _ => hw.elim
  | .query _ _ _, .ret _, _, _, _, _, _, hw, _, _, _, _, _
  | .query _ _ _, .send _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .query _ _ _, .sample _, _, _, _, _, _, hw, _, _, _, _, _
  | .query _ _ _, .sendPacked _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .query _ _ _, .samplePacked _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .query _ _ _, .grind _ _, _, _, _, _, _, hw, _, _, _, _, _
  | .query _ _ _, .commit _ _, _, _, _, _, _, hw, _, _, _, _, _ => hw.elim

/-- **The verifier accepts a winning script's proof**, for every hash function and permutation:
a script that wins the program with `true`, from no commitment, makes a proof (where its
proof-of-work searches succeed) that the compiled verifier accepts from the same seed. -/
theorem runProof_of_wins {P : VerifierProgram Bool} {S : Script β} {seed : KeccakState}
    {π : Proof} (hw : Wins B (fun a _ _ _ ↦ a = true) P S false [])
    (hπ : Id.run (runScriptWithHash (m := Id) H F P S seed fuel) = some π) :
    Id.run (runProofWithHash (m := Id) H F P seed π) = true := by
  simp only [runScriptWithHash, Id.run, bind, pure, Option.map_eq_some_iff] at hπ
  obtain ⟨⟨xs, os⟩, hp, rfl⟩ := hπ
  obtain ⟨a, b, g', cs', sp', ha, hrun⟩ := runWithHash_of_runFrom H F fuel P S false [] _ xs os hw
    (by simp) rfl hp [] []
  simp only [List.append_nil, List.map_nil] at hrun
  subst ha
  simp only [runProofWithHash, Id.run, bind, pure] at hrun ⊢
  rw [hrun]
  rfl

end Replay

end LeanVM.Prover

end
