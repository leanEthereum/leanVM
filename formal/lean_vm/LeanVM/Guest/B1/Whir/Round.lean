/-
  LeanVM.Guest.B1.Whir.Round

  B1 for `opening_round`: one fold round of the stacked WHIR opening.
-/

module

public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Common.Run
public import LeanVM.Guest.B1.Bits.Meaning
public import LeanVM.Guest.B1.Whir.Flat
public import LeanVM.Guest.CoreData

/-!
# `opening_round` (`lean_ethereum.py:1212-1229`, G below)

One fold round of CYWZ26's affine combiner (`foldRound`, `Statement/LeanVmVerifier.lean`): the
four scalars `u0, w, c0, c1`, a grind and `α`, then `β`; `α` stored for the point and, with
`β`, for the queries' row folds, and the claim folded at `α`.

* `roundBody`: its core IR (`core7_body`, by kernel evaluation);
* `MeaningOpeningRound`: what a call establishes, over the carried sponge (`rdS2`, `rdG2`,
  `Fs.squeeze`);
* `opening_round_sound`: the core IR gives the meaning, under `grind_check_Spec 7`, on a memory
  image whose `tabs` holds the bit windows;
* `opening_round_run`: the meaning runs `foldRound st` for every `st` with that claim.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- `opening_round`'s body (G:1212-1229): the capacity copied, the four scalars `u0, w, c0, c1`
and their permutation, the grind's nonce and permutation, `α`, the squeeze of `β`, the stores,
the claim. -/
def roundBody : List Stmt :=
  ((List.range 5).map fun i ↦ .atom (.copy (.n (10 + i)) (.n i))) ++
  fsNextT (.n 5) 0 15 ++ fsNextT (.n 5) 1 18 ++ fsNextT (.n 5) 2 21 ++ fsNextT (.n 5) 3 24 ++
  [keccakA (permIns 4 [.n 16, .n 17, .n 19, .n 20, .n 22, .n 23, .n 25, .n 26] 44 (osRun 10 5))
    (osRun 27 13)] ++
  fsNonceT (.n 5) 4 40 ++ padRunT 43 ++
  [keccakA (permIns 1 [.n 41, .n 42] 44 (osRun 35 5)) (osRun 48 13),
    .call "grind_check__L7" [.n 49, .n 7] []] ++
  challengeT (.n 48) 61 ++
  [keccakA (permIns 0 [] 44 (osRun 56 5)) (osRun 62 13)] ++ challengeT (.n 62) 75 ++
  [osLd 61 8 0, osLd 61 9 0, osLd 75 9 1,
    osMul 76 75 21, osAdd 77 15 76, osAdd 78 15 6, osMul 79 61 18, osAdd 80 78 79,
    osAdd 81 21 24, osMul 82 75 81, osAdd 83 80 82, osMul 84 61 83, osAdd 85 77 84] ++
  ((List.range 5).map fun i ↦ osCp (86 + i) (70 + i)) ++
  [osCst 91 (word 32 0), osMul 92 5 91, osCp 93 92, osCp 94 85,
    .ret [.n 86, .n 87, .n 88, .n 89, .n 90, .n 93, .n 94]]

set_option maxRecDepth 100000 in
theorem core7_body : Fn.body fn% «opening_round» = roundBody := stmtsEqb_sound (by decide +kernel)

theorem core7_params : Fn.params fn% «opening_round» = (List.range 10).map V.n := rfl

theorem find_opening_round : coreProgram.find? "opening_round" = some fn% «opening_round» :=
  coreProgram_find?_at (j := idx% «opening_round») rfl

/-! ## The meaning -/

/-- The sponge before the grind: the four scalars waiting. -/
def rdS2 (fs : List E) (m : List E) : Fs := (⟨fs, []⟩ : Fs).absorbAll m dsObserve

/-- `α` and the sponge after it. -/
def rdG2 (fs : List E) (m : List E) (n2 : E) : E × Fs :=
  (rdS2 fs m).grindSqueeze _root_.LeanVM.Parameters.Whir.foldGrindingBits n2

/-- The fold round's claim (G:1227-1228): `u0 + β c0 + α (u0 + claim + α w + β (c0 + c1))`. -/
def roundClaim (claim alpha beta u0 w c0 c1 : E) : E :=
  u0 + beta * c0 + alpha * (u0 + claim + alpha * w + beta * (c0 + c1))

/-- **`opening_round(fs0..fs4, cursor, claim, tabs, alphas, coefs)`** (G:1212-1229): the five
stream words at the cursor `u0, w, c0, c1, n2`; from the carried capacity with nothing waiting,
the four scalars are absorbed, the grind passes and draws `α`, then `β` is squeezed; `α` is stored
at `alphas`, `α, β` at `coefs`; the function returns the capacity after `β`, the cursor five words
on and the folded claim. -/
def MeaningOpeningRound (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, cur, claim, _, gp, cp], rets =>
    ∃ u0 w c0 c1 n2 : E, ReadsAt rd cur [u0, w, c0, c1, n2] ∧
      let fs := [f0, f1, f2, f3, f4]
      let m := [u0, w, c0, c1]
      let ga := rdG2 fs m n2
      let gb := ga.2.squeeze
      (rdS2 fs m).GrindOk _root_.LeanVM.Parameters.Whir.foldGrindingBits n2 ∧
        LoadHolds rd gp 0 ga.1 ∧ LoadHolds rd cp 0 ga.1 ∧ LoadHolds rd cp 1 gb.1 ∧
        rets = gb.2.cap ++ [cur * gen ^ 5, roundClaim claim ga.1 gb.1 u0 w c0 c1]
  | _, _ => False

/-! ## Soundness -/

variable {rd : Reader} {σ : Val}

theorem grindCheckName_seven : grindCheckName 7 = "grind_check__L7" := rfl

/-- Four scalars absorbed from an empty queue: all four waiting. -/
theorem absorbAll_four (cap : List E) (a b c d : E) (t : ℕ) :
    (⟨cap, []⟩ : Fs).absorbAll [a, b, c, d] t = ⟨cap, [(a, t), (b, t), (c, t), (d, t)]⟩ := by
  simp [Fs.absorbAll, Fs.absorb, rateScalars]

/-- One scalar absorbed below a full queue. -/
theorem absorb_short (s : Fs) (x : E) (t : ℕ) (h : s.pend.length ≠ 4) :
    s.absorb x t = ⟨s.cap, s.pend ++ [(x, t)]⟩ := by
  simp [Fs.absorb, rateScalars, h]

/-- An output cell of a permutation. -/
theorem outCell {σ : Val} {k : ℕ} {f : Fin 13 → E} (h : cells13 ((osRun k 13).map σ) = f)
    (i : Fin 13) : σ (.n (k + i.val)) = f i := by
  have := outs_eq h i (by simp [osRun])
  simpa [osRun] using this

/-- **`opening_round`'s core IR gives its meaning**, on a memory image of `2^κ` words,
`11 ≤ κ ≤ 32`, whose `tabs` holds the bit windows. -/
theorem opening_round_sound (hg : grind_check_Spec 7) {κ : ℕ} (hκ : κ ≤ 32) (hw : winTabBits ≤ κ)
    (L : MemoryImage κ) (args rets : List E) (ht : WinTabs L.read (args.getD 7 0))
    (h : coreProgram.Rel L.read "opening_round" args rets) : MeaningOpeningRound L.read args rets := by
  rw [rel_iff_sem find_opening_round, core7_body, core7_params] at h
  obtain ⟨σ, hp, h⟩ := h
  simp only [roundBody, holdsList_append, holds_fsNonceT, holds_fsNextT, holds_padRunT,
    holds_challengeT, Stmt.HoldsList, Stmt.Holds, holds_const, holds_add, holds_mul,
    holds_copy, holds_load, List.map_cons, List.map_nil, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, osLd, osMul, osAdd, osCp, osCst, and_assoc,
    Nat.reduceAdd] at h
  obtain ⟨c10, c11, c12, c13, c14, lu0, pu0, lw, pw, lc0, pc0, lc1, pc1, k1, ln2, pn2,
    pad, k2, g2, ch1, k3, ch2, sg, sa, sb, e76, e77, e78, e79, e80, e81, e82, e83, e84, e85,
    c86, c87, c88, c89, c90, e91, e92, e93, e94, hret⟩ := h
  subst hp hret
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.getD_cons_succ, List.getD_cons_zero] at ht ⊢
  have hb : _root_.LeanVM.Parameters.Whir.foldGrindingBits ≠ 0 := by decide
  obtain ⟨pd, z1, z2, z3, z4⟩ := pad
  have p15 := fsPackT_cells pu0
  have p18 := fsPackT_cells pw
  have p21 := fsPackT_cells pc0
  have p24 := fsPackT_cells pc1
  have p40 := fsPackT_cells pn2
  simp only [Prod.ext_iff, Nat.reduceAdd] at p15 p18 p21 p24 p40 z1 z2 z3 z4
  set fs := [σ (V.n 0), σ (V.n 1), σ (V.n 2), σ (V.n 3), σ (V.n 4)] with hfs
  -- the four scalars
  have K1 := keccakA_fs (s := ⟨fs, [(σ (.n 15), dsObserve), (σ (.n 18), dsObserve),
      (σ (.n 21), dsObserve), (σ (.n 24), dsObserve)]⟩) k1 (by simp) (by
    simp [permIns, osRun, pendCells, p15.1, p15.2, p18.1, p18.2, p21.1, p21.2, p24.1, p24.2, c10,
      c11, c12, c13, c14, fs, List.range_succ])
  set S1 := (⟨fs, [(σ (.n 15), dsObserve), (σ (.n 18), dsObserve), (σ (.n 21), dsObserve),
    (σ (.n 24), dsObserve)]⟩ : Fs).perm with hS1
  have hs2 : rdS2 fs [σ (.n 15), σ (.n 18), σ (.n 21), σ (.n 24)] =
      ⟨fs, [(σ (.n 15), dsObserve), (σ (.n 18), dsObserve), (σ (.n 21), dsObserve),
        (σ (.n 24), dsObserve)]⟩ := by
    rw [rdS2, absorbAll_four]
  have cap1 : capOf S1 = [σ (.n 35), σ (.n 36), σ (.n 37), σ (.n 38), σ (.n 39)] := by
    simp only [capOf, ← outCell K1 8, ← outCell K1 9, ← outCell K1 10, ← outCell K1 11,
      ← outCell K1 12]
    rfl
  -- the grind
  have K2 := keccakA_fs (s := ⟨capOf S1, [(σ (.n 40), dsPowNonce)]⟩) k2
    (by simp) (by
    simp [permIns, osRun, pendCells, p40.1, p40.2, z1, z2, z3, z4, cap1, List.range_succ])
  have hn2 : (rdS2 fs [σ (.n 15), σ (.n 18), σ (.n 21), σ (.n 24)]).nonceState
      (σ (.n 40)) = (⟨capOf S1, [(σ (.n 40), dsPowNonce)]⟩ : Fs).perm := by
    rw [hs2]; simp [Fs.nonceState, Fs.absorb, rateScalars, hS1]
  rw [← hn2] at K2
  have G2 := ((hg hκ hw L _ _ ht) []).mp (grindCheckName_seven ▸ g2)
  obtain ⟨gok2, hα, hs3⟩ := grindSqueeze_cells hb (σ (.n 40)) _ _ (outCell K2 0) (outCell K2 1) G2.2
  set S3 := (rdS2 fs [σ (.n 15), σ (.n 18), σ (.n 21), σ (.n 24)]).nonceState
    (σ (.n 40)) with hS3
  have cap3 : capOf S3 = [σ (.n 56), σ (.n 57), σ (.n 58), σ (.n 59), σ (.n 60)] := by
    simp only [capOf, ← outCell K2 8, ← outCell K2 9, ← outCell K2 10, ← outCell K2 11,
      ← outCell K2 12]
    rfl
  -- β
  have K3 := keccakA_fs (s := ⟨capOf S3, []⟩) k3 (by simp) (by
    simp [permIns, osRun, pendCells, z1, z2, z3, z4, cap3, List.range_succ])
  set S4 := (⟨capOf S3, []⟩ : Fs).perm with hS4
  have hβ : σ (.n 75) = challengeOf S4 := challengeT_value ch2 (outCell K3 0)
  have hG2 : rdG2 fs [σ (.n 15), σ (.n 18), σ (.n 21), σ (.n 24)] (σ (.n 40)) =
      (σ (.n 48), ⟨capOf S3, []⟩) := by
    rw [rdG2, Prod.ext_iff]; exact ⟨hα, hs3⟩
  refine ⟨σ (.n 15), σ (.n 18), σ (.n 21), σ (.n 24), σ (.n 40), ?_, ?_⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact lu0
    · exact lw
    · exact lc0
    · exact lc1
    · exact ln2
  · simp only [← hfs]
    simp only [hG2, Fs.squeeze, ← hS4]
    refine ⟨gok2, ?_, ?_, ?_, ?_⟩
    · rw [← ch1]; exact sg
    · rw [← ch1]; exact sa
    · rw [← hβ]; exact sb
    · rw [e93, e92, e91, show (32 : ℕ) = 2 ^ 5 by rfl, word_two_pow (by decide), c86, c87,
        c88, c89, c90, e94, e85, e84, e83, e82, e81, e80, e79, e78, e77, e76, ← ch1, ← hβ]
      simp only [capOf, ← outCell K3 8, ← outCell K3 9, ← outCell K3 10, ← outCell K3 11,
        ← outCell K3 12, roundClaim]
      rfl

/-! ## The run -/

/-- **`opening_round`'s meaning runs the Spec's `foldRound`**: from the carried capacity `fs` with
nothing waiting, the five words read, the grind passing, `foldRound st` returns the state with the
claim folded at `α` and `α` appended, and the round's `α, β`; the sponge left is the one after
`β`. -/
theorem opening_round_run (st : WhirState) (fs : List E) (u0 w c0 c1 n2 : E)
    (h2 : (rdS2 fs [u0, w, c0, c1]).GrindOk _root_.LeanVM.Parameters.Whir.foldGrindingBits n2) :
    RunsTo (foldRound st) ⟨fs, []⟩ [u0, w, c0, c1, n2]
      ({ st with
          claim := roundClaim st.claim (rdG2 fs [u0, w, c0, c1] n2).1
            (rdG2 fs [u0, w, c0, c1] n2).2.squeeze.1 u0 w c0 c1,
          alphas := st.alphas ++ [(rdG2 fs [u0, w, c0, c1] n2).1] },
        ⟨(rdG2 fs [u0, w, c0, c1] n2).1, (rdG2 fs [u0, w, c0, c1] n2).2.squeeze.1⟩)
      (rdG2 fs [u0, w, c0, c1] n2).2.squeeze.2 := by
  have hb : _root_.LeanVM.Parameters.Whir.foldGrindingBits ≠ 0 := by decide
  have g2 := runsToG_grind hb (rdS2 fs [u0, w, c0, c1]) n2 (h2.resolve_left hb)
  have e2 : rdG2 fs [u0, w, c0, c1] n2 =
      (challengeOf ((rdS2 fs [u0, w, c0, c1]).nonceState n2),
        ⟨capOf ((rdS2 fs [u0, w, c0, c1]).nonceState n2), []⟩) := Fs.grindSqueeze_pos _ hb _
  have es : rdS2 fs [u0, w, c0, c1] =
      ((((⟨fs, []⟩ : Fs).absorb u0 dsObserve).absorb w dsObserve).absorb c0 dsObserve).absorb
        c1 dsObserve := rfl
  rw [e2]
  rw [es] at g2 ⊢
  have r := (runsTo_readE _ u0).bind (f := fun u0 => do
      let w ← VerifierProgram.readScalar
      let c0 ← VerifierProgram.readScalar
      let c1 ← VerifierProgram.readScalar
      VerifierProgram.grindProofOfWork _root_.LeanVM.Parameters.Whir.foldGrindingBits
      let alpha ← VerifierProgram.sampleChallenge
      let beta ← VerifierProgram.sampleChallenge
      let claim := u0 + alpha * (u0 + st.claim) + alpha * alpha * w + beta * c0 +
        alpha * beta * (c0 + c1)
      return ({ st with claim := claim, alphas := st.alphas ++ [alpha] },
        (⟨alpha, beta⟩ : FoldRound)))
    ((runsTo_readE _ w).bind ((runsTo_readE _ c0).bind ((runsTo_readE _ c1).bind
      (g2.bindFrom ((runsFromG_sample _ _).bind ((runsTo_sampleE _).bind
        (runsTo_ret _ _)))))))
  refine RunsTo.of_eq r rfl rfl ?_ rfl
  simp only [Fs.squeeze, roundClaim]
  congr 2
  ring

end
end LeanVM.Guest.B1.Whir
