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
# `opening_round` (`lean_ethereum.py:1231-1255` at leanVM `98ceacf2`, G below)

One fold round of CYWZ26's affine combiner (`foldRound`, `Statement/LeanVmVerifier.lean`): a grind
and `θ`, the five scalars `u0, v0, c0, v1, c1`, a grind and `γ`, then `α`, `β`; `γ` stored for
the point, `α, β, θ` for the queries' row folds, and the claim folded.

* `roundBody`: its core IR (`core7_body`, by kernel evaluation);
* `MeaningOpeningRound`: what a call establishes, over the carried sponge (`rdG1`, `rdS2`,
  `rdG2`, `Fs.squeeze`);
* `opening_round_sound`: the core IR gives the meaning, under `grind_check_Spec 9`, on a memory
  image whose `tabs` holds the bit windows;
* `opening_round_run`: the meaning runs `foldRound st` for every `st` with that claim.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- `opening_round`'s body (G:1231-1255): the capacity copied, the first grind's nonce and
permutation, `θ`, the four scalars `u0, v0, c0, v1` and their permutation, `c1` and the second
grind's nonce and permutation, `γ`, the squeezes of `α` and `β`, the stores, the claim. -/
def roundBody : List Stmt :=
  ((List.range 5).map fun i ↦ .atom (.copy (.n (10 + i)) (.n i))) ++
  fsNonceT (.n 5) 0 15 ++ padRunT 18 ++
  [keccakA (permIns 1 [.n 16, .n 17] 19 (osRun 10 5)) (osRun 23 13),
    .call "grind_check__L9" [.n 24, .n 7] []] ++
  challengeT (.n 23) 36 ++
  fsNextT (.n 5) 1 37 ++ fsNextT (.n 5) 2 40 ++ fsNextT (.n 5) 3 43 ++ fsNextT (.n 5) 4 46 ++
  [keccakA (permIns 4 [.n 38, .n 39, .n 41, .n 42, .n 44, .n 45, .n 47, .n 48] 19 (osRun 31 5))
    (osRun 49 13)] ++
  fsNextT (.n 5) 5 62 ++ fsNonceT (.n 5) 6 65 ++
  [keccakA (permIns 2 [.n 63, .n 64, .n 66, .n 67] 19 (osRun 57 5)) (osRun 68 13),
    .call "grind_check__L9" [.n 69, .n 7] []] ++
  challengeT (.n 68) 81 ++
  [keccakA (permIns 0 [] 19 (osRun 76 5)) (osRun 82 13)] ++ challengeT (.n 82) 95 ++
  [keccakA (permIns 0 [] 19 (osRun 90 5)) (osRun 96 13)] ++ challengeT (.n 96) 109 ++
  [osLd 81 8 0, osLd 95 9 0, osLd 109 9 1, osLd 36 9 2,
    osMul 110 95 40, osAdd 111 37 110, osMul 112 109 43, osAdd 113 111 112, osAdd 114 6 40,
    osMul 115 36 37, osAdd 116 114 115, osMul 117 95 46, osAdd 118 116 117, osMul 119 109 62,
    osAdd 120 118 119] ++
  ((List.range 5).map fun i ↦ osCp (121 + i) (104 + i)) ++
  [osCst 126 (word 128 0), osMul 127 5 126, osCp 128 127, osAdd 129 113 120, osMul 130 81 129,
    osAdd 131 113 130, .ret [.n 121, .n 122, .n 123, .n 124, .n 125, .n 128, .n 131]]

set_option maxRecDepth 100000 in
theorem core7_body : Fn.body Data.core7 = roundBody := stmtsEqb_sound (by decide +kernel)

theorem core7_params : Fn.params Data.core7 = (List.range 10).map V.n := rfl

theorem find_opening_round : coreProgram.find? "opening_round" = some Data.core7 :=
  Program.find?_of_indexOf? (j := 7) (by decide +kernel) rfl

/-! ## The meaning -/

/-- The sponge after the first grind and `θ`. -/
def rdG1 (fs : List E) (n1 : E) : E × Fs := (⟨fs, []⟩ : Fs).grindSqueeze _root_.LeanVM.Parameters.Whir.foldGrindingBits n1

/-- The sponge before the second grind: the five scalars absorbed. -/
def rdS2 (fs : List E) (n1 : E) (m : List E) : Fs := (rdG1 fs n1).2.absorbAll m dsObserve

/-- `γ` and the sponge after it. -/
def rdG2 (fs : List E) (n1 : E) (m : List E) (n2 : E) : E × Fs :=
  (rdS2 fs n1 m).grindSqueeze _root_.LeanVM.Parameters.Whir.foldGrindingBits n2

/-- The fold round's claim (G:1250-1254): `side0 + γ(side0 + side1)`. -/
def roundClaim (claim theta gamma alpha beta u0 v0 c0 v1 c1 : E) : E :=
  let side0 := u0 + alpha * v0 + beta * c0
  side0 + gamma * (side0 + (claim + v0 + theta * u0 + alpha * v1 + beta * c1))

/-- **`opening_round(fs0..fs4, cursor, claim, tabs, gammas, coefs)`** (G:1231-1255): the seven
stream words at the cursor `n1, u0, v0, c0, v1, c1, n2`; from the carried capacity with nothing
waiting, the first grind passes and draws `θ`, the five scalars are absorbed, the second grind
passes and draws `γ`, then `α`, `β` are squeezed; `γ` is stored at `gammas`, `α, β, θ` at
`coefs`; the function returns the capacity after `β`, the cursor seven words on and the folded
claim. -/
def MeaningOpeningRound (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, cur, claim, _, gp, cp], rets =>
    ∃ n1 u0 v0 c0 v1 c1 n2 : E, ReadsAt rd cur [n1, u0, v0, c0, v1, c1, n2] ∧
      let fs := [f0, f1, f2, f3, f4]
      let m := [u0, v0, c0, v1, c1]
      let ga := (rdG2 fs n1 m n2).2.squeeze
      let gb := ga.2.squeeze
      (⟨fs, []⟩ : Fs).GrindOk _root_.LeanVM.Parameters.Whir.foldGrindingBits n1 ∧ (rdS2 fs n1 m).GrindOk _root_.LeanVM.Parameters.Whir.foldGrindingBits n2 ∧
        LoadHolds rd gp 0 (rdG2 fs n1 m n2).1 ∧ LoadHolds rd cp 0 ga.1 ∧ LoadHolds rd cp 1 gb.1 ∧
        LoadHolds rd cp 2 (rdG1 fs n1).1 ∧
        rets = gb.2.cap ++ [cur * gen ^ 7, roundClaim claim (rdG1 fs n1).1 (rdG2 fs n1 m n2).1 ga.1
          gb.1 u0 v0 c0 v1 c1]
  | _, _ => False

/-! ## Soundness -/

variable {rd : Reader} {σ : Val}

theorem grindCheckName_nine : grindCheckName 9 = "grind_check__L9" := rfl


/-- Five scalars absorbed from an empty queue: the first four permuted, the fifth waiting. -/
theorem absorbAll_five (cap : List E) (a b c d e : E) (t : ℕ) :
    (⟨cap, []⟩ : Fs).absorbAll [a, b, c, d, e] t =
      ⟨capOf (⟨cap, [(a, t), (b, t), (c, t), (d, t)]⟩ : Fs).perm, [(e, t)]⟩ := by
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
theorem opening_round_sound (hg : grind_check_Spec 9) {κ : ℕ} (hκ : κ ≤ 32) (hw : winTabBits ≤ κ)
    (L : MemoryImage κ) (args rets : List E) (ht : WinTabs L.read (args.getD 7 0))
    (h : coreProgram.Rel L.read "opening_round" args rets) : MeaningOpeningRound L.read args rets := by
  rw [rel_iff_sem find_opening_round, core7_body, core7_params] at h
  obtain ⟨σ, hp, h⟩ := h
  simp only [roundBody, holdsList_append, holds_fsNonceT, holds_fsNextT, holds_padRunT,
    holds_challengeT, Stmt.HoldsList, Stmt.Holds, holds_const, holds_add, holds_mul,
    holds_copy, holds_load, List.map_cons, List.map_nil, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, osLd, osMul, osAdd, osCp, osCst, and_assoc,
    Nat.reduceAdd] at h
  obtain ⟨c10, c11, c12, c13, c14, ln1, pn1, pad, k1, g1, ch1, lu0, pu0, lv0, pv0, lc0, pc0, lv1,
    pv1, k2, lc1, pc1, ln2, pn2, k3, g2, ch2, k4, ch3, k5, ch4, sg, sa, sb, st, e110, e111, e112,
    e113, e114, e115, e116, e117, e118, e119, e120, c121, c122, c123, c124, c125, e126, e127, e128,
    e129, e130, e131, hret⟩ := h
  subst hp hret
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.getD_cons_succ, List.getD_cons_zero] at ht ⊢
  have hb : _root_.LeanVM.Parameters.Whir.foldGrindingBits ≠ 0 := by decide
  obtain ⟨pd, z1, z2, z3, z4⟩ := pad
  have p15 := fsPackT_cells pn1
  have p37 := fsPackT_cells pu0
  have p40 := fsPackT_cells pv0
  have p43 := fsPackT_cells pc0
  have p46 := fsPackT_cells pv1
  have p62 := fsPackT_cells pc1
  have p65 := fsPackT_cells pn2
  simp only [Prod.ext_iff, Nat.reduceAdd] at p15 p37 p40 p43 p46 p62 p65 z1 z2 z3 z4
  set fs := [σ (V.n 0), σ (V.n 1), σ (V.n 2), σ (V.n 3), σ (V.n 4)] with hfs
  -- the first grind
  have K1 := keccakA_fs (s := ⟨fs, [(σ (.n 15), dsPowNonce)]⟩) k1 (by simp) (by
    simp [permIns, osRun, pendCells, p15.1, p15.2, z1, z2, z3, z4, c10, c11, c12, c13, c14, fs,
      List.range_succ])
  have hn1 : (⟨fs, []⟩ : Fs).nonceState (σ (.n 15)) =
      (⟨fs, [(σ (.n 15), dsPowNonce)]⟩ : Fs).perm := by
    simp [Fs.nonceState, Fs.absorb, rateScalars]
  rw [← hn1] at K1
  have G1 := ((hg hκ hw L _ _ ht) []).mp (grindCheckName_nine ▸ g1)
  obtain ⟨gok1, hθ, hs1⟩ := grindSqueeze_cells hb (σ (.n 15)) _ _ (outCell K1 0) (outCell K1 1) G1.2
  -- the five scalars
  set S1 := (⟨fs, []⟩ : Fs).nonceState (σ (.n 15)) with hS1
  have cap1 : capOf S1 = [σ (.n 31), σ (.n 32), σ (.n 33), σ (.n 34), σ (.n 35)] := by
    simp only [capOf, ← outCell K1 8, ← outCell K1 9, ← outCell K1 10, ← outCell K1 11,
      ← outCell K1 12]
    rfl
  have K2 := keccakA_fs (s := ⟨capOf S1, [(σ (.n 37), dsObserve), (σ (.n 40), dsObserve),
      (σ (.n 43), dsObserve), (σ (.n 46), dsObserve)]⟩) k2 (by simp) (by
    simp [permIns, osRun, pendCells, p37.1, p37.2, p40.1, p40.2, p43.1, p43.2, p46.1, p46.2, cap1, List.range_succ])
  set S2 := (⟨capOf S1, [(σ (.n 37), dsObserve), (σ (.n 40), dsObserve), (σ (.n 43), dsObserve),
    (σ (.n 46), dsObserve)]⟩ : Fs).perm with hS2
  have hs2 : rdS2 fs (σ (.n 15)) [σ (.n 37), σ (.n 40), σ (.n 43), σ (.n 46), σ (.n 62)] =
      ⟨capOf S2, [(σ (.n 62), dsObserve)]⟩ := by
    rw [rdS2, rdG1, hs1, absorbAll_five]
  have cap2 : capOf S2 = [σ (.n 57), σ (.n 58), σ (.n 59), σ (.n 60), σ (.n 61)] := by
    simp only [capOf, ← outCell K2 8, ← outCell K2 9, ← outCell K2 10, ← outCell K2 11,
      ← outCell K2 12]
    rfl
  -- the second grind
  have K3 := keccakA_fs (s := ⟨capOf S2, [(σ (.n 62), dsObserve), (σ (.n 65), dsPowNonce)]⟩) k3
    (by simp) (by
    simp [permIns, osRun, pendCells, p62.1, p62.2, p65.1, p65.2, z1, z2, z3, z4, cap2, List.range_succ])
  have hn2 : (rdS2 fs (σ (.n 15)) [σ (.n 37), σ (.n 40), σ (.n 43), σ (.n 46), σ (.n 62)]).nonceState
      (σ (.n 65)) = (⟨capOf S2, [(σ (.n 62), dsObserve), (σ (.n 65), dsPowNonce)]⟩ : Fs).perm := by
    rw [hs2]; simp [Fs.nonceState, Fs.absorb, rateScalars]
  rw [← hn2] at K3
  have G2 := ((hg hκ hw L _ _ ht) []).mp (grindCheckName_nine ▸ g2)
  obtain ⟨gok2, hγ, hs3⟩ := grindSqueeze_cells hb (σ (.n 65)) _ _ (outCell K3 0) (outCell K3 1) G2.2
  set S3 := (rdS2 fs (σ (.n 15)) [σ (.n 37), σ (.n 40), σ (.n 43), σ (.n 46), σ (.n 62)]).nonceState
    (σ (.n 65)) with hS3
  have cap3 : capOf S3 = [σ (.n 76), σ (.n 77), σ (.n 78), σ (.n 79), σ (.n 80)] := by
    simp only [capOf, ← outCell K3 8, ← outCell K3 9, ← outCell K3 10, ← outCell K3 11,
      ← outCell K3 12]
    rfl
  -- α and β
  have K4 := keccakA_fs (s := ⟨capOf S3, []⟩) k4 (by simp) (by
    simp [permIns, osRun, pendCells, z1, z2, z3, z4, cap3, List.range_succ])
  set S4 := (⟨capOf S3, []⟩ : Fs).perm with hS4
  have cap4 : capOf S4 = [σ (.n 90), σ (.n 91), σ (.n 92), σ (.n 93), σ (.n 94)] := by
    simp only [capOf, ← outCell K4 8, ← outCell K4 9, ← outCell K4 10, ← outCell K4 11,
      ← outCell K4 12]
    rfl
  have K5 := keccakA_fs (s := ⟨capOf S4, []⟩) k5 (by simp) (by
    simp [permIns, osRun, pendCells, z1, z2, z3, z4, cap4, List.range_succ])
  set S5 := (⟨capOf S4, []⟩ : Fs).perm with hS5
  have hα : σ (.n 95) = challengeOf S4 := challengeT_value ch3 (outCell K4 0)
  have hβ : σ (.n 109) = challengeOf S5 := challengeT_value ch4 (outCell K5 0)
  have hG2 : rdG2 fs (σ (.n 15)) [σ (.n 37), σ (.n 40), σ (.n 43), σ (.n 46), σ (.n 62)]
      (σ (.n 65)) = (σ (.n 68), ⟨capOf S3, []⟩) := by
    rw [rdG2, Prod.ext_iff]; exact ⟨hγ, hs3⟩
  have hG1 : (rdG1 fs (σ (.n 15))).1 = σ (.n 36) := by rw [ch1]; exact hθ
  refine ⟨σ (.n 15), σ (.n 37), σ (.n 40), σ (.n 43), σ (.n 46), σ (.n 62), σ (.n 65), ?_, ?_⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact ln1
    · exact lu0
    · exact lv0
    · exact lc0
    · exact lv1
    · exact lc1
    · exact ln2
  · simp only [← hfs]
    simp only [hG2, hG1, Fs.squeeze, ← hS4, ← hS5]
    refine ⟨gok1, gok2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← ch2]; exact sg
    · rw [← hα]; exact sa
    · rw [← hβ]; exact sb
    · exact st
    · rw [e128, e127, e126, show (128 : ℕ) = 2 ^ 7 by rfl, word_two_pow (by decide), c121, c122,
        c123, c124, c125, e131, e130, e129, e113, e112, e111, e110, e120, e119, e118, e117, e116,
        e115, e114, ← ch2, ← hα, ← hβ]
      simp only [capOf, ← outCell K5 8, ← outCell K5 9, ← outCell K5 10, ← outCell K5 11,
        ← outCell K5 12, roundClaim]
      rfl

/-! ## The run -/

/-- **`opening_round`'s meaning runs the Spec's `foldRound`**: from the carried capacity `fs` with
nothing waiting, the seven words read, both grinds passing, `foldRound st` returns the state with
the folded claim and `γ` appended, and the round's `θ, α, β`; the sponge left is the one after
`β`. -/
theorem opening_round_run (st : WhirState) (fs : List E) (n1 u0 v0 c0 v1 c1 n2 : E)
    (h1 : (⟨fs, []⟩ : Fs).GrindOk _root_.LeanVM.Parameters.Whir.foldGrindingBits n1)
    (h2 : (rdS2 fs n1 [u0, v0, c0, v1, c1]).GrindOk _root_.LeanVM.Parameters.Whir.foldGrindingBits n2) :
    RunsTo (foldRound st) ⟨fs, []⟩ [n1, u0, v0, c0, v1, c1, n2]
      ({ st with
          claim := roundClaim st.claim (rdG1 fs n1).1 (rdG2 fs n1 [u0, v0, c0, v1, c1] n2).1
            (rdG2 fs n1 [u0, v0, c0, v1, c1] n2).2.squeeze.1
            (rdG2 fs n1 [u0, v0, c0, v1, c1] n2).2.squeeze.2.squeeze.1 u0 v0 c0 v1 c1,
          gammas := st.gammas ++ [(rdG2 fs n1 [u0, v0, c0, v1, c1] n2).1] },
        ⟨(rdG1 fs n1).1, (rdG2 fs n1 [u0, v0, c0, v1, c1] n2).2.squeeze.1,
          (rdG2 fs n1 [u0, v0, c0, v1, c1] n2).2.squeeze.2.squeeze.1⟩)
      (rdG2 fs n1 [u0, v0, c0, v1, c1] n2).2.squeeze.2.squeeze.2 := by
  have hb : _root_.LeanVM.Parameters.Whir.foldGrindingBits ≠ 0 := by decide
  have g1 := runsToG_grind hb ⟨fs, []⟩ n1 (h1.resolve_left hb)
  have g2 := runsToG_grind hb (rdS2 fs n1 [u0, v0, c0, v1, c1]) n2 (h2.resolve_left hb)
  have e1 : rdG1 fs n1 = (challengeOf ((⟨fs, []⟩ : Fs).nonceState n1),
      ⟨capOf ((⟨fs, []⟩ : Fs).nonceState n1), []⟩) := Fs.grindSqueeze_pos _ hb _
  have e2 : rdG2 fs n1 [u0, v0, c0, v1, c1] n2 =
      (challengeOf ((rdS2 fs n1 [u0, v0, c0, v1, c1]).nonceState n2),
        ⟨capOf ((rdS2 fs n1 [u0, v0, c0, v1, c1]).nonceState n2), []⟩) := Fs.grindSqueeze_pos _ hb _
  have es : rdS2 fs n1 [u0, v0, c0, v1, c1] =
      (((((⟨capOf ((⟨fs, []⟩ : Fs).nonceState n1), []⟩ : Fs).absorb u0 dsObserve).absorb v0
        dsObserve).absorb c0 dsObserve).absorb v1 dsObserve).absorb c1 dsObserve := by
    rw [rdS2, e1]; rfl
  rw [e1, e2]
  rw [es] at g2 ⊢
  have r := g1.bindFrom (f := fun _ => do
      let theta ← VerifierProgram.sampleChallenge
      let u0 ← VerifierProgram.readScalar
      let v0 ← VerifierProgram.readScalar
      let c0 ← VerifierProgram.readScalar
      let v1 ← VerifierProgram.readScalar
      let c1 ← VerifierProgram.readScalar
      let u1 := st.claim + v0 + theta * u0
      VerifierProgram.grindProofOfWork _root_.LeanVM.Parameters.Whir.foldGrindingBits
      let gamma ← VerifierProgram.sampleChallenge
      let alpha ← VerifierProgram.sampleChallenge
      let beta ← VerifierProgram.sampleChallenge
      let claim := (1 + gamma) * (u0 + alpha * v0 + beta * c0) + gamma * (u1 + alpha * v1 + beta * c1)
      return ({ st with claim := claim, gammas := st.gammas ++ [gamma] }, (⟨theta, alpha, beta⟩ : FoldRound)))
    ((runsFromG_sample _ _).bind ((runsTo_readE _ u0).bind ((runsTo_readE _ v0).bind
      ((runsTo_readE _ c0).bind ((runsTo_readE _ v1).bind ((runsTo_readE _ c1).bind
        (g2.bindFrom ((runsFromG_sample _ _).bind ((runsTo_sampleE _).bind
          ((runsTo_sampleE _).bind (runsTo_ret _ _)))))))))))
  refine RunsTo.of_eq r rfl rfl ?_ rfl
  simp only [Fs.squeeze, roundClaim]
  congr 2
  ring

end
end LeanVM.Guest.B1.Whir
