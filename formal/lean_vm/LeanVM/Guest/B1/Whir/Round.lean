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
# `opening_round` (`lean_ethereum.py:1231-1252` at leanVM `914612b6`, G below)

One fold round of CYWZ26's affine combiner (`foldRound`, `Statement/LeanVmVerifier.lean`): the
five scalars `u0, v0, c0, v1, c1`, a grind and `α`, then `β`; `α` stored for the point and, with
`β`, for the queries' row folds, and the claim folded at `α`.

* `roundBody`: its core IR (`core7_body`, by kernel evaluation);
* `MeaningOpeningRound`: what a call establishes, over the carried sponge (`rdS2`, `rdG2`,
  `Fs.squeeze`);
* `opening_round_sound`: the core IR gives the meaning, under `grind_check_Spec 9`, on a memory
  image whose `tabs` holds the bit windows;
* `opening_round_run`: the meaning runs `foldRound st` for every `st` with that claim.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The template -/

/-- `opening_round`'s body (G:1231-1252): the capacity copied, the four scalars `u0, v0, c0, v1`
and their permutation, `c1` and the grind's nonce and permutation, `α`, the squeeze of `β`, the
stores, the claim. -/
def roundBody : List Stmt :=
  ((List.range 5).map fun i ↦ .atom (.copy (.n (10 + i)) (.n i))) ++
  fsNextT (.n 5) 0 15 ++ fsNextT (.n 5) 1 18 ++ fsNextT (.n 5) 2 21 ++ fsNextT (.n 5) 3 24 ++
  [keccakA (permIns 4 [.n 16, .n 17, .n 19, .n 20, .n 22, .n 23, .n 25, .n 26] 47 (osRun 10 5))
    (osRun 27 13)] ++
  fsNextT (.n 5) 4 40 ++ fsNonceT (.n 5) 5 43 ++ padRunT 46 ++
  [keccakA (permIns 2 [.n 41, .n 42, .n 44, .n 45] 47 (osRun 35 5)) (osRun 51 13),
    .call "grind_check__L9" [.n 52, .n 7] []] ++
  challengeT (.n 51) 64 ++
  [keccakA (permIns 0 [] 47 (osRun 59 5)) (osRun 65 13)] ++ challengeT (.n 65) 78 ++
  [osLd 64 8 0, osLd 64 9 0, osLd 78 9 1,
    osMul 79 64 18, osAdd 80 15 79, osMul 81 78 21, osAdd 82 80 81, osAdd 83 6 18,
    osMul 84 64 24, osAdd 85 83 84, osMul 86 78 40, osAdd 87 85 86] ++
  ((List.range 5).map fun i ↦ osCp (88 + i) (73 + i)) ++
  [osCst 93 (word 64 0), osMul 94 5 93, osCp 95 94, osAdd 96 82 87, osMul 97 64 96,
    osAdd 98 82 97, .ret [.n 88, .n 89, .n 90, .n 91, .n 92, .n 95, .n 98]]

set_option maxRecDepth 100000 in
theorem core7_body : Fn.body Data.core7 = roundBody := stmtsEqb_sound (by decide +kernel)

theorem core7_params : Fn.params Data.core7 = (List.range 10).map V.n := rfl

theorem find_opening_round : coreProgram.find? "opening_round" = some Data.core7 :=
  Program.find?_of_indexOf? (j := 7) (by decide +kernel) rfl

/-! ## The meaning -/

/-- The sponge before the grind: the five scalars absorbed. -/
def rdS2 (fs : List E) (m : List E) : Fs := (⟨fs, []⟩ : Fs).absorbAll m dsObserve

/-- `α` and the sponge after it. -/
def rdG2 (fs : List E) (m : List E) (n2 : E) : E × Fs :=
  (rdS2 fs m).grindSqueeze _root_.LeanVM.Parameters.Whir.foldGrindingBits n2

/-- The fold round's claim (G:1250-1252): `side0 + α(side0 + side1)`. -/
def roundClaim (claim alpha beta u0 v0 c0 v1 c1 : E) : E :=
  let side0 := u0 + alpha * v0 + beta * c0
  side0 + alpha * (side0 + (claim + v0 + alpha * v1 + beta * c1))

/-- **`opening_round(fs0..fs4, cursor, claim, tabs, alphas, coefs)`** (G:1231-1252): the six
stream words at the cursor `u0, v0, c0, v1, c1, n2`; from the carried capacity with nothing
waiting, the five scalars are absorbed, the grind passes and draws `α`, then `β` is squeezed;
`α` is stored at `alphas`, `α, β` at `coefs`; the function returns the capacity after `β`, the
cursor six words on and the folded claim. -/
def MeaningOpeningRound (rd : Reader) : List E → List E → Prop
  | [f0, f1, f2, f3, f4, cur, claim, _, gp, cp], rets =>
    ∃ u0 v0 c0 v1 c1 n2 : E, ReadsAt rd cur [u0, v0, c0, v1, c1, n2] ∧
      let fs := [f0, f1, f2, f3, f4]
      let m := [u0, v0, c0, v1, c1]
      let ga := rdG2 fs m n2
      let gb := ga.2.squeeze
      (rdS2 fs m).GrindOk _root_.LeanVM.Parameters.Whir.foldGrindingBits n2 ∧
        LoadHolds rd gp 0 ga.1 ∧ LoadHolds rd cp 0 ga.1 ∧ LoadHolds rd cp 1 gb.1 ∧
        rets = gb.2.cap ++ [cur * gen ^ 6, roundClaim claim ga.1 gb.1 u0 v0 c0 v1 c1]
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
  obtain ⟨c10, c11, c12, c13, c14, lu0, pu0, lv0, pv0, lc0, pc0, lv1, pv1, k1, lc1, pc1, ln2, pn2,
    pad, k2, g2, ch1, k3, ch2, sg, sa, sb, e79, e80, e81, e82, e83, e84, e85, e86, e87,
    c88, c89, c90, c91, c92, e93, e94, e95, e96, e97, e98, hret⟩ := h
  subst hp hret
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.getD_cons_succ, List.getD_cons_zero] at ht ⊢
  have hb : _root_.LeanVM.Parameters.Whir.foldGrindingBits ≠ 0 := by decide
  obtain ⟨pd, z1, z2, z3, z4⟩ := pad
  have p15 := fsPackT_cells pu0
  have p18 := fsPackT_cells pv0
  have p21 := fsPackT_cells pc0
  have p24 := fsPackT_cells pv1
  have p40 := fsPackT_cells pc1
  have p43 := fsPackT_cells pn2
  simp only [Prod.ext_iff, Nat.reduceAdd] at p15 p18 p21 p24 p40 p43 z1 z2 z3 z4
  set fs := [σ (V.n 0), σ (V.n 1), σ (V.n 2), σ (V.n 3), σ (V.n 4)] with hfs
  -- the four scalars
  have K1 := keccakA_fs (s := ⟨fs, [(σ (.n 15), dsObserve), (σ (.n 18), dsObserve),
      (σ (.n 21), dsObserve), (σ (.n 24), dsObserve)]⟩) k1 (by simp) (by
    simp [permIns, osRun, pendCells, p15.1, p15.2, p18.1, p18.2, p21.1, p21.2, p24.1, p24.2, c10,
      c11, c12, c13, c14, fs, List.range_succ])
  set S1 := (⟨fs, [(σ (.n 15), dsObserve), (σ (.n 18), dsObserve), (σ (.n 21), dsObserve),
    (σ (.n 24), dsObserve)]⟩ : Fs).perm with hS1
  have hs2 : rdS2 fs [σ (.n 15), σ (.n 18), σ (.n 21), σ (.n 24), σ (.n 40)] =
      ⟨capOf S1, [(σ (.n 40), dsObserve)]⟩ := by
    rw [rdS2, absorbAll_five]
  have cap1 : capOf S1 = [σ (.n 35), σ (.n 36), σ (.n 37), σ (.n 38), σ (.n 39)] := by
    simp only [capOf, ← outCell K1 8, ← outCell K1 9, ← outCell K1 10, ← outCell K1 11,
      ← outCell K1 12]
    rfl
  -- the grind
  have K2 := keccakA_fs (s := ⟨capOf S1, [(σ (.n 40), dsObserve), (σ (.n 43), dsPowNonce)]⟩) k2
    (by simp) (by
    simp [permIns, osRun, pendCells, p40.1, p40.2, p43.1, p43.2, z1, z2, z3, z4, cap1,
      List.range_succ])
  have hn2 : (rdS2 fs [σ (.n 15), σ (.n 18), σ (.n 21), σ (.n 24), σ (.n 40)]).nonceState
      (σ (.n 43)) = (⟨capOf S1, [(σ (.n 40), dsObserve), (σ (.n 43), dsPowNonce)]⟩ : Fs).perm := by
    rw [hs2]; simp [Fs.nonceState, Fs.absorb, rateScalars]
  rw [← hn2] at K2
  have G2 := ((hg hκ hw L _ _ ht) []).mp (grindCheckName_nine ▸ g2)
  obtain ⟨gok2, hα, hs3⟩ := grindSqueeze_cells hb (σ (.n 43)) _ _ (outCell K2 0) (outCell K2 1) G2.2
  set S3 := (rdS2 fs [σ (.n 15), σ (.n 18), σ (.n 21), σ (.n 24), σ (.n 40)]).nonceState
    (σ (.n 43)) with hS3
  have cap3 : capOf S3 = [σ (.n 59), σ (.n 60), σ (.n 61), σ (.n 62), σ (.n 63)] := by
    simp only [capOf, ← outCell K2 8, ← outCell K2 9, ← outCell K2 10, ← outCell K2 11,
      ← outCell K2 12]
    rfl
  -- β
  have K3 := keccakA_fs (s := ⟨capOf S3, []⟩) k3 (by simp) (by
    simp [permIns, osRun, pendCells, z1, z2, z3, z4, cap3, List.range_succ])
  set S4 := (⟨capOf S3, []⟩ : Fs).perm with hS4
  have hβ : σ (.n 78) = challengeOf S4 := challengeT_value ch2 (outCell K3 0)
  have hG2 : rdG2 fs [σ (.n 15), σ (.n 18), σ (.n 21), σ (.n 24), σ (.n 40)] (σ (.n 43)) =
      (σ (.n 51), ⟨capOf S3, []⟩) := by
    rw [rdG2, Prod.ext_iff]; exact ⟨hα, hs3⟩
  refine ⟨σ (.n 15), σ (.n 18), σ (.n 21), σ (.n 24), σ (.n 40), σ (.n 43), ?_, ?_⟩
  · intro k hk
    simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    · exact lu0
    · exact lv0
    · exact lc0
    · exact lv1
    · exact lc1
    · exact ln2
  · simp only [← hfs]
    simp only [hG2, Fs.squeeze, ← hS4]
    refine ⟨gok2, ?_, ?_, ?_, ?_⟩
    · rw [← ch1]; exact sg
    · rw [← ch1]; exact sa
    · rw [← hβ]; exact sb
    · rw [e95, e94, e93, show (64 : ℕ) = 2 ^ 6 by rfl, word_two_pow (by decide), c88, c89,
        c90, c91, c92, e98, e97, e96, e82, e81, e80, e79, e87, e86, e85, e84, e83, ← ch1, ← hβ]
      simp only [capOf, ← outCell K3 8, ← outCell K3 9, ← outCell K3 10, ← outCell K3 11,
        ← outCell K3 12, roundClaim]
      rfl

/-! ## The run -/

/-- **`opening_round`'s meaning runs the Spec's `foldRound`**: from the carried capacity `fs` with
nothing waiting, the six words read, the grind passing, `foldRound st` returns the state with the
claim folded at `α` and `α` appended, and the round's `α, β`; the sponge left is the one after
`β`. -/
theorem opening_round_run (st : WhirState) (fs : List E) (u0 v0 c0 v1 c1 n2 : E)
    (h2 : (rdS2 fs [u0, v0, c0, v1, c1]).GrindOk _root_.LeanVM.Parameters.Whir.foldGrindingBits
      n2) :
    RunsTo (foldRound st) ⟨fs, []⟩ [u0, v0, c0, v1, c1, n2]
      ({ st with
          claim := roundClaim st.claim (rdG2 fs [u0, v0, c0, v1, c1] n2).1
            (rdG2 fs [u0, v0, c0, v1, c1] n2).2.squeeze.1 u0 v0 c0 v1 c1,
          alphas := st.alphas ++ [(rdG2 fs [u0, v0, c0, v1, c1] n2).1] },
        ⟨(rdG2 fs [u0, v0, c0, v1, c1] n2).1, (rdG2 fs [u0, v0, c0, v1, c1] n2).2.squeeze.1⟩)
      (rdG2 fs [u0, v0, c0, v1, c1] n2).2.squeeze.2 := by
  have hb : _root_.LeanVM.Parameters.Whir.foldGrindingBits ≠ 0 := by decide
  have g2 := runsToG_grind hb (rdS2 fs [u0, v0, c0, v1, c1]) n2 (h2.resolve_left hb)
  have e2 : rdG2 fs [u0, v0, c0, v1, c1] n2 =
      (challengeOf ((rdS2 fs [u0, v0, c0, v1, c1]).nonceState n2),
        ⟨capOf ((rdS2 fs [u0, v0, c0, v1, c1]).nonceState n2), []⟩) := Fs.grindSqueeze_pos _ hb _
  have es : rdS2 fs [u0, v0, c0, v1, c1] =
      (((((⟨fs, []⟩ : Fs).absorb u0 dsObserve).absorb v0 dsObserve).absorb c0 dsObserve).absorb
        v1 dsObserve).absorb c1 dsObserve := rfl
  rw [e2]
  rw [es] at g2 ⊢
  have r := (runsTo_readE _ u0).bind (f := fun u0 => do
      let v0 ← VerifierProgram.readScalar
      let c0 ← VerifierProgram.readScalar
      let v1 ← VerifierProgram.readScalar
      let c1 ← VerifierProgram.readScalar
      let u1 := st.claim + v0
      VerifierProgram.grindProofOfWork _root_.LeanVM.Parameters.Whir.foldGrindingBits
      let alpha ← VerifierProgram.sampleChallenge
      let beta ← VerifierProgram.sampleChallenge
      let claim := (1 + alpha) * (u0 + alpha * v0 + beta * c0) +
        alpha * (u1 + alpha * v1 + beta * c1)
      return ({ st with claim := claim, alphas := st.alphas ++ [alpha] },
        (⟨alpha, beta⟩ : FoldRound)))
    ((runsTo_readE _ v0).bind ((runsTo_readE _ c0).bind ((runsTo_readE _ v1).bind
      ((runsTo_readE _ c1).bind (g2.bindFrom ((runsFromG_sample _ _).bind ((runsTo_sampleE _).bind
        (runsTo_ret _ _))))))))
  refine RunsTo.of_eq r rfl rfl ?_ rfl
  simp only [Fs.squeeze, roundClaim]
  congr 2
  ring

end
end LeanVM.Guest.B1.Whir
