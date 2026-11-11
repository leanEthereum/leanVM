/-
  LeanVM.Guest.B1.Whir.Commit

  A level's next commitment, its out-of-domain sample and the proof of work after it: the
  template's block runs the Spec's `levelMid` and `grindP`.
-/

module

public import LeanVM.Guest.B1.Whir.Folds
public import LeanVM.Guest.B1.Bits.Meaning
public import LeanVM.Guest.B1.Merkle.Climb

/-!
# The next commitment (TRIAGE G #42, G:1494-1553)

A level that is not the last reads the next commitment's root (two scalars, checked canonical,
stored in `level_roots`), samples its out-of-domain point (`opening_ood_point`, stored in
`ood_z`), reads the point's value and the claim's intro message (stored in `ood`), then the
proof-of-work nonce, absorbs the three scalars and the nonce and permutes: `grind_check` reads
the permutation's first cell. In the Spec (V:1798-1811) that is `levelMid` (the commitment,
`sampleN`, `readE`, `sumcheckRoundPoly`) and the level's `grindP`.

* `allOk_fsPackT`, `allOk_fsNextT`, `allOk_challengeT`: B1-a's inline templates, flat.
* `levelMid_grind_run`: the Spec's side, from the scalars read and the nonce's proof of work.
* `osCommit_sound`: the template's block, with `grind_check`'s call, runs it.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-! ## The inline templates, flat -/

theorem allOk_fsPackT (x : V) (b t : ℕ) : AllOk C rd σ (fsPackT x b t) ↔ FsPackOk σ x b t := by
  have h := holdsList_flat (C := C) (rd := rd) (σ := σ) (fsPackT x b t) rfl True (fun _ ↦ True)
  rw [holds_fsPackT] at h
  simpa using h.symm

theorem allOk_fsNextT (cur : V) (off b : ℕ) :
    AllOk C rd σ (fsNextT cur off b) ↔
      LoadHolds rd (σ cur) off (σ (.n b)) ∧ FsPackOk σ (.n b) (b + 1) dsObserve := by
  have h := holdsList_flat (C := C) (rd := rd) (σ := σ) (fsNextT cur off b) rfl True (fun _ ↦ True)
  rw [holds_fsNextT] at h
  simpa using h.symm

theorem allOk_challengeT (s0 s1 : V) (b : ℕ) :
    AllOk C rd σ (challengeT s0 s1 b) ↔ ChallengeOk σ s0 s1 b := by
  have h := holdsList_flat (C := C) (rd := rd) (σ := σ) (challengeT s0 s1 b) rfl True
    (fun _ ↦ True)
  rw [holds_challengeT] at h
  simpa using h.symm

/-- A read through the cursor's base at an offset past it. -/
theorem load_cur {cb : E} {co i : ℕ} {w : E} (h : LoadHolds rd cb (co + i) w) :
    LoadHolds rd (cb * gen ^ co) i w := (loadHolds_mul_gen_pow rd cb co i w).mpr h

/-- Words read at a cursor's base past its offset. -/
theorem readsAt_cur {cb : E} {co : ℕ} {xs : List E}
    (h : ∀ i (hi : i < xs.length), LoadHolds rd cb (co + i) xs[i]) : ReadsAt rd (cb * gen ^ co) xs :=
  fun i hi ↦ load_cur (h i hi)

theorem squeezeN_length : ∀ (n : ℕ) (s : Fs), (s.squeezeN n).1.length = n
  | 0, _ => rfl
  | n + 1, s => by simp only [Fs.squeezeN, List.length_cons, squeezeN_length n]

/-! ## The Spec's side -/

theorem squeezeN_pend_nil : ∀ (k : ℕ) (t : Fs), t.pend = [] → (t.squeezeN k).2.pend = []
  | 0, _, h => h
  | k + 1, t, _ => squeezeN_pend_nil k t.squeeze.2 rfl

theorem squeezeN_succ_pend (k : ℕ) (s : Fs) : (s.squeezeN (k + 1)).2.pend = [] :=
  squeezeN_pend_nil k s.squeeze.2 rfl

/-- The Spec's round polynomial of three coefficients, the two sent read. -/
theorem runsTo_round3 (s : Fs) (claim c0 c2 : E) :
    RunsTo (sumcheckRoundPoly 3 claim none) s [c0, c2] [c0, claim + c2, c2]
      ((s.absorb c0 dsObserve).absorbAll [c2] dsObserve) := by
  have hr0 := runsTo_readE s c0
  have hr1 := runsTo_readN (s.absorb c0 dsObserve) [c2]
  have := hr0.bind (f := fun c ↦ do
      let tail ← VerifierProgram.readScalars 1
      return c :: (claim + sumE tail) :: tail)
    (hr1.bind (f := fun tail ↦ (pure (c0 :: (claim + sumE tail) :: tail) : VerifierProgram
        (List E)))
      (runsTo_ret _ _))
  simpa [sumcheckRoundPoly, sumE_single] using this

/-- **`levelMid` then `grindP`** (V:1798-1811) on the carried sponge with two scalars waiting:
the root's two scalars, the out-of-domain point squeezed from the four waiting scalars, its value
and intro read, the nonce's proof of work on the permutation after it. -/
theorem levelMid_grind_run (F : Fs) (ra rb y c0 c2 nonce : E)
    {d : Digest} (hd : digestFromHalves (ra, rb) = some d) {m : ℕ} (hm : 1 ≤ m)
    (next : Whir.Level) (rest : List Whir.Level) (roots : List (Digest × ℕ × ℕ))
    (hpow : powOk Whir.queryGrindingBits
      ((⟨((F.absorbAll [ra, rb] dsObserve).squeezeN m).2.cap,
        [(y, dsObserve), (c0, dsObserve), (c2, dsObserve), (nonce, dsPowNonce)]⟩ : Fs).perm |>
        challengeOf) = true) :
    RunsWith (do
        let r ← levelMid m (next :: rest)
        VerifierProgram.grindProofOfWork Whir.queryGrindingBits
        pure r)
      F [ra, rb, y, c0, c2, nonce] [] roots
      ([], [(y, [c0, y + c2, c2], fun x ↦ eqEval ((F.absorbAll [ra, rb] dsObserve).squeezeN m).1 x)])
      ⟨capOf (⟨((F.absorbAll [ra, rb] dsObserve).squeezeN m).2.cap,
        [(y, dsObserve), (c0, dsObserve), (c2, dsObserve), (nonce, dsPowNonce)]⟩ : Fs).perm, []⟩
      (roots ++ [(d, levelShape m next (3 * 2 ^ next.fold))]) := by
  set hw := levelShape m next (3 * 2 ^ next.fold)
  set F1 := F.absorbAll [ra, rb] dsObserve
  set z := (F1.squeezeN m).1
  set F2 := (F1.squeezeN m).2
  have hp2 : F2.pend = [] := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact squeezeN_succ_pend k F1
  have e : (do
        let r ← levelMid m (next :: rest)
        VerifierProgram.grindProofOfWork Whir.queryGrindingBits
        pure r) =
      (VerifierProgram.readCommitment hw.1 hw.2).bind fun _ ↦ (VerifierProgram.sampleChallenges m).bind fun zz ↦ VerifierProgram.readScalar.bind fun yv ↦
        (sumcheckRoundPoly 3 yv none).bind fun intro ↦ (VerifierProgram.grindProofOfWork Whir.queryGrindingBits).bind
          fun _ ↦ VerifierProgram.ret (([] : List E), [(yv, intro, fun x ↦ eqEval zz x)]) := by
    simp only [levelMid, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
        VerifierProgram.bind_assoc, VerifierProgram.ret_bind, hw]
  rw [e]
  have h1 : RunsWith (VerifierProgram.readCommitment hw.1 hw.2) F [ra, rb] [] roots () F1 (roots ++ [(d, hw)]) :=
    runsWith_commitP F ra rb hd hw.1 hw.2 roots
  have h2 := RunsTo.withRoots (runsTo_sampleN m F1) (roots ++ [(d, hw)])
  have hF3 : F2.absorb y dsObserve = ⟨F2.cap, [(y, dsObserve)]⟩ := by
    simp [Fs.absorb, hp2, rateScalars]
  have h3 := RunsTo.withRoots (runsTo_readE F2 y) (roots ++ [(d, hw)])
  rw [hF3] at h3
  have h4 := RunsTo.withRoots (runsTo_round3 ⟨F2.cap, [(y, dsObserve)]⟩ y c0 c2)
    (roots ++ [(d, hw)])
  have hF4 : ((⟨F2.cap, [(y, dsObserve)]⟩ : Fs).absorb c0 dsObserve).absorbAll [c2] dsObserve =
      ⟨F2.cap, [(y, dsObserve), (c0, dsObserve), (c2, dsObserve)]⟩ := by
    simp [Fs.absorbAll, Fs.absorb, rateScalars]
  rw [hF4] at h4
  have hF5 : (⟨F2.cap, [(y, dsObserve), (c0, dsObserve), (c2, dsObserve)]⟩ : Fs).absorb nonce
      dsPowNonce = ⟨F2.cap, [(y, dsObserve), (c0, dsObserve), (c2, dsObserve), (nonce, dsPowNonce)]⟩ :=
    by simp [Fs.absorb, rateScalars]
  have h5 := RunsTo.withRoots (runsTo_grindP Whir.queryGrindingBits (by decide)
    ⟨F2.cap, [(y, dsObserve), (c0, dsObserve), (c2, dsObserve)]⟩ nonce
    (by rw [hF5]; exact hpow)) (roots ++ [(d, hw)])
  rw [hF5] at h5
  show RunsWith _ F ([ra, rb] ++ ([] ++ ([y] ++ ([c0, c2] ++ ([nonce] ++ [])))))
    ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ []))))) roots _ _ _
  exact RunsWith.bind' h1 (RunsWith.bind' h2 (RunsWith.bind' h3 (RunsWith.bind' h4
    (RunsWith.bind' h5 (runsWith_ret _ _ _)))))

/-! ## The template's block -/

/-- The packed cells of a scalar are its rate cells, once the first is canonical. -/
theorem packed_cells {x : V} {b t : ℕ} (h : FsPackOk σ x b t) (hc : IsCanonical128 (σ (.n (b + 6)))) :
    σ (.n (b + 6)) = (Keccak.scalarCells (σ x) t).1 ∧ σ (.n (b + 8)) = (Keccak.scalarCells (σ x) t).2 :=
  by have := fsPackT_cells h hc; simp only [Prod.ext_iff] at this; exact this

/-- A sponge's squeezes: the first from its permutation, the rest from its capacity. -/
theorem squeezeN_succ (k : ℕ) (s : Fs) :
    s.squeezeN (k + 1) = (challengeOf s.perm :: ((⟨capOf s.perm, []⟩ : Fs).squeezeN k).1,
      ((⟨capOf s.perm, []⟩ : Fs).squeezeN k).2) := rfl

/-- What a level's next commitment leaves. -/
structure CommitOut (rd : Reader) (σ : Val) (lvl m : ℕ) (st st' : OsSt) (F : Fs)
    (ra rb y c0 c2 nonce : E) (d : Digest) (z : List E) : Prop where
  root : (ra, rb) = digestHalves d
  rootA : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 2) ra
  rootB : LoadHolds rd (σ (.n osRoots)) (2 * lvl + 3) rb
  zlen : z.length = m
  zat : ∀ t (ht : t < z.length), LoadHolds rd (σ (.n osOodz)) ((lvl + 1) * ligColsCap + t) z[t]
  oy : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 1) y
  oc0 : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 2) c0
  oc2 : LoadHolds rd (σ (.n osOod)) ((lvl + 1) * oodSlots + 3) c2
  sponge : F = ⟨st'.fsv σ, []⟩
  cur : st'.cur σ = st.cur σ * gen ^ 6
  fs : st'.fs.length = 5
  mats : MatsOk σ st'.mats

/-- **A level's next commitment** (G:1494-1553), with the grinding check after it: the root's two
halves, the out-of-domain point, its value and intro, the nonce read at the cursor; they run the
Spec's `levelMid` and `grindP`. -/
theorem osCommit_sound
    (hCan : ∀ args rets, C "assert_canonical" args rets → MeaningAssertCanonical args rets)
    {lvl : ℕ} {lv : OsLv}
    (hOod : ∀ args rets, C ("opening_ood_point__L" ++ natStr lv.logCols) args rets →
      MeaningOpeningOodPoint lv.logCols rd args rets)
    (hGr : ∀ args rets, C ("grind_check__L" ++ natStr lv.grind) args rets →
      MeaningGrindCheck Whir.queryGrindingBits args rets)
    {plan : List (ℕ × ℕ × ℕ)} {st : OsSt} (hfs : st.fs.length = 5) (hmats : MatsOk σ st.mats)
    (hm : 1 ≤ lv.logCols) (hlvl : (lvl + 1) * ligColsCap < u128Bound)
    (hok : AllOk C rd σ ((osCommit plan lvl lv st).1 ++
      [.call ("grind_check__L" ++ natStr lv.grind) [.n (osCommit plan lvl lv st).2.2] []]))
    (next : Whir.Level) (rest : List Whir.Level) (roots : List (Digest × ℕ × ℕ)) :
    ∃ (ra rb y c0 c2 nonce : E) (d : Digest) (z : List E) (F' : Fs),
      ReadsAt rd (st.cur σ) [ra, rb, y, c0, c2, nonce] ∧
      CommitOut rd σ lvl lv.logCols st (osCommit plan lvl lv st).2.1 F' ra rb y c0 c2 nonce d z ∧
      RunsWith (do
          let r ← levelMid lv.logCols (next :: rest)
          VerifierProgram.grindProofOfWork Whir.queryGrindingBits
          pure r)
        (st.F σ) [ra, rb, y, c0, c2, nonce] [] roots
        ([], [(y, [c0, y + c2, c2], fun x ↦ eqEval z x)]) F'
        (roots ++ [(d, levelShape lv.logCols next (3 * 2 ^ next.fold))]) := by
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := fold_args st hfs
  obtain ⟨m', hm'⟩ : ∃ m', lv.logCols = m' + 1 := ⟨lv.logCols - 1, by omega⟩
  simp only [osCommit, hf, allOk_append, allOk_cons, allOk_nil, and_true, allOk_fsPackT,
    allOk_fsNextT, StmtOk, Atom.Holds, List.zipIdx_cons, List.zipIdx_nil, List.map_cons,
    List.map_nil, List.range_succ, List.range_zero, List.nil_append, List.cons_append, osRun,
    and_assoc, Nat.add_assoc, Nat.reduceAdd, Nat.add_zero, Nat.zero_add] at hok
  obtain ⟨-, -, -, -, -, P0, P1, L23, P23, L33, P33, can23, can33, R23, R33, hozA, hood, L52,
    P52, L62, P62, L72, P72, S52, S62, S72, L82, e83, e84, e85, e86, e87, P82, hK, hgr⟩ := hok
  set k := st.k
  -- the root's halves are canonical: a digest
  obtain ⟨ca, -⟩ := hCan _ _ can23
  obtain ⟨cb, -⟩ := hCan _ _ can33
  obtain ⟨d, hd⟩ := exists_digest ca cb
  have hdd : digestFromHalves (σ (.n (k + 23)), σ (.n (k + 33))) = some d := by
    rw [hd]; exact digestOfScalars_digestScalars d
  -- the out-of-domain point
  have hood' := hOod _ _ hood
  rw [hm'] at hood'
  obtain ⟨hcan, hpt, hrets⟩ := hood'
  have cnA := packed_cells P0 (hcan _ (by simp))
  have cnB := packed_cells P1 (hcan _ (by simp))
  have cnC := packed_cells P23 (hcan _ (by simp))
  have cnD := packed_cells P33 (hcan _ (by simp))
  have hF1 : (st.F σ).absorbAll [σ (.n (k + 23)), σ (.n (k + 33))] dsObserve =
      ⟨[σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)],
        [(σ (.n st.w0), dsObserve), (σ (.n st.w1), dsObserve), (σ (.n (k + 23)), dsObserve),
          (σ (.n (k + 33)), dsObserve)]⟩ := by
    rw [absorbAll_short _ _ _ (by simp [OsSt.F])]
    simp [OsSt.F, OsSt.fsv, hf]
  generalize hF1g : (⟨[σ (.n f0), σ (.n f1), σ (.n f2), σ (.n f3), σ (.n f4)],
    [(σ (.n st.w0), dsObserve), (σ (.n st.w1), dsObserve), (σ (.n (k + 23)), dsObserve),
      (σ (.n (k + 33)), dsObserve)]⟩ : Fs) = F1 at hF1
  have hS1 : permOf [σ (.n (k + 11)), σ (.n (k + 13)), σ (.n (k + 20)), σ (.n (k + 22)),
      σ (.n (k + 30)), σ (.n (k + 32)), σ (.n (k + 40)), σ (.n (k + 42)), σ (.n f0), σ (.n f1),
      σ (.n f2), σ (.n f3), σ (.n f4)] = F1.perm := by
    rw [← hF1g, perm_eq_cells _ (by simp)]
    simp [pendCells, cnA.1, cnA.2, cnB.1, cnB.2, cnC.1, cnC.2, cnD.1, cnD.2, dsObserve]
  rw [hS1] at hpt hrets
  simp only [Nat.add_sub_cancel] at hpt hrets
  generalize hrg : (⟨capOf F1.perm, []⟩ : Fs).squeezeN m' = rs at hpt hrets
  have hsq : F1.squeezeN lv.logCols = (challengeOf F1.perm :: rs.1, rs.2) := by
    rw [hm', ← hrg]; exact squeezeN_succ m' F1
  -- the absorb of the three scalars and the nonce
  obtain ⟨-, -, hcanK, hout⟩ := keccakA_perm (rd := rd) hK
  have cn52 := packed_cells P52 (hcanK _ (by simp))
  have cn62 := packed_cells P62 (hcanK _ (by simp))
  have cn72 := packed_cells P72 (hcanK _ (by simp))
  have cn82 := packed_cells P82 (hcanK _ (by simp))
  simp only [Nat.add_assoc, Nat.reduceAdd] at cn52 cn62 cn72 cn82
  set S2 := (⟨rs.2.cap, [(σ (.n (k + 52)), dsObserve), (σ (.n (k + 62)), dsObserve),
    (σ (.n (k + 72)), dsObserve), (σ (.n (k + 82)), dsPowNonce)]⟩ : Fs).perm with hS2
  have hS2' : permOf ([V.n (k + 59), V.n (k + 61), V.n (k + 69), V.n (k + 71), V.n (k + 79),
      V.n (k + 81), V.n (k + 94), V.n (k + 96), V.n (k + 83), V.n (k + 84), V.n (k + 85),
      V.n (k + 86), V.n (k + 87)].map σ) = S2 := by
    rw [hS2, perm_eq_cells _ (by simp)]
    simp only [List.map_cons, List.map_nil, e83, e84, e85, e86, e87]
    rw [hrets]
    simp [pendCells, cn52.1, cn52.2, cn62.1, cn62.2, cn72.1, cn72.2, cn82.1, cn82.2, dsObserve,
      dsPowNonce]
  rw [hS2'] at hout
  have o0 : σ (.n (k + 97)) = cellsOfState S2 false 0 := outs_eq hout 0 (by simp)
  have o8 : σ (.n (k + 105)) = cellsOfState S2 false 8 := outs_eq hout 8 (by simp)
  have o9 : σ (.n (k + 106)) = cellsOfState S2 false 9 := outs_eq hout 9 (by simp)
  have o10 : σ (.n (k + 107)) = cellsOfState S2 false 10 := outs_eq hout 10 (by simp)
  have o11 : σ (.n (k + 108)) = cellsOfState S2 false 11 := outs_eq hout 11 (by simp)
  have o12 : σ (.n (k + 109)) = cellsOfState S2 false 12 := outs_eq hout 12 (by simp)
  -- the proof of work
  obtain ⟨-, -, hlow⟩ := hGr _ _ hgr
  have hpow : powOk Whir.queryGrindingBits (challengeOf S2) = true := by
    have h17 : ((challengeOf S2).limb 0).lane.toNat % 2 ^ Whir.queryGrindingBits = 0 := by
      rw [Keccak.challengeOf_limb0, ← o0]; exact hlow
    exact decide_eq_true h17
  have hrun := levelMid_grind_run (st.F σ) (σ (.n (k + 23))) (σ (.n (k + 33))) (σ (.n (k + 52)))
    (σ (.n (k + 62))) (σ (.n (k + 72))) (σ (.n (k + 82))) hdd hm next rest roots
    (by rw [hF1, hsq]; exact hpow)
  have hoz : σ (.n (k + 46)) = σ (.n osOodz) * gen ^ ((lvl + 1) * ligColsCap) := by
    have h46 := (osMatP_shape plan st.mats osOodz ((lvl + 1) * ligColsCap) (k + 45)).2
      (by unfold ligColsCap; omega)
    have := osMatP_val hmats hlvl hozA
    rw [h46] at this
    exact this
  refine ⟨_, _, _, _, _, _, d, _, _, ?_, ⟨hd, R23, R33, squeezeN_length _ _, ?_, S52, S62, S72, ?_,
    ?_, rfl, osMatsAfter_ok hmats hlvl hozA⟩, hrun⟩
  · refine readsAt_cur fun i hi ↦ ?_
    rcases i with _ | _ | _ | _ | _ | _ | i
    · simpa using L23
    · exact L33
    · exact L52
    · exact L62
    · exact L72
    · exact L82
    · simp only [List.length_cons, List.length_nil] at hi; omega
  · intro t ht
    simp only [hF1, hsq] at ht ⊢
    have := hpt t ht
    rw [hoz, loadHolds_mul_gen_pow] at this
    exact this
  · rw [hF1, hsq]
    simp only [osCommit, OsSt.fsv, List.map_cons, List.map_nil, capOf]
    rw [← hS2, ← o8, ← o9, ← o10, ← o11, ← o12]
  · simp only [osCommit, OsSt.cur, pow_add, mul_assoc]

end
end LeanVM.Guest.B1.Whir
