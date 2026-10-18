/-
  LeanVM.Guest.B1.Tables.GkrBase

  Shared pieces of `verify_bus_gkr`'s and `verify_tables`'s soundness: statements read off a
  function's body by position, and the specification's GKR walk two levels at a time.
-/

module

public import LeanVM.Guest.B1.Main.Basic
public import LeanVM.Guest.B1.Tables.Common
public import LeanVM.Guest.B1.Tables.TCtx
public import LeanVM.Protocol.Compile.Prog

/-!
# Reading a body by position; the GKR walk by layers

A body without `ret` (`Stmt.noRetList`) that holds gives every run of its statements
(`holds_slice`), compared by kernel evaluation (`stmtsEqb`), so a soundness proof reads each fact
it needs off the body at its position: an atom (`holds_atom`), a call, an `fs_next`
(`holds_fsNextAt`), a `squeeze` (`holds_squeezeAt`).

On the specification's side, `gkrLayers` of an even depth is `gkrPairs`, steps of two levels
appended one at a time, and of an odd depth one level first (`gkrLayers_even`, `gkrLayers_odd`);
`sumcheck` runs round by round (`runsTo_sumcheck`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Reading a body by position -/

theorem gkr_noRetList_append (a b : List Stmt) :
    Stmt.noRetList (a ++ b) = (Stmt.noRetList a && Stmt.noRetList b) := by
  induction a with
  | nil => simp [Stmt.noRetList]
  | cons s a ih => simp [Stmt.noRetList, ih, Bool.and_assoc]

section Slices

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **A run of statements of a body without `ret`** holds: `blk`, equal to the statements at
position `n`. -/
theorem holds_slice {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsList C rd σ pre True kret) (n : ℕ) (blk : List Stmt)
    (heq : stmtsEqb blk ((pre.drop n).take blk.length) = true) :
    Stmt.HoldsList C rd σ blk True kret := by
  have hsplit : pre = pre.take n ++ (((pre.drop n).take blk.length) ++
      (pre.drop n).drop blk.length) := by simp
  rw [hsplit] at h hnr
  rw [gkr_noRetList_append, gkr_noRetList_append, Bool.and_eq_true, Bool.and_eq_true] at hnr
  rw [holdsList_append, holdsList_noRet _ hnr.1, holdsList_append,
    holdsList_noRet _ hnr.2.1] at h
  rw [stmtsEqb_sound heq]
  exact h.2.1

/-- One atom of a body without `ret` holds. -/
theorem holds_atom {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsList C rd σ pre True kret) (n : ℕ) (a : Atom)
    (heq : stmtsEqb [.atom a] ((pre.drop n).take 1) = true) : a.Holds rd σ := by
  have := holds_slice hnr h n [.atom a] heq
  simpa [Stmt.HoldsList, Stmt.Holds] using this

/-- One call of a body without `ret` holds. -/
theorem holds_call {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsList C rd σ pre True kret) (n : ℕ) (f : String) (args rets : List V)
    (heq : stmtsEqb [.call f args rets] ((pre.drop n).take 1) = true) :
    C f (args.map σ) (rets.map σ) := by
  have := holds_slice hnr h n [.call f args rets] heq
  simpa [Stmt.HoldsList, Stmt.Holds] using this

/-- One conditional call of a body without `ret` holds. -/
theorem holds_callIf {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsList C rd σ pre True kret) (n : ℕ) (c : V) (f : String) (args : List V)
    (heq : stmtsEqb [.callIf c f args] ((pre.drop n).take 1) = true) :
    σ c ≠ 0 → C f (args.map σ) [] := by
  have := holds_slice hnr h n [.callIf c f args] heq
  simp only [Stmt.HoldsList, Stmt.Holds, and_true] at this
  exact this.2

/-- An `fs_next` of a body without `ret`: the word at the cursor's offset `j`, absorbed. -/
theorem holds_fsNextAt {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsList C rd σ pre True kret) (n : ℕ) (s0 s1 cur : V) (j b : ℕ)
    (heq : stmtsEqb (fsNextT s0 s1 cur j b) ((pre.drop n).take 13) = true) :
    LoadHolds rd (σ cur) j (σ (.n b)) ∧ ∃ cv, (σ s0, σ s1) = digestScalars cv ∧
      (σ (.n (b + 13)), σ (.n (b + 14))) = digestScalars (obsCv cv (σ (.n b))) := by
  obtain ⟨⟨hl, cv, hcv, hv⟩, -⟩ := (holds_fsNextT (C := C) (rd := rd) (σ := σ) s0 s1 cur j b True
    kret).mp (holds_slice hnr h n _ (by
      rw [show (fsNextT s0 s1 cur j b).length = 13 by simp [fsNextT, fsCompressT]]; exact heq))
  refine ⟨hl, cv, hcv, ?_⟩
  have h12 := hv 12 (by omega) (by omega)
  have h13 := hv 13 (by omega) (by omega)
  rw [show b + 1 + 12 = b + 13 by omega] at h12
  rw [show b + 1 + 13 = b + 14 by omega] at h13
  rw [h12, h13, fsVals, fsVals, absorbCv_one]

/-- A `squeeze` of a body without `ret`: the new state and the challenge. -/
theorem holds_squeezeAt {pre : List Stmt} (hnr : Stmt.noRetList pre = true)
    (h : Stmt.HoldsList C rd σ pre True kret) (n : ℕ) (s0 s1 : V) (b : ℕ)
    (heq : stmtsEqb (squeezeT s0 s1 b) ((pre.drop n).take 14) = true) :
    ∃ cv, (σ s0, σ s1) = digestScalars cv ∧
      (σ (.n (b + 5)), σ (.n (b + 6))) = digestScalars (sqCv cv) ∧
      σ (.n (b + 13)) = challengeOf (sqCv cv) := by
  obtain ⟨⟨cv, hcv, hv⟩, -⟩ := (holds_squeezeT (C := C) (rd := rd) (σ := σ) s0 s1 b True kret).mp
    (holds_slice hnr h n _ (by
      rw [show (squeezeT s0 s1 b).length = 14 by simp [squeezeT, squeezeStateT, challengeT]]
      exact heq))
  refine ⟨cv, hcv, ?_, hv 13 (by omega)⟩
  rw [hv 5 (by omega), hv 6 (by omega)]
  simp only [sqVals, sqStateVals, absorbCv_sq]

end Slices

/-- A function whose body is `pre ++ [ret vs]`, `pre` without `ret`: its relation is some
valuation of its parameters satisfying `pre` and returning `vs`. -/
theorem rel_pre {rd : Reader} {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    {pre : List Stmt} {vs : List V} (hb : fn.body = pre ++ [.ret vs])
    (hnr : Stmt.noRetList pre = true) {args rets : List E}
    (h : coreProgram.Rel rd f args rets) :
    ∃ σ : Val, fn.params.map σ = args ∧
      Stmt.HoldsList (coreProgram.Rel rd) rd σ pre True (fun rs => rs = rets) ∧
      vs.map σ = rets := by
  rw [rel_iff_sem hf, hb] at h
  obtain ⟨σ, hp, hb⟩ := h
  rw [holdsList_append, holdsList_noRet _ hnr] at hb
  exact ⟨σ, hp, hb.1, hb.2⟩

/-! ## Memory -/

theorem loadHolds_gen_pow_mul {rd : Reader} {p : E} {j k : ℕ} {w : E} :
    LoadHolds rd (p * gen ^ j) k w ↔ LoadHolds rd p (j + k) w :=
  loadHolds_mul_gen_pow rd p j k w

/-- Words read at `p·g^a` are words read at `p` from offset `a`. -/
theorem readsAt_gen_pow_mul {rd : Reader} {p : E} {a : ℕ} {xs : List E} :
    ReadsAt rd (p * gen ^ a) xs ↔ ∀ k (hk : k < xs.length), LoadHolds rd p (a + k) xs[k] := by
  simp only [ReadsAt, loadHolds_gen_pow_mul]

/-- Two runs of words, one after the other. -/
theorem readsAt_append_pow {rd : Reader} {p : E} {xs ys : List E} (hx : ReadsAt rd p xs)
    (hy : ReadsAt rd (p * gen ^ xs.length) ys) : ReadsAt rd p (xs ++ ys) := by
  intro k hk
  rw [readsAt_gen_pow_mul] at hy
  by_cases h : k < xs.length
  · rw [List.getElem_append_left h]; exact hx k h
  · rw [List.getElem_append_right (by omega)]
    have := hy (k - xs.length) (by simp at hk; omega)
    rwa [show xs.length + (k - xs.length) = k by omega] at this

/-! ## Runs -/

theorem runsTo_require {c : Prop} [Decidable c] (hc : c) (cv : Digest) :
    RunsTo (Prog.require c) cv [] () cv := by
  simp only [Prog.require, hc, ↓reduceIte]
  exact runsTo_ret () cv

theorem runsTo_sampleN_two (cv : Digest) :
    RunsTo (Prog.sampleN 2) cv [] [challengeOf (sqCv cv), challengeOf (sqCv (sqCv cv))]
      (sqCv (sqCv cv)) :=
  runsTo_sampleN 2 cv

theorem runsTo_sampleN_one (cv : Digest) :
    RunsTo (Prog.sampleN 1) cv [] [challengeOf (sqCv cv)] (sqCv cv) :=
  runsTo_sampleN 1 cv

theorem sumcheck_cons_eq (claim : E) (count : ℕ) (e : Option E) (es : List (Option E)) :
    sumcheck claim count (e :: es) =
      roundPoly count claim e >>= fun r =>
        sumcheck r.1 count es >>= fun q => pure (r.2 :: q.1, q.2) := by
  simp only [sumcheck, roundPoly, bind_assoc, pure_bind]

/-- A round, then the rest of a sumcheck. -/
theorem RunsTo.sumcheck_cons {claim claim' ch fin : E} {count : ℕ} {e : Option E}
    {es : List (Option E)} {cv cv1 cv2 : Digest} {xs ys pt : List E}
    (h1 : RunsTo (roundPoly count claim e) cv xs (claim', ch) cv1)
    (h2 : RunsTo (sumcheck claim' count es) cv1 ys (pt, fin) cv2) :
    RunsTo (sumcheck claim count (e :: es)) cv (xs ++ ys) (ch :: pt, fin) cv2 := by
  rw [sumcheck_cons_eq]
  exact (h1.bind (RunsTo.bind (f := fun q => (pure (ch :: q.1, q.2) : Prog (List E × E))) h2
    (runsTo_ret _ _))).of_eq (by simp) rfl rfl

/-- **A sumcheck, round by round**: round `r` runs from `cvr r` on the words `ws r` to the claim
`cl (r + 1)` and the challenge `ch r`. -/
theorem runsTo_sumcheck (count : ℕ) :
    ∀ (es : List (Option E)) (cl : ℕ → E) (cvr : ℕ → Digest) (ws : ℕ → List E) (ch : ℕ → E),
      (∀ r (hr : r < es.length),
        RunsTo (roundPoly count (cl r) es[r]) (cvr r) (ws r) (cl (r + 1), ch r) (cvr (r + 1))) →
      RunsTo (sumcheck (cl 0) count es) (cvr 0) ((List.range es.length).flatMap ws)
        ((List.range es.length).map ch, cl es.length) (cvr es.length)
  | [], cl, cvr, ws, ch, _ => runsTo_ret _ _
  | e :: es, cl, cvr, ws, ch, h => by
    have ih := runsTo_sumcheck count es (fun r => cl (r + 1)) (fun r => cvr (r + 1))
      (fun r => ws (r + 1)) (fun r => ch (r + 1)) (fun r hr => h (r + 1) (by simp; omega))
    refine (RunsTo.sumcheck_cons (h 0 (by simp)) ih).of_eq ?_ ?_ rfl
    · simp only [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    · simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      rfl

/-! ## The GKR walk by layers -/

/-- `k` steps of two levels, appended one at a time. -/
def gkrPairs : ℕ → GkrState → Prog GkrState
  | 0, s => pure s
  | k + 1, s => gkrPairs k s >>= gkrStep 2

theorem gkrPairs_succ' (k : ℕ) (s : GkrState) :
    gkrPairs (k + 1) s = gkrStep 2 s >>= gkrPairs k := by
  induction k generalizing s with
  | zero => simp only [gkrPairs, pure_bind, bind_pure]
  | succ k ih => rw [gkrPairs, ih, bind_assoc]; rfl

theorem gkrLayers_even (k : ℕ) (s : GkrState) : gkrLayers (2 * k) s = gkrPairs k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, gkrLayers, gkrPairs_succ']
    simp only [show ¬ (2 * k % 2 = 1) by omega, ↓reduceIte]
    congr 1
    funext t
    exact ih t

theorem gkrLayers_odd (k : ℕ) (s : GkrState) :
    gkrLayers (2 * k + 1) s = gkrStep 1 s >>= gkrPairs k := by
  cases k with
  | zero => rw [gkrLayers]; rfl
  | succ k =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, gkrLayers]
    simp only [show 2 * k + 1 = 1 + 2 * k by omega, show (1 + 2 * k) % 2 = 1 by omega, ↓reduceIte]
    congr 1
    funext t
    rw [show 1 + 2 * k + 1 = 2 * (k + 1) by omega, gkrLayers_even]

theorem runsTo_readN_of_length {n : ℕ} (cv : Digest) {xs : List E} (h : xs.length = n) :
    RunsTo (Prog.readN n) cv xs xs (obsAll cv xs) := by
  subst h; exact runsTo_readN cv xs

/-- **A GKR step of `step` levels** from the state of `cv`: its combiner `lam`, the sumcheck over
the point (`hsc`), the three trees' `2^step` children, the products' check, and `step` new
coordinates. -/
theorem runsTo_gkrStep (step : ℕ) {cv cvS : Digest} {s : GkrState} {ws chs c0 c1 c2 : List E}
    {cl : E}
    (hsc : RunsTo (sumcheck (polyEval s.values (challengeOf (sqCv cv))) (2 ^ step + 1)
      (s.point.map some)) (sqCv cv) ws (chs, cl) cvS)
    (h0 : c0.length = 2 ^ step) (h1 : c1.length = 2 ^ step) (h2 : c2.length = 2 ^ step)
    (hreq : cl = polyEval [prodE c0, prodE c1, prodE c2] (challengeOf (sqCv cv))) :
    RunsTo (gkrStep step s) cv (ws ++ (c0 ++ (c1 ++ c2)))
      ⟨[c0, c1, c2].map (multilinearEval ·
          (sqAll step (obsAll (obsAll (obsAll cvS c0) c1) c2)).1),
        (sqAll step (obsAll (obsAll (obsAll cvS c0) c1) c2)).1 ++ chs⟩
      (sqAll step (obsAll (obsAll (obsAll cvS c0) c1) c2)).2 := by
  refine RunsTo.of_eq (xs := [] ++ (ws ++ (c0 ++ (c1 ++ (c2 ++ ([] ++ ([] ++ []))))))) ?_
    (by simp) rfl rfl
  unfold gkrStep
  refine (runsTo_sampleE cv).bind ?_
  refine hsc.bind ?_
  refine (runsTo_readN_of_length _ h0).bind ?_
  refine (runsTo_readN_of_length _ h1).bind ?_
  refine (runsTo_readN_of_length _ h2).bind ?_
  refine (runsTo_require hreq _).bind ?_
  refine (runsTo_sampleN step _).bind ?_
  exact runsTo_ret _ _

end
end LeanVM.Guest.B1.VerifySub
