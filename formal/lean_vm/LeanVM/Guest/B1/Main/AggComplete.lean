/-
  LeanVM.Guest.B1.Main.AggComplete

  B1 for `aggregate_claims` (G:3319-3486; TRIAGE #77), completeness: for every pointer of its
  `HeapBuf`s and every memory holding the honest words there, the batching's claim is stored.
-/

module

public import LeanVM.Guest.B1.Main.AggSound
public import LeanVM.Guest.B1.Main.AggLoop99C
public import LeanVM.Guest.B1.Main.AggEqtreeC

/-!
# `aggregate_claims`, completely

`aggRun cs h` is `Node.batch`'s run (`batch_spec`) as its parts: the transcript's states, the
lambdas, the two sumchecks' points and claims. `AggPtrs` names the fifteen `HeapBuf`s the body
allocates, and `AggMem` says the memory holds there what the guest writes: the sumcheck
messages, the rows' pointers, the transcript states, the lambdas, the running claims and weights,
the two points and the two `eqtree`s. `aggregate_claims_complete`: then `aggregate_claims` holds
on the claims at its buffers and the batched claim at `defer_stmt`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

variable {rd : Reader}

/-! ## The batching's run -/

/-- A child's bytecode term. -/
def bcTerm (c : ChildClaims) (l : E × E) : E :=
  l.1 * c.fresh.bytecodeValue + l.2 * c.carried.bytecodeValue

/-- A child's bytecode weight at `r`. -/
def bcWeight (r : List E) (c : ChildClaims) (l : E × E) : E :=
  l.1 * eqEval c.fresh.bytecodePoint r + l.2 * eqEval c.carried.bytecodePoint r

/-- A child's matrix term. -/
def mtTerm (c : ChildClaims) (l : E × E × E) : E :=
  l.1 * c.fresh.matrixValue + l.2.1 * c.carried.matrixA + l.2.2 * c.carried.matrixB

/-- A child's `A0` weight at `r`. -/
def mtWeightA (r : List E) (c : ChildClaims) (l : E × E × E) : E :=
  l.1 * freshWeight c.fresh r + l.2.1 * eqEval c.carried.matrixPoint r

/-- A child's `B0` weight at `r`. -/
def mtWeightB (r : List E) (c : ChildClaims) (l : E × E × E) : E :=
  l.1 * c.fresh.alpha * freshWeight c.fresh r + l.2.2 * eqEval c.carried.matrixPoint r

/-- The state after absorbing the count. -/
def agCv1 (cs : List ChildClaims) : Digest :=
  obsCv (blake2sBytes batchLabel) (ofK (Parameters.gpow cs.length))

/-- The state after absorbing every child. -/
def agCvA (cs : List ChildClaims) : Digest := obsAll (agCv1 cs) (cs.flatMap childCells)

/-- The bytecode lambdas. -/
def agLB (cs : List ChildClaims) : List (E × E) := (sq2 cs.length (agCvA cs)).1

/-- The bytecode sumcheck's run. -/
def agRb (cs : List ChildClaims) (h : BatchHints) : (List E × E) × Digest :=
  (batchRounds (sumE (List.zipWith bcTerm cs (agLB cs))) h.bytecodeRounds).run
    (sqIt2 (agCvA cs) cs.length)

/-- The matrix lambdas. -/
def agLM (cs : List ChildClaims) (h : BatchHints) : List (E × E × E) :=
  (sq3 cs.length (agRb cs h).2).1

/-- The matrix sumcheck's run. -/
def agRm (cs : List ChildClaims) (h : BatchHints) : (List E × E) × Digest :=
  (batchRounds (sumE (List.zipWith mtTerm cs (agLM cs h))) h.matrixRounds).run
    (sqIt3 (agRb cs h).2 cs.length)

/-! ## The memory -/

/-- The `HeapBuf`s `aggregate_claims` allocates, in allocation order. -/
structure AggPtrs where
  msgB : E
  msgM : E
  frow : E
  crow : E
  absb : E
  lamB : E
  bcc : E
  rs : E
  wB : E
  lamM : E
  mcc : E
  rM : E
  eqR : E
  eqC : E
  wsum : E

/-- **The honest words at the `HeapBuf`s** for the claims `cs` at `fresh`, `carried` and the hints
`h`: the messages, the rows' pointers, the transcript states, the lambdas, the running claims and
weights, the two points, the two `eqtree`s. -/
structure AggMem (rd : Reader) (P : AggPtrs) (fresh carried : E) (cs : List ChildClaims)
    (h : BatchHints) : Prop where
  msgB : ∀ r < 22, LoadHolds rd P.msgB (2 * r) (h.bytecodeRounds.getD r (0, 0)).1 ∧
    LoadHolds rd P.msgB (2 * r + 1) (h.bytecodeRounds.getD r (0, 0)).2
  msgM : ∀ r < 28, LoadHolds rd P.msgM (2 * r) (h.matrixRounds.getD r (0, 0)).1 ∧
    LoadHolds rd P.msgM (2 * r + 1) (h.matrixRounds.getD r (0, 0)).2
  rows : ∀ c < cs.length, LoadHolds rd P.frow c (fresh * gen ^ (106 * c)) ∧
    LoadHolds rd P.crow c (carried * gen ^ (53 * c))
  absb : ∀ c ≤ cs.length,
    LoadHolds rd P.absb (2 * c) (digestScalars (obsAll (agCv1 cs) ((cs.take c).flatMap childCells))).1 ∧
    LoadHolds rd P.absb (2 * c + 1)
      (digestScalars (obsAll (agCv1 cs) ((cs.take c).flatMap childCells))).2
  lamB : ∀ c < cs.length, LoadHolds rd P.lamB (2 * c) ((agLB cs).getD c (0, 0)).1 ∧
    LoadHolds rd P.lamB (2 * c + 1) ((agLB cs).getD c (0, 0)).2
  bcc : ∀ c ≤ cs.length,
    LoadHolds rd P.bcc (3 * c) (digestScalars (sqIt2 (agCvA cs) c)).1 ∧
    LoadHolds rd P.bcc (3 * c + 1) (digestScalars (sqIt2 (agCvA cs) c)).2 ∧
    LoadHolds rd P.bcc (3 * c + 2) (sumE (List.zipWith bcTerm (cs.take c) ((agLB cs).take c)))
  rs : ReadsAt rd P.rs (agRb cs h).1.1
  wB : ∀ c ≤ cs.length, LoadHolds rd P.wB c
    (sumE (List.zipWith (bcWeight (agRb cs h).1.1) (cs.take c) ((agLB cs).take c)))
  lamM : ∀ c < cs.length, LoadHolds rd P.lamM (3 * c) ((agLM cs h).getD c (0, 0, 0)).1 ∧
    LoadHolds rd P.lamM (3 * c + 1) ((agLM cs h).getD c (0, 0, 0)).2.1 ∧
    LoadHolds rd P.lamM (3 * c + 2) ((agLM cs h).getD c (0, 0, 0)).2.2
  mcc : ∀ c ≤ cs.length,
    LoadHolds rd P.mcc (3 * c) (digestScalars (sqIt3 (agRb cs h).2 c)).1 ∧
    LoadHolds rd P.mcc (3 * c + 1) (digestScalars (sqIt3 (agRb cs h).2 c)).2 ∧
    LoadHolds rd P.mcc (3 * c + 2) (sumE (List.zipWith mtTerm (cs.take c) ((agLM cs h).take c)))
  rM : ReadsAt rd P.rM (agRm cs h).1.1
  eqR : ∀ t < 6, ∀ i < 2 ^ (t + 1),
    LoadHolds rd P.eqR (2 ^ (t + 1) - 2 + i) (etK ((agRm cs h).1.1.take 6) (t + 1) i)
  eqC : ∀ t < 6, ∀ i < 2 ^ (t + 1),
    LoadHolds rd P.eqC (2 ^ (t + 1) - 2 + i) (etK (((agRm cs h).1.1.drop 14).take 6) (t + 1) i)
  wsum : ∀ c ≤ cs.length,
    LoadHolds rd P.wsum (2 * c)
      (sumE (List.zipWith (mtWeightA (agRm cs h).1.1) (cs.take c) ((agLM cs h).take c))) ∧
    LoadHolds rd P.wsum (2 * c + 1)
      (sumE (List.zipWith (mtWeightB (agRm cs h).1.1) (cs.take c) ((agLM cs h).take c)))

/-! ## The loops -/

section Loops

variable {cs : List ChildClaims} {h : BatchHints} {pis fresh carried : E} {P : AggPtrs}

theorem getD_lB (cs : List ChildClaims) {c : ℕ} (hc : c < cs.length) :
    (agLB cs).getD c (0, 0) = (challengeOf (sqCv (sqIt2 (agCvA cs) c)),
      challengeOf (sqCv (sqCv (sqIt2 (agCvA cs) c)))) := by
  obtain ⟨-, h2, h3⟩ := sq2_spec cs.length (agCvA cs)
  rw [agLB, List.getD_eq_getElem _ _ (by rw [h2]; exact hc), h3 c (by rw [h2]; exact hc)]

theorem getD_lM (cs : List ChildClaims) (h : BatchHints) {c : ℕ} (hc : c < cs.length) :
    (agLM cs h).getD c (0, 0, 0) = (challengeOf (sqCv (sqIt3 (agRb cs h).2 c)),
      challengeOf (sqCv (sqCv (sqIt3 (agRb cs h).2 c))),
      challengeOf (sqCv (sqCv (sqCv (sqIt3 (agRb cs h).2 c))))) := by
  obtain ⟨-, h2, h3⟩ := sq3_spec cs.length (agRb cs h).2
  rw [agLM, List.getD_eq_getElem _ _ (by rw [h2]; exact hc), h3 c (by rw [h2]; exact hc)]

theorem length_lB (cs : List ChildClaims) : (agLB cs).length = cs.length :=
  (sq2_spec cs.length (agCvA cs)).2.1

theorem length_lM (cs : List ChildClaims) (h : BatchHints) : (agLM cs h).length = cs.length :=
  (sq3_spec cs.length (agRb cs h).2).2.1

theorem sumE_take_succ' {α β : Type} (g : α → β → E) (cs : List α) (l : List β) (c : ℕ) (d : β)
    (h1 : c < cs.length) (h2 : c < l.length) :
    sumE (List.zipWith g (cs.take (c + 1)) (l.take (c + 1))) =
      sumE (List.zipWith g (cs.take c) (l.take c)) + g cs[c] (l.getD c d) := by
  rw [sumE_zipWith_take_succ g cs l c h1 h2, List.getD_eq_getElem _ _ h2]

theorem readsAt_of_getD {p : E} {xs ys : List E} (h : ReadsAt rd p xs) (hl : ys.length ≤ xs.length)
    (he : ∀ k < ys.length, xs.getD k 0 = ys.getD k 0) : ReadsAt rd p ys := fun k hk => by
  rw [← List.getD_eq_getElem _ 0 hk, ← he k hk]; exact readsAt_getD' h (by omega)

theorem ag_loop95 (hn0 : 0 < cs.length) (hC : ChildClaimsAt rd pis fresh carried cs)
    (hM : AggMem rd P fresh carried cs h) :
    coreProgram.Rel rd "__loop95" [1, gen ^ cs.length, P.absb, pis, fresh, P.frow, carried, P.crow]
      [] := by
  refine loop_complete (B := fun j => j < cs.length) hn0 rfl (fun j hj => hj)
    fun d j hj hK hnext => ?_
  obtain ⟨g0, g1, gsh, gfr, gb, gm, gcr⟩ := hC j hj
  obtain ⟨a0, a1⟩ := hM.absb j hj.le
  obtain ⟨o0, o1⟩ := hM.absb (j + 1) hj
  obtain ⟨wf, wc⟩ := hM.rows j hj
  have htk : (cs.take (j + 1)).flatMap childCells =
      (cs.take j).flatMap childCells ++ childCells cs[j] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
      List.flatMap_append, List.flatMap_singleton]
  have hob : obsAll (agCv1 cs) ((cs.take (j + 1)).flatMap childCells) =
      obsAll (obsAll (agCv1 cs) ((cs.take j).flatMap childCells))
        ((digestScalars cs[j].publicInput).1 :: (digestScalars cs[j].publicInput).2 ::
          (fixedCells cs[j].fresh ++ cs[j].carried.cells)) := by
    rw [htk, obsAll, obsAll, obsAll, List.foldl_append]
    rfl
  rw [hob, show 2 * (j + 1) = 2 * j + 2 by ring] at o0
  rw [hob, show 2 * (j + 1) + 1 = 2 * j + 3 by ring] at o1
  exact loop95_back d j _ _ _ _ _ (fixedCells_getD gsh).1 (deferCells_getD gb gm).1 a0 a1 g0 g1 gfr
    gcr wf wc o0 o1 hK hnext

theorem ag_loop96 (hn0 : 0 < cs.length) (hC : ChildClaimsAt rd pis fresh carried cs)
    (hM : AggMem rd P fresh carried cs h) :
    coreProgram.Rel rd "__loop96" [1, gen ^ cs.length, P.bcc, P.lamB, P.frow, P.crow] [] := by
  refine loop_complete (B := fun j => j < cs.length) hn0 rfl (fun j hj => hj)
    fun d j hj hK hnext => ?_
  obtain ⟨-, -, gsh, gfr, gb, gm, gcr⟩ := hC j hj
  obtain ⟨b0, b1, b2⟩ := hM.bcc j hj.le
  obtain ⟨n0, n1, n2⟩ := hM.bcc (j + 1) hj
  obtain ⟨l0, l1⟩ := hM.lamB j hj
  obtain ⟨wf, wc⟩ := hM.rows j hj
  have hfv := readsAt_getD' gfr (k := 22) (by rw [(fixedCells_getD gsh).1]; omega)
  have hcv := readsAt_getD' gcr (k := 22) (by rw [(deferCells_getD gb gm).1]; omega)
  rw [(fixedCells_getD gsh).2.2.1] at hfv
  rw [(deferCells_getD gb gm).2.2.1] at hcv
  rw [getD_lB cs hj] at l0 l1
  rw [sqIt2_succ, show 3 * (j + 1) = 3 * j + 3 by ring] at n0
  rw [sqIt2_succ, show 3 * (j + 1) + 1 = 3 * j + 4 by ring] at n1
  rw [show 3 * (j + 1) + 2 = 3 * j + 5 by ring,
    sumE_take_succ' _ _ _ _ (0, 0) hj (by rw [length_lB]; exact hj), getD_lB cs hj, bcTerm,
    ← add_assoc] at n2
  exact loop96_back d j _ _ _ _ _ _ b0 b1 l0 l1 n0 n1 wf wc b2 hfv hcv n2 hK hnext

theorem ag_loop98 (hn0 : 0 < cs.length) (hC : ChildClaimsAt rd pis fresh carried cs)
    (hM : AggMem rd P fresh carried cs h) :
    coreProgram.Rel rd "__loop98" [1, gen ^ cs.length, P.mcc, P.lamM, P.frow, P.crow] [] := by
  refine loop_complete (B := fun j => j < cs.length) hn0 rfl (fun j hj => hj)
    fun d j hj hK hnext => ?_
  obtain ⟨-, -, gsh, gfr, gb, gm, gcr⟩ := hC j hj
  obtain ⟨b0, b1, b2⟩ := hM.mcc j hj.le
  obtain ⟨n0, n1, n2⟩ := hM.mcc (j + 1) hj
  obtain ⟨l0, l1, l2⟩ := hM.lamM j hj
  obtain ⟨wf, wc⟩ := hM.rows j hj
  have hfv := readsAt_getD' gfr (k := 105) (by rw [(fixedCells_getD gsh).1]; omega)
  have hca := readsAt_getD' gcr (k := 51) (by rw [(deferCells_getD gb gm).1]; omega)
  have hcb := readsAt_getD' gcr (k := 52) (by rw [(deferCells_getD gb gm).1]; omega)
  rw [(fixedCells_getD gsh).2.2.2.2.2.2.2.2] at hfv
  rw [(deferCells_getD gb gm).2.2.2.2.1] at hca
  rw [(deferCells_getD gb gm).2.2.2.2.2] at hcb
  rw [getD_lM cs h hj] at l0 l1 l2
  rw [sqIt3_succ, show 3 * (j + 1) = 3 * j + 3 by ring] at n0
  rw [sqIt3_succ, show 3 * (j + 1) + 1 = 3 * j + 4 by ring] at n1
  rw [show 3 * (j + 1) + 2 = 3 * j + 5 by ring,
    sumE_take_succ' _ _ _ _ (0, 0, 0) hj (by rw [length_lM]; exact hj), getD_lM cs h hj, mtTerm,
    ← add_assoc, ← add_assoc] at n2
  exact loop98_back d j _ _ _ _ _ _ _ b0 b1 l0 l1 l2 n0 n1 wf wc b2 hfv hca hcb n2 hK hnext

theorem ag_loop97 (hn0 : 0 < cs.length) (hbr : h.bytecodeRounds.length = 22)
    (hC : ChildClaimsAt rd pis fresh carried cs) (hM : AggMem rd P fresh carried cs h) :
    coreProgram.Rel rd "__loop97" [1, gen ^ cs.length, P.frow, P.crow, P.rs, P.wB, P.lamB] [] := by
  have hrl : (agRb cs h).1.1.length = 22 := by rw [agRb, batchRounds_length, hbr]
  refine loop_complete (B := fun j => j < cs.length) hn0 rfl (fun j hj => hj)
    fun d j hj hK hnext => ?_
  obtain ⟨-, -, gsh, gfr, gb, gm, gcr⟩ := hC j hj
  obtain ⟨wf, wc⟩ := hM.rows j hj
  obtain ⟨l0, l1⟩ := hM.lamB j hj
  have hw := hM.wB j hj.le
  have hn := hM.wB (j + 1) hj
  rw [sumE_take_succ' _ _ _ _ (0, 0) hj (by rw [length_lB]; exact hj), bcWeight, ← add_assoc] at hn
  refine loop97_back d j _ _ _ cs[j].fresh.bytecodePoint cs[j].carried.bytecodePoint _ _ _ hrl gsh.1
    gb wf wc hM.rs ?_ ?_ hw l0 l1 hn hK hnext
  · exact readsAt_of_getD gfr (by rw [(fixedCells_getD gsh).1, gsh.1]; omega)
      fun k hk => (fixedCells_getD gsh).2.1 k (by rw [gsh.1] at hk; exact hk)
  · exact readsAt_of_getD gcr (by rw [(deferCells_getD gb gm).1, gb]; omega)
      fun k hk => (deferCells_getD gb gm).2.1 k (by rw [gb] at hk; exact hk)

theorem l99U_eq {f : FixedClaims} (hf : FreshShaped f) {rr : List E} (hr : rr.length = 28) :
    l99U (fixedCells f) (eqKernel (rr.take 6)) (eqKernel ((rr.drop 14).take 6)) rr =
      freshWeight f rr :=
  guestU_eq hf hr

theorem carProd_eq {d : DeferredClaim} (h1 : d.bytecodePoint.length = 22)
    (h2 : d.matrixPoint.length = 28) {rr : List E} (hr : rr.length = 28) :
    carProd d.cells rr 28 = eqEval d.matrixPoint rr := by
  rw [eqEval_prod _ _ 28 h2 hr, carProd]
  exact Finset.prod_congr rfl fun k hk => by
    rw [(deferCells_getD h1 h2).2.2.2.1 k (Finset.mem_range.mp hk)]

theorem ag_loop99 (hn0 : 0 < cs.length) (hmr : h.matrixRounds.length = 28)
    (hC : ChildClaimsAt rd pis fresh carried cs) (hM : AggMem rd P fresh carried cs h) :
    coreProgram.Rel rd "__loop99"
      [1, gen ^ cs.length, P.frow, P.eqR, P.rM, P.eqC, P.crow, P.lamM, P.wsum] [] := by
  have hrl : (agRm cs h).1.1.length = 28 := by rw [agRm, batchRounds_length, hmr]
  refine loop_complete (B := fun j => j < cs.length) hn0 rfl (fun j hj => hj)
    fun d j hj hK hnext => ?_
  obtain ⟨-, -, gsh, gfr, gb, gm, gcr⟩ := hC j hj
  obtain ⟨wf, wc⟩ := hM.rows j hj
  obtain ⟨l0, l1, l2⟩ := hM.lamM j hj
  obtain ⟨w0, w1⟩ := hM.wsum j hj.le
  obtain ⟨n0, n1⟩ := hM.wsum (j + 1) hj
  rw [sumE_take_succ' _ _ _ _ (0, 0, 0) hj (by rw [length_lM]; exact hj), mtWeightA, ← add_assoc,
    show 2 * (j + 1) = 2 * j + 2 by ring, ← l99U_eq gsh hrl, ← carProd_eq gb gm hrl] at n0
  rw [sumE_take_succ' _ _ _ _ (0, 0, 0) hj (by rw [length_lM]; exact hj), mtWeightB, ← add_assoc,
    show 2 * (j + 1) + 1 = 2 * j + 3 by ring, ← l99U_eq gsh hrl, ← carProd_eq gb gm hrl,
    ← (fixedCells_getD gsh).2.2.2.1] at n1
  refine loop99_back d j _ _ _ _ _ _ _ _ _ _ _ _ (fixedCells_getD gsh).1 (deferCells_getD gb gm).1
    hrl wf wc gfr gcr hM.rM (fun i hi => ?_) (fun i hi => ?_) l0 l1 l2 w0 w1 n0 n1 hK hnext
  · have := hM.eqR 5 (by omega) i (by norm_num; omega)
    rwa [etK, List.take_take, min_self, show 2 ^ (5 + 1) - 2 + i = 62 + i by norm_num] at this
  · have := hM.eqC 5 (by omega) i (by norm_num; omega)
    rwa [etK, List.take_take, min_self, show 2 ^ (5 + 1) - 2 + i = 62 + i by norm_num] at this

end Loops

/-! ## The body -/

/-- `Node.batch` on the run's parts. -/
theorem batch_eq (cs : List ChildClaims) (h : BatchHints) :
    batch cs h =
      if (agRb cs h).1.2 = h.bytecodeValue * sumE (List.zipWith (bcWeight (agRb cs h).1.1) cs (agLB cs)) ∧
          (agRm cs h).1.2 = h.matrixA * sumE (List.zipWith (mtWeightA (agRm cs h).1.1) cs (agLM cs h)) +
            h.matrixB * sumE (List.zipWith (mtWeightB (agRm cs h).1.1) cs (agLM cs h)) then
        some ⟨(agRb cs h).1.1, h.bytecodeValue, (agRm cs h).1.1, h.matrixA, h.matrixB⟩
      else none := by
  rw [batch_spec]
  simp only [(sq2_spec _ _).1, (sq3_spec _ _).1]
  rfl

theorem getD_take (l : List E) {n t : ℕ} (h : t < n) : (l.take n).getD t 0 = l.getD t 0 := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_drop (l : List E) (n t : ℕ) : (l.drop n).getD t 0 = l.getD (n + t) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- Lookups in `aggregate_claims`' valuation. -/
macro "ag_look" : tactic =>
  `(tactic| simp (disch := omega) only [setl, set_n_lt, set_n_ge, set_n_in, setEt_lt, setEt_ge,
    Nat.add_sub_cancel_left, ofArgs_n, List.getD_cons_succ, List.getD_cons_zero, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.add_zero, Nat.sub_self, Nat.zero_add])

/-- **`aggregate_claims`' honest valuation**: its pointers, the hints, the transcript's seed and
first absorb, the run's values, the two `eqtree`s, the final check, the stored points. -/
def agVal (cs : List ChildClaims) (h : BatchHints) (P : AggPtrs) (pis fresh carried dp : E) : Val :=
  let gn := gen ^ cs.length
  let cvA := agCvA cs
  let rb := agRb cs h
  let rm := agRm cs h
  let s1 := sumE (List.zipWith (mtWeightA rm.1.1) cs (agLM cs h))
  let s2 := sumE (List.zipWith (mtWeightB rm.1.1) cs (agLM cs h))
  setv (setv (setl (setEt (setl (setEt (setl (setv (setl
    (Val.ofArgs [gn, pis, fresh, carried, dp]) 5
      [P.msgB, P.msgM, h.bytecodeValue, h.matrixA, h.matrixB, P.frow, P.crow,
        word 13601591990776631179 14393745058652752134 0, word 10115303172019694088 4136606974476857268 0])
    14 14 (fsVals gn (blake2sBytes batchLabel) 1)) 28
    [gen, gn * gen, gn * gen * (gn * gen), P.absb, 1, 1 + gn, 1, gn * gn, P.absb * (gn * gn), gn * gn,
      P.lamB, gen, gn * gen, gn * gen * (gn * gen), gn * gen * (gn * gen) * (gn * gen), P.bcc,
      (digestScalars cvA).1, (digestScalars cvA).2, 0, 1, 1 + gn, 1, gn * gn, gn * gn * gn,
      P.bcc * (gn * gn * gn), (digestScalars (sqIt2 cvA cs.length)).1,
      (digestScalars (sqIt2 cvA cs.length)).2, sumE (List.zipWith bcTerm cs (agLB cs)), P.rs,
      (digestScalars rb.2).1, (digestScalars rb.2).2, rb.1.2, (digestScalars rb.2).1,
      (digestScalars rb.2).2, gen, gn * gen, P.wB, 0, 1, 1 + gn, 1, P.wB * gn,
      sumE (List.zipWith (bcWeight rb.1.1) cs (agLB cs)),
      h.bytecodeValue * sumE (List.zipWith (bcWeight rb.1.1) cs (agLB cs)), gn * gn, gn * gn * gn,
      P.lamM, gen, gn * gen, gn * gen * (gn * gen), gn * gen * (gn * gen) * (gn * gen), P.mcc, 0, 1,
      1 + gn, 1, gn * gn, gn * gn * gn, P.mcc * (gn * gn * gn),
      (digestScalars (sqIt3 rb.2 cs.length)).1, (digestScalars (sqIt3 rb.2 cs.length)).2,
      sumE (List.zipWith mtTerm cs (agLM cs h)), P.rM, (digestScalars rm.2).1, (digestScalars rm.2).2,
      rm.1.2, (digestScalars rm.2).1, (digestScalars rm.2).2, P.eqR])
    97 (rm.1.1.take 6)) 301 [P.eqC]) 302 ((rm.1.1.drop 14).take 6)) 506
    [gen, gn * gen, gn * gen * (gn * gen), P.wsum, 0, 0, 1, 1 + gn, 1, gn * gn, P.wsum * (gn * gn), s1,
      h.matrixA * s1, s2, h.matrixB * s2, h.matrixA * s1 + h.matrixB * s2])
    522 22 fun k => rb.1.1.getD k 0) 544 28 fun k => rm.1.1.getD k 0

/-- `aggregate_claims`' body on its honest valuation. -/
theorem agBody_holds {cs : List ChildClaims} {h : BatchHints} {d : DeferredClaim}
    (hne : cs ≠ []) (hb : batch cs h = some d)
    (hbr : h.bytecodeRounds.length = 22) (hmr : h.matrixRounds.length = 28)
    {pis fresh carried dp : E} (hC : ChildClaimsAt rd pis fresh carried cs)
    (hd : ReadsAt rd dp d.cells) (P : AggPtrs) (hM : AggMem rd P fresh carried cs h) :
    Stmt.HoldsList (coreProgram.Rel rd) rd (agVal cs h P pis fresh carried dp) agBody False
      (fun rs => rs = []) := by
  have hn0 : 0 < cs.length := List.length_pos_iff.mpr hne
  rw [batch_eq] at hb
  split_ifs at hb with hck
  obtain ⟨hck1, hck2⟩ := hck
  cases hb
  rw [agBody]
  simp only [holdsList_append, holds_fsCompressT (.n 12) (.n 13) (.n 0) 14 (by decide : 1 < 256)]
  rw [holdsList_noRet (eqtreeT (.n 90) 0 (.n 96) 97) (noRetList_eqtreeT ..),
    holdsList_noRet (eqtreeT (.n 90) 14 (.n 301) 302) (noRetList_eqtreeT ..),
    holdsList_noRet agStores noRetList_agStores]
  simp only [agP1, agP2, agP3, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    word_gen, word_one, word_zero]
  have hrb : (agRb cs h).1.1.length = 22 := by rw [agRb, batchRounds_length, hbr]
  have hrm : (agRm cs h).1.1.length = 28 := by rw [agRm, batchRounds_length, hmr]
  have hK : IsInK (1 + gen ^ cs.length) := isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK _)
  have tB : (agLB cs).take cs.length = agLB cs := by rw [← length_lB cs, List.take_length]
  have tM : (agLM cs h).take cs.length = agLM cs h := by rw [← length_lM cs h, List.take_length]
  obtain ⟨b0, b1, b2⟩ := hM.bcc 0 (Nat.zero_le _)
  obtain ⟨bn0, bn1, bn2⟩ := hM.bcc cs.length le_rfl
  obtain ⟨m0, m1, m2⟩ := hM.mcc 0 (Nat.zero_le _)
  obtain ⟨mn0, mn1, mn2⟩ := hM.mcc cs.length le_rfl
  obtain ⟨w0, w1⟩ := hM.wsum 0 (Nat.zero_le _)
  obtain ⟨wn0, wn1⟩ := hM.wsum cs.length le_rfl
  obtain ⟨a0, a1⟩ := hM.absb 0 (Nat.zero_le _)
  obtain ⟨an0, an1⟩ := hM.absb cs.length le_rfl
  have v0 := hM.wB 0 (Nat.zero_le _)
  have vn := hM.wB cs.length le_rfl
  simp only [List.take_zero, List.flatMap_nil, List.zipWith_nil_left, List.take_length, tB, tM]
    at b2 m2 w0 w1 a0 a1 an0 an1 v0 bn2 mn2 wn0 wn1 vn
  simp only [agVal]
  ag_look
  simp only [true_and, and_true]
  refine ⟨⟨blake2sBytes batchLabel, aggSeed_eq, fun k h1 h2 => by ag_look⟩, ?_, ?_, hK,
    fun _ => ag_loop95 hn0 hC hM, ?_, b0, ?_, b1, by simpa [sumE] using b2, hK,
    fun _ => ag_loop96 hn0 hC hM, ?_, ?_, ?_, ?_, by simpa [sumE] using v0, hK,
    fun _ => ag_loop97 hn0 hbr hC hM, ?_, e_add_eq_zero_iff.mpr hck1, m0, m1,
    by simpa [sumE] using m2, hK, fun _ => ag_loop98 hn0 hC hM, ?_, ?_, ?_, ?_, ?_, ?_,
    by simpa [sumE] using w0, by simpa [sumE] using w1, hK, fun _ => ag_loop99 hn0 hmr hC hM, ?_, ?_,
    e_add_eq_zero_iff.mpr hck2, ?_⟩
  · have e : fsVals (gen ^ cs.length) (blake2sBytes batchLabel) 1 12 = (digestScalars (agCv1 cs)).1 := by
      rw [agCv1, ← gen_pow_eq_ofK]; rfl
    rw [e]; simpa [obsAll] using a0
  · have e : fsVals (gen ^ cs.length) (blake2sBytes batchLabel) 1 13 = (digestScalars (agCv1 cs)).2 := by
      rw [agCv1, ← gen_pow_eq_ofK]; rfl
    rw [e]; simpa [obsAll] using a1
  · exact loadHolds_of_mul0 (by ring) an0
  · exact loadHolds_of_mul (by ring) an1
  · exact loadHolds_of_mul0 (by ring) bn0
  · exact loadHolds_of_mul (by ring) bn1
  · exact loadHolds_of_mul (by ring) bn2
  · exact (batch_sumcheck_L22_iff rd _ _).mpr ⟨_, h.bytecodeRounds, _, _, _, rfl, hbr,
      fun r hr => by
        have := hM.msgB r (by rwa [hbr] at hr)
        rwa [List.getD_eq_getElem _ _ hr] at this, rfl, hM.rs, rfl⟩
  · exact loadHolds_of_mul0 rfl vn
  · exact loadHolds_of_mul0 (by ring) mn0
  · exact loadHolds_of_mul (by ring) mn1
  · exact loadHolds_of_mul (by ring) mn2
  · exact (batch_sumcheck_L28_iff rd _ _).mpr ⟨_, h.matrixRounds, _, _, _, rfl, hmr,
      fun r hr => by
        have := hM.msgM r (by rwa [hmr] at hr)
        rwa [List.getD_eq_getElem _ _ hr] at this, rfl, hM.rM, rfl⟩
  · refine eqtree_complete (.n 90) (.n 96) 0 97 _ ((agRm cs h).1.1.take 6) (by simp [hrm])
      (etVals_congr (fun i h1 h2 => by ag_look; rfl) (setEt_vals _ _ _)) (fun t ht => ?_)
      (fun t ht i hi => by ag_look; exact hM.eqR t ht i hi)
    ag_look
    rw [getD_take _ ht]
    exact readsAt_getD' hM.rM (by omega)
  · refine eqtree_complete (.n 90) (.n 301) 14 302 _ (((agRm cs h).1.1.drop 14).take 6)
      (by simp [hrm]) (etVals_congr (fun i h1 h2 => by ag_look; rfl) (setEt_vals _ _ _)) (fun t ht => ?_)
      (fun t ht i hi => by ag_look; exact hM.eqC t ht i hi)
    ag_look
    rw [getD_take _ ht, getD_drop]
    exact readsAt_getD' hM.rM (by omega)
  · exact loadHolds_of_mul0 (by ring) wn0
  · exact loadHolds_of_mul (by ring) wn1
  · obtain ⟨dl, d1, d2, d3, d4, d5⟩ := deferCells_getD
      (d := ⟨(agRb cs h).1.1, h.bytecodeValue, (agRm cs h).1.1, h.matrixA, h.matrixB⟩) hrb hrm
    have hdk : ∀ k < 53, LoadHolds rd dp k
        (DeferredClaim.cells ⟨(agRb cs h).1.1, h.bytecodeValue, (agRm cs h).1.1, h.matrixA,
          h.matrixB⟩ |>.getD k 0) := fun k hk => readsAt_getD' hd (by rw [dl]; exact hk)
    rw [agStores]
    simp only [holdsList_append]
    rw [holdsList_range_flatten 22 (fun k => [Stmt.atom (.load (.n (522 + k)) (.n 56) k),
        .atom (.load (.n (522 + k)) (.n 4) k)]) (fun _ => rfl),
      holdsList_range_flatten 28 (fun k => [Stmt.atom (.load (.n (544 + k)) (.n 90) k),
        .atom (.load (.n (544 + k)) (.n 4) (23 + k))]) (fun _ => rfl)]
    simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true]
    refine ⟨fun k hk => ?_, ?_, fun k hk => ?_, ?_, ?_⟩
    · ag_look
      refine ⟨readsAt_getD' hM.rs (by omega), ?_⟩
      have := hdk k (by omega)
      rwa [d1 k hk] at this
    · ag_look
      have := hdk 22 (by omega)
      rwa [d2] at this
    · ag_look
      refine ⟨readsAt_getD' hM.rM (by omega), ?_⟩
      have := hdk (23 + k) (by omega)
      rwa [d3 k hk] at this
    · ag_look
      have := hdk 51 (by omega)
      rwa [d4] at this
    · ag_look
      have := hdk 52 (by omega)
      rwa [d5] at this

/-- **`aggregate_claims`, completely** (G:3319-3486; TRIAGE #77): for nonempty claims `cs` at the
buffers (`ChildClaimsAt`), hints `h` of `22` and `28` rounds whose batching closes
on `d`, stored at `defer_stmt`, every choice of the `HeapBuf` pointers `P` and every memory
holding the honest words there (`AggMem`), `aggregate_claims` holds. -/
theorem aggregate_claims_complete {cs : List ChildClaims} {h : BatchHints} {d : DeferredClaim}
    (hne : cs ≠ []) (hb : batch cs h = some d)
    (hbr : h.bytecodeRounds.length = 22) (hmr : h.matrixRounds.length = 28)
    {pis fresh carried dp : E} (hC : ChildClaimsAt rd pis fresh carried cs)
    (hd : ReadsAt rd dp d.cells) (P : AggPtrs) (hM : AggMem rd P fresh carried cs h) :
    coreProgram.Rel rd "aggregate_claims" [gen ^ cs.length, pis, fresh, carried, dp] [] := by
  rw [rel_iff_sem find_aggregate_claims]
  refine ⟨agVal cs h P pis fresh carried dp, by
    simp only [show Fn.params Data.core29 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl, List.map_cons,
      List.map_nil, agVal]; ag_look, ?_⟩
  rw [core29_body]
  exact agBody_holds hne hb hbr hmr hC hd P hM

end
end LeanVM.Guest.B1.Main
