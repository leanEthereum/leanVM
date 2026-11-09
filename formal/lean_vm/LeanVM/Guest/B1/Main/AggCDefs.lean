/-
  LeanVM.Guest.B1.Main.AggCDefs

  `aggregate_claims`' honest memory: its buffers' pointers (any choice of them) and the words an
  honest run of a batching leaves there.
-/

module

public import LeanVM.Guest.B1.Main.Aggregate
public import LeanVM.Guest.B1.Fwd.Canon

/-!
# `aggregate_claims`' honest memory

For `m` children `cs` and the hints `h`: a row's thirteen words (`rowW`: the capacity cells, then
the rate cells of the waiting scalars), the absorbing rows' sponges (`absSt`), the running claim
(`claimAt`) and weight (`weightAt`) after `c` children, the lambdas the powers of the challenge
`λ` (`lamA`). `AggPtrs`: `aggregate_claims`' buffers (the rounds `bc_sumcheck_msgs`, the pointer
tables `lf`, `lc`, the absorbing rows, the records of `bc_chain`, the sumcheck's point,
`bc_point1`, the weights). `AggMem rd P …`: the memory an honest run leaves at them and at `defer_stmt`.

`rowRel_of_reads`: a row of honest words carries its sponge (`RowRel`); `absSt_ok`: the honest
sponges' capacity cells are a state's, their scalars tagged `1`.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-- A row's thirteen words: the capacity cells, then the rate cells of the waiting scalars. -/
def rowW (s : Fs) : List E := s.cap ++ rateOf s.pend

/-- The absorbing row `c`'s sponge: after the count and the first `c` children's words. -/
def absSt (m : ℕ) (cs : List ChildClaims) (c : ℕ) : Fs :=
  aggS0.absorbAll (Batch.childCountCells m ++ (cs.take c).flatMap Batch.childCells) dsObserve

/-- The batching's challenge `λ`: the squeeze of the sponge after its words. -/
def lamA (cs : List ChildClaims) : E := (aggAbs cs).squeeze.1

/-- The running claim after `c` children. -/
def claimAt (cs : List ChildClaims) (c : ℕ) : E :=
  sumE (List.zipWith (fun c l ↦ l.1 * c.freshClaim.bytecodeValue + l.2 * c.carriedClaim.bytecodeValue)
    (cs.take c) (Batch.lambdaPowers (lamA cs) c))

/-- The running weight after `c` children, at the sumcheck's point. -/
def weightAt (cs : List ChildClaims) (h : BatchingHints) (c : ℕ) : E :=
  sumE (List.zipWith (fun c l ↦ l.1 * eqEval c.freshClaim.bytecodePoint (aggRun cs h).1.1 +
    l.2 * eqEval c.carriedClaim.bytecodePoint (aggRun cs h).1.1) (cs.take c)
    (Batch.lambdaPowers (lamA cs) c))

/-- The claim `aggregate_claims` writes: the sumcheck's point, the hinted value. -/
def aggOut (cs : List ChildClaims) (h : BatchingHints) : DeferredClaim :=
  ⟨(aggRun cs h).1.1, h.finalBytecodeValue⟩

/-- `aggregate_claims`' buffers. -/
structure AggPtrs where
  msgs : E
  lf : E
  lc : E
  absorb : E
  chain : E
  pt : E
  pt1 : E
  w : E

/-- **The memory an honest run of `aggregate_claims` leaves** at the pointers `P` and at
`defer_stmt` (`dst`), for the children `cs` (their claims through `cfresh`, `ccarried`) and the
hints `h`. -/
structure AggMem (rd : Reader) (cfresh ccarried dst : E) (cs : List ChildClaims) (h : BatchingHints)
    (P : AggPtrs) : Prop where
  absorb : ∀ c ≤ cs.length, ReadsAt rd (P.absorb * (gen ^ c) ^ 13) (rowW (absSt cs.length cs c))
  lf : ∀ c < cs.length, LoadHolds rd (P.lf * gen ^ c) 0 (cfresh * (gen ^ c) ^ 24)
  lc : ∀ c < cs.length, LoadHolds rd (P.lc * gen ^ c) 0 (ccarried * (gen ^ c) ^ 24)
  chain : ∀ c ≤ cs.length, ReadsAt rd (P.chain * (gen ^ c) ^ 2)
    [lamA cs ^ (2 * c), claimAt cs c]
  msgs : ReadsAt rd P.msgs (h.sumcheckMessages.flatMap fun g => [g.1, g.2])
  pt : ReadsAt rd P.pt (aggRun cs h).1.1
  pt1 : ReadsAt rd P.pt1 ((aggRun cs h).1.1.map (1 + ·))
  w : ∀ c ≤ cs.length, LoadHolds rd (P.w * gen ^ c) 0 (weightAt cs h c)
  dst : ReadsAt rd dst (aggOut cs h).cells

/-! ## Honest rows -/

/-- The sponge's capacity cells are a state's, its scalars tagged `1`, at most four. -/
def StOk (s : Fs) : Prop :=
  (∃ S, s.cap = capOf S) ∧ s.pend.length ≤ 4 ∧ ∀ q ∈ s.pend, q.2 = dsObserve

theorem stOk_absorb {s : Fs} (h : StOk s) (x : E) : StOk (s.absorb x dsObserve) := by
  obtain ⟨⟨S, hS⟩, hl, ht⟩ := h
  unfold Fs.absorb
  split
  · refine ⟨⟨_, rfl⟩, by simp, fun q hq => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rw [hq]
  · rename_i hne
    refine ⟨⟨S, hS⟩, ?_, fun q hq => ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]
      simp only [rateScalars] at hne
      omega
    · rcases List.mem_append.mp hq with hq | hq
      · exact ht q hq
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rw [hq]

theorem stOk_absorbAll : ∀ (xs : List E) {s : Fs}, StOk s → StOk (s.absorbAll xs dsObserve)
  | [], _, h => h
  | x :: xs, _, h => stOk_absorbAll xs (stOk_absorb h x)

theorem stOk_aggS0 : StOk aggS0 := ⟨⟨_, rfl⟩, by simp [aggS0], fun q hq => by simp [aggS0] at hq⟩

theorem absSt_ok (m : ℕ) (cs : List ChildClaims) (c : ℕ) : StOk (absSt m cs c) :=
  stOk_absorbAll _ stOk_aggS0

theorem aggAbs_ok (cs : List ChildClaims) : StOk (aggAbs cs) := stOk_absorbAll _ stOk_aggS0

theorem capOf_length (S : KeccakState) : (capOf S).length = 5 := rfl

theorem capOf_canonical (S : KeccakState) : AllCanonical (capOf S) := by
  intro c hc
  simp only [capOf, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> exact cellsOfState_canonical _ _ _

theorem rateOf_canonical (pend : List (E × ℕ)) : AllCanonical (rateOf pend) := by
  intro c hc
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
  exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl

theorem rowW_length {s : Fs} (h : StOk s) : (rowW s).length = 13 := by
  obtain ⟨⟨S, hS⟩, -, -⟩ := h
  simp [rowW, hS, capOf_length, rateOf]

theorem rowW_canonical {s : Fs} (h : StOk s) : AllCanonical (rowW s) := by
  obtain ⟨⟨S, hS⟩, -, -⟩ := h
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · rw [hS] at hc; exact capOf_canonical S c hc
  · exact rateOf_canonical _ c hc

theorem rowW_getD_cap {s : Fs} (h : StOk s) {i : ℕ} (hi : i < 5) :
    (rowW s).getD i 0 = s.cap.getD i 0 := by
  obtain ⟨⟨S, hS⟩, -, -⟩ := h
  rw [rowW, List.getD_append _ _ _ _ (by rw [hS, capOf_length]; exact hi)]

theorem rowW_getD_rate {s : Fs} (h : StOk s) {c : ℕ} (hc : c < 8) :
    (rowW s).getD (5 + c) 0 = Keccak.rateCell s.pend c := by
  obtain ⟨⟨S, hS⟩, -, -⟩ := h
  rw [rowW, List.getD_append_right _ _ _ _ (by rw [hS, capOf_length]; omega), hS, capOf_length,
    show 5 + c - 5 = c by omega]
  simp [rateOf, List.getD_eq_getElem?_getD, hc]

/-- **A row of honest words carries its sponge.** -/
theorem rowRel_of_reads {rd : Reader} {p : E} {s : Fs} (hs : StOk s) (h : ReadsAt rd p (rowW s)) :
    RowRel rd p s := by
  have hl := rowW_length hs
  have hm : ∀ k < 13, memAt rd p k = (rowW s).getD k 0 := fun k hk =>
    memAt_of_reads h (by rw [hl]; exact hk)
  obtain ⟨⟨S, hS⟩, hpl, ht⟩ := hs
  refine ⟨?_, hpl, fun k hk => ?_⟩
  · rw [rowCap, hS]
    refine list_eq_of_getD (n := 5) (by rfl) (by simp) fun i hi => ?_
    have e : (List.map (fun i ↦ memAt rd p i) (List.range 5)).getD i 0 = memAt rd p i := by
      simp [List.getD_eq_getElem?_getD, hi]
    rw [e, hm i (by omega), rowW_getD_cap ⟨⟨S, hS⟩, hpl, ht⟩ hi, hS]
  · have e1 := hm (5 + 2 * k) (by omega)
    have e2 := hm (6 + 2 * k) (by omega)
    rw [rowW_getD_rate ⟨⟨S, hS⟩, hpl, ht⟩ (by omega)] at e1
    rw [show 6 + 2 * k = 5 + (2 * k + 1) by omega,
      rowW_getD_rate ⟨⟨S, hS⟩, hpl, ht⟩ (by omega)] at e2
    rw [show 6 + 2 * k = 5 + (2 * k + 1) by omega]
    split
    · rename_i hkl
      refine ⟨ht _ (List.getElem_mem _), fun _ => ?_⟩
      rw [e1, e2, Keccak.rateCell_scalar _ k hkl, ht _ (List.getElem_mem _)]
    · rename_i hkl
      rw [e1, e2, Keccak.rateCell_past _ (by omega), Keccak.rateCell_past _ (by omega)]
      exact ⟨rfl, rfl⟩

end
end LeanVM.Guest.B1.Main
