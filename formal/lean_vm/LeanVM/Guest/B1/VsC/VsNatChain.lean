/-
  LeanVM.Guest.B1.VsC.VsNatChain

  An accepting run of plain sum-check rounds, read backwards into the guest's chain of rounds.
-/

module

public import LeanVM.Guest.B1.VsC.Os.CInvRound
public import LeanVM.Guest.B1.Link.RoundsRun

/-!
# The native chain of rounds

`natChain nt bits k st ws`: the chain of `k` rounds of `nt` tail coefficients and `bits` of grind
the guest computes from the state `st` on the words `ws` (`natStep`, `natRoundLen nt bits` words a
round). **`natChain_inv`**: an accepting carried run of `sumcheck st.cl (nt + 2) (replicate k none)`
from `st`'s capacity read such words, returns the chain's challenges and last claim, leaves its last
capacity, and the chain is a `RoundChain` on every memory reading the words at `st.cur`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Link
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Tables (TSt)

@[expose] public section

/-- The words of one round: the constant, the tail, the nonce unless zero bits. -/
def natRoundLen (nt bits : ℕ) : ℕ := nt + 1 + (if bits = 0 then 0 else 1)

/-- The sponge a round grinds on: its constant and tail absorbed. -/
def natRoundFs (nt : ℕ) (st : RSt) (ws : List E) : Fs :=
  ((⟨st.cap, []⟩ : Fs).absorb (ws.getD 0 0) dsObserve).absorbAll ((ws.drop 1).take nt) dsObserve

/-- **One round on the words `ws`**: its challenge and the state after it. -/
def natStep (nt bits : ℕ) (st : RSt) (ws : List E) : E × RSt :=
  let g := (natRoundFs nt st ws).grindSqueeze bits (ws.getD (nt + 1) 0)
  (g.1, ⟨g.2.cap, st.cur * gen ^ natRoundLen nt bits,
    polyEval (ws.getD 0 0 :: (st.cl + sumE ((ws.drop 1).take nt)) :: (ws.drop 1).take nt) g.1⟩)

/-- **`k` rounds on the words `ws`.** -/
def natChain (nt bits : ℕ) : ℕ → RSt → List E → List (E × RSt)
  | 0, _, _ => []
  | k + 1, st, ws => natStep nt bits st ws ::
      natChain nt bits k (natStep nt bits st ws).2 (ws.drop (natRoundLen nt bits))

theorem natChain_length (nt bits : ℕ) : ∀ (k : ℕ) (st : RSt) (ws : List E),
    (natChain nt bits k st ws).length = k
  | 0, _, _ => rfl
  | k + 1, st, ws => by simp [natChain, natChain_length nt bits k]

theorem natChain_cur (nt bits : ℕ) : ∀ (k : ℕ) (st : RSt) (ws : List E),
    (chainLast st (natChain nt bits k st ws)).cur = st.cur * gen ^ (k * natRoundLen nt bits)
  | 0, st, _ => by simp [natChain, chainLast]
  | k + 1, st, ws => by
    show (chainLast (natStep nt bits st ws).2 _).cur = _
    rw [natChain_cur nt bits k]
    simp only [natStep, mul_assoc, ← pow_add]
    congr 2
    ring

/-- **A chain's challenges and capacities do not depend on its cursor or claim.** -/
theorem natChain_fst_cap (nt bits : ℕ) : ∀ (k : ℕ) (cap : List E) (cur cl cur' cl' : E) (ws : List E),
    (natChain nt bits k ⟨cap, cur, cl⟩ ws).map Prod.fst = (natChain nt bits k ⟨cap, cur', cl'⟩ ws).map Prod.fst ∧
      (chainLast ⟨cap, cur, cl⟩ (natChain nt bits k ⟨cap, cur, cl⟩ ws)).cap =
        (chainLast ⟨cap, cur', cl'⟩ (natChain nt bits k ⟨cap, cur', cl'⟩ ws)).cap
  | 0, _, _, _, _, _, _ => ⟨rfl, rfl⟩
  | k + 1, cap, cur, cl, cur', cl', ws => by
    obtain ⟨h1, h2⟩ := natChain_fst_cap nt bits k (natStep nt bits ⟨cap, cur, cl⟩ ws).2.cap
      (natStep nt bits ⟨cap, cur, cl⟩ ws).2.cur (natStep nt bits ⟨cap, cur, cl⟩ ws).2.cl
      (natStep nt bits ⟨cap, cur', cl'⟩ ws).2.cur (natStep nt bits ⟨cap, cur', cl'⟩ ws).2.cl
      (ws.drop (natRoundLen nt bits))
    exact ⟨by simp only [natChain, List.map_cons]; exact congrArg₂ _ rfl h1, h2⟩

/-- The grind's challenge and sponge on the carried run: the ground challenge after a grind, a
squeeze otherwise. -/
theorem grindSqueeze_zero (s : Fs) (n : E) : s.grindSqueeze 0 n = s.squeeze := by
  simp [Fs.grindSqueeze]

/-- One round's words, as the guest reads them. -/
theorem natRound_words {nt bits : ℕ} {c0 n : E} {tail rest : List E} (htl : tail.length = nt) :
    (c0 :: tail ++ grindWords bits n ++ rest).getD 0 0 = c0 ∧
      ((c0 :: tail ++ grindWords bits n ++ rest).drop 1).take nt = tail ∧
      (bits ≠ 0 → (c0 :: tail ++ grindWords bits n ++ rest).getD (nt + 1) 0 = n) ∧
      (c0 :: tail ++ grindWords bits n ++ rest).drop (natRoundLen nt bits) = rest ∧
      (c0 :: tail ++ grindWords bits n).length = natRoundLen nt bits := by
  have hl : (c0 :: tail ++ grindWords bits n).length = natRoundLen nt bits := by
    unfold natRoundLen grindWords
    split <;> simp [htl]
  refine ⟨rfl, ?_, fun hb => ?_, List.drop_left' hl, hl⟩
  · have e : (c0 :: tail ++ grindWords bits n ++ rest).drop 1 = tail ++ (grindWords bits n ++ rest) := by
      simp
    rw [e, List.take_left' htl]
  · have e : c0 :: tail ++ grindWords bits n ++ rest = (c0 :: tail) ++ (n :: rest) := by
      simp [grindWords, hb]
    rw [e, List.getD_append_right _ _ _ _ (by simp [htl])]
    simp [htl]

/-- A run read in two parts. -/
theorem natReads_split {rd : Reader} {p : E} {xs ys : List E} (h : ReadsAt rd p (xs ++ ys)) :
    ReadsAt rd p xs ∧ ReadsAt rd (p * gen ^ xs.length) ys := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have := h k (by rw [List.length_append]; omega)
    rwa [List.getElem_append_left hk] at this
  · have := h (xs.length + k) (by rw [List.length_append]; omega)
    rw [List.getElem_append_right (by omega)] at this
    simp only [Nat.add_sub_cancel_left] at this
    rw [loadHolds_mul_gen_pow]; exact this

/-- **One round's grind and challenge, backwards**: on the carried run, after the round's reads. -/
theorem natGrind_inv {bits : ℕ} {s1 : Fs} {xs2 : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {β : Type} {k : E → VerifierProgram β} {r : β × TSt}
    (h1 : runTc ((VerifierProgram.grindProofOfWork bits).bind fun _ => VerifierProgram.sampleChallenge.bind k)
      ⟨s1, none, xs2, os, R⟩ = some r) :
    ∃ n xs3, xs2 = grindWords bits n ++ xs3 ∧ s1.GrindOk bits n ∧
      runTc (k (s1.grindSqueeze bits n).1) ⟨(s1.grindSqueeze bits n).2, none, xs3, os, R⟩ = some r := by
  by_cases hz : bits = 0
  · subst hz
    refine ⟨0, xs2, by simp [grindWords], Or.inl rfl, ?_⟩
    rw [grindSqueeze_zero]
    exact runTc_sampleE_none (st := ⟨s1, none, xs2, os, R⟩) h1 rfl
  · obtain ⟨n, xs3, hs, -, hp, hc⟩ := runTc_grindPoW hz h1
    simp only at hs
    refine ⟨n, xs3, by simp [grindWords, hz, hs], Or.inr hp, ?_⟩
    rw [Fs.grindSqueeze_pos _ hz]
    exact runTc_sampleE_some hc rfl

/-- A plain round of `sumcheck`, its steps in sequence. -/
theorem sumcheck_none_eq (claim : E) (count : ℕ) (rest : List (Option E)) :
    sumcheck claim count (none :: rest) =
      VerifierProgram.readScalar.bind fun c ↦
        (VerifierProgram.readScalars (count - 2)).bind fun t ↦
          (VerifierProgram.grindProofOfWork (grindingBits (count - 1))).bind fun _ ↦
            VerifierProgram.sampleChallenge.bind fun y ↦
              (sumcheck (polyEval (c :: (claim + sumE t) :: t) y) count rest).bind fun p ↦
                VerifierProgram.ret (y :: p.1, p.2) := by
  simp only [sumcheck, sumcheckRoundPoly, VerifierProgram.bind_eq', VerifierProgram.pure_eq',
    VerifierProgram.bind_assoc', VerifierProgram.ret_bind']

/-- **Plain sum-check rounds, backwards**: an accepting carried run reads the chain's words and
returns its challenges and last claim; the chain holds on every memory reading the words. -/
theorem natChain_inv {nt bits : ℕ} (hb : grindingBits (nt + 1) = bits) :
    ∀ (k : ℕ) (st : RSt) {xs : List E} {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)}
      {a : List E × E} {st1 : TSt},
      (∃ sp, (⟨st.cap, []⟩ : Fs).Carries sp) →
      runTc (sumcheck st.cl (nt + 2) (List.replicate k none)) ⟨⟨st.cap, []⟩, none, xs, os, R⟩ =
        some (a, st1) →
      ∃ ws xs', ws.length = k * natRoundLen nt bits ∧ xs = ws ++ xs' ∧
        a = ((natChain nt bits k st ws).map Prod.fst, (chainLast st (natChain nt bits k st ws)).cl) ∧
        st1 = ⟨⟨(chainLast st (natChain nt bits k st ws)).cap, []⟩, none, xs', os, R⟩ ∧
        ∀ (cur cl : E) rd, ReadsAt rd cur ws →
          RoundChain rd nt bits ⟨st.cap, cur, cl⟩ (natChain nt bits k ⟨st.cap, cur, cl⟩ ws)
  | 0, st, xs, os, R, a, st1, _, h => by
    have e := runTc_ret_inv (α := List E × E) h
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨[], xs, by simp, rfl, rfl, rfl, fun _ _ _ _ => trivial⟩
  | k + 1, st, xs, os, R, a, st1, hc, h => by
    rw [List.replicate_succ, sumcheck_none_eq] at h
    obtain ⟨c0, xs1, hs1, -, h⟩ := runTc_readE h
    obtain ⟨tail, xs2, htl, hs2, h⟩ := runTc_readScalars (nt + 2 - 2) _ _ rfl h
    simp only at hs1 hs2
    have htl' : tail.length = nt := by rw [htl]; rfl
    have e2 : nt + 2 - 1 = nt + 1 := rfl
    rw [e2, hb] at h
    obtain ⟨n, xs3, hx3, hok, h⟩ := natGrind_inv h
    set s1 := ((⟨st.cap, []⟩ : Fs).absorb c0 dsObserve).absorbAll tail dsObserve with hs1d
    set y := (s1.grindSqueeze bits n).1 with hy
    set cap' := (s1.grindSqueeze bits n).2.cap with hcap'
    have hpend : (s1.grindSqueeze bits n).2 = ⟨cap', []⟩ := by
      by_cases hz : bits = 0
      · subst hz; rw [hcap', grindSqueeze_zero]; rfl
      · rw [hcap', Fs.grindSqueeze_pos _ hz]
    have hc' : ∃ sp, (⟨cap', []⟩ : Fs).Carries sp := by
      by_cases hz : bits = 0
      · subst hz
        refine ⟨⟨s1.perm, [], none⟩, ?_, rfl, rfl⟩
        rw [hcap', grindSqueeze_zero]; rfl
      · refine ⟨⟨s1.nonceState n, [], none⟩, ?_, rfl, rfl⟩
        rw [hcap', Fs.grindSqueeze_pos _ hz]
    set st' : RSt := ⟨cap', st.cur * gen ^ natRoundLen nt bits,
      polyEval (c0 :: (st.cl + sumE tail) :: tail) y⟩ with hst'
    rw [hpend] at h
    obtain ⟨p, st3, h4, h5⟩ := runTc_bind_some h
    obtain ⟨ws', xs', hl', hx', ea, est, hch⟩ := natChain_inv hb k st' hc' h4
    have e := runTc_ret_inv h5
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    subst est
    obtain ⟨hw0, hwt, hwn, hwd, hwl⟩ := natRound_words (bits := bits) (c0 := c0) (n := n) (rest := ws') htl'
    have hstep : natStep nt bits st (c0 :: tail ++ grindWords bits n ++ ws') = (y, st') := by
      unfold natStep natRoundFs
      rw [hw0, hwt]
      by_cases hz : bits = 0
      · subst hz; simp only [grindSqueeze_zero]; rfl
      · rw [hwn hz]
    have hnat : natChain nt bits (k + 1) st (c0 :: tail ++ grindWords bits n ++ ws') =
        (y, st') :: natChain nt bits k st' ws' := by
      show natStep nt bits st _ :: natChain nt bits k (natStep nt bits st _).2 _ = _
      rw [hstep, hwd]
    have hstepG : ∀ cur cl : E, natStep nt bits ⟨st.cap, cur, cl⟩ (c0 :: tail ++ grindWords bits n ++ ws') =
        (y, ⟨cap', cur * gen ^ natRoundLen nt bits, polyEval (c0 :: (cl + sumE tail) :: tail) y⟩) := by
      intro cur cl
      unfold natStep natRoundFs
      rw [hw0, hwt]
      by_cases hz : bits = 0
      · subst hz; simp only [grindSqueeze_zero]; rfl
      · rw [hwn hz]
    refine ⟨c0 :: tail ++ grindWords bits n ++ ws', xs', ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.length_append, hwl, hl']; ring
    · rw [hs1, hs2, hx3, hx']; simp
    · rw [hnat, ea]; rfl
    · rw [hnat]; rfl
    · intro cur cl rd hr
      have hnatG : natChain nt bits (k + 1) ⟨st.cap, cur, cl⟩ (c0 :: tail ++ grindWords bits n ++ ws') =
          (y, ⟨cap', cur * gen ^ natRoundLen nt bits, polyEval (c0 :: (cl + sumE tail) :: tail) y⟩) ::
            natChain nt bits k ⟨cap', cur * gen ^ natRoundLen nt bits, polyEval (c0 :: (cl + sumE tail) :: tail) y⟩
              ws' := by
        show natStep nt bits _ _ :: natChain nt bits k (natStep nt bits _ _).2 _ = _
        rw [hstepG, hwd]
      rw [hnatG]
      obtain ⟨hr1, hr2⟩ := natReads_split hr
      refine ⟨⟨c0, tail, n, htl', hr1, hok, Prod.ext rfl hpend, ?_, rfl⟩, hch _ _ rd ?_⟩
      · show cur * gen ^ natRoundLen nt bits = _
        rw [← hwl]; simp only [List.length_append, List.length_cons, htl']
      · rw [← hwl]; exact hr2

end
end LeanVM.Guest.B1.VsC
