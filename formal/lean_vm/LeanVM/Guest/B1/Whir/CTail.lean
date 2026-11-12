/-
  LeanVM.Guest.B1.Whir.CTail

  The closing rounds honestly: each `opening_tail_round` call at its exact arguments,
  its challenge stored in `tail_challenges`, the unused entries zeroed.
-/

module

public import LeanVM.Guest.B1.Whir.CLvCommit
public import LeanVM.Guest.B1.Whir.TailRun

/-!
# The closing rounds, honestly (G:1697-1705)

* `tailRets cap cur cl p`: what `opening_tail_round` returns on the capacity `cap`, the cursor,
  the claim and the words `p` (its meaning's formula).
* `TailC C rd tch tabs j pairs cap cl cur`: the rounds' calls at their exact arguments and
  returns, each challenge stored at `tch·g^j`.
* `osTailRound_complete`, `osTailRounds_completeA`: the rounds as blocks at fixed values, the
  sponge and claim after them `tailRun`'s.
* `osTail_complete`: `tail_challenges` allocated at a given pointer, the rounds, the unused
  entries zeroed.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {H : CallRel → Reader → Prop}

/-- `opening_tail_round`'s returns. -/
def tailRets (cap : List E) (cur cl : E) (p : E × E) : List E :=
  let s := (⟨cap, []⟩ : Fs).absorbAll [p.1, p.2] dsObserve
  s.squeeze.2.cap ++ [cur * gen ^ 2, p.1 + s.squeeze.1 * (cl + (1 + s.squeeze.1) * p.2), s.squeeze.1]

theorem tailRets_length (cap : List E) (cur cl : E) (p : E × E) : (tailRets cap cur cl p).length = 8 := by
  simp [tailRets, Fs.squeeze, capOf]

/-- The closing rounds' calls at their exact arguments, each challenge stored at `tch·g^j`. -/
def TailC (C : CallRel) (rd : Reader) (tch tabs : E) : ℕ → List (E × E) → List E → E → E → Prop
  | _, [], _, _, _ => True
  | j, p :: rest, cap, cl, cur =>
    C "opening_tail_round" (cap ++ [cur, cl, tabs]) (tailRets cap cur cl p) ∧
      LoadHolds rd tch j ((tailRets cap cur cl p).getD 7 0) ∧
      TailC C rd tch tabs (j + 1) rest ((tailRets cap cur cl p).take 5) ((tailRets cap cur cl p).getD 6 0)
        (cur * gen ^ 2)

/-- The state after a closing round: its static facts. -/
theorem osTailRound_sf (tch j : ℕ) (st : OsSt) (hsf : st.Sf) : (osTailRound tch j st).2.Sf := by
  have k1 : st.k ≤ (osCurS st).2.2.k := osCurS_k st
  have ek : (osTailRound tch j st).2.k = (osCurS st).2.2.k + 8 := rfl
  refine ⟨rfl, ⟨fun f hf ↦ ?_, ?_, ?_, fun m hm ↦ ?_⟩, by show 0 < u128Bound; unfold u128Bound; positivity,
    fun p hp ↦ ?_, ?_⟩
  · have hf' : f ∈ [(osCurS st).2.2.k, (osCurS st).2.2.k + 1, (osCurS st).2.2.k + 2,
        (osCurS st).2.2.k + 3, (osCurS st).2.2.k + 4] := hf
    rw [ek]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
    rcases hf' with rfl | rfl | rfl | rfl | rfl <;> omega
  · show (osCurS st).2.2.k + 5 < (osCurS st).2.2.k + 8; omega
  · show (osCurS st).2.2.k + 6 < (osCurS st).2.2.k + 8; omega
  · obtain ⟨a, b, d⟩ := hsf.below.mats m hm; rw [ek]; exact ⟨by omega, by omega, by omega⟩
  · have := hsf.padB p hp; rw [ek]; omega
  · rw [ek]; have := hsf.k; omega

theorem osTailRound_k (tch j : ℕ) (st : OsSt) : st.k ≤ (osTailRound tch j st).2.k := by
  have := osCurS_k st
  show st.k ≤ _ + 8
  omega

theorem osTailRounds_k (tch : ℕ) : ∀ (n j : ℕ) (st : OsSt), st.k ≤ (osTailRounds tch j n st).2.k
  | 0, _, _ => le_rfl
  | n + 1, j, st => le_trans (osTailRound_k tch j st) (osTailRounds_k tch n (j + 1) _)

/-- **One closing round, honestly** (G:1699-1701). -/
theorem osTailRound_complete {tch j : ℕ} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, H C rd → st.Ok σ) (htch : tch < st.k) (p : E × E)
    (hC : ∀ C rd, H C rd → C "opening_tail_round" (st.fsv σ ++ [st.cur σ, σ (.n st.claim), σ (.n osTabs)])
        (tailRets (st.fsv σ) (st.cur σ) (σ (.n st.claim)) p) ∧
      LoadHolds rd (σ (.n tch)) j ((tailRets (st.fsv σ) (st.cur σ) (σ (.n st.claim)) p).getD 7 0)) :
    BlkA H σ st.k (osTailRound tch j st).2.k (osTailRound tch j st).1 (fun σ' ↦
      OsStep σ σ' st (osTailRound tch j st).2 ∧
      (osTailRound tch j st).2.F σ' = ⟨(tailRets (st.fsv σ) (st.cur σ) (σ (.n st.claim)) p).take 5, []⟩ ∧
      σ' (.n (osTailRound tch j st).2.claim) = (tailRets (st.fsv σ) (st.cur σ) (σ (.n st.claim)) p).getD 6 0 ∧
      (osTailRound tch j st).2.cur σ' = st.cur σ * gen ^ 2 ∧ (osTailRound tch j st).2.pad = st.pad) := by
  set cu := osCurS st with hcu
  set r := cu.2.2.k with hr
  set rets := tailRets (st.fsv σ) (st.cur σ) (σ (.n st.claim)) p with hrets
  have k1 : st.k ≤ r := osCurS_k st
  have pcu : cu.2.1 < r := osMat_ptr_lt _ _ _ hsf.below.cb
  have hA := osCurS_blkA (H := H) σ hsf.below.cb hsf.co
  have b1 := BlkA.seq k1 (show r ≤ r + 8 by omega) hA (B := [.call "opening_tail_round"
      ((st.fs ++ [cu.2.1, st.claim, osTabs]).map V.n) (osRun r 8)])
    (OutB := fun σ' ↦ ∀ i < 8, σ' (.n (r + i)) = rets.getD i 0) fun σ1 ha1 ho1 ↦ by
    refine call_blk rets (tailRets_length _ _ _ _) (fun i hi ↦ ?_) fun C rd hH ↦ ?_
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | rfl | rfl | rfl
      · have := hsf.below.fs i hi; omega
      · exact pcu
      · have := hsf.below.claim; omega
      · have := hsf.k; show 10 < r; omega
    · have e := ho1 C rd hH
      have hargs : (st.fs ++ [cu.2.1, st.claim, osTabs]).map (fun i ↦ σ1 (.n i)) =
          st.fsv σ ++ [st.cur σ, σ (.n st.claim), σ (.n osTabs)] := by
        simp only [List.map_append, List.map_cons, List.map_nil, OsSt.fsv]
        congr 1
        · exact List.map_congr_left fun f hf ↦ ha1 f (hsf.below.fs f hf)
        · rw [e, ha1 _ hsf.below.claim, ha1 osTabs (by have := hsf.k; show 10 < st.k; omega)]; rfl
      rw [hargs]
      exact (hC C rd hH).1
  have b2 := BlkA.seq (show st.k ≤ r + 8 by omega) (show r + 8 ≤ r + 8 from le_rfl) b1
    (B := [osLd (r + 7) tch j]) (OutB := fun _ ↦ True) fun σ1 ha1 ho1 ↦
      stores_blk fun C rd hH σ' ha ↦ by
        obtain ⟨-, e⟩ := ho1 C rd hH
        simp only [osLd, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_load]
        rw [ha _ (by omega), ha _ (by omega), e 7 (by omega), ha1 _ htch]
        exact (hC C rd hH).2
  have ek : (osTailRound tch j st).2.k = r + 8 := rfl
  rw [ek]
  refine BlkA.congr (BlkA.monoH b2.agree fun C rd hH σ' ha ⟨⟨⟨_, e0⟩, _⟩, hag⟩ ↦ ?_) (by
    simp only [osTailRound, List.append_assoc, List.cons_append, List.nil_append]; rfl)
  have hok' := hok C rd hH
  have hsf' := osTailRound_sf tch j st hsf
  refine ⟨⟨⟨hsf', matsOk_agree hok'.mats hsf.below.mats fun i hi ↦ hag i hi, ?_⟩, by omega, hag⟩,
    ?_, ?_, ?_, rfl⟩
  · exact (hok'.agree hag).pad
  · show (⟨[r, r + 1, r + 2, r + 3, r + 4].map (fun i ↦ σ' (.n i)), []⟩ : Fs) = _
    have l5 : (rets.take 5).length = 5 := by simp [hrets, tailRets_length]
    rw [five_getD l5]
    simp only [List.map_cons, List.map_nil]
    rw [show r = r + 0 from rfl, e0 0 (by omega), e0 1 (by omega), e0 2 (by omega), e0 3 (by omega),
      e0 4 (by omega)]
    simp [List.getD_eq_getElem?_getD]
  · show σ' (.n (r + 6)) = _; exact e0 6 (by omega)
  · show σ' (.n (r + 5)) * gen ^ 0 = _
    rw [e0 5 (by omega)]
    simp [hrets, tailRets, Fs.squeeze, capOf, OsSt.cur]

theorem tailRets_take (cap : List E) (cur cl : E) (p : E × E) :
    (tailRets cap cur cl p).take 5 = ((⟨cap, []⟩ : Fs).absorbAll [p.1, p.2] dsObserve).squeeze.2.cap := by
  simp [tailRets, Fs.squeeze, capOf]

theorem tailRets_claim (cap : List E) (cur cl : E) (p : E × E) :
    (tailRets cap cur cl p).getD 6 0 =
      p.1 + ((⟨cap, []⟩ : Fs).absorbAll [p.1, p.2] dsObserve).squeeze.1 *
        (cl + (1 + ((⟨cap, []⟩ : Fs).absorbAll [p.1, p.2] dsObserve).squeeze.1) * p.2) := by
  simp [tailRets, Fs.squeeze, capOf]

/-- **The closing rounds, honestly** (G:1699-1701): the sponge and claim after them
`tailRun`'s. -/
theorem osTailRounds_completeA {tch : ℕ} : ∀ (pairs : List (E × E)) (j : ℕ) (st : OsSt) (σ : Val),
    st.Sf → (∀ C rd, H C rd → st.Ok σ) → tch < st.k →
    (∀ C rd, H C rd → TailC C rd (σ (.n tch)) (σ (.n osTabs)) j pairs (st.fsv σ) (σ (.n st.claim))
      (st.cur σ)) →
    BlkA H σ st.k (osTailRounds tch j pairs.length st).2.k (osTailRounds tch j pairs.length st).1
      (fun σ' ↦ OsStep σ σ' st (osTailRounds tch j pairs.length st).2 ∧
        (osTailRounds tch j pairs.length st).2.F σ' =
          ⟨(tailRun pairs (st.fsv σ) (σ (.n st.claim))).2.2, []⟩ ∧
        σ' (.n (osTailRounds tch j pairs.length st).2.claim) =
          (tailRun pairs (st.fsv σ) (σ (.n st.claim))).2.1 ∧
        (osTailRounds tch j pairs.length st).2.cur σ' = st.cur σ * gen ^ (2 * pairs.length) ∧
        (osTailRounds tch j pairs.length st).2.pad = st.pad)
  | [], j, st, σ, hsf, hok, _, _ => by
    refine ⟨fun _ ↦ 0, fun C rd hH ↦ BlkF.nil fun σ' ha ↦ ?_⟩
    obtain ⟨eF, ec, ecl⟩ := hsf.vals ha
    exact ⟨⟨(hok C rd hH).agree ha, le_rfl, ha⟩, eF, ecl,
      show st.cur σ' = st.cur σ * gen ^ (2 * 0) by rw [ec]; simp, rfl⟩
  | p :: rest, j, st, σ, hsf, hok, htch, hT => by
    set st1 := (osTailRound tch j st).2 with hst1
    set rets := tailRets (st.fsv σ) (st.cur σ) (σ (.n st.claim)) p with hrets
    have hA := osTailRound_complete (H := H) (tch := tch) (j := j) σ hsf hok htch p fun C rd hH ↦
      ⟨(hT C rd hH).1, (hT C rd hH).2.1⟩
    have hk1 : st.k ≤ st1.k := osTailRound_k tch j st
    have hk2 : st1.k ≤ (osTailRounds tch (j + 1) rest.length st1).2.k :=
      osTailRounds_k tch rest.length (j + 1) st1
    have e : osTailRounds tch j (p :: rest).length st =
        ((osTailRound tch j st).1 ++ (osTailRounds tch (j + 1) rest.length st1).1,
          (osTailRounds tch (j + 1) rest.length st1).2) := rfl
    rw [e]
    refine BlkA.mono (BlkA.seq hk1 hk2 hA fun σ1 ha1 ho1 ↦ ?_) fun σ' ⟨_, ho⟩ ↦ ho
    have hsf1 : st1.Sf := osTailRound_sf tch j st hsf
    have hih := osTailRounds_completeA rest (j + 1) st1 σ1 hsf1 (fun C rd hH ↦ (ho1 C rd hH).1.ok)
      (lt_of_lt_of_le htch hk1) fun C rd hH ↦ by
        obtain ⟨_, eF, ecl, ecur, _⟩ := ho1 C rd hH
        have ef : st1.fsv σ1 = rets.take 5 := congrArg Fs.cap eF
        rw [ef, ecl, ecur, ha1 _ htch, ha1 osTabs (by have := hsf.k; show 10 < st.k; omega)]
        exact (hT C rd hH).2.2
    refine BlkA.monoH hih fun C rd hH σ' ha ⟨ho, eF, ecl, ecur, epad⟩ ↦ ?_
    obtain ⟨st1o, eF1, ecl1, ecur1, epad1⟩ := ho1 C rd hH
    have ef : st1.fsv σ1 = rets.take 5 := congrArg Fs.cap eF1
    rw [ef, ecl1, tailRets_take, tailRets_claim] at eF ecl
    refine ⟨⟨ho.ok, le_trans hk1 ho.le, fun i hi ↦ (ho.agree i (by omega)).trans
      (st1o.agree i hi)⟩, ?_, ?_, ?_, by rw [epad, epad1]⟩
    · rw [eF]; rfl
    · rw [ecl]; rfl
    · rw [ecur, ecur1, mul_assoc, ← pow_add]
      congr 2
      simp only [List.length_cons]
      ring

theorem osTailRounds_sf (tch : ℕ) : ∀ (n j : ℕ) (st : OsSt), st.Sf → (osTailRounds tch j n st).2.Sf
  | 0, _, _, h => h
  | n + 1, j, st, h => osTailRounds_sf tch n (j + 1) _ (osTailRound_sf tch j st h)

/-- The zeroed entries' values. -/
def tailZeros (m : ℕ) : List E := List.replicate m (word 0 0)

/-- **The closing rounds into `tail_challenges`, honestly** (G:1697-1705): the buffer allocated at
`pT`, the rounds, the unused entries zeroed. -/
theorem osTail_complete {c : OsCfg} {st : OsSt} (σ : Val) (hsf : st.Sf)
    (hok : ∀ C rd, H C rd → st.Ok σ) (pT : E) (pairs : List (E × E)) (hlen : pairs.length = c.yrLog)
    (hT : ∀ C rd, H C rd → TailC C rd pT (σ (.n osTabs)) 0 pairs (st.fsv σ) (σ (.n st.claim))
      (st.cur σ))
    (hz : ∀ C rd, H C rd → ∀ i < yrLogCap - c.yrLog, LoadHolds rd pT (c.yrLog + i) 0) :
    BlkA H σ st.k (osTail c st).2.1.k (osTail c st).1 (fun σ' ↦
      OsStep σ σ' st (osTail c st).2.1 ∧ (osTail c st).2.2 = st.k + 1 ∧
      σ' (.n st.k) = gw yrLogCap ∧ σ' (.n (st.k + 1)) = pT ∧
      (osTail c st).2.1.F σ' = ⟨(tailRun pairs (st.fsv σ) (σ (.n st.claim))).2.2, []⟩ ∧
      σ' (.n (osTail c st).2.1.claim) = (tailRun pairs (st.fsv σ) (σ (.n st.claim))).2.1 ∧
      (osTail c st).2.1.cur σ' = st.cur σ * gen ^ (2 * c.yrLog) ∧ (osTail c st).2.1.pad = st.pad) := by
  set k := st.k with hk
  set s0 : OsSt := { st with k := k + 2 } with hs0
  set f := osTailRounds (k + 1) 0 c.yrLog s0 with hf
  set j := f.2.k with hj
  set m := yrLogCap - c.yrLog with hm
  have hsf0 : s0.Sf := ⟨hsf.fs, ⟨fun x hx ↦ by have := hsf.below.fs x hx; show x < k + 2; omega,
    by have := hsf.below.cb; show st.cb < k + 2; omega, by have := hsf.below.claim; show st.claim < k + 2; omega,
    fun x hx ↦ by
      obtain ⟨a, b, d⟩ := hsf.below.mats x hx
      exact ⟨show x.out < k + 2 by omega, show x.src < k + 2 by omega, show x.base < k + 2 by omega⟩⟩,
    hsf.co, fun p hp ↦ by have := hsf.padB p hp; show p + 4 < k + 2; omega,
    by have := hsf.k; show 33 ≤ k + 2; omega⟩
  have kj : k + 2 ≤ j := by
    have := osTailRounds_k (k + 1) c.yrLog 0 s0
    exact this
  -- the buffer and the rounds
  have b1 := BlkA.seq (H := H) (show k ≤ k + 2 by omega) kj (heap_blk σ yrLogCap k pT)
    (B := f.1) (OutB := fun σ' ↦ f.2.Ok σ' ∧
      f.2.F σ' = ⟨(tailRun pairs (st.fsv σ) (σ (.n st.claim))).2.2, []⟩ ∧
      σ' (.n f.2.claim) = (tailRun pairs (st.fsv σ) (σ (.n st.claim))).2.1 ∧
      f.2.cur σ' = st.cur σ * gen ^ (2 * c.yrLog) ∧ f.2.pad = st.pad) fun σ1 ha1 ho1 ↦ by
    obtain ⟨eF, ec, ecl⟩ := hsf.vals ha1
    have efs : s0.fsv σ1 = st.fsv σ := congrArg Fs.cap eF
    have hok0 : ∀ C rd, H C rd → s0.Ok σ1 := fun C rd hH ↦ by
      have h := (hok C rd hH).agree ha1
      exact ⟨hsf0, h.mats, h.pad⟩
    have hT0 : ∀ C rd, H C rd → TailC C rd (σ1 (.n (k + 1))) (σ1 (.n osTabs)) 0 pairs (s0.fsv σ1)
        (σ1 (.n s0.claim)) (s0.cur σ1) := fun C rd hH ↦ by
      obtain ⟨-, e1⟩ := ho1 C rd hH
      rw [e1, efs, show s0.cur σ1 = st.cur σ from ec, show σ1 (.n s0.claim) = σ (.n st.claim) from ecl,
        ha1 osTabs (by have := hsf.k; show 10 < k; omega)]
      exact hT C rd hH
    have h := osTailRounds_completeA (H := H) (tch := k + 1) pairs 0 s0 σ1 hsf0 hok0
      (show k + 1 < k + 2 by omega) hT0
    rw [hlen] at h
    refine h.monoH fun C rd hH σ' _ ⟨ho, eF', ecl', ecur', epad'⟩ ↦ ?_
    rw [efs, show σ1 (.n s0.claim) = σ (.n st.claim) from ecl] at eF' ecl'
    exact ⟨ho.ok, eF', ecl', by rw [ecur', show s0.cur σ1 = st.cur σ from ec], epad'⟩
  -- the unused entries
  have b2 := BlkA.seq (H := H) (show k ≤ j by omega) (show j ≤ j + m by omega) b1
    (B := ((List.range m).map fun i ↦ [osCst (j + i) (word 0 0), osLd (j + i) (k + 1) (c.yrLog + i)]).flatten)
    (OutB := fun _ ↦ True) fun σ1 ha1 ho1 ↦ by
    refine ⟨lstF j (tailZeros m), fun C rd hH σ' ha hr ↦ ⟨?_, trivial⟩⟩
    obtain ⟨⟨-, e1⟩, -⟩ := ho1 C rd hH
    have ep : σ' (.n (k + 1)) = pT := by rw [ha _ (by omega), e1]
    rw [allOk_flatten]
    intro b hb
    simp only [List.mem_map, List.mem_range] at hb
    obtain ⟨i, hi, rfl⟩ := hb
    have v : σ' (.n (j + i)) = word 0 0 := by
      rw [lstF_at hr (by simp [tailZeros]) i (by simp [tailZeros]; omega)]
      simp [tailZeros, List.getD_eq_getElem?_getD, hi]
    simp only [osCst, osLd, allOk_cons, allOk_nil, and_true, stmtOk_atom, holds_const, holds_load, v,
      ep, word_zero]
    exact ⟨trivial, hz C rd hH i hi⟩
  have hsfj : f.2.Sf := osTailRounds_sf (k + 1) c.yrLog 0 s0 hsf0
  have ek : (osTail c st).2.1.k = j + m := rfl
  rw [ek]
  refine BlkA.congr (BlkA.monoH b2.agree fun C rd hH σ' ha ⟨⟨⟨⟨e0, e1⟩, hO, eF, ecl, ecur, epad⟩, _⟩, hag⟩ ↦ ?_)
    rfl
  refine ⟨⟨⟨⟨hsfj.fs, ⟨fun f' hf' ↦ by have := hsfj.below.fs f' hf'; show f' < j + m; omega,
      by have := hsfj.below.cb; show f.2.cb < j + m; omega,
      by have := hsfj.below.claim; show f.2.claim < j + m; omega,
      fun m' hm' ↦ by obtain ⟨a, b, d⟩ := hsfj.below.mats m' hm'; exact ⟨by omega, by omega, by omega⟩⟩,
      hsfj.co, fun p hp ↦ by have := hsfj.padB p hp; show p + 4 < j + m; omega,
      by have := hsfj.k; show 33 ≤ j + m; omega⟩, hO.mats, hO.pad⟩, by omega, hag⟩,
    rfl, e0, e1, eF, ecl, ecur, epad⟩

end
end LeanVM.Guest.B1.Whir
