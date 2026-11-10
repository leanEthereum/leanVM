/-
  LeanVM.Guest.B1.Gkr.Loop7Complete

  `__loop6` is complete: an iteration holds on its honest valuation when the memory holds its
  slot, its step's words, its round records and the next slot; iterations at every `g^j`,
  `j < m`, give the loop.
-/

module

public import LeanVM.Guest.B1.Gkr.Loop7C

/-!
# `__loop6`, completely (G:2047-2091)

`ly_iter`: from the slot of `L = 2j + 2 - sh` (`GkSlot`), one step of two levels
(`GkStepD.Ok`), its words at the cursor, its round records (`RecsAt`) and the slot of `L + 2` the
step leads to, the iteration at `g^j` holds (its body evaluated forward, region by region), given
the next iteration below the bound. `LyIter`: those words for the iteration at `g^j`;
`ly_complete`: with them at every `j < m`, `__loop6` holds from `1` below `g^m`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The children's words read, by tree. -/
theorem lyCh_of {σ : Val} {ch0 ch1 ch2 : List E} (h0 : ch0.length = 4) (h1 : ch1.length = 4)
    (h2 : ch2.length = 4) (hv : ∀ i < 12, σ (.n (lyEv i)) = (ch0 ++ (ch1 ++ ch2)).getD i 0) :
    lyCh σ 0 = ch0 ∧ lyCh σ 1 = ch1 ∧ lyCh σ 2 = ch2 := by
  rw [list4_eq h0, list4_eq h1, list4_eq h2] at hv ⊢
  rw [lyCh_eq, lyCh_eq, lyCh_eq, hv (4 * 0) (by omega), hv (4 * 0 + 1) (by omega),
    hv (4 * 0 + 2) (by omega), hv (4 * 0 + 3) (by omega), hv (4 * 1) (by omega),
    hv (4 * 1 + 1) (by omega), hv (4 * 1 + 2) (by omega), hv (4 * 1 + 3) (by omega),
    hv (4 * 2) (by omega), hv (4 * 2 + 1) (by omega), hv (4 * 2 + 2) (by omega),
    hv (4 * 2 + 3) (by omega)]
  simp

theorem tb_squeezeN_two (s : Fs) : s.squeezeN 2 =
    ([challengeOf s.perm, challengeOf (permOf (rateOf [] ++ capOf s.perm))],
      ⟨capOf (permOf (rateOf [] ++ capOf s.perm)), []⟩) := rfl

/-- `__loop6`'s arguments at `x = g^j`. -/
def lyArgs (x N : E) (sh : ℕ) (layers tabs rounds claim gmu kmn : E) : List E :=
  [x, N, gen ^ (2 - sh), layers, tabs, rounds, claim, gen ^ sh, gmu, kmn]

/-- **An iteration of `__loop6`, completely.** -/
theorem ly_iter {rd : Reader} {N layers tabs rounds claim gmu kmn : E} {j sh : ℕ}
    (hj : j < 2 ^ 30) (hsh2 : sh < 2) (hN : IsInK N) (hkmn : KModNext rd kmn)
    {s : Fs} {cur : E} {st : GkrState} {row pos : E} {D : GkStepD}
    (hS : GkSlot rd layers (2 * j + 2 - sh) s cur st row pos (gen ^ ((j + 1 - sh) / 4))
      (gen ^ ((j + 1 - sh) % 4)))
    (hD : D.Ok s st 2) (hx : TbReadsAt rd cur D.xs)
    (hR : RecsAt rd (rounds * pos) cur D.cs st.point (polyEval st.values s.squeeze.1)
      s.squeeze.2)
    (hS' : GkSlot rd layers (2 * j + 2 - sh + 2) (D.s' s st 2) (cur * gen ^ D.xs.length)
      (D.st' s st 2) (row * gen ^ 40) (pos * gen ^ (2 * j + 2 - sh + 1))
      (gen ^ ((j + 2 - sh) / 4)) (gen ^ ((j + 2 - sh) % 4)))
    (hnext : gen ^ j * gen + N ≠ 0 →
      coreProgram.Rel rd "__loop6" (lyArgs (gen ^ j * gen) N sh layers tabs rounds claim gmu kmn)
        []) :
    coreProgram.Rel rd "__loop6" (lyArgs (gen ^ j) N sh layers tabs rounds claim gmu kmn) [] := by
  obtain ⟨fn, hf, hp, hb⟩ := lyFound
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp ly_chk
  set args : List E := lyArgs (gen ^ j) N sh layers tabs rounds claim gmu kmn with hargs
  have hc6 : chk args.length lyEvL = some c' := hc'
  set σ : Val := B1.Val.ofArgs (ev rd (fun _ => 0) args lyEvL) with hσ
  have hG : ∀ s ∈ lyEvL, GoodS rd lyS (fun _ => 0) σ s :=
    (ev_spec rd (fun _ => 0) lyEvL args hc6).2.2
  have par : ∀ i < 10, σ (.n i) = args.getD i 0 := fun i hi =>
    ev_params rd _ hc6 (by simpa [hargs, lyArgs] using hi)
  have e0 : σ (.n 0) = gen ^ j := par 0 (by omega)
  have e1 : σ (.n 1) = N := par 1 (by omega)
  have e2 : σ (.n 2) = gen ^ (2 - sh) := par 2 (by omega)
  have e3 : σ (.n 3) = layers := par 3 (by omega)
  have e4 : σ (.n 4) = tabs := par 4 (by omega)
  have e5 : σ (.n 5) = rounds := par 5 (by omega)
  have e6 : σ (.n 6) = claim := par 6 (by omega)
  have e7 : σ (.n 7) = gen ^ sh := par 7 (by omega)
  have e8 : σ (.n 8) = gmu := par 8 (by omega)
  have e9 : σ (.n 9) = kmn := par 9 (by omega)
  set k := j + 1 - sh with hk
  set L := 2 * j + 2 - sh with hL
  have hLk : L = 2 * k + sh := by omega
  have hS0 := hS
  obtain ⟨hcl, hcap, hpe, hcur, hvl, hval, hrow, hpl, hpt, hpos, hhalf, hpar⟩ := hS
  obtain ⟨-, hcap', -, hcur', -, hval', hrow', -, hpt', hpos', hhalf', hpar'⟩ := hS'
  obtain ⟨hl, h4, hl0, hl1, hl2, hchk⟩ := hD
  set run := D.run s st with hrun
  have hcsl : D.cs.length = L := hl.trans hpl
  -- the head
  obtain ⟨hc0, hu0, hm0⟩ := hR 0 (by omega)
  simp only [List.take_zero, gkrRun, pow_zero, mul_one, Nat.mul_zero] at hc0 hu0 hm0
  obtain ⟨R1, e10, e11, e17, e42, e46, e47, m48, e53, e54, e56, e57, c25, c26, c27, c28⟩ :=
    lyc_head (C := coreProgram.Rel rd) (kret := fun rs => rs = []) hG e0 e2 hsh2
      (by rw [e3]; exact hS0) (by rw [e5]; exact hc0) (by rw [e5]; exact hu0)
      (by rw [e5]; exact hm0)
  rw [e5] at m48
  -- the rounds
  have hflat : TbReadsAt rd cur D.cs.flatten := (tbReadsAt_append.mp hx).1
  have hysl : (D.ys s st 2).length = 2 := rfl
  have hpt2 := tbReadsAt_append.mp hpt'
  have hch42 : TbReadsAt rd (row * gen ^ 42) run.1 := by
    have := hpt2.2
    rwa [hysl, mul_assoc, ← pow_add] at this
  have hT : ∀ a k', a + k' ≤ 2 * k + sh →
      TbGkrRoundsOut k' rd (σ (.n 48) * gen ^ a) (σ (.n 46) * gen ^ a) := by
    intro a k' hak
    rw [m48, e46]
    exact recs_rounds hR rfl hl h4 hflat hpt hch42 (by omega)
  have R2 := lyc_rounds (kret := fun rs => rs = []) hG hj hsh2 hk e10 e7 e53 e54 e56 e57 hT
  -- the last record
  obtain ⟨hcL, huL, hlL⟩ := hR L (by omega)
  have htk : D.cs.take L = D.cs := List.take_of_length_le (by omega)
  have htp : st.point.take L = st.point := List.take_of_length_le (by omega)
  rw [htk, htp] at hcL hlL
  obtain ⟨R3, m69, e70, e75⟩ := lyc_last (C := coreProgram.Rel rd) (kret := fun rs => rs = [])
    hG e11 (by rw [m48]; exact hcL) (by rw [m48]; exact huL)
  -- the children
  have hchl : (D.ch0 ++ (D.ch1 ++ D.ch2)).length = 12 := by simp [hl0, hl1, hl2]
  have hrc : TbReadsAt rd (σ (.n 75)) (D.ch0 ++ (D.ch1 ++ D.ch2)) := by
    have := (tbReadsAt_append.mp hx).2
    rwa [flatten_length_four h4, hcsl, ← e75] at this
  obtain ⟨R4, EV, B1⟩ := lyc_children (C := coreProgram.Rel rd) (kret := fun rs => rs = []) hG
    hcL.1 e70 hchl hrc
  obtain ⟨hch0, hch1, hch2⟩ := lyCh_of hl0 hl1 hl2 fun i hi => (EV i hi).1
  rw [hch0, hch1] at B1
  -- the check and the new coordinates
  have hcheck : run.2.1 =
      polyEval [prodE (lyCh σ 0), prodE (lyCh σ 1), prodE (lyCh σ 2)] (σ (.n 42)) := by
    rw [hch0, hch1, hch2, e42]; exact hchk
  obtain ⟨R5, e180, e194, e189⟩ := lyc_check (C := coreProgram.Rel rd)
    (kret := fun rs => rs = []) hG (fun i hi => (EV i hi).2.1) (fun i hi => (EV i hi).2.2) B1
    (by rw [m69, m48]; exact hlL) hcheck c25 c26 c27 c28
  rw [hch2] at e180 e194 e189
  have hpend : run.2.2.pend = [] :=
    tb_gkrRun_pend D.cs st.point (polyEval st.values s.squeeze.1) s.squeeze.2 rfl
  have hp0 : run.2.2 = ⟨run.2.2.cap, []⟩ := by rw [← hpend]
  have hsb : D.sb s st = ⟨capOf (Fs.perm ⟨capOf (Fs.perm ⟨run.2.2.cap,
      D.ch0.map (·, dsObserve)⟩), D.ch1.map (·, dsObserve)⟩), D.ch2.map (·, dsObserve)⟩ := by
    show (((run.2.2.absorbAll D.ch0 dsObserve).absorbAll D.ch1 dsObserve).absorbAll D.ch2
      dsObserve) = _
    rw [hp0, absorbAll_short ⟨run.2.2.cap, []⟩ D.ch0 dsObserve (by simp [hl0]), List.nil_append,
      tb_absorbAll_full ⟨run.2.2.cap, D.ch0.map (·, dsObserve)⟩ (by simp [hl0]) D.ch1 hl1,
      tb_absorbAll_full _ (by simp [hl1]) D.ch2 hl2]
  have hys : D.ys s st 2 = [σ (.n 180), σ (.n 194)] := by
    rw [e180, e194]; show ((D.sb s st).squeezeN 2).1 = _; rw [hsb, tb_squeezeN_two]; rfl
  have hs' : D.s' s st 2 = ⟨(List.range 5).map fun k ↦ σ (.n (189 + k)), []⟩ := by
    rw [e189]; show ((D.sb s st).squeezeN 2).2 = _; rw [hsb, tb_squeezeN_two]; rfl
  -- the next slot
  have ld : ∀ k w, LoadHolds rd layers (13 * (L + 2) + k) w →
      LoadHolds rd (σ (.n 17)) (26 + k) w := fun k w h => by
    rw [e17, e3, tb_loadHolds_mul_gen_pow, show 13 * L + (26 + k) = 13 * (L + 2) + k by ring]
    exact h
  have s26 : ∀ k < 5, LoadHolds rd (σ (.n 17)) (26 + k) (σ (.n (189 + k))) := by
    intro k hk
    have := hcap' k hk
    rw [hs'] at this
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
      Option.map_some, Option.getD_some] at this
    exact ld k _ this
  have hxl : D.xs.length = 4 * L + 12 := by
    simp [GkStepD.xs, flatten_length_four h4, hcsl, hl0, hl1, hl2]
  have s31 : LoadHolds rd (σ (.n 17)) 31 (σ (.n 75) * gen ^ 12) := by
    have h := ld 5 _ hcur'
    rw [hxl] at h
    rw [e75, mul_assoc, ← pow_add]
    exact h
  have sv : ∀ t < 3, LoadHolds rd (σ (.n 17)) (32 + t)
      (multilinearEval (lyCh σ t) [σ (.n 180), σ (.n 194)]) := by
    intro t ht
    have h := ld (6 + t) _ (by rw [← Nat.add_assoc]; exact hval' t ht)
    rw [show 26 + (6 + t) = 32 + t by ring] at h
    have hv : (D.st' s st 2).values.getD t 0 =
        multilinearEval (lyCh σ t) [σ (.n 180), σ (.n 194)] := by
      show ([D.ch0, D.ch1, D.ch2].map (multilinearEval · (D.ys s st 2))).getD t 0 = _
      rw [hys]
      interval_cases t
      · rw [hch0]; rfl
      · rw [hch1]; rfl
      · rw [hch2]; rfl
    rwa [hv] at h
  have s35 : LoadHolds rd (σ (.n 17)) 35 (σ (.n 46) * gen ^ 40) := by
    have h := ld 9 _ hrow'
    rw [e46]; exact h
  have s36 : LoadHolds rd (σ (.n 17)) 36 (σ (.n 47) * σ (.n 11) * gen) := by
    have h := ld 10 _ hpos'
    rwa [e47, e11, mul_assoc, ← pow_succ]
  obtain ⟨k4, k0⟩ := hkmn (k % 4) (Nat.mod_lt _ (by omega))
  have k4' : LoadHolds rd (σ (.n 9) * σ (.n 54)) 4 (gen ^ ((k % 4 + 1) / 4)) := by
    rw [e9, e54, tb_loadHolds_mul_gen_pow, show k % 4 + 4 = 4 + k % 4 by omega]; exact k4
  have k0' : LoadHolds rd (σ (.n 9) * σ (.n 54)) 0 (gen ^ ((k % 4 + 1) % 4)) := by
    rw [e9, e54, tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact k0
  have hk1 : j + 2 - sh = k + 1 := by omega
  have s37 : LoadHolds rd (σ (.n 17)) 37 (σ (.n 53) * gen ^ ((k % 4 + 1) / 4)) := by
    have h := ld 11 _ hhalf'
    rw [hk1] at h
    rwa [e53, ly_half_next k]
  have s38 : LoadHolds rd (σ (.n 17)) 38 (gen ^ ((k % 4 + 1) % 4)) := by
    have h := ld 12 _ hpar'
    rw [hk1] at h
    rwa [ly_parity_next k]
  have s40 : LoadHolds rd (σ (.n 46)) 40 (σ (.n 180)) := by
    have h := hpt2.1 0 (by rw [hysl]; omega)
    simp only [hys, List.getElem_cons_zero] at h
    rw [tb_loadHolds_mul_gen_pow] at h
    rw [e46]; exact h
  have s41 : LoadHolds rd (σ (.n 46)) 41 (σ (.n 194)) := by
    have h := hpt2.1 1 (by rw [hysl]; omega)
    simp only [hys, List.getElem_cons_succ, List.getElem_cons_zero] at h
    rw [tb_loadHolds_mul_gen_pow] at h
    rw [e46]; exact h
  have hK : IsInK (σ (.n 0) * gen + σ (.n 1)) := by
    rw [e0, e1]
    exact tb_isInK_add (tb_isInK_mul (tb_gen_pow_isInK _) (by simpa using tb_gen_pow_isInK 1)) hN
  have R6 := lyc_stores (C := coreProgram.Rel rd) (kret := fun rs => rs = []) hG
    (fun i hi => (EV i hi).2.1) s40 s41 s26 s31 sv s35 s36 k4' k0' s37 s38 hK (fun hne => by
      rw [e0, e1] at hne
      rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
      exact hnext hne)
  refine (tb_rel_pre hf (hb.trans lyBody_eq) lyPre_noRet args []).mpr ⟨σ, ?_, ?_, rfl⟩
  · rw [hp]
    show [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7),
      σ (.n 8), σ (.n 9)] = args
    rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
    rfl
  · rw [lyPre_eq]
    refine (tb_holdsList_append_noRet (A := lyR1 ++ lyR2 ++ lyR3 ++ lyR4 ++ lyR5)
      (by decide +kernel)).mpr ⟨?_, R6⟩
    refine (tb_holdsList_append_noRet (A := lyR1 ++ lyR2 ++ lyR3 ++ lyR4)
      (by decide +kernel)).mpr ⟨?_, R5⟩
    refine (tb_holdsList_append_noRet (A := lyR1 ++ lyR2 ++ lyR3)
      (by decide +kernel)).mpr ⟨?_, R4⟩
    refine (tb_holdsList_append_noRet (A := lyR1 ++ lyR2) (by decide +kernel)).mpr ⟨?_, R3⟩
    exact (tb_holdsList_append_noRet (A := lyR1) (by decide +kernel)).mpr ⟨R1, R2⟩

/-- **An iteration's words**: the slot of `L = 2j + 2 - sh`, one step of two levels, its words at
the cursor, its round records, and the slot of `L + 2`. -/
def LyIter (rd : Reader) (layers rounds : E) (sh j : ℕ) : Prop :=
  ∃ (s : Fs) (cur : E) (st : GkrState) (row pos : E) (D : GkStepD),
    GkSlot rd layers (2 * j + 2 - sh) s cur st row pos (gen ^ ((j + 1 - sh) / 4))
      (gen ^ ((j + 1 - sh) % 4)) ∧
    D.Ok s st 2 ∧ TbReadsAt rd cur D.xs ∧
    RecsAt rd (rounds * pos) cur D.cs st.point (polyEval st.values s.squeeze.1) s.squeeze.2 ∧
    GkSlot rd layers (2 * j + 2 - sh + 2) (D.s' s st 2) (cur * gen ^ D.xs.length) (D.st' s st 2)
      (row * gen ^ 40) (pos * gen ^ (2 * j + 2 - sh + 1)) (gen ^ ((j + 2 - sh) / 4))
      (gen ^ ((j + 2 - sh) % 4))

/-- **`__loop6`, completely**: an iteration's words at every `j < m` give the loop from `1` below
`g^m`. -/
theorem ly_complete {rd : Reader} {layers tabs rounds claim gmu kmn : E} {sh m : ℕ} (hm : 0 < m)
    (hmb : m < 2 ^ 30) (hsh2 : sh < 2) (hkmn : KModNext rd kmn)
    (hit : ∀ j < m, LyIter rd layers rounds sh j) :
    coreProgram.Rel rd "__loop6" (lyArgs 1 (gen ^ m) sh layers tabs rounds claim gmu kmn) [] := by
  have key : ∀ t, t < m → coreProgram.Rel rd "__loop6"
      (lyArgs (gen ^ (m - 1 - t)) (gen ^ m) sh layers tabs rounds claim gmu kmn) [] := by
    intro t
    induction t with
    | zero =>
      intro _
      obtain ⟨s, cur, st, row, pos, D, h1, h2, h3, h4, h5⟩ := hit (m - 1 - 0) (by omega)
      refine ly_iter (by omega) hsh2 (tb_gen_pow_isInK _) hkmn h1 h2 h3 h4 h5 fun hne => ?_
      rw [← pow_succ, show m - 1 - 0 + 1 = m by omega, e_add_self] at hne
      exact absurd rfl hne
    | succ t ih =>
      intro ht
      obtain ⟨s, cur, st, row, pos, D, h1, h2, h3, h4, h5⟩ := hit (m - 1 - (t + 1)) (by omega)
      refine ly_iter (by omega) hsh2 (tb_gen_pow_isInK _) hkmn h1 h2 h3 h4 h5 fun _ => ?_
      rw [← pow_succ, show m - 1 - (t + 1) + 1 = m - 1 - t by omega]
      exact ih (by omega)
  have := key (m - 1) (by omega)
  rwa [show m - 1 - (m - 1) = 0 by omega, pow_zero] at this

end
end LeanVM.Guest.B1.Tables
