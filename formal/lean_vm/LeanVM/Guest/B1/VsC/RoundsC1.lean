/-
  LeanVM.Guest.B1.VsC.RoundsC1

  `link_round`'s template at one bit of grind, evaluated forward on a chain of rounds, holds,
  its hints exact, and returns the chain's states.
-/

module

public import LeanVM.Guest.B1.VsC.RoundsC
public import LeanVM.Guest.B1.VsC.RoundsA
public import LeanVM.Guest.B1.Bits.GrindFwd
public import LeanVM.Guest.B1.Bits.GrindWin
public import LeanVM.Guest.Memory.LowDef

/-!
# Rounds with one bit of grind, completely

A round grinding one bit inlines `grind_check` at one bit, whose atoms hold only when the proof of
work passes. The sponge before the grind (`lrA_nonce`, from the atoms before it) is the chain's,
so the chain's `GrindOk` gives the proof of work on the template's word; the windows the oracle
gives are then the honest ones (`gcInlineO_vals_of_shape` at `GcShape 1`), `grind_check` holds
(`gcInline_complete_one`) and its hints are exact (`gcInline_exact_of_shape`). The round's
outputs are the chain's by `lrRound_stepP` and `roundStep_det`.

The oracle for the windows is per memory: round `r`'s word is `roundWord rd nt st_r`, lane `1` of
the nonce's permutation from the chain's state `st_r` over the words the memory holds at its
cursor. `winOracle` reads it from a list of the grinds' first values and words, their window runs
apart.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.Value
open LeanVM.Guest.B1.Link LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-! ## `grind_check` at one bit -/

theorem gcShape_one : GcShape 1 := ⟨by decide, by decide⟩

theorem gcPre_vals_one :
    (Stmt.valsList (gcPre 1)).all (fun v => decide (v = .n v.idx ∧ v.idx < gcLen 1)) = true := by decide

/-- `gcPre_complete_of` at one bit. -/
theorem gcPre_complete_one {C : CallRel} {rd : Reader}
    (hrc : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2)
    {w tabs : E} (ht : WinTabs rd tabs) (hlow : ((w.limb 0).lane.toNat % 2 ^ 1 = 0)) {σ : Val}
    (hσ : ∀ k < gcLen 1, σ (.n k) = gcVals rd 1 w tabs k) {next : Prop} (hn : next)
    {kret : List E → Prop} : Stmt.HoldsList C rd σ (gcPre 1) next kret := by
  have hv : ∀ v ∈ Stmt.valsList (gcPre 1), σ v = gcVals rd 1 w tabs v.idx := by
    intro v hv
    obtain ⟨hve, hlt⟩ := of_decide_eq_true (List.all_eq_true.mp gcPre_vals_one v hv)
    rw [hve]
    exact hσ _ hlt
  rw [Sig.holdsList_congr (σ' := fun v => gcVals rd 1 w tabs v.idx) (gcPre 1) hv next kret,
    holds_gcPre]
  obtain ⟨hh, hi, htl⟩ := gc_complete_of hrc gcShape_one.1 gcShape_one.2 ht hlow
  exact ⟨hh, hi, htl, hn⟩

/-- **`grind_check` at one bit, inlined, is complete** on the honest values. -/
theorem gcInline_complete_one {C : CallRel} {rd : Reader}
    (hrc : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2)
    {o : ℕ} {w tabs : V} {σ : Val} (ht : WinTabs rd (σ tabs))
    (hlow : ((σ w).limb 0).lane.toNat % 2 ^ 1 = 0)
    (hσ : ∀ k, 2 ≤ k → k < gcLen 1 → σ (.n (o + k - 2)) = gcVals rd 1 (σ w) (σ tabs) k)
    {next : Prop} (hn : next) {kret : List E → Prop} :
    Stmt.HoldsList C rd σ (gcInlineT 1 o w tabs) next kret := by
  rw [gcInlineT, Stmt.holdsList_rename]
  exact gcPre_complete_one hrc ht hlow (gcRen_vals hσ) hn

/-- **The windows' range checks pass** on a memory defined on its first `2^k` words, `11 ≤ k`. -/
theorem hrc_of_lowDef {k : ℕ} {rd : Reader} (hl : LowDef k rd) (hk : 11 ≤ k) :
    ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2 := by
  intro v hv e he
  obtain ⟨h1, h2, h3⟩ := rc_complete_low hl (K := 2 ^ v) (e := e)
    (le_trans (Nat.pow_le_pow_right (by norm_num) hv) (Nat.pow_le_pow_right (by norm_num) hk)) he
  refine ⟨_, _, _, by rw [gen_pow_eq_ofK]; exact h1, ?_, h3⟩
  rw [wBound_eq hv, gen_pow_eq_ofK, gen_pow_eq_ofK, h2]

/-! ## The atoms before the grind -/

/-- **The atoms before a round's grind needing a side condition**: a load at the cursor, or a
product. -/
theorem lrRoundA_side {nt bits o : ℕ} {cap : List ℕ} {cur : ℕ} {pad : Option ℕ} {a : Atom}
    (ha : Stmt.atom a ∈ lrRoundA nt bits o cap cur pad) (hn : needsSide a = true) :
    (∃ d i, a = .load d (.n cur) i ∧ (i ≤ nt ∨ i = nt + 1)) ∨ (∃ d x y, a = .mul d x y) := by
  unfold lrRoundA at ha
  simp only [List.mem_append, List.mem_flatten, List.mem_map, List.mem_range] at ha
  rcases ha with (((⟨_, ⟨i, hi, rfl⟩, hs⟩ | hs) | hs) | hs)
  · unfold lrStep lrScalar at hs
    simp only [List.mem_append] at hs
    rcases hs with hs | hs
    · split at hs
      · simp only [List.mem_singleton, lrPerm, Stmt.atom.injEq] at hs; subst hs; simp [needsSide] at hn
      · simp at hs
    · left
      split at hs <;> simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at hs <;>
        rcases hs with rfl | rfl | rfl | rfl <;>
        first | exact ⟨_, _, rfl, Or.inl (by omega)⟩ | simp [needsSide] at hn
  · split at hs
    · simp at hs
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at hs
      rcases hs with hs | rfl | rfl | rfl
      · split at hs
        · simp only [List.mem_singleton, lrPerm, Stmt.atom.injEq] at hs; subst hs; simp [needsSide] at hn
        · simp at hs
      · exact Or.inl ⟨_, _, rfl, Or.inr rfl⟩
      all_goals simp [needsSide] at hn
  · unfold lrPadCells at hs
    split at hs
    · simp at hs
    split at hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at hs
      rcases hs with rfl | rfl <;> simp [needsSide] at hn
    split at hs
    · simp at hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp [needsSide] at hn
  · simp only [List.mem_singleton, Stmt.atom.injEq] at hs; subst hs; simp [needsSide] at hn

/-! ## `grind_check`'s table reads -/

/-- A load of `grind_check`'s template at one bit: at offset `0`, through the head's or a step's
pointer. -/
def gcLoadOk1 : Stmt → Bool
  | .atom (.load _ p off) => off == 0 && (p.idx == gcW 1 + 7 ||
      (List.range (gcW 1)).any fun i => p.idx == gcW 1 + 9 * (i + 1) + 6)
  | _ => true

set_option maxRecDepth 100000 in
theorem gcPre_loads_one : (gcPre 1).all gcLoadOk1 = true := by decide +kernel

/-- **`grind_check`'s loads at one bit, inlined**: its table reads, through `gcPtrs`, at offset `0`. -/
theorem gcInlineT_load_one {o : ℕ} {w tabs d p : V} {off : ℕ}
    (h : Stmt.atom (.load d p off) ∈ gcInlineT 1 o w tabs) : off = 0 ∧ p ∈ gcPtrs 1 o := by
  obtain ⟨s0, hs0, e⟩ := renameList_mem_inv h
  have hok := List.all_eq_true.mp gcPre_loads_one s0 hs0
  cases s0 with
  | atom a0 =>
    cases a0 with
    | load d0 p0 off0 =>
      simp only [Stmt.rename, Atom.rename, Stmt.atom.injEq, Atom.load.injEq] at e
      obtain ⟨-, rfl, rfl⟩ := e
      simp only [gcLoadOk1, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, List.any_eq_true,
        List.mem_range] at hok
      obtain ⟨rfl, hp⟩ := hok
      have h0 : ¬ p0.idx = 0 := by rcases hp with hp | ⟨i, -, hp⟩ <;> omega
      have h1 : ¬ p0.idx = 1 := by rcases hp with hp | ⟨i, -, hp⟩ <;> omega
      have hR : gcRen o w tabs p0 = .n (o + p0.idx - 2) := by
        show (if p0.idx = 0 then w else if p0.idx = 1 then tabs else .n (o + p0.idx - 2)) = _
        simp only [h0, h1, ↓reduceIte]
      refine ⟨rfl, ?_⟩
      rw [hR]
      unfold gcPtrs
      rcases hp with hp | ⟨i, hi, hp⟩
      · rw [hp, show o + (gcW 1 + 7) - 2 = o + gcW 1 + 5 by omega]
        exact List.mem_cons_self
      · rw [hp, show o + (gcW 1 + 9 * (i + 1) + 6) - 2 = o + gcW 1 + 9 * (i + 1) + 4 by omega]
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    | _ => simp [Stmt.rename, Atom.rename] at e
  | _ => simp [Stmt.rename] at e

/-- **`grind_check`'s table reads' pointers** on its honest values: each a table word `tabs·g^e`,
`e < 2^11`. -/
theorem gcPtrs_of_vals {rd : Reader} {σ : Val} {b o : ℕ} (hb : GcShape b) {w tabs : V}
    (hv : ∀ k, 2 ≤ k → k < gcLen b → σ (.n (o + k - 2)) = gcVals rd b (σ w) (σ tabs) k) :
    ∀ p ∈ gcPtrs b o, ∃ e < 2 ^ 11, σ p = σ tabs * gen ^ e := by
  obtain ⟨⟨-, hT, hsum⟩, -⟩ := hb
  intro p hp
  simp only [gcPtrs, List.mem_cons, List.mem_map, List.mem_range] at hp
  rcases hp with rfl | ⟨i, hi, rfl⟩
  · refine ⟨gcV b (σ w) 0, lt_of_lt_of_le (gcV_zero_lt hsum (σ w)) (Nat.pow_le_pow_right (by decide) hT), ?_⟩
    have := hv (gcW b + 7) (by omega) (by unfold gcLen; omega)
    rw [show o + (gcW b + 7) - 2 = o + gcW b + 5 by omega] at this
    rw [this, gv_top_ptr]
  · refine ⟨gcV b (σ w) (i + 1) % 2 ^ 11, Nat.mod_lt _ (by positivity), ?_⟩
    have := hv (gcW b + 9 * (i + 1) + 6) (by omega) (by unfold gcLen; omega)
    rw [show o + (gcW b + 9 * (i + 1) + 6) - 2 = o + gcW b + 9 * (i + 1) + 4 by omega,
      gv_iter (by omega) (by omega) (by omega)] at this
    rw [this]
    rfl

/-! ## A round grinding one bit -/

/-- The word a round's grind checks, from the state `st` and the words the memory holds at its
cursor: lane `1` of the nonce's permutation. -/
noncomputable def roundWord (rd : Reader) (nt : ℕ) (st : RSt) : E :=
  cellsOfState (((((⟨st.cap, []⟩ : Fs).absorb (rdAt rd st.cur 0) dsObserve).absorbAll
    ((List.range nt).map fun i => rdAt rd st.cur (i + 1)) dsObserve).nonceState
      (rdAt rd st.cur (nt + 1)))) false ⟨1, by norm_num⟩

/-- **A round grinding one bit holds on its forward valuation**, from the chain's step, the
windows' oracle the honest one; its hints are exact. -/
theorem lrRound_complete1 {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {nt o : ℕ} {cap : List ℕ}
    {cur cl tabs : ℕ} {pad : Option ℕ} (hnt : 1 ≤ nt) (hnt' : nt ≤ 32) (hk3 : nt % 4 ≠ 3)
    (hG : ∀ a, Stmt.atom a ∈ lrRound nt 1 o cap cur cl tabs pad → Good rd S w σ a)
    (hmf : ∀ d x y, Stmt.atom (.mul d x y) ∈ lrRound nt 1 o cap cur cl tabs pad → x.idx < d.idx ∧ y.idx < d.idx)
    (hcS : ∀ d i, Atom.load d (.n cur) i ∉ S)
    (hpad : ∀ z, pad = some z → ∀ j < 4, σ (.n (z + j)) = 0)
    {st st' : RSt} {y : E} (hst : rstOf σ cap cur cl = st) (hstep : RoundStep rd nt 1 st y st')
    (hto : tabs < lrF o nt 1 pad + 13)
    (hSg : ∀ a ∈ S, loadInto (lrF o nt 1 pad + 13) (lrF o nt 1 pad + 13 + (gcLen 1 - 2)) a = false)
    (hrc : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2)
    (ht : WinTabs rd (σ (.n tabs)))
    (hwin : ∀ j ≤ gcW 1, w (lrF o nt 1 pad + 13 + j) = gcWin 1 (roundWord rd nt st) j) :
    (∀ a, Stmt.atom a ∈ lrRound nt 1 o cap cur cl tabs pad → a.Holds rd σ ∧ ∀ rd', a.Exact rd' σ) ∧
      σ (.n (lrD o nt 1 pad + 3)) = y ∧
      rstOf σ (lrOutCap nt 1 o pad) (lrD o nt 1 pad + 6) (lrD o nt 1 pad + 8) = st' ∧
      (∀ z, lrPad nt 1 o pad = some z → ∀ j < 4, σ (.n (z + j)) = 0) ∧
      ∀ p ∈ gcPtrs 1 (lrF o nt 1 pad + 13), ∃ e < 2 ^ 11, σ p = σ (.n tabs) * gen ^ e := by
  have hcur : σ (.n cur) = st.cur := by rw [← hst]; rfl
  obtain ⟨c0, tail, n, htl, hr, hok, -⟩ := id hstep
  have hcurL : ∀ d i, (i ≤ nt ∨ i = nt + 1) → Side rd S σ (.load d (.n cur) i) := by
    intro d i hi
    have hi' : i < (c0 :: tail ++ grindWords 1 n).length := by
      simp only [grindWords, one_ne_zero, ↓reduceIte, List.length_append, List.length_cons, htl]
      omega
    have hl := hr i hi'
    rw [← hcur] at hl
    simp only [Side, hcS d i, ↓reduceIte]
    exact ⟨hl.1, by rw [hl.2]; rfl⟩
  -- the atoms before the grind
  have hAA : ∀ a, Stmt.atom a ∈ lrRoundA nt 1 o cap cur pad → a.Holds rd σ := by
    intro a ha
    refine atoms_holds (atoms := [a]) (S := S) (w := w)
      (fun b hb => by rw [List.mem_singleton.mp hb]; exact hG a (mem_lrRound_of_A ha)) (fun b hb hn => ?_)
      a List.mem_cons_self
    rw [List.mem_singleton.mp hb] at hn ⊢
    rcases lrRoundA_side ha hn with ⟨d, i, rfl, hi⟩ | ⟨d, x, y, rfl⟩
    · exact Or.inr (hcurL d i hi)
    · simp [needsSide, hmf d x y (mem_lrRound_of_A ha)] at hn
  -- the sponge before the grind is the chain's
  obtain ⟨hrd, hword⟩ := lrA_nonce hAA hk3 rfl hpad
  rw [hcur] at hrd
  have he := readsAt_eq hrd hr (by simp [lrXs, grindWords, htl])
  rw [lrXs_eq] at he
  simp only [List.cons_append, List.cons.injEq, grindWords, one_ne_zero, ↓reduceIte] at he
  obtain ⟨rfl, he⟩ := he
  obtain ⟨rfl, hn⟩ := List.append_inj he (by simp [lrT, htl])
  simp only [List.cons.injEq, and_true] at hn
  have hcap : cap.map (σ ∘ .n) = st.cap := by rw [← hst]; rfl
  rw [lrXs_eq, absorbAll_cons, hcap, hn] at hword
  have hpow : ((σ (.n (lrF o nt 1 pad + 1))).limb 0).lane.toNat % 2 ^ 1 = 0 := by
    rw [hword]; exact (grindOk_iff one_ne_zero n).mp hok
  have hrdAt : ∀ i (h : i < (lrX σ o 0 :: lrT σ o nt ++ [n]).length),
      rdAt rd st.cur i = (lrX σ o 0 :: lrT σ o nt ++ [n])[i] := fun i h => rdAt_of_loadHolds (hr i h)
  have hW : roundWord rd nt st = σ (.n (lrF o nt 1 pad + 1)) := by
    have e0 : rdAt rd st.cur 0 = lrX σ o 0 := by rw [hrdAt 0 (by simp)]; rfl
    have e1 : (List.range nt).map (fun i => rdAt rd st.cur (i + 1)) = lrT σ o nt := by
      refine List.ext_getElem (by simp [htl]) fun i h1 h2 => ?_
      simp only [List.getElem_map, List.getElem_range]
      rw [hrdAt (i + 1) (by simp only [List.length_append, List.length_cons]; omega)]
      simp only [List.cons_append, List.getElem_cons_succ]
      rw [List.getElem_append_left h2]
    have e2 : rdAt rd st.cur (nt + 1) = n := by
      rw [hrdAt (nt + 1) (by simp [htl])]
      simp only [List.cons_append, List.getElem_cons_succ]
      rw [List.getElem_append_right (by omega)]
      simp [htl]
    rw [hword, roundWord, e0, e1, e2]
  -- the grind
  have hgi : ∀ s ∈ gcInlineT 1 (lrF o nt 1 pad + 13) (.n (lrF o nt 1 pad + 1)) (.n tabs), GoodS rd S w σ s := by
    intro s hs
    obtain ⟨a, rfl⟩ := gcInlineT_atoms (lrF o nt 1 pad + 13) _ _ s hs
    exact hG a (mem_lrRound_grind one_ne_zero hs)
  have hvals := gcInlineO_vals_of_shape (off := 0) gcShape_one (o := lrF o nt 1 pad + 13)
    (w := .n (lrF o nt 1 pad + 1)) (tabs := .n tabs)
    (by show lrF o nt 1 pad + 1 < lrF o nt 1 pad + 13; omega) (by show tabs < lrF o nt 1 pad + 13; omega)
    hgi hSg hrc (by rwa [pow_zero, mul_one]) (fun j hj => by rw [hwin j hj, hW])
  have hgH : Stmt.HoldsList (fun _ _ _ => True) rd σ
      (gcInlineT 1 (lrF o nt 1 pad + 13) (.n (lrF o nt 1 pad + 1)) (.n tabs)) True (fun _ => True) :=
    gcInline_complete_one hrc ht hpow hvals trivial
  have hgA := ((holdsList_atoms (gcInlineT_atoms _ _ _) _ _).mp hgH).1
  -- every atom
  have hA : ∀ a, Stmt.atom a ∈ lrRound nt 1 o cap cur cl tabs pad → a.Holds rd σ := by
    intro a ha
    refine atoms_holds (atoms := [a]) (S := S) (w := w)
      (fun b hb => by rw [List.mem_singleton.mp hb]; exact hG a ha) (fun b hb hn => ?_) a List.mem_cons_self
    rw [List.mem_singleton.mp hb] at hn ⊢
    rcases lrRound_side ha (Or.inl hn) with ⟨d, i, rfl, hi⟩ | ⟨d, x, y, rfl⟩ | ⟨-, hg⟩
    · exact Or.inr (hcurL d i (hi.imp id And.right))
    · simp [needsSide, hmf d x y ha] at hn
    · exact Or.inl (hgA _ hg)
  have hEx : ∀ a, Stmt.atom a ∈ lrRound nt 1 o cap cur cl tabs pad → ∀ rd', a.Exact rd' σ := by
    intro a ha rd'
    cases a with
    | hint h =>
      rcases lrRound_side ha (Or.inr ⟨h, rfl⟩) with ⟨_, _, h', _⟩ | ⟨_, _, _, h'⟩ | ⟨-, hg⟩
      · cases h'
      · cases h'
      · obtain ⟨a', e, hx⟩ := gcInline_exact_of_shape gcShape_one.1 hvals _ hg
        cases e
        exact hx rd'
    | _ => trivial
  obtain ⟨hstep', hpad'⟩ := lrRound_stepP hA hnt hnt' (Or.inr ⟨rfl, hk3⟩) hpad (fun _ => hpow)
  rw [hst] at hstep'
  obtain ⟨e1, e2⟩ := roundStep_det hstep' hstep
  exact ⟨fun a ha => ⟨hA a ha, hEx a ha⟩, e1, e2, hpad', gcPtrs_of_vals gcShape_one hvals⟩

/-! ## Rounds in a row -/

/-- Round `r`'s grind's first value. -/
def lrOg (nt pts tabs r o : ℕ) (cap : List ℕ) (cur cl : ℕ) (pad : Option ℕ) : ℕ :=
  lrF (lrRounds nt 1 pts tabs r o cap cur cl pad).2.2.2.2.1 nt 1 (lrRounds nt 1 pts tabs r o cap cur cl pad).2.2.2.2.2 + 13

theorem lrP_ge (o nt bits : ℕ) : o ≤ lrP o nt bits := by unfold lrP lrE; omega

/-- **`k` rounds grinding one bit hold on their forward valuation**, from a chain of `k` rounds,
the challenges stored at `pts`, round `r`'s windows the honest ones of the chain's `r`-th state;
the hints are exact and the state after them the chain's last. -/
theorem lrRounds_complete1 {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {nt pts tabs m : ℕ}
    (hnt : 1 ≤ nt) (hnt' : nt ≤ 32) (hk3 : nt % 4 ≠ 3) (hSp : ∀ d p off, Atom.load d p off ∈ S → p.idx < m)
    (hrc : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2)
    (ht : WinTabs rd (σ (.n tabs))) :
    ∀ (k o : ℕ) (cap : List ℕ) (cur cl : ℕ) (pad : Option ℕ) (st : RSt) (l : List (E × RSt)),
      m ≤ cur → m ≤ o → tabs < o →
      (∀ a, Stmt.atom a ∈ (lrRounds nt 1 pts tabs k o cap cur cl pad).1 → Good rd S w σ a) →
      (∀ d x y, Stmt.atom (.mul d x y) ∈ (lrRounds nt 1 pts tabs k o cap cur cl pad).1 →
        x.idx < d.idx ∧ y.idx < d.idx) →
      (∀ a ∈ S, ∀ r < k, loadInto (lrOg nt pts tabs r o cap cur cl pad)
        (lrOg nt pts tabs r o cap cur cl pad + (gcLen 1 - 2)) a = false) →
      (∀ r < k, ∀ j ≤ gcW 1, w (lrOg nt pts tabs r o cap cur cl pad + j) =
        gcWin 1 (roundWord rd nt (chainLast st (l.take r))) j) →
      (∀ z, pad = some z → ∀ j < 4, σ (.n (z + j)) = 0) →
      rstOf σ cap cur cl = st → l.length = k → RoundChain rd nt 1 st l →
      ReadsAt rd (σ (.n pts)) (l.map Prod.fst) →
      (∀ a, Stmt.atom a ∈ (lrRounds nt 1 pts tabs k o cap cur cl pad).1 → a.Holds rd σ ∧ ∀ rd', a.Exact rd' σ) ∧
        rstOf σ (lrRounds nt 1 pts tabs k o cap cur cl pad).2.1 (lrRounds nt 1 pts tabs k o cap cur cl pad).2.2.1
          (lrRounds nt 1 pts tabs k o cap cur cl pad).2.2.2.1 = chainLast st l ∧
        m ≤ (lrRounds nt 1 pts tabs k o cap cur cl pad).2.2.1 ∧
        m ≤ (lrRounds nt 1 pts tabs k o cap cur cl pad).2.2.2.2.1 ∧
        tabs < (lrRounds nt 1 pts tabs k o cap cur cl pad).2.2.2.2.1 ∧
        ∀ z, (lrRounds nt 1 pts tabs k o cap cur cl pad).2.2.2.2.2 = some z → ∀ j < 4, σ (.n (z + j)) = 0
  | 0, o, cap, cur, cl, pad, st, l, hc, ho, hto, _, _, _, _, hpad, hst, hl, _, _ => by
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero hl
    exact ⟨fun a ha => by simp [lrRounds] at ha, hst, hc, ho, hto, hpad⟩
  | k + 1, o, cap, cur, cl, pad, st, l, hc, ho, hto, hG, hmf, hSg, hW, hpad, hst, hl, hch, hpts => by
    obtain ⟨l1, p, rfl⟩ : ∃ l1 p, l = l1 ++ [p] :=
      ⟨l.dropLast, l.getLast (by rintro rfl; simp at hl), (List.dropLast_append_getLast _).symm⟩
    obtain ⟨y, st'⟩ := p
    have hl1 : l1.length = k := by simpa using hl
    obtain ⟨hch1, hch2⟩ := roundChain_append_inv hch
    have hpts' : ReadsAt rd (σ (.n pts)) (l1.map Prod.fst ++ [y]) := by simpa using hpts
    have hsub : ∀ a, Stmt.atom a ∈ (lrRounds nt 1 pts tabs k o cap cur cl pad).1 →
        Stmt.atom a ∈ (lrRounds nt 1 pts tabs (k + 1) o cap cur cl pad).1 := fun a ha => by
      rw [lrRounds_succ]; exact List.mem_append_left _ (List.mem_append_left _ ha)
    have htake : ∀ r ≤ k, (l1 ++ [(y, st')]).take r = l1.take r := fun r hr =>
      List.take_append_of_le_length (by omega)
    obtain ⟨hA1, hlast, hc1, ho1, hto1, hpad1⟩ := lrRounds_complete1 hnt hnt' hk3 hSp hrc ht k o cap cur cl pad
      st l1 hc ho hto (fun a ha => hG a (hsub a ha)) (fun d x y ha => hmf d x y (hsub _ ha))
      (fun a ha r hr => hSg a ha r (by omega))
      (fun r hr j hj => by rw [hW r (by omega) j hj, htake r (by omega)]) hpad hst hl1 hch1
      (readsAt_prefix hpts')
    have hy := readsAt_last hpts'
    have hSgk : ∀ a ∈ S, loadInto (lrOg nt pts tabs k o cap cur cl pad)
        (lrOg nt pts tabs k o cap cur cl pad + (gcLen 1 - 2)) a = false := fun a ha => hSg a ha k (by omega)
    have hWk : ∀ j ≤ gcW 1, w (lrOg nt pts tabs k o cap cur cl pad + j) =
        gcWin 1 (roundWord rd nt (chainLast st l1)) j := fun j hj => by
      rw [hW k (by omega) j hj, htake k le_rfl, ← hl1, List.take_length]
    unfold lrOg at hSgk hWk
    rw [lrRounds_succ] at hG hmf ⊢
    generalize lrRounds nt 1 pts tabs k o cap cur cl pad = prev at hA1 hlast hc1 ho1 hto1 hpad1 hG hmf hSgk hWk ⊢
    obtain ⟨as, cap', cur', cl', o', pad'⟩ := prev
    dsimp only at hA1 hlast hc1 ho1 hto1 hpad1 hG hmf hSgk hWk ⊢
    have hmemR : ∀ a, Stmt.atom a ∈ lrRound nt 1 o' cap' cur' cl' tabs pad' →
        Stmt.atom a ∈ as ++ lrRound nt 1 o' cap' cur' cl' tabs pad' ++
          [.atom (.load (.n (lrD o' nt 1 pad' + 3)) (.n pts) k)] := fun a ha =>
      List.mem_append_left _ (List.mem_append_right _ ha)
    have hF := lrP_le_lrF o' nt 1 pad'
    have hP := lrP_ge o' nt 1
    have hD := le_lrD o' nt 1 pad'
    obtain ⟨hR, hyv, hout, hpad2, -⟩ := lrRound_complete1 hnt hnt' hk3 (fun a ha => hG a (hmemR a ha))
      (fun d x y ha => hmf d x y (hmemR _ ha))
      (fun d i hS => absurd (hSp d _ i hS) (by show ¬ cur' < m; omega)) hpad1 hlast hch2.1
      (by omega) hSgk hrc ht hWk
    refine ⟨fun a ha => ?_, ?_, by omega, by simp only [lrNext]; omega, by simp only [lrNext]; omega, hpad2⟩
    · rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_append.mp ha with ha | ha
        · exact hA1 a ha
        · exact hR a ha
      · simp only [List.mem_singleton, Stmt.atom.injEq] at ha
        subst ha
        refine ⟨?_, fun _ => trivial⟩
        show LoadHolds rd (σ (.n pts)) k (σ (.n (lrD o' nt 1 pad' + 3)))
        rw [hyv]
        simpa [hl1] using hy
    · rw [chainLast_append]; exact hout

/-! ## The windows' oracle -/

/-- The windows' oracle: at a value in the window run of a grind `(first, word)` of `ps`, that
grind's honest window. -/
noncomputable def winOracle (ps : List (ℕ × E)) (i : ℕ) : E :=
  match ps.find? (fun p => decide (p.1 ≤ i ∧ i ≤ p.1 + gcW 1)) with
  | some p => gcWin 1 p.2 (i - p.1)
  | none => 0

theorem winOracle_at {ps : List (ℕ × E)} (hps : (ps.map Prod.fst).Pairwise (fun a b => a + gcW 1 < b))
    {p : ℕ × E} (hp : p ∈ ps) {j : ℕ} (hj : j ≤ gcW 1) : winOracle ps (p.1 + j) = gcWin 1 p.2 j := by
  have hpw := List.pairwise_iff_getElem.mp (List.pairwise_map.mp hps)
  unfold winOracle
  cases hf : ps.find? (fun p' => decide (p'.1 ≤ p.1 + j ∧ p.1 + j ≤ p'.1 + gcW 1)) with
  | none =>
    have := List.find?_eq_none.mp hf p hp
    simp at this
    omega
  | some q =>
    have hq := List.mem_of_find?_eq_some hf
    have hqp := List.find?_some hf
    simp only [decide_eq_true_eq] at hqp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem hq
    rcases Nat.lt_trichotomy i i' with h | rfl | h
    · have := hpw i i' hi hi' h; omega
    · simp
    · have := hpw i' i hi' hi h; omega

end
end LeanVM.Guest.B1.VsC
